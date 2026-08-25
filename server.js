/**
 * Bombergay — servidor de partidas en LAN.
 * Sirve los archivos del juego y manda la simulación: los clientes solo
 * envían teclas y dibujan lo que reciben, así nadie se desincroniza.
 *
 *   node server.js            → http://localhost:8090/versus.html
 */
'use strict';

const http = require('http');
const fs   = require('fs');
const path = require('path');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT ? +process.env.PORT : 8090;
const RAIZ = __dirname;

/* ---------- servidor de archivos ---------- */
// lista blanca: solo estas páginas y lo que haya en /sonidos/ se sirven por HTTP.
// así server.js, package.json, .git, etc. nunca son alcanzables desde fuera.
const TIPOS = {
  '.html': 'text/html; charset=utf-8',
  '.mp3':  'audio/mpeg'
};
const PAGINAS = new Set(['/menu.html', '/index.html', '/versus.html']);

const servidor = http.createServer((req, res) => {
  let rel = decodeURIComponent(req.url.split('?')[0]);
  if (rel === '/') rel = '/menu.html';
  if (rel === '/historia.html') rel = '/versus.html';   // mismo cliente, otro modo

  let file;
  if (PAGINAS.has(rel)) file = path.join(RAIZ, rel);
  else if (rel.startsWith('/sonidos/')) file = path.join(RAIZ, 'sonidos', path.basename(rel));
  else { res.writeHead(404); return res.end('404'); }

  fs.readFile(file, (err, data) => {
    if (err){ res.writeHead(404); return res.end('404'); }
    res.writeHead(200, { 'Content-Type': TIPOS[path.extname(file)] || 'application/octet-stream' });
    res.end(data);
  });
});

/* ---------- constantes del juego ---------- */
const COLS = 20, ROWS = 13, TS = 40;
const EMPTY = 0, SOLID = 1, BRICK = 2;
const BOMB_TIME = 2.4, FLAME_TIME = .5, TICK = 1 / 60, ENVIO = 1;   // simula a 60, manda a 60 (mensajes de ~300B, de sobra)
const TP_COOLDOWN = 4, RONDAS_PARA_GANAR = 3;

const COLORES = ['#4ec3ff', '#7ee787', '#ffb02e', '#ff6b9d'];
const ESQUINAS = [{cx:1,cy:1}, {cx:COLS-2,cy:ROWS-2}, {cx:COLS-2,cy:1}, {cx:1,cy:ROWS-2}];

const TIPOS_ENEMIGO = {
  walker: { color:'#b07cff', vel: 42, persigue: .35 },
  slime:  { color:'#79e06b', vel: 32, persigue: .2 }
};

const rnd = n => Math.floor(Math.random() * n);
const cellOf = v => Math.floor(v / TS);
const center = c => c * TS + TS / 2;

/* ---------- salas: se crean bajo demanda con un código, y se borran al vaciarse ---------- */
const NIVELES_HISTORIA = 11;   // igual que la campaña de un jugador (NIVELES_CAMPANA en index.html)
const MAX_JUGADORES = { versus: 4, historia: 2 };
const CODIGO_ALFABETO = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';   // sin 0/O ni 1/I, se confunden al leerlos

function crearSala(modo, codigo){
  return {
    codigo, modo,                // versus | historia
    fase: 'lobby',              // lobby | jugando | finRonda | finPartida
    jugadores: new Map(),       // id -> jugador
    clientes: new Set(),        // sockets de la sala, para difundir sin barrer todas las conexiones
    grid: null, items: null,
    bombas: [], llamas: [], enemigos: [],
    tema: 0, ronda: 1, aviso: '', temporizador: 0, gridSucio: true, campeon: null,
    salida: null, salidaAbierta: false, victoria: false
  };
}

const salas = new Map();                // código -> sala; solo existen mientras tengan jugadores
let sala = null;                        // sala en curso (Node es de un solo hilo)
const enSala = (s, fn) => { const antes = sala; sala = s; try { return fn(); } finally { sala = antes; } };

function generarCodigo(){
  let c;
  do {
    c = '';
    for (let i = 0; i < 4; i++) c += CODIGO_ALFABETO[rnd(CODIGO_ALFABETO.length)];
  } while (salas.has(c));
  return c;
}

function crearSalaNueva(modo){
  const codigo = generarCodigo();
  const s = crearSala(modo, codigo);
  salas.set(codigo, s);
  return s;
}

// para "partida rápida": cualquier sala del modo que aún admita gente
function buscarSalaAbierta(modo){
  for (const s of salas.values())
    if (s.modo === modo && s.fase === 'lobby' && s.jugadores.size < MAX_JUGADORES[modo]) return s;
  return null;
}

let siguienteId = 1;

function tile(cx, cy){
  if (cx < 0 || cy < 0 || cx >= COLS || cy >= ROWS) return SOLID;
  return sala.grid[cy * COLS + cx];
}
const setTile = (cx, cy, v) => { sala.grid[cy * COLS + cx] = v; sala.gridSucio = true; };
const bombaEn = (cx, cy) => sala.bombas.find(b => b.cx === cx && b.cy === cy);
const llamaEn = (cx, cy) => sala.llamas.some(f => f.cx === cx && f.cy === cy);

function bloqueado(cx, cy, ent){
  if (tile(cx, cy) !== EMPTY) return true;
  const b = bombaEn(cx, cy);
  return !!(b && !(ent && b.pass.has(ent.id)));
}

/* ---------- generación del mapa ---------- */
function nuevoMapa(){
  sala.grid  = new Uint8Array(COLS * ROWS);
  sala.items = new Array(COLS * ROWS).fill(null);
  sala.bombas = []; sala.llamas = []; sala.enemigos = [];
  sala.gridSucio = true;
  sala.salida = null; sala.salidaAbierta = false;
  const hist = sala.modo === 'historia';
  const nivel = sala.ronda;
  sala.tema = hist ? (nivel - 1) % 10 : rnd(10);

  for (let y = 0; y < ROWS; y++)
    for (let x = 0; x < COLS; x++)
      if (x === 0 || y === 0 || x === COLS-1 || y === ROWS-1 || (x % 2 === 0 && y % 2 === 0))
        sala.grid[y * COLS + x] = SOLID;

  // las cuatro esquinas quedan despejadas
  const libres = new Set();
  for (const e of ESQUINAS){
    const sx = e.cx === 1 ? 1 : -1, sy = e.cy === 1 ? 1 : -1;
    [[0,0],[1,0],[2,0],[0,1],[0,2],[1,1]].forEach(([dx,dy]) =>
      libres.add((e.cy + dy*sy) * COLS + (e.cx + dx*sx)));
  }

  const ladrillos = [];
  for (let y = 1; y < ROWS-1; y++)
    for (let x = 1; x < COLS-1; x++){
      const i = y * COLS + x;
      if (sala.grid[i] === EMPTY && !libres.has(i) && Math.random() < (hist ? .48 : .62)){
        sala.grid[i] = BRICK;
        ladrillos.push(i);
      }
    }

  // power-ups repartidos bajo los ladrillos
  const barajado = ladrillos.sort(() => Math.random() - .5);
  const bolsa = ['fire','fire','fire','fire','fire','fire','fire','fire',
                 'bomb','bomb','bomb','bomb','bomb','bomb','bomb','bomb',
                 'speed','speed','speed','speed','life','life','life','life',
                 'remote','remote','remote','remote','spike','spike','spike','spike'];
  const cuantos = hist ? 8 : 40;
  while (bolsa.length < cuantos) bolsa.push(['fire','bomb','speed'][rnd(3)]);
  bolsa.sort(() => Math.random() - .5);
  for (let k = 0; k < cuantos && k < barajado.length; k++)
    sala.items[barajado[k]] = bolsa[k];

  // en historia la puerta de salida se esconde bajo un ladrillo lejano
  if (hist && barajado.length){
    const lejos = barajado.slice().sort((a, b) => {
      const da = (a % COLS) + Math.floor(a / COLS), db = (b % COLS) + Math.floor(b / COLS);
      return db - da;
    });
    const i = lejos[rnd(Math.max(1, Math.min(8, lejos.length)))];
    sala.salida = { cx: i % COLS, cy: Math.floor(i / COLS) };
  }

  // bichos: en historia suben con el nivel
  const kinds = Object.keys(TIPOS_ENEMIGO);
  const cuantosBichos = hist ? Math.min(10, 2 + nivel) : 4;
  let guarda = 0;
  while (sala.enemigos.length < cuantosBichos && guarda++ < 800){
    const x = 1 + rnd(COLS-2), y = 1 + rnd(ROWS-2);
    if (sala.grid[y * COLS + x] !== EMPTY) continue;
    if (ESQUINAS.some(e => Math.abs(e.cx - x) + Math.abs(e.cy - y) < 5)) continue;
    const kind = kinds[rnd(kinds.length)];
    sala.enemigos.push({
      kind, x: center(x), y: center(y), dir: [[1,0],[-1,0],[0,1],[0,-1]][rnd(4)],
      vel: TIPOS_ENEMIGO[kind].vel * (hist ? 1 + (nivel - 1) * .04 : 1), pensar: 0
    });
  }
}

/* ---------- jugadores ---------- */
function colocarJugadores(reset = true){
  for (const p of sala.jugadores.values()){
    const e = ESQUINAS[p.esquina % 4];
    p.x = center(e.cx); p.y = center(e.cy);
    p.vivo = p.vidas > 0; p.muriendo = 0; p.invuln = 2;
    if (reset){
      p.vidas = 3;
      p.maxBombas = 1; p.rango = 1; p.vel = 105;
      p.remoto = false; p.espinas = false;
      p.vivo = true;
    }
    p.enSalida = false;
    p.aim = null; p.aimT = 0; p.tpCd = 0; p.dir = [0, 0];
  }
}

function nuevaRonda(reset = true){
  sala.campeon = null;
  sala.victoria = false;
  nuevoMapa();
  colocarJugadores(reset);
  sala.fase = 'jugando';
  sala.aviso = '';
}

/* ---------- movimiento ---------- */
function paso(ent, dx, dy, dt){
  if (!dx && !dy) return false;
  const s = ent.vel * dt;
  const cx = cellOf(ent.x), cy = cellOf(ent.y);
  let movido = false;
  if (dx){
    const carril = center(cy), d = carril - ent.y;
    if (Math.abs(d) > .5) ent.y += Math.sign(d) * Math.min(s * .8, Math.abs(d));
    else ent.y = carril;
    const nx = ent.x + dx * s, borde = nx + dx * 13;
    if (!bloqueado(cellOf(borde), cellOf(ent.y), ent)){ ent.x = nx; movido = true; }
    else {
      const tope = center(cx);
      const val = dx > 0 ? Math.min(nx, tope) : Math.max(nx, tope);
      if (val !== ent.x){ ent.x = val; movido = true; }
    }
  }
  if (dy){
    const carril = center(cx), d = carril - ent.x;
    if (Math.abs(d) > .5) ent.x += Math.sign(d) * Math.min(s * .8, Math.abs(d));
    else ent.x = carril;
    const ny = ent.y + dy * s, borde = ny + dy * 13;
    if (!bloqueado(cellOf(ent.x), cellOf(borde), ent)){ ent.y = ny; movido = true; }
    else {
      const tope = center(cy);
      const val = dy > 0 ? Math.min(ny, tope) : Math.max(ny, tope);
      if (val !== ent.y){ ent.y = val; movido = true; }
    }
  }
  return movido;
}

/* ---------- bombas ---------- */
function ponerBomba(p){
  const cx = cellOf(p.x), cy = cellOf(p.y);
  if (bombaEn(cx, cy)) return;
  if (sala.bombas.filter(b => b.dueno === p.id).length >= p.maxBombas) return;
  sala.bombas.push({
    cx, cy, t: p.remoto ? Infinity : BOMB_TIME, remoto: p.remoto,
    perfora: p.espinas, rango: p.rango, dueno: p.id, pass: new Set([p.id])
  });
}

function detonar(bomba){
  const i = sala.bombas.indexOf(bomba);
  if (i === -1) return;
  sala.bombas.splice(i, 1);

  const celdas = [{ cx: bomba.cx, cy: bomba.cy, core: 1, spike: bomba.perfora ? 1 : 0 }];
  for (const [dx, dy] of [[1,0],[-1,0],[0,1],[0,-1]]){
    for (let r = 1; r <= bomba.rango; r++){
      const cx = bomba.cx + dx * r, cy = bomba.cy + dy * r;
      const t = tile(cx, cy);
      if (t === SOLID) break;
      if (t === BRICK){
        setTile(cx, cy, EMPTY);
        if (sala.salida && sala.salida.cx === cx && sala.salida.cy === cy) sala.salidaAbierta = true;
        celdas.push({ cx, cy, dx, dy, spike: bomba.perfora ? 1 : 0, end: bomba.perfora ? 0 : 1 });
        if (!bomba.perfora) break;
        continue;
      }
      celdas.push({ cx, cy, dx, dy, spike: bomba.perfora ? 1 : 0, end: r === bomba.rango ? 1 : 0 });
    }
  }
  for (const c of celdas){
    sala.llamas.push({ ...c, t: FLAME_TIME, dueno: bomba.dueno,
                       rango: bomba.rango + (bomba.perfora ? 1.5 : 0) });
    const cadena = bombaEn(c.cx, c.cy);
    if (cadena) detonar(cadena);
  }
}

function detonarRemota(p){
  const mias = sala.bombas.filter(b => b.dueno === p.id && b.remoto);
  if (mias.length) detonar(mias[0]);
}

/* ---------- daño ---------- */
function matar(p, culpable){
  if (!p.vivo || p.invuln > 0 || p.muriendo > 0) return;
  p.vivo = false; p.muriendo = 1.1; p.vidas--;
  p.aim = null;
  if (culpable && culpable !== p.id){
    const otro = sala.jugadores.get(culpable);
    if (otro) otro.puntos += 200;
  }
}

function comprobarGolpes(){
  for (const p of sala.jugadores.values()){
    if (!p.vivo) continue;
    const cx = cellOf(p.x), cy = cellOf(p.y);
    const f = sala.llamas.find(f => f.cx === cx && f.cy === cy);
    if (f){ matar(p, f.dueno); continue; }
    for (const e of sala.enemigos)
      if (Math.hypot(e.x - p.x, e.y - p.y) < 24){ matar(p, null); break; }
  }
  sala.enemigos = sala.enemigos.filter(e => {
    const f = sala.llamas.find(f => f.cx === cellOf(e.x) && f.cy === cellOf(e.y));
    if (!f) return true;
    const dueno = sala.jugadores.get(f.dueno);
    if (dueno) dueno.puntos += 100;
    return false;
  });
}

function recoger(p){
  const cx = cellOf(p.x), cy = cellOf(p.y), i = cy * COLS + cx;
  const it = sala.items[i];
  if (!it || tile(cx, cy) !== EMPTY) return;
  sala.items[i] = null;
  sala.gridSucio = true;
  if (it === 'bomb')  p.maxBombas++;
  if (it === 'fire')  p.rango++;
  if (it === 'speed') p.vel = Math.min(190, p.vel + 22);
  if (it === 'remote') p.remoto = true;
  if (it === 'spike')  p.espinas = true;
  if (it === 'life'){ p.vidas = Math.min(6, p.vidas + 1); p.maxVidas = Math.max(p.maxVidas, p.vidas); }
  p.puntos += 50;
}

/* ---------- teletransporte ---------- */
function destinoValido(cx, cy){
  if (tile(cx, cy) !== EMPTY) return false;
  if (bombaEn(cx, cy) || llamaEn(cx, cy)) return false;
  if (sala.enemigos.some(e => cellOf(e.x) === cx && cellOf(e.y) === cy)) return false;
  return true;
}

function teletransportar(p){
  if (!p.aim) return;
  const { cx, cy } = p.aim;
  if (!destinoValido(cx, cy)) return;
  p.x = center(cx); p.y = center(cy);
  p.aim = null;
  p.tpCd = TP_COOLDOWN;
  p.invuln = Math.max(p.invuln, .6);
}

/* ---------- IA de los bichos ---------- */
function iaEnemigo(e, dt){
  const cx = cellOf(e.x), cy = cellOf(e.y);
  const centrado = Math.abs(e.x - center(cx)) < 2 && Math.abs(e.y - center(cy)) < 2;
  const movido = paso(e, e.dir[0], e.dir[1], dt);
  e.pensar -= dt;
  if (movido && !(centrado && e.pensar <= 0)) return;

  e.pensar = .35 + Math.random() * .5;
  const opciones = [[1,0],[-1,0],[0,1],[0,-1]].filter(([dx, dy]) =>
    !bloqueado(cx + dx, cy + dy, null) && !llamaEn(cx + dx, cy + dy));
  if (!opciones.length){ e.dir = [0, 0]; return; }

  let elegida = opciones[rnd(opciones.length)];
  if (Math.random() < TIPOS_ENEMIGO[e.kind].persigue){
    const vivos = [...sala.jugadores.values()].filter(p => p.vivo);
    const objetivo = vivos.sort((a, b) =>
      Math.hypot(a.x-e.x, a.y-e.y) - Math.hypot(b.x-e.x, b.y-e.y))[0];
    if (objetivo)
      elegida = opciones.slice().sort((a, b) =>
        Math.hypot(center(cx+a[0])-objetivo.x, center(cy+a[1])-objetivo.y) -
        Math.hypot(center(cx+b[0])-objetivo.x, center(cy+b[1])-objetivo.y))[0];
  }
  e.dir = elegida;
}

/* ---------- bucle ---------- */
function tick(dt){
  if (sala.fase === 'finRonda' || sala.fase === 'finPartida'){
    sala.temporizador -= dt;
    if (sala.temporizador <= 0){
      if (sala.fase === 'finPartida'){
        for (const p of sala.jugadores.values()){ p.rondas = 0; p.puntos = 0; p.listo = false; }
        sala.ronda = 1;
        sala.fase = 'lobby';
        sala.victoria = false;
        const todos = [...sala.jugadores.values()];
        if (todos.length >= minJugadores() && todos.every(p => p.listo)) nuevaRonda();   // revancha
      } else {
        sala.ronda++;
        nuevaRonda(sala.modo !== 'historia');   // en historia se conservan mejoras y vidas
      }
      difundirLobby();
    }
    return;
  }
  if (sala.fase !== 'jugando') return;

  for (const p of sala.jugadores.values()){
    if (p.muriendo > 0){
      p.muriendo -= dt;
      if (p.muriendo <= 0 && p.vidas > 0){
        const e = ESQUINAS[p.esquina % 4];
        p.x = center(e.cx); p.y = center(e.cy);
        p.vivo = true; p.invuln = 2.2;
      }
      continue;
    }
    if (!p.vivo) continue;
    p.invuln = Math.max(0, p.invuln - dt);
    p.tpCd = Math.max(0, p.tpCd - dt);

    const k = p.teclas;
    let dx = (k.r ? 1 : 0) - (k.l ? 1 : 0);
    let dy = (k.d ? 1 : 0) - (k.u ? 1 : 0);
    if (dx && dy) dy = 0;

    if (p.pulsoTp){                          // Q
      p.pulsoTp = false;
      if (p.aim) teletransportar(p);
      else if (p.tpCd <= 0){ p.aim = { cx: cellOf(p.x), cy: cellOf(p.y) }; p.aimT = 0; }
    }
    if (p.pulsoDet){ p.pulsoDet = false; detonarRemota(p); }
    if (p.cancelaAim){ p.cancelaAim = false; p.aim = null; }

    if (p.aim){                              // apuntando: quieto
      p.aimT -= dt;
      if ((dx || dy) && p.aimT <= 0){
        p.aim.cx = Math.max(1, Math.min(COLS-2, p.aim.cx + dx));
        p.aim.cy = Math.max(1, Math.min(ROWS-2, p.aim.cy + dy));
        p.aimT = .13;
      }
      recoger(p);
      continue;
    }

    p.dir = [dx, dy];
    paso(p, dx, dy, dt);
    if (p.pulsoBomba){ p.pulsoBomba = false; ponerBomba(p); }
    recoger(p);
  }

  for (const b of sala.bombas.slice()){
    if (!b.remoto) b.t -= dt;
    for (const id of Array.from(b.pass)){
      const p = sala.jugadores.get(id);
      if (!p || cellOf(p.x) !== b.cx || cellOf(p.y) !== b.cy) b.pass.delete(id);
    }
    if (b.t <= 0) detonar(b);
  }

  sala.llamas = sala.llamas.filter(f => (f.t -= dt) > 0);
  sala.enemigos.forEach(e => iaEnemigo(e, dt));
  comprobarGolpes();

  const activos = [...sala.jugadores.values()].filter(p => p.vidas > 0);

  if (sala.modo === 'historia'){
    if (!sala.jugadores.size) return;
    if (!activos.length){                                  // game over cooperativo
      sala.fase = 'finPartida';
      sala.victoria = false;
      sala.aviso = 'Game over en el nivel ' + sala.ronda;
      sala.campeon = null;
      sala.temporizador = 6;
      difundirLobby();
      return;
    }
    // la puerta solo funciona sin bichos en el mapa
    const libre = sala.enemigos.length === 0 && sala.salidaAbierta && sala.salida;
    const enPuerta = libre && activos.some(p =>
      p.vivo && cellOf(p.x) === sala.salida.cx && cellOf(p.y) === sala.salida.cy);
    if (enPuerta){
      activos.forEach(p => { p.puntos += 300; p.rondas = sala.ronda; });
      if (sala.ronda >= NIVELES_HISTORIA){
        sala.fase = 'finPartida';
        sala.victoria = true;
        sala.aviso = '¡Habéis terminado la campaña!';
        sala.campeon = null;
        sala.temporizador = 9;
      } else {
        sala.fase = 'finRonda';
        sala.aviso = 'Nivel ' + sala.ronda + ' superado';
        sala.campeon = null;
        sala.temporizador = 3;
      }
      difundirLobby();
    }
    return;
  }

  // versus: ¿queda uno en pie?
  if (sala.jugadores.size >= 2 && activos.length <= 1){
    const ganador = activos[0] || null;
    if (ganador){ ganador.rondas++; ganador.puntos += 500; }
    if (ganador && ganador.rondas >= RONDAS_PARA_GANAR){
      sala.fase = 'finPartida';
      sala.aviso = '¡' + ganador.nombre + ' gana la partida!';
      sala.campeon = { nombre: ganador.nombre, color: ganador.color, puntos: ganador.puntos };
      sala.temporizador = 8;
    } else {
      sala.fase = 'finRonda';
      sala.aviso = ganador ? 'Ronda para ' + ganador.nombre : 'Ronda en tablas';
      sala.campeon = ganador ? { nombre: ganador.nombre, color: ganador.color, puntos: ganador.puntos } : null;
      sala.temporizador = 4;
    }
    difundirLobby();
  }
}

/* ---------- red ---------- */
const wss = new WebSocketServer({ server: servidor });

function minJugadores(){ return sala.modo === 'historia' ? 1 : 2; }

function enviar(ws, obj){
  if (ws.readyState === 1) ws.send(JSON.stringify(obj));
}
function difundir(obj){
  const txt = JSON.stringify(obj);
  sala.clientes.forEach(c => { if (c.readyState === 1) c.send(txt); });
}

function resumenJugadores(){
  return [...sala.jugadores.values()].map(p => ({
    id: p.id, nombre: p.nombre, color: p.color, listo: p.listo,
    rondas: p.rondas, puntos: p.puntos, vidas: p.vidas, maxVidas: p.maxVidas
  }));
}
function difundirLobby(){
  difundir({ t: 'lobby', codigo: sala.codigo, modo: sala.modo, fase: sala.fase,
             jugadores: resumenJugadores(),
             ronda: sala.ronda, aviso: sala.aviso,
             paraGanar: sala.modo === 'historia' ? NIVELES_HISTORIA : RONDAS_PARA_GANAR,
             maxJugadores: MAX_JUGADORES[sala.modo],
             minJugadores: minJugadores(), victoria: !!sala.victoria,
             campeon: sala.campeon || null });
}

function estado(){
  const msg = {
    t: 's', modo: sala.modo, fase: sala.fase, tema: sala.tema, ronda: sala.ronda, aviso: sala.aviso,
    sal: (sala.modo === 'historia' && sala.salidaAbierta && sala.salida)
           ? [sala.salida.cx, sala.salida.cy, sala.enemigos.length === 0 ? 1 : 0] : null,
    b: sala.bombas.map(b => [b.cx, b.cy, b.remoto ? 1 : 0, b.perfora ? 1 : 0]),
    f: sala.llamas.map(f => [f.cx, f.cy, f.core ? 1 : 0, f.dx || 0, f.dy || 0, f.spike || 0,
                             +(f.t / FLAME_TIME).toFixed(2), f.rango || 1]),
    e: sala.enemigos.map(e => [Math.round(e.x), Math.round(e.y), e.kind === 'slime' ? 1 : 0,
                               e.dir[0], e.dir[1]]),
    p: [...sala.jugadores.values()].map(p => [
      p.id, Math.round(p.x), Math.round(p.y), p.dir[0], p.dir[1],
      p.vivo ? 1 : 0, p.vidas, p.maxVidas, +p.invuln.toFixed(1),
      p.aim ? p.aim.cx : -1, p.aim ? p.aim.cy : -1,
      p.remoto ? 1 : 0, p.espinas ? 1 : 0, p.maxBombas, p.rango, p.puntos,
      +p.tpCd.toFixed(1), +p.muriendo.toFixed(2), Math.round(p.vel)
    ])
  };
  if (sala.gridSucio && sala.grid){
    msg.g = Array.from(sala.grid).join('');
    msg.it = sala.items.map((v, i) => v ? [i, v] : null).filter(Boolean);
    sala.gridSucio = false;
  }
  return msg;
}

// primer puesto (color/esquina) libre, no el tamaño actual: si alguien se fue
// y otro entra después, jugadores.size puede repetir un puesto ya ocupado
function puestoLibre(s){
  const ocupados = new Set([...s.jugadores.values()].map(p => p.esquina));
  const tope = MAX_JUGADORES[s.modo];
  for (let i = 0; i < tope; i++) if (!ocupados.has(i)) return i;
  return s.jugadores.size;
}

function unirJugador(ws, s, nombre){
  const id = siguienteId++;
  const esquina = puestoLibre(s);
  const jugador = {
    id, ws, esquina,
    nombre: String(nombre || 'Jugador').slice(0, 12),
    color: COLORES[esquina % 4], listo: false,
    rondas: 0, puntos: 0, maxVidas: 3, vidas: 3,
    x: center(ESQUINAS[esquina % 4].cx), y: center(ESQUINAS[esquina % 4].cy),
    dir: [0, 0], vivo: true, muriendo: 0, invuln: 0,
    maxBombas: 1, rango: 1, vel: 105, remoto: false, espinas: false,
    aim: null, aimT: 0, tpCd: 0,
    teclas: { u:0, d:0, l:0, r:0 },
    pulsoBomba: false, pulsoTp: false, pulsoDet: false, cancelaAim: false
  };
  s.jugadores.set(id, jugador);
  s.clientes.add(ws);
  ws.codigo = s.codigo;
  enviar(ws, { t: 'bienvenido', id, codigo: s.codigo, modo: s.modo, cols: COLS, rows: ROWS, ts: TS, color: jugador.color });
  enSala(s, difundirLobby);
  return jugador;
}

wss.on('connection', ws => {
  ws._socket?.setNoDelay(true);   // sin esto, TCP agrupa paquetes chicos y suma hasta ~40ms por mensaje
  let jugador = null;
  ws.vivo = true;
  ws.on('pong', () => { ws.vivo = true; });

  ws.on('message', datos => {
    let m;
    try { m = JSON.parse(datos.toString()); } catch { return; }

    if (m.t === 'ping'){ enviar(ws, { t: 'pong', t0: m.t0 }); return; }

    if (m.t === 'listar'){                    // lista de salas abiertas, para elegir sin escribir código
      if (jugador) return;
      const modo = m.modo === 'historia' ? 'historia' : 'versus';
      const lista = [];
      for (const s of salas.values())
        if (s.modo === modo && s.fase === 'lobby')
          lista.push({ codigo: s.codigo, jugadores: s.jugadores.size, max: MAX_JUGADORES[modo] });
      enviar(ws, { t: 'salas', lista });
      return;
    }

    if (m.t === 'rapida'){                    // modo LAN: te mete en cualquier sala abierta, o crea una
      if (jugador) return;
      const modo = m.modo === 'historia' ? 'historia' : 'versus';
      const s = buscarSalaAbierta(modo) || crearSalaNueva(modo);
      jugador = unirJugador(ws, s, m.nombre);
      return;
    }

    if (m.t === 'crear'){
      if (jugador) return;
      const modo = m.modo === 'historia' ? 'historia' : 'versus';
      const s = crearSalaNueva(modo);
      jugador = unirJugador(ws, s, m.nombre);
      return;
    }

    if (m.t === 'unir'){
      if (jugador) return;
      const codigo = String(m.codigo || '').toUpperCase().trim();
      const s = salas.get(codigo);
      if (!s) return enviar(ws, { t: 'error', motivo: 'No existe ninguna sala con ese código.' });
      if (m.modo && s.modo !== m.modo)
        return enviar(ws, { t: 'error', motivo: 'Ese código es de modo ' + s.modo + ', no de ' + m.modo + '.' });
      if (s.jugadores.size >= MAX_JUGADORES[s.modo]) return enviar(ws, { t: 'lleno' });
      jugador = unirJugador(ws, s, m.nombre);
      return;
    }

    if (!jugador) return;
    sala = salas.get(ws.codigo);
    if (!sala) return;               // la sala se cerró (se vació) mientras tanto

    if (m.t === 'listo'){
      jugador.listo = !!m.v;
      const todos = [...sala.jugadores.values()];
      if (sala.fase === 'lobby' && todos.length >= minJugadores() && todos.every(p => p.listo)){
        sala.ronda = 1;
        todos.forEach(p => { p.rondas = 0; p.puntos = 0; });
        nuevaRonda();
      }
      difundirLobby();
      return;
    }

    if (m.t === 'k'){                       // teclas mantenidas
      jugador.teclas = { u: m.u|0, d: m.d|0, l: m.l|0, r: m.r|0 };
      return;
    }
    if (m.t === 'bomba'){ jugador.pulsoBomba = true; return; }
    if (m.t === 'tp'){    jugador.pulsoTp = true; return; }
    if (m.t === 'det'){   jugador.pulsoDet = true; return; }
    if (m.t === 'cancela'){ jugador.cancelaAim = true; return; }
    if (m.t === 'apunta' && jugador.aim){   // ratón
      jugador.aim.cx = Math.max(0, Math.min(COLS-1, m.cx|0));
      jugador.aim.cy = Math.max(0, Math.min(ROWS-1, m.cy|0));
      return;
    }
  });

  ws.on('close', () => {
    if (!jugador) return;
    const s = salas.get(ws.codigo);
    if (!s) return;
    s.jugadores.delete(jugador.id);
    s.clientes.delete(ws);
    if (s.jugadores.size === 0){
      salas.delete(ws.codigo);       // sala vacía: se libera, no queda ocupando memoria
      return;
    }
    enSala(s, difundirLobby);
  });
});

/* ---------- latido: expulsa conexiones muertas ---------- */
setInterval(() => {
  wss.clients.forEach(ws => {
    if (ws.vivo === false) return ws.terminate();   // no contestó el ping anterior
    ws.vivo = false;
    ws.ping();
  });
}, 10000);

/* ---------- arranque ---------- */
let cuentaEnvio = 0;
setInterval(() => {
  cuentaEnvio++;
  for (const s of salas.values()) enSala(s, () => {
    tick(TICK);
    if (sala.fase !== 'lobby' && cuentaEnvio % ENVIO === 0) difundir(estado());
  });
}, TICK * 1000);

servidor.listen(PORT, '0.0.0.0', () => {
  const nets = require('os').networkInterfaces();
  const ips = Object.values(nets).flat().filter(n => n && n.family === 'IPv4' && !n.internal);
  console.log('Bombergay versus escuchando en el puerto ' + PORT);
  console.log('  local : http://localhost:' + PORT + '/menu.html');
  ips.forEach(n => console.log('  en LAN: http://' + n.address + ':' + PORT + '/menu.html'));
});

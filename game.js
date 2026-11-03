const DEFAULT_IMAGE = './743876611_1801119841258005_5820049171402192924_n.png';
const GRID = 50;
const MAX_BLOCK_HEIGHT = 14;
const PLAYER_MAX_HP = 100;
const STARTING_BLOCKS = 8;

const canvas = document.querySelector('#gameCanvas');
const worldImageInput = document.querySelector('#worldImageInput');
const bossImageInput = document.querySelector('#bossImageInput');
const worldPreview = document.querySelector('#worldPreview');
const worldImageName = document.querySelector('#worldImageName');
const bossList = document.querySelector('#bossList');
const bossCount = document.querySelector('#bossCount');
const toast = document.querySelector('#toast');
const welcomeOverlay = document.querySelector('#welcomeOverlay');
const resultOverlay = document.querySelector('#resultOverlay');
const resultButton = document.querySelector('#resultButton');
const bossHud = document.querySelector('#bossHud');
const controlsCard = document.querySelector('#controlsCard');

let THREE;
let renderer;
let scene;
let camera;
let worldGroup;
let arenaGroup;
let playerGroup;
let terrainMesh;
let terrainHeights = new Uint8Array(GRID * GRID);
let blockRecords = [];
let worldImage;
let worldPixels;
let worldImageObjectUrl = null;
let bossGroup;
let bossRadius = 2.25;
let bossMaxHp = 120;
let bossHp = bossMaxHp;
let bossCatalog = [];
let activeBoss = 0;
let mode = 'world';
let started = false;
let yaw = 0;
let selectedSlot = 1;
let playerHp = PLAYER_MAX_HP;
let playerLevel = 1;
let blocksInPack = STARTING_BLOCKS;
let playerVelocityY = 0;
let jumpOffset = 0;
let guarding = false;
let pointerHeld = false;
let pointerDragged = false;
let pointerStart = { x: 0, y: 0 };
let currentPointer = { x: innerWidth / 2, y: innerHeight / 2 };
let playerCooldown = 0;
let bossCooldown = 1.1;
let elapsed = 0;
let toastTimer = 0;
let lastTimestamp = 0;
let audioEnabled = false;
let audioContext = null;
const keys = { w: false, a: false, s: false, d: false, space: false, shift: false };
const playerProjectiles = [];
const bossProjectiles = [];
const placedBlocks = [];

function showToast(message, duration = 2200) {
  toast.textContent = message;
  toast.classList.add('visible');
  clearTimeout(toastTimer);
  toastTimer = setTimeout(() => toast.classList.remove('visible'), duration);
}

function clamp(value, min, max) { return Math.max(min, Math.min(max, value)); }
function mix(a, b, t) { return a + (b - a) * t; }
function worldX(gx) { return gx - GRID / 2 + 0.5; }
function worldZ(gz) { return gz - GRID / 2 + 0.5; }

function loadImage(src) {
  return new Promise((resolve, reject) => {
    const img = new Image();
    img.onload = () => resolve(img);
    img.onerror = () => reject(new Error(`Không tải được ảnh: ${src}`));
    img.src = src;
  });
}

function setImagePixels(img) {
  const sampleCanvas = document.createElement('canvas');
  sampleCanvas.width = GRID;
  sampleCanvas.height = GRID;
  const context = sampleCanvas.getContext('2d', { willReadFrequently: true });
  const scale = Math.max(GRID / img.width, GRID / img.height);
  const sourceWidth = GRID / scale;
  const sourceHeight = GRID / scale;
  const cropX = (img.width - sourceWidth) / 2;
  const cropY = (img.height - sourceHeight) / 2;
  context.drawImage(img, cropX, cropY, sourceWidth, sourceHeight, 0, 0, GRID, GRID);
  worldPixels = context.getImageData(0, 0, GRID, GRID).data;
}

function readSource(gx, gz) {
  const i = (gz * GRID + gx) * 4;
  const r = worldPixels[i] / 255;
  const g = worldPixels[i + 1] / 255;
  const b = worldPixels[i + 2] / 255;
  return { r, g, b, lum: 0.2126 * r + 0.7152 * g + 0.0722 * b };
}

function deterministicNoise(x, z) {
  const n = Math.sin(x * 127.1 + z * 311.7 + 42.7) * 43758.5453;
  return (n - Math.floor(n)) * 2 - 1;
}

function caveGeometryContains(gx, gz, level) {
  const zCenter = (GRID - 1) / 2;
  const centerX = GRID - 13;
  const centerY = 3.2;
  const blockY = level + 0.5;
  const low = Math.min(GRID - 1, Math.max(centerX, gx));
  const tunnelDistance = Math.hypot(gx - low, gz - zCenter);
  const inTunnel = gx >= centerX - 2 && tunnelDistance < 2.15 && blockY > 1.2 && blockY < 4.7;
  const chamberDistance = Math.hypot(gx - centerX, gz - zCenter, (blockY - centerY) * 1.05);
  return inTunnel || chamberDistance < 4.6;
}

function topBlockColor(source, gx, gz) {
  const dark = source.lum < 0.14;
  const warm = source.r > source.g * 1.12 && source.r > source.b * 1.17;
  const cool = source.b > source.r * 1.13 && source.b > source.g * 1.04;
  let palette;
  if (dark) palette = [0.23, 0.29, 0.28];
  else if (cool) palette = [0.34, 0.48, 0.52];
  else if (warm) palette = [0.58, 0.43, 0.31];
  else palette = [0.39, 0.57, 0.37];
  const sourceWeight = dark ? 0.28 : 0.46;
  const shade = 0.92 + ((gx * 3 + gz * 7) % 5) * 0.035;
  const out = [source.r, source.g, source.b].map((c, i) => {
    const value = mix(palette[i], c, sourceWeight) * shade;
    return Math.round(clamp(value, 0.07, 0.9) * 5) / 5;
  });
  return out;
}

function disposeObject(object) {
  object.traverse?.(child => {
    child.geometry?.dispose?.();
    const mats = Array.isArray(child.material) ? child.material : [child.material];
    for (const material of mats) material?.dispose?.();
  });
}

function buildTerrain() {
  for (const child of [...worldGroup.children]) {
    worldGroup.remove(child);
    disposeObject(child);
  }
  const half = GRID / 2;
  const centerZ = (GRID - 1) / 2;
  for (let gz = 0; gz < GRID; gz++) {
    for (let gx = 0; gx < GRID; gx++) {
      const { lum } = readSource(gx, gz);
      const ridgeDistance = Math.hypot(gx - (GRID - 7), gz - centerZ);
      const caveRidge = Math.max(0, 1 - ridgeDistance / 10) * 5.2;
      const islandLift = Math.max(0, 1 - Math.hypot(gx - half, gz - half) / 43) * 1.2;
      const detail = deterministicNoise(gx, gz) * 0.72;
      const height = clamp(Math.floor(1.6 + lum * 7.7 + caveRidge + islandLift + detail), 2, MAX_BLOCK_HEIGHT - 1);
      terrainHeights[gz * GRID + gx] = height;
    }
  }

  const capacity = GRID * GRID * MAX_BLOCK_HEIGHT;
  const mesh = new THREE.InstancedMesh(
    new THREE.BoxGeometry(1, 1, 1),
    new THREE.MeshStandardMaterial({ roughness: 0.96, metalness: 0.01, flatShading: true, vertexColors: true }),
    capacity
  );
  mesh.instanceMatrix.setUsage(THREE.DynamicDrawUsage);
  mesh.frustumCulled = false;
  const matrix = new THREE.Matrix4();
  const position = new THREE.Vector3();
  const scale = new THREE.Vector3(1, 1, 1);
  const color = new THREE.Color();
  const quaternion = new THREE.Quaternion();
  blockRecords = [];
  let index = 0;

  for (let gz = 0; gz < GRID; gz++) {
    for (let gx = 0; gx < GRID; gx++) {
      const source = readSource(gx, gz);
      const height = terrainHeights[gz * GRID + gx];
      const top = topBlockColor(source, gx, gz);
      for (let level = 0; level < height; level++) {
        if (caveGeometryContains(gx, gz, level)) continue;
        const depth = height - 1 - level;
        let rgb;
        if (depth === 0) rgb = top;
        else if (depth < 3) rgb = source.lum < 0.14 ? [0.25, 0.28, 0.27] : [0.43, 0.32, 0.23];
        else if (level < 2) rgb = [0.24, 0.27, 0.26];
        else rgb = [0.34 + (source.b * 0.04), 0.37 + (source.g * 0.04), 0.37 + (source.r * 0.035)];
        position.set(worldX(gx), level + 0.5, worldZ(gz));
        matrix.compose(position, quaternion, scale);
        mesh.setMatrixAt(index, matrix);
        color.setRGB(rgb[0], rgb[1], rgb[2]);
        mesh.setColorAt(index, color);
        blockRecords[index] = { gx, gz, level, top: depth === 0, removed: false };
        index++;
      }
    }
  }
  mesh.count = index;
  mesh.instanceMatrix.needsUpdate = true;
  if (mesh.instanceColor) mesh.instanceColor.needsUpdate = true;
  terrainMesh = mesh;
  worldGroup.add(mesh);

  const underside = new THREE.Mesh(
    new THREE.BoxGeometry(GRID, 0.5, GRID),
    new THREE.MeshStandardMaterial({ color: 0x202c28, roughness: 1 })
  );
  underside.position.y = -0.35;
  worldGroup.add(underside);
  buildTrees();
  buildCaveMarker();
}

function heightAt(x, z) {
  const gx = clamp(Math.floor(x + GRID / 2), 0, GRID - 1);
  const gz = clamp(Math.floor(z + GRID / 2), 0, GRID - 1);
  return terrainHeights[gz * GRID + gx] || 1;
}

function makeVoxelBox(parent, size, at, hex, roughness = 0.92) {
  const mesh = new THREE.Mesh(
    new THREE.BoxGeometry(size[0], size[1], size[2]),
    new THREE.MeshStandardMaterial({ color: hex, roughness, flatShading: true })
  );
  mesh.position.set(at[0], at[1], at[2]);
  mesh.castShadow = true;
  mesh.receiveShadow = true;
  parent.add(mesh);
  return mesh;
}

function buildTrees() {
  const candidates = [
    [-18, -14], [-13, -17], [-8, -15], [-4, -19], [5, -17], [12, -15], [17, -10],
    [-19, -4], [-14, 2], [-16, 9], [-11, 16], [-5, 19], [7, 18], [13, 14], [18, 9], [16, -2]
  ];
  for (const [x, z] of candidates) {
    if (Math.hypot(x, z - 12) < 5 || (x > 10 && Math.abs(z) < 6)) continue;
    const y = heightAt(x, z);
    const tree = new THREE.Group();
    tree.position.set(x, y, z);
    makeVoxelBox(tree, [0.65, 2.7, 0.65], [0, 1.35, 0], 0x674a35);
    makeVoxelBox(tree, [1.8, 1.1, 1.7], [0, 3.1, 0], 0x3f7148);
    makeVoxelBox(tree, [1.35, 1.1, 1.35], [0, 3.9, 0], 0x538a52);
    makeVoxelBox(tree, [1.65, 0.65, 1.2], [0.45, 2.7, -0.15], 0x47794b);
    worldGroup.add(tree);
  }
}

function buildCaveMarker() {
  const entry = new THREE.Group();
  const x = GRID / 2 - 0.7;
  entry.position.set(x, 1.5, 0);
  const ring = new THREE.Mesh(
    new THREE.TorusGeometry(1.35, 0.15, 6, 14),
    new THREE.MeshStandardMaterial({ color: 0x86efba, emissive: 0x165437, emissiveIntensity: 1.3, roughness: 0.42 })
  );
  ring.rotation.y = Math.PI / 2;
  ring.position.y = 1.7;
  entry.add(ring);
  const core = new THREE.Mesh(
    new THREE.CircleGeometry(1.18, 8),
    new THREE.MeshBasicMaterial({ color: 0x101d19, side: THREE.DoubleSide })
  );
  core.rotation.y = Math.PI / 2;
  core.position.y = 1.7;
  core.position.x = -0.03;
  entry.add(core);
  const light = new THREE.PointLight(0x66e7aa, 2.5, 10, 2);
  light.position.set(-1.6, 2.4, 0);
  entry.add(light);
  worldGroup.add(entry);

  const chamber = new THREE.Group();
  chamber.position.set(x - 7.2, 1.1, 0);
  const crystalMaterial = new THREE.MeshStandardMaterial({ color: 0x87f4df, emissive: 0x36c6aa, emissiveIntensity: 2.1, roughness: 0.36, flatShading: true });
  for (const [cx, cz, h] of [[-1.2, -1.5, 2.2], [1.2, 1.1, 1.6], [0.2, -2.5, 1.2]]) {
    const crystal = new THREE.Mesh(new THREE.ConeGeometry(0.38, h, 5), crystalMaterial);
    crystal.position.set(cx, h / 2, cz);
    chamber.add(crystal);
  }
  const caveLight = new THREE.PointLight(0x4fd7bc, 2.3, 12, 2);
  caveLight.position.set(0, 2.5, 0);
  chamber.add(caveLight);
  worldGroup.add(chamber);
}

function buildPlayer() {
  playerGroup = new THREE.Group();
  const tunic = new THREE.MeshStandardMaterial({ color: 0x62bd7a, roughness: 0.82, flatShading: true });
  const skin = new THREE.MeshStandardMaterial({ color: 0xd5a17c, roughness: 0.95, flatShading: true });
  const dark = new THREE.MeshStandardMaterial({ color: 0x533d30, roughness: 1, flatShading: true });
  const pants = new THREE.MeshStandardMaterial({ color: 0x465b73, roughness: 0.95, flatShading: true });
  const addPart = (material, size, position) => {
    const mesh = new THREE.Mesh(new THREE.BoxGeometry(...size), material);
    mesh.position.set(...position);
    mesh.castShadow = true;
    playerGroup.add(mesh);
    return mesh;
  };
  addPart(tunic, [0.82, 0.95, 0.5], [0, 1.2, 0]);
  addPart(skin, [0.68, 0.68, 0.65], [0, 2.05, 0]);
  addPart(dark, [0.72, 0.2, 0.69], [0, 2.43, 0]);
  addPart(pants, [0.34, 0.78, 0.45], [-0.22, 0.38, 0]);
  addPart(pants, [0.34, 0.78, 0.45], [0.22, 0.38, 0]);
  const leftArm = addPart(skin, [0.26, 0.85, 0.35], [-0.56, 1.23, 0]);
  const rightArm = addPart(skin, [0.26, 0.85, 0.35], [0.56, 1.23, 0]);
  rightArm.name = 'rightArm';
  leftArm.name = 'leftArm';
  playerGroup.position.set(0, 0, 12);
  playerGroup.position.y = heightAt(playerGroup.position.x, playerGroup.position.z);
  scene.add(playerGroup);
}

function buildArena() {
  const floor = new THREE.Mesh(
    new THREE.CylinderGeometry(15, 15, 0.7, 12),
    new THREE.MeshStandardMaterial({ color: 0x37433e, roughness: 0.95, flatShading: true })
  );
  floor.position.y = -0.42;
  arenaGroup.add(floor);
  const inset = new THREE.Mesh(
    new THREE.CylinderGeometry(8.5, 8.5, 0.18, 12),
    new THREE.MeshStandardMaterial({ color: 0x53665a, roughness: 0.9, flatShading: true })
  );
  inset.position.y = 0.02;
  arenaGroup.add(inset);
  for (let i = 0; i < 8; i++) {
    const a = i / 8 * Math.PI * 2;
    const pillar = new THREE.Group();
    pillar.position.set(Math.cos(a) * 11.5, 0, Math.sin(a) * 11.5);
    makeVoxelBox(pillar, [1.1, 3.2, 1.1], [0, 1.6, 0], 0x4b5a50);
    makeVoxelBox(pillar, [1.5, 0.45, 1.5], [0, 3.4, 0], 0x748b6d);
    const rune = new THREE.Mesh(
      new THREE.BoxGeometry(0.22, 0.75, 0.22),
      new THREE.MeshStandardMaterial({ color: 0x9af0bf, emissive: 0x32975d, emissiveIntensity: 1.5 })
    );
    rune.position.set(0, 1.8, 0.57);
    pillar.add(rune);
    arenaGroup.add(pillar);
  }
  const arenaLight = new THREE.PointLight(0x73e0aa, 1.35, 28, 2);
  arenaLight.position.set(0, 7, 0);
  arenaGroup.add(arenaLight);
  arenaGroup.visible = false;
}

function buildBossModel(img) {
  const width = 32;
  const height = Math.max(8, Math.round(width * img.height / img.width));
  const sampleCanvas = document.createElement('canvas');
  sampleCanvas.width = width;
  sampleCanvas.height = height;
  const context = sampleCanvas.getContext('2d', { willReadFrequently: true });
  context.clearRect(0, 0, width, height);
  context.drawImage(img, 0, 0, width, height);
  const pixels = context.getImageData(0, 0, width, height).data;
  const cell = 3.4 / width;
  const mesh = new THREE.InstancedMesh(
    new THREE.BoxGeometry(1, 1, 1),
    new THREE.MeshStandardMaterial({ roughness: 0.78, metalness: 0.02, flatShading: true, vertexColors: true, emissive: 0x111111 }),
    width * height
  );
  mesh.frustumCulled = false;
  const matrix = new THREE.Matrix4();
  const pos = new THREE.Vector3();
  const scale = new THREE.Vector3();
  const quat = new THREE.Quaternion();
  const color = new THREE.Color();
  let count = 0;
  for (let y = 0; y < height; y++) {
    for (let x = 0; x < width; x++) {
      const i = (y * width + x) * 4;
      if (pixels[i + 3] < 28) continue;
      const r = pixels[i] / 255;
      const g = pixels[i + 1] / 255;
      const b = pixels[i + 2] / 255;
      const luminance = 0.2126 * r + 0.7152 * g + 0.0722 * b;
      const depth = cell * (1.1 + luminance * 1.7);
      pos.set((x - (width - 1) / 2) * cell, ((height - 1) / 2 - y) * cell, depth / 2);
      scale.set(cell * 0.95, cell * 0.95, depth);
      matrix.compose(pos, quat, scale);
      mesh.setMatrixAt(count, matrix);
      color.setRGB(r, g, b);
      mesh.setColorAt(count, color);
      count++;
    }
  }
  mesh.count = count;
  mesh.instanceMatrix.needsUpdate = true;
  if (mesh.instanceColor) mesh.instanceColor.needsUpdate = true;
  const group = new THREE.Group();
  group.add(mesh);
  const scaleBoss = 4.8 / Math.max(height * cell, 3.4);
  group.scale.setScalar(scaleBoss);
  bossRadius = 2.15;
  return group;
}

function clearProjectiles() {
  for (const projectile of [...playerProjectiles, ...bossProjectiles]) scene.remove(projectile.mesh);
  playerProjectiles.length = 0;
  bossProjectiles.length = 0;
}

function enterBoss() {
  if (mode !== 'world' || !bossCatalog.length) return;
  mode = 'boss';
  guarding = false;
  bossHud.hidden = false;
  document.querySelector('#objectiveText').textContent = `Đánh bại ${bossCatalog[activeBoss].name}`;
  document.querySelector('#playerState').textContent = 'CHIẾN ĐẤU';
  document.querySelector('#bossHudName').textContent = bossCatalog[activeBoss].name;
  if (bossGroup) {
    arenaGroup.remove(bossGroup);
    disposeObject(bossGroup);
  }
  bossGroup = buildBossModel(bossCatalog[activeBoss].img);
  bossGroup.position.set(0, 3.45, -6.2);
  arenaGroup.add(bossGroup);
  arenaGroup.visible = true;
  worldGroup.visible = false;
  playerGroup.position.set(0, 0, 7.5);
  playerHp = PLAYER_MAX_HP;
  bossMaxHp = 120 + Math.max(0, activeBoss) * 10;
  bossHp = bossMaxHp;
  playerCooldown = 0;
  bossCooldown = 1;
  clearProjectiles();
  resultOverlay.hidden = true;
  updateHud();
  playTone(480, 0.11);
  showToast(`Hang tinh thể: ${bossCatalog[activeBoss].name} đã xuất hiện`, 2600);
}

function exitBoss() {
  mode = 'world';
  guarding = false;
  arenaGroup.visible = false;
  worldGroup.visible = true;
  bossHud.hidden = true;
  playerGroup.position.set(0, heightAt(0, 12), 12);
  playerHp = PLAYER_MAX_HP;
  document.querySelector('#playerState').textContent = 'ĐANG KHÁM PHÁ';
  document.querySelector('#objectiveText').textContent = 'Tìm cổng hang phía Đông';
  resultOverlay.hidden = true;
  clearProjectiles();
  updateHud();
}

function updateHud() {
  const hpPercent = clamp(playerHp / PLAYER_MAX_HP * 100, 0, 100);
  document.querySelector('#playerHealthFill').style.width = `${hpPercent}%`;
  document.querySelector('#playerHealthText').textContent = `${Math.ceil(playerHp)} / ${PLAYER_MAX_HP}`;
  document.querySelector('#bossHealthFill').style.width = `${clamp(bossHp / bossMaxHp * 100, 0, 100)}%`;
  document.querySelector('#bossHealthText').textContent = `${Math.ceil(bossHp)} / ${bossMaxHp}`;
  document.querySelector('#playerLevel').textContent = String(playerLevel).padStart(2, '0');
  document.querySelector('#blockCount').textContent = `${blocksInPack} khối`;
  document.querySelector('#coordLabel').textContent = `${Math.round(playerGroup?.position.x ?? 0)}, ${Math.round(playerGroup?.position.z ?? 0)}`;
}

function showResult(won) {
  document.querySelector('#resultGlyph').textContent = won ? '✦' : '⟲';
  document.querySelector('#resultTitle').textContent = won ? 'CHIẾN THẮNG' : 'BẠN ĐÃ GỤC NGÃ';
  document.querySelector('#resultText').textContent = won
    ? `${bossCatalog[activeBoss].name} đã bị đánh bại. Bạn nhận được một khối tinh thể.`
    : 'Hãy đổi vị trí, né đòn và dùng cung khi boss ở xa.';
  resultButton.innerHTML = won ? 'TIẾP TỤC KHÁM PHÁ <span>→</span>' : 'HỒI SINH <span>↻</span>';
  resultButton.onclick = () => {
    if (won) {
      playerLevel++;
      blocksInPack++;
      activeBoss = (activeBoss + 1) % bossCatalog.length;
      renderBossList();
    }
    exitBoss();
  };
  resultOverlay.hidden = false;
}

function playTone(frequency, duration = 0.07) {
  if (!audioEnabled) return;
  try {
    audioContext ||= new AudioContext();
    const oscillator = audioContext.createOscillator();
    const gain = audioContext.createGain();
    oscillator.type = 'square';
    oscillator.frequency.value = frequency;
    gain.gain.setValueAtTime(0.045, audioContext.currentTime);
    gain.gain.exponentialRampToValueAtTime(0.001, audioContext.currentTime + duration);
    oscillator.connect(gain);
    gain.connect(audioContext.destination);
    oscillator.start();
    oscillator.stop(audioContext.currentTime + duration);
  } catch { /* Sound is an optional browser feature. */ }
}

function updateCamera(dt = 1 / 60) {
  if (!playerGroup) return;
  const forwardX = Math.sin(yaw);
  const forwardZ = -Math.cos(yaw);
  const distance = mode === 'boss' ? 8.4 : 8.2;
  const height = mode === 'boss' ? 4.6 : 4.4;
  const target = new THREE.Vector3(
    playerGroup.position.x - forwardX * distance,
    playerGroup.position.y + height + jumpOffset * 0.45,
    playerGroup.position.z - forwardZ * distance
  );
  const ease = 1 - Math.pow(0.001, Math.max(0, dt));
  camera.position.lerp(target, ease);
  camera.lookAt(playerGroup.position.x, playerGroup.position.y + 1.2 + jumpOffset * 0.22, playerGroup.position.z);
}

function movementVector() {
  const f = { x: Math.sin(yaw), z: -Math.cos(yaw) };
  const r = { x: Math.cos(yaw), z: Math.sin(yaw) };
  let x = 0;
  let z = 0;
  if (keys.w) { x += f.x; z += f.z; }
  if (keys.s) { x -= f.x; z -= f.z; }
  if (keys.d) { x += r.x; z += r.z; }
  if (keys.a) { x -= r.x; z -= r.z; }
  const length = Math.hypot(x, z);
  if (length > 0) { x /= length; z /= length; }
  return { x, z };
}

const caveEntry = { x: GRID / 2 - 0.7, z: 0 };

function stepWorld(dt) {
  if (!started) return;
  const move = movementVector();
  const speed = keys.shift ? 8.6 : 6.2;
  playerGroup.position.x += move.x * speed * dt;
  playerGroup.position.z += move.z * speed * dt;
  const edge = GRID / 2 - 0.65;
  playerGroup.position.x = clamp(playerGroup.position.x, -edge, edge);
  playerGroup.position.z = clamp(playerGroup.position.z, -edge, edge);
  const floorY = heightAt(playerGroup.position.x, playerGroup.position.z);
  jumpOffset += playerVelocityY * dt;
  playerVelocityY -= 20 * dt;
  if (jumpOffset <= 0) { jumpOffset = 0; playerVelocityY = 0; }
  playerGroup.position.y = floorY + jumpOffset;
  playerGroup.rotation.y = yaw;
  const distance = Math.hypot(playerGroup.position.x - caveEntry.x, playerGroup.position.z - caveEntry.z);
  document.querySelector('#interactPrompt').hidden = distance > 4.4;
  if (distance < 7) document.querySelector('#regionLabel').textContent = 'Hang tinh thể';
  else document.querySelector('#regionLabel').textContent = 'Thung lũng rêu';
}

function makeProjectile(colorHex, size, length = size) {
  const mesh = new THREE.Mesh(
    new THREE.BoxGeometry(size, size, length),
    new THREE.MeshStandardMaterial({ color: colorHex, emissive: colorHex, emissiveIntensity: 0.7, roughness: 0.4, flatShading: true })
  );
  scene.add(mesh);
  return mesh;
}

function fireArrow() {
  if (!bossGroup || playerCooldown > 0) return;
  const from = playerGroup.position.clone().add(new THREE.Vector3(0, 1.55, 0));
  const to = bossGroup.position.clone().add(new THREE.Vector3(0, 1.1, 0));
  const direction = to.sub(from).normalize();
  const mesh = makeProjectile(0xc5f2ac, 0.14, 0.82);
  mesh.position.copy(from).addScaledVector(direction, 0.95);
  mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 0, 1), direction);
  playerProjectiles.push({ mesh, velocity: direction.multiplyScalar(24), damage: 16 });
  playerCooldown = 0.52;
  playTone(730, 0.07);
  document.querySelector('#crosshair').classList.add('active');
  setTimeout(() => document.querySelector('#crosshair').classList.remove('active'), 120);
}

function swingSword() {
  if (!bossGroup || playerCooldown > 0) return;
  const distance = new THREE.Vector2(playerGroup.position.x - bossGroup.position.x, playerGroup.position.z - bossGroup.position.z).length();
  if (distance > 3.7) {
    showToast('Tiến lại gần để chém, hoặc đổi sang cung bằng phím 2');
    playerCooldown = 0.22;
    return;
  }
  bossHp = Math.max(0, bossHp - 18);
  playerCooldown = 0.48;
  bossGroup.position.x += (bossGroup.position.x - playerGroup.position.x) * 0.08;
  playTone(240, 0.12);
  showToast('Trúng đòn · Boss mất 18 máu', 850);
  updateHud();
  if (bossHp <= 0) {
    showResult(true);
    return;
  }
  document.querySelector('#crosshair').classList.add('active');
  setTimeout(() => document.querySelector('#crosshair').classList.remove('active'), 150);
}

function findWorldHit(clientX = currentPointer.x, clientY = currentPointer.y) {
  const rect = canvas.getBoundingClientRect();
  const pointer = new THREE.Vector2(
    ((clientX - rect.left) / rect.width) * 2 - 1,
    -((clientY - rect.top) / rect.height) * 2 + 1
  );
  const raycaster = new THREE.Raycaster();
  raycaster.setFromCamera(pointer, camera);
  const hits = raycaster.intersectObject(terrainMesh, false);
  return hits[0] || null;
}

function mineBlock(clientX, clientY) {
  if (!terrainMesh) return;
  const hit = findWorldHit(clientX, clientY);
  if (!hit || hit.instanceId === undefined) {
    showToast('Nhìn vào một khối địa hình để đào');
    return;
  }
  const record = blockRecords[hit.instanceId];
  if (!record || record.removed) return;
  const pos = new THREE.Vector3();
  const quat = new THREE.Quaternion();
  const scale = new THREE.Vector3(0, 0, 0);
  const matrix = new THREE.Matrix4().compose(pos, quat, scale);
  terrainMesh.setMatrixAt(hit.instanceId, matrix);
  terrainMesh.instanceMatrix.needsUpdate = true;
  record.removed = true;
  if (record.top) terrainHeights[record.gz * GRID + record.gx] = Math.max(1, record.level);
  blocksInPack++;
  updateHud();
  playTone(160, 0.05);
  showToast('Đã đào được 1 khối');
}

function placeBlock() {
  if (!terrainMesh || blocksInPack < 1) {
    showToast('Bạn đã hết khối để đặt');
    return;
  }
  const hit = findWorldHit();
  if (!hit) { showToast('Nhắm vào mặt đất để đặt khối'); return; }
  const x = Math.round(hit.point.x);
  const z = Math.round(hit.point.z);
  const y = Math.floor(hit.point.y) + 1.5;
  const block = new THREE.Mesh(
    new THREE.BoxGeometry(1, 1, 1),
    new THREE.MeshStandardMaterial({ color: 0x729c58, roughness: 0.98, flatShading: true })
  );
  block.position.set(x, y, z);
  block.castShadow = true;
  worldGroup.add(block);
  placedBlocks.push(block);
  blocksInPack--;
  updateHud();
  playTone(320, 0.05);
}

function primaryAction(clientX, clientY) {
  if (!started) return;
  if (mode === 'boss') {
    if (selectedSlot === 2) fireArrow();
    else if (selectedSlot === 1) swingSword();
    else showToast('Chọn kiếm (1) hoặc cung (2) để tấn công');
  } else if (selectedSlot === 3) {
    mineBlock(clientX, clientY);
  } else if (selectedSlot === 1) {
    showToast('Chọn cuốc chim (3) để đào khối');
  }
}

function bossAttack() {
  if (!bossGroup || bossCooldown > 0 || mode !== 'boss') return;
  const origin = bossGroup.position.clone().add(new THREE.Vector3(0, 1.1, 0));
  const target = playerGroup.position.clone().add(new THREE.Vector3(0, 1.15, 0));
  const direction = target.sub(origin).normalize();
  const mesh = makeProjectile(0xff8b67, 0.4, 0.55);
  mesh.position.copy(origin).addScaledVector(direction, 1.2);
  mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 0, 1), direction);
  bossProjectiles.push({ mesh, velocity: direction.multiplyScalar(9.2), damage: guarding ? 5 : 11 });
  bossCooldown = 1.65;
}

function stepBoss(dt) {
  if (!started) return;
  const move = movementVector();
  playerGroup.position.x += move.x * 6.8 * dt;
  playerGroup.position.z += move.z * 6.8 * dt;
  playerGroup.position.x = clamp(playerGroup.position.x, -10.2, 10.2);
  playerGroup.position.z = clamp(playerGroup.position.z, -1.5, 12.2);
  jumpOffset += playerVelocityY * dt;
  playerVelocityY -= 20 * dt;
  if (jumpOffset <= 0) { jumpOffset = 0; playerVelocityY = 0; }
  playerGroup.position.y = jumpOffset;
  playerGroup.rotation.y = yaw;
  playerCooldown -= dt;
  bossCooldown -= dt;
  bossAttack();
  if (bossGroup) {
    bossGroup.position.y = 3.45 + Math.sin(elapsed * 1.45) * 0.3;
    bossGroup.position.x = Math.sin(elapsed * 0.34) * 0.85;
    bossGroup.rotation.y = Math.sin(elapsed * 0.3) * 0.08;
  }
  stepProjectiles(dt);
  updateHud();
}

function stepProjectiles(dt) {
  for (let i = playerProjectiles.length - 1; i >= 0; i--) {
    const projectile = playerProjectiles[i];
    projectile.mesh.position.addScaledVector(projectile.velocity, dt);
    if (bossGroup && projectile.mesh.position.distanceTo(bossGroup.position.clone().add(new THREE.Vector3(0, 1, 0))) < bossRadius) {
      bossHp = Math.max(0, bossHp - projectile.damage);
      scene.remove(projectile.mesh);
      playerProjectiles.splice(i, 1);
      playTone(510, 0.06);
      if (bossHp <= 0) showResult(true);
    } else if (projectile.mesh.position.length() > 40) {
      scene.remove(projectile.mesh);
      playerProjectiles.splice(i, 1);
    }
  }
  for (let i = bossProjectiles.length - 1; i >= 0; i--) {
    const projectile = bossProjectiles[i];
    projectile.mesh.position.addScaledVector(projectile.velocity, dt);
    if (projectile.mesh.position.distanceTo(playerGroup.position.clone().add(new THREE.Vector3(0, 1.25 + jumpOffset, 0))) < 0.85) {
      const damage = guarding ? 3 : projectile.damage;
      playerHp = Math.max(0, playerHp - damage);
      scene.remove(projectile.mesh);
      bossProjectiles.splice(i, 1);
      playTone(115, 0.08);
      showToast(guarding ? 'Đỡ đòn thành công' : `Bạn mất ${damage} máu`, 900);
      if (playerHp <= 0) showResult(false);
    } else if (projectile.mesh.position.length() > 40) {
      scene.remove(projectile.mesh);
      bossProjectiles.splice(i, 1);
    }
  }
}

function selectSlot(slot) {
  selectedSlot = slot;
  document.querySelectorAll('.hotbar-slot').forEach(button => button.classList.toggle('selected', Number(button.dataset.slot) === slot));
  const labels = { 1: 'Kiếm gỗ', 2: 'Cung', 3: 'Cuốc chim', 4: 'Khối rêu' };
  document.querySelector('#toolLabel').textContent = labels[slot];
}

function addBossImage(img, name, url) {
  bossCatalog.push({ img, name: name.replace(/\.[^.]+$/, '').slice(0, 22) || `Boss ${bossCatalog.length + 1}`, url });
  renderBossList();
}

function renderBossList() {
  bossList.replaceChildren();
  bossCatalog.forEach((boss, index) => {
    const button = document.createElement('button');
    button.className = `boss-chip${index === activeBoss ? ' selected' : ''}`;
    button.type = 'button';
    button.title = boss.name;
    button.setAttribute('aria-label', `Chọn boss ${boss.name}`);
    const image = document.createElement('img');
    image.src = boss.url;
    image.alt = '';
    const name = document.createElement('span');
    name.textContent = boss.name;
    button.append(image, name);
    button.addEventListener('click', () => {
      if (mode === 'boss') {
        showToast('Hãy kết thúc trận hoặc nhấn ESC để đổi boss.');
        return;
      }
      activeBoss = index;
      renderBossList();
      showToast(`Đã chọn boss: ${boss.name}`);
    });
    bossList.append(button);
  });
  const add = document.createElement('label');
  add.className = 'boss-chip boss-chip-more';
  add.htmlFor = 'bossImageInput';
  add.title = 'Thêm ảnh boss';
  add.textContent = '+';
  bossList.append(add);
  bossCount.textContent = String(bossCatalog.length).padStart(2, '0');
}

function bindInputs() {
  worldImageInput.addEventListener('change', async event => {
    const file = event.target.files?.[0];
    if (!file) return;
    try {
      const url = URL.createObjectURL(file);
      const img = await loadImage(url);
      worldImage = img;
      if (worldImageObjectUrl) URL.revokeObjectURL(worldImageObjectUrl);
      worldImageObjectUrl = url;
      worldPreview.src = url;
      worldImageName.textContent = file.name;
      setImagePixels(img);
      buildTerrain();
      if (playerGroup) playerGroup.position.y = heightAt(playerGroup.position.x, playerGroup.position.z) + jumpOffset;
      showToast('Đã tạo lại địa hình từ ảnh mới');
    } catch (error) {
      showToast(error.message || 'Không thể đọc ảnh này');
    }
    event.target.value = '';
  });

  bossImageInput.addEventListener('change', async event => {
    const files = [...(event.target.files || [])].filter(file => file.type.startsWith('image/'));
    for (const file of files) {
      if (bossCatalog.length >= 12) { showToast('Bộ sưu tập hỗ trợ tối đa 12 boss'); break; }
      const url = URL.createObjectURL(file);
      try {
        addBossImage(await loadImage(url), file.name, url);
      } catch {
        URL.revokeObjectURL(url);
        showToast(`Không đọc được ảnh ${file.name}`);
      }
    }
    event.target.value = '';
  });

  document.querySelector('#startButton').addEventListener('click', () => {
    started = true;
    welcomeOverlay.hidden = true;
    showToast('Thế giới đã sẵn sàng · Tìm cổng hang phát sáng ở phía Đông', 2800);
  });
  document.querySelector('#helpToggle').addEventListener('click', () => controlsCard.classList.toggle('collapsed'));
  document.querySelector('#closeHelp').addEventListener('click', () => controlsCard.classList.add('collapsed'));
  document.querySelector('#soundToggle').addEventListener('click', event => {
    audioEnabled = !audioEnabled;
    event.currentTarget.classList.toggle('sound-on', audioEnabled);
    event.currentTarget.title = audioEnabled ? 'Tắt âm thanh' : 'Bật âm thanh';
    if (audioEnabled) playTone(520, 0.1);
    showToast(audioEnabled ? 'Âm thanh đã bật' : 'Âm thanh đã tắt', 900);
  });
  document.querySelectorAll('.hotbar-slot').forEach(button => button.addEventListener('click', () => selectSlot(Number(button.dataset.slot))));

  window.addEventListener('keydown', event => {
    const key = event.key.toLowerCase();
    if (key in keys) keys[key] = true;
    if (key === ' ') {
      keys.space = true;
      event.preventDefault();
      if (started && jumpOffset <= 0.02) playerVelocityY = mode === 'boss' ? 8.2 : 8;
    }
    if (key >= '1' && key <= '4') selectSlot(Number(key));
    if (key === 'e' && started && mode === 'world') {
      const d = Math.hypot(playerGroup.position.x - caveEntry.x, playerGroup.position.z - caveEntry.z);
      if (d <= 4.4) enterBoss();
      else showToast('Cổng hang đang ở phía Đông của bản đồ');
    }
    if (key === 'escape' && mode === 'boss') exitBoss();
  });
  window.addEventListener('keyup', event => {
    const key = event.key.toLowerCase();
    if (key in keys) keys[key] = false;
    if (key === ' ') keys.space = false;
    if (key === 'shift') keys.shift = false;
  });
  window.addEventListener('blur', () => {
    Object.keys(keys).forEach(key => { keys[key] = false; });
    guarding = false;
  });
  canvas.addEventListener('contextmenu', event => event.preventDefault());
  canvas.addEventListener('pointerdown', event => {
    currentPointer = { x: event.clientX, y: event.clientY };
    if (event.button === 2) {
      if (mode === 'boss') {
        guarding = true;
        document.querySelector('#playerState').textContent = 'ĐANG ĐỠ ĐÒN';
      } else if (started && selectedSlot === 4) {
        placeBlock();
      }
      return;
    }
    if (event.button === 0 && started) {
      pointerHeld = true;
      pointerDragged = false;
      pointerStart = { x: event.clientX, y: event.clientY };
    }
  });
  window.addEventListener('pointermove', event => {
    currentPointer = { x: event.clientX, y: event.clientY };
    if (!pointerHeld) return;
    const dx = event.clientX - pointerStart.x;
    const dy = event.clientY - pointerStart.y;
    if (Math.abs(dx) + Math.abs(dy) > 4) pointerDragged = true;
    if (pointerDragged) {
      yaw += dx * 0.0045;
      pointerStart = { x: event.clientX, y: event.clientY };
    }
  });
  window.addEventListener('pointerup', event => {
    if (event.button === 2) {
      guarding = false;
      if (mode === 'boss') document.querySelector('#playerState').textContent = 'CHIẾN ĐẤU';
    }
    if (event.button === 0 && pointerHeld) {
      if (!pointerDragged) primaryAction(event.clientX, event.clientY);
      pointerHeld = false;
    }
  });
}

function renderFrame(timestamp) {
  requestAnimationFrame(renderFrame);
  const dt = Math.min(0.05, Math.max(0, (timestamp - (lastTimestamp || timestamp)) / 1000));
  lastTimestamp = timestamp;
  elapsed += dt;
  if (mode === 'world') stepWorld(dt);
  else stepBoss(dt);
  updateCamera(dt || 1 / 60);
  if (renderer && scene && camera) renderer.render(scene, camera);
}

async function boot() {
  try {
    THREE = await import('three');
    renderer = new THREE.WebGLRenderer({ canvas, antialias: true, powerPreference: 'high-performance' });
  } catch (error) {
    console.error(error);
    document.querySelector('#loadFallback').hidden = false;
    return;
  }

  renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.75));
  renderer.setSize(window.innerWidth, window.innerHeight);
  renderer.shadowMap.enabled = true;
  renderer.shadowMap.type = THREE.PCFSoftShadowMap;
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.15;

  scene = new THREE.Scene();
  scene.background = new THREE.Color(0x8eae9f);
  scene.fog = new THREE.FogExp2(0x8eae9f, 0.014);
  camera = new THREE.PerspectiveCamera(57, window.innerWidth / window.innerHeight, 0.1, 160);
  const skyLight = new THREE.HemisphereLight(0xe8f4df, 0x38473d, 1.25);
  scene.add(skyLight);
  const sun = new THREE.DirectionalLight(0xffefcf, 2.15);
  sun.position.set(-18, 32, 16);
  sun.castShadow = true;
  sun.shadow.mapSize.set(1024, 1024);
  sun.shadow.camera.left = -34;
  sun.shadow.camera.right = 34;
  sun.shadow.camera.top = 34;
  sun.shadow.camera.bottom = -34;
  scene.add(sun);
  worldGroup = new THREE.Group();
  arenaGroup = new THREE.Group();
  scene.add(worldGroup, arenaGroup);

  try {
    worldImage = await loadImage(DEFAULT_IMAGE);
    worldPreview.src = DEFAULT_IMAGE;
    const defaultBossImage = await loadImage(DEFAULT_IMAGE);
    addBossImage(defaultBossImage, 'Kẻ canh hang', DEFAULT_IMAGE);
  } catch (error) {
    console.error(error);
    document.querySelector('#loadFallback').hidden = false;
    return;
  }
  setImagePixels(worldImage);
  buildTerrain();
  buildPlayer();
  buildArena();
  bindInputs();
  updateHud();
  updateCamera(1);
  window.addEventListener('resize', () => {
    camera.aspect = window.innerWidth / window.innerHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(window.innerWidth, window.innerHeight);
  });
  requestAnimationFrame(renderFrame);
}

boot();

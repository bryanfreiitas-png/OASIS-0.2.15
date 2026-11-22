import express from 'express';
import http from 'http';
import fs from 'fs';
import path from 'path';
import { WebSocketServer, WebSocket } from 'ws';
import { fileURLToPath } from 'url';
import {
  CATALOG_ITEMS,
  DEFAULT_FLOOR_STYLE_ID,
  DEFAULT_WALL_STYLE_ID,
  FLOOR_BLOCK_PACKS,
  FLOOR_STYLES,
  GEM_PACKAGES,
  LOT_PURCHASE_PRICES,
  MAX_PLAYER_LOTS,
  MAX_PLOT_GRID_BLOCKS,
  MIN_PLOT_BUILD_BLOCKS,
  STARTER_PLOT_MAX_BLOCKS,
  SURVIVAL_CONFIG,
  WALL_STYLES,
  createInitialNeeds,
  createInitialQuests,
  createInitialRoutineTasks,
  createStarterPlotTiles,
  formatEspacoRoomKey,
  parseEspacoRoomKey,
  QUALITY_META,
  getCatalogItem,
} from './src/shared/catalog.ts';
import { getFurnitureFootprint } from './src/shared/furnitureLayout.ts';
import { getPracaReturnSpawnNormalized } from './src/maps/praca/interactives.ts';
import { getForagingSpawnNormalized } from './src/maps/foraging/collisions.ts';
import { LIVE_TRADE_MAX_SLOTS } from './src/shared/types.ts';
import { PLOT_GRID_SIZE } from './src/shared/wallUtils.ts';
import type {
  ActionId,
  AvatarConfig,
  ChatMessage,
  Direction,
  EconomyConfig,
  ExpressionId,
  LiveTradeSession,
  LotAccessMode,
  MarketListing,
  MarketTransaction,
  PlacedFurniture,
  PlayerLot,
  PlayerNeeds,
  PlayerProfile,
  ProfessionId,
  PublicLotDirectoryEntry,
  ResourceNodeState,
  RoomTheme,
  SpaceInfoPayload,
  TradeOffer,
  WorldPlayer,
} from './src/shared/types.ts';
import {
  ENABLE_BLACK_MARKET,
  PROFESSIONS_META,
  PROFESSION_IDS,
  getAvailableProfessionSlots,
  getBlackMarketUnitPrice,
  getNextUnlockTotalLevel,
  getProfessionBonuses,
  getProfessionSkill,
  getUnlockedProfessionIds,
  rollGatherQuality,
} from './src/shared/professions.ts';
import {
  addItemToInventory,
  applyProfessionXp,
  canUseTool,
  consumeInventoryInstance,
  consumeInventoryItemById,
  countInventoryItem,
  ensureEconomyConfig,
  ensurePlayerResourceNodes,
  ensureProfessionProfile,
  getEffectiveMarketTaxRate,
  getEffectiveRepairCost,
  getItemQuantity,
  getNodeDefById,
  getRecipeById,
  isPlayerWithinNodeRange,
  resolveEquippedTool,
  rollCraftQuality,
  rollRangeInt,
  syncWorldPlayerProfession,
  tickResourceNodes,
} from './src/server/professionEngine.ts';
import { pruneWallOverridesForTiles, sanitizeWallEdgeList } from './src/shared/wallUtils.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);

const DATA_FILE = path.join(__dirname, 'oasis-world-state.json');

interface PersistedState {
  profiles: Record<string, PlayerProfile>;
  marketListings: MarketListing[];
  marketHistory: MarketTransaction[];
  economyConfig: EconomyConfig;
  trades: Record<string, TradeOffer>;
}

const DEFAULT_CHAT_SEED: Record<string, ChatMessage[]> = {
  praca: [
    {
      id: 'seed_welcome',
      roomKey: 'praca',
      senderId: 'sistema',
      senderName: 'OASIS',
      senderColor: '#fbbf24',
      text: 'Bem-vindo à Praça Central! Clique na calçada ou use WASD para andar.',
      type: 'system',
      timestamp: Date.now() - 60000,
    },
  ],
  balada: [],
  cafeteria: [],
  mercado: [],
};

function createInitialPersistedState(): PersistedState {
  return {
    profiles: {},
    marketListings: [
      {
        listingId: 'lst_seed_sofa',
        sellerId: 'bazar_oasis',
        sellerName: 'Bazar OASIS',
        itemId: 'rust_02',
        instanceId: 'seed_inst_sofa',
        priceCoins: 245,
        quantity: 1,
        unitPriceCoins: 245,
        createdAt: Date.now() - 360000,
      },
      {
        listingId: 'lst_seed_arcade',
        sellerId: 'bazar_oasis',
        sellerName: 'Bazar OASIS',
        itemId: 'neon_21',
        instanceId: 'seed_inst_arcade',
        priceCoins: 450,
        quantity: 1,
        unitPriceCoins: 450,
        createdAt: Date.now() - 240000,
      },
      {
        listingId: 'lst_seed_jacket',
        sellerId: 'bazar_oasis',
        sellerName: 'Bazar OASIS',
        itemId: 'shirt_jaqueta_cyber',
        instanceId: 'seed_inst_jacket',
        priceCoins: 215,
        quantity: 1,
        unitPriceCoins: 215,
        createdAt: Date.now() - 120000,
      },
    ],
    marketHistory: [],
    economyConfig: ensureEconomyConfig(),
    trades: {},
  };
}

let state: PersistedState = createInitialPersistedState();
try {
  if (fs.existsSync(DATA_FILE)) {
    const raw = fs.readFileSync(DATA_FILE, 'utf-8');
    const parsed = JSON.parse(raw) as PersistedState;
    if (parsed && parsed.profiles) {
      state = {
        ...createInitialPersistedState(),
        ...parsed,
        marketHistory: Array.isArray(parsed.marketHistory) ? parsed.marketHistory : [],
        economyConfig: ensureEconomyConfig(parsed.economyConfig),
      };
    }
  }
} catch (err) {
  console.error('Failed to load persisted state, using defaults:', err);
}
const lastGatherAtByPlayer = new Map<string, number>();

let saveTimer: NodeJS.Timeout | null = null;
function scheduleSave() {
  if (saveTimer) clearTimeout(saveTimer);
  saveTimer = setTimeout(() => {
    try {
      fs.writeFileSync(DATA_FILE, JSON.stringify(state, null, 2), 'utf-8');
    } catch (err) {
      console.error('Error saving state:', err);
    }
  }, 400);
}

// Ephemeral live session state
const roomChats: Record<string, ChatMessage[]> = { ...DEFAULT_CHAT_SEED };
const activePlayers = new Map<string, WorldPlayer>();
const socketsByPlayer = new Map<string, WebSocket>();
const playerBySocket = new Map<WebSocket, string>();
const liveTradeSessions = new Map<string, LiveTradeSession>();
// roomKey -> (seatId -> playerId)
const seatOccupancies = new Map<string, Map<string, string>>();

function getRoomSeatsPayload(roomKey: string): Record<string, string> {
  const m = seatOccupancies.get(roomKey);
  if (!m) return {};
  const out: Record<string, string> = {};
  for (const [seatId, pid] of m.entries()) {
    const occupant = activePlayers.get(pid);
    if (occupant && occupant.roomKey === roomKey) {
      out[seatId] = pid;
    } else {
      m.delete(seatId);
    }
  }
  return out;
}

function releasePlayerSeats(playerId: string, broadcast = true): void {
  for (const [roomKey, roomSeats] of seatOccupancies.entries()) {
    let changed = false;
    for (const [seatId, pid] of roomSeats.entries()) {
      if (pid === playerId) {
        roomSeats.delete(seatId);
        changed = true;
      }
    }
    if (changed && broadcast) {
      broadcastToRoom(roomKey, {
        type: 'room:seats',
        payload: { roomKey, seats: getRoomSeatsPayload(roomKey) },
      });
    }
  }
}

type NeedKey = keyof PlayerNeeds;
interface SurvivalRuntime {
  exact: Record<NeedKey, number>;
  notified: Record<NeedKey, { t50: boolean; t25: boolean; t5: boolean }>;
  restFullNotified: boolean;
}
const survivalRuntimes = new Map<string, SurvivalRuntime>();

function clampStat(v: number): number {
  return Math.max(0, Math.min(100, Math.round(v)));
}

function clampFloat(v: number): number {
  return Math.max(0, Math.min(100, v));
}

function getOrCreateRuntime(profile: PlayerProfile): SurvivalRuntime {
  let rt = survivalRuntimes.get(profile.id);
  if (!rt) {
    const n = profile.needs || createInitialNeeds();
    rt = {
      exact: {
        energia: clampFloat(n.energia),
        fome: clampFloat(n.fome),
        diversao: clampFloat(n.diversao),
        higiene: clampFloat(n.higiene),
      },
      notified: {
        energia: { t50: n.energia <= 50, t25: n.energia <= 25, t5: n.energia <= 5 },
        fome: { t50: n.fome <= 50, t25: n.fome <= 25, t5: n.fome <= 5 },
        diversao: { t50: n.diversao <= 50, t25: n.diversao <= 25, t5: n.diversao <= 5 },
        higiene: { t50: n.higiene <= 50, t25: n.higiene <= 25, t5: n.higiene <= 5 },
      },
      restFullNotified: n.energia >= 100,
    };
    survivalRuntimes.set(profile.id, rt);
  }
  return rt;
}

function getEnergyCostMultiplier(profile: PlayerProfile): number {
  const rt = getOrCreateRuntime(profile);
  return rt.exact.fome <= SURVIVAL_CONFIG.HUNGRY_PENALTY_THRESHOLD
    ? SURVIVAL_CONFIG.HUNGRY_PENALTY_MULTIPLIER
    : 1;
}

function sendNeedThresholdAlert(ws: WebSocket | undefined, key: NeedKey, threshold: 50 | 25 | 5) {
  if (!ws) return;
  const messages: Record<NeedKey, Record<50 | 25 | 5, string>> = {
    energia: {
      50: '⚡ Energia em 50%! Lembre-se de descansar na cama.',
      25: '⚠️ Energia baixa (25%)! Vá para sua cama antes de apagar.',
      5: '🚨 ENERGIA CRÍTICA (5%)! Você vai apagar se zerar por 10s!',
    },
    fome: {
      50: '🍽️ Fome em 50%! Agora tudo gasta +25% de Energia e Diversão!',
      25: '⚠️ Fome em 25%! Procure comida antes de desmaiar.',
      5: '🚨 FOME CRÍTICA (5%)! Você vai desmaiar se zerar por 10s!',
    },
    diversao: {
      50: '🎉 Diversão em 50%! Sente num banco, vá à Balada ou regue plantas.',
      25: '⚠️ Diversão baixa (25%)! Faça uma atividade divertida.',
      5: '🚨 Diversão crítica (5%)! Seu humor está no limite!',
    },
    higiene: {
      50: '🧼 Higiene em 50%! Arrume a casa ou renove o visual.',
      25: '⚠️ Higiene baixa (25%)!',
      5: '🚨 Higiene crítica (5%)!',
    },
  };
  const kind = threshold === 5 ? 'error' : 'info';
  sendJson(ws, {
    type: 'toast',
    payload: { message: messages[key][threshold], kind },
  });
  sendJson(ws, {
    type: 'need:alert',
    payload: { need: key, threshold, message: messages[key][threshold] },
  });
}

function setNeedValue(profile: PlayerProfile, key: NeedKey, nextRaw: number) {
  if (profile.godMode && nextRaw < 100) {
    nextRaw = 100;
  }
  const rt = getOrCreateRuntime(profile);
  const oldVal = rt.exact[key];
  const newVal = clampFloat(nextRaw);
  rt.exact[key] = newVal;
  profile.needs[key] = clampStat(newVal);

  const flags = rt.notified[key];
  if (newVal > 50) flags.t50 = false;
  if (newVal > 25) flags.t25 = false;
  if (newVal > 5) flags.t5 = false;

  if (key === 'energia' && newVal < 100) {
    rt.restFullNotified = false;
  }

  const ws = socketsByPlayer.get(profile.id);
  if (oldVal > 50 && newVal <= 50 && !flags.t50) {
    flags.t50 = true;
    sendNeedThresholdAlert(ws, key, 50);
  }
  if (oldVal > 25 && newVal <= 25 && !flags.t25) {
    flags.t25 = true;
    sendNeedThresholdAlert(ws, key, 25);
  }
  if (oldVal > 5 && newVal <= 5 && !flags.t5) {
    flags.t5 = true;
    sendNeedThresholdAlert(ws, key, 5);
  }
}

function addNeedDelta(profile: PlayerProfile, key: NeedKey, delta: number) {
  if (profile.godMode && delta < 0) return;
  const rt = getOrCreateRuntime(profile);
  setNeedValue(profile, key, rt.exact[key] + delta);
}

const LEGACY_FURN_MAP: Record<string, string> = {
  furn_sofa_raro: 'rust_02',
  furn_sofa_neon: 'neon_02',
  furn_cama_oasis: 'rust_03',
  furn_mesa_centro: 'rust_05',
  furn_planta: 'rust_30',
  furn_fliperama: 'neon_21',
  furn_luminaria: 'neon_40',
  furn_mesa_dj: 'neon_24',
  furn_tapete: 'rust_41',
};

function pickWalkableEspacoTile(
  plotTiles: string[],
  furniture: PlacedFurniture[]
): { x: number; y: number } {
  const isFree = (tx: number, ty: number) =>
    !furniture.some((f) => {
      if (f.x !== tx || f.y !== ty) return false;
      const cat = getCatalogItem(f.itemId);
      return Boolean(cat && cat.shape !== 'rug');
    });
  if (!plotTiles || plotTiles.length === 0) {
    for (let r = 0; r < PLOT_GRID_SIZE; r++) {
      const cx = 8;
      const cy = Math.min(PLOT_GRID_SIZE - 1, 8 + (r % 2 === 0 ? Math.floor(r / 2) : -Math.ceil(r / 2)));
      if (isFree(cx, cy)) return { x: cx, y: cy };
    }
    return { x: 8, y: 8 };
  }
  const parsed = plotTiles
    .map((key) => {
      const [xs, ys] = key.split(',');
      return { x: Number(xs), y: Number(ys), key };
    })
    .filter((t) => Number.isFinite(t.x) && Number.isFinite(t.y));
  if (parsed.length === 0) return { x: 8, y: 8 };

  const avgX = parsed.reduce((acc, t) => acc + t.x, 0) / parsed.length;
  const avgY = parsed.reduce((acc, t) => acc + t.y, 0) / parsed.length;
  const sorted = [...parsed].sort(
    (a, b) => Math.hypot(a.x - avgX, a.y - avgY) - Math.hypot(b.x - avgX, b.y - avgY)
  );
  const free = sorted.find(
    (t) =>
      !furniture.some((f) => {
        if (f.x !== t.x || f.y !== t.y) return false;
        const cat = getCatalogItem(f.itemId);
        return Boolean(cat && cat.shape !== 'rug');
      })
  );
  const picked = free || sorted[0];
  return { x: picked.x, y: picked.y };
}

function getProfileLot(profile: PlayerProfile, lotIndex = 1): PlayerLot | undefined {
  if (!Array.isArray(profile.lots)) return undefined;
  return profile.lots.find((l) => l.lotIndex === lotIndex);
}

function syncLegacyFieldsFromLot1(profile: PlayerProfile): void {
  const lot1 = getProfileLot(profile, 1);
  if (!lot1) return;
  profile.roomFurniture = lot1.furniture;
  profile.roomTheme = lot1.theme;
  profile.hasBuiltSpace = Boolean(lot1.hasBuiltSpace);
  profile.floorStyleId = lot1.floorStyleId;
  profile.wallStyleId = lot1.wallStyleId;
  profile.plotTiles = lot1.plotTiles;
  profile.plotMaxBlocks = lot1.plotMaxBlocks;
  profile.wallAdded = lot1.wallAdded;
  profile.wallRemoved = lot1.wallRemoved;
  if (lot1.lastBedPos !== undefined) {
    profile.lastBedPos = lot1.lastBedPos;
  }
}

function resolveTargetOwnedLot(profile: PlayerProfile, worldPlayer?: WorldPlayer): PlayerLot {
  ensureProfileFields(profile);
  const parsed = worldPlayer ? parseEspacoRoomKey(worldPlayer.roomKey) : null;
  if (parsed && parsed.ownerId === profile.id) {
    const inside = getProfileLot(profile, parsed.lotIndex);
    if (inside) return inside;
  }
  return (
    getProfileLot(profile, profile.activeLotIndex || 1) ||
    getProfileLot(profile, 1) ||
    profile.lots![0]
  );
}

function removeFurnitureFromAllLots(profile: PlayerProfile, instanceId: string): number[] {
  ensureProfileFields(profile);
  const changedLotIndices: number[] = [];
  for (const lot of profile.lots || []) {
    const before = lot.furniture.length;
    if (before === 0) continue;
    lot.furniture = lot.furniture.filter((f) => f.instanceId !== instanceId);
    if (lot.furniture.length !== before) {
      changedLotIndices.push(lot.lotIndex);
      const anotherBed = lot.furniture.find((f) => getCatalogItem(f.itemId)?.shape === 'bed');
      lot.lastBedPos = anotherBed
        ? { x: anotherBed.x, y: anotherBed.y, itemId: anotherBed.itemId }
        : null;
    }
  }
  profile.roomFurniture = profile.roomFurniture.filter((f) => f.instanceId !== instanceId);
  syncLegacyFieldsFromLot1(profile);
  return changedLotIndices;
}

function ensureProfileFields(profile: PlayerProfile): PlayerProfile {
  if (profile.hasBuiltSpace === undefined) {
    profile.hasBuiltSpace = Array.isArray(profile.plotTiles) && profile.plotTiles.length > 0;
  }
  if (!Array.isArray(profile.plotTiles)) {
    profile.plotTiles = [];
  }
  if (!profile.plotMaxBlocks || profile.plotMaxBlocks < STARTER_PLOT_MAX_BLOCKS) {
    profile.plotMaxBlocks = STARTER_PLOT_MAX_BLOCKS;
  }
  const tileSet = new Set(profile.plotTiles);
  const prunedWalls = pruneWallOverridesForTiles(
    tileSet,
    Array.isArray(profile.wallAdded) ? profile.wallAdded : [],
    Array.isArray(profile.wallRemoved) ? profile.wallRemoved : []
  );
  profile.wallAdded = prunedWalls.wallAdded;
  profile.wallRemoved = prunedWalls.wallRemoved;
  if (!profile.floorStyleId) {
    const legacyFloorMap: Record<RoomTheme, string> = {
      madeira_classica: DEFAULT_FLOOR_STYLE_ID,
      neon_roxo: 'piso_neon_roxo',
      praia_areia: 'piso_bege_areia',
      marmore_luxo: 'piso_marmore_branco',
    };
    profile.floorStyleId = legacyFloorMap[profile.roomTheme] || DEFAULT_FLOOR_STYLE_ID;
  }
  if (!profile.wallStyleId) {
    const legacyWallMap: Record<RoomTheme, string> = {
      madeira_classica: DEFAULT_WALL_STYLE_ID,
      neon_roxo: 'parede_roxo_cyber',
      praia_areia: 'parede_azul_ceu',
      marmore_luxo: 'parede_grafite_escuro',
    };
    profile.wallStyleId = legacyWallMap[profile.roomTheme] || DEFAULT_WALL_STYLE_ID;
  }
  if (!Array.isArray(profile.ownedFloorStyles) || profile.ownedFloorStyles.length === 0) {
    profile.ownedFloorStyles = Array.from(new Set([DEFAULT_FLOOR_STYLE_ID, profile.floorStyleId]));
  } else if (!profile.ownedFloorStyles.includes(DEFAULT_FLOOR_STYLE_ID)) {
    profile.ownedFloorStyles.unshift(DEFAULT_FLOOR_STYLE_ID);
  }
  if (!Array.isArray(profile.ownedWallStyles) || profile.ownedWallStyles.length === 0) {
    profile.ownedWallStyles = Array.from(new Set([DEFAULT_WALL_STYLE_ID, profile.wallStyleId]));
  } else if (!profile.ownedWallStyles.includes(DEFAULT_WALL_STYLE_ID)) {
    profile.ownedWallStyles.unshift(DEFAULT_WALL_STYLE_ID);
  }
  if (!profile.needs) {
    profile.needs = createInitialNeeds();
  }
  if (!Array.isArray(profile.routineTasks) || profile.routineTasks.length === 0) {
    profile.routineTasks = createInitialRoutineTasks();
  }
  if (!profile.lastMealAt) {
    profile.lastMealAt = Date.now();
  }
  if (!Array.isArray(profile.roomFurniture)) {
    profile.roomFurniture = [];
  }
  for (const inv of profile.inventory) {
    if (LEGACY_FURN_MAP[inv.itemId]) inv.itemId = LEGACY_FURN_MAP[inv.itemId];
  }
  for (const rf of profile.roomFurniture) {
    if (LEGACY_FURN_MAP[rf.itemId]) rf.itemId = LEGACY_FURN_MAP[rf.itemId];
  }
  if (profile.lastBedPos === undefined) {
    const placedBed = profile.roomFurniture.find((f) => getCatalogItem(f.itemId)?.shape === 'bed');
    profile.lastBedPos = placedBed
      ? { x: placedBed.x, y: placedBed.y, itemId: placedBed.itemId }
      : null;
  }

  // Multi-lot migration & sanitization (up to MAX_PLAYER_LOTS = 5 lots)
  if (!Array.isArray(profile.lots) || profile.lots.length === 0) {
    profile.lots = [
      {
        lotIndex: 1,
        name: 'Lote 1',
        accessMode: 'public',
        theme: profile.roomTheme || 'madeira_classica',
        hasBuiltSpace: Boolean(profile.hasBuiltSpace),
        floorStyleId: profile.floorStyleId || DEFAULT_FLOOR_STYLE_ID,
        wallStyleId: profile.wallStyleId || DEFAULT_WALL_STYLE_ID,
        furniture: [...profile.roomFurniture],
        plotTiles: [...profile.plotTiles],
        plotMaxBlocks: Math.max(STARTER_PLOT_MAX_BLOCKS, profile.plotMaxBlocks || STARTER_PLOT_MAX_BLOCKS),
        wallAdded: [...(profile.wallAdded || [])],
        wallRemoved: [...(profile.wallRemoved || [])],
        lastBedPos: profile.lastBedPos ?? null,
      },
    ];
  } else {
    const seen = new Set<number>();
    const normalizedLots: PlayerLot[] = [];
    for (const rawLot of profile.lots) {
      const idx = Math.max(1, Math.min(MAX_PLAYER_LOTS, Math.floor(Number(rawLot.lotIndex) || 1)));
      if (seen.has(idx)) continue;
      seen.add(idx);
      const lotTiles = Array.isArray(rawLot.plotTiles) ? rawLot.plotTiles : [];
      const lotPruned = pruneWallOverridesForTiles(
        new Set(lotTiles),
        Array.isArray(rawLot.wallAdded) ? rawLot.wallAdded : [],
        Array.isArray(rawLot.wallRemoved) ? rawLot.wallRemoved : []
      );
      const lotFurn = Array.isArray(rawLot.furniture) ? rawLot.furniture : [];
      for (const rf of lotFurn) {
        if (LEGACY_FURN_MAP[rf.itemId]) rf.itemId = LEGACY_FURN_MAP[rf.itemId];
      }
      const validPin = typeof rawLot.accessPin === 'string' && /^\d{6}$/.test(rawLot.accessPin)
        ? rawLot.accessPin
        : undefined;
      const mode: LotAccessMode = rawLot.accessMode === 'private' && validPin ? 'private' : 'public';
      const bed = lotFurn.find((f) => getCatalogItem(f.itemId)?.shape === 'bed');
      normalizedLots.push({
        lotIndex: idx,
        name: String(rawLot.name || `Lote ${idx}`).trim().slice(0, 24) || `Lote ${idx}`,
        accessMode: mode,
        ...(mode === 'private' && validPin ? { accessPin: validPin } : {}),
        theme: rawLot.theme || 'madeira_classica',
        hasBuiltSpace: rawLot.hasBuiltSpace ?? lotTiles.length > 0,
        floorStyleId: rawLot.floorStyleId || DEFAULT_FLOOR_STYLE_ID,
        wallStyleId: rawLot.wallStyleId || DEFAULT_WALL_STYLE_ID,
        furniture: lotFurn,
        plotTiles: lotTiles,
        plotMaxBlocks:
          idx === 1
            ? Math.max(STARTER_PLOT_MAX_BLOCKS, Number(rawLot.plotMaxBlocks) || STARTER_PLOT_MAX_BLOCKS)
            : Math.max(0, Number(rawLot.plotMaxBlocks) || 0),
        wallAdded: lotPruned.wallAdded,
        wallRemoved: lotPruned.wallRemoved,
        lastBedPos:
          rawLot.lastBedPos !== undefined
            ? rawLot.lastBedPos
            : bed
            ? { x: bed.x, y: bed.y, itemId: bed.itemId }
            : null,
      });
    }
    normalizedLots.sort((a, b) => a.lotIndex - b.lotIndex);
    profile.lots = normalizedLots;
  }

  if (!profile.activeLotIndex || !getProfileLot(profile, profile.activeLotIndex)) {
    profile.activeLotIndex = profile.lots[0]?.lotIndex || 1;
  }
  syncLegacyFieldsFromLot1(profile);

  if (profile.isFainted === undefined) profile.isFainted = false;
  if (profile.faintedUntil === undefined) profile.faintedUntil = null;
  if (profile.energyZeroSince === undefined) profile.energyZeroSince = null;
  if (profile.hungerZeroSince === undefined) profile.hungerZeroSince = null;
  if (profile.isRestingOnBed === undefined) profile.isRestingOnBed = false;
  if (profile.activeActivity === undefined) profile.activeActivity = null;
  if (profile.godMode === undefined) profile.godMode = false;
  ensureProfessionProfile(profile);
  return profile;
}

const CHAT_COLORS = ['#4ade80', '#f472b6', '#a78bfa', '#38bdf8', '#fbbf24', '#fb923c'];
function getPlayerColor(name: string): string {
  let hash = 0;
  for (let i = 0; i < name.length; i++) {
    hash = name.charCodeAt(i) + ((hash << 5) - hash);
  }
  return CHAT_COLORS[Math.abs(hash) % CHAT_COLORS.length];
}

function getRoomPlayers(roomKey: string): WorldPlayer[] {
  const result: WorldPlayer[] = [];
  for (const p of activePlayers.values()) {
    if (p.roomKey === roomKey) {
      result.push(p);
    }
  }
  return result;
}

function getRoomCounts(): Record<string, number> {
  const counts: Record<string, number> = {
    praca: 0,
    balada: 0,
    cafeteria: 0,
    mercado: 0,
    espaco: 0,
    floresta: 0,
    mina: 0,
    oasis_deserto: 0,
  };
  for (const p of activePlayers.values()) {
    const base = p.roomKey.startsWith('espaco') ? 'espaco' : p.roomKey;
    counts[base] = (counts[base] || 0) + 1;
  }
  return counts;
}

function sendJson(ws: WebSocket | undefined, payload: unknown) {
  if (ws && ws.readyState === WebSocket.OPEN) {
    ws.send(JSON.stringify(payload));
  }
}

function broadcastToRoom(roomKey: string, payload: unknown) {
  for (const [playerId, player] of activePlayers.entries()) {
    if (player.roomKey === roomKey) {
      sendJson(socketsByPlayer.get(playerId), payload);
    }
  }
}

function broadcastAll(payload: unknown) {
  for (const ws of socketsByPlayer.values()) {
    sendJson(ws, payload);
  }
}

function updateQuestProgress(profile: PlayerProfile, metric: PlayerProfile['quests'][0]['metric'], amount: number, isAbsolute = false) {
  for (const q of profile.quests) {
    if (q.metric === metric && !q.claimed) {
      q.progress = isAbsolute ? Math.min(q.target, amount) : Math.min(q.target, q.progress + amount);
    }
  }
}

function getSpacePayload(ownerId: string, lotIndex = 1): SpaceInfoPayload {
  const owner = state.profiles[ownerId];
  if (owner) {
    ensureProfileFields(owner);
    const lot = getProfileLot(owner, lotIndex) || owner.lots![0];
    return {
      ownerId: owner.id,
      ownerName: owner.name,
      lotIndex: lot.lotIndex,
      lotName: lot.name,
      accessMode: lot.accessMode,
      theme: lot.theme,
      hasBuiltSpace: Boolean(lot.hasBuiltSpace),
      floorStyleId: lot.floorStyleId || DEFAULT_FLOOR_STYLE_ID,
      wallStyleId: lot.wallStyleId || DEFAULT_WALL_STYLE_ID,
      furniture: lot.furniture,
      plotTiles: lot.plotTiles,
      plotMaxBlocks: lot.plotMaxBlocks,
      wallAdded: lot.wallAdded || [],
      wallRemoved: lot.wallRemoved || [],
    };
  }
  return {
    ownerId,
    ownerName: 'Visitante',
    lotIndex: 1,
    lotName: 'Lote Demo',
    accessMode: 'public',
    theme: 'neon_roxo',
    hasBuiltSpace: true,
    floorStyleId: 'piso_neon_roxo',
    wallStyleId: 'parede_roxo_cyber',
    furniture: [
      { instanceId: 'demo_1', itemId: 'neon_46', x: 5, y: 5, rotation: 0 },
      { instanceId: 'demo_2', itemId: 'neon_02', x: 4, y: 4, rotation: 0 },
      { instanceId: 'demo_3', itemId: 'neon_21', x: 7, y: 4, rotation: 0 },
      { instanceId: 'demo_4', itemId: 'neon_30', x: 3, y: 4, rotation: 0 },
    ],
    plotTiles: createStarterPlotTiles(),
    plotMaxBlocks: STARTER_PLOT_MAX_BLOCKS,
    wallAdded: [],
    wallRemoved: [],
  };
}

function getLotsDirectoryPayload(): PublicLotDirectoryEntry[] {
  const entries: PublicLotDirectoryEntry[] = [];
  for (const owner of Object.values(state.profiles)) {
    ensureProfileFields(owner);
    const ownerOnline = activePlayers.has(owner.id);
    for (const lot of owner.lots || []) {
      let visitorsOnline = 0;
      for (const wp of activePlayers.values()) {
        const parsed = parseEspacoRoomKey(wp.roomKey);
        if (parsed && parsed.ownerId === owner.id && parsed.lotIndex === lot.lotIndex) {
          visitorsOnline += 1;
        }
      }
      entries.push({
        ownerId: owner.id,
        ownerName: owner.name,
        lotIndex: lot.lotIndex,
        lotName: lot.name,
        accessMode: lot.accessMode,
        builtBlocks: lot.plotTiles.length,
        furnitureCount: lot.furniture.length,
        visitorsOnline,
        ownerOnline,
      });
    }
  }
  entries.sort((a, b) => {
    if (b.visitorsOnline !== a.visitorsOnline) return b.visitorsOnline - a.visitorsOnline;
    if (a.ownerOnline !== b.ownerOnline) return a.ownerOnline ? -1 : 1;
    const nameCmp = a.ownerName.localeCompare(b.ownerName, 'pt-BR');
    if (nameCmp !== 0) return nameCmp;
    return a.lotIndex - b.lotIndex;
  });
  return entries;
}

function ensureStarterInventory(avatar: AvatarConfig): PlayerProfile['inventory'] {
  const items: PlayerProfile['inventory'] = [];
  const add = (itemId: string | null) => {
    if (!itemId || itemId === 'shirt_sem') return;
    if (!items.some((i) => i.itemId === itemId)) {
      items.push({
        instanceId: `inv_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
        itemId,
        obtainedAt: Date.now(),
      });
    }
  };
  add(avatar.shirtId);
  add(avatar.pantsId);
  add(avatar.shoesId);
  add(avatar.accessoryId);
  const starterHair = CATALOG_ITEMS.find(
    (i) => i.category === 'cabelo' && i.hairStyleId === avatar.hairStyle
  );
  if (starterHair) add(starterHair.id);
  // Give 3 starter Rústico furniture pieces so Nosso Espaço is immediately cozy!
  add('rust_03');
  add('rust_30');
  add('rust_41');
  return items;
}

async function startServer() {
  const app = express();
  app.use(express.json());

  app.get('/api/health', (_req, res) => {
    res.json({ ok: true, playersOnline: activePlayers.size });
  });

  app.get('/api/public-spaces', (_req, res) => {
    res.json({ spaces: getLotsDirectoryPayload() });
  });

  const server = http.createServer(app);
  const wss = new WebSocketServer({ server });

  wss.on('connection', (ws) => {
    ws.on('message', (rawData) => {
      let msg: { type: string; payload?: Record<string, unknown> };
      try {
        msg = JSON.parse(rawData.toString());
      } catch {
        return;
      }

      const payload = msg.payload || {};

      if (msg.type === 'auth:join') {
        const requestedId = String(payload.playerId || `p_${Math.random().toString(36).slice(2, 10)}`);
        const name = String(payload.name || 'Morador').trim().slice(0, 18) || 'Morador';
        const bio = String(payload.bio || 'Explorando a cidade de OASIS!').slice(0, 80);
        const avatar = payload.avatar as AvatarConfig;

        let profile = state.profiles[requestedId];
        if (!profile) {
          const starterInv = ensureStarterInventory(avatar);

          profile = {
            id: requestedId,
            name,
            bio,
            moedas: 0,
            gemas: 0,
            stepsWalked: 0,
            avatar,
            inventory: starterInv,
            roomFurniture: [],
            roomTheme: 'madeira_classica',
            hasBuiltSpace: false,
            floorStyleId: DEFAULT_FLOOR_STYLE_ID,
            wallStyleId: DEFAULT_WALL_STYLE_ID,
            ownedFloorStyles: [DEFAULT_FLOOR_STYLE_ID],
            ownedWallStyles: [DEFAULT_WALL_STYLE_ID],
            plotTiles: [],
            plotMaxBlocks: STARTER_PLOT_MAX_BLOCKS,
            wallAdded: [],
            wallRemoved: [],
            needs: createInitialNeeds(),
            routineTasks: createInitialRoutineTasks(),
            friends: [],
            quests: createInitialQuests(),
            lastMealAt: Date.now(),
            lastBedPos: null,
            isFainted: false,
            faintedUntil: null,
            energyZeroSince: null,
            hungerZeroSince: null,
            isRestingOnBed: false,
            activeActivity: null,
          };
          ensureProfileFields(profile);
          state.profiles[requestedId] = profile;
          scheduleSave();
        } else {
          ensureProfileFields(profile);
          profile.name = name;
          profile.bio = bio;
          if (avatar) {
            profile.avatar = avatar;
          }
          // Reset fainted timer if it expired while offline
          if (profile.isFainted && profile.faintedUntil && Date.now() >= profile.faintedUntil) {
            profile.isFainted = false;
            profile.faintedUntil = null;
            profile.hungerZeroSince = null;
            profile.needs.fome = Math.max(profile.needs.fome, 20);
          }
          profile.isRestingOnBed = false;
          profile.activeActivity = null;
          scheduleSave();
        }

        ensureProfessionProfile(profile);
        const playerResourceNodes = ensurePlayerResourceNodes(profile, Date.now(), state.economyConfig);
        getOrCreateRuntime(profile);

        const roomKey = 'praca';
        const pracaSpawn = getPracaReturnSpawnNormalized();
        const worldPlayer: WorldPlayer = {
          id: profile.id,
          name: profile.name,
          bio: profile.bio,
          avatar: profile.avatar,
          roomKey,
          x: pracaSpawn.x,
          y: pracaSpawn.y,
          direction: 'frente',
          expression: 'feliz',
          action: profile.isFainted ? 'deitado' : 'parado',
          isOnline: true,
          isFainted: Boolean(profile.isFainted),
          faintedUntil: profile.faintedUntil ?? null,
          isRestingOnBed: false,
          activeActivity: null,
        };
        syncWorldPlayerProfession(profile, worldPlayer);

        activePlayers.set(profile.id, worldPlayer);
        socketsByPlayer.set(profile.id, ws);
        playerBySocket.set(ws, profile.id);

        if (!roomChats[roomKey]) roomChats[roomKey] = [];

        const pendingTrades = Object.values(state.trades).filter(
          (t) => t.status === 'pendente' && (t.toId === profile.id || t.fromId === profile.id)
        );

        const activeLiveTrades = Array.from(liveTradeSessions.values()).filter(
          (s) =>
            (s.status === 'convite' || s.status === 'negociando') &&
            (s.a.playerId === profile.id || s.b.playerId === profile.id)
        );

        sendJson(ws, {
          type: 'init:sync',
          payload: {
            profile,
            roomKey,
            players: getRoomPlayers(roomKey),
            seats: getRoomSeatsPayload(roomKey),
            chatHistory: roomChats[roomKey].slice(-40),
            roomCounts: getRoomCounts(),
            marketListings: state.marketListings,
            marketHistory: state.marketHistory.slice(0, 80),
            resourceNodes: Object.values(playerResourceNodes),
            economyConfig: state.economyConfig,
            trades: pendingTrades,
            liveTradeSession: activeLiveTrades[0] || null,
            lotsDirectory: getLotsDirectoryPayload(),
            onlinePlayers: Array.from(activePlayers.values()).map((p) => ({ id: p.id, name: p.name, roomKey: p.roomKey })),
          },
        });

        broadcastToRoom(roomKey, {
          type: 'room:players',
          payload: { roomKey, players: getRoomPlayers(roomKey) },
        });
        broadcastAll({
          type: 'city:counts',
          payload: {
            roomCounts: getRoomCounts(),
            onlinePlayers: Array.from(activePlayers.values()).map((p) => ({ id: p.id, name: p.name, roomKey: p.roomKey })),
          },
        });
        return;
      }

      const playerId = playerBySocket.get(ws);
      if (!playerId) return;
      const profile = state.profiles[playerId];
      const worldPlayer = activePlayers.get(playerId);
      if (!profile || !worldPlayer) return;

      if (msg.type === 'room:change') {
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou! Espere ajuda ou aguarde a recuperação.', kind: 'error' } });
          return;
        }
        const rawTarget = String(payload.roomKey || 'praca');
        if (rawTarget === 'shopping') {
          sendJson(ws, { type: 'toast', payload: { message: 'Os móveis agora ficam no botão Catálogo!', kind: 'info' } });
          return;
        }
        const parsedLot = parseEspacoRoomKey(rawTarget);
        const targetRoomKey = parsedLot
          ? formatEspacoRoomKey(parsedLot.ownerId, parsedLot.lotIndex)
          : rawTarget;
        const oldRoomKey = worldPlayer.roomKey;
        if (oldRoomKey === targetRoomKey) return;

        let spaceInfo: SpaceInfoPayload | null = null;
        if (parsedLot) {
          const owner = state.profiles[parsedLot.ownerId];
          if (owner) {
            ensureProfileFields(owner);
            const targetLot = getProfileLot(owner, parsedLot.lotIndex);
            if (!targetLot) {
              sendJson(ws, {
                type: 'toast',
                payload: { message: `${owner.name} ainda não possui o Lote ${parsedLot.lotIndex}.`, kind: 'error' },
              });
              return;
            }
            if (targetLot.accessMode === 'private' && parsedLot.ownerId !== playerId) {
              const suppliedPin = String(payload.pin || '').trim();
              if (!suppliedPin || suppliedPin !== targetLot.accessPin) {
                sendJson(ws, {
                  type: 'lot:pin_required',
                  payload: {
                    ownerId: owner.id,
                    ownerName: owner.name,
                    lotIndex: targetLot.lotIndex,
                    lotName: targetLot.name,
                    wrongPin: Boolean(suppliedPin),
                  },
                });
                return;
              }
            }
            if (parsedLot.ownerId === playerId) {
              profile.activeLotIndex = targetLot.lotIndex;
              scheduleSave();
              sendJson(ws, { type: 'profile:update', payload: { profile } });
            }
          }
          spaceInfo = getSpacePayload(parsedLot.ownerId, parsedLot.lotIndex);
        }

        releasePlayerSeats(playerId, true);

        const fromRoom = typeof payload.fromRoom === 'string' ? payload.fromRoom : oldRoomKey;
        const spawnMap: Record<string, { x: number; y: number }> = {
          praca: getPracaReturnSpawnNormalized(fromRoom),
          balada: { x: 2.68, y: 8.43 },
          cafeteria: { x: 4.75, y: 7.46 },
          floresta: getForagingSpawnNormalized('floresta'),
          mina: getForagingSpawnNormalized('mina'),
          oasis_deserto: getForagingSpawnNormalized('oasis_deserto'),
        };
        const spawn = spaceInfo
          ? pickWalkableEspacoTile(spaceInfo.plotTiles, spaceInfo.furniture)
          : spawnMap[targetRoomKey] || { x: 5, y: 7 };
        worldPlayer.roomKey = targetRoomKey;
        worldPlayer.x = spawn.x;
        worldPlayer.y = spawn.y;
        worldPlayer.action = 'parado';
        worldPlayer.isRestingOnBed = false;
        worldPlayer.activeActivity = null;
        profile.isRestingOnBed = false;
        profile.activeActivity = null;
        worldPlayer.bubbleText = undefined;

        if (!roomChats[targetRoomKey]) {
          roomChats[targetRoomKey] = [];
        }

        broadcastToRoom(oldRoomKey, {
          type: 'room:players',
          payload: { roomKey: oldRoomKey, players: getRoomPlayers(oldRoomKey) },
        });

        sendJson(ws, {
          type: 'room:entered',
          payload: {
            roomKey: targetRoomKey,
            players: getRoomPlayers(targetRoomKey),
            seats: getRoomSeatsPayload(targetRoomKey),
            chatHistory: roomChats[targetRoomKey].slice(-40),
            spaceInfo,
          },
        });

        broadcastToRoom(targetRoomKey, {
          type: 'room:players',
          payload: { roomKey: targetRoomKey, players: getRoomPlayers(targetRoomKey) },
        });

        broadcastAll({
          type: 'city:counts',
          payload: {
            roomCounts: getRoomCounts(),
            onlinePlayers: Array.from(activePlayers.values()).map((p) => ({ id: p.id, name: p.name, roomKey: p.roomKey })),
          },
        });
        if (oldRoomKey.startsWith('espaco:') || targetRoomKey.startsWith('espaco:')) {
          broadcastAll({
            type: 'lots:updated',
            payload: { lotsDirectory: getLotsDirectoryPayload() },
          });
        }
      } else if (msg.type === 'lots:list') {
        sendJson(ws, {
          type: 'lots:updated',
          payload: { lotsDirectory: getLotsDirectoryPayload() },
        });
      } else if (msg.type === 'lot:buy') {
        ensureProfileFields(profile);
        const ownedCount = profile.lots?.length || 1;
        const requestedIdx = Math.floor(Number(payload.lotIndex || ownedCount + 1));
        const payWith = payload.payWith === 'gemas' ? 'gemas' : 'moedas';
        if (ownedCount >= MAX_PLAYER_LOTS) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Você já possui o máximo de ${MAX_PLAYER_LOTS} lotes!`, kind: 'info' },
          });
          return;
        }
        const expectedIdx = ownedCount + 1;
        if (requestedIdx !== expectedIdx || requestedIdx < 2 || requestedIdx > MAX_PLAYER_LOTS) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Compre os lotes em ordem sequencial (próximo: Lote ${expectedIdx}).`, kind: 'error' },
          });
          return;
        }
        const priceDef = LOT_PURCHASE_PRICES.find((p) => p.lotIndex === requestedIdx);
        if (!priceDef) return;
        if (payWith === 'gemas') {
          if (profile.gemas < priceDef.priceGems) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: `Você precisa de ${priceDef.priceGems} gemas para comprar o ${priceDef.label}!`, kind: 'error' },
            });
            return;
          }
          profile.gemas -= priceDef.priceGems;
        } else {
          if (profile.moedas < priceDef.priceCoins) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: `Você precisa de ${priceDef.priceCoins.toLocaleString('pt-BR')} moedas para comprar o ${priceDef.label}!`, kind: 'error' },
            });
            return;
          }
          profile.moedas -= priceDef.priceCoins;
        }
        const newLot: PlayerLot = {
          lotIndex: requestedIdx,
          name: `Lote ${requestedIdx}`,
          accessMode: 'public',
          theme: 'madeira_classica',
          hasBuiltSpace: false,
          floorStyleId: DEFAULT_FLOOR_STYLE_ID,
          wallStyleId: DEFAULT_WALL_STYLE_ID,
          furniture: [],
          plotTiles: [],
          plotMaxBlocks: 0,
          wallAdded: [],
          wallRemoved: [],
          lastBedPos: null,
        };
        profile.lots!.push(newLot);
        profile.activeLotIndex = requestedIdx;
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastAll({ type: 'lots:updated', payload: { lotsDirectory: getLotsDirectoryPayload() } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `🏡 ${priceDef.label} comprado! Agora compre blocos no modo Construir para edificar nele.`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'lot:configure') {
        ensureProfileFields(profile);
        const lotIndex = Math.floor(Number(payload.lotIndex || 1));
        const lot = getProfileLot(profile, lotIndex);
        if (!lot) {
          sendJson(ws, { type: 'toast', payload: { message: 'Lote não encontrado.', kind: 'error' } });
          return;
        }
        const nextName = String(payload.name || '').trim().slice(0, 24) || `Lote ${lot.lotIndex}`;
        const nextMode: LotAccessMode = payload.accessMode === 'private' ? 'private' : 'public';
        if (nextMode === 'private') {
          const pin = String(payload.accessPin ?? lot.accessPin ?? '').trim();
          if (!/^\d{6}$/.test(pin)) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: 'Escolha uma senha numérica de exatamente 6 dígitos para trancar o lote.', kind: 'error' },
            });
            return;
          }
          lot.accessPin = pin;
        } else {
          delete lot.accessPin;
        }
        lot.name = nextName;
        lot.accessMode = nextMode;
        syncLegacyFieldsFromLot1(profile);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        const lotRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
        broadcastToRoom(lotRoomKey, {
          type: 'space:updated',
          payload: { roomKey: lotRoomKey, spaceInfo: getSpacePayload(profile.id, lot.lotIndex) },
        });
        broadcastAll({ type: 'lots:updated', payload: { lotsDirectory: getLotsDirectoryPayload() } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message:
              nextMode === 'private'
                ? `🔒 "${lot.name}" definido como Privado (senha de 6 dígitos ativa).`
                : `🌐 "${lot.name}" agora está Público para visitas!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'seat:occupy') {
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou! Não pode sentar agora.', kind: 'error' } });
          return;
        }
        const seatId = String(payload.seatId || '').trim().slice(0, 64);
        if (!seatId) return;
        const rk = worldPlayer.roomKey;
        let roomSeats = seatOccupancies.get(rk);
        if (!roomSeats) {
          roomSeats = new Map<string, string>();
          seatOccupancies.set(rk, roomSeats);
        }
        const existingHolder = roomSeats.get(seatId);
        if (existingHolder && existingHolder !== playerId && activePlayers.get(existingHolder)?.roomKey === rk) {
          sendJson(ws, { type: 'toast', payload: { message: 'Este assento já está ocupado por outro jogador!', kind: 'info' } });
          sendJson(ws, { type: 'room:seats', payload: { roomKey: rk, seats: getRoomSeatsPayload(rk) } });
          return;
        }
        releasePlayerSeats(playerId, false);
        roomSeats.set(seatId, playerId);

        const maxCoord = rk.startsWith('espaco') ? PLOT_GRID_SIZE - 1 : 11;
        const sx = Number(payload.x);
        const sy = Number(payload.y);
        if (Number.isFinite(sx) && Number.isFinite(sy)) {
          worldPlayer.x = Math.max(0, Math.min(maxCoord, sx));
          worldPlayer.y = Math.max(0, Math.min(maxCoord, sy));
        }
        if (payload.direction) {
          worldPlayer.direction = payload.direction as Direction;
        }
        worldPlayer.action = 'sentado';
        profile.isRestingOnBed = false;
        worldPlayer.isRestingOnBed = false;
        profile.activeActivity = null;
        worldPlayer.activeActivity = null;

        broadcastToRoom(rk, {
          type: 'room:seats',
          payload: { roomKey: rk, seats: getRoomSeatsPayload(rk) },
        });
        broadcastToRoom(rk, {
          type: 'player:updated',
          payload: { player: worldPlayer },
        });
      } else if (msg.type === 'seat:release') {
        releasePlayerSeats(playerId, true);
        const maxCoord = worldPlayer.roomKey.startsWith('espaco') ? PLOT_GRID_SIZE - 1 : 11;
        const rx = Number(payload.x);
        const ry = Number(payload.y);
        if (Number.isFinite(rx) && Number.isFinite(ry)) {
          worldPlayer.x = Math.max(0, Math.min(maxCoord, rx));
          worldPlayer.y = Math.max(0, Math.min(maxCoord, ry));
        }
        if (payload.direction) {
          worldPlayer.direction = payload.direction as Direction;
        }
        if (worldPlayer.action === 'sentado') {
          worldPlayer.action = 'parado';
        }
        broadcastToRoom(worldPlayer.roomKey, {
          type: 'player:updated',
          payload: { player: worldPlayer },
        });
      } else if (msg.type === 'player:move') {
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou! Não pode andar até ser alimentado.', kind: 'error' } });
          return;
        }
        const x = Number(payload.x);
        const y = Number(payload.y);
        const direction = (payload.direction as Direction) || worldPlayer.direction;
        const action = (payload.action as ActionId) || 'parado';
        const steps = Math.max(0, Math.min(10, Number(payload.steps || 1)));
        const maxCoord = worldPlayer.roomKey.startsWith('espaco') ? PLOT_GRID_SIZE - 1 : 11;

        if (Number.isFinite(x) && Number.isFinite(y)) {
          worldPlayer.x = Math.max(0, Math.min(maxCoord, x));
          worldPlayer.y = Math.max(0, Math.min(maxCoord, y));
          worldPlayer.direction = direction;
          worldPlayer.action = action;

          if (action !== 'sentado') {
            releasePlayerSeats(playerId, true);
          }

          // Moving away cancels stationary bed rest / plant watering / arcade unless explicitly lying on bed
          if (action !== 'deitado') {
            profile.isRestingOnBed = false;
            worldPlayer.isRestingOnBed = false;
          }
          profile.activeActivity = null;
          worldPlayer.activeActivity = null;

          if (steps > 0) {
            profile.stepsWalked += steps;
            updateQuestProgress(profile, 'steps', steps);
            const mult = getEnergyCostMultiplier(profile);
            addNeedDelta(profile, 'energia', -steps * 0.42 * mult);
            addNeedDelta(profile, 'higiene', -steps * 0.04);
            scheduleSave();
            sendJson(ws, { type: 'profile:update', payload: { profile } });
          }

          broadcastToRoom(worldPlayer.roomKey, {
            type: 'player:updated',
            payload: { player: worldPlayer },
          });
        }
      } else if (msg.type === 'player:state') {
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou e está esperando ajuda!', kind: 'error' } });
          return;
        }
        if (payload.expression) worldPlayer.expression = payload.expression as ExpressionId;
        if (payload.action) {
          const nextAct = payload.action as ActionId;
          worldPlayer.action = nextAct;
          if (nextAct !== 'sentado') {
            releasePlayerSeats(playerId, true);
          }
          if (nextAct !== 'deitado') {
            profile.isRestingOnBed = false;
            worldPlayer.isRestingOnBed = false;
          }
          profile.activeActivity = null;
          worldPlayer.activeActivity = null;
          if (nextAct === 'dancando' || nextAct === 'pulando' || nextAct === 'comemorando' || nextAct === 'correndo') {
            const mult = getEnergyCostMultiplier(profile);
            addNeedDelta(profile, 'energia', -1.5 * mult);
            sendJson(ws, { type: 'profile:update', payload: { profile } });
          }
        }
        if (payload.direction) worldPlayer.direction = payload.direction as Direction;

        broadcastToRoom(worldPlayer.roomKey, {
          type: 'player:updated',
          payload: { player: worldPlayer },
        });
      } else if (msg.type === 'avatar:update') {
        const newAvatar = payload.avatar as AvatarConfig;
        if (newAvatar) {
          profile.avatar = { ...profile.avatar, ...newAvatar };
          if (typeof payload.name === 'string' && payload.name.trim()) {
            profile.name = payload.name.trim().slice(0, 18);
            worldPlayer.name = profile.name;
          }
          if (typeof payload.bio === 'string') {
            profile.bio = payload.bio.slice(0, 80);
            worldPlayer.bio = profile.bio;
          }
          worldPlayer.avatar = profile.avatar;
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          broadcastToRoom(worldPlayer.roomKey, {
            type: 'player:updated',
            payload: { player: worldPlayer },
          });
        }
      } else if (msg.type === 'chat:send') {
        const text = String(payload.text || '').trim().slice(0, 140);
        if (!text) return;

        const cmd = text.toLowerCase();
        if (cmd === '/oasis') {
          profile.moedas += 10000;
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: { message: '✨ Comando /oasis: +10.000 moedas adicionadas!', kind: 'success' },
          });
          return;
        }
        if (cmd === '/oasis2') {
          setNeedValue(profile, 'energia', 100);
          profile.energyZeroSince = null;
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: { message: '⚡ Comando /oasis2: Energia restaurada para 100%!', kind: 'success' },
          });
          return;
        }
        if (cmd === '/oasis3') {
          setNeedValue(profile, 'fome', 100);
          profile.lastMealAt = Date.now();
          profile.hungerZeroSince = null;
          if (profile.isFainted) {
            profile.isFainted = false;
            profile.faintedUntil = null;
            worldPlayer.isFainted = false;
            worldPlayer.faintedUntil = null;
            worldPlayer.action = 'parado';
            broadcastToRoom(worldPlayer.roomKey, {
              type: 'player:updated',
              payload: { player: worldPlayer },
            });
          }
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: { message: '🍽️ Comando /oasis3: Fome restaurada para 100%!', kind: 'success' },
          });
          return;
        }
        if (cmd === '/god') {
          profile.godMode = !profile.godMode;
          if (profile.godMode) {
            setNeedValue(profile, 'energia', 100);
            setNeedValue(profile, 'fome', 100);
            setNeedValue(profile, 'diversao', 100);
            setNeedValue(profile, 'higiene', 100);
            profile.lastMealAt = Date.now();
            profile.energyZeroSince = null;
            profile.hungerZeroSince = null;
            if (profile.isFainted) {
              profile.isFainted = false;
              profile.faintedUntil = null;
              worldPlayer.isFainted = false;
              worldPlayer.faintedUntil = null;
              worldPlayer.action = 'parado';
              broadcastToRoom(worldPlayer.roomKey, {
                type: 'player:updated',
                payload: { player: worldPlayer },
              });
            }
          }
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: profile.godMode
                ? '🛡️ Modo /god ATIVADO: Energia, Fome, Diversão e Higiene não caem mais!'
                : '🛡️ Modo /god DESATIVADO: Necessidades voltaram ao normal.',
              kind: profile.godMode ? 'success' : 'info',
            },
          });
          return;
        }
        if (cmd.startsWith('/profadmin')) {
          const parts = cmd.split(/\s+/);
          const sub = parts[1] || '';
          const val = Number(parts[2]);
          if (sub === 'tax' && Number.isFinite(val)) {
            state.economyConfig = ensureEconomyConfig({ ...state.economyConfig, marketTaxRate: val / 100 });
          } else if (sub === 'trialmin' && Number.isFinite(val)) {
            state.economyConfig = ensureEconomyConfig({ ...state.economyConfig, trialDurationMs: val * 60000 });
          } else if (sub === 'xpmult' && Number.isFinite(val)) {
            state.economyConfig = ensureEconomyConfig({ ...state.economyConfig, xpMultiplier: val });
          } else if (sub === 'changecost' && Number.isFinite(val)) {
            state.economyConfig = ensureEconomyConfig({ ...state.economyConfig, professionChangeCostCoins: val });
          } else {
            sendJson(ws, {
              type: 'toast',
              payload: {
                message: 'Uso: /profadmin tax <0..25> | trialmin <1..60> | xpmult <0.5..5> | changecost <0..5000>',
                kind: 'info',
              },
            });
            return;
          }
          scheduleSave();
          broadcastAll({ type: 'economy:config', payload: { economyConfig: state.economyConfig } });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: `⚙️ Economia atualizada (Taxa: ${Math.round(state.economyConfig.marketTaxRate * 100)}% · Teste: ${Math.round(state.economyConfig.trialDurationMs / 60000)}m · XP: ${state.economyConfig.xpMultiplier}x)`,
              kind: 'success',
            },
          });
          return;
        }

        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você está desmaiado! Aguarde ajuda ou use /oasis3.', kind: 'error' } });
          return;
        }

        const roomKey = worldPlayer.roomKey;
        if (!roomChats[roomKey]) roomChats[roomKey] = [];

        const chatMsg: ChatMessage = {
          id: `msg_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
          roomKey,
          senderId: profile.id,
          senderName: profile.name,
          senderColor: getPlayerColor(profile.name),
          text,
          type: 'chat',
          timestamp: Date.now(),
        };

        roomChats[roomKey].push(chatMsg);
        if (roomChats[roomKey].length > 80) roomChats[roomKey].shift();

        worldPlayer.bubbleText = text;
        worldPlayer.bubbleExpiresAt = Date.now() + 5500;

        updateQuestProgress(profile, 'messages', 1);
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(roomKey, { type: 'chat:message', payload: { message: chatMsg } });
        broadcastToRoom(roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
      } else if (msg.type === 'shop:buy') {
        const itemId = String(payload.itemId || '');
        const payWith = payload.payWith === 'gemas' ? 'gemas' : 'moedas';
        const item = getCatalogItem(itemId);
        if (
          !item ||
          item.craftOrigin ||
          item.category === 'recurso' ||
          item.category === 'material' ||
          item.category === 'ferramenta' ||
          item.category === 'estrutura'
        ) {
          if (item) {
            sendJson(ws, {
              type: 'toast',
              payload: {
                message: 'Item exclusivo da economia de profissões! Compre de jogadores no Mercado Global ou fabrique na Oficina.',
                kind: 'error',
              },
            });
          }
          return;
        }

        if (payWith === 'gemas') {
          if (!item.priceGems || profile.gemas < item.priceGems) {
            sendJson(ws, { type: 'toast', payload: { message: 'Gemas insuficientes para este item.', kind: 'error' } });
            return;
          }
          profile.gemas -= item.priceGems;
        } else {
          if (profile.moedas < item.priceCoins) {
            sendJson(ws, { type: 'toast', payload: { message: 'Moedas insuficientes! Trabalhe nos minigames ou venda itens.', kind: 'error' } });
            return;
          }
          profile.moedas -= item.priceCoins;
        }

        profile.inventory.push({
          instanceId: `inv_${Date.now()}_${Math.random().toString(36).slice(2, 7)}`,
          itemId: item.id,
          obtainedAt: Date.now(),
        });

        updateQuestProgress(profile, 'trades_or_buys', 1);
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, { type: 'toast', payload: { message: `Você comprou ${item.name}!`, kind: 'success' } });
      } else if (msg.type === 'gems:buy') {
        const packId = String(payload.packId || '');
        const pack = GEM_PACKAGES.find((p) => p.id === packId);
        if (!pack) return;

        profile.gemas += pack.gems + pack.bonus;
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `Pacote "${pack.label}" creditado: +${pack.gems + pack.bonus} gemas!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'gems:exchange') {
        const gemsToSpend = Math.max(1, Math.floor(Number(payload.gems || 0)));
        if (profile.gemas < gemsToSpend) {
          sendJson(ws, { type: 'toast', payload: { message: 'Gemas insuficientes.', kind: 'error' } });
          return;
        }
        const coinsEarned = gemsToSpend * 25;
        profile.gemas -= gemsToSpend;
        profile.moedas += coinsEarned;
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, { type: 'toast', payload: { message: `Convertido: +${coinsEarned} moedas!`, kind: 'success' } });
      } else if (msg.type === 'inventory:equip') {
        const itemId = payload.itemId ? String(payload.itemId) : null;
        const category = String(payload.category || '');
        if (itemId && itemId !== 'shirt_sem') {
          const owned = profile.inventory.some((i) => i.itemId === itemId);
          if (!owned) return;
        }

        if (category === 'roupa_cima') profile.avatar.shirtId = itemId;
        if (category === 'roupa_baixo') profile.avatar.pantsId = itemId;
        if (category === 'calcado') profile.avatar.shoesId = itemId;
        if (category === 'acessorio') profile.avatar.accessoryId = itemId;
        if (category === 'cabelo') {
          const hairCat = itemId ? getCatalogItem(itemId) : null;
          profile.avatar.hairStyle =
            hairCat?.hairStyleId ||
            (profile.avatar.gender === 'feminino' ? 'coque_alto' : 'topete_fade');
        }

        worldPlayer.avatar = profile.avatar;
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
      } else if (msg.type === 'room:furnish') {
        ensureProfileFields(profile);
        const lot = resolveTargetOwnedLot(profile, worldPlayer);
        const op = String(payload.op || '');
        let furnCountChanged = false;
        if (op === 'place') {
          const instanceId = String(payload.instanceId || '');
          const rawX = Math.floor(Number(payload.x));
          const rawY = Math.floor(Number(payload.y));
          const rotation = ([0, 90, 180, 270].includes(Number(payload.rotation)) ? Number(payload.rotation) : 0) as 0 | 90 | 180 | 270;
          if (!Number.isFinite(rawX) || !Number.isFinite(rawY) || rawX < 0 || rawY < 0 || rawX >= PLOT_GRID_SIZE || rawY >= PLOT_GRID_SIZE) {
            sendJson(ws, { type: 'toast', payload: { message: 'Posicione o móvel dentro dos limites 16×16 do lote!', kind: 'error' } });
            return;
          }
          const owned = profile.inventory.find((i) => i.instanceId === instanceId);
          if (!owned) return;
          const item = getCatalogItem(owned.itemId);
          if (!item || item.category !== 'movel') return;

          const placedElsewhere = (profile.lots || []).some(
            (l) => l.lotIndex !== lot.lotIndex && l.furniture.some((f) => f.instanceId === instanceId)
          );
          if (placedElsewhere) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: 'Este móvel já está colocado em outro lote seu! Remova-o de lá primeiro.', kind: 'error' },
            });
            return;
          }

          const fp = getFurnitureFootprint(item.id, item.shape, rotation);
          const x = Math.max(0, Math.min(PLOT_GRID_SIZE - fp.w, rawX));
          const y = Math.max(0, Math.min(PLOT_GRID_SIZE - fp.h, rawY));

          const existingIdx = lot.furniture.findIndex((f) => f.instanceId === instanceId);
          if (existingIdx >= 0) {
            lot.furniture[existingIdx] = { instanceId, itemId: item.id, x, y, rotation };
          } else {
            lot.furniture.push({ instanceId, itemId: item.id, x, y, rotation });
            furnCountChanged = true;
          }
          if (item.shape === 'bed') {
            lot.lastBedPos = { x, y, itemId: item.id };
            profile.lastBedPos = { x, y, itemId: item.id };
          }
        } else if (op === 'remove') {
          const instanceId = String(payload.instanceId || '');
          const before = lot.furniture.length;
          lot.furniture = lot.furniture.filter((f) => f.instanceId !== instanceId);
          furnCountChanged = lot.furniture.length !== before;
          const anotherBed = lot.furniture.find((f) => getCatalogItem(f.itemId)?.shape === 'bed');
          lot.lastBedPos = anotherBed
            ? { x: anotherBed.x, y: anotherBed.y, itemId: anotherBed.itemId }
            : null;
          if (anotherBed) {
            profile.lastBedPos = lot.lastBedPos;
          }
        } else if (op === 'rotate') {
          const instanceId = String(payload.instanceId || '');
          const furn = lot.furniture.find((f) => f.instanceId === instanceId);
          if (furn) {
            const nextRot = (((furn.rotation + 90) % 360) as 0 | 90 | 180 | 270);
            const item = getCatalogItem(furn.itemId);
            const fp = getFurnitureFootprint(furn.itemId, item?.shape, nextRot);
            furn.rotation = nextRot;
            furn.x = Math.max(0, Math.min(PLOT_GRID_SIZE - fp.w, furn.x));
            furn.y = Math.max(0, Math.min(PLOT_GRID_SIZE - fp.h, furn.y));
          }
        } else if (op === 'theme') {
          lot.theme = String(payload.theme || 'madeira_classica') as RoomTheme;
        }

        syncLegacyFieldsFromLot1(profile);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });

        const targetRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
        broadcastToRoom(targetRoomKey, {
          type: 'space:updated',
          payload: {
            roomKey: targetRoomKey,
            spaceInfo: getSpacePayload(profile.id, lot.lotIndex),
          },
        });
        if (furnCountChanged) {
          broadcastAll({ type: 'lots:updated', payload: { lotsDirectory: getLotsDirectoryPayload() } });
        }
      } else if (msg.type === 'room:build_tile') {
        ensureProfileFields(profile);
        const lot = resolveTargetOwnedLot(profile, worldPlayer);
        const x = Math.floor(Number(payload.x));
        const y = Math.floor(Number(payload.y));
        if (!Number.isFinite(x) || !Number.isFinite(y) || x < 0 || y < 0 || x >= PLOT_GRID_SIZE || y >= PLOT_GRID_SIZE) return;

        const tileKey = `${x},${y}`;
        const existsIdx = lot.plotTiles.indexOf(tileKey);

        if (existsIdx >= 0) {
          if (lot.plotTiles.length <= MIN_PLOT_BUILD_BLOCKS) {
            sendJson(ws, { type: 'toast', payload: { message: `Mantenha ao menos ${MIN_PLOT_BUILD_BLOCKS} blocos de terreno no seu lote!`, kind: 'error' } });
            return;
          }
          lot.plotTiles.splice(existsIdx, 1);
        } else {
          if (lot.plotTiles.length >= lot.plotMaxBlocks) {
            sendJson(ws, {
              type: 'toast',
              payload: {
                message:
                  lot.plotMaxBlocks <= 0
                    ? 'Este lote ainda não possui blocos! Compre blocos na aba Construir.'
                    : `Limite de ${lot.plotMaxBlocks} blocos atingido neste lote! Compre mais blocos para expandir.`,
                kind: 'error',
              },
            });
            return;
          }
          lot.plotTiles.push(tileKey);
          lot.hasBuiltSpace = true;
        }

        const prunedAfterTile = pruneWallOverridesForTiles(
          new Set(lot.plotTiles),
          lot.wallAdded || [],
          lot.wallRemoved || []
        );
        lot.wallAdded = prunedAfterTile.wallAdded;
        lot.wallRemoved = prunedAfterTile.wallRemoved;

        syncLegacyFieldsFromLot1(profile);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });

        const targetRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
        broadcastToRoom(targetRoomKey, {
          type: 'space:updated',
          payload: {
            roomKey: targetRoomKey,
            spaceInfo: getSpacePayload(profile.id, lot.lotIndex),
          },
        });
        broadcastAll({ type: 'lots:updated', payload: { lotsDirectory: getLotsDirectoryPayload() } });
      } else if (msg.type === 'room:save_plot') {
        ensureProfileFields(profile);
        const lot = resolveTargetOwnedLot(profile, worldPlayer);
        const rawTiles = Array.isArray(payload.tiles) ? payload.tiles : [];
        const uniqueSet = new Set<string>();
        for (const t of rawTiles) {
          if (typeof t !== 'string') continue;
          const parts = t.split(',');
          if (parts.length !== 2) continue;
          const x = Math.floor(Number(parts[0]));
          const y = Math.floor(Number(parts[1]));
          if (!Number.isFinite(x) || !Number.isFinite(y) || x < 0 || y >= PLOT_GRID_SIZE || y < 0 || y >= PLOT_GRID_SIZE) continue;
          uniqueSet.add(`${x},${y}`);
        }
        const nextTiles = Array.from(uniqueSet);
        if (nextTiles.length < MIN_PLOT_BUILD_BLOCKS) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Monte seu lote com pelo menos ${MIN_PLOT_BUILD_BLOCKS} blocos antes de salvar!`, kind: 'error' },
          });
          return;
        }
        if (nextTiles.length > lot.plotMaxBlocks) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Você usou ${nextTiles.length} blocos, mas este lote possui ${lot.plotMaxBlocks} disponíveis.`, kind: 'error' },
          });
          return;
        }

        const hasWallPayload = Array.isArray(payload.wallAdded) || Array.isArray(payload.wallRemoved);
        const rawWallAdded = hasWallPayload
          ? sanitizeWallEdgeList(payload.wallAdded)
          : lot.wallAdded || [];
        const rawWallRemoved = hasWallPayload
          ? sanitizeWallEdgeList(payload.wallRemoved)
          : lot.wallRemoved || [];
        const prunedWalls = pruneWallOverridesForTiles(uniqueSet, rawWallAdded, rawWallRemoved);

        const wasFirstBuild = !lot.hasBuiltSpace;
        lot.plotTiles = nextTiles;
        lot.wallAdded = prunedWalls.wallAdded;
        lot.wallRemoved = prunedWalls.wallRemoved;
        lot.hasBuiltSpace = true;

        syncLegacyFieldsFromLot1(profile);

        const targetRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
        if (worldPlayer.roomKey === targetRoomKey) {
          const curX = Math.round(worldPlayer.x);
          const curY = Math.round(worldPlayer.y);
          const outOfLot = curX < 0 || curX >= PLOT_GRID_SIZE || curY < 0 || curY >= PLOT_GRID_SIZE;
          if (outOfLot || (wasFirstBuild && nextTiles.length > 0 && !uniqueSet.has(`${curX},${curY}`))) {
            const safeSpawn = pickWalkableEspacoTile(nextTiles, lot.furniture);
            worldPlayer.x = safeSpawn.x;
            worldPlayer.y = safeSpawn.y;
            worldPlayer.action = 'parado';
            broadcastToRoom(targetRoomKey, {
              type: 'player:updated',
              payload: { player: worldPlayer },
            });
          }
        }

        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(targetRoomKey, {
          type: 'space:updated',
          payload: {
            roomKey: targetRoomKey,
            spaceInfo: getSpacePayload(profile.id, lot.lotIndex),
          },
        });
        broadcastAll({ type: 'lots:updated', payload: { lotsDirectory: getLotsDirectoryPayload() } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: nextTiles.length === 0
              ? `Estrutura limpa! "${lot.name}" (16×16) está pronto para jardim ou nova construção.`
              : wasFirstBuild
              ? `${lot.name} construído com ${nextTiles.length} blocos! Agora decore o interior e o jardim!`
              : `Estrutura de "${lot.name}" salva (${nextTiles.length} blocos)!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'space:buy_blocks') {
        ensureProfileFields(profile);
        const lot = resolveTargetOwnedLot(profile, worldPlayer);
        const packId = String(payload.packId || '');
        const payWith = payload.payWith === 'gemas' ? 'gemas' : 'moedas';
        const pack = FLOOR_BLOCK_PACKS.find((p) => p.id === packId);
        if (!pack) return;

        if (lot.plotMaxBlocks >= MAX_PLOT_GRID_BLOCKS) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `${lot.name} já atingiu o tamanho máximo de ${MAX_PLOT_GRID_BLOCKS} blocos!`, kind: 'info' },
          });
          return;
        }

        const roomRemaining = MAX_PLOT_GRID_BLOCKS - lot.plotMaxBlocks;
        const blocksToAdd = Math.min(pack.blocks, roomRemaining);

        if (payWith === 'gemas') {
          if (profile.gemas < pack.priceGems) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: `Você precisa de ${pack.priceGems} gemas para comprar ${pack.label}!`, kind: 'error' },
            });
            return;
          }
          profile.gemas -= pack.priceGems;
        } else {
          if (profile.moedas < pack.priceCoins) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: `Você precisa de ${pack.priceCoins.toLocaleString('pt-BR')} moedas para comprar ${pack.label}!`, kind: 'error' },
            });
            return;
          }
          profile.moedas -= pack.priceCoins;
        }

        lot.plotMaxBlocks += blocksToAdd;
        syncLegacyFieldsFromLot1(profile);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });

        const targetRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
        broadcastToRoom(targetRoomKey, {
          type: 'space:updated',
          payload: {
            roomKey: targetRoomKey,
            spaceInfo: getSpacePayload(profile.id, lot.lotIndex),
          },
        });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `+${blocksToAdd} bloco(s) adicionados ao ${lot.name}! Capacidade do lote: ${lot.plotMaxBlocks} blocos.`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'space:buy_or_apply_style') {
        ensureProfileFields(profile);
        const lot = resolveTargetOwnedLot(profile, worldPlayer);
        const kind = payload.kind === 'wall' ? 'wall' : 'floor';
        const styleId = String(payload.styleId || '');
        const payWith = payload.payWith === 'gemas' ? 'gemas' : 'moedas';

        if (kind === 'floor') {
          const style = FLOOR_STYLES.find((s) => s.id === styleId);
          if (!style) return;
          const ownedList = profile.ownedFloorStyles || [DEFAULT_FLOOR_STYLE_ID];
          const alreadyOwned = ownedList.includes(style.id) || style.priceCoins === 0;
          if (!alreadyOwned) {
            if (payWith === 'gemas' && style.priceGems) {
              if (profile.gemas < style.priceGems) {
                sendJson(ws, { type: 'toast', payload: { message: `Gemas insuficientes (${style.priceGems} gemas).`, kind: 'error' } });
                return;
              }
              profile.gemas -= style.priceGems;
            } else {
              if (profile.moedas < style.priceCoins) {
                sendJson(ws, { type: 'toast', payload: { message: `Você precisa de ${style.priceCoins} moedas para comprar o piso "${style.name}"!`, kind: 'error' } });
                return;
              }
              profile.moedas -= style.priceCoins;
            }
            ownedList.push(style.id);
            profile.ownedFloorStyles = ownedList;
          }
          lot.floorStyleId = style.id;
          syncLegacyFieldsFromLot1(profile);
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          const targetRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
          broadcastToRoom(targetRoomKey, {
            type: 'space:updated',
            payload: { roomKey: targetRoomKey, spaceInfo: getSpacePayload(profile.id, lot.lotIndex) },
          });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: alreadyOwned
                ? `Piso "${style.name}" aplicado ao ${lot.name}!`
                : `Piso "${style.name}" comprado e aplicado ao ${lot.name}!`,
              kind: 'success',
            },
          });
        } else {
          const style = WALL_STYLES.find((s) => s.id === styleId);
          if (!style) return;
          const ownedList = profile.ownedWallStyles || [DEFAULT_WALL_STYLE_ID];
          const alreadyOwned = ownedList.includes(style.id) || style.priceCoins === 0;
          if (!alreadyOwned) {
            if (payWith === 'gemas' && style.priceGems) {
              if (profile.gemas < style.priceGems) {
                sendJson(ws, { type: 'toast', payload: { message: `Gemas insuficientes (${style.priceGems} gemas).`, kind: 'error' } });
                return;
              }
              profile.gemas -= style.priceGems;
            } else {
              if (profile.moedas < style.priceCoins) {
                sendJson(ws, { type: 'toast', payload: { message: `Você precisa de ${style.priceCoins} moedas para comprar a parede "${style.name}"!`, kind: 'error' } });
                return;
              }
              profile.moedas -= style.priceCoins;
            }
            ownedList.push(style.id);
            profile.ownedWallStyles = ownedList;
          }
          lot.wallStyleId = style.id;
          syncLegacyFieldsFromLot1(profile);
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          const targetRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
          broadcastToRoom(targetRoomKey, {
            type: 'space:updated',
            payload: { roomKey: targetRoomKey, spaceInfo: getSpacePayload(profile.id, lot.lotIndex) },
          });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: alreadyOwned
                ? `Parede "${style.name}" aplicada ao ${lot.name}!`
                : `Parede "${style.name}" comprada e aplicada ao ${lot.name}!`,
              kind: 'success',
            },
          });
        }
      } else if (msg.type === 'routine:action') {
        ensureProfileFields(profile);
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou! Espere ajuda ou aguarde a recuperação.', kind: 'error' } });
          return;
        }
        const actionType = String(payload.actionType || '');
        const mult = getEnergyCostMultiplier(profile);
        let toastText = 'Rotina atualizada!';
        let taskToComplete: string | null = null;
        let nextPose: ActionId | null = null;

        if (actionType === 'dormir_cama') {
          profile.isRestingOnBed = true;
          profile.activeActivity = null;
          profile.energyZeroSince = null;
          worldPlayer.isRestingOnBed = true;
          worldPlayer.activeActivity = null;
          nextPose = 'deitado';
          taskToComplete = 'rt_descansar';
          toastText = 'Descansando na cama... Energia recupera gradualmente (5 min até 100%). Você pode levantar quando quiser!';
        } else if (actionType === 'relaxar_sofa') {
          profile.isRestingOnBed = false;
          profile.activeActivity = null;
          worldPlayer.isRestingOnBed = false;
          worldPlayer.activeActivity = null;
          addNeedDelta(profile, 'diversao', 2);
          nextPose = 'sentado';
          toastText = 'Sentado no sofá! Permanecer sentado recupera diversão aos poucos.';
        } else if (actionType === 'regar_planta') {
          profile.isRestingOnBed = false;
          profile.activeActivity = 'regando';
          worldPlayer.isRestingOnBed = false;
          worldPlayer.activeActivity = 'regando';
          addNeedDelta(profile, 'energia', -2 * mult);
          addNeedDelta(profile, 'higiene', -2);
          nextPose = 'comemorando';
          taskToComplete = 'rt_arrumar';
          toastText = 'Regando as plantas! Permaneça na atividade para ganhar diversão por segundo.';
        } else if (actionType === 'arrumar_casa') {
          profile.isRestingOnBed = false;
          profile.activeActivity = null;
          worldPlayer.isRestingOnBed = false;
          worldPlayer.activeActivity = null;
          addNeedDelta(profile, 'energia', -8 * mult);
          addNeedDelta(profile, 'higiene', 22);
          addNeedDelta(profile, 'diversao', 3);
          nextPose = 'comemorando';
          taskToComplete = 'rt_arrumar';
          toastText = `Casa arrumada (+22 Higiene · -${Math.round(8 * mult)} Energia)!`;
        } else if (actionType === 'jogar_arcade') {
          profile.isRestingOnBed = false;
          profile.activeActivity = 'arcade';
          worldPlayer.isRestingOnBed = false;
          worldPlayer.activeActivity = 'arcade';
          addNeedDelta(profile, 'energia', -3 * mult);
          nextPose = 'comemorando';
          toastText = 'Jogando no fliperama! Permaneça na máquina para subir diversão por segundo.';
        } else if (actionType === 'lanche_cafeteria') {
          const cost = 20;
          if (profile.moedas < cost) {
            sendJson(ws, { type: 'toast', payload: { message: `Você precisa de ${cost} moedas para comprar Café & Croissant!`, kind: 'error' } });
            return;
          }
          profile.moedas -= cost;
          addNeedDelta(profile, 'fome', 22);
          addNeedDelta(profile, 'energia', 3);
          profile.lastMealAt = Date.now();
          profile.hungerZeroSince = null;
          taskToComplete = 'rt_comer';
          nextPose = 'comemorando';
          toastText = 'Café & Croissant consumido (-20 moedas · +22% Fome · +3% Energia)!';
        } else if (actionType === 'frutas_mercado') {
          const cost = 9;
          if (profile.moedas < cost) {
            sendJson(ws, { type: 'toast', payload: { message: `Você precisa de ${cost} moedas para comprar Maçã da Vila!`, kind: 'error' } });
            return;
          }
          profile.moedas -= cost;
          addNeedDelta(profile, 'fome', 11);
          profile.lastMealAt = Date.now();
          profile.hungerZeroSince = null;
          taskToComplete = 'rt_comer';
          nextPose = 'comemorando';
          toastText = 'Maçã da Vila consumida (-9 moedas · +11% Fome)!';
        } else if (actionType === 'tomar_banho') {
          addNeedDelta(profile, 'energia', -3 * mult);
          addNeedDelta(profile, 'higiene', 35);
          nextPose = 'comemorando';
          taskToComplete = 'rt_arrumar';
          toastText = 'Visual renovado (+35 Higiene)!';
        } else if (actionType === 'abrir_bau') {
          addNeedDelta(profile, 'energia', -3 * mult);
          addNeedDelta(profile, 'diversao', 4);
          nextPose = 'agachado';
          taskToComplete = 'rt_arrumar';
          toastText = 'Você organizou seus itens no baú (+4 Diversão)!';
        } else if (actionType === 'sentar_mesa') {
          profile.isRestingOnBed = false;
          profile.activeActivity = null;
          worldPlayer.isRestingOnBed = false;
          worldPlayer.activeActivity = null;
          addNeedDelta(profile, 'diversao', 2);
          nextPose = 'sentado';
          toastText = 'Sentado à mesa!';
        }

        if (taskToComplete) {
          const rt = profile.routineTasks.find((t) => t.id === taskToComplete);
          if (rt && !rt.done) {
            rt.done = true;
            profile.moedas += rt.rewardCoins;
            toastText += ` · Tarefa da rotina: +${rt.rewardCoins} moedas!`;
          }
        }

        if (nextPose) {
          worldPlayer.action = nextPose;
          broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
        }

        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, { type: 'toast', payload: { message: toastText, kind: 'success' } });
      } else if (msg.type === 'food:eat') {
        ensureProfileFields(profile);
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou e não consegue comer sozinho! Peça ajuda a outro jogador.', kind: 'error' } });
          return;
        }
        const instanceId = String(payload.instanceId || '');
        const idx = profile.inventory.findIndex((i) => i.instanceId === instanceId);
        if (idx < 0) return;
        const cat = getCatalogItem(profile.inventory[idx].itemId);
        if (!cat || cat.category !== 'comida') return;

        const res = consumeInventoryInstance(profile, instanceId, 1);
        if (!res) return;
        const hungerGain = cat.hungerRestore ?? 10;
        const energyGain = cat.energyRestore ?? 0;
        const funGain = cat.funRestore ?? 0;
        const hygieneGain = cat.hygieneRestore ?? 0;
        addNeedDelta(profile, 'fome', hungerGain);
        if (energyGain > 0) addNeedDelta(profile, 'energia', energyGain);
        if (funGain > 0) addNeedDelta(profile, 'diversao', funGain);
        if (hygieneGain > 0) addNeedDelta(profile, 'higiene', hygieneGain);
        profile.lastMealAt = Date.now();
        profile.hungerZeroSince = null;

        const eatTask = profile.routineTasks.find((t) => t.id === 'rt_comer');
        if (eatTask && !eatTask.done) {
          eatTask.done = true;
          profile.moedas += eatTask.rewardCoins;
        }

        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `Você consumiu ${cat.name} (+${hungerGain}% Fome${energyGain ? ` · +${energyGain}% Energia` : ''})!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'player:feed') {
        ensureProfileFields(profile);
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você está desmaiado e não pode ajudar ninguém agora.', kind: 'error' } });
          return;
        }
        const targetPlayerId = String(payload.targetPlayerId || '');
        const instanceId = String(payload.instanceId || '');
        if (!targetPlayerId || targetPlayerId === profile.id) return;

        const targetProfile = state.profiles[targetPlayerId];
        const targetWorld = activePlayers.get(targetPlayerId);
        if (!targetProfile || !targetWorld || !targetProfile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Este jogador não está desmaiado no momento.', kind: 'error' } });
          return;
        }

        const idx = profile.inventory.findIndex((i) => i.instanceId === instanceId);
        if (idx < 0) return;
        const cat = getCatalogItem(profile.inventory[idx].itemId);
        if (!cat || cat.category !== 'comida') return;

        const fed = consumeInventoryInstance(profile, instanceId, 1);
        if (!fed) return;
        const hungerGain = Math.max(10, cat.hungerRestore ?? 15);
        addNeedDelta(targetProfile, 'fome', hungerGain);
        if (cat.energyRestore) addNeedDelta(targetProfile, 'energia', cat.energyRestore);
        if (cat.hygieneRestore) addNeedDelta(targetProfile, 'higiene', cat.hygieneRestore);
        targetProfile.lastMealAt = Date.now();
        targetProfile.hungerZeroSince = null;
        targetProfile.isFainted = false;
        targetProfile.faintedUntil = null;
        targetWorld.isFainted = false;
        targetWorld.faintedUntil = null;
        targetWorld.action = 'parado';

        // Small fun reward for helping a fellow citizen
        addNeedDelta(profile, 'diversao', 6);

        const sysMsg: ChatMessage = {
          id: `sys_${Date.now()}_${Math.random().toString(36).slice(2, 5)}`,
          roomKey: targetWorld.roomKey,
          senderId: 'sistema',
          senderName: 'OASIS',
          senderColor: '#4ade80',
          text: `${profile.name} alimentou e levantou ${targetProfile.name} com ${cat.name}!`,
          type: 'system',
          timestamp: Date.now(),
        };
        if (!roomChats[targetWorld.roomKey]) roomChats[targetWorld.roomKey] = [];
        roomChats[targetWorld.roomKey].push(sysMsg);

        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, { type: 'toast', payload: { message: `Você alimentou ${targetProfile.name} com ${cat.name} (+6% Diversão)!`, kind: 'success' } });

        const targetWs = socketsByPlayer.get(targetProfile.id);
        sendJson(targetWs, { type: 'profile:update', payload: { profile: targetProfile } });
        sendJson(targetWs, {
          type: 'toast',
          payload: { message: `${profile.name} deu ${cat.name} para você! Você se levantou (+${hungerGain}% Fome)!`, kind: 'success' },
        });
        broadcastToRoom(targetWorld.roomKey, { type: 'chat:message', payload: { message: sysMsg } });
        broadcastToRoom(targetWorld.roomKey, { type: 'player:updated', payload: { player: targetWorld } });
      } else if (msg.type === 'liveTrade:invite') {
        const toId = String(payload.toId || '');
        const targetProfile = state.profiles[toId];
        const targetWs = socketsByPlayer.get(toId);
        if (!targetProfile || !targetWs || toId === profile.id) {
          sendJson(ws, { type: 'toast', payload: { message: 'O jogador precisa estar online para abrir a Mesa de Troca ao vivo.', kind: 'error' } });
          return;
        }

        const session: LiveTradeSession = {
          sessionId: `lt_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
          a: {
            playerId: profile.id,
            playerName: profile.name,
            slots: [],
            coins: 0,
            locked: false,
            confirmed: false,
          },
          b: {
            playerId: targetProfile.id,
            playerName: targetProfile.name,
            slots: [],
            coins: 0,
            locked: false,
            confirmed: false,
          },
          status: 'convite',
          createdAt: Date.now(),
        };
        liveTradeSessions.set(session.sessionId, session);

        const sysMsg: ChatMessage = {
          id: `sys_${Date.now()}`,
          roomKey: worldPlayer.roomKey,
          senderId: 'sistema',
          senderName: 'Sistema',
          senderColor: '#22d3ee',
          text: `${profile.name} convidou ${targetProfile.name} para uma mesa de troca!`,
          type: 'system',
          timestamp: Date.now(),
        };
        if (!roomChats[worldPlayer.roomKey]) roomChats[worldPlayer.roomKey] = [];
        roomChats[worldPlayer.roomKey].push(sysMsg);
        broadcastToRoom(worldPlayer.roomKey, { type: 'chat:message', payload: { message: sysMsg } });

        sendJson(ws, { type: 'liveTrade:updated', payload: { session } });
        sendJson(targetWs, { type: 'liveTrade:updated', payload: { session } });
        sendJson(targetWs, { type: 'toast', payload: { message: `${profile.name} abriu um convite de Troca ao Vivo!`, kind: 'info' } });
      } else if (msg.type === 'liveTrade:accept_invite') {
        const sessionId = String(payload.sessionId || '');
        const session = liveTradeSessions.get(sessionId);
        if (!session || session.status !== 'convite' || session.b.playerId !== profile.id) return;

        session.status = 'negociando';
        sendJson(socketsByPlayer.get(session.a.playerId), { type: 'liveTrade:updated', payload: { session } });
        sendJson(ws, { type: 'liveTrade:updated', payload: { session } });
      } else if (msg.type === 'liveTrade:toggle_item') {
        const sessionId = String(payload.sessionId || '');
        const instanceId = String(payload.instanceId || '');
        const session = liveTradeSessions.get(sessionId);
        if (!session || session.status !== 'negociando') return;

        const side =
          session.a.playerId === profile.id
            ? session.a
            : session.b.playerId === profile.id
            ? session.b
            : null;
        if (!side) return;

        const idx = side.slots.findIndex((s) => s.instanceId === instanceId);
        if (idx >= 0) {
          side.slots.splice(idx, 1);
        } else {
          if (side.slots.length >= LIVE_TRADE_MAX_SLOTS) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: `A mesa de troca tem limite máximo de ${LIVE_TRADE_MAX_SLOTS} itens por jogador.`, kind: 'error' },
            });
            return;
          }
          const invItem = profile.inventory.find((i) => i.instanceId === instanceId);
          if (!invItem) return;
          const catItem = getCatalogItem(invItem.itemId);
          if (!catItem || !catItem.tradeable) return;
          side.slots.push({ instanceId: invItem.instanceId, itemId: invItem.itemId });
        }

        // Security lock reset whenever either side edits items
        session.a.locked = false;
        session.b.locked = false;
        session.a.confirmed = false;
        session.b.confirmed = false;

        sendJson(socketsByPlayer.get(session.a.playerId), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(session.b.playerId), { type: 'liveTrade:updated', payload: { session } });
      } else if (msg.type === 'liveTrade:set_coins') {
        const sessionId = String(payload.sessionId || '');
        const coins = Math.max(0, Math.min(profile.moedas, Math.floor(Number(payload.coins || 0))));
        const session = liveTradeSessions.get(sessionId);
        if (!session || session.status !== 'negociando') return;

        const side =
          session.a.playerId === profile.id
            ? session.a
            : session.b.playerId === profile.id
            ? session.b
            : null;
        if (!side) return;

        side.coins = coins;
        session.a.locked = false;
        session.b.locked = false;
        session.a.confirmed = false;
        session.b.confirmed = false;

        sendJson(socketsByPlayer.get(session.a.playerId), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(session.b.playerId), { type: 'liveTrade:updated', payload: { session } });
      } else if (msg.type === 'liveTrade:lock') {
        const sessionId = String(payload.sessionId || '');
        const session = liveTradeSessions.get(sessionId);
        if (!session || session.status !== 'negociando') return;

        const side =
          session.a.playerId === profile.id
            ? session.a
            : session.b.playerId === profile.id
            ? session.b
            : null;
        if (!side) return;

        side.locked = !side.locked;
        if (!side.locked) {
          session.a.confirmed = false;
          session.b.confirmed = false;
        }

        sendJson(socketsByPlayer.get(session.a.playerId), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(session.b.playerId), { type: 'liveTrade:updated', payload: { session } });
      } else if (msg.type === 'liveTrade:confirm') {
        const sessionId = String(payload.sessionId || '');
        const session = liveTradeSessions.get(sessionId);
        if (!session || session.status !== 'negociando') return;
        if (!session.a.locked || !session.b.locked) {
          sendJson(ws, { type: 'toast', payload: { message: 'Os dois jogadores precisam travar a oferta antes de confirmar!', kind: 'error' } });
          return;
        }

        const side =
          session.a.playerId === profile.id
            ? session.a
            : session.b.playerId === profile.id
            ? session.b
            : null;
        if (!side) return;

        side.confirmed = true;

        if (!(session.a.confirmed && session.b.confirmed)) {
          sendJson(socketsByPlayer.get(session.a.playerId), { type: 'liveTrade:updated', payload: { session } });
          sendJson(socketsByPlayer.get(session.b.playerId), { type: 'liveTrade:updated', payload: { session } });
          return;
        }

        const profA = state.profiles[session.a.playerId];
        const profB = state.profiles[session.b.playerId];
        if (!profA || !profB) return;

        if (profA.moedas < session.a.coins || profB.moedas < session.b.coins) {
          sendJson(socketsByPlayer.get(profA.id), { type: 'toast', payload: { message: 'Saldo insuficiente para concluir a troca.', kind: 'error' } });
          sendJson(socketsByPlayer.get(profB.id), { type: 'toast', payload: { message: 'Saldo insuficiente para concluir a troca.', kind: 'error' } });
          session.a.confirmed = false;
          session.b.confirmed = false;
          sendJson(socketsByPlayer.get(profA.id), { type: 'liveTrade:updated', payload: { session } });
          sendJson(socketsByPlayer.get(profB.id), { type: 'liveTrade:updated', payload: { session } });
          return;
        }

        const aHasAll = session.a.slots.every((s) => profA.inventory.some((i) => i.instanceId === s.instanceId));
        const bHasAll = session.b.slots.every((s) => profB.inventory.some((i) => i.instanceId === s.instanceId));
        if (!aHasAll || !bHasAll) {
          session.status = 'cancelada';
          sendJson(socketsByPlayer.get(profA.id), { type: 'liveTrade:updated', payload: { session } });
          sendJson(socketsByPlayer.get(profB.id), { type: 'liveTrade:updated', payload: { session } });
          return;
        }

        // Atomic swap of coins & up to 6 items per side
        profA.moedas = profA.moedas - session.a.coins + session.b.coins;
        profB.moedas = profB.moedas - session.b.coins + session.a.coins;

        const moveItems = (src: PlayerProfile, dst: PlayerProfile, slots: LiveTradeSession['a']['slots']) => {
          for (const sl of slots) {
            const idx = src.inventory.findIndex((i) => i.instanceId === sl.instanceId);
            if (idx >= 0) {
              const [moved] = src.inventory.splice(idx, 1);
              const changedLots = removeFurnitureFromAllLots(src, sl.instanceId);
              for (const li of changedLots) {
                const rk = formatEspacoRoomKey(src.id, li);
                broadcastToRoom(rk, {
                  type: 'space:updated',
                  payload: { roomKey: rk, spaceInfo: getSpacePayload(src.id, li) },
                });
              }
              if (src.equippedTools) {
                for (const pid of Object.keys(src.equippedTools) as ProfessionId[]) {
                  if (src.equippedTools[pid] === sl.instanceId) delete src.equippedTools[pid];
                }
              }
              const stillHasSame = src.inventory.some((i) => i.itemId === moved.itemId);
              if (!stillHasSame) {
                if (src.avatar.shirtId === moved.itemId) src.avatar.shirtId = 'shirt_sem';
                if (src.avatar.pantsId === moved.itemId) src.avatar.pantsId = 'pants_shorts_branco';
                if (src.avatar.shoesId === moved.itemId) src.avatar.shoesId = null;
                if (src.avatar.accessoryId === moved.itemId) src.avatar.accessoryId = null;
                const wp = activePlayers.get(src.id);
                if (wp) {
                  wp.avatar = src.avatar;
                  broadcastToRoom(wp.roomKey, { type: 'player:updated', payload: { player: wp } });
                }
              }
              addItemToInventory(dst, moved.itemId, {
                quantity: getItemQuantity(moved),
                durability: moved.durability,
                maxDurability: moved.maxDurability,
                quality: moved.quality,
                craftedBy: moved.craftedBy,
              });
            }
          }
        };

        moveItems(profA, profB, session.a.slots);
        moveItems(profB, profA, session.b.slots);

        profA.needs.diversao = clampStat(profA.needs.diversao + 12);
        profB.needs.diversao = clampStat(profB.needs.diversao + 12);
        updateQuestProgress(profA, 'trades_or_buys', 1);
        updateQuestProgress(profB, 'trades_or_buys', 1);

        session.status = 'concluida';
        scheduleSave();

        sendJson(socketsByPlayer.get(profA.id), { type: 'profile:update', payload: { profile: profA } });
        sendJson(socketsByPlayer.get(profB.id), { type: 'profile:update', payload: { profile: profB } });
        sendJson(socketsByPlayer.get(profA.id), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(profB.id), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(profA.id), { type: 'toast', payload: { message: 'Troca ao vivo concluída com sucesso!', kind: 'success' } });
        sendJson(socketsByPlayer.get(profB.id), { type: 'toast', payload: { message: 'Troca ao vivo concluída com sucesso!', kind: 'success' } });
      } else if (msg.type === 'liveTrade:cancel') {
        const sessionId = String(payload.sessionId || '');
        const session = liveTradeSessions.get(sessionId);
        if (!session) return;
        if (session.a.playerId !== profile.id && session.b.playerId !== profile.id) return;

        session.status = 'cancelada';
        sendJson(socketsByPlayer.get(session.a.playerId), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(session.b.playerId), { type: 'liveTrade:updated', payload: { session } });
        sendJson(socketsByPlayer.get(session.a.playerId), { type: 'toast', payload: { message: 'Mesa de troca encerrada.', kind: 'info' } });
        sendJson(socketsByPlayer.get(session.b.playerId), { type: 'toast', payload: { message: 'Mesa de troca encerrada.', kind: 'info' } });
      } else if (msg.type === 'market:list') {
        const instanceId = String(payload.instanceId || '');
        const priceCoins = Math.max(2, Math.min(999999, Math.floor(Number(payload.priceCoins || 50))));
        const invItem = profile.inventory.find((i) => i.instanceId === instanceId);
        if (!invItem) return;

        const catItem = getCatalogItem(invItem.itemId);
        if (!catItem || !catItem.tradeable) return;

        const maxQty = getItemQuantity(invItem);
        const listQty = catItem.stackable
          ? Math.max(1, Math.min(maxQty, Math.floor(Number(payload.quantity || maxQty))))
          : 1;

        const removed = consumeInventoryInstance(profile, instanceId, listQty);
        if (!removed) return;

        const changedLots = removeFurnitureFromAllLots(profile, instanceId);
        for (const li of changedLots) {
          const rk = formatEspacoRoomKey(profile.id, li);
          broadcastToRoom(rk, {
            type: 'space:updated',
            payload: { roomKey: rk, spaceInfo: getSpacePayload(profile.id, li) },
          });
        }
        const stillHasSame = profile.inventory.some((i) => i.itemId === invItem.itemId);
        if (!stillHasSame) {
          if (profile.avatar.shirtId === invItem.itemId) profile.avatar.shirtId = 'shirt_sem';
          if (profile.avatar.pantsId === invItem.itemId) profile.avatar.pantsId = 'pants_shorts_branco';
          if (profile.avatar.shoesId === invItem.itemId) profile.avatar.shoesId = null;
          if (profile.avatar.accessoryId === invItem.itemId) profile.avatar.accessoryId = null;
          worldPlayer.avatar = profile.avatar;
        }

        const listing: MarketListing = {
          listingId: `lst_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
          sellerId: profile.id,
          sellerName: profile.name,
          itemId: invItem.itemId,
          instanceId: removed.consumed.instanceId,
          priceCoins,
          quantity: listQty,
          unitPriceCoins: Math.max(1, Math.round(priceCoins / listQty)),
          itemSnapshot: {
            ...(removed.consumed.durability !== undefined ? { durability: removed.consumed.durability } : {}),
            ...(removed.consumed.maxDurability !== undefined ? { maxDurability: removed.consumed.maxDurability } : {}),
            ...(removed.consumed.quality ? { quality: removed.consumed.quality } : {}),
            ...(removed.consumed.craftedBy ? { craftedBy: removed.consumed.craftedBy } : {}),
          },
          createdAt: Date.now(),
        };
        state.marketListings.unshift(listing);
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastAll({
          type: 'market:updated',
          payload: { marketListings: state.marketListings, marketHistory: state.marketHistory.slice(0, 80) },
        });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `${listQty > 1 ? `${listQty}x ` : ''}${catItem.name} anunciado por ${priceCoins} moedas!`, kind: 'success' },
        });
      } else if (msg.type === 'market:cancel') {
        const listingId = String(payload.listingId || '');
        const idx = state.marketListings.findIndex((l) => l.listingId === listingId && l.sellerId === profile.id);
        if (idx < 0) return;
        const [removed] = state.marketListings.splice(idx, 1);
        addItemToInventory(profile, removed.itemId, {
          quantity: removed.quantity ?? 1,
          durability: removed.itemSnapshot?.durability,
          maxDurability: removed.itemSnapshot?.maxDurability,
          quality: removed.itemSnapshot?.quality,
          craftedBy: removed.itemSnapshot?.craftedBy,
        });
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastAll({
          type: 'market:updated',
          payload: { marketListings: state.marketListings, marketHistory: state.marketHistory.slice(0, 80) },
        });
      } else if (msg.type === 'market:buy') {
        const listingId = String(payload.listingId || '');
        const idx = state.marketListings.findIndex((l) => l.listingId === listingId);
        if (idx < 0) {
          sendJson(ws, { type: 'toast', payload: { message: 'Anúncio não está mais disponível.', kind: 'error' } });
          return;
        }
        const listing = state.marketListings[idx];
        if (listing.sellerId === profile.id) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você já é o vendedor deste anúncio.', kind: 'error' } });
          return;
        }

        const cat = getCatalogItem(listing.itemId);
        const totalQty = Math.max(1, Math.floor(listing.quantity ?? 1));
        const requestedBuyQty = cat?.stackable && totalQty > 1 && payload.quantity !== undefined
          ? Math.max(1, Math.min(totalQty, Math.floor(Number(payload.quantity))))
          : totalQty;

        const grossCoins = requestedBuyQty >= totalQty
          ? listing.priceCoins
          : Math.max(1, Math.round((listing.priceCoins * requestedBuyQty) / totalQty));

        if (profile.moedas < grossCoins) {
          sendJson(ws, { type: 'toast', payload: { message: 'Moedas insuficientes para comprar no Mercado.', kind: 'error' } });
          return;
        }

        if (requestedBuyQty >= totalQty) {
          state.marketListings.splice(idx, 1);
        } else {
          listing.quantity = totalQty - requestedBuyQty;
          listing.priceCoins = Math.max(1, listing.priceCoins - grossCoins);
          listing.unitPriceCoins = Math.max(1, Math.round(listing.priceCoins / listing.quantity));
        }

        profile.moedas -= grossCoins;
        addItemToInventory(profile, listing.itemId, {
          quantity: requestedBuyQty,
          durability: listing.itemSnapshot?.durability,
          maxDurability: listing.itemSnapshot?.maxDurability,
          quality: listing.itemSnapshot?.quality,
          craftedBy: listing.itemSnapshot?.craftedBy,
        });
        updateQuestProgress(profile, 'trades_or_buys', 1);

        const sellerProfile = state.profiles[listing.sellerId];
        const taxRate = sellerProfile
          ? getEffectiveMarketTaxRate(sellerProfile, state.economyConfig)
          : state.economyConfig.marketTaxRate;
        const taxCoins = grossCoins >= 10 ? Math.floor(grossCoins * taxRate) : 0;
        const netCoins = Math.max(1, grossCoins - taxCoins);

        if (sellerProfile) {
          ensureProfessionProfile(sellerProfile);
          sellerProfile.moedas += netCoins;
          sellerProfile.profession!.stats.marketSold += requestedBuyQty;
          const sellerWs = socketsByPlayer.get(sellerProfile.id);
          sendJson(sellerWs, { type: 'profile:update', payload: { profile: sellerProfile } });
          sendJson(sellerWs, {
            type: 'toast',
            payload: {
              message: `${profile.name} comprou ${requestedBuyQty > 1 ? `${requestedBuyQty}x ` : ''}${cat?.name || 'item'} (+${netCoins} moedas · taxa ${taxCoins})!`,
              kind: 'success',
            },
          });
        }

        const tx: MarketTransaction = {
          txId: `tx_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
          listingId: listing.listingId,
          buyerId: profile.id,
          buyerName: profile.name,
          sellerId: listing.sellerId,
          sellerName: listing.sellerName,
          itemId: listing.itemId,
          quantity: requestedBuyQty,
          grossCoins,
          taxCoins,
          netCoins,
          timestamp: Date.now(),
        };
        state.marketHistory.unshift(tx);
        if (state.marketHistory.length > 200) state.marketHistory.length = 200;

        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastAll({
          type: 'market:updated',
          payload: { marketListings: state.marketListings, marketHistory: state.marketHistory.slice(0, 80) },
        });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `Comprado: ${requestedBuyQty > 1 ? `${requestedBuyQty}x ` : ''}${cat?.name || 'Item'}!`, kind: 'success' },
        });
      // [MERCADO_NEGRO - REMOVÍVEL] Venda instantânea por preço reduzido para manter liquidez
      } else if (msg.type === 'market:sell_black_market') {
        if (!ENABLE_BLACK_MARKET) {
          sendJson(ws, { type: 'toast', payload: { message: 'Mercado Negro indisponível no momento.', kind: 'info' } });
          return;
        }
        ensureProfessionProfile(profile);
        const instanceId = String(payload.instanceId || '');
        const invItem = profile.inventory.find((i) => i.instanceId === instanceId);
        if (!invItem) return;

        const catItem = getCatalogItem(invItem.itemId);
        if (!catItem || !catItem.tradeable) {
          sendJson(ws, { type: 'toast', payload: { message: 'Este item não pode ser vendido no Mercado Negro.', kind: 'error' } });
          return;
        }
        if (catItem.category !== 'recurso' && catItem.category !== 'material') {
          sendJson(ws, {
            type: 'toast',
            payload: { message: 'O Mercado Negro compra apenas recursos e materiais de coleta!', kind: 'error' },
          });
          return;
        }

        const maxQty = getItemQuantity(invItem);
        const sellQty = catItem.stackable
          ? Math.max(1, Math.min(maxQty, Math.floor(Number(payload.quantity || maxQty))))
          : 1;

        const removed = consumeInventoryInstance(profile, instanceId, sellQty);
        if (!removed) return;

        const changedLots = removeFurnitureFromAllLots(profile, instanceId);
        for (const li of changedLots) {
          const rk = formatEspacoRoomKey(profile.id, li);
          broadcastToRoom(rk, {
            type: 'space:updated',
            payload: { roomKey: rk, spaceInfo: getSpacePayload(profile.id, li) },
          });
        }
        const stillHasSame = profile.inventory.some((i) => i.itemId === invItem.itemId);
        if (!stillHasSame) {
          if (profile.avatar.shirtId === invItem.itemId) profile.avatar.shirtId = 'shirt_sem';
          if (profile.avatar.pantsId === invItem.itemId) profile.avatar.pantsId = 'pants_shorts_branco';
          if (profile.avatar.shoesId === invItem.itemId) profile.avatar.shoesId = null;
          if (profile.avatar.accessoryId === invItem.itemId) profile.avatar.accessoryId = null;
          worldPlayer.avatar = profile.avatar;
        }

        const unitPrice = getBlackMarketUnitPrice(catItem, removed.consumed.quality);
        const totalCoins = Math.max(1, unitPrice * sellQty);
        profile.moedas += totalCoins;
        profile.profession!.stats.marketSold += sellQty;
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `🏴 Mercado Negro: ${sellQty > 1 ? `${sellQty}x ` : ''}${catItem.name} vendido por +${totalCoins} moedas!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'trade:send') {
        const toId = String(payload.toId || '');
        const targetProfile = state.profiles[toId];
        if (!targetProfile || toId === profile.id) {
          sendJson(ws, { type: 'toast', payload: { message: 'Jogador precisa estar online para troca direta.', kind: 'error' } });
          return;
        }
        const offeredInstanceIds = Array.isArray(payload.offeredInstanceIds) ? payload.offeredInstanceIds.map(String) : [];
        const requestedInstanceIds = Array.isArray(payload.requestedInstanceIds) ? payload.requestedInstanceIds.map(String) : [];
        const offeredCoins = Math.max(0, Math.floor(Number(payload.offeredCoins || 0)));
        const requestedCoins = Math.max(0, Math.floor(Number(payload.requestedCoins || 0)));

        if (offeredCoins > profile.moedas) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você não tem moedas suficientes para essa oferta.', kind: 'error' } });
          return;
        }

        const offeredItemIds: string[] = [];
        for (const instId of offeredInstanceIds) {
          const found = profile.inventory.find((i) => i.instanceId === instId);
          if (!found) return;
          offeredItemIds.push(found.itemId);
        }

        const requestedItemIds: string[] = [];
        for (const instId of requestedInstanceIds) {
          const found = targetProfile.inventory.find((i) => i.instanceId === instId);
          if (!found) return;
          requestedItemIds.push(found.itemId);
        }

        const trade: TradeOffer = {
          tradeId: `tr_${Date.now()}_${Math.random().toString(36).slice(2, 6)}`,
          fromId: profile.id,
          fromName: profile.name,
          toId: targetProfile.id,
          toName: targetProfile.name,
          offeredInstanceIds,
          offeredItemIds,
          offeredCoins,
          requestedInstanceIds,
          requestedItemIds,
          requestedCoins,
          status: 'pendente',
          createdAt: Date.now(),
        };
        state.trades[trade.tradeId] = trade;
        scheduleSave();

        // System chat notification matching mockup ("Sistema: Julia pediu uma troca")
        const sysMsg: ChatMessage = {
          id: `sys_${Date.now()}`,
          roomKey: worldPlayer.roomKey,
          senderId: 'sistema',
          senderName: 'Sistema',
          senderColor: '#22d3ee',
          text: `${profile.name} pediu uma troca com ${targetProfile.name}`,
          type: 'system',
          timestamp: Date.now(),
        };
        if (!roomChats[worldPlayer.roomKey]) roomChats[worldPlayer.roomKey] = [];
        roomChats[worldPlayer.roomKey].push(sysMsg);
        broadcastToRoom(worldPlayer.roomKey, { type: 'chat:message', payload: { message: sysMsg } });

        sendJson(ws, { type: 'trade:updated', payload: { trade } });
        sendJson(socketsByPlayer.get(targetProfile.id), { type: 'trade:updated', payload: { trade } });
        sendJson(ws, { type: 'toast', payload: { message: `Proposta de troca enviada para ${targetProfile.name}!`, kind: 'success' } });
      } else if (msg.type === 'trade:respond') {
        const tradeId = String(payload.tradeId || '');
        const accept = Boolean(payload.accept);
        const trade = state.trades[tradeId];
        if (!trade || trade.status !== 'pendente' || trade.toId !== profile.id) return;

        const fromProfile = state.profiles[trade.fromId];
        if (!fromProfile) return;

        if (!accept) {
          trade.status = 'recusada';
          scheduleSave();
          sendJson(ws, { type: 'trade:updated', payload: { trade } });
          sendJson(socketsByPlayer.get(fromProfile.id), { type: 'trade:updated', payload: { trade } });
          return;
        }

        // Validate both still have items & coins
        if (fromProfile.moedas < trade.offeredCoins || profile.moedas < trade.requestedCoins) {
          sendJson(ws, { type: 'toast', payload: { message: 'Moedas insuficientes para concluir a troca.', kind: 'error' } });
          return;
        }
        const fromHasAll = trade.offeredInstanceIds.every((id) => fromProfile.inventory.some((i) => i.instanceId === id));
        const toHasAll = trade.requestedInstanceIds.every((id) => profile.inventory.some((i) => i.instanceId === id));
        if (!fromHasAll || !toHasAll) {
          sendJson(ws, { type: 'toast', payload: { message: 'Um dos itens não está mais no inventário.', kind: 'error' } });
          return;
        }

        // Swap coins
        fromProfile.moedas = fromProfile.moedas - trade.offeredCoins + trade.requestedCoins;
        profile.moedas = profile.moedas - trade.requestedCoins + trade.offeredCoins;

        // Swap items
        for (const instId of trade.offeredInstanceIds) {
          const idx = fromProfile.inventory.findIndex((i) => i.instanceId === instId);
          if (idx >= 0) {
            const [moved] = fromProfile.inventory.splice(idx, 1);
            const changedLots = removeFurnitureFromAllLots(fromProfile, instId);
            for (const li of changedLots) {
              const rk = formatEspacoRoomKey(fromProfile.id, li);
              broadcastToRoom(rk, {
                type: 'space:updated',
                payload: { roomKey: rk, spaceInfo: getSpacePayload(fromProfile.id, li) },
              });
            }
            profile.inventory.push(moved);
          }
        }
        for (const instId of trade.requestedInstanceIds) {
          const idx = profile.inventory.findIndex((i) => i.instanceId === instId);
          if (idx >= 0) {
            const [moved] = profile.inventory.splice(idx, 1);
            const changedLots = removeFurnitureFromAllLots(profile, instId);
            for (const li of changedLots) {
              const rk = formatEspacoRoomKey(profile.id, li);
              broadcastToRoom(rk, {
                type: 'space:updated',
                payload: { roomKey: rk, spaceInfo: getSpacePayload(profile.id, li) },
              });
            }
            fromProfile.inventory.push(moved);
          }
        }

        trade.status = 'aceita';
        updateQuestProgress(profile, 'trades_or_buys', 1);
        updateQuestProgress(fromProfile, 'trades_or_buys', 1);
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, { type: 'trade:updated', payload: { trade } });
        sendJson(ws, { type: 'toast', payload: { message: 'Troca concluída com sucesso!', kind: 'success' } });

        const fromWs = socketsByPlayer.get(fromProfile.id);
        sendJson(fromWs, { type: 'profile:update', payload: { profile: fromProfile } });
        sendJson(fromWs, { type: 'trade:updated', payload: { trade } });
        sendJson(fromWs, { type: 'toast', payload: { message: `${profile.name} aceitou sua troca!`, kind: 'success' } });
      } else if (msg.type === 'friend:add') {
        const friendId = String(payload.friendId || '');
        const friendName = String(payload.friendName || '');
        if (!friendId || friendId === profile.id) return;

        if (!profile.friends.some((f) => f.id === friendId)) {
          profile.friends.push({ id: friendId, name: friendName || 'Morador' });
          updateQuestProgress(profile, 'friends', 1);
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, { type: 'toast', payload: { message: `${friendName} adicionado aos amigos!`, kind: 'success' } });
        }
      } else if (msg.type === 'minigame:complete') {
        ensureProfileFields(profile);
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou! Não pode trabalhar agora.', kind: 'error' } });
          return;
        }
        const rt = getOrCreateRuntime(profile);
        if (rt.exact.energia <= 1) {
          sendJson(ws, { type: 'toast', payload: { message: 'Sem energia para trabalhar! Descanse em uma cama primeiro.', kind: 'error' } });
          return;
        }
        const jobName = String(payload.jobName || 'Trabalho');
        const passed = payload.passed !== false && Number(payload.rewardCoins ?? 0) > 0;
        const mult = getEnergyCostMultiplier(profile);
        if (!passed) {
          const failEnergy = Math.round(12 * mult);
          addNeedDelta(profile, 'energia', -12 * mult);
          addNeedDelta(profile, 'fome', -3);
          addNeedDelta(profile, 'higiene', -3);
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: `❌ Turno falhou em "${jobName}"! Nenhuma moeda ganha (-${failEnergy}% Energia).`,
              kind: 'error',
            },
          });
          return;
        }
        const rewardCoins = Math.max(4, Math.min(12, Math.floor(Number(payload.rewardCoins || 5))));
        const energyCost = Math.round(30 * mult);
        profile.moedas += rewardCoins;
        addNeedDelta(profile, 'energia', -30 * mult);
        addNeedDelta(profile, 'fome', -6);
        addNeedDelta(profile, 'diversao', -10 * mult);
        addNeedDelta(profile, 'higiene', -8);
        const workTask = profile.routineTasks.find((t) => t.id === 'rt_trabalho');
        if (workTask && !workTask.done) {
          workTask.done = true;
          profile.moedas += workTask.rewardCoins;
        }
        updateQuestProgress(profile, 'minigames', 1);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `Turno em "${jobName}": +${rewardCoins} moedas (-${energyCost}% Energia)!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'quest:claim') {
        const questId = String(payload.questId || '');
        const quest = profile.quests.find((q) => q.id === questId);
        if (!quest || quest.claimed || quest.progress < quest.target) return;

        quest.claimed = true;
        profile.moedas += quest.rewardCoins;
        profile.gemas += quest.rewardGems;
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `Missão "${quest.title}" resgatada: +${quest.rewardCoins} moedas e +${quest.rewardGems} gemas!`,
            kind: 'success',
          },
        });
      } else if (
        msg.type === 'profession:unlock' ||
        msg.type === 'profession:confirm' ||
        msg.type === 'profession:start_trial'
      ) {
        ensureProfessionProfile(profile);
        const profId = String(payload.professionId || '') as ProfessionId;
        if (!PROFESSION_IDS.includes(profId)) return;
        const prof = profile.profession!;
        const skill = prof.skills[profId];

        if (skill.unlocked) {
          prof.mode = 'confirmed';
          prof.activeProfession = profId;
          prof.xp = skill.xp;
          prof.level = skill.level;
          prof.skillPoints = skill.skillPoints;
          prof.unlockedSkills = [...skill.unlockedSkills];
          prof.specialization = skill.specialization;
          syncWorldPlayerProfession(profile, worldPlayer);
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: `${PROFESSIONS_META[profId].emoji} Profissão destacada: ${PROFESSIONS_META[profId].name} (Nv.${skill.level}).`,
              kind: 'info',
            },
          });
          return;
        }

        const availableSlots = getAvailableProfessionSlots(prof);
        if (availableSlots <= 0) {
          const nextLvl = getNextUnlockTotalLevel(prof);
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: nextLvl
                ? `Sem slots disponíveis! Alcance Nível Total ${nextLvl} para liberar mais uma profissão.`
                : 'Todas as profissões já foram liberadas!',
              kind: 'error',
            },
          });
          return;
        }

        skill.unlocked = true;
        skill.unlockedAt = Date.now();
        skill.level = Math.max(1, skill.level);
        prof.mode = 'confirmed';
        prof.activeProfession = profId;
        if (!prof.confirmedAt) prof.confirmedAt = Date.now();
        prof.xp = skill.xp;
        prof.level = skill.level;
        prof.skillPoints = skill.skillPoints;
        prof.unlockedSkills = [...skill.unlockedSkills];
        prof.specialization = skill.specialization;
        prof.claimedStarterKit = true;

        // Grant starter Tier-1 tool for the newly unlocked profession if player has none
        const starterId = PROFESSIONS_META[profId].starterToolId;
        const alreadyHasStarter = profile.inventory.some((i) => i.itemId === starterId);
        if (!alreadyHasStarter) {
          const created = addItemToInventory(profile, starterId);
          if (created && !profile.equippedTools![profId]) {
            profile.equippedTools![profId] = created.instanceId;
          }
        }

        syncWorldPlayerProfession(profile, worldPlayer);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `${PROFESSIONS_META[profId].emoji} Nova profissão liberada: ${PROFESSIONS_META[profId].name}! Ferramenta inicial recebida.`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'profession:stop_trial') {
        // Legacy no-op cleanly handled
        ensureProfessionProfile(profile);
        sendJson(ws, { type: 'profile:update', payload: { profile } });
      } else if (msg.type === 'profession:set_active' || msg.type === 'profession:change') {
        ensureProfessionProfile(profile);
        const profId = String(payload.professionId || '') as ProfessionId;
        if (!PROFESSION_IDS.includes(profId)) return;
        const prof = profile.profession!;
        const skill = prof.skills[profId];
        if (!skill.unlocked) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Libere ${PROFESSIONS_META[profId].name} primeiro quando tiver um slot disponível.`, kind: 'error' },
          });
          return;
        }
        prof.mode = 'confirmed';
        prof.activeProfession = profId;
        prof.xp = skill.xp;
        prof.level = skill.level;
        prof.skillPoints = skill.skillPoints;
        prof.unlockedSkills = [...skill.unlockedSkills];
        prof.specialization = skill.specialization;

        syncWorldPlayerProfession(profile, worldPlayer);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `${PROFESSIONS_META[profId].emoji} Título ativo alterado para ${PROFESSIONS_META[profId].name} Nv.${skill.level}.`,
            kind: 'info',
          },
        });
      } else if (msg.type === 'profession:unlock_skill') {
        ensureProfessionProfile(profile);
        const prof = profile.profession!;
        const targetPid = (String(payload.professionId || prof.activeProfession || '') as ProfessionId);
        if (!PROFESSION_IDS.includes(targetPid)) return;
        const skillProg = prof.skills[targetPid];
        if (!skillProg.unlocked) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Libere ${PROFESSIONS_META[targetPid].name} antes de evoluir talentos.`, kind: 'error' },
          });
          return;
        }
        const skillId = String(payload.skillId || '');
        const meta = PROFESSIONS_META[targetPid];
        const sk = meta.skills.find((s) => s.id === skillId);
        if (!sk) return;
        if (skillProg.unlockedSkills.includes(skillId)) return;
        if (skillProg.level < sk.requiredLevel) {
          sendJson(ws, { type: 'toast', payload: { message: `Requer Nível ${sk.requiredLevel} em ${meta.name}.`, kind: 'error' } });
          return;
        }
        if (skillProg.skillPoints < sk.costPoints) {
          sendJson(ws, { type: 'toast', payload: { message: `Pontos de talento insuficientes em ${meta.name}!`, kind: 'error' } });
          return;
        }
        skillProg.skillPoints -= sk.costPoints;
        skillProg.unlockedSkills.push(skillId);
        if (prof.activeProfession === targetPid) {
          prof.skillPoints = skillProg.skillPoints;
          prof.unlockedSkills = [...skillProg.unlockedSkills];
        }
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `🌟 Talento de ${meta.name} desbloqueado: ${sk.name}!`, kind: 'success' },
        });
      } else if (msg.type === 'profession:choose_spec') {
        ensureProfessionProfile(profile);
        const prof = profile.profession!;
        const targetPid = (String(payload.professionId || prof.activeProfession || '') as ProfessionId);
        if (!PROFESSION_IDS.includes(targetPid)) return;
        const skillProg = prof.skills[targetPid];
        if (!skillProg.unlocked) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Libere ${PROFESSIONS_META[targetPid].name} antes de escolher especialização.`, kind: 'error' },
          });
          return;
        }
        if (skillProg.specialization) {
          sendJson(ws, { type: 'toast', payload: { message: 'Especialização já definida para esta profissão.', kind: 'error' } });
          return;
        }
        const specId = String(payload.specId || '');
        const meta = PROFESSIONS_META[targetPid];
        const sp = meta.specializations.find((s) => s.id === specId);
        if (!sp) return;
        if (skillProg.level < sp.requiredLevel) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Especializações desbloqueiam no Nível ${sp.requiredLevel} em ${meta.name}.`, kind: 'error' },
          });
          return;
        }
        skillProg.specialization = sp.id;
        if (prof.activeProfession === targetPid) {
          prof.specialization = sp.id;
        }
        syncWorldPlayerProfession(profile, worldPlayer);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `🎖️ Especialização em ${meta.name}: ${sp.name}!`, kind: 'success' },
        });
      } else if (msg.type === 'profession:buy_starter_tool' || msg.type === 'profession:buy_tool') {
        ensureProfessionProfile(profile);
        const itemId = String(payload.itemId || '');
        const cat = getCatalogItem(itemId);
        if (!cat || cat.category !== 'ferramenta' || !cat.toolStats || cat.toolStats.tier !== 1) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: 'A Guilda fornece apenas ferramentas básicas Tier 1. Tier 2–4 são forjados por Ferreiros!', kind: 'error' },
          });
          return;
        }
        if (profile.moedas < cat.priceCoins) {
          sendJson(ws, { type: 'toast', payload: { message: `Precisa de ${cat.priceCoins} moedas.`, kind: 'error' } });
          return;
        }
        profile.moedas -= cat.priceCoins;
        const created = addItemToInventory(profile, cat.id);
        if (created) {
          profile.equippedTools![cat.toolStats.professionId] = created.instanceId;
        }
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `${cat.name} adquirida e equipada (-${cat.priceCoins} moedas)!`, kind: 'success' },
        });
      } else if (msg.type === 'tool:equip') {
        ensureProfessionProfile(profile);
        const instanceId = String(payload.instanceId || '');
        const inv = profile.inventory.find((i) => i.instanceId === instanceId);
        if (!inv) return;
        const cat = getCatalogItem(inv.itemId);
        if (!cat?.toolStats) return;

        const check = canUseTool(profile, cat, inv);
        if (!check.ok) {
          sendJson(ws, { type: 'toast', payload: { message: check.reason, kind: 'error' } });
          return;
        }
        profile.equippedTools![cat.toolStats.professionId] = inv.instanceId;
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `🔧 ${cat.name} equipada para ${PROFESSIONS_META[cat.toolStats.professionId].name}!`, kind: 'success' },
        });
      } else if (msg.type === 'tool:repair') {
        ensureProfessionProfile(profile);
        const instanceId = String(payload.instanceId || '');
        const mode = payload.mode === 'kit' ? 'kit' : 'coins';
        const inv = profile.inventory.find((i) => i.instanceId === instanceId);
        if (!inv) return;
        const cat = getCatalogItem(inv.itemId);
        if (!cat?.toolStats) return;

        const maxD = inv.maxDurability ?? cat.toolStats.maxDurability;
        const curD = inv.durability ?? maxD;
        if (curD >= maxD) {
          sendJson(ws, { type: 'toast', payload: { message: 'Esta ferramenta já está com 100% de durabilidade.', kind: 'info' } });
          return;
        }

        if (mode === 'kit') {
          if (!consumeInventoryItemById(profile, 'kit_reparo', 1)) {
            sendJson(ws, {
              type: 'toast',
              payload: { message: 'Você não tem Kit de Reparo! Compre no Mercado ou peça a um Ferreiro.', kind: 'error' },
            });
            return;
          }
          inv.durability = Math.min(maxD, curD + Math.ceil(maxD * 0.6));
          inv.maxDurability = maxD;
        } else {
          // Coin repair at Ferreiro anvil / Guild bench
          const cost = getEffectiveRepairCost(profile, cat, inv, state.economyConfig);
          if (profile.moedas < cost) {
            sendJson(ws, { type: 'toast', payload: { message: `Reparo custa ${cost} moedas.`, kind: 'error' } });
            return;
          }
          profile.moedas -= cost;
          inv.durability = maxD;
          inv.maxDurability = maxD;
        }

        profile.profession!.stats.repaired += 1;
        let xpMsg = '';
        if (getProfessionSkill(profile.profession, 'ferreiro').unlocked) {
          const xpRes = applyProfessionXp(profile, 'ferreiro', 14, state.economyConfig);
          if (xpRes.gainedXp > 0) xpMsg = ` (+${xpRes.gainedXp} XP Ferreiro${xpRes.leveledUp ? ` · Nv.${xpRes.newLevel}!` : ''})`;
        }

        syncWorldPlayerProfession(profile, worldPlayer);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
        sendJson(ws, {
          type: 'toast',
          payload: { message: `🛠️ ${cat.name} reparada (${inv.durability}/${maxD})${xpMsg}!`, kind: 'success' },
        });
      } else if (msg.type === 'item:use_utility') {
        ensureProfileFields(profile);
        const lot = resolveTargetOwnedLot(profile, worldPlayer);
        const instanceId = String(payload.instanceId || '');
        const inv = profile.inventory.find((i) => i.instanceId === instanceId);
        if (!inv) return;
        const cat = getCatalogItem(inv.itemId);
        if (!cat || cat.category !== 'estrutura' || !cat.structureBlocks) return;

        if (lot.plotMaxBlocks >= MAX_PLOT_GRID_BLOCKS) {
          sendJson(ws, { type: 'toast', payload: { message: `${lot.name} já atingiu o tamanho máximo!`, kind: 'info' } });
          return;
        }

        const consumed = consumeInventoryInstance(profile, instanceId, 1);
        if (!consumed) return;

        lot.plotMaxBlocks = Math.min(MAX_PLOT_GRID_BLOCKS, lot.plotMaxBlocks + cat.structureBlocks);
        syncLegacyFieldsFromLot1(profile);
        scheduleSave();
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        const ownRoomKey = formatEspacoRoomKey(profile.id, lot.lotIndex);
        broadcastToRoom(ownRoomKey, {
          type: 'space:updated',
          payload: { roomKey: ownRoomKey, spaceInfo: getSpacePayload(profile.id, lot.lotIndex) },
        });
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `🏗️ Kit Estrutural aplicado ao ${lot.name}! Agora suporta até ${lot.plotMaxBlocks} blocos!`,
            kind: 'success',
          },
        });
      } else if (msg.type === 'gather:execute') {
        ensureProfileFields(profile);
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou e não pode coletar recursos.', kind: 'error' } });
          return;
        }
        const now = Date.now();
        const lastAt = lastGatherAtByPlayer.get(playerId) || 0;
        if (now - lastAt < state.economyConfig.gatherCooldownMs) {
          sendJson(ws, { type: 'toast', payload: { message: 'Aguarde um instante antes de coletar novamente.', kind: 'info' } });
          return;
        }

        const nodeId = String(payload.nodeId || '');
        const def = getNodeDefById(nodeId);
        const playerNodes = ensurePlayerResourceNodes(profile, now, state.economyConfig);
        const nodeSt = playerNodes[nodeId];
        if (!def || !nodeSt) return;

        if (!isPlayerWithinNodeRange(worldPlayer, def)) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Aproxime-se de ${def.name} para coletar!`, kind: 'error' },
          });
          return;
        }
        if (nodeSt.charges <= 0) {
          const waitSec = nodeSt.nextRespawnAt ? Math.max(1, Math.ceil((nodeSt.nextRespawnAt - now) / 1000)) : def.respawnSeconds;
          sendJson(ws, {
            type: 'toast',
            payload: { message: `${def.name} esgotado para você! Regenera em ${waitSec}s.`, kind: 'info' },
          });
          return;
        }

        ensureProfessionProfile(profile);
        const prof = profile.profession!;
        const skill = getProfessionSkill(prof, def.professionId);
        const profName = PROFESSIONS_META[def.professionId].name;

        if (!skill.unlocked) {
          const slots = getAvailableProfessionSlots(prof);
          sendJson(ws, {
            type: 'toast',
            payload: {
              message:
                slots > 0
                  ? `Libere ${profName} gratuitamente no menu Ofícios para coletar aqui!`
                  : `Profissão ${profName} bloqueada. Evolua suas profissões para liberar novo slot a cada 10 níveis!`,
              kind: 'error',
            },
          });
          return;
        }
        if (skill.level < def.minLevel) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Requer Nível ${def.minLevel} em ${profName} (atual Nv.${skill.level}).`, kind: 'error' },
          });
          return;
        }

        // Check equipped tool or auto-find an eligible unbroken tool in inventory
        let equipped = resolveEquippedTool(profile, def.professionId);
        if (!equipped) {
          const fallback = profile.inventory.find((i) => {
            const c = getCatalogItem(i.itemId);
            return c?.toolStats?.professionId === def.professionId && canUseTool(profile, c, i).ok;
          });
          if (fallback) {
            profile.equippedTools![def.professionId] = fallback.instanceId;
            equipped = resolveEquippedTool(profile, def.professionId);
          }
        }
        if (equipped) {
          const check = canUseTool(profile, equipped.cat, equipped.inv);
          if (!check.ok) {
            sendJson(ws, { type: 'toast', payload: { message: check.reason, kind: 'error' } });
            return;
          }
          if ((equipped.cat.toolStats?.tier || 1) < def.requiredToolTier) {
            sendJson(ws, {
              type: 'toast',
              payload: {
                message: `Este ponto exige ferramenta Tier ${def.requiredToolTier}+ forjada por um Ferreiro!`,
                kind: 'error',
              },
            });
            return;
          }
        } else if (def.requiredToolTier > 0) {
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: `Equipe uma ferramenta de ${profName} (compre na Guilda em Ofícios)!`,
              kind: 'error',
            },
          });
          return;
        }

        const bonuses = getProfessionBonuses(prof, def.professionId);
        const mult = getEnergyCostMultiplier(profile);
        const energyCost = Math.max(2, Math.round(def.energyCost * mult * (1 - bonuses.energySave)));
        const rt = getOrCreateRuntime(profile);
        if (rt.exact.energia < energyCost) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: 'Energia baixa! Descanse na cama ou consuma um chá/refeição.', kind: 'error' },
          });
          return;
        }

        const rawScore = Number(payload.minigameScore ?? payload.score ?? 1);
        const failed = Boolean(payload.failed) || rawScore < 0.65;

        let toolBrokenNotice = '';
        if (equipped) {
          const skipWear = !failed && Math.random() < bonuses.durabilitySave;
          if (!skipWear) {
            const maxD = equipped.inv.maxDurability ?? equipped.cat.toolStats!.maxDurability;
            const nextD = Math.max(0, (equipped.inv.durability ?? maxD) - 1);
            equipped.inv.durability = nextD;
            if (nextD === 0) {
              delete profile.equippedTools![def.professionId];
              toolBrokenNotice = ` ⚠️ ${equipped.cat.name} quebrou!`;
            }
          }
        }

        lastGatherAtByPlayer.set(playerId, now);

        if (failed) {
          const failEnergy = Math.max(2, Math.round(energyCost * 0.6));
          addNeedDelta(profile, 'energia', -failEnergy);
          addNeedDelta(profile, 'higiene', -0.8);
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: {
              message: `❌ Coleta falhou em ${def.name}! Nenhum recurso ou XP obtido.${toolBrokenNotice}`,
              kind: 'error',
            },
          });
          return;
        }

        addNeedDelta(profile, 'energia', -energyCost);
        addNeedDelta(profile, 'higiene', -1.2);

        const score = Math.max(0.75, Math.min(1.5, rawScore));
        const toolEff = equipped?.cat.toolStats?.efficiency ?? 1.0;
        const toolRare = equipped?.cat.toolStats?.rareBonus ?? 0;
        const toolTier = equipped?.cat.toolStats?.tier ?? 1;
        const nodeTier = def.tier || Math.max(1, Math.min(4, def.requiredToolTier || 1));

        const gainedItems: Array<{ name: string; qty: number; qualityLabel: string }> = [];
        const baseQty = rollRangeInt(def.primaryDrop.minQty, def.primaryDrop.maxQty);
        const yieldMult = (toolEff * 0.9 + bonuses.yieldBonus) * (score >= 1.2 ? 1.15 : 1);
        const primaryQty = Math.max(1, Math.round(baseQty * yieldMult));
        const primaryQuality = rollGatherQuality(nodeTier, toolTier, score, bonuses.rareBonus + toolRare);
        addItemToInventory(profile, def.primaryDrop.itemId, {
          quantity: primaryQty,
          quality: primaryQuality,
        });
        gainedItems.push({
          name: getCatalogItem(def.primaryDrop.itemId)?.name || def.primaryDrop.itemId,
          qty: primaryQty,
          qualityLabel: primaryQuality !== 'comum' ? ` [${QUALITY_META[primaryQuality].label}]` : '',
        });

        const scoreChanceMult = score >= 1.18 ? 1.15 : 1.0;

        if (def.secondaryDrop) {
          const secChance =
            (def.secondaryDrop.chance + bonuses.rareBonus * 0.3 + toolRare * 0.3) * scoreChanceMult;
          if (Math.random() < secChance) {
            const q2 = rollRangeInt(def.secondaryDrop.minQty, def.secondaryDrop.maxQty);
            const qual2 = rollGatherQuality(nodeTier, toolTier, score, bonuses.rareBonus + toolRare);
            addItemToInventory(profile, def.secondaryDrop.itemId, {
              quantity: q2,
              quality: qual2,
            });
            gainedItems.push({
              name: getCatalogItem(def.secondaryDrop.itemId)?.name || def.secondaryDrop.itemId,
              qty: q2,
              qualityLabel: qual2 !== 'comum' ? ` [${QUALITY_META[qual2].label}]` : '',
            });
          }
        }
        if (def.rareDrop) {
          const rareChance =
            (def.rareDrop.chance + bonuses.rareBonus * 0.5 + toolRare * 0.5) * scoreChanceMult;
          if (Math.random() < rareChance) {
            const q3 = rollRangeInt(def.rareDrop.minQty, def.rareDrop.maxQty);
            const qual3 = rollGatherQuality(
              nodeTier,
              toolTier,
              Math.max(1.0, score),
              bonuses.rareBonus + toolRare + 0.08
            );
            addItemToInventory(profile, def.rareDrop.itemId, {
              quantity: q3,
              quality: qual3,
            });
            gainedItems.push({
              name: getCatalogItem(def.rareDrop.itemId)?.name || def.rareDrop.itemId,
              qty: q3,
              qualityLabel: qual3 !== 'comum' ? ` [${QUALITY_META[qual3].label}]` : '',
            });
          }
        }

        // Deplete ONLY THIS PLAYER's node charge & start respawn timer
        nodeSt.charges = Math.max(0, nodeSt.charges - 1);
        if (!nodeSt.nextRespawnAt) {
          nodeSt.nextRespawnAt = now + Math.round(def.respawnSeconds * 1000 * state.economyConfig.nodeRespawnMultiplier);
        }

        prof.stats.gathered += primaryQty;
        const xpRes = applyProfessionXp(profile, def.professionId, def.xpReward, state.economyConfig);
        syncWorldPlayerProfession(profile, worldPlayer);
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        sendJson(ws, { type: 'nodes:updated', payload: { resourceNodes: Object.values(playerNodes) } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });

        const dropStr = gainedItems.map((g) => `+${g.qty} ${g.name}${g.qualityLabel}`).join(', ');
        const xpStr = ` (+${xpRes.gainedXp} XP ${profName}${xpRes.leveledUp ? ` · 🆙 Nv.${xpRes.newLevel}!` : ''})`;
        const unlockStr = xpRes.unlockedNewSlot ? ' 🎉 +1 nova profissão liberada em Ofícios!' : '';
        sendJson(ws, {
          type: 'toast',
          payload: { message: `${def.emoji} ${dropStr}${xpStr}${unlockStr}${toolBrokenNotice}`, kind: 'success' },
        });
      } else if (msg.type === 'craft:execute') {
        ensureProfileFields(profile);
        ensureProfessionProfile(profile);
        if (profile.isFainted) {
          sendJson(ws, { type: 'toast', payload: { message: 'Você desmaiou e não pode fabricar agora.', kind: 'error' } });
          return;
        }
        const recipeId = String(payload.recipeId || '');
        const recipe = getRecipeById(recipeId);
        if (!recipe) return;

        const batchQty = Math.max(1, Math.min(5, Math.floor(Number(payload.quantity || 1))));
        const prof = profile.profession!;
        const skill = getProfessionSkill(prof, recipe.professionId);
        const profName = PROFESSIONS_META[recipe.professionId].name;

        if (!skill.unlocked) {
          const slots = getAvailableProfessionSlots(prof);
          sendJson(ws, {
            type: 'toast',
            payload: {
              message:
                slots > 0
                  ? `Libere ${profName} em Ofícios para fabricar esta receita!`
                  : `Profissão ${profName} bloqueada. Evolua suas profissões (+10 níveis) para liberar novo slot!`,
              kind: 'error',
            },
          });
          return;
        }
        if (skill.level < recipe.minLevel) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Requer Nível ${recipe.minLevel} em ${profName} (atual Nv.${skill.level}).`, kind: 'error' },
          });
          return;
        }
        if (recipe.requiredSkillId && !skill.unlockedSkills.includes(recipe.requiredSkillId)) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: `Desbloqueie o talento necessário de ${profName} em Talentos.`, kind: 'error' },
          });
          return;
        }

        let equipped = resolveEquippedTool(profile, recipe.professionId);
        if (!equipped && recipe.requiredToolTier) {
          const fallback = profile.inventory.find((i) => {
            const c = getCatalogItem(i.itemId);
            return c?.toolStats?.professionId === recipe.professionId && canUseTool(profile, c, i).ok;
          });
          if (fallback) {
            profile.equippedTools![recipe.professionId] = fallback.instanceId;
            equipped = resolveEquippedTool(profile, recipe.professionId);
          }
        }
        if (recipe.requiredToolTier) {
          if (equipped) {
            const check = canUseTool(profile, equipped.cat, equipped.inv);
            if (!check.ok) {
              sendJson(ws, { type: 'toast', payload: { message: check.reason, kind: 'error' } });
              return;
            }
            if ((equipped.cat.toolStats?.tier || 1) < recipe.requiredToolTier) {
              sendJson(ws, {
                type: 'toast',
                payload: { message: `Requer ferramenta Tier ${recipe.requiredToolTier}+ forjada por Ferreiro!`, kind: 'error' },
              });
              return;
            }
          } else {
            sendJson(ws, {
              type: 'toast',
              payload: { message: `Equipe sua ferramenta de ${profName}!`, kind: 'error' },
            });
            return;
          }
        }

        const feeCoins = (recipe.craftFeeCoins ?? 0) * batchQty;
        if (profile.moedas < feeCoins) {
          sendJson(ws, { type: 'toast', payload: { message: `Falta ${feeCoins} moedas de taxa da oficina.`, kind: 'error' } });
          return;
        }

        for (const ing of recipe.ingredients) {
          const need = ing.quantity * batchQty;
          const have = countInventoryItem(profile, ing.itemId);
          if (have < need) {
            const ingName = getCatalogItem(ing.itemId)?.name || ing.itemId;
            sendJson(ws, {
              type: 'toast',
              payload: { message: `Faltam insumos: ${ingName} (${have}/${need}). Compre no Mercado!`, kind: 'error' },
            });
            return;
          }
        }

        const bonuses = getProfessionBonuses(prof, recipe.professionId);
        const energyCost = Math.max(2, Math.round(recipe.energyCost * batchQty * (1 - bonuses.energySave)));
        const rt = getOrCreateRuntime(profile);
        if (rt.exact.energia < energyCost) {
          sendJson(ws, {
            type: 'toast',
            payload: { message: 'Energia insuficiente! Coma ou descanse antes de fabricar.', kind: 'error' },
          });
          return;
        }

        for (const ing of recipe.ingredients) {
          consumeInventoryItemById(profile, ing.itemId, ing.quantity * batchQty);
        }
        profile.moedas -= feeCoins;
        addNeedDelta(profile, 'energia', -energyCost);

        const outCat = getCatalogItem(recipe.outputItemId);
        let totalProduced = recipe.outputQuantity * batchQty;
        if (outCat?.stackable && Math.random() < bonuses.yieldBonus) {
          totalProduced += 1;
        }

        const toolTier = equipped?.cat.toolStats?.tier ?? 1;
        const qual = rollCraftQuality(bonuses.craftQuality, toolTier);

        const customMaxDur = outCat?.toolStats
          ? Math.round(outCat.toolStats.maxDurability * qual.durabilityMult)
          : undefined;

        addItemToInventory(profile, recipe.outputItemId, {
          quantity: totalProduced,
          durability: customMaxDur,
          maxDurability: customMaxDur,
          quality: !outCat?.stackable ? qual.quality : undefined,
          craftedBy: profile.name,
        });

        let brokenMsg = '';
        if (equipped) {
          const skipWear = Math.random() < bonuses.durabilitySave;
          if (!skipWear) {
            const maxD = equipped.inv.maxDurability ?? equipped.cat.toolStats!.maxDurability;
            const nextD = Math.max(0, (equipped.inv.durability ?? maxD) - batchQty);
            equipped.inv.durability = nextD;
            if (nextD === 0) {
              delete profile.equippedTools![recipe.professionId];
              brokenMsg = ` ⚠️ ${equipped.cat.name} quebrou!`;
            }
          }
        }

        prof.stats.crafted += totalProduced;
        const xpRes = applyProfessionXp(profile, recipe.professionId, recipe.xpReward * batchQty, state.economyConfig);
        syncWorldPlayerProfession(profile, worldPlayer);
        scheduleSave();

        sendJson(ws, { type: 'profile:update', payload: { profile } });
        broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });

        const qualTag = !outCat?.stackable && qual.quality !== 'comum' ? ` [${qual.quality.toUpperCase()}]` : '';
        const xpStr = ` (+${xpRes.gainedXp} XP ${profName}${xpRes.leveledUp ? ` · 🆙 Nv.${xpRes.newLevel}!` : ''})`;
        const unlockStr = xpRes.unlockedNewSlot ? ' 🎉 +1 nova profissão liberada!' : '';
        sendJson(ws, {
          type: 'toast',
          payload: {
            message: `⚒️ Produzido: ${totalProduced}x ${outCat?.name || recipe.outputItemId}${qualTag}${xpStr}${unlockStr}${brokenMsg}`,
            kind: 'success',
          },
        });
      }
    });

    ws.on('close', () => {
      const playerId = playerBySocket.get(ws);
      if (playerId) {
        const p = activePlayers.get(playerId);
        const oldRoom = p?.roomKey;
        releasePlayerSeats(playerId, true);
        activePlayers.delete(playerId);
        socketsByPlayer.delete(playerId);
        playerBySocket.delete(ws);

        if (oldRoom) {
          broadcastToRoom(oldRoom, {
            type: 'room:players',
            payload: { roomKey: oldRoom, players: getRoomPlayers(oldRoom) },
          });
        }
        broadcastAll({
          type: 'city:counts',
          payload: {
            roomCounts: getRoomCounts(),
            onlinePlayers: Array.from(activePlayers.values()).map((pl) => ({ id: pl.id, name: pl.name, roomKey: pl.roomKey })),
          },
        });
        if (oldRoom && oldRoom.startsWith('espaco:')) {
          broadcastAll({
            type: 'lots:updated',
            payload: { lotsDirectory: getLotsDirectoryPayload() },
          });
        }
      }
    });
  });

  // Authoritative 1-second Survival Tick Loop (Energia, Fome, Diversão, Higiene, Blackout & Desmaio)
  setInterval(() => {
    const now = Date.now();
    for (const [playerId, worldPlayer] of activePlayers.entries()) {
      const profile = state.profiles[playerId];
      const ws = socketsByPlayer.get(playerId);
      if (!profile) continue;
      ensureProfileFields(profile);
      const rt = getOrCreateRuntime(profile);

      // 1) Handle Fainted state (4 minutes unless fed by another player)
      if (profile.isFainted) {
        if (profile.faintedUntil && now >= profile.faintedUntil) {
          profile.isFainted = false;
          profile.faintedUntil = null;
          profile.hungerZeroSince = null;
          profile.lastMealAt = now;
          setNeedValue(profile, 'fome', 20);
          worldPlayer.isFainted = false;
          worldPlayer.faintedUntil = null;
          worldPlayer.action = 'parado';
          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'toast',
            payload: { message: 'Você acordou do desmaio! Procure comida urgente (Fome: 20%).', kind: 'info' },
          });
          broadcastToRoom(worldPlayer.roomKey, {
            type: 'player:updated',
            payload: { player: worldPlayer },
          });
        }
        continue;
      }

      if (profile.godMode) {
        setNeedValue(profile, 'energia', 100);
        setNeedValue(profile, 'fome', 100);
        setNeedValue(profile, 'diversao', 100);
        setNeedValue(profile, 'higiene', 100);
        profile.energyZeroSince = null;
        profile.hungerZeroSince = null;
        sendJson(ws, { type: 'profile:update', payload: { profile } });
        continue;
      }

      const isHungry = rt.exact.fome <= SURVIVAL_CONFIG.HUNGRY_PENALTY_THRESHOLD;
      const mult = isHungry ? SURVIVAL_CONFIG.HUNGRY_PENALTY_MULTIPLIER : 1;

      // 2) Hunger silent drain (6 minutes = 360s full bar)
      addNeedDelta(profile, 'fome', -(100 / SURVIVAL_CONFIG.HUNGER_DURATION_SECONDS));

      if (rt.exact.fome <= 0) {
        if (!profile.hungerZeroSince) {
          profile.hungerZeroSince = now;
          sendJson(ws, {
            type: 'toast',
            payload: { message: '🚨 FOME ZERADA! Coma algo em 10 segundos ou você vai desmaiar!', kind: 'error' },
          });
        } else if (now - profile.hungerZeroSince >= SURVIVAL_CONFIG.ZERO_GRACE_SECONDS * 1000) {
          profile.isFainted = true;
          profile.faintedUntil = now + SURVIVAL_CONFIG.FAINT_DURATION_SECONDS * 1000;
          profile.isRestingOnBed = false;
          profile.activeActivity = null;
          profile.energyZeroSince = null;

          worldPlayer.isFainted = true;
          worldPlayer.faintedUntil = profile.faintedUntil;
          worldPlayer.isRestingOnBed = false;
          worldPlayer.activeActivity = null;
          worldPlayer.action = 'deitado';

          const sysMsg: ChatMessage = {
            id: `sys_faint_${Date.now()}_${Math.random().toString(36).slice(2, 5)}`,
            roomKey: worldPlayer.roomKey,
            senderId: 'sistema',
            senderName: 'OASIS',
            senderColor: '#fb7185',
            text: `${profile.name} desmaiou de fome! Jogadores com comida podem alimentá-lo para levantá-lo.`,
            type: 'system',
            timestamp: now,
          };
          if (!roomChats[worldPlayer.roomKey]) roomChats[worldPlayer.roomKey] = [];
          roomChats[worldPlayer.roomKey].push(sysMsg);

          scheduleSave();
          sendJson(ws, { type: 'profile:update', payload: { profile } });
          sendJson(ws, {
            type: 'player:faint',
            payload: { faintedUntil: profile.faintedUntil, message: 'VOCÊ DESMAIOU! ESPERANDO AJUDA...' },
          });
          broadcastToRoom(worldPlayer.roomKey, { type: 'chat:message', payload: { message: sysMsg } });
          broadcastToRoom(worldPlayer.roomKey, { type: 'player:updated', payload: { player: worldPlayer } });
          continue;
        }
      } else {
        profile.hungerZeroSince = null;
      }

      // 3) Fun drain (4 minutes = 240s, +25% faster if hungry <= 50%) + per-second activity gain
      let funDelta = -(100 / SURVIVAL_CONFIG.FUN_DURATION_SECONDS) * mult;
      let activityEnergyDelta = 0;

      const baseRoom = worldPlayer.roomKey.startsWith('espaco') ? 'espaco' : worldPlayer.roomKey;
      if (baseRoom === 'balada') {
        funDelta += 0.72; // Being in Balada Neon gives fun per second
      }
      if (worldPlayer.action === 'dancando') {
        funDelta += baseRoom === 'balada' ? 0.68 : 0.92;
        activityEnergyDelta -= 0.45 * mult;
      } else if (worldPlayer.action === 'sentado') {
        funDelta += 0.85; // Sitting on a bench / sofa gives fun per second
      }
      if (profile.activeActivity === 'regando') {
        funDelta += 1.05; // Watering plants gives fun per second while active
        activityEnergyDelta -= 0.35 * mult;
      } else if (profile.activeActivity === 'arcade') {
        funDelta += 1.15; // Playing arcade gives fun per second while active
        activityEnergyDelta -= 0.45 * mult;
      }

      addNeedDelta(profile, 'diversao', funDelta);

      // 4) Hygiene gentle drain (10 minutes = 600s)
      addNeedDelta(profile, 'higiene', -(100 / SURVIVAL_CONFIG.HYGIENE_DURATION_SECONDS));

      // 5) Energy: Bed recovery (5 minutes = 300s to full) OR active drain / 0-energy blackout
      if (profile.isRestingOnBed && worldPlayer.action === 'deitado') {
        profile.energyZeroSince = null;
        addNeedDelta(profile, 'energia', 100 / SURVIVAL_CONFIG.ENERGY_RECOVERY_SECONDS);
        if (rt.exact.energia >= 100 && !rt.restFullNotified) {
          rt.restFullNotified = true;
          sendJson(ws, {
            type: 'toast',
            payload: { message: '⚡ Energia 100% recuperada! Você pode levantar da cama quando quiser.', kind: 'success' },
          });
        }
      } else {
        if (activityEnergyDelta !== 0) {
          addNeedDelta(profile, 'energia', activityEnergyDelta);
        }

        if (rt.exact.energia <= 0) {
          if (!profile.energyZeroSince) {
            profile.energyZeroSince = now;
            sendJson(ws, {
              type: 'toast',
              payload: { message: '🚨 ENERGIA ZERADA! Vá para uma cama em 10 segundos ou você vai apagar!', kind: 'error' },
            });
          } else if (now - profile.energyZeroSince >= SURVIVAL_CONFIG.ZERO_GRACE_SECONDS * 1000) {
            // BLACKOUT! Teleport to last bed placed in player's lots (preferring active lot or a lot with a bed)
            const activeLot = resolveTargetOwnedLot(profile, worldPlayer);
            const lotWithBed =
              (activeLot.furniture.some((f) => getCatalogItem(f.itemId)?.shape === 'bed') ? activeLot : null) ||
              (profile.lots || []).find((l) => l.furniture.some((f) => getCatalogItem(f.itemId)?.shape === 'bed')) ||
              activeLot;
            const targetRoomKey = formatEspacoRoomKey(profile.id, lotWithBed.lotIndex);
            const oldRoomKey = worldPlayer.roomKey;
            const placedBed = lotWithBed.furniture.find((f) => getCatalogItem(f.itemId)?.shape === 'bed');
            const fallbackTile = pickWalkableEspacoTile(lotWithBed.plotTiles, lotWithBed.furniture);
            const bedPos =
              lotWithBed.lastBedPos &&
              lotWithBed.lastBedPos.x >= 0 &&
              lotWithBed.lastBedPos.x < PLOT_GRID_SIZE &&
              lotWithBed.lastBedPos.y >= 0 &&
              lotWithBed.lastBedPos.y < PLOT_GRID_SIZE
                ? lotWithBed.lastBedPos
                : placedBed
                ? { x: placedBed.x, y: placedBed.y }
                : fallbackTile;

            profile.energyZeroSince = null;
            profile.isRestingOnBed = true;
            profile.activeActivity = null;
            profile.activeLotIndex = lotWithBed.lotIndex;

            worldPlayer.roomKey = targetRoomKey;
            worldPlayer.x = bedPos.x;
            worldPlayer.y = bedPos.y;
            worldPlayer.action = 'deitado';
            worldPlayer.isRestingOnBed = true;
            worldPlayer.activeActivity = null;
            worldPlayer.bubbleText = undefined;

            if (!roomChats[targetRoomKey]) roomChats[targetRoomKey] = [];

            if (oldRoomKey !== targetRoomKey) {
              broadcastToRoom(oldRoomKey, {
                type: 'room:players',
                payload: { roomKey: oldRoomKey, players: getRoomPlayers(oldRoomKey) },
              });
              sendJson(ws, {
                type: 'room:entered',
                payload: {
                  roomKey: targetRoomKey,
                  players: getRoomPlayers(targetRoomKey),
                  seats: getRoomSeatsPayload(targetRoomKey),
                  chatHistory: roomChats[targetRoomKey].slice(-40),
                  spaceInfo: getSpacePayload(profile.id, lotWithBed.lotIndex),
                },
              });
              broadcastToRoom(targetRoomKey, {
                type: 'room:players',
                payload: { roomKey: targetRoomKey, players: getRoomPlayers(targetRoomKey) },
              });
              broadcastAll({
                type: 'city:counts',
                payload: {
                  roomCounts: getRoomCounts(),
                  onlinePlayers: Array.from(activePlayers.values()).map((p) => ({ id: p.id, name: p.name, roomKey: p.roomKey })),
                },
              });
            } else {
              broadcastToRoom(targetRoomKey, {
                type: 'player:updated',
                payload: { player: worldPlayer },
              });
            }

            sendJson(ws, { type: 'profile:update', payload: { profile } });
            sendJson(ws, {
              type: 'player:blackout',
              payload: { message: 'VOCÊ APAGOU!' },
            });
            scheduleSave();
            continue;
          }
        } else {
          profile.energyZeroSince = null;
        }
      }

      // 6) Per-Player Resource Node Regeneration Tick (private per player!)
      if (profile.resourceNodes && tickResourceNodes(profile.resourceNodes, now, state.economyConfig)) {
        scheduleSave();
        sendJson(ws, { type: 'nodes:updated', payload: { resourceNodes: Object.values(profile.resourceNodes) } });
      }

      sendJson(ws, { type: 'profile:update', payload: { profile } });
    }
  }, 1000);

  // Expose catalog & economy configuration endpoints
  app.get('/api/catalog', (_req, res) => {
    res.json({ items: CATALOG_ITEMS });
  });

  app.get('/api/economy/config', (_req, res) => {
    res.json({
      economyConfig: state.economyConfig,
      marketHistoryCount: state.marketHistory.length,
    });
  });

  if (process.env.NODE_ENV !== 'production') {
    app.use('/assets', express.static(path.join(__dirname, 'public', 'assets')));
    const { createServer: createViteServer } = await import('vite');
    const vite = await createViteServer({
      server: { middlewareMode: true, allowedHosts: true },
      appType: 'spa',
    });
    app.use(vite.middlewares);
  } else {
    const distPath = path.join(__dirname, 'dist');
    app.use(express.static(distPath));
    app.get('*', (_req, res) => {
      res.sendFile(path.join(distPath, 'index.html'));
    });
  }

  const PORT = 3000;
  server.listen(PORT, '0.0.0.0', () => {
    console.log(`OASIS Server running on http://0.0.0.0:${PORT}`);
  });
}

startServer().catch((err) => {
  console.error('Failed to start OASIS server:', err);
  process.exit(1);
});

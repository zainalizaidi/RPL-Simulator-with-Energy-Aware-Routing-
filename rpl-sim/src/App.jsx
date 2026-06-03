import { useState, useEffect, useRef, useCallback, useReducer } from "react";

// ─── CONSTANTS ───────────────────────────────────────────────────────────────
const E_ELEC = 50e-9;
const E_AMP  = 100e-12;

const COLORS = {
  bg:      "#080c12",
  bg2:     "#0e1420",
  bg3:     "#141c2e",
  bg4:     "#1a2236",
  border:  "#1e2d45",
  borderHi:"#2a3f60",
  cyan:    "#38bdf8",
  green:   "#34d399",
  amber:   "#fbbf24",
  red:     "#f87171",
  purple:  "#a78bfa",
  pink:    "#f472b6",
  muted:   "#64748b",
  mutedHi: "#94a3b8",
  white:   "#e2e8f0",
  node: {
    root:   "#a78bfa",
    router: "#38bdf8",
    leaf:   "#34d399",
    dead:   "#4a3040",
  },
  rpl: {
    DIS: "#fb923c",
    DIO: "#38bdf8",
    DAO: "#34d399",
  },
  pkt: ["#38bdf8","#34d399","#fbbf24","#f87171","#a78bfa"],
};

// ─── MATH HELPERS ────────────────────────────────────────────────────────────
function dist(a, b) { return Math.hypot(a.x - b.x, a.y - b.y); }
function ease(t)    { return t * t * (3 - 2 * t); }
function txEnergy(bytes, d) {
  const k = Math.max(1, bytes * 8);
  return k * E_ELEC + k * E_AMP * d * d;
}

// ─── BUILD EDGES ─────────────────────────────────────────────────────────────
function buildEdges(nodes, maxConn) {
  const edges = []; const seen = new Set();
  nodes.forEach((a, i) => {
    const dists = nodes
      .map((b, j) => ({ d: dist(a, b), j }))
      .filter(x => x.j !== i)
      .sort((x, y) => x.d - y.d)
      .slice(0, maxConn);
    dists.forEach(({ d, j }) => {
      const key = `${Math.min(i,j)}-${Math.max(i,j)}`;
      if (!seen.has(key)) {
        seen.add(key);
        edges.push({
          a: i, b: j, dist: d,
          energyCost: parseFloat((1.0 + d * 0.06 + nodes.length * 0.05).toFixed(2)),
          active: false, pulseAlpha: 0,
        });
      }
    });
  });
  return edges;
}

// ─── ASSIGN RANKS ────────────────────────────────────────────────────────────
function assignRanks(nodes, edges) {
  nodes.forEach(n => n.rank = 9999);
  const root = nodes.find(n => n.role === "root");
  if (!root) return;
  root.rank = 0;
  let changed = true;
  while (changed) {
    changed = false;
    edges.forEach(e => {
      const a = nodes[e.a], b = nodes[e.b];
      if (a.rank + 1 < b.rank) { b.rank = a.rank + 1; changed = true; }
      if (b.rank + 1 < a.rank) { a.rank = b.rank + 1; changed = true; }
    });
  }
}

// ─── DIJKSTRA ────────────────────────────────────────────────────────────────
function findPath(srcId, dstId, nodes, edges, mode) {
  const adj = {};
  nodes.forEach(n => adj[n.id] = []);
  edges.forEach(e => {
    adj[e.a].push({ to: e.b, edge: e });
    adj[e.b].push({ to: e.a, edge: e });
  });
  const D = {}; const prev = {};
  nodes.forEach(n => D[n.id] = Infinity);
  D[srcId] = 0;
  const pq = [{ cost: 0, id: srcId }];
  const visited = new Set();
  while (pq.length) {
    pq.sort((a, b) => a.cost - b.cost);
    const { cost, id } = pq.shift();
    if (visited.has(id)) continue;
    visited.add(id);
    for (const { to, edge } of adj[id]) {
      const v = nodes[to];
      if (!v.alive) continue;
      const ratio = v.initEnergy > 0 ? v.energy / v.initEnergy : 0;
      const w = mode === "energy"
        ? edge.energyCost * (1 + (1 - ratio) * 2)
        : edge.energyCost;
      const nc = D[id] + w;
      if (nc < D[to]) { D[to] = nc; prev[to] = id; pq.push({ cost: nc, id: to }); }
    }
  }
  if (!isFinite(D[dstId])) return null;
  const path = []; let cur = dstId;
  while (cur !== undefined) { path.unshift(cur); cur = prev[cur]; }
  return path[0] === srcId ? path : null;
}

// ─── DODAG BFS ────────────────────────────────────────────────────────────────
function buildDodagTree(nodes, edges) {
  const root = nodes.find(n => n.role === "root");
  if (!root) return [];
  const adj = {};
  nodes.forEach(n => adj[n.id] = []);
  edges.forEach(e => { adj[e.a].push(e.b); adj[e.b].push(e.a); });
  const visited = new Set([root.id]);
  const queue = [{ id: root.id, rank: 0 }];
  const tree = [];
  while (queue.length) {
    const { id, rank } = queue.shift();
    for (const nbrId of adj[id]) {
      if (!visited.has(nbrId)) {
        visited.add(nbrId);
        nodes[nbrId].rank = rank + 1;
        tree.push([id, nbrId]);
        queue.push({ id: nbrId, rank: rank + 1 });
      }
    }
  }
  return tree;
}

// ─── DEFAULT SETUP ───────────────────────────────────────────────────────────
function makeDefaultNodes(count = 7) {
  const roles = ["root","router","router","leaf","leaf","router","leaf","leaf","router","leaf","router","leaf"];
  const labels = ["Root","N1","N2","N3","N4","N5","N6","N7","N8","N9","N10","N11"];
  return Array.from({ length: count }, (_, i) => ({
    id: i,
    label: labels[i] || `N${i}`,
    role: roles[i] || (i === 0 ? "root" : Math.random() > 0.4 ? "router" : "leaf"),
    initEnergy: i === 0 ? 9999 : Math.round(200 + Math.random() * 300),
    energy: 0,
    x: Math.round(10 + Math.random() * 80),
    y: Math.round(10 + Math.random() * 80),
    alive: true,
    rank: 9999,
    pktsTx: 0, pktsRx: 0,
  })).map(n => ({ ...n, energy: n.initEnergy }));
}

function nodeColor(n) {
  if (!n.alive) return COLORS.node.dead;
  const r = n.initEnergy > 0 ? n.energy / n.initEnergy : 0;
  if (r > 0.6) return COLORS.node[n.role] || COLORS.green;
  if (r > 0.25) return COLORS.amber;
  return COLORS.red;
}

const PLACEHOLDERS = {
  nodeCount: "e.g. 7", minEnergy: "e.g. 200", maxEnergy: "e.g. 500",
  maxConn: "e.g. 3", area: "e.g. 100", pktSize: "e.g. 128",
  pktCount: "e.g. 40", txRate: "e.g. 2",
};
function F({ label, field, cfg, update }) {
  const [focused, setFocused] = useState(false);
  const hasVal = !!cfg[field];
  return (
    <div style={{ marginBottom: 14 }}>
      <label style={{ display:"block", fontSize: 10, color: focused ? COLORS.cyan : COLORS.muted, marginBottom: 5, letterSpacing: "0.08em", textTransform:"uppercase", fontFamily:"'JetBrains Mono',monospace", transition:"color 0.2s" }}>{label}</label>
      <input type="text" inputMode="numeric" value={cfg[field]}
        placeholder={PLACEHOLDERS[field] || ""}
        onChange={e => update(field, e.target.value)}
        onFocus={() => setFocused(true)}
        onBlur={() => setFocused(false)}
        style={{ width: "100%", background: focused ? COLORS.bg4 : COLORS.bg3,
          border: `1px solid ${focused ? COLORS.cyan : hasVal ? COLORS.borderHi : COLORS.border}`,
          color: COLORS.white, padding: "9px 12px", borderRadius: 8, fontFamily: "'JetBrains Mono',monospace", fontSize: 13,
          boxSizing: "border-box", outline: "none", transition:"all 0.2s",
          boxShadow: focused ? `0 0 0 3px ${COLORS.cyan}18` : "none" }} />
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════════════
//  SETUP SCREEN
// ═══════════════════════════════════════════════════════════════════════════════
function SetupScreen({ onLaunch }) {
  const [cfg, setCfg] = useState({
    nodeCount: "", mode: "energy",
    minEnergy: "", maxEnergy: "",
    maxConn: "", area: "",
    pktSize: "", pktCount: "", txRate: "",
  });
  const [nodes, setNodes] = useState([]);

  const update = (k, v) => setCfg(p => ({ ...p, [k]: v }));

  const rebuildTable = () => {
    const c = Math.max(3, Math.min(12, parseInt(cfg.nodeCount) || 0));
    if (!c) { alert("Please enter Number of Nodes (3–12) first."); return; }
    const minE = parseFloat(cfg.minEnergy) || 100;
    const maxE = parseFloat(cfg.maxEnergy) || minE;
    const areaVal = parseFloat(cfg.area) || 100;
    const newNodes = makeDefaultNodes(c).map(n => ({
      ...n,
      initEnergy: n.role === "root" ? 9999 : Math.round(minE + Math.random() * Math.max(0, maxE - minE)),
      x: Math.round(5 + Math.random() * (areaVal - 10)),
      y: Math.round(5 + Math.random() * (areaVal - 10)),
    }));
    newNodes.forEach(n => n.energy = n.initEnergy);
    setNodes(newNodes);
  };

  const randomize = () => {
    if (!nodes.length) { alert("Please build the table first using REBUILD TABLE."); return; }
    const minE = parseFloat(cfg.minEnergy) || 100;
    const maxE = parseFloat(cfg.maxEnergy) || minE;
    const areaVal = parseFloat(cfg.area) || 100;
    setNodes(prev => prev.map(n => {
      const e = n.role === "root" ? 9999 : Math.round(minE + Math.random() * Math.max(0, maxE - minE));
      return { ...n, initEnergy: e, energy: e,
        x: Math.round(5 + Math.random() * (areaVal - 10)),
        y: Math.round(5 + Math.random() * (areaVal - 10)) };
    }));
  };

  const updateNode = (i, field, val) => setNodes(prev => {
    const next = [...prev];
    next[i] = { ...next[i], [field]: val };
    if (field === "initEnergy") next[i].energy = val;
    return next;
  });

  const launch = () => {
    // Validate all fields
    const errors = [];
    const nc = parseInt(cfg.nodeCount);
    if (!cfg.nodeCount || isNaN(nc) || nc < 3 || nc > 12) errors.push("Number of Nodes must be 3–12");
    if (!cfg.minEnergy || isNaN(parseFloat(cfg.minEnergy)) || parseFloat(cfg.minEnergy) < 100) errors.push("Min Node Energy must be ≥ 100 J");
    if (!cfg.maxEnergy || isNaN(parseFloat(cfg.maxEnergy))) errors.push("Max Node Energy is required");
    if (parseFloat(cfg.maxEnergy) < parseFloat(cfg.minEnergy)) errors.push("Max Energy must be ≥ Min Energy");
    if (!cfg.maxConn || isNaN(parseInt(cfg.maxConn)) || parseInt(cfg.maxConn) < 2 || parseInt(cfg.maxConn) > 5) errors.push("Max Links per Node must be 2–5");
    if (!cfg.area || isNaN(parseFloat(cfg.area)) || parseFloat(cfg.area) <= 0) errors.push("Simulation Area must be > 0");
    if (!cfg.pktSize || isNaN(parseInt(cfg.pktSize)) || parseInt(cfg.pktSize) < 1) errors.push("Packet Size must be ≥ 1 byte");
    if (!cfg.pktCount || isNaN(parseInt(cfg.pktCount)) || parseInt(cfg.pktCount) < 1) errors.push("Number of Packets must be ≥ 1");
    if (!cfg.txRate || isNaN(parseFloat(cfg.txRate)) || parseFloat(cfg.txRate) <= 0) errors.push("TX Rate must be > 0");
    if (!nodes.length) errors.push("No nodes configured — use REBUILD TABLE first");
    if (errors.length) { alert("Please fix the following:" + errors.map(e => "• " + e).join("")); return; }
    const validNodes = nodes.map(n => ({
      ...n,
      initEnergy: parseFloat(n.initEnergy) || 0,
      energy: parseFloat(n.initEnergy) || 0,
      x: parseFloat(n.x) || 0,
      y: parseFloat(n.y) || 0,
    }));
    if (!validNodes.some(n => n.role === "root")) validNodes[0].role = "root";
    onLaunch({ ...cfg, nodes: validNodes });
  };

  const PLACEHOLDERS = {
    nodeCount: "e.g. 7", minEnergy: "e.g. 200", maxEnergy: "e.g. 500",
    maxConn: "e.g. 3", area: "e.g. 100", pktSize: "e.g. 128",
    pktCount: "e.g. 40", txRate: "e.g. 2",
  };

  return (
    <div style={{ minHeight: "100vh", background: COLORS.bg, color: COLORS.white, fontFamily: "'JetBrains Mono',monospace", padding: "32px 24px" }}>
      <style>{`
        @import url('https://fonts.googleapis.com/css2?family=JetBrains+Mono:wght@300;400;500;600;700&family=Space+Grotesk:wght@400;500;600;700&display=swap');
        * { box-sizing: border-box; }
        ::placeholder { color: #334155 !important; }
        select option { background: #0e1420; }
        ::-webkit-scrollbar { width: 4px; }
        ::-webkit-scrollbar-track { background: transparent; }
        ::-webkit-scrollbar-thumb { background: #1e2d45; border-radius: 2px; }
      `}</style>

      {/* Header */}
      <div style={{ textAlign: "center", marginBottom: 40 }}>
        <div style={{ fontSize: 28, fontWeight: 700, color: COLORS.white, letterSpacing: "-0.02em", fontFamily:"'Space Grotesk',sans-serif", marginBottom:6 }}>
          RPL Energy-Aware <span style={{ color: COLORS.cyan }}>Routing</span> Simulator
        </div>
        <div style={{ color: COLORS.muted, fontSize: 12, letterSpacing:"0.06em", textTransform:"uppercase" }}>DODAG Formation · Energy-Aware Routing Protocol</div>
      </div>

      <div style={{ display: "grid", gridTemplateColumns: "1fr 1fr", gap: 16, maxWidth: 920, margin: "0 auto" }}>
        {/* Left */}
        <div style={{ background: `linear-gradient(135deg, ${COLORS.bg2} 0%, ${COLORS.bg3} 100%)`, border: `1px solid ${COLORS.border}`, borderRadius: 14, padding: 24 }}>
          <div style={{ display:"flex", alignItems:"center", gap:8, marginBottom: 20 }}>
            <div style={{ width:3, height:16, borderRadius:2, background: COLORS.cyan }} />
            <div style={{ color: COLORS.cyan, fontWeight: 600, fontSize: 11, letterSpacing:"0.12em", textTransform:"uppercase" }}>Network Configuration</div>
          </div>
          <F label="Number of Nodes (3–12)" field="nodeCount" cfg={cfg} update={update} />
          <div style={{ marginBottom: 14 }}>
            <label style={{ display:"block", fontSize: 10, color: COLORS.muted, marginBottom: 5, letterSpacing: "0.08em", textTransform:"uppercase" }}>Routing Mode</label>
            <select value={cfg.mode} onChange={e => update("mode", e.target.value)}
              style={{ width: "100%", background: COLORS.bg3, border: `1px solid ${COLORS.border}`, color: COLORS.white, padding: "9px 12px", borderRadius: 8, fontFamily: "'JetBrains Mono',monospace", fontSize: 13, outline:"none", cursor:"pointer" }}>
              <option value="energy">Energy-Aware Greedy</option>
              <option value="minimum">Minimum Energy Routing</option>
            </select>
          </div>
          <F label="Min Node Energy J (≥100)" field="minEnergy" cfg={cfg} update={update} />
          <F label="Max Node Energy J" field="maxEnergy" cfg={cfg} update={update} />
          <F label="Max Links per Node (2–5)" field="maxConn" cfg={cfg} update={update} />
          <F label="Simulation Area %" field="area" cfg={cfg} update={update} />
        </div>

        {/* Right */}
        <div style={{ background: `linear-gradient(135deg, ${COLORS.bg2} 0%, ${COLORS.bg3} 100%)`, border: `1px solid ${COLORS.border}`, borderRadius: 14, padding: 24 }}>
          <div style={{ display:"flex", alignItems:"center", gap:8, marginBottom: 20 }}>
            <div style={{ width:3, height:16, borderRadius:2, background: COLORS.purple }} />
            <div style={{ color: COLORS.purple, fontWeight: 600, fontSize: 11, letterSpacing:"0.12em", textTransform:"uppercase" }}>Packet Configuration</div>
          </div>
          <F label="Packet Size (bytes)" field="pktSize" cfg={cfg} update={update} />
          <F label="Number of Packets to Send" field="pktCount" cfg={cfg} update={update} />
          <F label="TX Rate (packets/second)" field="txRate" cfg={cfg} update={update} />
          <div style={{ marginTop: 20, padding: 16, background: COLORS.bg, border:`1px solid ${COLORS.border}`, borderRadius: 10, fontSize: 11, color: COLORS.muted, lineHeight:1.8 }}>
            <div style={{ color: COLORS.purple, fontWeight: 700, marginBottom: 8, fontSize:10, letterSpacing:"0.1em", textTransform:"uppercase" }}>Energy Model — First-Order Radio</div>
            <div style={{ color: COLORS.mutedHi }}>E<sub>tx</sub> = k · E<sub>elec</sub> + k · E<sub>amp</sub> · d²</div>
            <div>E<sub>elec</sub> = 50 nJ/bit &nbsp;·&nbsp; E<sub>amp</sub> = 100 pJ/bit/m²</div>
            <div style={{ marginTop: 6, color: COLORS.amber, fontSize:10 }}>k = pkt_size × 8 bits &nbsp;·&nbsp; d = distance</div>
          </div>
        </div>
      </div>

      {/* Node Table */}
      <div style={{ maxWidth: 920, margin: "16px auto 0", background: `linear-gradient(135deg, ${COLORS.bg2} 0%, ${COLORS.bg3} 100%)`, border: `1px solid ${COLORS.border}`, borderRadius: 14, padding: 24 }}>
        <div style={{ display:"flex", alignItems:"center", gap:8, marginBottom: 16 }}>
          <div style={{ width:3, height:16, borderRadius:2, background: COLORS.green }} />
          <div style={{ color: COLORS.green, fontWeight: 600, fontSize: 11, letterSpacing:"0.12em", textTransform:"uppercase" }}>Node Details</div>
          <div style={{ marginLeft:"auto", color: COLORS.muted, fontSize:10 }}>edit freely</div>
        </div>
        <div style={{ overflowX: "auto" }}>
          <table style={{ width: "100%", borderCollapse: "collapse", fontSize: 12 }}>
            <thead>
              <tr>
                {["ID","Label","Role","Energy J","X %","Y %"].map(h => (
                  <th key={h} style={{ padding: "8px 10px", textAlign: "left", borderBottom: `1px solid ${COLORS.border}`, color: COLORS.muted, fontSize:10, letterSpacing:"0.08em", textTransform:"uppercase", fontWeight:500 }}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {nodes.map((n, i) => (
                <tr key={i} style={{ borderBottom: `1px solid ${COLORS.border}18` }}>
                  <td style={{ padding: "7px 10px", color: COLORS.muted, fontSize:11 }}>{n.id}</td>
                  <td style={{ padding: "7px 10px" }}>
                    <input value={n.label} onChange={e => updateNode(i,"label",e.target.value)}
                      style={{ background: "transparent", border: "none", color: nodeColor(n), width: 60, fontFamily: "'JetBrains Mono',monospace", fontSize: 12, outline:"none" }} />
                  </td>
                  <td style={{ padding: "7px 10px" }}>
                    <select value={n.role} onChange={e => updateNode(i,"role",e.target.value)}
                      style={{ background: COLORS.bg4, border: `1px solid ${COLORS.border}`, color: COLORS.node[n.role], borderRadius: 6, fontSize: 11, fontFamily: "'JetBrains Mono',monospace", padding: "3px 6px", outline:"none", cursor:"pointer" }}>
                      <option value="root">root</option>
                      <option value="router">router</option>
                      <option value="leaf">leaf</option>
                    </select>
                  </td>
                  <td style={{ padding: "7px 10px" }}>
                    <input type="text" inputMode="numeric" value={n.initEnergy} onChange={e => updateNode(i,"initEnergy",e.target.value)}
                      style={{ background: "transparent", border: "none", color: COLORS.amber, width: 70, fontFamily: "'JetBrains Mono',monospace", fontSize: 12, outline:"none" }} />
                  </td>
                  <td style={{ padding: "7px 10px" }}>
                    <input type="text" inputMode="numeric" value={n.x} onChange={e => updateNode(i,"x",e.target.value)}
                      style={{ background: "transparent", border: "none", color: COLORS.white, width: 50, fontFamily: "'JetBrains Mono',monospace", fontSize: 12, outline:"none" }} />
                  </td>
                  <td style={{ padding: "7px 10px" }}>
                    <input type="text" inputMode="numeric" value={n.y} onChange={e => updateNode(i,"y",e.target.value)}
                      style={{ background: "transparent", border: "none", color: COLORS.white, width: 50, fontFamily: "'JetBrains Mono',monospace", fontSize: 12, outline:"none" }} />
                  </td>
                </tr>
              ))}
            </tbody>
          </table>
        </div>
      </div>

      {/* Buttons */}
      <div style={{ maxWidth: 920, margin: "20px auto 0", display: "flex", gap: 10 }}>
        <button onClick={randomize} style={btnStyle(COLORS.border, COLORS.mutedHi)}>↺ Randomize</button>
        <button onClick={rebuildTable} style={btnStyle(COLORS.border, COLORS.amber)}>⟳ Rebuild Table</button>
        <button onClick={launch} style={btnStyle(COLORS.cyan, COLORS.bg, true)}>▶ Launch Simulation</button>
      </div>
    </div>
  );
}

function btnStyle(border, color, bold = false) {
  return {
    background: bold ? border : "transparent",
    border: `1px solid ${border}`,
    color, padding: "10px 22px", borderRadius: 8,
    fontFamily: "'JetBrains Mono',monospace", fontSize: 12, cursor: "pointer",
    fontWeight: bold ? 700 : 400, letterSpacing: "0.05em", transition:"all 0.15s",
  };
}

// ═══════════════════════════════════════════════════════════════════════════════
//  SIMULATION ENGINE HOOK
// ═══════════════════════════════════════════════════════════════════════════════
function useSimEngine(cfg, active) {
  const stateRef = useRef({
    nodes: [], edges: [],
    packets: [], rplMsgs: [],
    dodagPhase: "idle", dodagTreeEdges: [],
    dodagFormed: false,
    stats: { sent:0, delivered:0, dropped:0, totalHops:0, totalEnergy:0, startTime:0 },
    eventLog: [], txLog: [],
    pktCounter: 0, totalPkts: 0,
    pktSize: 128, txRate: 2, mode: "energy",
    running: false, paused: false,
    spawnedCount: 0,
  });
  const [tick, setTick] = useState(0);
  const rafRef = useRef(null);
  const lastSpawnRef = useRef(0);

  const S = stateRef.current;

  const addLog = useCallback((text, tag) => {
    S.eventLog.push({ text: `[${new Date().toLocaleTimeString()}] ${text}`, tag });
    if (S.eventLog.length > 200) S.eventLog.shift();
  }, []);

  const addTx = useCallback((src, dst, msgType, content, color, phase = "", payloadBytes = null) => {
    S.txLog.push({ ts: new Date().toLocaleTimeString(), src, dst, msgType, content, color, phase, payloadBytes });
    if (S.txLog.length > 500) S.txLog.shift();
  }, []);

  // ── DODAG formation ─────────────────────────────────────────
  const startDodag = useCallback(() => {
    const nodes = S.nodes;
    const root = nodes.find(n => n.role === "root");
    if (!root) return;

    // Assign ranks via BFS
    S.dodagTreeEdges = buildDodagTree(nodes, S.edges);
    assignRanks(nodes, S.edges);

    S.dodagPhase = "DIS";
    addLog("━━ DODAG FORMATION STARTED ━━", "cyan");
    addLog("Phase 1 › DIS — nodes solicit DODAG info", "dis");

    const adj = {};
    nodes.forEach(n => adj[n.id] = []);
    S.edges.forEach(e => { adj[e.a].push(e.b); adj[e.b].push(e.a); });

    let delay = 0;
    const nonRoot = nodes.filter(n => n.role !== "root");

    // Phase 1: DIS
    nonRoot.forEach(node => {
      const nbrs = adj[node.id];
      if (!nbrs.length) return;
      const target = nbrs.reduce((best, nid) =>
        dist(node, nodes[nid]) < dist(node, nodes[best]) ? nid : best, nbrs[0]);
      const t = nodes[target];
      setTimeout(() => {
        if (!S.running) return;
        S.rplMsgs.push({ type:"DIS", src:node, dst:t, rank:null, progress:0, done:false,
          x:node.x, y:node.y, color:COLORS.rpl.DIS, icon:"?", label:"DIS?" });
        addLog(`  ${node.label} ──DIS?──▶ ${t.label}  (soliciting DODAG)`, "dis");
        addTx(node.label, t.label, "DIS", `"${node.label}" asks: "Do you know a DODAG? Please send me DIO." → ${t.label}`, COLORS.rpl.DIS, "Phase 1");
      }, delay);
      delay += 180;
    });

    // Phase 2: DIO
    setTimeout(() => {
      if (!S.running) return;
      S.dodagPhase = "DIO";
      addLog("Phase 2 › DIO — root broadcasts DODAG ranks", "dio");
      let dioDelay = 0;
      S.dodagTreeEdges.forEach(([pid, cid]) => {
        const pn = nodes[pid], cn = nodes[cid];
        setTimeout(() => {
          if (!S.running) return;
          S.rplMsgs.push({ type:"DIO", src:pn, dst:cn, rank:cn.rank, progress:0, done:false,
            x:pn.x, y:pn.y, color:COLORS.rpl.DIO, icon:"i", label:`DIO[r=${cn.rank}]` });
          addLog(`  ${pn.label} ──DIO[r=${cn.rank}]──▶ ${cn.label}  (rank advertisement)`, "dio");
          addTx(pn.label, cn.label, "DIO", `"${pn.label}" tells "${cn.label}": "I am at rank ${pn.rank}. Join DODAG — your rank will be ${cn.rank}."`, COLORS.rpl.DIO, "Phase 2");
        }, dioDelay);
        dioDelay += 200;
      });

      // Phase 3: DAO
      const totalDio = dioDelay;
      setTimeout(() => {
        if (!S.running) return;
        S.dodagPhase = "DAO";
        addLog("Phase 3 › DAO — nodes register routes upward", "dao");
        const parentMap = {};
        S.dodagTreeEdges.forEach(([pid, cid]) => parentMap[cid] = pid);
        const sorted = [...nonRoot].sort((a, b) => b.rank - a.rank);
        let daoDelay = 0;
        sorted.forEach(node => {
          const pid = parentMap[node.id] ?? (adj[node.id][0]);
          if (pid === undefined) return;
          const pn = nodes[pid];
          setTimeout(() => {
            if (!S.running) return;
            S.rplMsgs.push({ type:"DAO", src:node, dst:pn, rank:node.rank, progress:0, done:false,
              x:node.x, y:node.y, color:COLORS.rpl.DAO, icon:"▲", label:`DAO[r=${node.rank}]` });
            addLog(`  ${node.label} ──DAO[r=${node.rank}]──▶ ${pn.label}  (route registration)`, "dao");
            addTx(node.label, pn.label, "DAO", `"${node.label}" tells "${pn.label}": "I am at rank ${node.rank}. Register my route — I can reach DODAG via you."`, COLORS.rpl.DAO, "Phase 3");
          }, daoDelay);
          daoDelay += 220;
        });

        setTimeout(() => {
          if (!S.running) return;
          S.dodagFormed = true;
          S.dodagPhase = "done";
          addLog("━━ DODAG FORMATION COMPLETE — packets starting ━━", "green");
          startPackets();
        }, daoDelay + 400);
      }, totalDio + 300);
    }, delay + 300);
  }, [addLog, addTx]);

  const startPackets = useCallback(() => {
    S.spawnedCount = 0;
    S.stats.startTime = performance.now() / 1000;
    lastSpawnRef.current = performance.now();
  }, []);

  // ── Main animation loop ──────────────────────────────────────
  const loop = useCallback((now) => {
    if (!S.running) return;
    const SPD = 1.5;

    // Move RPL messages
    S.rplMsgs = S.rplMsgs.filter(m => !m.done);
    S.rplMsgs.forEach(m => {
      m.progress = Math.min(1, m.progress + 0.04 * SPD);
      const t = ease(m.progress);
      m.x = m.src.x + (m.dst.x - m.src.x) * t;
      m.y = m.src.y + (m.dst.y - m.src.y) * t;
      if (m.progress >= 1) m.done = true;
    });

    // Spawn packets
    if (S.dodagFormed && S.spawnedCount < S.totalPkts) {
      const interval = 1000 / S.txRate;
      if (now - lastSpawnRef.current >= interval) {
        lastSpawnRef.current = now;
        const root = S.nodes.find(n => n.role === "root");
        const sources = S.nodes.filter(n => n.alive && n.role !== "root");
        if (!sources.length) { S.stats.dropped++; S.spawnedCount++; }
        else {
          const src = sources[Math.floor(Math.random() * sources.length)];
          const pathIds = findPath(src.id, root.id, S.nodes, S.edges, S.mode);
          S.stats.sent++;
          S.spawnedCount++;
          if (!pathIds || pathIds.length < 2) {
            S.stats.dropped++;
            addLog(`✗ DROP  ${src.label}→Root  (no route)`, "amber");
          } else {
            S.pktCounter++;
            const path = pathIds.map(id => S.nodes[id]);
            S.packets.push({
              id: S.pktCounter, path, size: S.pktSize,
              hopIdx: 0, progress: 0, delivered: false, dropped: false,
              hopsDone: 0, x: path[0].x, y: path[0].y,
              color: COLORS.pkt[S.pktCounter % COLORS.pkt.length],
              trail: [],
            });
            addLog(`→ PKT#${S.pktCounter}  ${src.label}→Root  ${path.length-1} hops`, "cyan");
          }
        }
      }
    }

    // Move packets
    S.packets = S.packets.filter(p => !p.delivered && !p.dropped).concat(
      S.packets.filter(p => p.delivered || p.dropped)
    ).slice(-200);
    S.packets.forEach(p => {
      if (p.delivered || p.dropped) return;
      p.progress += 0.05 * SPD;
      const segA = p.path[p.hopIdx], segB = p.path[p.hopIdx + 1];
      const t = Math.min(p.progress, 1);
      p.x = segA.x + (segB.x - segA.x) * ease(t);
      p.y = segA.y + (segB.y - segA.y) * ease(t);
      p.trail.push({ x: p.x, y: p.y });
      if (p.trail.length > 12) p.trail.shift();

      // activate edge
      const edge = S.edges.find(e =>
        (e.a === segA.id && e.b === segB.id) || (e.a === segB.id && e.b === segA.id));
      if (edge) { edge.active = true; edge.pulseAlpha = 1; }

      if (p.progress >= 1) {
        p.progress = 0;
        p.hopIdx++;
        p.hopsDone++;
        const hopDist = dist(segA, segB);
        // Convert 0-100 coordinate units to metres (×10), apply First-Order Radio Model,
        // then scale so nodes visibly drain: target ~50% depletion over totalPkts×avgHops transmissions.
        const distMeters  = hopDist * 10;
        const rawJ        = txEnergy(p.size, distMeters);
        const avgNodeE    = S.nodes.reduce((a, n) => a + n.initEnergy, 0) / S.nodes.length;
        const avgHopsEst  = Math.max(2, Math.round(S.nodes.length / 2));
        const budgetPerTx = (avgNodeE * 0.5) / (S.totalPkts * avgHopsEst);
        const rawBaseline = txEnergy(128, 300); // baseline at d=300m,128B ~ 9.6e-5 J
        const energy      = rawJ * (budgetPerTx / rawBaseline);
        segA.energy = Math.max(0, segA.energy - energy);
        S.stats.totalEnergy += energy;
        if (segA.energy === 0 && segA.alive) {
          segA.alive = false;
          addLog(`💀 ${segA.label} DEAD — energy depleted`, "red");
        }
        const hop = p.hopsDone, total = p.path.length - 1;
        addTx(segA.label, segB.label, "PKT",
          `PKT#${p.id} [${p.size}B]  hop ${hop}/${total}  Drained: ${energy.toFixed(3)}J  (${segA.label}: ${segA.energy.toFixed(1)}J left)`,
          "#d2a8ff", "Data", p.size);

        if (p.hopIdx >= p.path.length - 1) {
          p.delivered = true;
          p.x = p.path[p.path.length-1].x;
          p.y = p.path[p.path.length-1].y;
          S.stats.delivered++;
          S.stats.totalHops += p.hopsDone;
          addLog(`✓ PKT#${p.id} delivered  ${p.hopsDone} hops`, "green");
          const pathStr = p.path.map(n => n.label).join(" → ");
          addTx(p.path[p.path.length-2].label, p.path[p.path.length-1].label, "ACK",
            `PKT#${p.id} DELIVERED to Root ✓  Path: ${pathStr}  Total hops: ${p.hopsDone}`,
            COLORS.green, "Data", p.size);
        }
      }
    });

    // Fade edges
    S.edges.forEach(e => {
      if (e.active) { e.pulseAlpha -= 0.08; if (e.pulseAlpha <= 0) { e.active = false; e.pulseAlpha = 0; } }
    });

    // Check done
    if (S.dodagFormed && S.spawnedCount >= S.totalPkts && !S.packets.some(p => !p.delivered && !p.dropped)) {
      addLog("✓ All packets processed — simulation complete", "green");
      S.running = false;
    }

    setTick(t => t + 1);
    if (S.running || S.packets.some(p => !p.delivered && !p.dropped)) {
      rafRef.current = requestAnimationFrame(loop);
    }
  }, [addLog, addTx]);

  // ── Public API ────────────────────────────────────────────────
  const start = useCallback((config) => {
    const nodes = config.nodes.map(n => ({ ...n }));
    if (!nodes.some(n => n.role === "root")) nodes[0].role = "root";
    const maxConn = Math.max(2, Math.min(5, parseInt(config.maxConn)||3));
    const edges = buildEdges(nodes, maxConn);

    Object.assign(S, {
      nodes, edges,
      packets: [], rplMsgs: [],
      dodagPhase: "idle", dodagTreeEdges: [],
      dodagFormed: false,
      stats: { sent:0, delivered:0, dropped:0, totalHops:0, totalEnergy:0, startTime: performance.now()/1000 },
      eventLog: [], txLog: [],
      pktCounter: 0, spawnedCount: 0,
      totalPkts: Math.max(1, parseInt(config.pktCount)||40),
      pktSize: Math.max(16, parseInt(config.pktSize)||128),
      txRate: Math.max(0.1, parseFloat(config.txRate)||2),
      mode: config.mode || "energy",
      running: true, paused: false,
    });

    addLog(`Simulation started — ${nodes.length} nodes`, "cyan");

    setTimeout(() => startDodag(), 400);
    if (rafRef.current) cancelAnimationFrame(rafRef.current);
    rafRef.current = requestAnimationFrame(loop);
    setTick(t => t + 1);
  }, [loop, startDodag, addLog]);

  const pause = useCallback(() => {
    S.paused = !S.paused;
    addLog(`Simulation ${S.paused ? "PAUSED" : "RESUMED"}`, "amber");
    if (!S.paused) rafRef.current = requestAnimationFrame(loop);
    setTick(t => t + 1);
  }, [loop, addLog]);

  const stop = useCallback(() => {
    S.running = false;
    if (rafRef.current) cancelAnimationFrame(rafRef.current);
    addLog("Simulation stopped by user", "amber");
    setTick(t => t + 1);
  }, [addLog]);

  useEffect(() => () => { if (rafRef.current) cancelAnimationFrame(rafRef.current); }, []);

  return { state: S, tick, start, pause, stop };
}

// ═══════════════════════════════════════════════════════════════════════════════
//  NETWORK CANVAS
// ═══════════════════════════════════════════════════════════════════════════════
function NetworkCanvas({ state, tick }) {
  const canvasRef = useRef(null);
  const [tooltip, setTooltip] = useState(null);
  const [hoveredNode, setHoveredNode] = useState(null);

  useEffect(() => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const ctx = canvas.getContext("2d");
    const W = canvas.width, H = canvas.height;
    const PAD = 30;
    const sx = x => PAD + (x / 100) * (W - PAD * 2);
    const sy = y => PAD + (y / 100) * (H - PAD * 2);

    ctx.clearRect(0, 0, W, H);
    ctx.fillStyle = COLORS.bg;
    ctx.fillRect(0, 0, W, H);

    // Grid dots
    ctx.fillStyle = COLORS.border + "60";
    for (let gx = 0; gx <= 100; gx += 10)
      for (let gy = 0; gy <= 100; gy += 10) {
        ctx.beginPath(); ctx.arc(sx(gx), sy(gy), 1.5, 0, Math.PI*2); ctx.fill();
      }

    const nodes = state.nodes || [];
    const edges = state.edges || [];
    const packets = state.packets || [];
    const rplMsgs = state.rplMsgs || [];

    // Edges
    edges.forEach(e => {
      const a = nodes[e.a], b = nodes[e.b];
      if (!a || !b) return;
      ctx.beginPath();
      ctx.moveTo(sx(a.x), sy(a.y));
      ctx.lineTo(sx(b.x), sy(b.y));
      ctx.strokeStyle = e.active ? COLORS.cyan : COLORS.border;
      ctx.lineWidth = e.active ? 2 : 1;
      ctx.globalAlpha = e.active ? 0.9 : 0.5;
      ctx.stroke();
      ctx.globalAlpha = 1;

      // energy label
      const mx = (sx(a.x) + sx(b.x)) / 2, my = (sy(a.y) + sy(b.y)) / 2;
      ctx.font = "10px monospace";
      ctx.fillStyle = COLORS.muted;
      ctx.textAlign = "center";
      ctx.fillText(`${e.energyCost}J`, mx, my);
    });

    // DODAG tree arrows
    (state.dodagTreeEdges || []).forEach(([pid, cid]) => {
      const pn = nodes[pid], cn = nodes[cid];
      if (!pn || !cn) return;
      const x1 = sx(pn.x), y1 = sy(pn.y), x2 = sx(cn.x), y2 = sy(cn.y);
      const angle = Math.atan2(y2 - y1, x2 - x1);
      const r = 14;
      const ex = x2 - r * Math.cos(angle), ey = y2 - r * Math.sin(angle);
      ctx.beginPath();
      ctx.moveTo(x1 + r * Math.cos(angle), y1 + r * Math.sin(angle));
      ctx.lineTo(ex, ey);
      ctx.strokeStyle = COLORS.purple;
      ctx.lineWidth = 1.5;
      ctx.globalAlpha = 0.55;
      ctx.setLineDash([5, 3]);
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.globalAlpha = 1;
      // arrowhead
      ctx.beginPath();
      ctx.moveTo(ex, ey);
      ctx.lineTo(ex - 8*Math.cos(angle-0.3), ey - 8*Math.sin(angle-0.3));
      ctx.lineTo(ex - 8*Math.cos(angle+0.3), ey - 8*Math.sin(angle+0.3));
      ctx.closePath();
      ctx.fillStyle = COLORS.purple + "88";
      ctx.fill();
    });

    // Packet trails
    packets.forEach(p => {
      if (p.delivered || p.dropped) return;
      if (p.trail.length > 1) {
        ctx.beginPath();
        ctx.moveTo(sx(p.trail[0].x), sy(p.trail[0].y));
        p.trail.forEach(pt => ctx.lineTo(sx(pt.x), sy(pt.y)));
        ctx.strokeStyle = p.color;
        ctx.lineWidth = 1;
        ctx.globalAlpha = 0.3;
        ctx.stroke();
        ctx.globalAlpha = 1;
      }
      ctx.beginPath();
      ctx.arc(sx(p.x), sy(p.y), 6, 0, Math.PI * 2);
      ctx.fillStyle = p.color;
      ctx.fill();
      ctx.strokeStyle = "#fff";
      ctx.lineWidth = 1;
      ctx.stroke();
    });

    // Nodes
    nodes.forEach(n => {
      const nx = sx(n.x), ny = sy(n.y);
      const r = n.role === "root" ? 18 : n.role === "router" ? 14 : 11;
      const col = nodeColor(n);

      ctx.globalAlpha = n.alive ? 0.95 : 0.35;
      ctx.beginPath();
      ctx.arc(nx, ny, r, 0, Math.PI * 2);
      ctx.fillStyle = col;
      ctx.fill();
      if (n.id === hoveredNode) {
        ctx.strokeStyle = "#fff";
        ctx.lineWidth = 2;
        ctx.stroke();
      }
      ctx.globalAlpha = 1;

      // icon
      ctx.font = `bold ${r-2}px monospace`;
      ctx.fillStyle = COLORS.bg;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(n.role === "root" ? "R" : n.role === "router" ? "↔" : "◉", nx, ny);

      // label
      ctx.font = "bold 10px monospace";
      ctx.fillStyle = n.alive ? COLORS.white : COLORS.muted;
      ctx.fillText(n.label, nx, ny + r + 9);

      // energy
      ctx.font = "9px monospace";
      ctx.fillStyle = col;
      ctx.fillText(`${Math.round(n.energy)}J`, nx, ny + r + 18);
    });

    // RPL messages
    rplMsgs.forEach(m => {
      if (m.done) return;
      const mx = sx(m.x), my = sy(m.y);
      ctx.beginPath();
      ctx.arc(mx, my, 10, 0, Math.PI * 2);
      ctx.fillStyle = m.color;
      ctx.globalAlpha = 0.92;
      ctx.fill();
      ctx.globalAlpha = 1;

      ctx.font = "bold 9px monospace";
      ctx.fillStyle = COLORS.bg;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(m.icon, mx, my);

      ctx.font = "9px monospace";
      ctx.fillStyle = m.color;
      ctx.fillText(m.label, mx, my - 14);
    });

    // Phase badge
    if (state.dodagPhase && state.dodagPhase !== "done" && state.dodagPhase !== "idle") {
      const pc = COLORS.rpl[state.dodagPhase] || COLORS.white;
      ctx.fillStyle = COLORS.bg2 + "ee";
      ctx.fillRect(W/2 - 70, 8, 140, 26);
      ctx.strokeStyle = pc;
      ctx.lineWidth = 1;
      ctx.strokeRect(W/2 - 70, 8, 140, 26);
      ctx.font = "bold 12px monospace";
      ctx.fillStyle = pc;
      ctx.textAlign = "center";
      ctx.textBaseline = "middle";
      ctx.fillText(`◉ ${state.dodagPhase} phase`, W/2, 21);
    }

    // HUD
    const s = state.stats || {};
    const elapsed = s.startTime ? ((performance.now()/1000) - s.startTime).toFixed(1) : "0.0";
    ctx.font = "11px monospace";
    ctx.fillStyle = COLORS.muted;
    ctx.textAlign = "left";
    ctx.textBaseline = "top";
    ctx.fillText(`PKT ${s.sent||0}/${state.totalPkts||0}  ✓${s.delivered||0}  ✗${s.dropped||0}  T=${elapsed}s`, 8, 8);
  }, [tick, hoveredNode, state]);

  const handleMouseMove = useCallback((e) => {
    const canvas = canvasRef.current;
    if (!canvas) return;
    const rect = canvas.getBoundingClientRect();
    const mx = (e.clientX - rect.left) * (canvas.width / rect.width);
    const my = (e.clientY - rect.top) * (canvas.height / rect.height);
    const PAD = 30, W = canvas.width, H = canvas.height;
    const sx = x => PAD + (x / 100) * (W - PAD * 2);
    const sy = y => PAD + (y / 100) * (H - PAD * 2);

    let found = null;
    (state.nodes || []).forEach(n => {
      const r = n.role === "root" ? 18 : n.role === "router" ? 14 : 11;
      if (Math.hypot(mx - sx(n.x), my - sy(n.y)) < r + 5) found = n;
    });
    setHoveredNode(found ? found.id : null);
    setTooltip(found ? {
      x: e.clientX, y: e.clientY,
      node: found,
    } : null);
  }, [state.nodes]);

  return (
    <div style={{ position: "relative", flex: 1, minHeight: 0 }}>
      <canvas ref={canvasRef} width={700} height={500}
        style={{ width: "100%", height: "100%", display: "block" }}
        onMouseMove={handleMouseMove}
        onMouseLeave={() => { setTooltip(null); setHoveredNode(null); }}
      />
      {tooltip && (
        <div style={{ position: "fixed", left: tooltip.x + 12, top: tooltip.y - 10, zIndex: 999,
          background: COLORS.bg2, border: `1px solid ${nodeColor(tooltip.node)}`,
          borderRadius: 8, padding: "8px 12px", fontSize: 12, fontFamily: "monospace",
          color: COLORS.white, pointerEvents: "none", minWidth: 140 }}>
          <div style={{ color: nodeColor(tooltip.node), fontWeight: 700, marginBottom: 4 }}>{tooltip.node.label} ({tooltip.node.role})</div>
          <div>Rank: {tooltip.node.rank === 9999 ? "—" : tooltip.node.rank}</div>
          <div>Energy: {tooltip.node.energy.toFixed(1)} / {tooltip.node.initEnergy} J</div>
          <div>Ratio: {(tooltip.node.energy / tooltip.node.initEnergy * 100).toFixed(0)}%</div>
          <div>Status: <span style={{ color: tooltip.node.alive ? COLORS.green : COLORS.red }}>{tooltip.node.alive ? "ALIVE" : "DEAD"}</span></div>
          <div>Pos: ({tooltip.node.x.toFixed(0)}, {tooltip.node.y.toFixed(0)})</div>
        </div>
      )}
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════════════
//  SIMULATION SCREEN
// ═══════════════════════════════════════════════════════════════════════════════
function SimScreen({ cfg, onSetup, onReport, engine }) {
  const { state, tick, pause, stop } = engine;
  const logRef = useRef(null);
  const [txFilter, setTxFilter] = useState("ALL");
  const [activeTab, setActiveTab] = useState("log");

  useEffect(() => {
    if (logRef.current) logRef.current.scrollTop = logRef.current.scrollHeight;
  }, [tick]);

  const s = state.stats || {};
  const sent = s.sent || 0, delivered = s.delivered || 0, dropped = s.dropped || 0;
  const rate = sent > 0 ? (delivered / sent * 100).toFixed(1) : "—";
  const alive = (state.nodes || []).filter(n => n.alive).length;
  const total = (state.nodes || []).length;

  const tagColor = tag => ({
    cyan:"#58a6ff", green:"#3fb950", amber:"#d29922", red:"#f85149",
    muted:"#8b949e", purple:"#bc8cff", dio:"#58a6ff", dis:"#ffa657", dao:"#3fb950"
  }[tag] || COLORS.white);

  const dodagLabel = {
    idle: ["● Waiting…", COLORS.muted],
    DIS:  ["● Phase 1/3: DIS — Soliciting…", COLORS.rpl.DIS],
    DIO:  ["● Phase 2/3: DIO — Propagating ranks…", COLORS.cyan],
    DAO:  ["● Phase 3/3: DAO — Registering routes…", COLORS.green],
    done: ["✓ DODAG Formed — routing active", COLORS.green],
  }[state.dodagPhase || "idle"] || ["● Waiting…", COLORS.muted];

  const txEntries = (state.txLog || []).filter(e => txFilter === "ALL" || e.msgType === txFilter);

  return (
    <div style={{ height: "100vh", display: "flex", flexDirection: "column", background: COLORS.bg, fontFamily: "'JetBrains Mono',monospace", overflow: "hidden" }}>
      {/* Top bar */}
      <div style={{ display: "flex", alignItems: "center", gap: 8, padding: "10px 16px", background: COLORS.bg2, borderBottom: `1px solid ${COLORS.border}`, flexShrink: 0 }}>
        <div style={{ width:6, height:6, borderRadius:"50%", background: COLORS.green, boxShadow:`0 0 8px ${COLORS.green}`, flexShrink:0 }} />
        <span style={{ color: COLORS.white, fontWeight: 700, fontSize: 13, marginRight: 8, letterSpacing:"-0.01em" }}>RPL Simulation</span>
        <button onClick={onSetup} style={smallBtn(COLORS.border, COLORS.mutedHi)}>◀ Setup</button>
        <button onClick={pause} style={smallBtn(COLORS.border, COLORS.amber)}>{state.paused ? "▶ Resume" : "⏸ Pause"}</button>
        <button onClick={stop} style={smallBtn(COLORS.border, COLORS.red)}>⏹ Stop</button>
        <button onClick={onReport} style={smallBtn(COLORS.purple, COLORS.purple)}>↗ Report</button>
        <div style={{ marginLeft: "auto", fontSize: 11, color: COLORS.muted }}>
          <span style={{ color: COLORS.cyan }}>{cfg.mode === "energy" ? "Energy-Aware Greedy" : "Minimum Energy Routing"}</span>
        </div>
      </div>

      {/* Main area: LEFT LOG | CANVAS | RIGHT STATS */}
      <div style={{ flex: 1, display: "flex", minHeight: 0, overflow: "hidden" }}>

        {/* ── LEFT PANEL: Event Log + MSG Log ── */}
        <div style={{ width: 280, display: "flex", flexDirection: "column", background: COLORS.bg2, borderRight: `1px solid ${COLORS.border}`, overflow: "hidden", flexShrink: 0 }}>

          {/* Log tabs */}
          <div style={{ display: "flex", borderBottom: `1px solid ${COLORS.border}`, flexShrink: 0 }}>
            {[["log","Event Log"],["tx","Msg Log"]].map(([id,label]) => (
              <button key={id} onClick={() => setActiveTab(id)}
                style={{ flex:1, padding:"9px 4px", background: "transparent",
                  border:"none", borderBottom: activeTab===id ? `2px solid ${COLORS.cyan}` : "2px solid transparent",
                  color: activeTab===id ? COLORS.cyan : COLORS.muted,
                  fontSize:10, cursor:"pointer", fontFamily:"'JetBrains Mono',monospace", fontWeight: activeTab===id ? 700 : 400,
                  letterSpacing:"0.08em", textTransform:"uppercase", transition:"color 0.15s" }}>
                {label}
              </button>
            ))}
          </div>

          {/* Event Log */}
          {activeTab === "log" && (
            <div ref={logRef} style={{ flex:1, overflowY:"auto", padding:"10px 12px", fontSize:11, lineHeight:1.7 }}>
              {(state.eventLog || []).length === 0 && (
                <div style={{ color: COLORS.muted, fontStyle: "italic", marginTop: 8 }}>Waiting for events…</div>
              )}
              {(state.eventLog || []).map((e,i) => (
                <div key={i} style={{ color: tagColor(e.tag), marginBottom:3, wordBreak:"break-all",
                  paddingBottom:3, borderBottom:`1px solid ${COLORS.border}18` }}>{e.text}</div>
              ))}
            </div>
          )}

          {/* TX / MSG Log */}
          {activeTab === "tx" && (
            <div style={{ flex:1, display:"flex", flexDirection:"column", overflow:"hidden" }}>
              <div style={{ display:"flex", flexWrap:"wrap", gap:4, padding:"8px 10px", borderBottom:`1px solid ${COLORS.border}`, flexShrink:0 }}>
                {["ALL","DIS","DIO","DAO","PKT","ACK"].map(f => (
                  <button key={f} onClick={() => setTxFilter(f)}
                    style={{ padding:"2px 8px", border:`1px solid ${txFilter===f ? (COLORS.rpl[f]||COLORS.cyan) : COLORS.border}`,
                      background: txFilter===f ? (COLORS.rpl[f]||COLORS.cyan)+"22" : "transparent",
                      color: txFilter===f ? (COLORS.rpl[f]||COLORS.cyan) : COLORS.muted,
                      borderRadius:5, fontSize:10, cursor:"pointer", fontFamily:"'JetBrains Mono',monospace" }}>
                    {f}
                  </button>
                ))}
              </div>
              <div style={{ flex:1, overflowY:"auto", padding:8 }}>
                {txEntries.length === 0 && (
                  <div style={{ color: COLORS.muted, fontStyle:"italic", fontSize:11, marginTop:8 }}>No messages yet…</div>
                )}
                {txEntries.slice(-100).map((e,i) => (
                  <div key={i} style={{ marginBottom:7, border:`1px solid ${e.color}30`, borderRadius:8,
                    padding:"7px 10px", background: COLORS.bg3 }}>
                    <div style={{ display:"flex", alignItems:"center", gap:6, marginBottom:4 }}>
                      <span style={{ background:e.color, color:COLORS.bg, padding:"1px 6px", borderRadius:4,
                        fontSize:9, fontWeight:700, flexShrink:0, letterSpacing:"0.05em" }}>{e.msgType}</span>
                      <span style={{ color:COLORS.white, fontSize:11, fontWeight:700 }}>{e.src} → {e.dst}</span>
                      {e.phase && <span style={{ color:COLORS.muted, fontSize:9, marginLeft:"auto" }}>{e.phase}</span>}
                    </div>
                    <div style={{ color:e.color, fontSize:10, wordBreak:"break-all", lineHeight:1.5 }}>{e.content}</div>
                    <div style={{ color:COLORS.muted, fontSize:9, marginTop:3 }}>{e.ts}</div>
                  </div>
                ))}
              </div>
            </div>
          )}
        </div>

        {/* ── CANVAS (center, grows) ── */}
        <NetworkCanvas state={state} tick={tick} />

        {/* ── RIGHT PANEL: Stats + Energy + DODAG ── */}
        <div style={{ width: 220, display: "flex", flexDirection: "column", background: COLORS.bg2,
          borderLeft: `1px solid ${COLORS.border}`, overflow: "hidden", flexShrink: 0 }}>

          {/* Stats */}
          <div style={{ padding: "12px 14px", borderBottom: `1px solid ${COLORS.border}`, flexShrink:0 }}>
            <div style={{ color: COLORS.mutedHi, fontSize: 10, fontWeight: 600, letterSpacing:"0.1em", textTransform:"uppercase", marginBottom: 10 }}>Live Statistics</div>
            {[
              ["Sent",     sent,      COLORS.cyan],
              ["Delivered",delivered, COLORS.green],
              ["Dropped",  dropped,   dropped > 0 ? COLORS.red : COLORS.muted],
              ["Success",  rate + (rate !== "—" ? "%" : ""),
                           parseFloat(rate) > 80 ? COLORS.green : parseFloat(rate) > 50 ? COLORS.amber : COLORS.red],
              ["Active",   `${alive}/${total}`, COLORS.cyan],
            ].map(([k,v,c]) => (
              <div key={k} style={{ display:"flex", justifyContent:"space-between", marginBottom:6, fontSize:12 }}>
                <span style={{ color: COLORS.muted }}>{k}</span>
                <span style={{ color: c, fontWeight: 700 }}>{v}</span>
              </div>
            ))}
          </div>

          {/* Node energy */}
          <div style={{ padding: "12px 14px", borderBottom: `1px solid ${COLORS.border}`, flexShrink:0 }}>
            <div style={{ color: COLORS.mutedHi, fontSize: 10, fontWeight: 600, letterSpacing:"0.1em", textTransform:"uppercase", marginBottom: 10 }}>Node Energy</div>
            {(state.nodes || []).map(n => {
              const r = n.initEnergy > 0 ? n.energy / n.initEnergy : 0;
              const c = nodeColor(n);
              return (
                <div key={n.id} style={{ display: "flex", alignItems: "center", gap: 6, marginBottom: 6 }}>
                  <span style={{ color: n.alive ? c : COLORS.muted, width: 36, fontSize: 10,
                    overflow:"hidden", whiteSpace:"nowrap", flexShrink:0 }}>{n.label}</span>
                  <div style={{ flex: 1, height: 4, background: COLORS.bg4, borderRadius: 2, overflow: "hidden" }}>
                    <div style={{ width: `${Math.round(r*100)}%`, height: "100%", background: c,
                      borderRadius: 2, transition: "width 0.4s" }} />
                  </div>
                  <span style={{ color: c, fontSize: 9, width: 36, textAlign: "right", flexShrink:0 }}>{Math.round(n.energy)}J</span>
                </div>
              );
            })}
          </div>

          {/* DODAG phase */}
          <div style={{ padding: "12px 14px", flexShrink:0 }}>
            <div style={{ color: COLORS.mutedHi, fontSize: 10, fontWeight: 600, letterSpacing:"0.1em", textTransform:"uppercase", marginBottom: 8 }}>DODAG Formation</div>
            <div style={{ color: dodagLabel[1], fontSize: 11, marginBottom: 10, lineHeight: 1.5, fontWeight:600 }}>{dodagLabel[0]}</div>
            <div style={{ display: "flex", flexDirection: "column", gap: 6 }}>
              {[["DIS","Solicitation","#fb923c"],["DIO","Info Object",COLORS.cyan],["DAO","Route Advert",COLORS.green]].map(([k,tip,c]) => (
                <div key={k} style={{ display:"flex", alignItems:"center", gap:7, fontSize:11 }}>
                  <span style={{ width:6, height:6, borderRadius:"50%", background:c, flexShrink:0, boxShadow:`0 0 6px ${c}` }} />
                  <span style={{ color:c, fontWeight:700, width:28 }}>{k}</span>
                  <span style={{ color:COLORS.muted, fontSize:10 }}>{tip}</span>
                </div>
              ))}
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}

function smallBtn(border, color) {
  return { background:"transparent", border:`1px solid ${border}`, color, padding:"5px 12px",
    borderRadius:6, fontFamily:"'JetBrains Mono',monospace", fontSize:10, cursor:"pointer",
    letterSpacing:"0.06em", transition:"all 0.15s" };
}

// ═══════════════════════════════════════════════════════════════════════════════
//  REPORT SCREEN
// ═══════════════════════════════════════════════════════════════════════════════
function ReportScreen({ state, cfg, onBack, onNewSetup }) {
  const s = state.stats || {};
  const nodes = state.nodes || [];
  const edges = state.edges || [];
  const sent = s.sent||0, delivered = s.delivered||0, dropped = s.dropped||0;
  const rate = sent > 0 ? delivered/sent*100 : 0;
  const avgHops = delivered > 0 ? s.totalHops/delivered : 0;
  const elapsed = s.startTime ? ((performance.now()/1000) - s.startTime).toFixed(1) : "0";
  const dead = nodes.filter(n => !n.alive);
  const totalInit = nodes.reduce((a,n) => a + n.initEnergy, 0);
  const totalRem  = nodes.reduce((a,n) => a + n.energy, 0);
  const consumed  = totalInit - totalRem;
  const avgEdgeE  = edges.length > 0 ? edges.reduce((a,e) => a + e.energyCost,0)/edges.length : 1;
  const alpha = 0.65;
  const threshold = totalInit > 0
    ? parseFloat(((totalInit*alpha) / (nodes.length * Math.max(avgHops,1) * avgEdgeE)).toFixed(2))
    : 0;
  const thresholdOk = totalRem > threshold * nodes.length;
  const status = rate > 80 ? "Healthy" : rate > 50 ? "Moderate" : "Critical";
  const modeName = cfg?.mode === "energy" ? "Energy-Aware Greedy" : "Minimum Energy Routing";

  const Card = ({label, val, color}) => (
    <div style={{ background: `linear-gradient(135deg, ${COLORS.bg2} 0%, ${COLORS.bg3} 100%)`,
      border:`1px solid ${COLORS.border}`, borderRadius:12,
      padding:"16px 12px", textAlign:"center", flex:1, minWidth:90 }}>
      <div style={{ fontSize:26, fontWeight:700, color, fontFamily:"'Space Grotesk',sans-serif" }}>{val}</div>
      <div style={{ fontSize:10, color:COLORS.muted, marginTop:5, letterSpacing:"0.06em", textTransform:"uppercase" }}>{label}</div>
    </div>
  );

  const parentMap = {};
  (state.dodagTreeEdges||[]).forEach(([pid,cid]) => parentMap[cid] = pid);
  const nonRoot = nodes.filter(n => n.role !== "root");
  const adj = {};
  nodes.forEach(n => adj[n.id] = []);
  edges.forEach(e => { adj[e.a]?.push(e.b); adj[e.b]?.push(e.a); });

  return (
    <div style={{ minHeight:"100vh", background:COLORS.bg, color:COLORS.white, fontFamily:"'JetBrains Mono',monospace", display:"flex", flexDirection:"column" }}>
      {/* Topbar */}
      <div style={{ display:"flex", alignItems:"center", gap:8, padding:"10px 20px", background:COLORS.bg2, borderBottom:`1px solid ${COLORS.border}`, flexShrink:0 }}>
        <div style={{ width:6, height:6, borderRadius:"50%", background:COLORS.purple, boxShadow:`0 0 8px ${COLORS.purple}`, flexShrink:0 }} />
        <span style={{ color:COLORS.white, fontWeight:700, fontSize:13, marginRight:8 }}>Simulation Report</span>
        <button onClick={onBack} style={smallBtn(COLORS.border,COLORS.mutedHi)}>◀ Simulation</button>
        <button onClick={onNewSetup} style={smallBtn(COLORS.border,COLORS.cyan)}>↺ New Setup</button>
      </div>

      <div style={{ flex:1, overflowY:"auto", padding:"28px 36px" }}>
        {/* Sub header */}
        <div style={{ textAlign:"center", marginBottom:28 }}>
          <div style={{ color:COLORS.muted, fontSize:11, letterSpacing:"0.06em" }}>
            {modeName} &nbsp;·&nbsp; {nodes.length} nodes &nbsp;·&nbsp; {cfg?.pktSize||128}B packets &nbsp;·&nbsp; {sent} transmissions
          </div>
          <div style={{ height:1, background:COLORS.border, margin:"14px 0" }} />
        </div>

        {/* Metric cards */}
        <div style={{ display:"flex", flexWrap:"wrap", gap:10, marginBottom:28 }}>
          <Card label="Nodes"        val={nodes.length}                color={COLORS.white} />
          <Card label="Sent"         val={sent}                        color={COLORS.cyan} />
          <Card label="Delivered"    val={delivered}                   color={COLORS.green} />
          <Card label="Dropped"      val={dropped}                     color={dropped>0?COLORS.red:COLORS.green} />
          <Card label="Delivery Rate" val={`${rate.toFixed(1)}%`}     color={rate>80?COLORS.green:rate>50?COLORS.amber:COLORS.red} />
          <Card label="Avg Hops"     val={avgHops.toFixed(1)}          color={COLORS.cyan} />
          <Card label="Energy Used"  val={`${consumed.toFixed(1)}J`}  color={COLORS.amber} />
          <Card label="Dead Nodes"   val={dead.length}                 color={dead.length>0?COLORS.red:COLORS.green} />
        </div>

        {/* Threshold */}
        <Section title="Threshold Energy Analysis" />
        <div style={{ background:COLORS.bg3, border:`1px solid ${COLORS.purple}40`, borderRadius:12, padding:20, marginBottom:24 }}>
          <div style={{ color:COLORS.muted, fontSize:11, marginBottom:10, lineHeight:1.7 }}>
            Threshold = (Σ Initial Energy × α) ÷ (N × Avg Hops × Avg Edge Cost)
          </div>
          <div style={{ color:COLORS.purple, fontSize:18, fontWeight:700, marginBottom:10, lineHeight:1.5 }}>
            = ({totalInit.toFixed(0)} × {alpha}) ÷ ({nodes.length} × {avgHops.toFixed(2)} × {avgEdgeE.toFixed(2)}) = {threshold} J
          </div>
          <div style={{ color:thresholdOk?COLORS.green:COLORS.amber, fontWeight:700, fontSize:13, marginBottom:6 }}>
            {thresholdOk ? "✓ Above threshold — routing sustainable" : "⚠ Below threshold — routing at risk"}
          </div>
          <div style={{ color:COLORS.muted, fontSize:10 }}>
            Remaining: {totalRem.toFixed(1)} J &nbsp;·&nbsp; Required: {(threshold*nodes.length).toFixed(1)} J &nbsp;·&nbsp; α = {alpha}
          </div>
        </div>

        {/* Briefing */}
        <Section title="Network Briefing" />
        <div style={{ background:COLORS.bg2, border:`1px solid ${COLORS.border}`, borderRadius:12, padding:20, marginBottom:24, fontSize:12, lineHeight:2 }}>
          <div>Routing Mode: <span style={{ color:COLORS.cyan }}>{modeName}</span></div>
          <div>Network Status: <span style={{ color:rate>80?COLORS.green:rate>50?COLORS.amber:COLORS.red }}>{status}</span></div>
          <div>Simulation Time: <span style={{ color:COLORS.white }}>{elapsed} seconds</span></div>
          <div style={{ height:1, background:COLORS.border, margin:"8px 0" }} />
          <div>Packets Sent: <span style={{ color:COLORS.cyan }}>{sent}</span></div>
          <div>Packets Delivered: <span style={{ color:COLORS.green }}>{delivered}</span></div>
          <div>Packets Dropped: <span style={{ color:dropped>0?COLORS.red:COLORS.muted }}>{dropped}</span></div>
          <div>Success Rate: <span style={{ color:rate>80?COLORS.green:rate>50?COLORS.amber:COLORS.red }}>{rate.toFixed(1)}%</span></div>
          <div style={{ height:1, background:COLORS.border, margin:"8px 0" }} />
          <div>Average Hop Count: <span style={{ color:COLORS.white }}>{avgHops.toFixed(1)}</span></div>
          <div>Total Energy Used: <span style={{ color:COLORS.amber }}>{consumed.toFixed(1)} J</span></div>
          <div>Dead Nodes: <span style={{ color:dead.length>0?COLORS.red:COLORS.green }}>{dead.length}</span></div>
        </div>

        {/* Node energy table */}
        <Section title="Node Energy Status" />
        <div style={{ background:COLORS.bg2, border:`1px solid ${COLORS.border}`, borderRadius:12, overflow:"hidden", marginBottom:24 }}>
          <table style={{ width:"100%", borderCollapse:"collapse", fontSize:12 }}>
            <thead>
              <tr style={{ background:COLORS.bg3 }}>
                {["Node","Role","Initial (J)","Remaining (J)","Consumed (J)","Level","Status"].map(h => (
                  <th key={h} style={{ padding:"9px 10px", textAlign:"left", color:COLORS.muted, borderBottom:`1px solid ${COLORS.border}`, fontSize:10, letterSpacing:"0.06em", textTransform:"uppercase", fontWeight:500 }}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {[...nodes].sort((a,b) => a.energy/a.initEnergy - b.energy/b.initEnergy).map(n => {
                const r = n.initEnergy>0 ? n.energy/n.initEnergy : 0;
                const barFill = "█".repeat(Math.round(r*10)) + "░".repeat(10-Math.round(r*10));
                const st = !n.alive ? "DEAD" : r>0.5?"OK":r>0.2?"LOW":"CRIT";
                const sc = !n.alive?COLORS.red:r>0.5?COLORS.green:r>0.2?COLORS.amber:COLORS.red;
                return (
                  <tr key={n.id} style={{ borderBottom:`1px solid ${COLORS.border}18` }}>
                    <td style={{ padding:"8px 10px", color:nodeColor(n), fontWeight:700 }}>{n.label}</td>
                    <td style={{ padding:"8px 10px", color:COLORS.muted }}>{n.role}</td>
                    <td style={{ padding:"8px 10px", color:COLORS.white }}>{n.initEnergy.toFixed(0)}</td>
                    <td style={{ padding:"8px 10px", color:nodeColor(n) }}>{n.energy.toFixed(1)}</td>
                    <td style={{ padding:"8px 10px", color:COLORS.amber }}>{(n.initEnergy-n.energy).toFixed(1)}</td>
                    <td style={{ padding:"8px 10px", color:nodeColor(n), letterSpacing:-1, fontSize:10 }}>{barFill}</td>
                    <td style={{ padding:"8px 10px", color:sc, fontWeight:700, fontSize:11 }}>{st}</td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>

        {/* DODAG Formation */}
        <Section title="DODAG Formation · DIS / DIO / DAO" />
        <div style={{ display:"flex", gap:10, marginBottom:20, flexWrap:"wrap" }}>
          {[
            ["DIS Messages", nonRoot.length, COLORS.rpl.DIS, "Each non-root node solicits DODAG info"],
            ["DIO Messages", (state.dodagTreeEdges||[]).length, COLORS.cyan, "Root propagates rank downward via BFS"],
            ["DAO Messages", nonRoot.length, COLORS.green, "Nodes register routes upward to root"],
            ["Tree Depth", Math.max(...nodes.map(n => n.rank<9999?n.rank:0), 0), COLORS.purple, "Max DODAG rank achieved"],
          ].map(([label,val,color,tip]) => (
            <div key={label} style={{ flex:1, minWidth:120, background:`linear-gradient(135deg, ${COLORS.bg2} 0%, ${COLORS.bg3} 100%)`, border:`1px solid ${color}30`, borderRadius:12, padding:"16px 12px", textAlign:"center" }}>
              <div style={{ fontSize:28, fontWeight:700, color, fontFamily:"'Space Grotesk',sans-serif" }}>{val}</div>
              <div style={{ fontSize:10, fontWeight:700, color, marginBottom:4, letterSpacing:"0.06em", textTransform:"uppercase" }}>{label}</div>
              <div style={{ fontSize:10, color:COLORS.muted }}>{tip}</div>
            </div>
          ))}
        </div>

        <div style={{ color:COLORS.mutedHi, fontWeight:600, fontSize:10, letterSpacing:"0.1em", textTransform:"uppercase", marginBottom:10 }}>
          DODAG Tree Structure — parent → child relationships
        </div>
        <div style={{ background:COLORS.bg2, border:`1px solid ${COLORS.border}`, borderRadius:12, overflow:"hidden", marginBottom:20 }}>
          <table style={{ width:"100%", borderCollapse:"collapse", fontSize:11 }}>
            <thead>
              <tr style={{ background:COLORS.bg3 }}>
                {["Phase","Message","From","To","Rank","Description"].map(h => (
                  <th key={h} style={{ padding:"9px 10px", textAlign:"left", color:COLORS.muted, borderBottom:`1px solid ${COLORS.border}`, fontSize:10, letterSpacing:"0.06em", textTransform:"uppercase", fontWeight:500 }}>{h}</th>
                ))}
              </tr>
            </thead>
            <tbody>
              {/* DIS rows */}
              {nonRoot.map(node => {
                const nbrs = adj[node.id]||[];
                if (!nbrs.length) return null;
                const closest = nbrs.reduce((best,nid) => dist(node,nodes[nid])<dist(node,nodes[best])?nid:best, nbrs[0]);
                return (
                  <tr key={`dis-${node.id}`} style={{ borderBottom:`1px solid ${COLORS.border}10` }}>
                    <td style={{ padding:"6px 10px", color:COLORS.rpl.DIS }}>1 DIS</td>
                    <td style={{ padding:"6px 10px", color:COLORS.rpl.DIS }}>DIS?</td>
                    <td style={{ padding:"6px 10px", color:COLORS.white }}>{node.label}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.white }}>{nodes[closest]?.label||"—"}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.muted }}>—</td>
                    <td style={{ padding:"6px 10px", color:COLORS.muted }}>{node.label} solicits DODAG information</td>
                  </tr>
                );
              })}
              {/* DIO rows */}
              {(state.dodagTreeEdges||[]).map(([pid,cid]) => {
                const pn=nodes[pid], cn=nodes[cid];
                if (!pn||!cn) return null;
                return (
                  <tr key={`dio-${pid}-${cid}`} style={{ borderBottom:`1px solid ${COLORS.border}10` }}>
                    <td style={{ padding:"6px 10px", color:COLORS.cyan }}>2 DIO</td>
                    <td style={{ padding:"6px 10px", color:COLORS.cyan }}>DIO[r={cn.rank}]</td>
                    <td style={{ padding:"6px 10px", color:COLORS.white }}>{pn.label}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.white }}>{cn.label}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.cyan }}>{cn.rank}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.muted }}>{pn.label} advertises rank {cn.rank} to {cn.label}</td>
                  </tr>
                );
              })}
              {/* DAO rows */}
              {[...nonRoot].sort((a,b)=>b.rank-a.rank).map(node => {
                const pid = parentMap[node.id];
                if (pid === undefined) return null;
                const pn = nodes[pid];
                if (!pn) return null;
                return (
                  <tr key={`dao-${node.id}`} style={{ borderBottom:`1px solid ${COLORS.border}10` }}>
                    <td style={{ padding:"6px 10px", color:COLORS.green }}>3 DAO</td>
                    <td style={{ padding:"6px 10px", color:COLORS.green }}>DAO[r={node.rank}]</td>
                    <td style={{ padding:"6px 10px", color:COLORS.white }}>{node.label}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.white }}>{pn.label}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.green }}>{node.rank}</td>
                    <td style={{ padding:"6px 10px", color:COLORS.muted }}>{node.label} registers route to {pn.label} (toward root)</td>
                  </tr>
                );
              })}
            </tbody>
          </table>
        </div>

        {/* Explanation box */}
        <div style={{ background:COLORS.bg3, border:`1px solid ${COLORS.border}`, borderRadius:12, padding:20, marginBottom:48, fontSize:12, lineHeight:2, color:COLORS.muted }}>
          <span style={{ color:COLORS.rpl.DIS, fontWeight:700 }}>DIS</span> (DODAG Information Solicitation) — A node broadcasts DIS to ask nearby nodes for DODAG info. This triggers DIO replies.<br/><br/>
          <span style={{ color:COLORS.cyan, fontWeight:700 }}>DIO</span> (DODAG Information Object) — Sent by the root (rank 0) and relayed hop-by-hop downward. Each DIO carries the sender's rank so receivers can compute their own rank (rank = parent_rank + 1). This builds the DODAG tree.<br/><br/>
          <span style={{ color:COLORS.green, fontWeight:700 }}>DAO</span> (Destination Advertisement Object) — After a node learns its rank via DIO, it sends a DAO upward toward the root to register its presence and establish downward route table entries.
        </div>
      </div>
    </div>
  );
}

function Section({ title }) {
  return (
    <div style={{ marginBottom:12 }}>
      <div style={{ display:"flex", alignItems:"center", gap:8 }}>
        <div style={{ width:3, height:14, borderRadius:2, background: COLORS.purple, flexShrink:0 }} />
        <div style={{ color:COLORS.mutedHi, fontWeight:600, fontSize:10, letterSpacing:"0.12em", textTransform:"uppercase" }}>{title}</div>
      </div>
      <div style={{ height:1, background:COLORS.border, marginTop:8, marginBottom:14 }} />
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════════════
//  ROOT APP
// ═══════════════════════════════════════════════════════════════════════════════
export default function App() {
  const [screen, setScreen] = useState("setup");
  const [cfg, setCfg] = useState(null);
  const engine = useSimEngine(cfg, screen === "sim");

  const handleLaunch = (config) => {
    setCfg(config);
    setScreen("sim");
    engine.start(config);
  };

  const handleStop = () => {
    engine.stop();
  };

  const handleSetup = () => {
    engine.stop();
    setScreen("setup");
  };

  const handleReport = () => {
    setScreen("report");
  };

  const handleBack = () => {
    setScreen("sim");
  };

  const handleNewSetup = () => {
    engine.stop();
    setScreen("setup");
  };

  return (
    <div style={{ margin:0, padding:0, boxSizing:"border-box" }}>
      {screen === "setup" && <SetupScreen onLaunch={handleLaunch} />}
      {screen === "sim" && cfg && (
        <SimScreen
          cfg={cfg}
          onSetup={handleSetup}
          onReport={handleReport}
          engine={engine}
        />
      )}
      {screen === "report" && (
        <ReportScreen
          state={engine.state}
          cfg={cfg}
          onBack={handleBack}
          onNewSetup={handleNewSetup}
        />
      )}
    </div>
  );
}

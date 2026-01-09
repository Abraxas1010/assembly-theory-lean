#!/usr/bin/env python3
"""
Generate visualizations for Assembly Theory formalization.

Creates:
- Module dependency graph (SVG)
- Declaration UMAP 2D/3D (HTML)
- Assembly index bounds diagram (SVG)
"""

import argparse
import datetime as _dt
import json
import re
from pathlib import Path

# Optional dependencies
try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False

try:
    import umap
    HAS_UMAP = True
except ImportError:
    HAS_UMAP = False

DATA_VAR = "ASSEMBLY_PROOFS"
DATA_JS_NAME = "assembly_proofs_data.js"


def _iso_now() -> str:
    return _dt.datetime.now(tz=_dt.timezone.utc).isoformat().replace("+00:00", "Z")


def _classify_family(module: str, rel_path: str) -> str:
    """Heuristic module-family classification for coloring."""
    base = Path(rel_path).stem
    if base in {"AssemblyCore"}:
        return "Core"
    if base in {"AssemblyPath"}:
        return "Path"
    if base in {"AssemblyIndex"}:
        return "Index"
    if base in {"AssemblyBounds"}:
        return "Bounds"
    if base in {"AssemblyQuotient"}:
        return "Quotient"
    if "Molecular" in base:
        return "Molecular"
    if "Hypergraph" in base:
        return "Hypergraph"
    if "Space" in base:
        return "Space"
    if base in {"CopyNumberSelection"}:
        return "Selection"
    return "Other"


def _module_name_from_relpath(rel_path: Path) -> str:
    # Relpath is relative to HeytingLean/ATheory
    return "HeytingLean.ATheory." + str(rel_path.with_suffix("")).replace("/", ".")


def _iter_decl_lines(lines: list[str]):
    """Yield (line_no, kind, ident, namespace_prefix) for declarations."""
    ns_stack: list[str] = []
    ns_re = re.compile(r"^\s*namespace\s+([A-Za-z_][\w.]*)\s*$")
    end_re = re.compile(r"^\s*end(?:\s+([A-Za-z_][\w.]*)\s*)?$")
    decl_re = re.compile(
        r"^(theorem|lemma|def|abbrev|structure|inductive|class)\s+([A-Za-z_][\w']*)\b"
    )
    inst_re = re.compile(r"^instance\s+([A-Za-z_][\w']*)\b")

    mods = {
        "private",
        "protected",
        "noncomputable",
        "unsafe",
        "partial",
        "irreducible",
        "mutual",
        "section",
        "namespace",
        "open",
        "attribute",
        "export",
    }

    def strip_attrs_and_mods(line: str) -> str:
        s = line.lstrip()
        # Strip leading attributes like `@[simp]` (possibly multiple).
        while s.startswith("@["):
            end = s.find("]")
            if end == -1:
                break
            s = s[end + 1 :].lstrip()
        tokens = s.split()
        while tokens and tokens[0] in mods:
            tokens = tokens[1:]
        return " ".join(tokens)

    for idx, line in enumerate(lines):
        m = ns_re.match(line)
        if m:
            ns_stack.append(m.group(1))
            continue

        m = end_re.match(line)
        if m:
            if ns_stack:
                # Best-effort: pop one namespace; ignore the identifier (Lean also uses `end section`).
                ns_stack.pop()
            continue

        s = strip_attrs_and_mods(line)
        m = decl_re.match(s)
        if m:
            kind, ident = m.group(1), m.group(2)
            prefix = ".".join(ns_stack)
            kind_norm = "def" if kind == "abbrev" else kind
            yield (idx + 1, kind_norm, ident, prefix)
            continue

        m = inst_re.match(s)
        if m:
            ident = m.group(1)
            prefix = ".".join(ns_stack)
            yield (idx + 1, "instance", ident, prefix)



def extract_declarations(lean_dir: Path) -> list:
    """Extract declarations from Lean files (best-effort, namespace-aware)."""
    decls: list[dict] = []

    for lean_file in sorted(lean_dir.rglob("*.lean")):
        rel_path = lean_file.relative_to(lean_dir)
        module = _module_name_from_relpath(rel_path)

        lines = lean_file.read_text(encoding="utf-8").splitlines()
        for line_no, kind, ident, prefix in _iter_decl_lines(lines):
            full_name = f"{prefix}.{ident}" if prefix else ident
            snippet = "\n".join(lines[line_no - 1 : min(len(lines), line_no + 5)]).rstrip()[:800]
            rel_from_repo = str((lean_dir / rel_path).as_posix())
            family = _classify_family(module, rel_from_repo)
            decls.append(
                {
                    "name": full_name,
                    "id": full_name,
                    "kind": kind,
                    "module": module,
                    "path": rel_from_repo,
                    "line": line_no,
                    "family": family,
                    "snippet": snippet,
                }
            )

    return decls


def extract_imports(lean_dir: Path) -> list:
    """Extract import edges between modules."""
    edges = []

    for lean_file in lean_dir.rglob("*.lean"):
        rel_path = lean_file.relative_to(lean_dir)
        module = _module_name_from_relpath(rel_path)

        content = lean_file.read_text(encoding="utf-8")
        for match in re.finditer(r"^\s*import\s+([A-Za-z0-9_.]+)\s*$", content, flags=re.M):
            target = match.group(1)
            if not target.startswith("HeytingLean.ATheory"):
                continue
            edges.append({"source": target, "target": module})

    return edges


def generate_graph_json(lean_dir: Path, output: Path):
    """Generate graph JSON for visualization."""
    decls = extract_declarations(lean_dir)
    edges = extract_imports(lean_dir)

    # Unique modules
    modules = sorted(set(d["module"] for d in decls))

    graph = {
        "nodes": [{"id": m, "name": m, "type": "module"} for m in modules],
        "edges": edges,
        "declarations": decls,
    }

    with open(output, "w") as f:
        json.dump(graph, f, indent=2)

    print(f"Generated {output}")
    return graph


def generate_dependency_dot(graph: dict, output: Path):
    """Generate DOT file for module dependencies."""
    dot = ["digraph AssemblyTheory {"]
    dot.append('  rankdir=TB;')
    dot.append('  node [shape=box, style=filled, fillcolor=lightblue];')

    # Cluster by namespace
    namespaces = {}
    for node in graph["nodes"]:
        parts = node["name"].split(".")
        ns = ".".join(parts[:3]) if len(parts) >= 3 else parts[0]
        if ns not in namespaces:
            namespaces[ns] = []
        namespaces[ns].append(node["name"])

    for ns, modules in namespaces.items():
        dot.append(f'  subgraph cluster_{ns.replace(".", "_")} {{')
        dot.append(f'    label="{ns}";')
        for m in modules:
            short = m.split(".")[-1]
            dot.append(f'    "{m}" [label="{short}"];')
        dot.append('  }')

    for edge in graph["edges"]:
        if edge["source"] in [n["name"] for n in graph["nodes"]]:
            dot.append(f'  "{edge["source"]}" -> "{edge["target"]}";')

    dot.append("}")

    with open(output, "w") as f:
        f.write("\n".join(dot))

    print(f"Generated {output}")


def _normalize_01(arr: "np.ndarray") -> "np.ndarray":
    lo = arr.min(axis=0)
    hi = arr.max(axis=0)
    span = np.maximum(hi - lo, 1e-9)
    return (arr - lo) / span


def _knn_edges(X: "np.ndarray", k: int = 3) -> list[list[int]]:
    n = int(X.shape[0])
    edges: set[tuple[int, int]] = set()
    for i in range(n):
        d2 = np.sum((X - X[i]) ** 2, axis=1)
        d2[i] = np.inf
        nn = np.argsort(d2)[:k]
        for j in nn:
            a, b = (i, int(j)) if i < int(j) else (int(j), i)
            edges.add((a, b))
    return [[a, b] for (a, b) in sorted(edges)]


def _write_text(path: Path, text: str):
    path.write_text(text, encoding="utf-8")


def generate_umap_html(graph: dict, output_2d: Path, output_3d: Path):
    """Generate interactive 2D/3D UMAP viewers with visible kNN edges."""
    if not (HAS_NUMPY and HAS_UMAP):
        print("Skipping UMAP: requires numpy and umap-learn")
        return

    decls = graph["declarations"]
    if len(decls) < 5:
        print("Not enough declarations for UMAP")
        return

    # Feature vectors (lightweight + deterministic)
    kinds = ["theorem", "lemma", "def", "structure", "inductive", "class", "instance"]
    kind_to_idx = {k: i for i, k in enumerate(kinds)}
    families = sorted(set(d.get("family", "Other") for d in decls))
    fam_to_idx = {f: i for i, f in enumerate(families)}

    X = []
    for d in decls:
        vec = [0.0] * (len(kinds) + len(families) + 6)
        k = d.get("kind", "")
        if k in kind_to_idx:
            vec[kind_to_idx[k]] = 1.0
        fam = d.get("family", "Other")
        if fam in fam_to_idx:
            vec[len(kinds) + fam_to_idx[fam]] = 1.0
        name = d.get("name", "")
        mod = d.get("module", "")
        snip = d.get("snippet", "") or ""
        vec[len(kinds) + len(families) + 0] = float(len(name))
        vec[len(kinds) + len(families) + 1] = float(mod.count("."))
        vec[len(kinds) + len(families) + 2] = float(snip.count("∀") + snip.count("forall"))
        vec[len(kinds) + len(families) + 3] = float(snip.count("∃") + snip.count("exists"))
        vec[len(kinds) + len(families) + 4] = float(snip.count("=") + snip.count("≤") + snip.count("≥"))
        vec[len(kinds) + len(families) + 5] = float(len(snip))
        X.append(vec)

    X = np.asarray(X, dtype=float)

    reducer_2d = umap.UMAP(n_components=2, random_state=42, n_neighbors=min(15, len(X) - 1))
    Y2 = reducer_2d.fit_transform(X)

    reducer_3d = umap.UMAP(n_components=3, random_state=42, n_neighbors=min(15, len(X) - 1))
    Y3 = reducer_3d.fit_transform(X)

    pos2 = _normalize_01(Y2)
    pos3 = _normalize_01(Y3)

    edges = _knn_edges(X, k=3)

    items = []
    for i, d in enumerate(decls):
        items.append(
            {
                "id": d.get("id") or d.get("name"),
                "name": d.get("name"),
                "kind": d.get("kind"),
                "path": d.get("path"),
                "line": d.get("line"),
                "family": d.get("family"),
                "snippet": d.get("snippet"),
                "pos": {"x": float(pos2[i, 0]), "y": float(pos2[i, 1])},
                "pos3": {
                    "x": float(pos3[i, 0]),
                    "y": float(pos3[i, 1]),
                    "z": float(pos3[i, 2]),
                },
            }
        )

    payload = {
        "meta": {
            "generatedAt": _iso_now(),
            "seed": "assembly-theory-umap-v1",
            "source": "RESEARCHER_BUNDLE/HeytingLean/ATheory",
            "notes": "UMAP embedding of Assembly Theory declarations (edges = kNN in feature space).",
        },
        "items": items,
        "edges": edges,
    }

    data_js = output_2d.parent / DATA_JS_NAME
    _write_text(data_js, f"window.{DATA_VAR} = {json.dumps(payload, ensure_ascii=False)}\n")
    print(f"Generated {data_js}")

    _write_text(output_2d, _assembly_2d_html(data_js.name))
    print(f"Generated {output_2d}")
    _write_text(output_3d, _assembly_3d_html(data_js.name))
    print(f"Generated {output_3d}")


def _assembly_family_color_map_js() -> str:
    # Keep consistent with preview colors.
    return """{
      'Core':'#43a047',
      'Space':'#1e88e5',
      'Path':'#00acc1',
      'Index':'#8e24aa',
      'Bounds':'#fbc02d',
      'Quotient':'#d81b60',
      'Molecular':'#f4511e',
      'Hypergraph':'#fb8c00',
      'Selection':'#5e35b1',
      'Other':'#90a4ae'
    }"""


def _assembly_2d_html(data_js_name: str) -> str:
    return f"""<!doctype html>
<html lang=\"en\">
  <head>
    <meta charset=\"utf-8\" />
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />
    <title>Assembly Theory — 2D Proof Map</title>
    <style>
      :root {{ color-scheme: dark; }}
      body {{ margin: 0; overflow: hidden; background:#0b0f14; color:#e6eef7; font: 13px/1.35 ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial; }}
      #ui {{ position: fixed; top: 12px; left: 12px; right: 12px; display:flex; gap: 10px; align-items: center; z-index: 10; }}
      .panel {{ background: rgba(15,23,33,0.92); border: 1px solid #1c2a3a; border-radius: 10px; padding: 10px 12px; backdrop-filter: blur(6px); }}
      input[type=\"text\"]{{ width: 360px; max-width: 60vw; background:#0b1320; color:#e6eef7; border:1px solid #24364a; border-radius: 8px; padding: 7px 10px; outline:none; }}
      label {{ user-select:none; }}
      button {{ background:#132033; color:#e6eef7; border:1px solid #24364a; border-radius: 8px; padding: 7px 10px; cursor:pointer; }}
      button:hover {{ background:#182a42; }}
      #tip {{ position: fixed; pointer-events:none; z-index: 20; padding: 6px 8px; border-radius: 8px; background: rgba(0,0,0,0.75); border:1px solid rgba(255,255,255,0.10); display:none; max-width: 56vw; }}
      #details {{ position: fixed; right: 12px; bottom: 12px; width: min(520px, calc(100vw - 24px)); max-height: 45vh; overflow:auto; white-space: pre-wrap; }}
      #details h3 {{ margin: 0 0 8px; font-size: 14px; }}
      .muted {{ color:#b8c7d9; }}
      .row {{ display:flex; gap: 10px; align-items:center; flex-wrap: wrap; }}
      canvas {{ display:block; }}
      a {{ color:#8ab4f8; text-decoration:none; }}
      a:hover{{ text-decoration:underline; }}
      code {{ background:#0b1320; border:1px solid #24364a; border-radius: 6px; padding:1px 6px; }}
    </style>
  </head>
  <body>
    <div id=\"ui\" class=\"row\">
      <div class=\"panel row\">
        <a href=\"./index.html\">&larr; index</a>
        <input id=\"q\" type=\"text\" placeholder=\"Search declarations (substring)...\" />
        <label><input id=\"showEdges\" type=\"checkbox\" checked /> edges</label>
        <button id=\"fit\">Fit</button>
      </div>
      <div class=\"panel muted\">Pan: drag &middot; Zoom: wheel &middot; Select: click</div>
    </div>
    <div id=\"tip\"></div>
    <div id=\"details\" class=\"panel\" style=\"display:none\"></div>
    <canvas id=\"c\"></canvas>

    <script src=\"./{data_js_name}\"></script>
    <script>
      ;(() => {{
        const data = window.{DATA_VAR} || {{ items: [], edges: [] }}
        const items = data.items || []
        const edges = data.edges || []
        const canvas = document.getElementById('c')
        const ctx = canvas.getContext('2d')
        const tip = document.getElementById('tip')
        const details = document.getElementById('details')
        const q = document.getElementById('q')
        const showEdges = document.getElementById('showEdges')
        const fitBtn = document.getElementById('fit')

        const colorMap = {_assembly_family_color_map_js()}
        const colorForFamily = (fam) => colorMap[fam] || '#90a4ae'

        const margin = 24
        const view = {{ s: 1.0, ox: 0, oy: 0 }}
        let dragging = null
        let hover = null
        let selected = null
        let query = ''

        const visibleIdx = () => {{
          const ql = query.trim().toLowerCase()
          const idx = []
          for (let i=0;i<items.length;i++){{
            const it = items[i]
            if (!it) continue
            if (!ql || String(it.name||'').toLowerCase().includes(ql)) idx.push(i)
          }}
          return idx
        }}
        let vis = visibleIdx()

        const resize = () => {{
          canvas.width = window.innerWidth
          canvas.height = window.innerHeight
          render()
        }}

        const toX = (px) => margin + px * (canvas.width - 2*margin) * view.s + view.ox
        const toY = (py) => margin + (1 - py) * (canvas.height - 2*margin) * view.s + view.oy

        const fit = () => {{
          vis = visibleIdx()
          if (!vis.length) return
          let minX=1e9,maxX=-1e9,minY=1e9,maxY=-1e9
          for (const i of vis){{
            const p = items[i].pos || {{x:0.5,y:0.5}}
            minX = Math.min(minX, p.x); maxX=Math.max(maxX,p.x)
            minY = Math.min(minY, p.y); maxY=Math.max(maxY,p.y)
          }}
          const pad = 0.10
          const w = Math.max(0.02, (maxX-minX)*(1+pad))
          const h = Math.max(0.02, (maxY-minY)*(1+pad))
          view.s = Math.max(0.3, Math.min(10, Math.min(1/w, 1/h)))
          const cx=(minX+maxX)/2, cy=(minY+maxY)/2
          const targetX = canvas.width/2
          const targetY = canvas.height/2
          const innerW = canvas.width - 2*margin
          const innerH = canvas.height - 2*margin
          view.ox = targetX - (margin + cx * innerW * view.s)
          view.oy = targetY - (margin + (1-cy) * innerH * view.s)
          render()
        }}
        fitBtn.addEventListener('click', fit)

        const dist2 = (a,b,c,d) => (a-c)*(a-c)+(b-d)*(b-d)
        const hitTest = (sx, sy) => {{
          let best = null
          let bestD = Infinity
          for (const i of vis){{
            const p = items[i].pos
            if (!p) continue
            const x = toX(p.x), y = toY(p.y)
            const d = dist2(sx, sy, x, y)
            if (d < bestD) {{ bestD = d; best = i }}
          }}
          const r = 12
          if (best !== null && bestD <= r*r) return best
          return null
        }}

        const showTip = (sx, sy, it) => {{
          tip.style.display = 'block'
          tip.style.left = (sx + 12) + 'px'
          tip.style.top = (sy + 12) + 'px'
          tip.textContent = it.name
        }}
        const hideTip = () => {{ tip.style.display='none' }}

        const escapeHtml = (s) => String(s).replace(/[&<>\\"]/g, (c) => ({{'&':'&amp;','<':'&lt;','>':'&gt;','\\"':'&quot;'}}[c]||c))

        const showDetails = (it) => {{
          const loc = it.path ? `${{it.path}}:${{it.line||1}}` : ''
          details.style.display = 'block'
          details.innerHTML =
            `<h3>${{escapeHtml(it.name||'')}}</h3>` +
            `<div class=\"muted\">${{escapeHtml(it.kind||'')}} &middot; <code>${{escapeHtml(it.family||'')}}</code></div>` +
            (loc ? `<div style=\"margin-top:6px\"><code>${{escapeHtml(loc)}}</code></div>` : '') +
            (it.snippet ? `<div style=\"margin-top:10px\" class=\"muted\"><pre style=\"margin:0\">${{escapeHtml(it.snippet)}}</pre></div>` : '')
        }}

        const render = () => {{
          vis = visibleIdx()
          ctx.clearRect(0,0,canvas.width,canvas.height)
          ctx.fillStyle = '#0b0f14'
          ctx.fillRect(0,0,canvas.width,canvas.height)

          if (showEdges.checked) {{
            ctx.lineWidth = 1
            ctx.strokeStyle = 'rgba(59,75,93,0.30)'
            ctx.beginPath()
            const visSet = new Set(vis)
            for (const [i,j] of edges){{
              if (!visSet.has(i) || !visSet.has(j)) continue
              const a = items[i].pos, b = items[j].pos
              if (!a || !b) continue
              ctx.moveTo(toX(a.x), toY(a.y))
              ctx.lineTo(toX(b.x), toY(b.y))
            }}
            ctx.stroke()
          }}

          for (const i of vis){{
            const it = items[i]
            const p = it.pos
            if (!p) continue
            const x = toX(p.x), y = toY(p.y)
            const base = 3.4
            const r = (i === selected ? base*1.9 : i === hover ? base*1.5 : base)
            ctx.beginPath()
            ctx.fillStyle = colorForFamily(it.family || '')
            ctx.globalAlpha = 0.95
            ctx.arc(x, y, r, 0, Math.PI*2)
            ctx.fill()
          }}
          ctx.globalAlpha = 1
        }}

        q.addEventListener('input', () => {{ query = q.value; render() }})

        canvas.addEventListener('mousemove', (ev) => {{
          const idx = hitTest(ev.clientX, ev.clientY)
          hover = idx
          if (idx !== null) showTip(ev.clientX, ev.clientY, items[idx])
          else hideTip()
          render()
        }})

        canvas.addEventListener('mousedown', (ev) => {{
          dragging = {{ x: ev.clientX, y: ev.clientY }}
        }})
        window.addEventListener('mouseup', () => {{ dragging = null }})

        window.addEventListener('mousemove', (ev) => {{
          if (!dragging) return
          const dx = ev.clientX - dragging.x
          const dy = ev.clientY - dragging.y
          dragging = {{ x: ev.clientX, y: ev.clientY }}
          view.ox += dx
          view.oy += dy
          render()
        }})

        canvas.addEventListener('wheel', (ev) => {{
          ev.preventDefault()
          const factor = ev.deltaY > 0 ? 0.92 : 1.08
          view.s = Math.max(0.2, Math.min(30, view.s * factor))
          render()
        }}, {{ passive:false }})

        canvas.addEventListener('click', (ev) => {{
          const idx = hitTest(ev.clientX, ev.clientY)
          selected = idx
          if (idx !== null) showDetails(items[idx])
          else details.style.display = 'none'
          render()
        }})

        window.addEventListener('resize', resize)
        resize(); fit();
      }})()
    </script>
  </body>
</html>
"""


def _assembly_3d_html(data_js_name: str) -> str:
    return f"""<!doctype html>
<html lang=\"en\">
  <head>
    <meta charset=\"utf-8\" />
    <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />
    <title>Assembly Theory — 3D Proof Map</title>
    <style>
      :root {{ color-scheme: dark; }}
      body {{ margin: 0; overflow: hidden; background:#0b0f14; color:#e6eef7; font: 13px/1.35 ui-sans-serif, system-ui, -apple-system, Segoe UI, Roboto, Helvetica, Arial; }}
      #ui {{ position: fixed; top: 12px; left: 12px; right: 12px; display:flex; gap: 10px; align-items: center; z-index: 10; }}
      .panel {{ background: rgba(15,23,33,0.92); border: 1px solid #1c2a3a; border-radius: 10px; padding: 10px 12px; backdrop-filter: blur(6px); }}
      .muted {{ color:#b8c7d9; }}
      #tip {{ position: fixed; pointer-events:none; z-index: 20; padding: 6px 8px; border-radius: 8px; background: rgba(0,0,0,0.75); border:1px solid rgba(255,255,255,0.10); display:none; max-width: 56vw; }}
      #details {{ position: fixed; right: 12px; bottom: 12px; width: min(520px, calc(100vw - 24px)); max-height: 45vh; overflow:auto; white-space: pre-wrap; }}
      #details h3 {{ margin: 0 0 8px; font-size: 14px; }}
      a {{ color:#8ab4f8; text-decoration:none; }}
      a:hover{{ text-decoration:underline; }}
      code {{ background:#0b1320; border:1px solid #24364a; border-radius: 6px; padding:1px 6px; }}
    </style>
  </head>
  <body>
    <div id=\"ui\" class=\"panel\">
      <a href=\"./index.html\">&larr; index</a>
      <span style=\"margin-left:10px\" class=\"muted\">Drag: rotate &middot; Wheel: zoom &middot; Shift+drag/right-drag: pan &middot; Hover/click: details</span>
    </div>
    <div id=\"tip\"></div>
    <div id=\"details\" class=\"panel\" style=\"display:none\"></div>

    <script src=\"./vendor/three.min.js\"></script>
    <script src=\"./{data_js_name}\"></script>
    <script>
      ;(() => {{
        const params = new URLSearchParams(window.location.search)
        const EMBED = params.get('embed') === '1'
        const SPIN = params.get('spin') === '1'
        if (EMBED) {{
          const ui = document.getElementById('ui')
          if (ui) ui.style.display = 'none'
        }}

        const data = window.{DATA_VAR} || {{ items: [], edges: [] }}
        const items = data.items || []
        const edges = data.edges || []

        const tip = document.getElementById('tip')
        const details = document.getElementById('details')
        if (EMBED) {{
          if (tip) tip.style.display = 'none'
          if (details) details.style.display = 'none'
        }}

        const colorMap = {_assembly_family_color_map_js()}
        const colorForFamily = (fam) => {{
          const c = colorMap[fam] || '#90a4ae'
          return parseInt(c.replace('#',''), 16)
        }}

        const renderer = new THREE.WebGLRenderer({{ antialias: true }})
        renderer.setPixelRatio(Math.min(2, window.devicePixelRatio || 1))
        renderer.setSize(window.innerWidth, window.innerHeight)
        document.body.appendChild(renderer.domElement)

        const scene = new THREE.Scene()
        scene.background = new THREE.Color(0x0b0f14)

        const camera = new THREE.PerspectiveCamera(60, window.innerWidth / window.innerHeight, 0.01, 200)

        const light = new THREE.DirectionalLight(0xffffff, 0.9)
        light.position.set(2, 3, 4)
        scene.add(light)
        scene.add(new THREE.AmbientLight(0xffffff, 0.35))

        const group = new THREE.Group()
        scene.add(group)

        const pts = items.map(it => it.pos3 || {{x:Math.random(), y:Math.random(), z:Math.random()}})
        let minx=1e9,maxx=-1e9,miny=1e9,maxy=-1e9,minz=1e9,maxz=-1e9
        for (const p of pts){{ minx=Math.min(minx,p.x); maxx=Math.max(maxx,p.x); miny=Math.min(miny,p.y); maxy=Math.max(maxy,p.y); minz=Math.min(minz,p.z); maxz=Math.max(maxz,p.z) }}
        const cx=(minx+maxx)/2, cy=(miny+maxy)/2, cz=(minz+maxz)/2
        const s = 2 / Math.max(1e-6, (maxx-minx), (maxy-miny), (maxz-minz))
        const xyz = pts.map(p => ({{ x:(p.x-cx)*s, y:(p.y-cy)*s, z:(p.z-cz)*s }}))

        const geom = new THREE.SphereGeometry(0.020, 14, 14)
        const meshes = []
        for (let i=0;i<items.length;i++){{
          const it = items[i]
          const m = new THREE.MeshPhongMaterial({{
            color: colorForFamily(it.family || ''),
            shininess: 30,
          }})
          const mesh = new THREE.Mesh(geom, m)
          mesh.position.set(xyz[i].x, xyz[i].y, xyz[i].z)
          mesh.userData = {{ idx: i }}
          group.add(mesh)
          meshes.push(mesh)
        }}

        // edges as one LineSegments (compact buffer, brighter + always visible)
        const seg = []
        for (const [i,j] of edges){{
          const a = xyz[i], b = xyz[j]
          if (!a || !b) continue
          seg.push(a.x, a.y, a.z, b.x, b.y, b.z)
        }}
        const edgeGeom = new THREE.BufferGeometry()
        edgeGeom.setAttribute('position', new THREE.Float32BufferAttribute(seg, 3))
        const edgeMat = new THREE.LineBasicMaterial({{
          color: 0xcfd8dc,
          transparent: true,
          opacity: 0.65,
          depthTest: false
        }})
        const edgeLines = new THREE.LineSegments(edgeGeom, edgeMat)
        edgeLines.renderOrder = 0
        scene.add(edgeLines)

        const state = {{ dragging: false, panning: false, x0:0, y0:0, theta: 0.6, phi: 1.0, r: 3.2, tx:0, ty:0, tz:0 }}
        const clamp = (x, a, b) => Math.max(a, Math.min(b, x))
        const updateCamera = () => {{
          state.phi = clamp(state.phi, 0.05, Math.PI - 0.05)
          const sinPhi = Math.sin(state.phi)
          const px = state.tx + state.r * sinPhi * Math.cos(state.theta)
          const py = state.ty + state.r * Math.cos(state.phi)
          const pz = state.tz + state.r * sinPhi * Math.sin(state.theta)
          camera.position.set(px, py, pz)
          camera.lookAt(state.tx, state.ty, state.tz)
        }}
        updateCamera()

        const onDown = (ev) => {{
          state.dragging = true
          state.panning = ev.shiftKey || ev.button === 2
          state.x0 = ev.clientX
          state.y0 = ev.clientY
        }}
        const onUp = () => {{ state.dragging = false; state.panning = false }}
        const onMove = (ev) => {{
          if (!state.dragging) return
          const dx = ev.clientX - state.x0
          const dy = ev.clientY - state.y0
          state.x0 = ev.clientX
          state.y0 = ev.clientY
          if (state.panning) {{
            const panScale = 0.0025 * state.r
            const dir = new THREE.Vector3()
            camera.getWorldDirection(dir)
            const right = new THREE.Vector3().crossVectors(dir, camera.up).normalize()
            const up = new THREE.Vector3().copy(camera.up).normalize()
            state.tx -= right.x * dx * panScale
            state.ty -= right.y * dx * panScale
            state.tz -= right.z * dx * panScale
            state.tx += up.x * dy * panScale
            state.ty += up.y * dy * panScale
            state.tz += up.z * dy * panScale
          }} else {{
            state.theta -= dx * 0.006
            state.phi -= dy * 0.006
          }}
          updateCamera()
        }}
        const onWheel = (ev) => {{
          ev.preventDefault()
          const factor = ev.deltaY > 0 ? 1.08 : 0.93
          state.r = clamp(state.r * factor, 0.5, 40)
          updateCamera()
        }}

        renderer.domElement.addEventListener('contextmenu', (e) => e.preventDefault())
        renderer.domElement.addEventListener('mousedown', onDown)
        window.addEventListener('mouseup', onUp)
        window.addEventListener('mousemove', onMove)
        renderer.domElement.addEventListener('wheel', onWheel, {{ passive:false }})

        const escapeHtml = (s) => String(s).replace(/[&<>\\"]/g, (c) => ({{'&':'&amp;','<':'&lt;','>':'&gt;','\\"':'&quot;'}}[c]||c))

        const showDetails = (it) => {{
          const loc = it.path ? `${{it.path}}:${{it.line||1}}` : ''
          details.style.display = 'block'
          details.innerHTML =
            `<h3>${{escapeHtml(it.name||'')}}</h3>` +
            `<div class=\"muted\">${{escapeHtml(it.kind||'')}} &middot; <code>${{escapeHtml(it.family||'')}}</code></div>` +
            (loc ? `<div style=\"margin-top:6px\"><code>${{escapeHtml(loc)}}</code></div>` : '') +
            (it.snippet ? `<div style=\"margin-top:10px\" class=\"muted\"><pre style=\"margin:0\">${{escapeHtml(it.snippet)}}</pre></div>` : '')
        }}

        if (!EMBED) {{
          const raycaster = new THREE.Raycaster()
          const mouse = new THREE.Vector2()
          let hover = null
          let selected = null
          const showTip = (sx, sy, it) => {{
            tip.style.display = 'block'
            tip.style.left = (sx + 12) + 'px'
            tip.style.top = (sy + 12) + 'px'
            tip.textContent = it.name
          }}
          const hideTip = () => {{ tip.style.display='none' }}
          const pick = (ev) => {{
            mouse.x = (ev.clientX / window.innerWidth) * 2 - 1
            mouse.y = -(ev.clientY / window.innerHeight) * 2 + 1
            raycaster.setFromCamera(mouse, camera)
            const hits = raycaster.intersectObjects(meshes)
            if (hits && hits.length) return hits[0].object.userData.idx
            return null
          }}
          renderer.domElement.addEventListener('mousemove', (ev) => {{
            const idx = pick(ev)
            hover = idx
            if (idx !== null) showTip(ev.clientX, ev.clientY, items[idx])
            else hideTip()
          }})
          renderer.domElement.addEventListener('click', (ev) => {{
            const idx = pick(ev)
            selected = idx
            if (idx !== null) showDetails(items[idx])
            else details.style.display = 'none'
          }})
        }}

        const onResize = () => {{
          camera.aspect = window.innerWidth / window.innerHeight
          camera.updateProjectionMatrix()
          renderer.setSize(window.innerWidth, window.innerHeight)
        }}
        window.addEventListener('resize', onResize)

        let last = performance.now()
        const animate = () => {{
          const now = performance.now()
          const dt = (now - last) / 1000
          last = now
          if (SPIN && !state.dragging) {{
            state.theta -= dt * 0.35
            updateCamera()
          }}
          renderer.render(scene, camera)
          requestAnimationFrame(animate)
        }}
        animate()
      }})()
    </script>
  </body>
</html>
"""


def generate_bounds_diagram(output: Path):
    """Generate SVG diagram showing AI bounds."""
    svg = '''<?xml version="1.0" encoding="UTF-8"?>
<svg xmlns="http://www.w3.org/2000/svg" width="600" height="300" viewBox="0 0 600 300">
  <defs>
    <linearGradient id="bg" x1="0%" y1="0%" x2="100%" y2="0%">
      <stop offset="0%" style="stop-color:#e8f4f8"/>
      <stop offset="100%" style="stop-color:#d0e8f0"/>
    </linearGradient>
  </defs>

  <!-- Background -->
  <rect width="600" height="300" fill="url(#bg)" rx="10"/>

  <!-- Title -->
  <text x="300" y="35" text-anchor="middle" font-family="Arial" font-size="18" font-weight="bold" fill="#2c3e50">
    Assembly Index Bounds
  </text>

  <!-- Axis line -->
  <line x1="50" y1="150" x2="550" y2="150" stroke="#34495e" stroke-width="2"/>

  <!-- Lower bound marker -->
  <rect x="100" y="130" width="120" height="40" fill="#3498db" rx="5"/>
  <text x="160" y="155" text-anchor="middle" font-family="Arial" font-size="12" fill="white">
    log₂(size)
  </text>
  <text x="160" y="190" text-anchor="middle" font-family="Arial" font-size="10" fill="#7f8c8d">
    Lower Bound
  </text>

  <!-- AI region -->
  <rect x="230" y="120" width="140" height="60" fill="#2ecc71" rx="5"/>
  <text x="300" y="145" text-anchor="middle" font-family="Arial" font-size="14" font-weight="bold" fill="white">
    Assembly
  </text>
  <text x="300" y="165" text-anchor="middle" font-family="Arial" font-size="14" font-weight="bold" fill="white">
    Index (AI)
  </text>

  <!-- Upper bound marker -->
  <rect x="380" y="130" width="120" height="40" fill="#e74c3c" rx="5"/>
  <text x="440" y="155" text-anchor="middle" font-family="Arial" font-size="12" fill="white">
    size - 1
  </text>
  <text x="440" y="190" text-anchor="middle" font-family="Arial" font-size="10" fill="#7f8c8d">
    Upper Bound
  </text>

  <!-- Arrows -->
  <path d="M 220 150 L 235 140 L 235 160 Z" fill="#34495e"/>
  <path d="M 380 150 L 365 140 L 365 160 Z" fill="#34495e"/>

  <!-- Legend -->
  <text x="300" y="240" text-anchor="middle" font-family="Arial" font-size="11" fill="#34495e">
    log₂(size) ≤ AI ≤ size - 1
  </text>
  <text x="300" y="260" text-anchor="middle" font-family="Arial" font-size="10" fill="#7f8c8d">
    Proved in AssemblyBounds.lean
  </text>

  <!-- Reuse note -->
  <text x="300" y="280" text-anchor="middle" font-family="Arial" font-size="9" fill="#95a5a6">
    AI = dagJoinCount (with intermediate reuse)
  </text>
</svg>'''

    with open(output, "w") as f:
        f.write(svg)

    print(f"Generated {output}")


def main():
    parser = argparse.ArgumentParser(description="Generate Assembly Theory visualizations")
    parser.add_argument("--lean-dir", required=True, help="Path to HeytingLean directory")
    parser.add_argument("--out-dir", required=True, help="Output directory")
    args = parser.parse_args()

    lean_dir = Path(args.lean_dir)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Generate graph JSON
    graph_json = out_dir / "assembly_graph.json"
    graph = generate_graph_json(lean_dir / "ATheory", graph_json)

    # Generate DOT file
    dot_file = out_dir / "dependency_graph.dot"
    generate_dependency_dot(graph, dot_file)

    # Generate UMAP visualizations
    generate_umap_html(
        graph,
        out_dir / "assembly_2d.html",
        out_dir / "assembly_3d.html"
    )

    # Generate bounds diagram
    generate_bounds_diagram(out_dir / "bounds_diagram.svg")

    print("\nVisualization generation complete!")
    print(f"Files in {out_dir}:")
    for f in out_dir.iterdir():
        print(f"  - {f.name}")


if __name__ == "__main__":
    main()

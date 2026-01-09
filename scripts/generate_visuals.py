#!/usr/bin/env python3
"""
Generate visualizations for Assembly Theory formalization.

Creates:
- Module dependency graph (SVG)
- Declaration UMAP 2D/3D (HTML)
- Assembly index bounds diagram (SVG)
"""

import argparse
import json
import os
import re
import sys
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

try:
    import plotly.express as px
    import plotly.graph_objects as go
    HAS_PLOTLY = True
except ImportError:
    HAS_PLOTLY = False


def extract_declarations(lean_dir: Path) -> list:
    """Extract declarations from Lean files."""
    decls = []

    for lean_file in lean_dir.rglob("*.lean"):
        rel_path = lean_file.relative_to(lean_dir)
        module = str(rel_path).replace("/", ".").replace(".lean", "")

        with open(lean_file, "r") as f:
            content = f.read()

        # Extract declarations
        patterns = [
            (r"theorem\s+(\w+)", "theorem"),
            (r"lemma\s+(\w+)", "lemma"),
            (r"def\s+(\w+)", "def"),
            (r"structure\s+(\w+)", "structure"),
            (r"inductive\s+(\w+)", "inductive"),
            (r"class\s+(\w+)", "class"),
            (r"instance\s+(\w+)", "instance"),
        ]

        for pattern, kind in patterns:
            for match in re.finditer(pattern, content):
                name = match.group(1)
                decls.append({
                    "name": f"{module}.{name}",
                    "kind": kind,
                    "module": module,
                    "file": str(rel_path),
                })

    return decls


def extract_imports(lean_dir: Path) -> list:
    """Extract import edges between modules."""
    edges = []

    for lean_file in lean_dir.rglob("*.lean"):
        rel_path = lean_file.relative_to(lean_dir)
        module = str(rel_path).replace("/", ".").replace(".lean", "")

        with open(lean_file, "r") as f:
            content = f.read()

        for match in re.finditer(r"import\s+(HeytingLean\.\S+)", content):
            target = match.group(1)
            edges.append({"source": target, "target": module})

    return edges


def generate_graph_json(lean_dir: Path, output: Path):
    """Generate graph JSON for visualization."""
    decls = extract_declarations(lean_dir)
    edges = extract_imports(lean_dir)

    # Unique modules
    modules = list(set(d["module"] for d in decls))

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


def generate_umap_html(graph: dict, output_2d: Path, output_3d: Path):
    """Generate UMAP visualizations."""
    if not (HAS_NUMPY and HAS_UMAP and HAS_PLOTLY):
        print("Skipping UMAP: requires numpy, umap-learn, plotly")
        return

    decls = graph["declarations"]
    if len(decls) < 5:
        print("Not enough declarations for UMAP")
        return

    # Build feature vectors
    # Features: kind (one-hot), name length, module depth
    kinds = ["theorem", "lemma", "def", "structure", "inductive", "class", "instance"]
    kind_to_idx = {k: i for i, k in enumerate(kinds)}

    X = []
    labels = []
    colors = []

    for d in decls:
        vec = [0] * len(kinds)
        if d["kind"] in kind_to_idx:
            vec[kind_to_idx[d["kind"]]] = 1
        vec.append(len(d["name"]))
        vec.append(d["module"].count("."))
        X.append(vec)
        labels.append(d["name"])
        colors.append(d["kind"])

    X = np.array(X, dtype=float)

    # 2D UMAP
    reducer_2d = umap.UMAP(n_components=2, random_state=42, n_neighbors=min(15, len(X)-1))
    Y2 = reducer_2d.fit_transform(X)

    fig_2d = px.scatter(
        x=Y2[:, 0], y=Y2[:, 1],
        hover_name=labels,
        color=colors,
        title="Assembly Theory Declarations (2D UMAP)",
        width=900, height=700
    )
    fig_2d.update_traces(marker=dict(size=8))
    fig_2d.write_html(output_2d)
    print(f"Generated {output_2d}")

    # 3D UMAP
    if len(X) >= 10:
        reducer_3d = umap.UMAP(n_components=3, random_state=42, n_neighbors=min(15, len(X)-1))
        Y3 = reducer_3d.fit_transform(X)

        fig_3d = px.scatter_3d(
            x=Y3[:, 0], y=Y3[:, 1], z=Y3[:, 2],
            hover_name=labels,
            color=colors,
            title="Assembly Theory Declarations (3D UMAP)",
            width=900, height=700
        )
        fig_3d.update_traces(marker=dict(size=4))
        fig_3d.write_html(output_3d)
        print(f"Generated {output_3d}")


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

#!/usr/bin/env python3
"""
Generate high-quality UMAP preview SVGs for Assembly Theory formalization.
Matches the style of Sky_PaperPack with animated 3D rotation and kNN edges.
"""

import json
import math
import os
import sys
from pathlib import Path

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False
    print("Warning: numpy not installed, using fallback", file=sys.stderr)

try:
    import umap
    HAS_UMAP = True
except ImportError:
    HAS_UMAP = False
    print("Warning: umap-learn not installed", file=sys.stderr)


def extract_declarations(lean_dir: Path) -> list:
    """Extract declarations from Lean files."""
    import re
    decls = []

    for lean_file in lean_dir.rglob("*.lean"):
        rel_path = lean_file.relative_to(lean_dir.parent)
        module = str(rel_path).replace("/", ".").replace(".lean", "")

        # Determine module family for coloring
        if "Paper" in module:
            if "Bound" in module:
                family = "Bounds"
            elif "Index" in module:
                family = "Index"
            elif "Path" in module:
                family = "Path"
            elif "Molecular" in module:
                family = "Molecular"
            elif "Hyper" in module:
                family = "Hypergraph"
            elif "Quotient" in module:
                family = "Quotient"
            else:
                family = "Space"
        elif "Core" in module:
            family = "Core"
        elif "Selection" in module or "Copy" in module:
            family = "Selection"
        else:
            family = "Other"

        with open(lean_file, "r") as f:
            content = f.read()

        patterns = [
            (r"theorem\s+(\w+)", "theorem"),
            (r"lemma\s+(\w+)", "lemma"),
            (r"def\s+(\w+)", "def"),
            (r"structure\s+(\w+)", "structure"),
            (r"inductive\s+(\w+)", "inductive"),
        ]

        for pattern, kind in patterns:
            for match in re.finditer(pattern, content):
                name = match.group(1)
                # Skip private/auxiliary names
                if name.startswith("_") or name in ["mk", "rec", "casesOn"]:
                    continue
                decls.append({
                    "name": f"{module}.{name}",
                    "short": name,
                    "kind": kind,
                    "module": module,
                    "family": family,
                })

    return decls


# Module family colors (HSL format for consistency with Sky style)
FAMILY_COLORS = {
    "Core": ("128", "70%", "58%"),      # Green
    "Space": ("220", "70%", "58%"),     # Blue
    "Path": ("180", "70%", "58%"),      # Cyan
    "Index": ("285", "70%", "58%"),     # Purple
    "Bounds": ("49", "70%", "58%"),     # Yellow
    "Quotient": ("345", "70%", "58%"),  # Pink
    "Molecular": ("10", "70%", "58%"),  # Red-Orange
    "Hypergraph": ("33", "70%", "58%"), # Orange
    "Selection": ("251", "70%", "58%"), # Violet
    "Other": ("0", "0%", "58%"),        # Gray
}


def generate_2d_preview(decls, coords, out_path):
    """Generate 2D UMAP preview SVG with kNN edges."""
    width, height = 1500, 900
    margin = 50
    plot_width = 1090
    plot_height = 800

    # Normalize coordinates
    if len(coords) > 0:
        x_min, x_max = coords[:, 0].min(), coords[:, 0].max()
        y_min, y_max = coords[:, 1].min(), coords[:, 1].max()
        x_range = max(x_max - x_min, 0.001)
        y_range = max(y_max - y_min, 0.001)

        norm_coords = []
        for i, (x, y) in enumerate(coords):
            nx = margin + 20 + (x - x_min) / x_range * (plot_width - 40)
            ny = margin + 20 + (y - y_min) / y_range * (plot_height - 40)
            norm_coords.append((nx, ny))
    else:
        norm_coords = [(width/2, height/2) for _ in decls]

    # Count families
    family_counts = {}
    for d in decls:
        f = d["family"]
        family_counts[f] = family_counts.get(f, 0) + 1

    svg_lines = [
        '<?xml version="1.0" encoding="utf-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="UMAP preview">',
        f'<rect x="0" y="0" width="{width}" height="{height}" fill="#0b0f14"/>',
        f'<text x="{margin}" y="32" fill="#ffffff" font-size="20" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">UMAP 2D — Assembly Theory proof/declaration map</text>',
        f'<text x="{margin}" y="48" fill="#b8c7d9" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Points: declarations ({len(decls)}) • Colors: module family • Edges: kNN similarity links</text>',
        f'<rect x="{margin}" y="{margin}" width="{plot_width}" height="{plot_height}" fill="#0f1721" stroke="#1c2a3a" stroke-width="1"/>',
    ]

    # Add kNN edges (connect each point to 3 nearest neighbors)
    if len(norm_coords) > 3:
        for i, (x1, y1) in enumerate(norm_coords):
            distances = []
            for j, (x2, y2) in enumerate(norm_coords):
                if i != j:
                    d = math.sqrt((x2-x1)**2 + (y2-y1)**2)
                    distances.append((d, j))
            distances.sort()
            for _, j in distances[:3]:
                x2, y2 = norm_coords[j]
                svg_lines.append(
                    f'<line x1="{x1:.2f}" y1="{y1:.2f}" x2="{x2:.2f}" y2="{y2:.2f}" '
                    f'stroke="#90a4ae" stroke-opacity="0.30" stroke-width="1.25"/>'
                )

    # Add points
    for i, d in enumerate(decls):
        x, y = norm_coords[i]
        h, s, l = FAMILY_COLORS.get(d["family"], ("0", "0%", "58%"))
        fill = f"hsl({h} {s} {l})"
        svg_lines.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="4" fill="{fill}" stroke="#0b0f14" stroke-width="1">')
        svg_lines.append(f'  <title>{d["name"]}</title>')
        svg_lines.append('</circle>')

    # Add legend
    legend_x = plot_width + margin + 20
    legend_y = 68
    for family, count in sorted(family_counts.items(), key=lambda x: -x[1]):
        h, s, l = FAMILY_COLORS.get(family, ("0", "0%", "58%"))
        fill = f"hsl({h} {s} {l})"
        svg_lines.append(f'<rect x="{legend_x}" y="{legend_y}" width="10" height="10" fill="{fill}" stroke="hsl({h} 70% 32%)" stroke-width="1"/>')
        svg_lines.append(f'<text x="{legend_x + 16}" y="{legend_y + 9}" fill="#e6eef7" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">{family} <tspan fill="#b8c7d9">({count})</tspan></text>')
        legend_y += 16

    svg_lines.append('</svg>')

    with open(out_path, 'w') as f:
        f.write('\n'.join(svg_lines))

    print(f"Generated {out_path}")


def generate_3d_animated_preview(decls, coords_3d, out_path):
    """Generate animated 3D UMAP preview SVG with rotation."""
    width, height = 1500, 900
    margin = 50
    plot_width = 1400
    plot_height = 800

    # Normalize 3D coordinates
    if len(coords_3d) > 0:
        for dim in range(3):
            d_min, d_max = coords_3d[:, dim].min(), coords_3d[:, dim].max()
            d_range = max(d_max - d_min, 0.001)
            coords_3d[:, dim] = (coords_3d[:, dim] - d_min) / d_range - 0.5

    # Count families
    family_counts = {}
    for d in decls:
        f = d["family"]
        family_counts[f] = family_counts.get(f, 0) + 1

    svg_lines = [
        '<?xml version="1.0" encoding="utf-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" role="img" aria-label="UMAP preview">',
        f'<rect x="0" y="0" width="{width}" height="{height}" fill="#0b0f14"/>',
        f'<text x="{margin}" y="32" fill="#ffffff" font-size="20" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">UMAP 3D — Assembly Theory proof/declaration map (animated)</text>',
        f'<text x="{margin}" y="48" fill="#b8c7d9" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">Rotation preview of 3D embedding (WebGL viewer available on GitHub Pages)</text>',
        f'<rect x="{margin}" y="{margin}" width="{plot_width}" height="{plot_height}" fill="#0f1721" stroke="#1c2a3a" stroke-width="1"/>',
    ]

    # Add legend
    legend_x = 68
    legend_y = 68
    for family, count in sorted(family_counts.items(), key=lambda x: -x[1]):
        h, s, l = FAMILY_COLORS.get(family, ("0", "0%", "58%"))
        fill = f"hsl({h} {s} {l})"
        svg_lines.append(f'<rect x="{legend_x}" y="{legend_y}" width="10" height="10" fill="{fill}" stroke="hsl({h} 70% 32%)" stroke-width="1"/>')
        svg_lines.append(f'<text x="{legend_x + 16}" y="{legend_y + 9}" fill="#e6eef7" font-size="12" font-family="ui-sans-serif,system-ui,Segoe UI,Roboto,Helvetica,Arial">{family} <tspan fill="#b8c7d9">({count})</tspan></text>')
        legend_y += 16

    # Generate animation frames for rotation
    num_frames = 72  # One frame every 5 degrees
    duration = 14  # seconds
    center_x = margin + plot_width / 2
    center_y = margin + plot_height / 2
    scale = min(plot_width, plot_height) * 0.35

    # Precompute projected (x,y) positions for each node at each frame.
    n = len(decls)
    pxs = [["0"] * (num_frames + 1) for _ in range(n)]
    pys = [["0"] * (num_frames + 1) for _ in range(n)]

    for frame in range(num_frames):
        angle = 2 * math.pi * frame / num_frames
        ca = math.cos(angle)
        sa = math.sin(angle)

        for i in range(n):
            if len(coords_3d) > i:
                x, y, z = coords_3d[i]
            else:
                x, y, z = 0, 0, 0

            # Rotate around Y axis
            rx = x * ca + z * sa
            rz = -x * sa + z * ca
            # Project to 2D
            px = center_x + rx * scale
            py = center_y + y * scale - rz * scale * 0.3  # slight perspective
            pxs[i][frame] = f"{px:.2f}"
            pys[i][frame] = f"{py:.2f}"

    # loop back
    for i in range(n):
        pxs[i][num_frames] = pxs[i][0]
        pys[i][num_frames] = pys[i][0]

    # Add kNN edges in 3D space (keep this light for README render performance)
    if HAS_NUMPY and len(coords_3d) >= 5:
        k_nn = 2
        edges = set()
        pts = coords_3d
        for i in range(n):
            d2 = np.sum((pts - pts[i]) ** 2, axis=1)
            d2[i] = float("inf")
            nn = np.argsort(d2)[:k_nn]
            for j in nn:
                a, b = (i, int(j)) if i < int(j) else (int(j), i)
                edges.add((a, b))

        svg_lines.append('<g stroke="#90a4ae" stroke-opacity="0.22" stroke-width="1">')
        for a, b in sorted(edges):
            svg_lines.append(f'<line x1="{pxs[a][0]}" y1="{pys[a][0]}" x2="{pxs[b][0]}" y2="{pys[b][0]}">')
            svg_lines.append(f'  <animate attributeName="x1" dur="{duration}s" repeatCount="indefinite" values="{";".join(pxs[a])}"/>')
            svg_lines.append(f'  <animate attributeName="y1" dur="{duration}s" repeatCount="indefinite" values="{";".join(pys[a])}"/>')
            svg_lines.append(f'  <animate attributeName="x2" dur="{duration}s" repeatCount="indefinite" values="{";".join(pxs[b])}"/>')
            svg_lines.append(f'  <animate attributeName="y2" dur="{duration}s" repeatCount="indefinite" values="{";".join(pys[b])}"/>')
            svg_lines.append('</line>')
        svg_lines.append('</g>')

    for i, d in enumerate(decls):
        h, s, l = FAMILY_COLORS.get(d["family"], ("0", "0%", "58%"))
        fill = f"hsl({h} {s} {l})"

        svg_lines.append(f'<circle r="4" fill="{fill}" stroke="#0b0f14" stroke-width="1">')
        svg_lines.append(f'  <title>{d["name"]}</title>')
        svg_lines.append(f'  <animate attributeName="cx" dur="{duration}s" repeatCount="indefinite" values="{";".join(pxs[i])}"/>')
        svg_lines.append(f'  <animate attributeName="cy" dur="{duration}s" repeatCount="indefinite" values="{";".join(pys[i])}"/>')
        svg_lines.append('</circle>')

    svg_lines.append('</svg>')

    with open(out_path, 'w') as f:
        f.write('\n'.join(svg_lines))

    print(f"Generated {out_path}")


def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument("--lean-dir", required=True)
    parser.add_argument("--out-dir", required=True)
    args = parser.parse_args()

    lean_dir = Path(args.lean_dir)
    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    # Extract declarations
    decls = extract_declarations(lean_dir)
    print(f"Found {len(decls)} declarations")

    if not decls:
        print("No declarations found!")
        return

    # Generate features and UMAP coordinates
    if HAS_NUMPY and HAS_UMAP and len(decls) >= 5:
        # Build feature vectors
        kinds = ["theorem", "lemma", "def", "structure", "inductive"]
        kind_to_idx = {k: i for i, k in enumerate(kinds)}

        X = []
        for d in decls:
            vec = [0] * len(kinds)
            if d["kind"] in kind_to_idx:
                vec[kind_to_idx[d["kind"]]] = 1
            vec.append(len(d["name"]))
            vec.append(d["module"].count("."))
            vec.append(len(d.get("family", "")))
            X.append(vec)

        X = np.array(X, dtype=float)

        # 2D UMAP
        n_neighbors = min(15, len(X) - 1)
        reducer_2d = umap.UMAP(n_components=2, random_state=42, n_neighbors=n_neighbors)
        coords_2d = reducer_2d.fit_transform(X)

        # 3D UMAP
        reducer_3d = umap.UMAP(n_components=3, random_state=42, n_neighbors=n_neighbors)
        coords_3d = reducer_3d.fit_transform(X)
    else:
        # Fallback: random layout
        import random
        random.seed(42)
        coords_2d = np.array([[random.random(), random.random()] for _ in decls])
        coords_3d = np.array([[random.random()-0.5, random.random()-0.5, random.random()-0.5] for _ in decls])

    # Generate SVGs
    generate_2d_preview(decls, coords_2d, out_dir / "assembly_2d_preview.svg")
    generate_3d_animated_preview(decls, coords_3d, out_dir / "assembly_3d_preview_animated.svg")

    print("Done!")


if __name__ == "__main__":
    main()

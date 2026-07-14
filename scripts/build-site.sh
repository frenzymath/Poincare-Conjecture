#!/usr/bin/env bash
# Build the public reference site into docs/ (GitHub Pages source).
# Regenerates each project's blueprint dashboard from its blueprint (+ Lean, where
# present), then the landing index. Output docs/ is committed and served by Pages
# (Settings → Pages → Deploy from branch: main /docs). Needs `hgraph` on PATH.
#
# Usage: bash scripts/build-site.sh
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$HERE"
command -v hgraph >/dev/null || { echo "error: hgraph not on PATH"; exit 1; }

PROJECTS=(DoCarmo Petersen MorganTian Lee Hatcher Evans)
declare -A TITLE=(
  [DoCarmo]="Riemannian Geometry — do Carmo (OpenGALib)"
  [Petersen]="Riemannian Geometry — Petersen"
  [MorganTian]="Ricci Flow & the Poincaré Conjecture — Morgan–Tian"
  [Lee]="Introduction to Riemannian Manifolds — Lee"
  [Hatcher]="Algebraic Topology — Hatcher"
  [Evans]="Partial Differential Equations — Evans"
)

rm -rf docs; mkdir -p docs
for p in "${PROJECTS[@]}"; do
  echo ">> $p"
  ( cd "$p"
    rm -rf hgraph/nodes hgraph/edges
    hgraph sync
    hgraph dashboard --out dashboard.html --title "${TITLE[$p]}" --self-contained --home ../ --no-katex-check
  )
  mkdir -p "docs/$p"
  cp "$p/dashboard.html" "docs/$p/dashboard.html"
done

hgraph site --manifest site.yaml --out docs/index.html --overview site/overview.html
touch docs/.nojekyll   # tell Pages not to run Jekyll on the static output
echo "built docs/ ($(du -sh docs | cut -f1))"

#!/usr/bin/env bash
# Build the public reference site into docs/ (GitHub Pages source).
# Re-syncs each project's graph from its blueprint (+ Lean, where present), then
# builds the whole site in one shot. Output docs/ is committed and served by
# Pages (Settings → Pages → Deploy from branch: main /docs). Needs `hgraph` on PATH.
#
# Usage: bash scripts/build-site.sh
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$HERE"
command -v hgraph >/dev/null || { echo "error: hgraph not on PATH"; exit 1; }

PROJECTS=(DoCarmo Petersen MorganTian Lee Hatcher Evans)

rm -rf docs; mkdir -p docs

# 1. Re-derive each project's graph from its sources. Titles live in site.yaml
#    now, not here — `hgraph sync` only needs the project's hgraph/config.yaml.
for p in "${PROJECTS[@]}"; do
  echo ">> $p"
  ( cd "$p"; rm -rf hgraph/nodes hgraph/edges; hgraph sync )
done

# 2. The whole site, one command. hgraph no longer builds a per-project
#    dashboard.html: it emits one React app that hash-routes to #/<root> and
#    fetches docs/<root>/data.json, and `hgraph site` writes the landing page,
#    the assets/ bundle and every project's data.json under docs/ itself.
python3 scripts/gen_overview.py
hgraph site --manifest site.yaml --out docs/index.html --overview site/overview.html

# 3. Keep the old per-project URLs alive: docs/<P>/dashboard.html used to be the
#    real artifact and may be linked to from outside. Point them at the route
#    that replaced them.
for p in "${PROJECTS[@]}"; do
  cat > "docs/$p/dashboard.html" <<EOF
<!doctype html>
<meta charset="utf-8">
<title>Moved — $p</title>
<meta http-equiv="refresh" content="0; url=../#/$p">
<link rel="canonical" href="../#/$p">
<p>This dashboard now lives at <a href="../#/$p">../#/$p</a>.</p>
EOF
done

touch docs/.nojekyll   # tell Pages not to run Jekyll on the static output
echo "built docs/ ($(du -sh docs | cut -f1))"

# Contributing

`PoincareConjecture/` contains the primary proof, organized by mathematical
dependency. `references/` holds book and article blueprints and retained Lean
developments. `references/shared/` contains their common infrastructure.
Keep changes focused and
preserve the pinned Lean toolchains and mathlib revisions.

## Lean checks

Automatic CI does **not** compile Lean. It scans `PoincareConjecture/`, fails on
source occurrences of `sorry`, `sorryAx`, `admit` or `axiom`, and publishes a directory
statistics table in the Actions summary. JSON and per-file CSV are available
as a seven-day artifact. Comments and string literals do not count as admissions.
The scanner is lexical, not a Lean parser or transitive proof audit.

Run the same check locally:

```bash
pip install -r requirements-site.txt
python scripts/lean_stats.py PoincareConjecture --exclude references --exclude contracts --exclude comparator/Challenge.lean --output .verification/statistics --check
```

Statistics distinguish physical LOC, nonblank LOC, nonblank LOC after removing
docstrings, and nonblank LOC after removing all comments. Both declaration
docstrings (`/--`) and module documentation (`/-!`) are removed in the docstring
column. Dependencies under `.lake/` are excluded.

Build changed packages locally before publishing proof edits:

```bash
cd PoincareConjecture
lake exe cache get
lake build
```

`scripts/validate-lean-changes.sh origin/main` runs dependency-aware local
builds. The optional repository hooks (`git config core.hooksPath .githooks`)
also run these builds on Lean pushes. This local policy is independent of CI.
The **Manual Lean build** Actions workflow retains the full package matrix
for explicit use; it does not run on pushes or PRs and stores no Lake caches.

See [verification.md](site/verification.md) for comparator evidence and release
verification. A successful source scan does not imply a successful Lean build.

## Blueprints

Give statements stable labels, record dependencies with `\uses{...}`, and
link declarations with `\lean{...}`. Preserve precise source citations.
Only add `\leanok` after checking the corresponding declaration and statement.

## Website

All graph records are temporary build output. No `hgraph/` directory belongs
in Git. The authored inputs are:

- `config.yaml`: workspace manifest and project order.
- `site/projects/<project-root>/config.yaml`: source paths and project settings.
- `site/reviews/<project-root>/<node-id>/`: authored comments and review verdicts.
- Blueprints, Lean sources and `site/` assets.

The Pages workflow installs the pinned hgraph dependency, stages source links
and copies of authored feedback in temporary storage, generates the graph and
site, then deletes that staging area. It deploys `_site/` using a Pages artifact.
No graph cache is required for correctness, and ordinary contributors need not
install or run hgraph.

For a local preview, put large temporary output on workspace disk:

```bash
mkdir -p "$HOME/.horizon/development-tmp/site"
export TMPDIR="$HOME/.horizon/development-tmp/site"
pip install -r requirements-site.txt
python scripts/build_site.py --out _site
python3 -m http.server 8000 --directory _site
```

The same script runs in CI. Generated graphs and `_site/` are not committed.
Review attachment names retain their stable node identifiers; editing an
authored attachment under `site/reviews/` updates the deployed feedback on the
next site build. Temporary generated data must not be used to store new reviews.

The Proof Map's authored data lives in `site/proof-map/src/proof-data.js` and
its figures in `site/proof-map/public/figures/`.
The site build includes `site/legacy-routes.js` to preserve bookmarks from
before the reference-directory rename.

## Pull requests

Explain the mathematical or technical change, validation and remaining
assumptions. CI reports source statistics; local builds and comparator results
must be identified separately. Contributions use the repository's Apache 2.0
license.

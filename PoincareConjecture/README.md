# Poincare-Conjecture

This is the repository's complete Lean 4 formalization of the Poincare conjecture.
Its blueprint follows
the dependency architecture of the Poincare conjecture rather than reproducing
the chapter order of a particular source.

The projects under `../references/` collect book and article blueprints with
their mathematical dependency graphs. They provide blueprint-only references;
completing those books is not an objective of this formalization.

## Status

The [subject-organized proof library](IMPORT.md) has passed a full Lean build
and endpoint axiom audits at `516badd1`. Comparator accepted both public targets
at `1876d7dc`, checked by Nanoda and Lean's default kernel. The recursive axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
See the [verification evidence](references/ricci-flow/mapher/integration-verification/README.md)
for the exact revisions, verifier configuration, and logs, and the
[FrenzyMath announcement](https://frenzymath.com/news/poincare-formalization/)
for the project's background.

The separately authored Morgan--Tian blueprint is a reading guide. Its readiness
labels and declaration links still need reconciliation with the completed Lean
library; they do not describe the verification status of the proof.

## Build

```bash
lake exe cache get
lake build
```

Graph synchronization and local website preview are documented in the root
`CONTRIBUTING.md`.

## Blueprint map

The project-local `Blueprint map` tab is generated from the live hgraph nodes
and `uses` edges. Regenerate it after changing the blueprint or synchronizing
the graph:

```bash
python3 blueprint/tools/build_blueprint_map.py
```

The generated `blueprint/blueprint-map-tab.html` is loaded only by this
project's blueprint tab; the built-in dependency graph remains the canonical
hgraph view. The map is a collapsed reader view of the same live semantic DAG,
not a smaller proof graph.

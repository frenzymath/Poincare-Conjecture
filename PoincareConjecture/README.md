# Poincare-Conjecture

This is the repository's primary formalization project. Its blueprint follows
the dependency architecture of the Poincare conjecture rather than reproducing
the chapter order of a particular source.

The projects under `../formalized-sources/` remain faithful reference
formalizations of books and articles. Results from those projects may inform
or support this development, but they do not define its organization.

## Status

The evolving six-chapter Morgan--Tian Blueprint currently contains 279
mathematical declarations and 854 direct prerequisite edges. The live structural
audit reports one terminal sink (`thm:poincare-conjecture`), all 279 declarations
reach it, and no cycles, forward edges, duplicate edges, unresolved references,
or isolated declarations. Counts are descriptive consequences of the current
mathematical decomposition; historical snapshots and generated audit dossiers
are not the deliverable for this task. The shared hgraph retains stale
historical Poincare records from superseded source revisions; they are excluded
from the active graph and are not live prerequisites.

The route is now a mathematically closed, source-backed candidate Blueprint
pending human expert review. Source comparison repaired the surgery spacetime
and cutoff domain, canonical-neighborhood continuation, the corrected Appendix
A.19/A.20/A.21/A.24 topology interfaces, explicit relative fiber and cap
incidence classification, surgery reconstruction and Corollary 15.4, and the
finite-net loop-width argument. The Hempel, Plateau--Morrey,
Douglas--Hildebrandt, and parabolic-flow results are retained as explicit
imported contracts with their exact registered Morgan--Tian/White/Topping/
Perelman locations and all hypotheses consumed by later nodes; their classical
source proofs remain part of the human review boundary. Live nodes remain
marked `\notready`: this project makes no claim of Lean formalization or expert
approval.

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

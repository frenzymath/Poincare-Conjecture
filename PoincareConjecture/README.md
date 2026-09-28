# Poincare-Conjecture

This is the repository's primary formalization project. Its blueprint follows
the dependency architecture of the Poincare conjecture rather than reproducing
the chapter order of a particular source.

The projects under `../references/` collect book and article blueprints with
their earlier Lean developments retained. They provide mathematical references;
completing those books is not an objective of this formalization.

## Status

The evolving six-chapter, seven-stage Morgan--Tian Blueprint currently contains 280
mathematical declarations and 856 direct prerequisite edges. The live structural
audit reports one terminal sink (`thm:poincare-conjecture`), all 280 declarations
reach it, and no cycles, forward edges, duplicate edges, unresolved references,
or isolated declarations. Counts are descriptive consequences of the current
mathematical decomposition; historical snapshots and generated audit dossiers
are not the deliverable for this task. The shared hgraph retains stale
historical Poincare records from superseded source revisions; they are excluded
from the active graph and are not live prerequisites.

The smooth route is a source-backed candidate Blueprint
pending human expert review. Source comparison repaired the surgery spacetime
and cutoff domain, canonical-neighborhood continuation, the corrected Appendix
A.19/A.20/A.21/A.24 topology interfaces, explicit relative fiber and cap
incidence classification, surgery reconstruction and Corollary 15.4, and the
finite-net loop-width argument. The Hempel, Plateau--Morrey,
Douglas--Hildebrandt, and parabolic-flow results are retained as explicit
imported contracts with their exact registered Morgan--Tian/White/Topping/
Perelman locations and all hypotheses consumed by later nodes; their classical
source proofs remain part of the human review boundary. Three analytic nodes
are now Lean-checked: forward-Dini comparison, its finite-downward-jump
extension (with the terminal endpoint controlled), and the scalar width
lifetime bound. Three topological endgame nodes are now checked as well:
trivial free products have trivial factors, both sphere-bundle models have
infinite cyclic fundamental group, and a simply connected spherical space
form is diffeomorphic to the three-sphere. The last result includes proofs
of smooth quotient charts and smooth local inverse branches, not an assumed
smooth quotient projection. The mapping-torus calculation uses a genuine
integer orbit quotient and identifies the identity model with the actual
product of the two-sphere and unit circle.
The simply-connected orientability step is now checked as well: the actual
tangent transition determinants construct a two-sheeted cover, and lifting
the identity yields continuous local frame changes with positive transition
determinants. No orientation cover or global orientation is assumed.

Their proofs, regression tests, and namespace-wide axiom audit are built by
`lake build`; see [comparison validation](COMPARISON_VALIDATION.md) and
[topological endgame validation](TOPOLOGY_VALIDATION.md), and
[orientability validation](ORIENTABILITY_VALIDATION.md).
The remaining nodes stay marked `\notready`. In particular, the geometric
finite-extinction theorem and the Poincare theorem are not Lean-formalized by
this contribution, and no independent expert approval is claimed.

The exact full topological target is
`PoincareConjecture.TopologicalPoincareStatement`. It does not assume a smooth
atlas, positive Ricci curvature, a surgery flow, or a spherical presentation.
The definition records the proposition only. The present smooth blueprint
additionally needs the three-dimensional smoothability bridge before it
proves that topological statement; this bridge is not hidden in the target.

Chapter 3 is organized into two implementation stages: Stage 3, **Blow-Up
Limits, Kappa-Solutions, and Canonical Neighborhoods**, and Stage 4,
**Continuation of Controlled Ricci Flow with Surgery**.  The handoff is before
the first-failure extension argument; the remaining chapters retain their
existing order and roles.

## Build

```bash
lake exe cache get
lake build
```

The primary package now reuses the Hatcher reference project's checked sphere
fundamental-group proof at a pinned source commit and subdirectory. Both the
Lean and Mathlib versions remain unchanged. One existing style warning in
`HatcherLib.Ch1.Circle` recommends writing a proposition-valued `def` as a
`theorem`; the reference source is not changed merely to hide that warning.
This does not affect kernel checking or the transitive axiom audit.

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

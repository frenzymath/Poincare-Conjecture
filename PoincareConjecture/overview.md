# The Poincare Conjecture

This project is building a formalization-oriented proof architecture for the
statement that every closed smooth simply connected three-manifold is
diffeomorphic to the three-sphere. Its six chapters and seven implementation
stages follow logical role rather than the chapter order of Morgan--Tian or
another single source.

## Current status

- **Semantic graph:** the live six-chapter, seven-stage route has 279 declarations and 854
  direct prerequisite edges. Every declaration reaches the unique terminal
  theorem; the audit finds no cycle, forward edge, duplicate edge, unresolved
  reference, or isolated node.
- **Mathematics:** mathematically closed, source-backed candidate Blueprint
  pending human expert review. The source comparison pass repaired the
  Appendix A.19/A.20/A.21/A.24 polarity and relative-boundary interfaces,
  terminal-domain cutoff, first-failure positivity branch, explicit fiber/cap
  incidence classification, surgery reconstruction, Corollary 15.4, and the
  finite-net loop-width cone. Hempel, Plateau--Morrey,
  Douglas--Hildebrandt, and parabolic-flow results are explicit imported
  contracts with registered source locations and stated hypotheses; their
  classical source proofs remain within the human review boundary.
- **Lean:** no live blueprint node is claimed formalized; all remain marked
  `\notready`.
- **Expert approval:** not obtained or claimed.
- **Route:** Morgan--Tian with explicitly cited Kleiner--Lott analytic
  interfaces where their hypotheses are stated in full.

The detailed current-source findings and imported-interface inventory are in
`blueprint/review/current-source-review.md`.

## Proof route

The foundations chapter fixes the comparison principles and neck-and-cap
topology used throughout. The analytic-control chapter develops reduced
geometry, local estimates, compactness, and noncollapsing. Chapter 3 is split
into Stage 3, **Blow-Up Limits, Kappa-Solutions, and Canonical Neighborhoods**,
and Stage 4, **Continuation of Controlled Ricci Flow with Surgery**. Stage 3
classifies the blow-up models and proves the canonical-neighborhood interfaces;
Stage 4 carries out first-failure extension, surgery restart, finite surgery
count, and all-time continuation. Stage 5 develops the corrected curve-shrinking
estimates. Stage 6 uses two-sphere and loop-space widths to show that no
component survives indefinitely. Stage 7 reconstructs the initial manifold
backward from the empty terminal slice and specializes its connected-sum
classification to the simply connected case.

The semantic DAG is the complete working inventory beneath this route. The
project-local blueprint map collapses it into a concise reader view; it does
not remove the underlying dependencies.

## Provenance

The live TeX and hgraph are the authoritative evolving record. Historical
snapshots are retained only as provenance and are not completion targets.
Morgan--Tian and the registered Kleiner--Lott, White, Topping, and Perelman
sources are used as explicit proof boundaries only where the live declaration
states the consumed hypotheses and conclusion. Hatcher is retained only as
historical context; no unregistered page-level anchor is consumed by the live
graph.

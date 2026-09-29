# Dehn Surfaces: Bounded Integration Review

Status: accepted by main at the digest in `dehn-surfaces-v4.json`.
The bounded review below is retained as the history of the finite findings.
Main subsequently read the complete chapter continuously and checked all
replacements and its three consumer interfaces. Sphere separation is now
stated before the enclosing-region construction, with Brown 1962 Theorem 3,
p.339 and Brown 1960 Theorem 5, p.76. Both primary papers were inspected;
Theorem 4 of the latter is not the complement-ball conclusion. The central
bibliography records these sources. Compact-core and smoothing consumers
use the same enclosing region and full rims. The disk, tower and annulus
termination measures and collar residual remain distinct. Obsolete
pending-status prose was removed. No unresolved internal finding remains;
whole-book gates remain separate.

This review reuses the independent revision-5 review recorded in
`dehn-surfaces-v4.json`. It checks only the finite ordinary-projection
repairs, tube and sector pasting, boundary parametrizations, termination
measures, and the marked-surface and collar-residual interfaces. Main-agent
whole-chapter review remains pending. This record does not mark the chapter
accepted or replace the JSON review record.

## Finite Finding and Correction

The proper-disk proof previously asserted inward compression without
exposing the finite residual on which it is the identity. The proof now
defines the closed strip, relatively open half-strip and complete roof,
constructs the residual by common subdivision and closure of the remaining
simplex interiors, and proves their exact overlap. The affine height change
`t -> (t + 1) / 2` then pastes to the identity as a finite PL embedding.
The identities have the label `eq:dehn-collar-residual` and are referenced
from smoothing. The residual is internal to this proof, not an extra field
in the generalized Dehn input.

Exact producers under `PoincareLib/Topology/Manifold/Smoothing/`:

- `Dehn/Collars/FiniteResidual.lean`,
  `exists_triangulation_closed_subcomplex_complement` and
  `exists_triangulation_collar_residual` (line 72).
- `Dehn/Collars/StripResidual.lean`,
  `exists_finite_collar_strip_residual` (line 27).
- `Dehn/Collars/InwardCompression.lean`,
  `exists_inward_collar_compression` (line 26).

## Bounded Reconciliation

No further finite defect was found in the repaired mechanisms inspected:

- `Dehn/General/ScheduledProjectedCrossings.lean`,
  `OriginalGeneralPositionData.exists_scheduled_crossed_marked_disk`:
  disjoint support windows transport whole branch images and the marked
  rim homotopy through the finite composite.
- `Dehn/Annuli/Descent/OrdinaryProjection.lean`,
  `Step.exists_ordinary_annulus_projection`: both rim maps remain fixed,
  the projected double locus is finite, and all collisions have ordinary
  charts away from the rims.
- `Dehn/Annuli/Surgery/Tubes/Blocks/VertexBlockMap.lean`,
  `ComponentBranchModel.exists_local_vertex_block_map`, and its
  `SectorMaps.lean` producer: exact sector intersections and common full
  end-face maps give an injective pasted tube with the stated preimages.
- `Dehn/Annuli/Parameters/HomotopicRimExtension.lean`,
  `exists_annulus_homotopic_rim_extension`: homotopy forces equal signs;
  interval extensions, a common reflection and independent phases retain
  both complete prescribed maps.
- `Dehn/General/OriginalFinitePLTower.lean`,
  `exists_terminal_reachable`, and
  `Polyhedral/Coverings/FinitePLCoverTowerCount.lean`: the same fixed finite
  source marks give the strictly decreasing natural-number tower measure.
- `Dehn/Disks/Resolution/BoundaryTermination.lean`,
  `OrdinaryDoubleCurveModel.exists_marked_disk_without_boundary_double_curves`,
  and `Dehn/Annuli/Descent/Reduction/Termination.lean`,
  `exists_embedded_planar_stage_annulus`: the disk and annulus component
  counts are the actual termination measures, with the required rim clauses.

The compact-core marked-disk application correctly allows the output rim
to change while retaining its excluded class and full-frontier properness.
The exact generalized-Dehn export is recorded in
`Triangulation/Handles/HamiltonProtectedGeometricInputs.lean`, definitions
`HasHamiltonProtectedDehnAnnulus`, `HasHamiltonProtectedDehnDisks`,
`HasHamiltonProtectedDehnSurfaces`, `HasHamiltonStandardProperDehnDisks`,
and `HasHamiltonGeneralizedDehnInput` (lines 141-211), and assembled in
`Dehn/Generalized.lean`.

## Scope Boundary

No Lean files, JSON acceptance state or checkers were changed. No builds,
Lean audits or comparator runs were performed. Relative-rigidity work was
not duplicated. Shared collar existence, sphere-separation placement and
whole-chapter integration remain for the main review; this bounded review
does not certify those larger obligations.

# Smoothing: Bounded Dehn Interface Review

This is a bounded integration review of the Dehn consumer passages, reusing
the independent Dehn review recorded in `dehn-surfaces-v4.json`. Main-agent
whole-chapter review remains pending. No chapter acceptance or replacement
of the existing JSON review is asserted.

## Findings and Corrections

The generalized-Dehn description incorrectly listed protected disks for
zero-, one- and two-period cases. It now states the actual index-one
annulus and index-two simultaneous disjoint disk pair, with their exact
rim maps and same-surface enclosing regions, together with the separate
standard proper-disk family preserving its prescribed boundary map.
The full discrete lattice and retained chart hypotheses are retained.

The former intersection-edge explanation and lexicographic count were
replaced by the actual mechanisms: a fixed-source finite tower measure;
disk boundary-component reduction followed by rim-fixed interior-circle
reduction; and annulus reduction of the actual source double-component
count. The proof is cross-referenced to the Dehn chapter.

The final handoff previously requested a finite collar residual as though
it were an additional generalized-Dehn output. It now distinguishes the
surface contracts from the internal residual construction used to paste
the prescribed-boundary disk compression. The substantive residual proof
is in `dehn-surfaces.tex`, at `eq:dehn-collar-residual`.

## Exact Sources

All paths below are under `PoincareLib/Topology/Manifold/Smoothing/`:

- `Triangulation/Handles/HamiltonProtectedGeometricInputs.lean`,
  `HasHamiltonProtectedDehnAnnulus`, `HasHamiltonProtectedDehnDisks`,
  `HasHamiltonProtectedDehnSurfaces`, `HasHamiltonStandardProperDehnDisks`,
  and `HasHamiltonGeneralizedDehnInput` (lines 141-211).
- `Dehn/Generalized.lean`, `hasHamiltonProtectedDehnSurfaces` and
  `hasHamiltonGeneralizedDehnInput`.
- `Dehn/General/OriginalFinitePLTower.lean`, `exists_terminal_reachable`.
- `Dehn/Disks/Resolution/BoundaryTermination.lean`,
  `OrdinaryDoubleCurveModel.exists_marked_disk_without_boundary_double_curves`.
- `Dehn/Annuli/Descent/Reduction/Termination.lean`,
  `exists_embedded_planar_stage_annulus`.
- `Dehn/Collars/FiniteResidual.lean`, `exists_triangulation_collar_residual`;
  `Dehn/Collars/StripResidual.lean`, `exists_finite_collar_strip_residual`;
  `Dehn/Collars/InwardCompression.lean`, `exists_inward_collar_compression`.

## Scope Boundary

The first pass edited the corrected Dehn export, termination summary and
final handoff. The additional bounded Cairns pass below edits only the
opening exposition of `sec:cairns-pullback`. This review does not recheck
smoothing's remaining arguments or
the actively owned relative-rigidity construction. No Lean files, JSON
acceptance state or checkers were changed; no builds, Lean audits or
comparator runs were performed. Main must read the complete chapter before
making any broader disposition.

## Cairns Construction: Additional Bounded Pass

The opening two paragraphs of `sec:cairns-pullback` previously asserted
normal-position extension and transition regularity through wrapper names.
They now expose the vertex-plane construction, the dimension-three
positive-face extension targets, the finite face recurrence preserving
ambient germs, the full-slice parametric filling and smoothing, and the
affine-leaf extension formula. The local chart argument retains the inverse
secant bound and paired-facet image-interior premise. The common-kernel and
leaf-incidence equations give an explicit invertible linear system for
the chart transitions.

This pass does not edit the subsequent carrier-pullback formula or later
sections, which remain under main review. It establishes no acceptance
disposition. The theorem proved here is a smooth atlas; the prose does not
infer real analyticity merely from smooth leaf fields.

Decisive sources read, under `PoincareLib/Topology/Manifold/Smoothing/`:

- `SmoothAtlas/LeafFields/SmoothNormalPosition.lean`,
  `exists_smooth_transverse_leafField_of_brouwerStars`, and
  `Polyhedral/General/BrouwerStarProjection.lean`,
  `nonempty_vertexStarPlanes_of_affineOnFaces`.
- `SmoothAtlas/Simplicial/PositiveFacePlanes.lean`,
  `contractible_positiveFaceStarPlanes`; its three-dimensional cases in
  `General/LinkIncidencePlanes.lean`, `Simplicial/CyclicFacePlanes.lean`,
  and `Simplicial/SmallNormalFacePlanes.lean` under `SmoothAtlas/`.
- The cyclic operator mechanism in `SmoothAtlas/Graphs/`
  `TangentCycleProjections.lean`, `AmbientCycleOperators.lean`,
  `CycleFrameCoordinates.lean`, `CycleProjectionSpace.lean`,
  `FixedEdgeCycleSpace.lean`, and `PlanarCycleConfigurationSpace.lean`;
  the two-ray convex operator target in
  `SmoothAtlas/General/TwoPointNormalSpace.lean`.
- `Polyhedral/LeafFields/FiniteSmoothLeafField.lean`,
  `exists_smoothLeafField_near_faces` and `exists_smoothLeafField_near_space`;
  `Polyhedral/Simplicial/SimplicialFaceLeafAttachment.lean`; and
  `Polyhedral/LeafFields/IntrinsicCellLeafAttachment.lean` and
  `ConvexCellLeafAttachment.lean`.
- `Polyhedral/General/GeometricCoreAttachment.lean` and
  `ParametricSmoothCore.lean`; `Polyhedral/LeafFields/ParametricLeafGluing.lean`,
  `RelativeTransverseGerms.lean`, `RelativeTransverseSmoothing.lean`,
  `CompactLeafGluing.lean`, and the affine-leaf formula and derivative in
  `AffineLeafCoordinates.lean` (lines 25-78). The uniform tube estimate
  was read in `AffineLeafInjectivity.lean`,
  `injOn_affineLeafMap_of_lipschitz`, and its assembly in
  `CompactAffineLeafChart.lean`,
  `exists_smooth_affineLeaf_chart_of_compact`.
- `Polyhedral/LeafFields/SmoothLeafFieldChart.lean`,
  `exists_chart_of_smoothLeafField`; `SmoothTransverseFrames.lean`,
  `FiniteComplexLeafChart.lean`, and `NormalizedProjectionLeaves.lean` in
  the same directory.
- `Polyhedral/Coordinates/FiniteComplexProjectionChart.lean` and
  `StrictDerivativeCarrierChart.lean`; the centered derivative calculation
  in `Polyhedral/General/VariableProjectionDerivative.lean`.
- `SmoothAtlas/LeafFields/LeafProjectionAtlas.lean`,
  `exists_smooth_atlas_of_leaf_coordinates`;
  `SmoothAtlas/Coordinates/ProjectionCoordinates.lean`; and
  `Polyhedral/LeafFields/TransverseAffineProjection.lean`,
  `transverseCoordinates_eq_iff` and `contDiffAt_transverseCoordinates`.

These source reads resolve the concrete missing mechanism in the specified
passage. They are not an exhaustive prerequisite audit. Main-agent
whole-chapter review remains pending.

## Alexander Index Three: Bounded Construction Pass

Replaced only the fourth-case passage in `drafts/smoothing.tex`, from
"The fourth case" to the finite supported assembly section. The old
paragraph incorrectly presented the zero-charge theorem as the entire
sphere argument. The replacement explains the finite section-charge
induction, its positive-charge split, the zero-charge construction of
both actual regions, their identification with the chart image, and the
whole-boundary extension and supported Alexander isotopy.

All source paths below are relative to
`PoincareLib/Topology/Manifold/Smoothing/`. Exact principal producers read:

- `Polyhedral/General/AlexanderComplexityCharge.lean:27`,
  `alexanderCurveCount`: a disjoint family contributes zero; at a meeting
  level the entire polygon family contributes. The complete presentation
  is `AlexanderComplexityPresentation.lean:24`. The finite measure and
  binary induction are `AlexanderRecursiveInduction.lean:45,109`;
  `AlexanderComplexitySum.lean:94` proves strict decrease from the
  levelwise inequalities and the one strict level.
- `Triangulation/Spheres/FinitePLSphereRegionInduction.lean:31`,
  `Regions/AlexanderInitialRegionInduction.lean:31`, and
  `Regions/AlexanderRegionInduction.lean:29`: original finite surface,
  generic initial height, retained admissibility and fixed outer body.
- `Triangulation/Regions/AlexanderPrescribedRegionSplit.lean:30` and
  `Triangulation/Affine/AlexanderConvexSupportSplit.lean:36`: exact cap
  incidences, support inside the fixed convex body, and pointed versus
  ordinary opposite cap moves. The level estimates were inspected in
  selected proof passages of
  `Polyhedral/General/AlexanderRecursivePointedChildren.lean:95-205`
  and `AlexanderRecursiveOrdinaryChildren.lean:135-240`; this is not a
  claim to have reread both files in full.
- `Triangulation/Regions/AlexanderRegionCertificates.lean`,
  `AlexanderRegionDeformedAssembly.lean:28`,
  `AlexanderRegionAssembly.lean:29`, `AlexanderRegionOpenAttachment.lean`,
  and `AlexanderRegionOpenExcision.lean`: the two literal ball pairs,
  pullback by each cap deformation, and the disjoint/nested alternatives.
  The nested collar construction was read in
  `Triangulation/Spheres/AlexanderRegionSphericalExcision.lean:31`
  and `Polyhedral/Regions/BoundedRegionNestedExcision.lean:29`;
  the decisive attachment and relative-neighborhood part of
  `Polyhedral/Spheres/BoundedRegionSphericalExcision.lean:28-100`
  was read. The exterior attachment case was also read in
  `Triangulation/Regions/AlexanderRegionExteriorExcision.lean:30`.
- `Triangulation/Regions/ZeroChargeRegionBalls.lean:30` and
  `Triangulation/Spheres/FinitePLSphereGenericSweep.lean:33`: signed-link
  control, unique extrema and one whole polygon at every intermediate
  level. The collar and exact fixed-disk identification were read in
  `Triangulation/Collars/ZeroChargeCollarCapStep.lean` and
  `Triangulation/Affine/ZeroChargeAffineHeightStep.lean`.
- `Triangulation/General/ZeroChargePairedCapStep.lean:38,52,351`,
  `ZeroChargePairedCapContinuation.lean:29,73`, and
  `ZeroChargePairedCapEndpoints.lean:28`: supported vertical push,
  preservation of both balls, finite interval subdivision and last-cone
  attachment. The first cone's literal exterior was checked in
  `Triangulation/Spheres/FinitePLSphereFirstCapExterior.lean:32`,
  `Triangulation/Affine/AffineFirstCapExterior.lean:30`, and
  `Triangulation/Affine/ConvexFrontierConeExterior.lean:35`; it is built
  by coning the complementary disk in a convex envelope and attaching
  to the envelope's cylinder exterior.
- `Triangulation/Handles/HamiltonIndexThreeRegionBalls.lean:32,96,121,164`,
  `HamiltonIndexThreeRegionSupplier.lean:42`,
  `HamiltonHandleThree.lean:30`, and
  `Polyhedral/Isotopy/ClosedBallIsotopy.lean:25,59`: exact chart boundary
  and image, the bottom-face contradiction identifying the region,
  prescribed boundary extension, and the correction direction
  `h.symm` after `g`.

This finite pass supplies the mechanisms missing from the specified
index-three paragraph. It does not claim a fresh exhaustive verification
of every imported PL collar or planar theorem, or chapter acceptance.
Main-agent whole-chapter/readability review remains separate. No Lean
files, contracts, acceptance JSON or checkers were changed, and no builds,
audits or comparator were run.

## Finite Geometric Realization: Additional Bounded Pass

The opening paragraph of `sec:independent-triangulation` previously jumped
from the compatible PL atlas to a finite geometric complex with affine
vertex stars. Its replacement exposes the supported PL graph blocks, their
height-one coordinate recovery and the resulting compact embedding. It
then constructs the exact finite image from local PL witnesses and a
compatible hyperplane subdivision, and explains the Lebesgue-number
subdivision placing whole closed stars in coordinate cores. The ambient
block projection is the actual chart on each such core, proving both
injection and interior image. The final paragraph explains purity,
connected edge links and the exact two-point triangle links, retaining the
full cofaces rather than a truncated local link.

Only this opening block before "This issue is repaired" was edited in
this pass. The independent-vertex realization and subsequent passages
were not changed. This is the geometric realization of the constructed
PL atlas, not a use of smooth-manifold triangulation. Main-agent
whole-chapter review remains pending; no acceptance state, Lean source,
build, audit or comparator was changed or run.

Sources read for this bounded mechanism, under
`PoincareLib/Topology/Manifold/Smoothing/`:

- `SmoothAtlas/Handles/HamiltonCairnsBridge.lean` and
  `Polyhedral/Affine/HamiltonAffineStars.lean`,
  `ChartedSpace.exists_finite_geometric_affine_star_triangulation`.
- `Polyhedral/Graphs/HamiltonPLGraphCover.lean`,
  `HamiltonPLGraphEmbedding.lean`, and `HamiltonPLGraphBlock.lean`;
  `CompactPLGraphCoordinates.lean`,
  `exists_locallyPL_supported_graph_extension`; and
  `SupportedPLGraphCoordinates.lean`,
  `AffineOnFaces.graph_vertex_bounds` and `exists_supported_graph_extension`.
- `Polyhedral/Handles/HamiltonFiniteImage.lean`;
  `Polyhedral/Topology/CompactLocallyPLImage.lean`,
  `exists_finite_triangulation_range_of_locallyPL`; and
  `Polyhedral/Polyhedra/FinitePolyhedralUnions.lean`,
  `exists_finite_triangulation_iUnion_convexHull` and
  `exists_finite_triangulation_iUnion`.
- `Polyhedral/Barycentric/FineSimplicialSubdivision.lean` and
  `AffineChartStarSubdivision.lean`,
  `exists_finite_subdivision_affine_vertex_stars`; and
  `Polyhedral/Coordinates/VertexStarChartRestriction.lean`,
  `injOn_and_interior_closedStar_of_chart`.
- `Polyhedral/Affine/AffineStarPurity.lean` and
  `AffineStarConnectedLinks.lean`;
  `Polyhedral/Simplicial/AffineStarFacetLinks.lean`,
  `InteriorFullCofaces.lean` and `InteriorFacetLinks.lean`; and
  `Polyhedral/Topology/InteriorConnectedLinks.lean`.

The finite polyhedral-neighborhood, common-subdivision and barycentric
mesh results are used as ordinary finite PL facts with their decisive
consumer arguments read above. This pass does not reopen their complete
prerequisite trees or certify the remaining chapter.

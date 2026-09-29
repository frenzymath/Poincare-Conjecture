# Ancient Models Integration Review

Status: accepted at the digest and with the outgoing interfaces recorded in
the final section. Earlier entries retain the chronology of resolved findings.
Authoring is finished, and the integration reviewer owns subsequent draft
corrections. Review uses production source
`751329327f4f582797bda8e6cffe7cdf7531cc1d`; Lean and contracts are unchanged.

## Terminal Annular Rigidity

Expanded the bounded ancient volume proof's local differential obstruction.
Read `AncientVolume/ScalarRatio/Cone/{RadialRegularity,RadialGradient,
HomotheticField,HomotheticLaplacian,NullPlane,NullReaction,TerminalRigidity}.lean`
in full, under `Geometry/RicciFlow/Harnack/Noncompact/`.
The source smoothness argument uses Rademacher at a nearby center and a joint
normal-endpoint inverse; it does not assume differentiability of the
Lipschitz potential at the requested point. The prose now supplies this
argument and the geodesic Hessian computation.

The homothetic-field computation is developed slot by slot. Its tensor
Laplacian is distinguished from the scalar Laplacian of a zero evaluation.
The terminal left derivative is nonpositive; the full fixed-input reaction,
including Ricci corrections, vanishes on the curvature-kernel plane.
This yields Ricci nonpositivity and hence flatness under nonnegative
curvature operator. This is a local result: no completeness or future-time
extension of the coordinate domain is used.

Read the consumers `ScalarRatio/{InfiniteRatio,FiniteRatio,
PositiveRatioContradiction}.lean`, `Cone/ZeroRatio/UmbilicRigidity.lean`,
and `ZeroVolume/Induction.lean` in full. These identify the actual required
producer chain and its quantifiers, not coverage completion. The annular
potential and interpolation constructions, zero-ratio compatible charts
and enclosing realization, and dimension-reduction producers still need
full substantive review. A combined read of `AnnularPotential.lean` and
`AnnularRigidity.lean` was truncated; it is not recorded as full-file review.

## Radial Potential and Local Variations

Read `Cone/{AnnularPotential,AnnularDistance,AnnularVariation,LocalDilation,
SourceVariation,FiniteRayApproximation,RayApproximation,RayPerturbation,
RayLimits}.lean` in full in separate untruncated reads. Expanded the
actual squared-distance equicontinuity argument, local two-sided ambient
distance convergence, simultaneous ray approximations, monotone comparison
cosines, and compact inverse-chart realization of a radial variation.
The Fermat argument uses the distances to both endpoints of the same
variation point; no smooth global dilation or continuity of that point's
choice is assumed. These steps now derive the exact potential interpolation
identity instead of invoking a cone identification.

Read `Annular/AncientLimit.lean` in full at the actual coefficient-limit
assembly. It retains terminal time, scalar one, and a common positive
metric neighborhood for all past times by Ricci monotonicity. Its
normalized spacetime, normal-chart and jet producers still require review;
the draft's initial construction paragraph is not accepted as complete.

Directly inspected the corrected Kleiner--Lott journal archive at printed
pp. 2674--2677, including Lemma 41.4 and the Case 1 curvature computation.
The source uses radial cone smoothness via Rademacher and a positive
curvature-plane contradiction. The implemented variant develops a
homothetic gradient and traces the radial tensor Laplacian to Ricci.
The text preserves that actual proof route without a novelty claim.

## Normalization and Terminal Time

Read `Annular/{Control,Normalization,NormalizedLimit,NormalizedSpacetime,
SpacetimeCompactness,LimitPositivity,HalfCylinder,ClosedCompactness}.lean`
in full. Read `Annular/SpacetimeBounds.lean` in full: the coefficient
comparison, terminal-ball derivative bounds, ellipticity radius, spatial
induction and mixed-jet assembly. Expanded their actual mechanism and
quantifier order: a single chart radius precedes the chosen past-slab
length; the upper estimates may depend on that length. Parabolic
noncollapse is applied only after the annular tail bound supplies its
whole-cylinder curvature antecedent.

The terminal-time extraction is on a closed convex half-cylinder. Bounds
on the next derivatives provide equicontinuity, a common diagonal retains
all boundary jets, and derivative extension identifies them at time zero.
The chapter does not extend the flow to future times. It also distinguishes
the incomplete annular coordinate domain from a complete pointed limit.

Also read `Annular/{Compactness,ChartFlow,FlowRealization}.lean` in full.
The realization constructs the metric from positive coefficients and its
canonical Levi-Civita connection; first time and second spatial jets retain
the equation within the closed time interval. This is not an assumed
limit flow. Read `Cone/AnnularRigidity.lean` in full by completing separate
reads of lines 1--165, 166--319, and 320--end. Its restriction and metric
transport preserve local geodesics and speeds, then transfer terminal
flatness by curvature naturality.

Read the shared `Compactness/Coordinates/SpacetimeBounds/` producers
`SpatialEvolution.lean`, `Ricci/{Pullback,JetBounds}.lean`,
`Curvature/MetricBounds.lean`, and `Bootstrap/Evolution.lean` in full.
Expanded the inverse-metric differentiation identity, the Christoffel
derivative order, conversion of covariant to ordinary curvature derivatives,
and fixed-basis Ricci contraction. This explains why the unknown highest
metric jet occurs only linearly. The mixed-jet induction is simultaneous
over every spatial order; it uses only finitely many thresholds at any
given order.

Under `Geometry/Riemannian/Coordinates/Exponential/JetBounds/`, read
`FiniteOrder/{Pullback,Metric,Frame}.lean` and `CoframeJacobi.lean` in full,
and `ConnectionKernel.lean` lines 85--132. Expanded the actual radial
parallel coframe, its Jacobi initial-value problem, the curvature/connection
induction, and the metric product formula. Lower matrix-parameter estimates
and radial-connection differentiation are identified dependencies, not
claimed full-file reviews here.

Under `Geometry/Riemannian/Comparison/Injectivity/`, read
`{Uniform,CanonicalPowers,CenterPacking,Noncollapse,PackingScale,
PrecompactData,BallDiffeomorphism,NoPeriod,FiniteOrbit,OrbitConvexity}.lean`
and `Lifting/OrbitMargins.lean` in full (the initially truncated packing
scale read was repeated separately). Read `RadialConvexity.lean` lines
1--160. The prose develops smaller-ball volume, exponential differential
bounds, the finite packing count, short return and loop lifts, exclusion
of finite periods by a compact orbit-energy minimum and radial convexity,
and propagation of distinct sheets to obtain the volume contradiction.
It retains the explicit count-dependent loop scale; shortness alone does
not justify infinite order. Exact intrinsic-ball coverage is then derived
from minimizing parameters and injectivity.

The subordinate short-return, smooth lifting, Jacobi-pairing, and area-formula
producers still need the shared compactness source review. Their mathematical
roles are exposed in the text; this bounded pass does not assert recursive
source-review completion or chapter acceptance.

## Zero-Ratio Annulus and Link

Read `ScalarRatio/FiniteRatioSequence.lean` in full. The finite alternative
now chooses points approaching the decreasing tail supremum, and retains
a single eventual upper bound before separating positive and zero limits.

Under `ScalarRatio/Cone/`, read `Metric/UniformConeDistance.lean` in full:
the Dini argument is uniform over ray pairs and both radial parameters in
a bounded interval, including zero. This justifies using one threshold
for annular nets. Read `Metric/{Link,UniformRayDistance,SphereApproximation}.lean`
and `Metric/Family/{DenseDirections,AnnularNets,Annular}.lean` in full;
`Metric/Cone.lean` was read through line 210. The draft now defines the
ray pseudometric, its metric quotient, and the actual cone distance before
using a smooth link or cone.

Read `ZeroRatio/Family/{Rays,Embedding,Realization,Coverage}.lean`,
`ZeroRatio/FamilyOverlaps.lean`, `ZeroRatio/Backward/MetricJets.lean`,
`ZeroRatio/Source/{BackwardFlatAnnulus,Transitions,Quotient,Neighborhood,
UnitNeighborhood,Embeddings}.lean`, and
`ZeroRatio/Surface/LocalModelsAnnuli.lean` in full. Expanded the common
countable chart extraction, static backward spatial jets, cross-distance
limits, zero-distance overlap maps, compact target confinement, and
derivative control of actual transitions. The common cone realization
retains all cross-distances; dense centers and uniform ball coverage
cover the whole unit slice. No independent choices of incompatible
chart realizations are used.

Read the shared Ricci-flow compactness producers
`Compactness/GeometricLimit/Stages/SourceEmbedding/{Finite,Extension,Separation}.lean`
and `Analysis/Calculus/Diffeomorphism/SmoothCorrection.lean` in full.
The text develops the cutoff correction of the new chart to the retained
old embedding, the nested compact domains, and the uniform distance
argument excluding new collisions. It then explains why finite ray nets
and chart-ball coverage place an entire thin source annulus in every
chosen neighborhood of the compact unit slice. The lower overlap jet
and cutoff-diffeomorphism producers remain shared dependencies; this
pass does not claim their recursive review is complete.

Read `ZeroRatio/Source/{Metric,UnitPotential}.lean`,
`Positive/RadialPotential.lean`, and
`UnitLink/{RegularCharts,Transitions,Metric,Connected}.lean` in full.
The truncated transition output was completed by a separate read of
lines 160--210. Expanded regularity from the eikonal identity, the
implicit-function atlas, distance-derived smooth ambient transitions,
and descent of the induced level metric. The radial potential and its
Hessian/gradient identities are transported to the actual fixed source
neighborhood. Subordinate positive-cone atlas and metric producers are
identified imports, not claimed fully reviewed here.

Read `Metric/{Geodesics,AngularPaths,Antipodal}.lean` in full. Added the
source distance-split construction, compact passage to exact cone
splits, normalized nonantipodal paths, and the source Toponogov inequality
for antipodal endpoints. The argument uses the positive-dimensional
level atlas to choose a third direction; it covers the one-dimensional
link and does not assume simple connectedness. The whole-ball
approximation and midpoint-completion producers still need their shared
source review.

The `ZeroRatio/Backward/SourceLimit.lean` assembly was inspected, with a
separate untruncated read of lines 125--310. The initial full-file output
was truncated; full review of that assembly and its enclosing-chart
producers is not claimed. The enclosing realization, angular metric,
volume rigidity, and dimension reduction remain pending. The chapter
is not accepted.

## Enclosing Realization and Zero-Ratio Rigidity

Completed `ZeroRatio/Backward/SourceLimit.lean` with untruncated reads of
lines 1--124 and 311--474, in addition to the recorded middle read.
Read `ZeroRatio/Backward/{FilledDomainDecay,BallControl,EnclosingCharts,
EuclideanCoefficients,EnclosedLimit,GlobalEnclosedLimit,LimitLinkRigidity}.lean`
in full; the two enclosed-limit files were split into separate reads.
Read the shared `Geometry/Riemannian/Distance/{CompactImages,
CompactNeighborhood}.lean` in full. The draft now obtains the earlier
diameter from the compact connected link's intrinsic metric, extends it
to an open neighborhood by finitely many coordinate segments, states the
actual bounded-ancient Harnack distance inequality, and keeps the order:
choose the extra scale, obtain whole-past ball decay, apply noncollapse,
then construct enclosing normal charts.

The Euclidean coefficient limit is identified by the radial Jacobi error
estimate and polarization. Countably many actual inverse-chart maps have
one smooth compatible limit, with image confined to radius rho/8 inside
the radius-rho/4 coefficient domain. The explicit straight coordinate
segment in radius rho/6 transfers terminal distance separation; no
confinement of an ambient minimizing curve is asserted. Lower transition
compactness and normal-chart producers remain shared review obligations.

Read `Geometry/Riemannian/Hypersurface/{RadialPotential,
HomotheticRadialPotential,UmbilicSphere}.lean` in full. Expanded the
normalized local isometry, the pushed-forward radial gradient, the
connection identity giving equality of normal and immersion differentials,
and retained global separation. The positive-dimensional sphere is covered
by an open-and-closed image argument, including for circle links.

Read `UnitLink/{Distance,AngularDistance,AngularLower}.lean` in full;
the angular-distance file was read in three untruncated pieces. Read
`Polar/{SmoothAction,Metric,Tensor}.lean` in full. The text derives the
angular triangle inequality using an explicit intermediate cone radius,
compares short angles to chords along subdivided paths, and computes the
normalized segment's angular speed and integral. Antipodal endpoints are
handled by nearby level-chart points and the proved source comparison.
The draft includes joint radial smoothness from geodesic dependence and
the polar tensor calculation. `Polar/LocalChart.lean`, `Polar/Orbits.lean`,
and `ZeroRatio/MetricArc.lean` are identified lower producers, not claimed
fully reviewed here.

Read `Metric/{Euclidean,VolumeComparison,RiemannianVolume,VolumeRigidity}.lean`
and reread `ZeroRatio/UmbilicRigidity.lean` in full. The radial extension
uses a chordal isometry, not just an intrinsic spherical classification.
The source-to-cone contraction is defined only on the ray union, where
it is well-defined and covers the radial cone ball. Hausdorff volume
comparison is therefore available without a volume-convergence assertion.

Read `Geometry/Riemannian/Comparison/Volume/Rigidity/{MaximalBalls,
Density,Radial,Flatness}.lean` in full. Expanded center independence,
all-radius equality, unit normal-coordinate density, and the transverse
Jacobi trace inequality that forces center Ricci to vanish. The underlying
Hausdorff/Riemannian measure identification, polar change of variables,
and transverse Jacobi comparison still require shared source review.

This completes a substantive expansion of the zero-ratio route, not a
whole-chapter acceptance. Dimension reduction remains a sketch. A later
readability pass must divide the long bounded-ancient proof into named
intermediate results once their statements and interfaces are settled.

## Selected Line and Ancient Factor

Read `AncientVolume/Splitting/{DimensionReduction,AncientFactor,ParallelLimit,
SurfaceLine,NonflatLineLimit,TerminalFactor,Backward,SelectedComparison,
SmallSelectedLine,SmallRescaledLimit}.lean` and
`AncientVolume/Volume/{Factor,FactorRatio,SmallSelectedLimit}.lean` in full.
Reread `ZeroVolume/Induction.lean` in full. These paths are under
`Geometry/RicciFlow/Harnack/Noncompact/`. The old prose incorrectly ended
the induction with a separately constructed one-dimensional ancient factor.
The source base case constructs a nonflat surface limit with a line and
uses surface curvature algebra to contradict its parallel unit direction.
The draft now uses that base case. The induction selects at t1-1 < 0,
retaining positive volume at t1 <= 0. The stronger scalar-ratio theorem
itself includes the terminal slice; its consumer needs only negative times.

Read `AncientVolume/{PointSelection,BackwardControl}.lean` and
`Splitting/{InitialDirections,SelectedEndpoints,SourceSegments,
EndpointSelection,BufferedSegments,DistanceDistortion,GeometricLine,
LineLimit,OppositeSegments,LimitTransport}.lean` in full. Expanded bounded
doubling with the displacement budget, the further radius reduction,
whole-past curvature control, and the parabolic noncollapse antecedent.
The pointwise scalars remain bounded; the curvature-scaled distances and
radii diverge. The same buffered pointed limit retains nonflatness,
positive volume and the line. Farther-vertex selection, comparison-cosine
trimming, the exponential containment margin, and the length-independent
additive time error are explicit. The line is obtained through actual
inverse embeddings using source-ball coverage and one common ultrafilter.
The general compactness, Toponogov, Calabi-support and coverage producers
remain shared lower review obligations; their use here is not a claim
that those dependencies are fully reviewed. `AncientRescaledLimit.lean`
was searched only, not read in full; this route uses `SmallRescaledLimit`.

Read `Geometry/RicciFlow/Splitting/{Persistence,NullEvolution,NullConnection,
NullSectionEnergy,KernelTransport,ParallelField}.lean`,
`KernelTransport/{Ricci,Monotonicity}.lean`,
`MaximumPrinciple/{RicciPropagation,RicciNullity}.lean`,
`PartialTrace/Continuity.lean`, and `PartialTraceEvolution.lean` in full.
The combined partial-trace/parallel-field output was truncated; separate
reads of partial-trace lines 330--end and parallel-field lines 1--65
completed the visible portions. The text develops minimizing partial
frames, nonnegative moving-frame reaction, nullity thresholds, the
terminal null-section energy identity, and actual kernel transport across
rank changes by inverse regularization. It then uses all three null slots
of the Ricci derivative in connection variation and metric duality to
preserve one fixed parallel gradient. Lower scalar strong-positivity,
radial frame jets, Ricci transport and local null-section producers are
identified shared review obligations, not discharged by their wrappers.

Read `AncientVolume/Splitting/{FactorFlow,SurfaceFlatness}.lean`,
`AncientVolume/Volume/Noncollapse.lean`, and
`Geometry/Riemannian/Splitting/ParallelGradient/Volume.lean` and
`Volume/Balls.lean` in full. The fixed zero-level metric satisfies Ricci
flow by tangential Ricci restriction. The draft gives its global product
map and inverse, the product-cylinder volume comparison, and the single
constant AVR(G(0))/2^(n+1) at every factor time, center and radius.
This proves the actual factor noncollapse implication and noncompactness.
Induced curvature/regular-level geometry and product-measure construction
still require their lower source review.

The proposed cross-reference to a line-specific Busemann splitting proof
in `ricci-flow.tex` had no matching exposition and was removed before
publication. Read `Geometry/Riemannian/Splitting/Busemann/{Main,Parallel,
Calibration}.lean`, `Weak/{Subharmonic,Harmonic,StrongMaximum,UpperTest,
Comparison,Supports}.lean`, `Regularity/Smoothness.lean`, and `Alignment.md`
in full. The replacement exposition distinguishes lower supports of the
approximants from supports of their limit, uses their explicit factor-two
Laplacian error, and derives compact comparison before upper tests and
the exponential-barrier maximum argument. It then develops signed weak
harmonicity, coordinate elliptic regularity, calibrated spheres and Bochner.
The integral distance comparison, local weak derivatives and Bochner
producers remain shared review targets. This new passage adds a real
missing section interface; it does not count a citation as its proof.

Compared the actual source text with Kleiner--Lott corrected 2013,
Proposition 41.13, printed p. 2678 (original TeX label `propI.11.4`),
and Morgan--Tian's published Clay edition, Definition 2.2 and Proposition
2.3, printed p. 22, and Lemma 2.14 with its proof, pp. 28--29
(PDF pages 65, 71--72). The implemented route retains the surface base
case, uses factor-four point selection, an interior time buffer, direct
source-segment line construction, and an explicit all-past factor volume
constant. Its Busemann sign is opposite to Morgan--Tian; unit gradient
is obtained by compact calibrated spheres, and Bochner supplies the
parallelness needed for a product. No novelty claim is made.

The chapter remains pending. The interface division below addresses the
structure of this expanded argument; a complete independent readability
pass remains necessary. The source read list is traceability, not
completeness evidence.

## Exposition Interfaces

Separated the bounded-ancient argument into a short dimension-induction
proof and seven named intermediate results. The two finite scalar-ratio
obstructions share only the stated hypotheses of the proposition, not its
conclusion. The selected-limit lemma explicitly retains a positive time
buffer, completeness, full curvature bound, line and positive volume on
the same limit. Busemann splitting is a separate static lemma. Persistence
and the factor have explicit independent hypotheses, including the fixed
field and one all-past curvature bound. The factor lemma uses general K;
the induction specializes it to 4 n^2. No extra curvature normalization or
noncollapse hypothesis is silently imposed on the factor.

The new text labels and substantive source assemblies are:

| Text Label | Source Assembly |
| --- | --- |
| `lem:ancient-infinite-scalar-ratio` | `ScalarRatio/InfiniteRatio.lean`, `infinite_scalar_ratio_of_bounded_ancient` |
| `lem:ancient-positive-ratio-obstruction` | `ScalarRatio/FiniteRatio.lean`, `false_of_positive_finite_scalar_ratio`, assembling `PositiveRatioContradiction.lean` with `Cone/MetricComparison.lean` for corresponding-side comparison |
| `lem:ancient-zero-ratio-obstruction` | `ScalarRatio/Cone/ZeroRatio/UmbilicRigidity.lean`, `curvature_eq_zero_of_zero_ratio`, then bounded ancient positivity |
| `lem:ancient-selected-line` | `Splitting/NonflatLineLimit.lean`, `exists_nonflat_small_ancient_limit_with_line_of_unbounded_scalar_ratio` |
| `lem:ancient-line-busemann` | `Geometry/Riemannian/Splitting/Busemann/Main.lean`, `busemann_parallel_unit_gradient` |
| `lem:ancient-parallel-persistence` | `Geometry/RicciFlow/Splitting/Persistence.lean`, `backward_persistence_of_parallel_gradient`, on every closed slab |
| `lem:ancient-fixed-factor` | `Splitting/AncientFactor.lean`, `parallelGradientFactor_ancient_geometry`, with `FactorFlow` and volume producers |

Paths without a `Geometry/` prefix in this table are relative to
`Geometry/RicciFlow/Harnack/Noncompact/AncientVolume/`. These are exposition
interfaces and traceability entries, not assertions of completed lower
dependency review. The long positive-ratio and zero-ratio constructions
still need a further readability pass alongside those lower dependencies.

## Radial Orbit and Polar Interfaces

Read `ScalarRatio/Cone/ZeroRatio/MetricArc.lean` and
`ScalarRatio/Cone/Polar/{Dilation,Orbits,SmoothAction,Metric,LocalChart}.lean`
at the retained production revision. Expanded the angular-distance proof
to explain the following prerequisites before differentiating a normalized
cone segment:

- Exact affine distance makes an arc smooth in local normal coordinates.
  Opposite-side distance equality forces opposite initial unit directions
  by the almost-isometric exponential chord bound and the unit-vector
  equality case. Fixing one parameter on each side proves linearity
  of inverse normal coordinates. No completeness of the local metric is
  required.
- The actual dilation orbit has speed equal to radius and potential
  `(1+t)^2 u`. Its initial velocity equals the gradient by the eikonal
  identity and the squared norm of their difference.
- Continuity first gives one neighborhood and time interval for all nearby
  starting points. Rescaling orbit time produces a geodesic on `(-1,2)`
  with smooth data `(y,t grad u(y))`; smooth endpoint dependence proves
  joint smoothness. Pointwise smooth orbits alone would not suffice.
- Fixed positive dilation is a distance isometry after scaling the source
  metric. The previously used local distance-isometry transition theorem
  supplies its smoothness. The induced regular-level metric, radial unit
  norm and orthogonality give the positive polar tensor. In equal
  dimensions its differential is invertible, and radius and normalization
  identify the local inverse on overlaps.

Also read `Geometry/Riemannian/Distance/{GeodesicCorner,CornerRigidity}.lean`
and `ScalarRatio/Cone/ZeroRatio/IsometryTensor.lean` in full; read
`Geometry/Riemannian/Coordinates/Exponential/SmoothExtension.lean`
lines 285--end, including the open-and-closed propagation of smooth
geodesic data and its endpoint consumer. The corner proof above follows
the actual exponential chord argument, not an alternative first-variation
proof. Tensor preservation uses geodesic speed followed by polarization.

Read `ScalarRatio/Cone/ZeroRatio/{IsometryRegularity,IsometryLipschitz,
NormalEndpoints,IsometricCharts}.lean` in full. Replaced the earlier
squared-distance-coordinate explanation of transition smoothness with
the actual nearby-Rademacher-center argument. The joint endpoint inverse
is chosen before the differentiability center, so it covers the prescribed
point. The proof retains a common interval of geodesics within the open
domain, passes them through the distance map, and reconstructs smoothness
from their linear initial velocities. This also justifies the smooth
homothety used for the polar tensor.

This closes the exposition of these polar and transition interfaces,
conditional on the earlier retained-chart construction. It does not close
the subordinate normal-chart, exponential chord, frozen-distance or local
geodesic-dependence review. The source reference is Kleiner--Lott,
corrected 2013, Theorem 41.2,
Case 2, p. 2677; the local-chart construction explains the implemented
regularity steps rather than attributing them verbatim to that page.

## Universal Noncollapse and Compact Round Limits

Under `Geometry/RicciFlow/AncientKappa/Noncollapse/Universal/`, read
`Nonround.lean`, `Estimate.lean`, `FlowControl.lean`,
`ClosedCylinders.lean`, `Convergence/{Alternative,Region,Volume}.lean`,
`ReducedLength/{ShortPath,Region,TerminalBound,Recovery}.lean`,
`ModelVolume.lean`, `ModelGeometry/{NoncompactVolume,QuotientVolume}.lean`,
and `Roundness/{CompactLimit,AncientCriterion,Cone,Reaction,Preservation,
TransportedContact,Static,TimeShift}.lean` and
`Roundness/Convergence/{CompactPinching,Spectrum}.lean` in full.
Also read `Geometry/RicciFlow/Generalized/Noncollapse/TerminalRegion.lean`
in full. Directly inspected Morgan--Tian, Corollary 9.44, printed
pp. 208--209, and Proposition 9.58, printed pp. 220--221.

Added `lem:ancient-compact-round-limit`, with the actual uniform
contraction identity forcing all curvature eigenvalues toward the round
value. Compact convergence covers the whole source by an open-and-closed
argument. The proof explains the fixed convex pinching cone for the Ricci
complement, its reaction boundary inequality, compact tensor comparison,
and the limiting Einstein equation at every negative time and at zero.
This uses preservation of every factor c > 1; it does not merely infer
roundness from closeness. Morgan--Tian cites Hamilton's pinching toward
roundness at this point; the implemented cone-preservation route is
developed without a novelty claim. Also read
`Roundness/{RicciComplementEvolution,MovingCurvature,SpatialContact}.lean`
and `Analysis/Parabolic/LocalPreservation.lean` in full. The moving-input
product rule cancels the fixed-input Ricci corrections; cyclic curvature
components identify the complement equation. Local compact shrinking
charts supply a compact bounded family of supporting pairs for the
maximum argument. Lower support-reaction, connection-contact and compact
maximum producers still require the shared review.

Expanded `thm:ancient-universal` with the quotient-ball injectivity
argument, the explicit factor-eight volume loss under convergence,
backward volume monotonicity on the fixed region, and source-ball coverage
for scalar control. The path estimate uses a seed action at most six,
terminal squared speed at most exp(4), and total action at most
14 + 4 exp(4). Square-root-time smoothing is justified before comparing
with the actual reduced-length infimum.

For recovery, read
`ReducedGeometry/ReducedLength/Minimum/Variational/Recovery/Finite.lean`
in full, `Recovery/Primitive.lean` lines 1--190, `Recovery/Chart.lean`
lines 1--155, `TimeSupport/RegularPath.lean` lines 1--200, and
`Extension/Manifold.lean` lines 1--100, under `Geometry/RicciFlow/`.
The text gives the interior-bump integral correction, constant endpoint
germs, uniform primitive bound, compact chart confinement and strong-L2
kinetic convergence. This is now explained locally rather than referred
to as if already developed in the reduced-geometry draft. Its general
finite-chart recovery interface remains to be reconciled in that chapter.

The open stable preimage of the earlier region is specified explicitly;
ordinary capture makes its image conull in the region and its branch
action the ordinary reduced length. This supplies the precise interface
to `thm:m15-noncollapse`. The original radius, half-open past convention,
and terminal time are then recovered; nonroundness after time translation
uses compactness and the same pinching preservation. Lower capture,
model-volume and tensor comparison dependencies remain pending, as does
the whole chapter.

## Interior Flat-Limit Contradiction

Under `Geometry/RicciFlow/AncientKappa/Compactness/`, read
`LocalBounds/{AuxiliaryContradiction,EarlierVolumeUpper,FlatVolume,
VolumeDeficit,SmallRadiusRescaling}.lean` and
`Unnormalized/{Noncollapse,Flatness,Volume}.lean` in full.
Expanded the local-control proof of `thm:ancient-compactness` to
distinguish the bounded nonflat positive-volume auxiliary limit from
the subsequent flat limit with a unit-volume deficit.

The latter has bounds depending on each spatial radius, not an assumed
global bound. Terminal base scalars tending to zero force base curvature
zero at every interior time by the source past estimate; local scalar-zero
rigidity and nonnegative curvature operator then give flatness on every
interior slice. Complete-ball coverage, strict smaller-cylinder margins
and volume convergence retain the original kappa, so flatness supplies
an all-radius lower volume bound with no constant loss.

The earlier-ball upper bound uses only the fixed terminal unit ball:
tangent norms inflate by at most exp(27 B delta), volumes by at most
exp(81 B delta), and ball monotonicity places the earlier ball inside
that region. The stated delta retains the three-quarter Euclidean deficit.
The final contradiction is now an explicit exponential/Jacobi argument:
zero curvature makes the pullback metric Euclidean on the injectivity
ball; rescaling by (sigma/r)^2 and using all-radius noncollapse proves
Euclidean ball volume at every radius. No flat quotient classification
or terminal convergence is assumed.

Lower finite-radius point selection, scalar-zero rigidity, complete interior
compactness and exact ball-volume convergence remain shared review inputs.
Their consumers and quantifier order are exposed here; this does not
accept the complete normalized compactness theorem or the chapter.

## Finite-Radius Curvature Estimate

Read `AncientKappa/Compactness/LocalBounds/{FiniteRadius,Selection,
Volume,Rescaling,Sequence,BackwardVolume,Limit,AuxiliaryContradiction}.lean`
and `AncientKappa/Compactness/{ScalarBuffer,Nonflatness,Noncollapse}.lean`
in full, under `Geometry/RicciFlow/`. Also read
`Analysis/Parabolic/PointPicking.lean` and
`Geometry/RicciFlow/Harnack/Noncompact/Comparison.lean` in full;
`Harnack/Noncompact/Exhaustion.lean` through line 180 and
`Harnack/Noncompact/AncientVolume/Nonflatness.lean` through line 110
were supporting partial reads. Directly inspected Morgan--Tian printed
pp. 223--227, especially Corollary 9.62, Lemma 9.65 and Claim 9.66.

Expanded the finite-radius estimate inside `thm:ancient-compactness`.
The point-selection proof now retains its displacement budget, termination
from individual boundedness, factor-four whole-past control and the
half-size rescaled radius. Recentering explicitly gives nu/27 by containment
and Bishop--Gromov. Expanding controlled balls retain the same normalized
sequence, while finite exceptional prefixes affect only compactness input
constants and not the eventual global bound B=4 on its interior limit.

The earlier reference slice carries volume at least nu/(27 exp(27 B)^6)
times radius cubed: both the radius and measure losses are shown.
The source scalar evolution and uniform second curvature derivatives give
one positive base-scalar buffer before zero on the same limit.
The text now proves backward nonflatness by forward scalar comparison,
including the proper exponential barrier on a noncompact slab, rather
than inferring it from scalar monotonicity. The distinct static
noncollapse loss kappa/27 is derived using the radius-a/3 cylinder and
then transferred to the limit. Translation to the positive interior
slice allows the zero-AVR theorem at the earlier reference slice.

This is the fixed-kappa dimension-three specialization actually used.
Morgan--Tian Corollary 9.62 states a broader dimension-dependent estimate;
the exposition does not assert that broader quantifier order. Its
terminal-limit argument is replaced in this implementation by an interior
buffer and explicit volume transfer; the subsequent flat-volume argument
also uses injectivity and scaling instead of classifying flat quotients.
No novelty claim is made. Lower complete interior compactness, local
derivative estimates, distance smoothing and ball-volume convergence
remain shared review obligations; this expansion does not accept them
or the whole chapter.

## Convergence Through Time Zero

Read the following under `Geometry/RicciFlow/AncientKappa/Compactness/`:
`TerminalJets.lean`, `TerminalDerivatives.lean`,
`Coordinates/{Terminal,SpatialBounds,EmbeddingBounds,EmbeddingConvergence,
TerminalPositivity,FlowRealization}.lean` and
`Terminal/{Construction,Gluing,Completeness,Assembly,Normalization,
Noncollapse}.lean`. The initial combined EmbeddingBounds display was
truncated; the continuation from line 320 through the end was read in
separate bounded displays, completing the file.

Split the long normalized-compactness proof into local curvature control,
convergence through zero and the still-pending global curvature bound.
The terminal proof now retains the original carrier, subsequence and
embeddings explicitly. It derives all-time curvature derivatives on a
terminal r-ball using the earlier unit ball inside the terminal (r+1)-ball.
Complete reference-slice compact transfer supplies one source terminal
ball for each compact limit chart. Reference ellipticity propagates with
the exp(54 C d) coefficient factor on a closed slab. The already developed
affine spatial-jet argument supplies spatial bounds; the coordinate Ricci
equation supplies mixed bounds.

An auxiliary closed-domain candidate is identified by interior convergence;
the displayed two-time comparison, with error at most 2 L eta plus an
interior compact error, upgrades the original full sequence through zero.
Positive coefficients and one-sided derivatives realize the chart flows;
agreement on overlaps at zero follows by continuity from the common
interior metric. No new spatial atlas or subsequence is silently substituted.

Terminal completeness is proved before using terminal compact balls:
individual short paths have compact image and map into source balls of
twice the radius, transferring a uniform local curvature bound. On a
terminal 3r-ball that bound makes every terminal Cauchy sequence Cauchy
for the complete reference metric; the common manifold topology identifies
the limit. Scalar normalization and operator sign are passed separately.
Exact terminal kappa follows from an earlier radius-rho cylinder with
rho^2-r^2 < s < 0 and volume loss exp(81 r^(-2)(-s)); time tends to zero
before rho tends to r. This replaces the earlier undifferentiated statement
that strict margins alone pass noncollapse through the endpoint.

Subordinate coordinate bootstraps, complete interior compactness,
terminal curvature convergence and exact interior cylinder convergence
remain shared review obligations. The global boundedness proof and
the chapter are not accepted.

## Regular Bands and Both Neck Components

Read in full, under `Geometry/RicciFlow/AncientKappa/Compactness/Boundedness/`:
`Conclusion.lean`, `Spherical.lean`, `Geometry/{GradientGap,LinearGrowth,
LevelTransport}.lean`, `Geometry/Smoothing/{RegularBand,Radial,
ControlledTransport,NeckTransport}.lean`,
`Geometry/Smoothing/ComponentDiameter/{Uniform,Euclidean,Components,
Exhaustion}.lean`, `Geometry/NeckLevels/{Scale,ScalarGraph,Axial,
SignedSegments}.lean`, `Projective/{Exclusion,Scale}.lean`,
`Projective/Levels/{Graph,GraphMetric,Transport}.lean` and
`Projective/Geometry/{GapRate,SignedSegments}.lean`.
Also read `Geometry/Riemannian/Soul/{ExhaustionFunction,Horoball}.lean`
in full. Directly inspected corrected Kleiner--Lott printed pp. 2687--2688,
Theorem 46.1 and Remark 46.4.

Expanded the fixed-terminal-metric obstruction in `thm:ancient-compactness`.
The actual ray-supremum exhaustion and its linear distance bound fix a
radial rate before the remote center is selected. Compact convex value
gaps give a band gradient lower bound before the two smoothing errors;
the Hessian error is then chosen below the radial and transport thresholds.
The normalized negative-gradient variation calculation now shows the
factor-two tangential expansion, while the reverse flow gives bijectivity
and transport of whole components.

The axial step exposes its precise remaining geometric input: the
signed long minimizing-segment comparison. The first half-slab exit is
at least scale/(8 epsilon), and the radial value gap forces a negative
initial derivative. Signed axial alignment transfers this to a uniform
absolute axial derivative on the central slab. The projective branch uses
the descended axial coordinate and the original covering differential.
The two explicit choices of slab width dominate the corresponding
central-section oscillations. Fiberwise monotonicity constructs a unique
smooth graph; antipodal uniqueness makes the projective height even.
Open-and-closed capture identifies a whole ambient level component.
Its graph differential and the sphere's diameter bound the transported
component by 4 pi scale (1+8/l), with no injectivity assumption on the
sphere parametrization in the projective case.

The low-level diameter constant is fixed on C_2 intersect {3/4 <= f <= 5/4}
inside {1/2 < f < 3/2}, independently of the remote band and approximation.
The text develops the coordinate-cover contradiction using a collared
surface's bounded complementary side and an interior extremum. The
underlying collar-separation theorem remains a topology interface to review;
no ambient Schoenflies identification is used in this argument.

Kleiner--Lott uses a one-ended exhaustion boundary and a nonexpanding
retraction. The implementation reviewed here treats individual components,
uses smooth almost-convex bands and expansion at most two, and explicitly
retains the projective alternative. This source comparison is a statement
of the implemented route, not a novelty claim. Lower convex smoothing,
signed geodesic alignment, separation/collar constructions, and the
selected line-splitting blowup still require review before acceptance.

## Signed Long-Neck Comparison

Read in full under `Geometry/RicciFlow/CanonicalNeighborhood/Neck/`:
`Flux/Directional/Geodesic.lean`,
`Geodesic/{Axial,Threshold,Intrinsic,Long,Alignment,Interval,Acceleration}.lean`,
`Geodesic/Acceleration/{Hessian,Estimate}.lean`, and
`Geodesic/Jets/{Centered,Coefficients,Reparametrization}.lean`.
Read in full under `AncientKappa/Compactness/Boundedness/Projective/`:
`Intrinsic.lean`, `Geometry/{Segments,Axial,Pairing,Hessian,FirstJet,Coefficients,
Reparametrization}.lean`. Directly inspected Morgan--Tian printed
pp. 498--501, especially Lemma A.4, pp. 498--499.

The global-boundedness proof now develops the signed comparison rather
than invoking it. Centered first metric jets and ellipticity give the
scale-aware Hessian estimate K epsilon/scale^2 by the Koszul formula.
The spherical path and linear axial interpolation give the intrinsic
competitor with transverse constant sqrt(2)(pi+1). The fixed window
scale/(200 sqrt(epsilon)) lies on one side of every parameter, including
both endpoints, because twice its length is below the segment length.
Acceleration control and minimality give absolute axial velocity at
least A^-1-C/window-delta*window. Its scaled value tends to one.
Nonvanishing, continuity, and the mean value theorem determine the sign
from the endpoints. The actual pullback metric error then gives the
squared tangent error 2 beta+5 epsilon, uniformly over scales and lengths.

Both the competitor and Hessian argument apply on the actual projective
cover: the axial coordinate descends through its same-height fibers;
only local differential inverses are used. The proof retains the
original cover's axial tangent at each preimage. Morgan--Tian proves
the model case and appeals to geodesic dependence on the metric. The
implementation provides the explicit intermediate-window argument
above; no novelty claim is made. The centered-jet calculation was then
followed to the stereographic formula: its derivative vanishes at the
center, so the first covariant error jet is the ordinary coefficient
derivative. Basis norms at most two give component bound 8 epsilon;
expansion in three basis vectors in each slot gives operator bound
216 epsilon. The text includes this step. The general inverse-Gram
tensor norm and coordinate Hessian transformation interfaces remain
shared coordinate background to reconcile with the rest of the book.

The compactness review remark has been updated to identify the actual
remaining smoothing, separation, and blowup obligations. The earlier
regular-band section's pending signed-comparison item is advanced by
this review, without accepting the chapter.

## Selected Raw Blowup and Terminal Transfer

Read in full under `AncientKappa/Compactness/Boundedness/`:
`{PointSelection,BlowupProduct,Factor,Line,ScalarBuffer,Noncollapse,
AncientSolution,BufferedSegments,Distance,TerminalParameters,
TerminalCylinder,TerminalCloseness,Escape}.lean` and
`Projective/{Alternatives,TerminalCloseness}.lean`.
The middle of `BlowupProduct.lean`, initially display-truncated, was
read separately through lines 180--245. Also read
`CanonicalNeighborhood/Neck/Convergence/Bounds/Terminal.lean` in full.
The source comparison is Kleiner--Lott Theorem 46.1, pp. 2687--2688,
previously directly inspected; its compressed blowup step is expanded
using the actual source constructions.

Replaced the opening wrapper paragraph of the global-boundedness proof.
Continuous scalar curvature is bounded on the compact point-selection
budget ball, so doubling terminates without assuming the desired global
bound. The selected scalar factors diverge; controlled rescaled radii
and distances diverge, while relative radii tend to zero. The text
explicitly does not claim that unscaled radii diverge. Raw rescalings
have curvature at most four on expanding terminal balls throughout
their past. The scalar buffer is chosen under an arbitrary positive
cap; the auxiliary interior limit obtains its global bound from these
expanding balls. Static noncollapse is kappa/27, and the actual product
factor has parabolic constant kappa/54. The earlier selected-line and
persistent-factor arguments are reused with their applicable hypotheses.
The closed-time comparison uses Ricci bound twelve and additive error
108 delta, not the constants of the earlier bounded-volume argument.

The terminal transfer is now quantitative. Finite jet constants precede
the buffer and actual limit. Scalar normalization theta lies in [1/2,1]
and differs from one by at most D delta. The earlier convergence error,
time error and normalization error give tau+(B+2DZ)delta. The cap
epsilon/[2(C_0+1)(B+2DZ+1)] controls the whole covariant jet sum.
Take the minimum of both branch caps before constructing the limit.
The original maps, exact fibers, centers and inverse-square-root scalar
scales then transfer to the same terminal metric. Diameter control and
center escape exclude the fixed basepoint from every late half-slab.

The finite-jet time estimate's lower coordinate bootstrap remains shared
with the preceding terminal-convergence review. General pointed
compactness and corresponding-side comparison remain pending as already
recorded. The full chapter is still not accepted; lower smoothing and
collared-surface separation review remain reachable next steps.

## Remote-Frontier Smoothing and Collar Separation

Read in full `AncientKappa/Compactness/Boundedness/Geometry/InnerParallel.lean`,
`Geometry/Smoothing/{Depth,Exhaustion}.lean` and
`Geometry/Smoothing/ComponentDiameter/Collars.lean`; reread the latter
directory's `Euclidean.lean`. Read in full
`Geometry/Riemannian/Distance/Smoothing/{ClosedSet,Compact}.lean`,
`Geometry/Riemannian/Comparison/Hessian/{Distance,DistanceToSet}.lean`,
`Analysis/Approximation/{Semiconcavity,RegularizedMinimum/Finite,
RegularizedMinimum/Finite/Basic}.lean`, and
`Analysis/Convex/EuclideanUpperSupport.lean`.
Read `RegularizedMinimum/AbsoluteValue.lean` through line 170 and
reread the depth identity in `Geometry/Riemannian/Soul/Horoball.lean`.
Read in full `Topology/Manifold/Separation/{Sign,Components,Connected,
Bounded}.lean`. Directly inspected Morgan--Tian Lemma 2.20 and its
context on printed pp. 31--32: that lemma is about a positive-curvature
soul and central spheres, not the arbitrary compact collared separator
used here. Its source-file citation is contextual, not a precise
statement identification.

Expanded the actual smoothing mechanism: calibrated rays identify
remote-frontier depth with c-f on positive levels, retaining only the
needed inequality at the zero core. Nearest-point distance supports,
quarter-segment shortening and the affine index field give upper
Hessian 4/(3 distance). Normalized charts, semiconcavity and positive
convolution produce local approximations. The gluing uses nested
cutoffs, a small positive bias and a finite smooth minimum. The value
gap makes every invalid branch inactive. Nonnegative weights summing
to one and a negative Hessian for the selector preserve the derivative
bounds with a controlled loss. Choosing remote depth 8/(3H), then
derivative loss H/2, gives the required almost-convex exhaustion.
The coordinate support and convolution steps are exposed; the lower
radial inverse/index-form background and general coordinate conversion
remain shared geometry interfaces recorded in earlier reviews.

The low-level diameter argument now constructs its separator's sign
function. A clamped collar coordinate extends to the circle; simple
connectivity gives the normalized real lift. Its zero set is precisely
the central section. The two sign regions are connected by the
boundary-neighborhood argument, and connected Euclidean exteriors
identify exactly one bounded side. This works for any compact connected
collared central space; no sphere identification or ambient Schoenflies
theorem is used. The gradient collar itself is now developed from a
common compact-level flow time, scalar evolution f(Phi_t x)=f(x)+t,
and the explicit reverse-time inverse justified by flow uniqueness.
Mathematical signposts divide the long global-boundedness proof into
its seven mechanisms. The author JSON retains its historical issues
and gains a current integration progress record pointing to this review,
including the remaining shared inputs and unaccepted classification
and asymptotic-potential sections. Whole-book readability and shared interface reconciliation
remain pending; these expansions do not accept the chapter.

## Surface Shrinker Critical Levels and Coarea

Read the complete-surface compactness route and the compact differential
and conservation files under `Soliton/TwoDimensional/`. Read
`Compact/Regularity/Smooth.lean` and the rigidity files
`Degenerate`, `GlobalExtrema`, `RegularLevels`, `CriticalLevel`,
`Jacobi/Potential`, `Jacobi/NoInteriorZero`, `LevelArea`, `Coarea`,
`SlabDensity`, `VolumeDensity`, `PoleInequality`, `TotalCurvature`, and
`Roundness`. Read `Geometry/Riemannian/Surface/SublevelVolume.lean` and
its `Bounds.lean`, and the conjugate-point route
`Comparison/Volume/Conjugate/{NoConjugate,Frame/Negative}.lean`.
The normalized-chart Taylor and volume-density machinery is ordinary
local Riemannian background; its quantitative disk comparison is now
explicit in the proof.

Replaced the unsupported inference from connectedness to one circular
level family. The actual argument first obtains the critical-value
alternatives from the conserved gradient energy and the strict
exponential tangent inequality. Degenerate critical points force
constancy by that same algebraic inequality, not by the draft's
previous appeal to an unspecified scalar ODE. For a nondegenerate
critical point, the potential derivative along a minimizing geodesic
is a scalar Jacobi field. Rolle's theorem would give an interior zero
if the endpoint had the same potential. The proof now exhibits the
negative index variation that rules this out, hence proves the unique
minimum needed in the sublevel normalization.

The regular-level argument retains total length, without assuming
connectedness or orientability of the levels. Its gradient flow,
length variation and gradient-energy ODE give constant coarea density.
Exhaustion by closed regular slabs gives the open-slab area formula;
normal coordinates at the unique minimum and two disk inclusions
identify its constant as 2 pi/a0. Integrating exponential curvature
on regular slabs, then passing to the endpoints, gives the sufficient
inequality against total curvature. This avoids an unproved assertion
that all critical fibers have zero area. The endpoint exponential
trapezoid inequality contradicts Gauss--Bonnet in both orientability
cases. The C2-to-smooth bootstrap and differentiated conservation
identities are also exposed.

Direct source comparison: Morgan--Tian printed pp. 203--208 contains
Proposition 9.39 and Corollary 9.40 about splitting at infinity, not
the stated complete static surface lemma. The relevant classification
is Theorem 9.42 and compact Claim 9.43, with the latter referring to
Chow--Knopf Proposition 5.21, p. 118. The implemented surface proof
supplies compactness directly from a positive scalar lower bound and
Myers, without bounded curvature or noncollapsing. Updated the lemma's
locator to distinguish this stronger hypothesis range. No novelty
claim follows. Also directly checked printed p. 19: Theorem 1.34 is
Bishop--Gromov, so its citation in the conjugate-point source files is
contextual, not the no-interior-conjugate-point theorem. The book's
expanded index-form proof does not rely on that inaccurate locator.

This resolves the compact surface-rigidity mechanism in the draft,
not the entire surface ancient-limit route or chapter acceptance.
The surface entropy argument and its compact-convergence interfaces
remain under review, followed by the three-dimensional classification.

## Ancient Surface Entropy and Compact Convergence

Read `Soliton/TwoDimensional/Ancient/{Compactness,Roundness,Endpoint}.lean`;
the entropy files `Bochner`, `Fisher`, `Evolution`, `Evolution/Volume`,
`Evolution/LogIntegral`, `Variation/Global`, `Positivity`, `ScalarPositivity`,
`UniformLimit`, `Rescaling`, `Rigidity`, and `Convergence`; all four
`Entropy/Poisson/{Harmonic,Spectrum,SmoothEigenbasis,Approximation}` files;
and `Convergence/{Diffeomorphisms,MetricJets,CurvatureJets,Scalar,Volume}`.
These readings retain the original rescalings and spatial maps throughout.
The lower scalar-evolution and heat-contact machinery is shared with
the Ricci-flow chapter, whose broader analytic review remains pending.

Expanded the proof to derive entropy evolution from constant total scalar
curvature, volume variation, and logarithmic integration by parts. Its
normalization is invariant under constant metric scaling in dimension two.
The equality case now explicitly uses continuity and full support of area.
The Fisher inequality follows from integrated Bochner, a completed square,
and approximation of mean-zero scalar curvature by smooth Laplacians.
The finite spectral sums divide only positive modes by their eigenvalues;
harmonic zero modes are constant and orthogonal to the datum. Only the
L2 convergence of their Laplacians is needed. The compact energy resolvent,
Rellich compactness and elliptic regularity are identified as the ordinary
spectral inputs, rather than assuming an unconstructed Poisson solution.

The convergence step now transfers compactness by the retained global
diffeomorphisms, obtains uniform scalar convergence from metric derivatives
through order two and compactness, and uses Gauss--Bonnet to bound the
varying areas by 16 pi at the normalized scalar-one limit. Uniform density
convergence then gives entropy convergence despite changing measures.
The exact rescaling identity transfers these entropies to the original
backward times. Nonnegativity and monotonicity force zero entropy at every
negative time; scalar continuity and nonflatness include time zero.
The scalar positivity argument uses an earlier nonflat slice and heat
propagation, without importing the three-dimensional curvature-cone part
of the referenced Ricci-flow proposition.

Directly inspected Chow--Knopf printed pp. 117--120 and 133--136 in the
retained PDF (PDF pp. 130--133 and 146--149), and Morgan--Tian printed
pp. 213--214. Chow--Knopf Proposition 5.21 uses Kazdan--Warner after
passing to a sphere cover; the implemented compact rigidity instead uses
the Jacobi/coarea argument developed above. Proposition 5.39 has decreasing
entropy and a negative sum-of-squares derivative. The archival
`entropy-transcription-correction.md` correctly records the erroneous
"nondecreasing" wording in a derived merged transcription; the actual
PDF was used for this review. Morgan--Tian Corollary 9.50 invokes both
backward and forward round limits. The implementation uses nonnegative
relative entropy and its backward zero limit, so no forward maximal
extension or forward roundness theorem is needed here. No novelty claim
is made. Added the existing source's bibliographic data to the publication
bibliography and precise locators to both surface statements.

The specified asymptotic-limit construction remains an upstream review
obligation. This closes the exposed surface-rigidity and entropy mechanisms
conditional on that input, not M19 or whole-chapter acceptance by itself.

## Compact Three-Dimensional Shrinking Flows

Read `Soliton/Flow/{Generation,Bounds,Speed,Complete/Gradient,
SelfSimilar/Construction,Regularity/Potential}.lean`; read
`ThreeDimensional/Classification/Static.lean` and
`Compact/{RicciPositive,QuotientHomothety,QuotientMaximum,
RicciNormEvolution,RicciContraction,RicciSpectrum,PinchingAlgebra,
Einstein,Roundness}.lean`. Read
`Splitting/{PartialTraceEvolution,PartialTrace/Continuity,
MaximumPrinciple/RicciNullity,MaximumPrinciple/RicciPropagation}.lean`.
The global vector-field continuation theorem and lower radial-frame
and heat-contact maximum-principle producers are shared analytic inputs;
their remaining review is not hidden by these reads.

Replaced the draft's unsupported compact splitting explanation for
Ricci positivity. The actual proof uses a potential maximum, where
Ricci is at least half the metric, and spatial constancy of Ricci
nullity at an interior slice of the supplied ancient flow. The new
text develops partial traces as variational sums over orthonormal
frames, continuity, radial spatial supports and Ricci time transport.
The moving-frame reaction is a sum of nonnegative sectional terms
weighted by nonnegative Ricci eigenvalues. These supply lower-contact
heat inequalities and scalar strong positivity. All partial traces
then detect and propagate the kernel-dimension thresholds. The
compact positivity step needs only the zero threshold, but the general
mechanism is retained for the later nullity/splitting interface.

Expanded generation from the given C2 potential: coordinate bootstrap,
bounded Hessian, the squared-gradient-speed Gronwall inequality,
compact confinement in both time directions, complete gradient action,
and the exact -log(-t) time change. The proof now computes the Ricci
flow equation and the backward curvature bound from homothety.
The subsequent classification retains any supplied shrinking flow.

The normalized Ricci argument now explains why a fixed maximizing
point has zero time derivative, without differentiating a moving
maximizer. It derives the quotient PDE from the norm and scalar
equations, includes both inverse metric factors, applies the tensor
Cauchy--Schwarz estimate at the critical point, and identifies the
reaction contraction by the dimension-three curvature formula.
The explicit gap polynomial proves coercivity even at repeated
eigenvalues. Its zero forces the global quotient to be 1/3; contracted
Bianchi and the Ricci complement give roundness on each actual slice.

Directly inspected Morgan--Tian printed pp. 74--75 and 206--208 and
Kleiner--Lott Appendix A, Theorems A.5 and A.7, printed p. 2841.
The compact argument specializes the pinching mechanism rather than
using an entire forward round-limit theorem. Recorded in shared
`source-specializations.md` the false nonnegative-Ricci dichotomy in
the printed first sentence of MT Theorem 4.23 and the explicit shrinking
sphere-times-fixed-circle counterexample. The implementation's
potential-maximum argument supplies its own stronger input and does
not use that overstatement. No Lean or reference edit was made.
Kleiner--Lott A.7 concerns curvature-operator image/holonomy; the
displayed Ricci partial-trace proof supplies the specific needed
nullity result rather than identifying the two statements verbatim.

The noncompact level-area argument, global splitting realization,
asymptotic curvature bound and same-flow self-similarity remain under
review. The compact expansion does not accept M20 or the chapter.

## Noncompact Potential Growth and Scalar Normalization

At the unchanged production source pin, read
`Soliton/ThreeDimensional/Noncompact/{RicciIntegral,RadialGrowth,
ProperPotential}.lean` and
`Rigidity/{PotentialLevels,ScalarFlow,ScalarBounds,Contradiction,
NullReduction,LevelCurvature}.lean`. Read the full
`Rigidity/AtInfinity/{UnscaledLimit,Line,ScalarTransfer,Normalized}.lean`,
`Rigidity/Normalization/{RoundSlices,Scalar,Flow}.lean` and
`Rigidity/Levels/{Flow,Area,ScalarUpper,MetricExpansion}.lean`.
The first path is relative to `PoincareLib/Geometry/RicciFlow/`;
the `Rigidity/` paths are within its `Soliton/ThreeDimensional/Noncompact/`.
The lower index, selected-segment comparison, fixed-level product
and metric-coordinate producers retain the shared review obligations
already recorded above.

Expanded the noncompact strict-Ricci alternative through the level
curvature estimates. The draft now derives the uniform minimizing
Ricci integral, radial derivative and quadratic potential growth,
compact sublevels and attained minimum, and uniform high-gradient
threshold from the scalar conservation identity. It does not assume
connectedness of high levels. The complete gradient flow reaches a
compact core backwards and propagates its positive scalar minimum
globally.

The unscaled source is translated to extinction time one. The text
explains extraction on the whole open time interval using one normal
atlas, scalar transfer through second metric jets, escape in every
complete source slice, and the line construction in the retained
limit. Round factors are constructed separately at each selected
time by backward parallel-gradient persistence and surface
classification. Spatial scalar constancy and the cylindrical Ricci
norm reduce the actual ambient scalar evolution to a Riccati ODE.
Positivity up to time one and the inherited diverging lower bound
force its integration constant to be one. Every escaping source
sequence therefore has a scalar subsequence tending to one.
Strict scalar growth on every high gradient trajectory then proves
the uniform strict threshold R < 1.

Expanded normalized-gradient metric variation on individual
components, the sharp sectional complement Ricci bound, intrinsic
area first variation and the weaker sufficient Gauss bound. The
last inequality only needs q > 1 and 0 <= Ric(N,N) <= R < 1;
it does not replace intrinsic level curvature by ambient scalar.

Directly compared Morgan--Tian Proposition 9.46, Claims 9.47--9.48
and 9.51, equations (9.21)--(9.25), printed pp. 209--216.
The implemented argument retains a limit from any escaping sequence,
normalizes it on the ambient flow, and will compare actual transported
components. It does not require the historical inference that a
positively sectionally curved carrier is R3 to exclude projective
surface factors. The high-level graph construction, its convergence,
component capture and area transport remain to be reviewed next.
No acceptance or final rendering follows from this partial expansion.

## Retained Potential Graphs and the Area Contradiction

Continued through `Noncompact/Rigidity/Levels/`:
`PotentialLimit.lean`, `PotentialLimit/{Growth,Bounds,Estimates,
JetBounds,Connection,Equation,Forcing,Extraction,Identities,Factor,
ProductConvergence}.lean`, `Graph.lean`,
`Graph/{Estimates,Convergence,Metric,Component,Comparison}.lean`,
`Graphs/{Construction,Comparison}.lean`,
`Transport/{Complete,Normalized,Shift,Diffeomorph}.lean`,
`{AreaConvergence,TotalCurvature,AreaObstruction}.lean` and the
consuming `Rigidity/Contradiction.lean`. The shared full coordinate
compactness, product-isometry and measure-construction inputs retain
their broader review obligations. Standard Gauss--Bonnet is used with
the precise compact, boundaryless surface hypotheses, including the
nonorientable case.

The expanded proof constructs a complete bounded extension of the
normalized gradient, with the actual smooth denominator, speed bound
three, action law and exact high-level shift. Centers are integer
points of one trajectory; the two extracted subsequences and final
tail are represented by one strictly increasing source index. This
preserves their exact potential differences and transported centers.

Normalized potentials use the diverging gradient scale at each center.
The proof supplies bounded-Hessian oscillation, conservation-based
gradient bounds, bounded image distance for each compact limit set,
and the coordinate Hessian recurrence using the retained spacetime
metric and its time derivative. The Leibniz induction supplies all
jets before diagonal extraction. Vanishing forcing gives zero
Hessian; the inverse-metric energy at the retained base is exactly
one and parallelism propagates it. The zero level of this particular
potential is the retained connected complete factor, whose scalar
one gives compactness by Myers. No identification with a previously
chosen Busemann potential is presumed.

The graph construction now gives endpoint signs, a uniform vertical
derivative lower bound, a unique root, implicit smoothness, and
explicit height/differential bounds. The exact graph metric and
relative error estimate yield area convergence by a two-dimensional
determinant comparison. Compact immersion into the regular level is
open and closed, hence fills a whole component. Transported centers
identify those components; injective parametrizations give the actual
diffeomorphism and expanding pullback metrics. Finally the positive
integral of 1 minus intrinsic scalar and metric independence of total
curvature contradict area monotonicity and convergence.

Compared directly with Morgan--Tian printed pp. 214--216. The source
instead excludes projective factors using positive-sectional topology
and states convergence of full levels to spherical slices. The actual
proof needs only strict Ricci positivity for the contradiction and
works on retained connected components of arbitrary compact surface
topology. Its Gauss estimate drops the nonnegative second fundamental
form norm and uses q > 1, in place of the historical sharper trace
coefficient. These are verified route differences, not novelty claims.
The previous pending high-level graph summary is superseded by this
expansion; whole-chapter readability, shared prerequisites, null
splitting, quotients and the asymptotic self-similarity remain pending.

## Null Cover and Fixed Coordinates for the Supplied Flow

Continued through `Soliton/ThreeDimensional/Splitting/`:
`{NullPlane,Reaction,Rank,LocalParallel,UnitCover}.lean`,
`Global/{Coordinate,CoverCoordinate,Completeness,Noncollapse,
FixedNullity,FlowExtension,FlowTransport,SourceProduct,Realization}.lean`
and `Global/Surface/{Normalization,AmbientScalar,LevelSphere,
SolitonEquation,SphereDiffeomorph,RoundCover,Cover,DeckAction,
DeckCardinality,IsometryLift}.lean`. Also read the shared
`Splitting/{NullSections,NullSectionEnergy,NullConnection}.lean`.
Earlier fixed-level product and backward-persistence evidence is
reused; their subordinate review obligations are not discharged
merely by this application. The local round-chart and germ-continuation
producers under `Geometry/Riemannian/SpaceForm/` remain part of the
shared space-form review.

Replaced the compressed splitting paragraph with the null-plane
diffusion/reaction signs and its explicit three-dimensional matrix
argument. Spatial nullity, nonflatness and curvature polarization
give rank one. Smooth null sections are constructed using the inverse
of the Ricci matrix plus projection onto its kernel at the center.
The differentiated-null-section energy identity and terminal time
derivative sign then prove parallelism. These are separate steps;
constant rank alone does not imply a parallel distribution.

The exposition constructs the actual two-sheeted unit-kernel cover,
including local sign charts, free reversal and the global coordinate
r(x,v)=2 df_x(v). Finite-cover properness supplies completeness, and
the complete unit parallel flow gives an explicit product map and
inverse. Ball path lifting, local curvature preservation and Hausdorff
volume comparison retain metric kappa noncollapse. The actual zero-level
ancient factor has kappa/2 and is nonflat on every past slice by bounded
ancient scalar positivity. Surface classification and restriction of
the soliton equation fix sectional curvature 1/2 and ambient scalar one.

The proof retains arbitrary supplied shrinking-flow data. Its pointwise
slice homotheties imply constant nullity and scalar -1/t. Backward kernel
inclusion plus equality of dimension fixes the literal kernel subspaces.
Differentiated curvature annihilation and contracted second Bianchi kill
all slots of the Ricci derivative; connection variation and the metric
equation preserve the same parallel field and its dual dr. The resulting
scalar tensor ODE gives g_t=(-t)(g_-1-dr^2)+dr^2 in fixed coordinates.
No differentiable family of chosen homotheties is assumed.

The sphere cover has singleton or antipodal fibers, proved by orthogonal
first-order lifting, uniqueness of local isometries and the determinant
injection for a free O(3) subgroup. Reversal either exchanges the two
cover components, making either component map bijectively to the original
carrier, or preserves one component and acts freely on its zero level.
The latter excludes the antipodal surface: an orthogonal lift of any
surface isometry has a fixed real line. These arguments retain the
actual quotient map and deck action; the final normal-form and projective
identification review remains pending.

Directly inspected Morgan--Tian Theorem 1.11 and its space-form consequence,
printed pp. 8--9, and Claim 9.45, printed p. 209 (preceded by Claim 9.43
and Corollary 9.44 on p. 208). The historical proof invokes Hamilton
splitting and then rules out a circle by its potential. The implementation
constructs a real coordinate directly and separately proves all-time
identification for supplied flow data. These are recorded route differences,
not novelty claims. Publication checks do not discharge shared prerequisites
or whole-chapter readability; acceptance remains pending.

## Quotient Normal Forms on the Original Carrier

Read `Soliton/Models/Certificates.lean`,
`Certificates/QuotientTransport.lean`,
`Spherical/{Normalization,FlowScale,Certificate}.lean` and
`Involution/{MetricSeparation,Factorization,FactorMetrics,SphereFactor,
Rigidity,Formula,ProjectivePlane,Twisted,NormalForm}.lean`.
Read `Geometry/Riemannian/SpaceForm/SphereIsometry.lean`,
`Quotient/Covering.lean`, the substantive first-order deck, fiber,
finiteness and orientation proofs in `Quotient/DeckAction.lean`,
and `Quotient/Orientation.lean`. Inspected the explicit forward/inverse
maps and smoothness proofs in `Topology/Homotopy/Sphere/Polar.lean`.
The lower round-distance, local-round-chart and germ-continuation
proofs remain in the shared space-form review.

The compact branch now obtains fixed-coordinate homothety by integrating
the actual metric equation, after Ricci naturality under each supplied
slice homothety. Potential extrema give sectional scale 1/4; the sphere
cover thus has scale -4t at every negative time. The proof constructs
deck orbits from first-order local-isometry uniqueness, obtains freeness
by lift uniqueness and finiteness from a compact discrete fiber, and
uses the implemented even-dimensional determinant cancellation to put
the action in SO(4).

The cylinder branch separates the two tangent forms using two times.
The proof now explains why preservation of their kernels gives zero
cross derivatives and factorization on connected slices. Unit derivative
norm plus involutivity gives a line isometry. On the sphere, preservation
of curve length and the angle/chord formula give chord isometry. Distances
to zero and one classify the line map. The draft's alternative invocation
of an orthogonal sphere matrix has been replaced by the actual normalized
midpoint argument, using only inner-product preservation and involutivity.

Positive pullback metric and equal dimensions make the supplied quotient
projection a local diffeomorphism, hence an open quotient map. Matching
its fibers with the standard projective map gives a homeomorphism in both
directions. The twisted formula now uses the source coordinate ordering
(w,x), its explicit smooth inverse (u/|u|,a/|u|), and the actual punctured
cover onto the supplied smooth carrier. The theorem retains the precise
distinction between a homeomorphism of topological models and a compatible
smooth local-diffeomorphism cover. Time-dependent metric and sectional
curvature transports retain the same projection and identification.

Directly compared Morgan--Tian Theorem 1.11 and its consequence,
printed pp. 8--9, Corollary 9.54's conclusion on p. 218, and the
three-model list in Proposition 9.58, pp. 220--221. The projective
alternatives agree with that list; the source constructs explicit
commuting coordinates rather than only giving diffeomorphism types.
This expansion does not discharge the asymptotic self-similarity proof
needed before Corollary 9.54 can be applied, or the shared space-form
producers. Whole-chapter acceptance remains pending.

## Self-Similarity of the Retained Asymptotic Flow

Read `Soliton/ThreeDimensional/Asymptotic/SelfSimilarity/`
`{Bounds,GradientGrowth,Confinement,Regularity,Evolution,
MetricIdentity,Flow,LiftedFlow}.lean`,
`Geometry/Riemannian/ScalarOperators/Gradient/Growth.lean`,
`Geometry/Riemannian/Metric/Flow/LinearGrowth.lean`,
`Geometry/Manifold/Flow/TimeDependent/Global.lean` and
`Geometry/RicciFlow/Metric/PullbackVariation/Soliton.lean`.
This review is conditional on the preceding per-slice global curvature
bound; it does not discharge the neck-scale obstruction. The underlying
ordinary differential equation local existence and metric variation
calculus retain their shared background treatment.

The expanded proof obtains slab Ricci and Hessian bounds from the right
endpoint bound and retained scalar monotonicity. It bounds the gradient
at the stored base by compact-time continuity, compares all tangent norms
and distances with one complete reference slice, and uses a regularized
gradient norm to handle critical points. This produces the actual
linear spatial growth bound in that fixed metric, including the harmless
dimension-dependent constant and additive regularization term.

An integrated-speed majorant supplies the Gronwall estimate in both time
directions without differentiating the distance function at the cut locus.
Completeness makes the confinement ball compact. Uniform local existence
on its product with a finite time slab, restarts near the proposed endpoint,
and uniqueness give smooth continuation on neighborhoods of each initial
point. Overlapping slabs agree. The resulting global evolution has the
composition law and inverse obtained by reversing the two times.

The proof differentiates the pulled-back metric along the actual negative
potential gradient, cancels the Hessian by the soliton equation, and solves
the scalar tensor ODE after division by time. Its inverse maps give the
homotheties of the original retained limit flow. The universe lift is
implementation transport by a fixed diffeomorphism, not additional
mathematics or a different flow. This differs from Morgan--Tian Corollary
9.54, printed p. 218, which identifies the classified generated flow with
the limit by uniqueness and splitting. The implemented direct evolution
keeps the original flow throughout. The earlier reduced-length energy
passage, per-slice curvature proof and whole-chapter review remain pending.

## Reduced-Length Energy and Time Derivatives

Read `AncientKappa/Asymptotic/ReducedLength/GradientConvergence/`
`{AncientEnergy,AncientHamiltonJacobi,AncientSpacetimeQuadratic,
AncientFixedTime,AncientQuadratic,AncientBounds,RescaledWeak,
RescaledEquations,AncientTimeEquation}.lean` and the corresponding
`LimitEquations/{Soliton,SmoothHamiltonJacobi}.lean`. The shared
analysis reads are `Analysis/Elliptic/Regularity/GradientCompactness/`
`{Cauchy,Energy,Identification,FluxBound,IntegralTests,Coercivity,
DirectionalLimit,TimeIdentification,Products,ParametricProducts}.lean`,
`EnergyEstimate/{FluxComparison,ComparisonTest}.lean`, and
`WeakInequalityLipschitz.lean`.

The draft now derives the exact local coercivity estimate from two
nonnegative Lipschitz tests at finite indices. It explains extension,
truncation and positive mollification, retains the changing density and
inverse metric, and displays both the uniform function error and the
coefficient error. Completeness in L2 and integration by parts identify
the resulting gradient limit. Product estimates give spatial L1 energy
convergence; joint measurability, a uniform integrable bound and Fubini
give spacetime convergence. The source rescaling factor is retained on
both sides of the weak inequality.

The time argument uses a further almost-everywhere energy subsequence,
the rescaled Hamilton--Jacobi equation and the common spacetime Lipschitz
bound. Integration by parts identifies the limiting time derivative.
Continuity after regularization upgrades the identity to every point.
This local argument does not assert a global pointwise-convergent
subsequence over all charts, or infer gradient convergence from uniform
convergence alone. Mass, weak heat equality, smoothness, tensor defect
and nonflatness still require further source/readability review.

Directly read Morgan--Tian Claim 9.22, printed pp. 190--191, and
Lemma 9.23/Corollary 9.24, pp. 191--192. The historical gradient proof
tests against the limit and uses weak W1,2 convergence; the implementation
uses two finite-index tests to obtain an explicit Cauchy estimate with
changing coefficients. No novelty claim follows. The printed statement
of Lemma 9.23 says D(psi) <= 0 for nonnegative psi, whereas its proof's
equation (9.9) says D >= 0 and Corollary 9.24 uses that latter sign.
For D = ell_tau + |grad ell|^2 - R + n/(2 tau) - Delta ell,
the density identity is (partial_tau - Delta + R)u = -u D;
D >= 0 is the sign needed for the conjugate-heat subsolution.
This discrepancy is reported without changing the reference or Lean.

## Mass, Weak Equality and Tensor Defect

Read the reduced-length `Mass/{Limit,LowerBound,UpperBound,Distortion,
Cutoff,Laplacian,HeatCutoffs}.lean`, `Tails/Gaussian.lean`,
`Tails/Limit/{Bounds,Gaussian,Moments,Cutoff}.lean`,
`LimitGradient/{Coordinates,Global,Norm}.lean`,
`GradientConvergence/AncientSecondInequality.lean` and
`LimitEquations/{ActualSlice,Spacetime,GlobalPairing,Cancellation,Smooth,
Exponential/HeatSlice,Exponential/Spacetime}.lean`.
Also read `ConjugateHeat/{Cutoff,CutoffPairing,Coordinates/Regularity,
Coordinates/GlobalRegularity}.lean`, `Soliton/Equation/{Potential,
EntropyEvolution,BackwardPotential}.lean`, the reduced-volume limit,
`Geometry/Riemannian/Heat/Energy/Cutoff.lean` and
`Geometry/Riemannian/Distance/{LocalApproximation,LipschitzApproximation}.lean`.

The exposition now proves the almost-everywhere Hamilton--Jacobi identity
before the heat inequality that uses it. It passes the second spatial
inequality through energy/flux convergence, justifies the exponential
Lipschitz test, and keeps the backward volume derivative. Finite chart
decomposition gives a positive global heat pairing. No smoothness is
assumed at this stage.

The mass proof retains the actual basepoints and embeddings. Source-ball
containment and injectivity transfer half the limiting distance, giving
the explicit quadratic lower bound. Polynomial ball volume and a convergent
Gaussian shell sum give uniform tails. Tangent-norm distortion gives both
Jacobian inequalities with factor C^n. Relatively compact exhaustion proves
one mass inequality; source-ball containment and a uniform tail prove the
other. The limits C down to 1 and epsilon down to zero are explicit.

The square-root moment and a single cutoff from the first backward slice
give the actual C/R flux bound. Local mollification with metric distortion
6/5, followed by a partition with summable value errors, constructs the
smooth distance approximation. Backward metric monotonicity preserves its
cutoff gradient bound on the whole slab. Lipschitz Green's formula controls
the integrated Laplacian, without assuming a pointwise Laplacian bound.
Dominated convergence gives vanishing product-test pairing. Positive tests
K chi eta plus/minus an arbitrary compact test force equality by linearity.

The coordinate forward equation is for rho u, not u against Euclidean
measure. Smoothness of its actual continuous representative and logarithmic
recovery are stated with local ellipticity; the shared interior weak-jet
producer remains under review. The tensor calculation now displays the
Laplacian, gradient-energy and scalar drifts and their square completion.
Zero entropy factor implies zero tensor in an orthonormal basis.
Flat Gaussian rigidity and retained geometric extraction remain pending.

Compared directly Morgan--Tian Corollary 9.26, Claims 9.27--9.29,
Corollary 9.30 and Claim 9.31, printed pp. 195--198. The implemented proof
keeps compact product tests throughout the positivity argument. The printed
proof of Corollary 9.30 on p. 197 also says non-positive where its statement
and the subsequent positivity argument require nonnegative; the sign
convention recorded above resolves the use in this book. These are
reported source discrepancies, not changes to formalization or references.

## Local Weak Regularity and Flat Gaussian Normalization

Read the canonical weak equation and `ForwardEquation.lean`, `Smooth.lean`,
the weak compact extension, mollified forcing and local energy producers,
`Interior/{ConstantEnergy,ConstantEnergyIdentity,PrincipalHessianBound,
VariableEnergy,UniformCutoffEnergy}.lean`, and the first/second/forced
energy producers under `Interior/Energy/`. Read the spatial and time jet
bootstraps, actual weak principal residual, differentiated test equation,
and L2 flux commutator under `Interior/Jets/`. The shared Sobolev
`Embedding/SmoothRepresentative.lean` supplies the finite exponent tower
and identification of the continuous representative; subordinate Sobolev
and Morrey inputs and their background locators remain to be reconciled.
All these paths are below `PoincareLib/Analysis/Parabolic/WeakRegularity/`
except the last, below `Analysis/Elliptic/Regularity/Sobolev/`.

The new lemma `lem:ancient-weak-regularity` states local positivity and the
actual adjoint test equation. It gives the scale-independent commutator
bound, first divergence energy estimate, weak-gradient identification,
constant-matrix Hessian coercivity, coefficient absorption and cutoff
estimate. The forced version uses already known weak gradients and L2
commutators, so differentiating never assumes the regularity being proved.
Spatial induction and the time equation produce all mixed weak jets.
Finite exponent iteration and Morrey embedding identify the original
continuous function, with neighborhoods allowed to depend on order.
The density application displays its expanded drift and zeroth term.

Read `AncientKappa/Asymptotic/Nonflat/Gaussian.lean`,
`Soliton/Flat/{Rigidity,Exponential}.lean` below the Ricci-flow directory,
and `Geometry/Riemannian/Coordinates/Exponential/FlatMetric.lean`.
The flat argument now constructs the zero of the potential directly,
determines terminal velocity, proves exponential injectivity and
surjectivity, and uses flat radial Jacobi fields to obtain the global
metric and measure identity. The exact potential normalization gives the
Gaussian mass contradiction on every chosen slice. Renamed the quadratic
tail constant to avoid collision with the Hausdorff-volume calibration.

Compared Morgan--Tian Proposition 9.20's regularity conclusion on printed
p. 198 and Claim 9.36 on pp. 202--203. The former invokes standard parabolic
theory; the latter uses the Euclidean universal cover and deck actions.
The implementation develops weak-jet regularity and a direct normalized
exponential argument. Imported weak-regularity headers citing pp. 207--208
do not locate this step in the Clay edition. Source and reference files
are unchanged. This completes these local proof expansions, not chapter
acceptance: retained extraction and the shared prerequisites remain open.

## Retained Geometric Extraction

Read `Asymptotic/{Theory,LocalCurvature,SpatialCurvature,FiniteCompactness,
Exhaustion,Limits}.lean`, `ReducedLength/{Harnack,TimeBounds,CenterBounds}.lean`,
`Compactness/{Windows,Input}.lean`, and
`Compactness/Nested/{Step,Family,Gluing,Limit,Diagonal,Embedding}.lean`.
Read the relative maps, extraction, distance, isometry, surjectivity,
inverse-limit, pointed and flow-metric producers, together with
`Coordinates/{DerivativeBounds,TransitionBounds,Smooth,MetricLimit}.lean`.
The local-isometry derivative mechanism was followed into
`Compactness/GeometricLimit/Overlap/JetBounds.lean` and the induction in
`Geometry/Riemannian/Coordinates/TransitionBounds.lean`. Read
`Inheritance/{Noncollapse,Volume}.lean` for the exact retained constant.
Paths here are under `Geometry/RicciFlow/AncientKappa/` unless their
different subject root is displayed.

Corrected an actual narrative mismatch: the implementation does not build
the ancient carrier as a direct union of nested spatial regions. It uses
global pointed diffeomorphisms between complete finite-window limits,
pulls every flow to the first carrier, and defines its metric through
exact overlap equality. Completeness is inherited slice by slice.
The draft now develops the comparison maps, compact confinement,
arbitrarily small distance distortion, reverse-image surjectivity,
inverse uniform convergence, Christoffel derivative induction and
preservation of all common-time metrics. A countable compact-jet diagonal
also retains domain containment and proves strict increase of the actual
source indices.

The two-time curvature bound now uses the global weighted reduced-length
comparison, the normalized basepoint bound 3n/(2 sigma^3), and integrated
Harnack at max(s,t). Its constant is independent of both earlier times.
The buffered finite-window input checks the actual small parabolic ball
and volume calibration. Limit noncollapse uses a strictly smaller radius,
compact-cylinder curvature margin, time-independent spatial maps and
the two Jacobian/radius volume inequalities; taking radii to the target
retains exactly kappa. Metric-sphere nullity is explained through the
complete exponential.

Direct comparison with Morgan--Tian Claims 9.15--9.16 and Corollary 9.17,
printed pp. 186--187, places these arguments at the end of Section 9.2.1.
Section 9.2.2 starts on p. 187 and concerns the potential. Several source
headers instead locate finite-window compactness at Section 9.2.2,
pp. 184--185; recorded here as a locator correction without source edits.
The historical diagonal argument and this explicit compatible-window
construction serve the same conclusion; no novelty claim follows.
The shared full compactness construction, coordinate/measure background
and the potential extraction remain review obligations.

## Potential Extraction on the Retained Manifold

Read `ReducedLength/{TemporalBounds,TimeGrowth,SpacetimeBounds,
CoordinateBounds}.lean` and the ancient extraction files
`{Actual,ActualMass,LimitRegularity,Limit,CompactBounds,CylinderBounds,
MetricBounds,CylinderCover,UniformLimits}.lean`. Followed spatial
exceptional-set integration into
`Analysis/Calculus/WeakDerivative/DistanceBound.lean` and compact bound
propagation into `Analysis/Asymptotics/LocalOscillation.lean`.

The former two-sentence potential extraction now gives the actual
mechanism: both weighted time comparisons, the scale-independent
quadratic center bound, coordinate metric control at the earliest slice,
and the square-root derivative estimate. Translated segments and Fubini
justify integration even when the original segment lies in the cut locus.
The set of points with eventual bounds is nonempty and clopen by local
oscillation; connectedness and a finite subcover give a compact uniform
bound. This avoids assuming a basepoint-centered chart covers an arbitrary
compact set. Squaring and weighted time comparison give the stated
spatial and temporal Lipschitz constants on each cylinder.

The countable cylinder diagonal, overlap identification, positivity,
compact-uniform convergence and Lipschitz limit are developed. Reselecting
the geometric convergence retains the same limit carrier and metric,
and restriction to the earlier nested domain/window preserves each
embedding. Added the explicit dimensional observation that nonflatness
excludes dimensions zero and one before using local positive-dimensional
analytic arguments.

Directly compared Morgan--Tian Section 9.2.2, pp. 187--188, and Remark 9.19,
p. 188. The latter's warning that the limit is not asserted to be a reduced
length based at a point in the ancient limit is now explicit. Claim 9.15,
p. 186, uses a linear upper growth estimate after normalized time one;
the implementation uses a weaker quadratic bound obtained from
|ell_tau| <= 2 ell/tau, sufficient for each compact positive-time interval.
No stronger uniform-in-time bound is claimed. Original reduced-length
variation, full-measure regularity and the shared compactness producers
remain review interfaces; the chapter is not accepted.

## Signed Neck Flux and Whole-Carrier Escape

Read the neck `Separation/Scale.lean` proof through its signed consumers
in `Flux/IntegralBounds/{ScaleComparison,Directional,Oriented}.lean`,
`Flux/{Directional,Volume,ModelVolume}.lean`,
`Flux/WeakComparison/Oriented.lean` and `Flux/Cutoff/Oriented.lean`.
Followed the weak sign into
`Geometry/Riemannian/Soul/BusemannWeakLaplacian.lean`.
The draft now defines the distance-minus-time Busemann function, derives
its nonpositive weak Laplacian by distance comparison and dominated
convergence, and obtains the nonnegative differential pairing by Green's
identity. Corrected the former unexplained appeal to convexity.

The scalar-normalized cylinder, both orientations of the outward profile,
compact test T1-T2, and exact volume and axial-covector factors are now
explicit. Only the inner neck uses directional alignment; the outer bound
uses the Lipschitz estimate. The inequalities give A s1^2/8 <= 8 A s2^2,
hence s2 >= s1/8, with the negative outward flux sign retained throughout.

Read `Separation/EscapeCarrier.lean`, soul
`Separation/{Neck,Surrounding,Ordering,DistanceMaximum,BoundaryDistance}.lean`,
neck `Separation/{Depth,Depth/Points}.lean`, and
`Flux/Cutoff/DepthProfile.lean`. Developed whole-carrier escape at fixed
epsilon, compact closure of a fixed neck, radial boundary maxima and
the frontier-diameter estimate. Developed the actual global smooth
bump depth argument, which controls ambient paths leaving the neck.
The radial homeomorphism and ambient complementary-region producers
remain distinct inputs; their definitions have been inspected but their
full constructions are not yet accepted.

Directly compared Morgan--Tian Definition 2.18, Proposition 2.19 and
Lemma 2.20, printed pp. 31--32. The implementation uses fixed unit-slab
profiles, one signed inner estimate and a coarse outer bound, yielding
R2 <= 64 R1 rather than the printed asymptotic estimate R2 <= 2 R1.
Both suffice for the scale contradiction. The source's justification of
almost-everywhere differentiability by saying the gradient is L2 is
insufficient on its own; the implemented proof uses Lipschitz regularity
and Rademacher. The source's distance-sphere isotopy route to soul-side
separation differs from the implemented radial-maximum and cutoff-depth
route; no novelty claim follows.

Read the long calibrated-segment consumer in
`Separation/{Calibrated,Ray,Segment}.lean` and alignment consumers
`Geodesic/{Axial,Threshold,Long,Pairing}.lean`. Their lower calibrated-ray,
intrinsic competitor, first-metric-jet and scalar window producers still
need review and exposition before equation (E) is discharged. The
unbounded-curvature-to-small-necks reduction is also still an input.
Neither this flux development nor the published proof build accepts the
neck obstruction, asymptotic classification or whole chapter by itself.

## Calibrated Segments and Uniform Axial Alignment

Followed `Geometry/Riemannian/Soul/CalibratedRay.lean` and
`Neck/Flux/BusemannGradient.lean` through the compact-limit coray,
smooth segment replacement, endpoint Lipschitz squeeze, and equality
in Cauchy--Schwarz. The exposition retains the same ultrafilter for
all parameter limits; it does not presume the metric coray was already
a smooth geodesic. A sufficiently distant calibrated endpoint lies
outside both the compact side and the closed half-neck slab.

Developed first exit, the s/(8 epsilon) length lower bound, and the
outward sign. The latter uses a later frontier crossing, the initial
distance bound to every frontier point, and the previously developed
global depth cutoff. Both coordinate orientations are retained.

Read `Geodesic/{Interval,Intrinsic,Alignment}.lean` and followed the
metric derivative into `Geodesic/Jets.lean`,
`Geodesic/Jets/{Centered,Coefficients,Reparametrization,Ellipticity}.lean`,
and `Geodesic/Acceleration{,/Estimate,/Hessian}.lean`.
Developed the centered stereographic model derivative, first covariant
jet evaluation, finite coordinate expansion, ellipticity and inverse
bound, three-term Koszul estimate and unit-tangent scaling.
These give the actual universal axial acceleration K epsilon/s^2.
The intrinsic competitor interpolates both spherical and axial
coordinates and stays in the cylinder interval.

The s/(200 sqrt(epsilon)) window now gives an explicit normalized
speed lower bound tending to one, uniformly in the neck scale.
Nonvanishing derivative and endpoint orientation determine its sign.
The bilinear pairing errors give squared tangent error at most
2 beta + 5 epsilon. This completes the displayed inner Busemann
direction estimate, conditional on the stated complete-geodesic and
metric-jet background, with no appeal to later ancient classification.

Directly compared Morgan--Tian Lemma A.4, printed pp. 498--499.
Its last paragraph appeals to continuous dependence of minimizing
geodesics on the metric. Such a statement needs qualifications at
nonunique minimizers and on intervals whose lengths grow as epsilon
shrinks. The implementation instead supplies the uniform window
argument developed here. The statement's length threshold and
orientation are preserved after arbitrary-scale rescaling; no novelty
claim is made. The point-soul construction, ambient sphere separator,
and curvature blow-up reduction remain unresolved, so the enclosing
neck obstruction and the chapter remain unaccepted.

## Ambient Collar Separation Before Classification

Read `Topology/Manifold/Separation/{Sign,Connected,Components,Bounded}.lean`
and `CanonicalNeighborhood/Neck/Separation/{Ambient,Ordering}.lean`.
Added a self-contained collar-side lemma before the asymptotic-limit
classification proof. The clamped transverse coordinate descends to a
circle map constant off the compact inner collar. Its normalized real
lift agrees with the coordinate on the entire connected collar and has
exactly the central sphere as zero set. The proof identifies both sign
sets as connected by ruling out a component missing the collar, obtains
their common boundary, and uses the connected Euclidean exterior to
identify the bounded side and its compact closure.

Developed strict nesting for disjoint connected separators with a common
point on their bounded sides, using connected unbounded complementary
regions and the boundary identities. Carrier connectedness upgrades this
to the whole-neck inclusions needed by the flux test.

Directly inspected Hatcher Propositions 1.33--1.34, printed pp. 61--62,
for the ordinary lifting input, and Proposition 2B.1(b), pp. 169--170,
for the historical comparison. The implementation's collared-case proof
uses circle lifting, not the latter's homology induction. It does not
assert that either closure is a ball, supply an isotopy, or discharge
the separate ambient Schoenflies review. Those stronger inputs remain
open where used elsewhere in the book.

Refined the annotated outline to put these static geometric inputs
before ancient classification, avoiding dependence on M27 in the later
neck/cap chapter. The point-soul package was followed through its actual
singleton horoball, Euclidean-flow and radial-flow composition; its
substantive lower construction remains unresolved. No chapter acceptance
or global coverage claim follows from the new separation lemma.

## The Actual Singleton Busemann Level

Followed the point-soul composition through
`Geometry/Riemannian/Soul/Point{,/Terminal}.lean`,
`Point/Terminal/{Construction,MaximalDepth}.lean`,
`Point/Terminal/StrictCurvature/Busemann/{Rigidity,StrictLevels,Concavity}.lean`,
and `Point/Terminal/StrictCurvature/Hessian/{UniformSupport,Distance,
Transform,Inverse,Radial}.lean`. Read the retained affine index comparison
and endpoint-ball contribution in `StrictCurvature/{IndexComparison,
EndpointBall}.lean`, together with
`Soul/{Horoball,CompleteGeometry,BusemannConcavity}.lean`.

Added the precise singleton-level lemma before the ambient collar lemma.
It defines the intersection over all based ray Busemann functions,
derives every-geodesic concavity from normalized squared-distance upper
supports, and develops compactness by extracting a forbidden ray in a
noncompact convex level. Calibrated corays and the Lipschitz bound give
both inequalities for complement distance, hence the exact inner-parallel
level shift. Compact maximization and a short segment toward the complement
give the nonempty maximal-depth level with empty ambient interior.

Developed the strict improvement with its quantifier order: a fixed
positive-curvature neighborhood supplies a common endpoint ball; the
quarter-segment Calabi support retains the terminal affine curvature
integral and the full radial-square subtraction. The explicit coefficient
is bounded above by -kappa rho/6 for sufficiently distant sources.
The increasing transform 1-exp(-u) adds the missing radial negativity.
After ray-parameter normalization a common upper value bound gives one
positive quadratic margin for every based ray and every nearby endpoint.
The upper-support criterion and pointwise limits retain that margin.
A midpoint gap uniform over all rays yields one strictly smaller level,
contradicting empty interior and proving the singleton assertion.

Directly compared Maeder-Baumdicker--Seidel Lemma 3.13(i), printed
pp. 17--19 (the whole lemma continues through p. 20), Morgan--Tian
Theorem 2.7 and discussion, pp. 25--27, and the archived Petersen third
edition. Petersen Lemma 12.4.8 is on printed pp. 467--468, PDF pages
480--481; the lemma's p. 467 was also visually inspected. Its distance-to-
boundary support proof differs from the implemented uniformly transformed
ray supports. Lean headers citing pp. 461--462 do not match this PDF.
The retained reference README's blanket offset +19 is also unreliable
for this locator; no reference or Lean file was changed. PDF SHA-256:
`f723542b3c4f6c20e67f7c7842ea9d12afb788e557fb3058b31e5231c58d5a8e`.
Added the third-edition entry to the publication bibliography.

The common Calabi inverse branch, index-form nonnegativity, curvature
neighborhood and squared-distance support constructions still need their
shared exposition reconciled; this lemma is not a certificate that those
lower producers were independently reviewed in full. The Euclidean and
distance-radial outward-flow constructions remain the next point-soul
obligation. Whole-chapter acceptance remains pending.

## Complete Outward Flow and Both Coordinate Constructions

Followed `Soul/Point/Flow/Outward/{BusemannGap,DistanceGap,Neighborhood,
Field,Center,Gluing,DistanceAscent}.lean`, `Flow/{CenteredGlobal,
DistanceEvolution,TrajectoryCoordinates,RadiusReparametrization,
DistanceCoordinates,RadialFromFlow}.lean`, and `Topology/Flow/Radius.lean`.
Also read `Riemannian/Flow/{CenterNormalization,Normalization,BoundedSpeed,
Euclidean}.lean`, `Manifold/Flow/{RadialConjugacy,RadialExtension}.lean`,
`Distance/NormalSphere.lean`, `Coordinates/Exponential/Gauss/SquaredRadius.lean`,
and the scalar `Analysis/Calculus/MeanValue/UpperSupport.lean`.
These paths are under `PoincareLib/Geometry/` except the explicit topology
and analysis paths; the production source pin remains
`751329327f4f582797bda8e6cffe7cdf7531cc1d`.

Replaced the pending-flow paragraph with a precise lemma preserving the
same singleton point for both conclusions. The proof develops the
separating ray, distant finite squared-distance gap, and one smooth
potential with a positive derivative against every minimizing inward
direction on a whole neighborhood. The last quantifier is obtained by
a fixed short segment, a compact Hessian bound and a small majorant
deficit, not by assuming continuous choices of minimizing directions.

Developed the partition-of-unity inequality, exact center potential,
cutoff gluing and a positive bounded-speed rescaling equal to one near
the center. Compact confinement gives completeness. First-variation
upper supports are applied in reversed time; a positive margin on each
finite orbit segment proves strict increase of actual distance even at
cut points. Compact forward and backward orbit closures prove that all
positive radii are attained. The draft includes the scalar support
mean-value argument rather than treating distance as differentiable.

For the smooth conclusion, developed the Euler-field identity from
Gauss's lemma, exponential local conjugacy and the global chart by
fixed-time formulas. Both the chart and its inverse are smooth locally
with one fixed time; smooth hitting times are unnecessary. For the
distance-radial conclusion, first ensured that the entire small metric
sphere lies in the normal chart, then developed the level-times-time
homeomorphism and joint continuity of the ordered inverse. This yields
actual-distance coordinates without asserting smooth distance spheres.

Directly re-read Morgan--Tian printed p. 27 (PDF page 70). That discussion
describes the outward flow from acute minimizing directions and refers
out for the soul theorem. The implementation instead extracts a common
potential from the defining singleton horoball and squares distance near
the center. This is a precise construction choice, not a novelty claim.
The reference to a field vanishing at the soul while agreeing near it
with the distance gradient is not used literally: the implemented smooth
field is half the squared-distance gradient near the point.

Shared Calabi inverse branches, index-form comparison, first-variation
supports, normal-ball geometry and their cross-chapter exposition still
require reconciliation. Local smooth ODE existence, uniqueness and
continuation are ordinary background; the compact-confinement mechanism
is stated in the proof. No whole-chapter acceptance follows. The next
ancient-specific gap is the curvature blowup producing small necks used
by the static flux obstruction.

## Same-Slice Reduction and Compact-Ball Selection

Read `Soliton/ThreeDimensional/Asymptotic/Curvature/{Bounded,SmallNecks,
Dichotomy,NullSplitting,PointSelection,BufferedLimit,Line,Noncollapse,
SelectedRoundFactor,RoundBlowup,RoundNormalization}.lean` under
`PoincareLib/Geometry/RicciFlow/`. Followed the null alternative into
`ThreeDimensional/Splitting/Global/NullScalar.lean` and
`Global/Surface/Scalar.lean`; the latter uses the raw complete-surface
shrinker theorem rather than a bounded ancient-solution premise.
Read `PoincareLib/Analysis/Parabolic/PointPicking.lean` in full.

The earlier phrase "lifted slice" was potentially misleading: the small
neck and boundedness wrappers use `ULift`, a diffeomorphic type-universe
copy, not a geometric cover of a different metric manifold. Corrected
the mathematical narrative to keep the original slice. The actual
unit Ricci-kernel cover in the null branch is a separate finite covering
construction and remains explicitly identified as such.

Developed the noncircular null alternative: normalize by inverse absolute
time, use the raw null-plane product and the already developed complete
surface shrinker lemma, and descend the scalar identity by the surjective
local isometry. This gives scalar -1/t and contradicts unboundedness;
strict sectional positivity and Euclidean topology then follow.
The shared local curvature/partial-trace foundations remain under review.

Developed compact-ball point selection using the precise displacement
budget d(x,q)+2L/sqrt(R(q)) <= d(p,x)/2. Doubling terminates by continuity
on one proper closed ball, with no global curvature bound. Choosing the
starting points outside radii 2(i+1)^2 and dividing the controlled radius
by i+1 retains diverging normalized radius while making its ratio to the
base distance tend to zero. The retained scalar time monotonicity gives
the backward bounds 4Q on scalar and 36Q on the adopted tensor norm.
The rescaled flows are the actual Q_i h(t_0+u/Q_i), normalized at zero.

Compared Morgan--Tian Corollary 9.38 and Proposition 9.39, printed
pp. 204--205, and Corollary 9.53, p. 217, directly. The draft now keeps
local selection separate from global boundedness and records the extra
buffer, projective-factor exclusion and terminal-transfer steps.
Those steps and the subordinate selected-line comparison are not yet
discharged merely by reading their composition wrappers. The broad
coverage and chapter acceptance gates remain pending.

## Antipodal Exclusion and Quantitative Terminal Necks

Read `Geometry/Manifold/Immersion/{Even,AntipodalCollar}.lean` and
`RicciFlow/Soliton/ThreeDimensional/Asymptotic/Curvature/{SphereCover,
AntipodalExclusion,CylinderNormalization}.lean`. Added the full odd-
determinant proof of the collar obstruction and its application through
one compact slab of the stored convergence embeddings. It only needs
a local diffeomorphism on that slab; it neither invokes nor establishes
ambient Schoenflies. The round-surface covering dichotomy is the
previously developed covering input and remains part of the shared
space-form review.

Read `CanonicalNeighborhood/Neck/Convergence/Terminal/{AncientNeck,Neck,
Closeness,Jets}.lean`, `Convergence/Bounds/Terminal.lean`,
`Harnack/Noncompact/CurvatureControl/Cylinders/Expanding/{LimitScalar,
ScalarTime,ParametrizedTerminalJets,TerminalJets}.lean`,
`Cylinders/ScalarTime.lean`, and
`Compactness/Convergence/Terminal/SpatialJets.lean` under
`PoincareLib/Geometry/RicciFlow/`. Developed a standalone buffered-to-
terminal cylinder lemma with its source hypotheses and quantifier order.

The proof fixes scalar evolution and local derivative constants before
the buffer. It obtains 1-D delta <= s <= 1 and s >= 1/2; retains the
actual spatial embeddings; propagates their metric jets using uniform
ellipticity, covariant curvature bounds and affine highest-jet evolution;
and integrates to get B delta. The scalar-normalization error is bounded
by 2D Z delta. A fixed compact-slab coefficient comparison gives the
explicit squared error and a tolerance chosen before any limit. The
terminal neck has scale one and the actual terminal metric, connection,
center and coordinate map. Rescaling back gives exactly Q_i^(-1/2).

Read `Soliton/ThreeDimensional/{LimitNoncollapse,Noncollapse}.lean` and
developed the radius-nine loss giving static kappa/729 before boundedness,
the radius-one-sixth volume input, and the product-factor kappa/1458.
The enclosing reduction now states how the same selected convergence is
retained through the buffered limit, surface factor, antipodal exclusion
and terminal transfer, with the buffer tolerance selected first.

Compared Morgan--Tian Proposition 5.14, printed pp. 90--91, Proposition
9.39, pp. 204--205, and Corollary 9.53, p. 217. Also directly read
Kleiner--Lott Theorem D.1, printed p. 2847, and Appendix E, pp. 2848--2849
(PDF pages 261--263). The draft cites these exact locators. The source
comparison does not replace exposition of the local estimates: their
controlled-cylinder confinement, derivative producers and shared
fixed-coordinate evolution foundations remain to be reconciled.
The selected-line comparison, complete pointed compactness and static
noncollapse passage on this exact retained limit remain open below the
composition level. No chapter acceptance or final rendering is claimed.

## Selected Lines Without a Volume Premise

Extracted the geometric selected-line lemma before its first use.
Its hypotheses concern one complete nonnegatively curved source slice,
escaping centers, diverging normalized distances and control radii, a
fixed backward buffer with a local Ricci upper bound, and the supplied
complete pointed convergence. The zero-buffer case requires only the
terminal metrics. Replaced all three uses: unscaled shrinking-model
limits, unbounded-scalar asymptotic selection, and the later positive-AVR
limit. The first two no longer refer into a theorem assuming positive AVR.

Read the actual producers under
Harnack/Noncompact/AncientVolume/Splitting/: SelectedComparison,
SelectedEndpoints, EndpointSelection, BufferedSegments,
DistanceDistortion, SmallSelectedLine, CompleteCoverage, and
LineLimit. The corresponding-side and hinge premises are supplied by
the intrinsic nonnegative-sectional-curvature comparison; review of its
underlying Jacobi/index-form construction remains shared work.

Retained the convergent initial directions and farther vertices in the
original metric, scalar normalization, trimmed diverging radii with
margin 4 exp(Lambda delta), and the same limit through all subsequences.
Expanded the end-cutoff index estimate giving a buffer error independent
of the diverging radius, the squared-cosine squeeze, and earlier minimizing
segments. Expanded completeness-based source-ball coverage by first exit,
both distance comparisons for moving inverse images, and the common
ultrafilter producing a line through the actual limit basepoint.

Directly compared Morgan--Tian Theorem 5.35, printed pp. 100--102
(PDF pp. 143--145), with Kleiner--Lott Proposition 41.13, p. 2678,
and Appendix G, p. 2852. The source comments' pp. 122--123 refer to
the arXiv edition; publication citations now use the archived book's
printed pagination. The buffer and retained-embedding passage are explicit
in the exposition. No curvature-factor divergence, global curvature bound,
or positive-volume premise was added to the geometric lemma.

This resolves the section-level interface, not the shared comparison,
complete-geodesic, compactness or later splitting foundations. Those
remain pending; no whole-chapter acceptance follows.

## Shared Comparison Interface Reconciled

The Ricci-flow draft now contains lem:rf-squared-distance-comparison
with the actual index, no-conjugacy, inverse-branch, approximate-support,
hinge and two-chord mechanisms. Read and compared its producers as
recorded in ricci-flow-integration-v4.md. The selected-line proof,
every-geodesic concavity of Busemann levels, and outward-flow distance
support now refer to that shared lemma. This supersedes the pending
hinge/corresponding-side and basic shifted-support entries above.
The positive-curvature terminal index improvement, other analytic
compactness inputs and full chapter review remain distinct obligations.

## Static Noncollapse on the Same Limit

Reconciled the shrinking-model limit, unbounded-scalar cylindrical
reduction and later kappa/27 limit with the shared lemma
lem:rf-limit-static-noncollapse. Its proof, recorded in the Ricci-flow
review, develops arbitrary-center image coverage, curvature margins,
ball-volume convergence at every radius and passage to the full radius.
This supersedes the pending static-noncollapse-passage descriptions
above; construction and completeness of the supplied limit remain
separate review obligations. The same original convergence embeddings
and existing constants are retained. No whole-chapter acceptance.

## Uniform Positive Curvature and the Terminal Index Term

Reconciled the singleton proof's strict terminal-index estimate with
the now-developed common inverse-branch and index arguments. Re-read
Soul/Point/Terminal/StrictCurvature/{IndexComparison,LocalIntegral,
EndpointBall,LowerBound,Uniform} and Hessian/UniformSupport.
Expanded the actual compactness device for varying tangent planes:
transport pairs into a fixed tangent space, add the three squared
normalization errors to the curvature numerator, minimize on a product
of radius-two closed balls, and retain a common positive margin nearby.
Actual orthonormal pairs have bounded inverse transports and zero
penalties. The Gram-determinant identity supplies the bound for arbitrary
pairs, including dependent ones.

The quarter-shift branch now refers to the shared reversal proof.
Parallel transport retains the endpoint norm and radial pairing; the
last rho units of length lie in the positive endpoint ball. The existing
explicit integral in (S3), its negative coefficient, exponential transform
and common ray-independent concavity margin agree with these producers.
This resolves the basic curvature-neighborhood and terminal-index
dependencies previously listed as pending for the singleton lemma.
Whole-chapter and other compactness reviews remain pending.

## Weak Parabolic Regularity

Reviewed the local regularity lemma against the actual producer chain
under Analysis/Parabolic/WeakRegularity. The draft now identifies the
WeakSolutionOn distributional predicate, local compact-ball ellipticity,
the mollified principal residual, forced second-jet energy construction,
spatial and time jet induction, the volume-preserving spacetime split,
and the Sobolev smooth-representative identification.

Pointwise positive definiteness is used only after shrinking to a
compact ball, where a uniform eigenvalue lower bound is obtained. The
argument therefore does not smuggle in global uniform ellipticity.
The local chain matches Morgan--Tian Proposition 9.20, pp. 207--208
(Clay edition pp. 188--198) and the cited Evans sections. The chapter
remains pending while later asymptotic and compactness interfaces are
reviewed.

## Asymptotic Equation Producer Chain

The asymptotic theorem was reread from its conclusion back to the source
producers. Reduced-length Harnack bounds provide curvature on buffered
windows; the nested compactness assembly, window restrictions, relative
distance control, ball coverage, and strict-radius volume squeeze then retain
one complete carrier across overlapping times. The nested diagonal supplies
all space-time metric jets on the exhausting coordinate sets. The relevant
source families are `AncientKappa/Asymptotic/Bounds`,
`Asymptotic/Compactness/Windows`, `Asymptotic/Compactness/Nested/Assembly`,
and `Asymptotic/Compactness/Nested/Diagonal`.

The potential is extracted only after this geometric diagonal. Connected
local oscillation bounds and overlap agreement give a common locally
Lipschitz limit; Gaussian shell estimates preserve the actual mass. The two
weighted comparison inequalities pass to weak heat and Hamilton--Jacobi
identities through the compactly supported gradient-energy and cutoff
estimates in `Asymptotic/ReducedLength/GradientConvergence/AncientEnergy.lean`
and `AncientHamiltonJacobi.lean`. Local uniform convergence alone would not
pass the quadratic gradient term. The weak equality is then upgraded by the
regularity producer chain documented in the new `lem:ancient-weak-regularity`
entry.

The backward-potential sign conversion is supplied by
`Soliton/Equation/BackwardPotential.lean`; the entropy evolution identity in
`Soliton/Equation/EntropyEvolution.lean` identifies its defect with the square
of `Ric + Hess f + (2t)^{-1}h`, so the weighted vanishing argument yields the
stated soliton equation. The later smooth negative-gradient flow and pullback
metric identity come from
`Soliton/ThreeDimensional/Asymptotic/SelfSimilarity/Regularity.lean` and
`MetricIdentity.lean`, rather than from a certificate wrapper. This agrees
with Morgan--Tian Proposition 9.32 and Lemma 9.33, pp. 200--202. The chapter
remains pending: compactness and energy interfaces still require independent
mathematical review.

## Annular And Cone Source Boundary

The finite positive scalar-ratio branch now has an explicit source trace.
`ScalarRatio/Annular/Normalization.lean` chooses the radial margin and normal
radius from the tail bound; parabolic noncollapsing gives whole-past curvature
control. `Annular/SpacetimeCompactness.lean` and `ClosedCompactness.lean`
retain mixed jets through the closed time-zero boundary, and
`Annular/FlowRealization.lean` plus `AncientLimit.lean` construct the actual
local ancient flow with nonnegative curvature and terminal scalar one.
`LimitCurvature.lean` supplies the curvature transfer. This is a local flow
construction, not a complete cone or a certificate shortcut.

The zero-ratio source boundary is separate. `Cone/ZeroRatio/Potential.lean`
and `Limit.lean` construct the distance-normalized flat annular limits;
`Cone/ZeroRatio/Backward/EnclosedLimit.lean` and `GlobalEnclosedLimit.lean`
construct compatible enclosing charts and the global smooth isometric
immersion. The lower-distance theorem only controls ambient distances inside
the convergent enclosing charts. The link identification and volume rigidity
are subsequent arguments in `Cone/Metric/AnnulusApproximation.lean`,
`BallApproximation.lean`, `RadialIdentification.lean`, and `VolumeRigidity.lean`.
The radial variation still depends on the intrinsic corresponding-side
Toponogov comparison; coefficient convergence does not supply that input.

The chapter remains pending. The source trace resolves the local producer
interfaces, while annular overlap quantifiers, cone chart coverage, the
backward separation estimate, and the dimension-reduction inequalities still
need independent source and readability checks.

The independent cone audit found one substantive issue now corrected in the
draft: per-ray embeddings do not by themselves provide a common positive
radius or a common subsequence. The exposition now invokes
`ZeroRatio/Source/BackwardFlatAnnulus.lean`, whose aggregate theorem supplies
the shared radius, diagonal, overlap atlas, backward jets, compact unit-slice
neighborhood, and annular coverage. The Euclidean unit-umbilic step is tied to
`ZeroRatio/Backward/SourceLimit.lean`, including its full-flow hypotheses and
dimension shift. The volume paragraph is tied to the packaged ray-projection
producers in `Metric/VolumeComparison.lean` and `Metric/RiemannianVolume.lean`;
the chapter retains the direct argument as readable explanation. The audit
initially asserted that the cutoff interpolation could not preserve the
radial Gauss identity. That assertion was wrong: both coefficient forms
satisfy the same pointwise linear identity, and the convex combination
retains it. The direct source correction and replacement of aggregate
invocations by the actual coverage argument are recorded below. The exact
named consumers traced at this stage were:
exists_backward_enclosing_euclidean_charts,
exists_global_enclosed_smooth_limit,
nonempty_chordal_sphere_isometry_of_unit_umbilic,
asymptoticCone_radial_unit_ball_volume_of_chordal_isometry, and
curvatureTensor_eq_zero_of_asymptoticCone_volume_ge_euclidean. The text
describes the geometric mechanism. The earlier concern about measurability
of the ray projection was also overstated: its Lipschitz outer-measure
bound applies on arbitrary subsets. The formal measurable extension is
an available implementation, not an additional mathematical obstruction.

## Uniform Cone Charts And The Unit Slice

Re-read `ZeroRatio/UniformCharts.lean`, `ChartFamily.lean`,
`FlatChartFamily.lean`, `ChartCoverage.lean`,
`Family/{Embedding,Realization,RadialRealization,Coverage,OpenCharts}.lean`,
`Source/{UnitNeighborhood,Neighborhood,BackwardFlatAnnulus}.lean`,
and `Cone/Metric/Family/Annular.lean`. These implement the local annular
construction in Kleiner--Lott, corrected 2013, Theorem 41.2, Case 2,
printed p. 2677. The chapter now develops their common-radius and coverage
arguments in place of invoking the aggregate result.

The zero-ratio threshold for A = 1/(n^2+1) yields whole-past curvature at
most 4 on a terminal radius-1/4 ball about every normalized exterior center
of radius at least 3/4. Closed-time-cylinder noncollapsing at radius 1/8
gives the same volume lower bound at every center. The local injectivity
estimate therefore fixes one positive chart radius before any ray choice
or diagonal. Radial estimates give uniform ellipticity on one smaller
ball; the normal-coordinate jet bounds and a countable compact exhaustion
give one coefficient subsequence for all charts.

The earlier audit's claim about loss of the Gauss identity is retracted.
`Comparison/Injectivity/PullbackExtension.lean`,
`exists_uniform_extension_of_quadratic_bounds`, proves the global identity
directly for C = chi B + (1-chi) delta. Both summands have radial pairing
<x,v>, so the convex combination has the same pairing everywhere. The
chapter includes this calculation and derives d_h(0,x) = |x| by radial
length and Cauchy--Schwarz. Only flatness and coefficient-germ agreement
are restricted to the retained inner ball. The corrected statement agrees
with `FlatChartFamily.lean`; no formal source was changed.

The common annular relation has vanishing distortion for all related pairs,
not just each chart separately. Compact cone-annulus limits along a common
free ultrafilter preserve cross-distances and actual ray centers. Finite
nets upgrade to uniform convergence on each compact coordinate ball.
`Family/RadialRealization.lean` then extracts an ordinary increasing
subsequence retaining all normalized source-radius limits, with the first
m+1 charts controlled to error 1/(m+1). This extra extraction had been
omitted from the prose and is now explicit.

Actual normal-chart target coverage proves cone-ball coverage: approximate
a cone point within the center radius by a source point, use distortion to
place it in the source ball, and use the inverse normal chart and exact
radial identity to retain its coordinate preimage in a compact ball.
Uniform cone convergence and closedness of the compact image give
surjectivity onto that cone ball. A radial margin keeps this argument in
the full cone. The global Gauss identity preserves the covered radius
when restricting to the common backward-jet radius.

The 1/2 and 3/2 tangent-norm bounds give an open embedding on the Euclidean
radius-a/4 ball and coverage of the center cone ball of radius a/8.
The cross-distance zero relation descends these maps to the existing
overlap quotient. Their openness makes the quotient realization open;
their exact cross-distances make it injective. Dense centers and the
common covered radius contain the whole unit slice. Its preimage is
compact by continuity of the inverse on the image. The earlier audit's
suggestion that properness was additionally needed is retracted.
Finite relatively compact chart neighborhoods then give the domain for
the subsequent patching construction.

An independent source/readability pass checked the expanded text and found
no further substantive gap in this bounded construction. The spatial
agreement ball and the final common radius are explicitly restricted
before using backward convergence or compact cone realization.
This resolves these local quantifier and coverage gaps. Backward enclosing
geometry, global immersion and remaining chapter interfaces still require
their full review; this is not chapter acceptance.

## Neck And Point-Soul Interface Reconciliation

The source-path remarks added during integration belong here rather than
in the mathematical chapter. The earlier sections "The Actual Singleton
Busemann Level" and "Complete Outward Flow and Both Coordinate
Constructions" record the construction and precise source families;
"Ambient Collar Separation Before Classification" records the separate
collar and nesting proof. The draft's pending remark now acknowledges
these developments instead of incorrectly saying the point-soul
parametrizations have yet to be constructed. Shared geometric prerequisites
and whole-chapter acceptance remain pending.

Re-read `CanonicalNeighborhood/Neck/Separation/Scale.lean` and
`Soliton/ThreeDimensional/Asymptotic/Curvature/Bounded.lean` in full.
The scale theorem selects a universal positive epsilon threshold before
the manifold and metric; its positive lower scale bound is selected after
the complete strictly positively curved metric and the fixed epsilon.
The boundedness consumer first fixes the original negative-time slice,
gets that slice's lower bound, and requests a smaller neck on that same
slice. Its `ULift` is only type transport. The preceding signed-flux review
records the actual submodule paths, including
`Flux/IntegralBounds/{Directional,ScaleComparison}.lean` and
`Flux/WeakComparison/Oriented.lean`.

## Whole Components And Uniform Scale Bounds

Re-read the complete `Projective/Levels/{Graph,Capture,Transport}.lean`,
`Projective/Scale.lean`, `Geometry/Smoothing/ControlledTransport.lean`,
`Geometry/TransportComponentDiameter.lean` and
`Geometry/Smoothing/ComponentDiameter/Uniform.lean` under
`AncientKappa/Compactness/Boundedness/`. Read the graph differential and
tangent-norm arguments in `Projective/Levels/GraphMetric.lean` through their
completed proofs. This pass checks component capture and constant order;
it does not re-certify the earlier smoothing or complete-limit producers.

The source chooses the fixed metric's radial constant l first, then W,
then the neck accuracy threshold. Independent native review found that
the initial prose restriction `W < epsilon^(-1)` was insufficient for
the half-neck first-exit displacement. The draft now retains the actual
`Projective/Geometry/SignedSegments.lean` choice
`epsilon_0 <= 1/(4(W+1))`, ensuring `W < 1/(4 epsilon)` before
claiming displacement at least `1/(4 epsilon)`. This correction leaves
the threshold independent of the remote point and neck scale.
The closed central slab is contained
in the regular band by
`(2 W + 4 (pi + 1)) s <= 1/2` and the exhaustion's Lipschitz bound.
This implication is now explicit in the chapter. The smoothing value
error is `min s (1/8)`; its Hessian error is independently decreased
after the band gradient lower bound is fixed. The transport estimate
is expansion at most two, not a nonexpanding retraction.

The graph theorem alone gives the level-set equality inside a slab.
The chapter now explains the additional step in `Capture.lean`: local
diffeomorphisms have open slab images, so the graph image is relatively
open in the ambient level; compactness and Hausdorffness make it closed.
Connectedness then identifies exactly one whole component. The exact
antipodal fiber relation gives even height, while the graph differential
bound uses no global injectivity. With gradient bound 2 and axial lower
bound `(l/2) s`, that bound is `2 s (1 + 8/l)`.

Finally the compact upper level and continuous bijective transport give
a homeomorphism onto the lower level. Thus every pair in its corresponding
lower component has preimages under the spherical parametrization.
The norm bound and a sphere path of length at most pi give diameter
at most `4 pi s (1 + 8/l)`. The lower diameter constant is independent
of both the smoothing and collar width. These component and quantitative
transport obligations are reconciled with the draft; the remaining
shared source and whole-chapter review obligations below remain open.
The independent reviewer found no further substantive mismatch in this
bounded graph/transport pass after the capture and inverse arguments
were made explicit. This is not acceptance of the whole compactness proof.

## Shared Comparison Interface Resolved

Re-read `Comparison/Toponogov/{Global,Hinge,Triangle,Semiconcavity,
IndexComparison,Support/Hessian}.lean` and
`Soul/BusemannConcavity.lean`, under `Geometry/Riemannian/`, against
`lem:rf-squared-distance-comparison` and its selected-line and annular-ray
consumers. The previously developed shortened-tail, no-conjugacy and
index-form proof is recorded in the Ricci-flow integration review, with
the exact Morgan--Tian and Petersen locators. This pass also checked the
arbitrary-geodesic extension, which is proved in the Busemann file rather
than obtained by dropping the minimizing premise from `Semiconcavity`.

The upper supports give concavity of squared distance minus speed squared
times parameter squared. A selected endpoint support gives the hinge
upper bound; separate concavity in the two side parameters gives the
corresponding-side lower bound. Thus trimming decreases the comparison
cosine, as used by the retained-line lemma. For annular rays the equal-radius
case bounds the relative distant-ray error by the error at parameter one.
Separate monotonicity of the comparison cosine yields the diagonal squeeze
and the radial perturbation polynomial used by the local annular argument.
No volume hypothesis or global flow classification enters these implications.

An independent native source/readability pass found no defect in this
interface. Completeness, connectedness and nonnegative sectional curvature
are retained at each fixed-metric use; ordinary smooth ODE, exponential
and index-form infrastructure remains the stated background. This resolves
the shared corresponding-side comparison item, not the later cone-atlas,
complete-limit, line-splitting or full chapter acceptance obligations.

## Enclosing Geometry And Transition Bounds Reconciled

Re-read the complete `ZeroRatio/Backward/{SourceLimit,EnclosingCharts,
BallControl,NormalCharts,EuclideanCoefficients,EnclosedLimit,
GlobalEnclosedLimit}.lean`, `Distance/{CompactImages,CompactNeighborhood}.lean`
and `Hypersurface/HomotheticRadialPotential.lean`. An independent bounded
source/readability pass found no new defect in the enclosing, global-limit,
normal or separation construction. The earlier complete producer reads
and expansion are recorded in "Enclosing Realization and Zero-Ratio
Rigidity"; this pass reconciles their current prose, not a new proof claim.

The text now explicitly fixes the normalized radius from dimension n,
curvature bound one on a radius-two ball, and unit-ball volume lower bound
kappa. This radius precedes c. The already fixed image-distance bound D
then determines c; the earlier-ball decay is used only afterward on the
fixed radius 2/sqrt(c). Thus the choice is not circular. The raw aggregate
unit-umbilic invocation was removed from the narrative. Its trace remains
here: `exists_unitSlice_euclidean_umbilic_of_zero_ratio` uses the source
dimension parameter m+2; for an n-dimensional source m=n-2, with n>=2.

Read `Coordinates/{TransitionCompactness,TransitionBounds,TransitionLimit,
CompactFamily}.lean`, `Coordinates/Transition/Hessian.lean` and
`Coordinates/Coefficients/{InverseBounds,ChristoffelBounds}.lean` in full.
These files are under `Geometry/Riemannian/`. Their mathematical source
context is Morgan--Tian, Section 5.1, Theorem 5.6, printed pp. 85--87,
and Proposition 5.14, printed pp. 90--91. The chapter now supplies the
ellipticity estimate for the first transition derivative, compactness of
the invertible coefficient family, inverse-metric jets, Koszul contraction,
and induction through the bilinear Christoffel transformation formula.
The source proves that formula by differentiating the pullback identity
and using the symmetry of second derivatives. Evaluation at moving
transition points is justified by compact target containment and local
uniform convergence. The ordinary finite-dimensional chain rule,
matrix inversion and smooth Arzela--Ascoli diagonal are background here.

These derivative estimates apply both to the earlier annular overlap
maps and to the actual inverse enclosing-chart maps. In the latter case
one countable source atlas and one subsequence retain all limits; equality
of the original maps on overlaps descends to the global immersion.
The metric identity yields nonsingularity, but global injectivity is only
used after the separately proved terminal-distance separation. This
reconciles the transition-compactness and enclosing interfaces; the
lower normal-coordinate estimates remain in the shared geometric review,
and no whole-chapter acceptance is asserted.

## Whole-Ball Approximation And Metric Segments

Read `Cone/Metric/BallApproximation.lean` and re-read
`Cone/Metric/Geodesics.lean` in full. Read
`Topology/MetricSpace/Curves/Midpoints.lean` in full, and the properness,
unit-slice and dilation proofs in `Cone/Metric/ConeTopology.lean`
through line 175. The chapter now explicitly extends the ray relation
through the vertex: near normalized radius zero a fixed ray has error
at most twice that radius; outside use the uniform annular approximation.
Uniform two-radius ray-distance control supplies the remaining distortion,
and exact ray representatives cover the whole cone ball.

The whole-ball relation confines source geodesic split points in one
compact radial region. Compact passage gives exact splits, including
the endpoint cases. The previous generic midpoint/completion sentence
was replaced with the actual source construction: finite equally spaced
chains, step-function interpolation, one free-ultrafilter limit in a
compact ball, and the limiting exact distance formula. This reconciles
the whole-ball approximation and metric-segment input to link connectedness.
An independent source/readability pass found no substantive gap in this
expansion or the transition-derivative expansion above.

## Metric Arcs And Smooth Polar Coordinates

An independent bounded source/readability audit read
`ZeroRatio/MetricArc.lean` (affine metric arc regularity, lines 31 and 222),
`Polar/Orbits.lean` (orbit interval and gradient velocity, lines 100 and 156),
`Polar/LocalChart.lean` (actual polar inverse, arbitrary positive radius
and domain-wide smoothness, lines 41, 169 and 235), and
`Polar/Dilation.lean` (scaled charts and fixed homotheties, lines 78, 166
and 195), under the cone directory. It also checked the support in
`Geometry/Riemannian/Distance/NormalBall.lean:128`,
`Distance/Minimizing/ExponentialChord.lean:35,92`,
`Distance/GeodesicCorner.lean:36` and `Distance/SegmentSpeed.lean:126`.
The main agent checked the current prose and read the orbit speed,
interval and gradient-velocity source calculation.

No substantive mismatch was found: metric arcs are used on open parameter
intervals, no completeness of the coordinate metric is assumed, and the
no-corner proof uses arbitrarily sharp local chord bounds. The text now
recovers speed by the distance quotient rather than suggesting a
derivative of absolute value at zero. It explicitly uses
P(r,z) = delta_c P(r/c,z) to transfer joint smoothness from unit radius
to each c>0; the radial factor 1/c cancels the homothety factor c in the
tensor formula. The earlier differentiation of the radial potential
now refers forward to metric-arc regularity, independent of smooth
dilation. This reconciles these lower smooth polar producers. The
remaining measure and volume comparison is a separate review obligation.

## Hausdorff Volume And Local Rigidity

The measure audit read `Measure/Basic.lean`, `Measure/HausdorffDensity.lean`
and `Measure/HausdorffDensity/{FrozenMetric,LocalDistance,ChartComparison,
MeasureComparison,LocalFormula}.lean` under `Geometry/Riemannian/`.
The main agent also read the latter aggregate, measure comparison and
local formula in full. The draft now explains the frozen linear metric,
local intrinsic-distance comparison (including first exit), determinant
normalization, countable disjoint refinement and distortion tending to one.
This recovers the coordinate volume form from the retained normalized
Hausdorff measure. The ray-range projection needs no measurability or
full-measure assertion: the Lipschitz inequality is for outer measure on
arbitrary subsets. Its exact factor is L^(-n). The audit checked
`Cone/Metric/{UniformConeDistance,VolumeComparison,Euclidean}.lean` and
the Euclidean Hausdorff normalization in mathlib.

Read `Comparison/Volume/Rigidity/{Radial,Density}.lean`,
`Transverse/{RadialComparison,RayComparison,AbsoluteDeterminant,
RadialSystem,Center,Compression,Matrix,Density}.lean`,
`Polar/ChangeOfVariables.lean`, `Jacobi/Operator.lean`, `Riccati.lean`
and `ScalarComparison.lean` in full under `Geometry/Riemannian/`.
The draft now develops the transverse Jacobi matrix of dimension n-1,
Wronskian symmetry, Riccati trace inequality, determinant-root comparison
and center regularity. The absolute determinant formula is explicitly
for positive radius; its signed density expression extends smoothly
through zero. Exact ball volume, pointwise density at most one and
continuity force density one. The radial inequality then gives vanishing
Ricci at the center, hence zero curvature operator under nonnegativity.
An independent lower-source/readability audit found no substantive defect
in this local rigidity passage. The classical comparison locator is
Morgan--Tian, Theorem 1.34, printed p. 19.

These are bounded reconciliations, not recursive closure or chapter
acceptance. Shared Jacobi-system, normal-coordinate and global volume
comparison foundations remain within the geometric prerequisite review.

## Positive Cone Atlas And Metric Descent

An independent lower-source/readability audit read
`Positive/{Manifold,Metric,RadialPotential}.lean`,
`ZeroRatio/{IsometryLipschitz,NormalEndpoints,IsometricCharts,
IsometryRegularity,IsometryTensor}.lean`,
`ZeroRatio/Source/{Smooth,Metric,UnitPotential}.lean`,
`UnitLink/{Manifold,SmoothAtlas,RegularCharts}.lean` and shared
`Geometry/Riemannian/Metric/Gluing/Descent.lean` in full.
It rechecked the transition and descent cores of
`UnitLink/{Transitions,Metric}.lean`. No substantive mismatch was found.
The draft now explicitly normalizes any positive-radius point to the
unit slice and dilates a retained chart back to that point, scaling both
metric and potential by the squared radius. This proves chart coverage
without assuming a prior smooth structure on the cone.

Dependency precision matters here: `Source/Metric.lean` uses
`Positive/Distance.lean:217`, `positiveChart_symm_inner`, derived from
metric descent and restriction of derivatives. It does not use the later
global intrinsic-distance equality at line 457. That unused theorem is
not a missing premise of this local construction. The local atlas,
distance-isometry, tensor descent and potential transport interfaces are
reconciled; recursive shared ODE and regular-level foundations are not
claimed closed by this audit.

## Weak Busemann Comparison And Regularity

Read `Splitting/Busemann/Weak/{Distribution,Subharmonic}.lean`,
`Splitting/Busemann/Regularity/{Distribution,Smoothness}.lean`,
`Splitting/Busemann/Bochner.lean`, `ScalarOperators/Bochner.lean`,
`Measure/Regularity/Lipschitz.lean`, `Measure/Green/Lipschitz.lean`
and `Comparison/Laplacian/Weak/{Integral,RadialTest,RadialIntegral,
RadialGradient}.lean` in full under `Geometry/Riemannian/`.
Read `Analysis/Calculus/{WeakDerivative/LipschitzGreen,
Integral/RadialComparison}.lean`,
`Analysis/Elliptic/Regularity/Sobolev/Weak/Lipschitz.lean` and
`Analysis/Elliptic/Regularity/Distribution.lean` in full.

An independent complementary audit checked the polar assembly, signed
integral and almost-everywhere transport, following their lower
`CutTime`, `RadialNull`, `NullImage`, `Injectivity` and `RayInterval`
mechanisms. The draft now explains measurable terminal vectors via
rational radial extensions, singleton-ray nullity, null exponential
images and nonterminal injectivity. No continuity of cut time is used.
The signed scalar comparison retains the terminal contribution
-q(d)J(d), which is nonpositive but need not vanish. The origin term
vanishes because n-1>0. Both integrands are integrable by their polynomial
bounds, without assuming integrability of the Jacobian derivative.
The audit's two endpoint clarifications were applied: choose the
truncating ball to contain the test support, and use density continuity
only through d=min(c,b) strictly inside the exponential domain.

The weak Green identity is developed from local Lipschitz extensions,
coordinate-line integration by parts, Rademacher and a finite partition
on the test support. Compact domination justifies the Busemann limit
for each fixed distance lower bound, then that lower bound tends to
infinity. The text also constructs weak coordinate derivatives and
converts the adjoint equation to the first-order divergence equation
using the smooth compact flux as test. A precise cross-reference now
targets the Ricci-flow chapter's local elliptic bootstrap, with matching
smoothness, positivity and compact-local square-integrability hypotheses.
Continuity identifies the same representative. The Bochner computation
retains the positive Ricci sign and shows how its traced third derivatives
arise. Independent checks found no further substantive defect in these
bounded passages. The broader elliptic bootstrap remains a shared review
obligation; these checks do not accept the chapter.

## Fixed-Factor Product Measure

An independent audit read `Splitting/ParallelGradient/Volume/
{Coordinates,Fubini,Measure}.lean` and `Measure/Coarea/Fubini.lean`
in full under `Geometry/Riemannian/`. The exact Gram-density equality,
normalized Euclidean product measure, Tonelli on chart rectangles and
countable-cover gluing justify the cylinder factor 2r without finite
total volume. The text now explains these steps. This reconciles the
product-measure input and its constant w/2^(n+1). `LevelSet.lean` and
`LevelComplete.lean` were also read by that reviewer, but their general
induced-level geometry and completeness inputs remain under review.

## Heat-Contact Positivity And Ricci Frames

Read all of `Geometry/RicciFlow/Splitting/MaximumPrinciple/`
`{LowerContacts,Positive,Endpoint,CompactBounds,MetricBump,ChartOperator,
CoefficientRegularity,RicciPropagation,RicciNullity}.lean`,
`Barrier/{MovingBump,Jets,CoefficientBound,Subsolution}.lean` and
`ChartChain/{Geometry,SeedTube,ScheduledSegments}.lean` in full.
The draft now states the exact continuous lower-spatial-contact / upper-
time-support condition in a named lemma. Its compact comparison uses a
strict time penalty and the derivative sign at a maximum relative to the
past. Terminal time follows by continuity. The moving bump includes the
actual inverse metric, Christoffel drift and center velocity; explicit
boundary scale and damping control the support boundary. Finite compact
chart subdivision and equal positive time slots propagate positivity
between any prescribed points. No completeness or global coefficient
bound is imposed. Independent review found no substantive defect in the
signs, damping constants, contact order or endpoints.

An independent audit fully read `Geometry/RicciFlow/Frame/RicciTransport.lean`,
`Splitting/TimeTransport.lean`, `Splitting/PartialTraceEvolution.lean`, and
`Geometry/Riemannian/Tensor/MaximumPrinciple/Transport/`
`{Isometry,Radial,Local,Jets,MetricCompatibility}.lean`; it checked the
mathematical cores in `Transport/Metric.lean`, `Contact.lean`,
`SupportingLaplacian.lean` and `Frame/Transport.lean:1-178`.
The text now derives the zero first and diagonal second radial jets,
without asserting zero mixed second jets. It explains the fixed-fiber
linear time ODE and normalization U(s)U(t)^(-1) at each contact time.
The direct producer is `Splitting/TimeTransport` on the closed slab;
the similarly named `Frame/RicciTransport` is a separate interface.
Spatial and temporal supports are separate constructions through the same
minimizing frame. Their support order is correct and needs no smooth
eigenframe. Fixed tangent-space ODE and coordinate calculus remain ordinary
background, not a hidden assumption of Ricci-kernel transport.

Directly inspected the archived published Morgan--Tian text: Theorem 4.16
is on printed p. 70 and Theorem 4.18 on p. 71. Several Lean comments give
p. 95 or pp. 95-96. Recorded this locator discrepancy and the explicit
barrier route in `reconstruction/source-specializations.md`; Lean and
reference files remain unchanged. A literal carriage return corrupting
the orthonormal-frame minimum was also corrected in the draft.

## Null Sections And Fixed-Level Geometry

Read `Geometry/RicciFlow/Splitting/{NullSections,CurvatureNullity,
NullSectionEnergy,NullConnection}.lean` and
`Geometry/Riemannian/Tensor/RicciDerivative.lean` in full. The draft now
constructs each local smooth null section by an inverse regularized with
projection onto the reference kernel. Constant rank gives surjectivity
of the kernel projection; this is not a choice of smooth eigenvectors.
The pointwise curvature-null argument uses a nonnegative radial form
of trace zero, a second nonnegative form, polarization and first Bianchi.
It then explains why differentiation of curvature nullity and contracted
second Bianchi annihilate the derivative slot of the Ricci derivative.
The terminal energy calculation retains the sign from earlier-time
nonnegativity and the fixed-input Ricci evolution.
An independent source/readability pass found no substantive gap in the
inverse construction, polarization, terminal sign or derivative-slot
Bianchi identity. The text explicitly notes that first-derivative
annihilation holds for every local null section, eliminating the
correction containing its covariant derivative. It displays the exact
contracted Bianchi identity with the retained curvature convention.

The complementary fixed-level audit checked the general regular-level
straightening, `Metric/Induced/Complete`, `Hypersurface/Connection`,
`Splitting/ParallelGradient/FactorCurvature/{Normal,Traces}` and the
actual `AncientVolume/Splitting/FactorFlow` consumer. The expanded text
derives connectedness by retraction, completeness by closed embedding and
intrinsic topology, and the connection by Koszul. Pairing with the parallel
normal makes the second fundamental form zero; adjoining that normal to
an orthonormal frame makes all extra Ricci/scalar/full-norm trace terms
zero. Independent review found no substantive defect in this bounded
factor passage. These checks do not certify the whole chapter or the
shared geometric and analytic foundations.

## Shared Normal Coordinates And Local Injectivity

Completed the bounded lower quantitative review with the existing native
reviewers. Read-only review covered normal-coordinate
`JetBounds/{TransportVariation,RadialFrameVariation,RadialConnection,
ConnectionKernel,ConnectionComponentJets,RadialIntegral,
RadialConnectionBounds,FrameInduction,MatrixParameterBounds,
JacobiCoefficientJets}` and the linear/Jacobi parameter ODE producers.
The draft now derives H'(t) from the curvature commutator, explains the
parallel ray identity T(tx)x=x, integrates the connection and differentiates
the radial integral with the t^m factor. The order l+m<=N is retained;
there is no extra curvature derivative or circular coframe estimate.
Ordinary augmented linear ODE estimates and Gronwall suffice for the
matrix parameter step and need no project-specific expansion.

The local injectivity audit inspected
`Injectivity/{Collision,InverseRadius,ReturnDirection,ReturnedLoop}`,
`Lifting/{Compact,Bounded,DeckMotion,SmoothDeck,FiniteFibers}`,
the Jacobi pairing/radial convexity producers and `Packing/DensityBound`.
The draft adds the attained first-collision argument, opposite inverse
radius gradients, smooth local inverse description of deck motion and
the countable measurable partition proving the finite-fiber volume bound.
Its N-dependent radius and finite-orbit energy argument reconcile with
the source. A stale shorter version in the Ricci-flow chapter was corrected
to this local mechanism; the cross-reference does not assume the ancient
flow or compactness result in which the calculation is applied.

Independent rereads of these bounded edits found no remaining substantive
defect after specifying the ray-velocity identity and matching chart
readout. Shared global comparison and analytic prerequisites are distinct
from this completed local coordinate/injectivity review.

## Final Sequential Review And Finite Corrections

Under operator direction 2438, reused the completed producer reviews
instead of reopening broad prerequisite discovery. The two existing native
reviewers read the complete chapter sequentially in two nonoverlapping
parts: the opening through self-similarity, and asymptotic volume through
the final quotient identifications. The main integration reviewer checked
each finding against the actual text and source, and corrected:

- The infinite scalar-ratio proof formerly attributed earlier-slice
  positivity to Harnack alone. Read
  `Geometry/RicciFlow/Harnack/Noncompact/AncientVolume/Nonflatness.lean:90-170`.
  Forward scalar comparison first prevents an identically zero earlier
  slice; bounded Harnack from t0-1 then gives positivity at every selected
  point at t0. The draft now exposes both steps.
- The normalized global-curvature proof cited the positive-AVR selected-line
  and factor lemmas without that premise. It now invokes the already proved
  geometric selected-line lemma, then only the fixed-level product and
  curvature construction from the factor proof. Its independent product-ball
  calculation gives kappa/54 noncollapse; no positive AVR is assumed.
- Partial-trace positivity gives nullity information. Actual backward
  inclusion of kernel vectors additionally uses derivative annihilation
  and transport; the draft now points to the developed persistence proof.
- The asymptotic summary now follows its displayed proof: the scalar defect
  is identically zero, and its pointwise evolution annihilates the tensor
  square. The old summary's vanishing-weighted-integral attribution was
  inaccurate. This also corrects that wording in the historical Asymptotic
  Equation Producer Chain entry above.
- Removed implementation-path summaries and obsolete pending-review remarks
  from the mathematical narrative, preserving the mathematical dependency
  statements. The source paths remain in this review. Corrected the stale
  MT Proposition 9.20 locator to printed p. 198, as already established by
  the direct source comparison under Local Weak Regularity and in
  `reconstruction/source-specializations.md`. This supersedes the erroneous
  pp. 207-208 wording in the later historical Weak Parabolic Regularity entry.

Both reviewers independently reread the actual corrections and found no
remaining defect from their finite passes. The second-half reviewer also
read the Ricci-flow consumer: bounded-slab Harnack proves bounded ancient
zero AVR, which supports slab control and only then full slice-wise Harnack.
Later whole-past structural bounds may use the full theorem. The bounded
zero-AVR predecessor is reconciled for Ricci-flow chapter acceptance.

Ordinary ODE, compact metric, spectral, Sobolev, local elliptic and
Riemannian background is not reopened absent a concrete missing argument.
The specialized limit, cone, product, persistence, quotient and terminal
geometry is developed in the draft and traced above. This finite pass
does not certify whole-book completeness or fresh Lean verification.

## Acceptance And Outgoing Interfaces

Accepted by the main integration reviewer on 29 September 2026 at draft
SHA-256 `0fa8edc89baec2d0a30b496999ebf57017c1adff76fc708a41c5da9c6b6b0670`,
after the extinction calibration, the producer and sequential reviews above,
and acceptance of the corrected reduced-geometry chapter at digest
`0ec11f86d8bb7fac9e859f25304eb395f9e187bcc7dd77ee68bee39289bb3a2e`.
The latter review is recorded in `reduced-geometry-integration-v4.md`.

The outgoing comparison preserves whole finite past slabs, the interior
time choice tau_max=tau_i+1, the Harnack bound K>=-L and its gradient/time
consequences, the common slice-null regular spacetime locus, and the signed
weak Laplacian inequality used in the flux argument. Lipschitz derivatives,
Fubini and exact parabolic density/measure cancellation have the stated
hypotheses. The limiting potential is constructed in this chapter and is
not assumed to be reduced length from a missing limiting basepoint.
No cross-chapter mismatch remains in this interface.

This decision supersedes the historical pending-prerequisite descriptions
above and in the author JSON. Accepted Ricci-flow and reduced-geometry
interfaces retain all their hypotheses. M16--M24 and the additional bounded
ancient zero-volume predecessor are located in the current milestone
register. Consumer applications, whole-book final source links and complete
PDF/site inspection remain integration obligations; this chapter acceptance
does not certify those unfinished tasks.

No Lean build, make check, endpoint audit or comparator was run, in accordance
with operator direction 2418. Pinned verification evidence is reused.

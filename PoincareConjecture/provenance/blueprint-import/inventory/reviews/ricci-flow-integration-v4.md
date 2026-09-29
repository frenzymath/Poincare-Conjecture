# Ricci Flow: Integration Review in Progress

Owner: `blueprint-v4-integration`, session
`session_fd894b3e2eb047718aa35f162d35c568`.
Source revision: `751329327f4f582797bda8e6cffe7cdf7531cc1d`.
Status: bounded pinching contact and fiber geometry reviews completed;
chapter not accepted.
The harmonic-coordinate construction has its separate bounded review in
`harmonic-coordinates-integration-v4.md`.

## Geometric Pinching Contact

The initial sequential reading covered normalization, local construction,
curvature estimates and pinching. The pinching prose left the spatial
contact cancellation and compact time comparison too compressed. Integration
expanded both in `sec:rf-pinching`, after confirming the author had finished.

The following current source files were read for this bounded correction:

- `Geometry/RicciFlow/Pinching.lean` and
  `Pinching/GeometricPreservation/{Preservation,Transport,TimeEvolution,
  TransportedContact,ScaledContact}.lean`: actual producer, initial absolute
  time, metric ODE, rate-two geometric reaction, scaling, and transfer of
  the slice contact sign. The diffusion is the pulled-back rough Laplacian;
  no spatial differentiation of the time transport is used in that transfer.
- `Pinching/LocalContact.lean` and
  `Geometry/Riemannian/Tensor/MaximumPrinciple/{CarrierContact,
  SupportingLaplacian}.lean`: the carrier support is constructed from the
  local maximum of distance, rather than assumed to have a scalar maximum.
- `MaximumPrinciple/Transport/{Radial,MetricCompatibility}.lean` and
  `Transport/Isometry.lean` through the all-vector jet construction:
  smooth parameter-dependent radial ODE, uniqueness under radial
  reparametrization, zero first and diagonal second covariant jets at the
  center, preserved Gram matrices and induced tensor isometries. These use
  coordinate rays and the full connection coefficients; a normal chart
  with identically vanishing connection is not asserted.
- `Analysis/Parabolic/LocalPreservation.lean`, `CompactMaximum.lean`, and
  the active-support/reaction portion of `ConvexSupport.lean`: finite compact
  local covers, bounded support points, support at the nearest carrier
  point, reaction Lipschitz estimate, and exponentially weighted maximum
  over a compact family. The maximum-distance function is not asserted to
  be differentiable. The right endpoint uses the derivative from the left.
- `Pinching/Region.lean`, `ReactionSupport.lean`, and the trace/logarithmic
  boundary calculations in `ReactionInvariance.lean`: least-eigenvalue
  concavity, convex negative part, the rate-one scalar calculation and
  inwardness obtained from a short symmetric reaction curve and scaling.

All paths above are relative to `PoincareLib/`. This is a mathematical
source review of those steps, not a new import-closure or kernel audit.

## Readability Check of the Replacement

The replacement defines the active pair before use, constructs the spatial
transport, proves its two required jets, derives the support inequality,
and only then takes the scalar Laplacian. It separates spatial transport
from the time transport. For the compact-family argument it gives the
nearest-point bound `2H+J`, the support parameter space and the endpoint
maximum contradiction.

During the independent reread, corrected a potential false shortcut:
an active support pair need not have its anchor at the nearest carrier
point. Its normal also supports the carrier at that nearest point. The
prose proves this by splitting the active scalar pairing into two terms;
only the nearest point is used in the Lipschitz estimate. This agrees with
`unitSupport_at_nearestPoint_of_active` and does not impose strict convexity.

## Scalar-Integral Level Construction

Read `Geometry/Riemannian/Soul/{Injectivity,Exhaustion}.lean` and
`Comparison/Injectivity/Radius/ConvexDescent.lean`. The stationary
minimum argument in the draft retains the strict exhaustion decrease
and the stationary average of the two inverse exponential branches.
The Busemann and first-cut branch producers still require their own
source comparison; these entry reads do not close that review.

For scalar integrals, read the dimension induction and step in
`Geometry/Curvature/Integral/Induction/Corners/`, the opening 180 lines
of `Integral/Scalar.lean`, and the following construction:

- `TiltedDirectionalSlab.lean`, `RadialAugmentation.lean`,
  `Slab/Parameters.lean`, `TiltedArea.lean` in full;
- `DirectionalPair.lean`, the prescribed-slab partner construction and
  complete value-tube theorem and proof (lines 113-282 and 513-778);
- `TiltedSlab.lean` through the compact inner strip construction;
- `Slab/AnnularBound.lean` through the actual tilted slab selection and
  strip-bound setup; `Slab/GeometricBound.lean` through the component
  geometry and iterated-level transfer setup;
- `ComponentBound.lean` through the buffered component construction and
  scaling setup, and `StrainerAnnularComponents.lean` in full.

Expanded the previously brief smoothing/tilting paragraph to give the
actual functions, tolerance before scale, squared opposition estimate,
strict cross sign, Gram-matrix regularity and compact-strip argument.
Corrected the diameter assertion to apply to each connected component;
the level need not be connected. The displayed area is total level area.
The shifted value interval is bounded away from zero and comparable to
the annulus radius. A common area constant can consequently be expressed
as a multiple of the appropriate power of that shifted value.

### Uniform Geometry of the Actual Fibers

Expanded the quantitative argument after reading these sources (same
`Geometry/Curvature/Integral/Induction/Corners/` directory):

- `LocalDistance.lean`, `PrefixDistance.lean`, `PrefixPair.lean`,
  `PrefixBounds.lean`, `Diameter.lean`, `StrainerComponents.lean` and
  `BufferedComponent.lean` in full;
- `LocalVolume.lean` and `PrefixSliceVolume.lean` in full;
  `Hessian.lean` through the Gram-coefficient Hessian proof;
- `Geometry/Riemannian/Metric/Induced/RegularLevelCompactDistance.lean`
  in full, the two main constructions in
  `ScalarOperators/Gradient/Flow/CompactRetraction.lean`, and
  `SliceVolume.lean` from the slice-volume consumer through the final
  coarea and gradient-flow bound (lines 219 onward).

The prose derives the normal Gram coefficients and their nonpositive
sign, retains the original defining equations during the opposite-function
tilt, and gives both forward hitting maps. Their derivative estimate uses
only level-tangent Hessians: orthogonal initial projection, tangential
flow differential, and an oblique final projection for the second map.
The common Lipschitz bound handles infinitely many crossings of the level.
The compact buffer supplies ODE continuation on incomplete prefix fibers.

The iteration gives `9 exp(128 C rho)` per equation. An ambient ball cover
then bounds the component count and each intrinsic component diameter.
The prose explicitly retains the closed `40 rho` ambient buffer, `rho <= 1`
and the sectional lower bound after rescaling. Separation of components
constructs the restricted ambient domain used by the induction hypothesis.
For area, backward continuation supplies coverage by forward flow images;
the forward Jacobian and coarea give the iterated bound with coefficient
`(4(k+1)/r)^k exp(2 n C r)` and ambient radius `3r/2`.

Directly inspected Petrunin's manuscript pp. 8-12, especially section 4.5,
pp. 9-10. It suggests corner-surface convergence for the level-area bound.
The implemented proof instead supplies the quantitative flow/coarea
construction now developed in the text. This is a source comparison,
not a claim of novelty.

### Upper-Level Opposite Partner

Read `Geometry/Riemannian/Distance/Smoothing/Directional/OppositeLevel.lean`,
`Smoothing/ClosedSet.lean`, `Smoothing/Compact.lean`,
`Metric/Gradient/LevelDistance.lean`,
`ScalarOperators/Gradient/Oscillation.lean`,
`Comparison/Hessian/{Distance,DistanceToSet}.lean`, and
`Topology/MetricSpace/AscendingSlope/Level.lean` in full.
Read the finite regularized minimum through its weighted Hessian and
active-branch estimates in `Smoothing/FiniteMinimum.lean`.

Expanded the actual upper-level construction: a compact penalized maximum
reaches the level, a nearest-point segment supplies the reverse distance
bound, and the defect is at most `5 sigma^2 s`. Local convolution followed
by biased-cutoff regularized minima retains the upper Hessian bound.
The prose explains why invalid branches have zero differential weight;
it does not use an uncontrolled partition-of-unity Hessian formula.
The oscillation argument for `u + rho`, on radius `sigma s/8`, gives
the gradient-sum bound `64 sigma`; normalization gives opposition error
`128 sigma`. The squared error budget then controls mixed products with
the old gradients.

### Radial Directional Smoothing

Expanded the first radial function after completing the reading of
`Directional/ConstraintsDistance.lean`. Also read the following sources
under `Geometry/Riemannian/Distance/Smoothing/Directional/` in full:
`Ascent.lean`, `ConstraintsCoordinates.lean`, `ConstraintsSubset.lean`,
`ConstraintsCompact.lean`, `CornerTube.lean`, `RadialTube.lean`,
`RegularSlab.lean`, `PrescribedSlab.lean`, `Excess.lean`,
`AnnularStability.lean` and `AscentStability.lean`.
Read `RadialPair.lean` through line 180, including the paired endpoint
derivative calculation. Read `Analysis/Approximation/Convolution/DirectionalLocal.lean`,
`Geometry/Manifold/PartitionOfUnity/LevelLocalization.lean`,
`Topology/MetricSpace/AscendingSlope.lean`, and the corner-induction
`AnnularTubeSmoothing.lean` and `DirectionalTubeSlab.lean` in full.

The replacement derives the endpoint bounds for both old gradients from
the two upper Hessian bounds and the small sum of opposite gradients.
It explains freezing the pulled-back fields, converting support derivative
bounds into increments, convolution, and gluing with active branches.
The enlarged annulus has margin `sigma^2 r/1024`; the value error is
`sigma^4 r/1048576`. A compact penalized maximum produces a finite ascent
increment, and Taylor's upper estimate gives the lower gradient bound.
Band cutoffs preserve the central germ and make the specified value band
proper. The numerical losses agree with the source after substituting
`delta = sigma^2` in `DirectionalTubeSlab.lean`.

### Concentration and Angular Rank

Read these files in `Geometry/Curvature/Integral/Concentration/` in full:
`CornerMaximalRank.lean`, `CornerModels.lean`, `CornerConcentration.lean`,
`CornerRankGrowth.lean`, `CornerRescaling.lean`, `SubsetSpires.lean`,
`RegularRadius.lean`, `MaximalRadius.lean`, `PuncturedCover.lean`,
`RadiusSelection.lean`, `SubsetCenterSelection.lean`,
`FiberConcentration.lean`, `ExpandingSubsetSpireCenters.lean`,
`RadiusConvergence.lean`, `RadiusLimitAscent.lean`, `CenterSelection.lean`,
`FiberLimits.lean`, `ExpandingSubsetRankGrowth.lean`,
`WeightedAnnuli.lean` and `WeightedFiniteCover.lean`.
Read `CornerCenters.lean` lines 120-305, `RankGrowth.lean` through line
200, and `FiberAnnuli.lean` through the complete positive-radius and
zero-radius individual-center estimates (before the mixed-cover theorem).

Read `Geometry/Alexandrov/Packing/{PuncturedAscent,PuncturedAngles,Net,
RiemannianLimit,LimitRankGrowth,MovingBadAscentGrowth}.lean` in full and
`BadAscentGrowth.lean` through line 240. Read
`Geometry/Alexandrov/Comparison/{DistanceAscent,BadAscentStability}.lean`
in full. These reads include the finite-configuration angle calculation
and the pointwise rank-growth consumer; they do not constitute a fresh
recursive audit of all comparison or pointed-limit dependencies.

The expanded text defines exceptional points using maximal punctured
ascent radii, proves their finiteness, and uses strict rate gaps to pass
ascent between source and limit. Compact selection yields a factor-two
near-minimum without assuming continuity of the bad-radius function.
The exceptional-point inequality forces selected centers back to the
specified limit point.

Corrected the earlier fixed-annulus coverage assertion: a finite family
of fixed annuli is used only after removing small neighborhoods of the
exceptional points. Inside those neighborhoods, the ratio `227/228`
supplies a geometric sequence of annuli. Their buffered errors have
bounded overlap, and the geometric scalar terms sum because `m >= 3`.
The zero-radius case uses the absence of atoms in positive-dimensional
induced volume. Finite-member selection then gives a positive shrinking
radius with divergent localized curvature-to-error ratio.

The metric, defining functions, curvature error and scalar integrals are
all scaled explicitly. Backward approximation lifts each point of the
new marked section into the old selection neighborhood. Near-minimality
supplies a bad point at original distance greater than `r_j/4`, hence
rescaled distance greater than `1/16`. The angle calculation adds a
direction at every new marked point. Shortening to a common small
radius accounts for the change in hyperbolic comparison angles under
rescaling; scale invariance of those angles is not asserted.

Directly compared Petrunin's manuscript sections 3.3-3.7, pp. 6-7, and
4.6-4.7, pp. 12-14. The source describes exact minimizing lifts and
rescaling by `2 a_n`; this implementation uses factor-two near-minima,
strict ascent-rate buffers, actual marked fiber sections and `4 r_j`.
The prose follows the latter choices. This is the same proof mechanism,
not a novelty claim.

### Signed Slab Estimate and Normalization

Completed the reads of `Corners/Slab/{AnnularBound,GeometricBound}.lean`
and read `Corners/Slab/{WeightedBound,AnnularSummation,Coverage,
StripCenters}.lean` and `Corners/ComponentSlab.lean` in full. Read
`Induction/{ScaleAnnulusBound,Slab,Intermediate,SlabError,Boundary,
SectionalErrorBounds}.lean` in full and `SectionalIntegral.lean` through
the complete pointwise and integrated sectional-error estimates.
Also read `Corners/{Localization,ModelReduction}.lean` in full and
the remaining cover-transfer theorem in `Concentration/CornerCenters.lean`.
These paths are relative to `Geometry/Curvature/Integral/`.

Expanded the integrated level calculation. The level dimension is `m-1`,
so its scalar-integral scaling term has exponent `m-3`. The text uses the
actual continuous Gauss error `E + beta H^- + (m-1) beta^2`; it does not
replace that error with an unexplained curvature bound. First variation
gives the negative mean-curvature estimate. Coarea uses the lower speed
bound for the scalar integral and the upper speed bound for the error.
Integration by parts retains the sign of `beta' = -alpha/t^2` and the
lower endpoint term.

The signed Bochner identity leaves `-2 A'(b')` at the outer level. The
mean value theorem on `[b,3b/2]` bounds this using `A(b)`, and positivity
allows restriction back to `[a,b]`. The prose now displays every term
needed to see why the remainder has order `r^(m-2)` and why `m >= 3`.
The normalized numerical net covers radial points with tilt error
`s/256` and value error `s/128`; this justifies a uniform finite strip
cover and bounds the multiplicity of its error integrals.

For normalization, the text now chooses `rho_0 = min(1,eta/2)`, scales
the metric and defining functions together, and shows the Hessian bound
improves. The ambient packing factor is
`ceil(V_-1,m+k(6)/V_-1,m+k(rho_0/4))`. The local scalar scaling term is
`rho_0^(m-2) <= 1`, yielding the stated compact-fiber bound. The iterated
and augmented level descriptions have the same induced metric, which
is the metric used throughout these scalar and volume integrals.

The scalar-integral mechanisms now have expanded proofs, but this is not
whole-chapter acceptance. The remaining pointed-limit and comparison
producers must be covered by the corresponding library exposition or
checked explicitly during compactness review. The first-variation and
integrated hypersurface-Bochner background, and the low-dimensional
reductions, remain part of the full sequential source/readability pass.

## Hamilton Null Contact

Expanded the contact calculation beyond the statement that derivatives
cancel. Read `Harnack/Matrix/Positivity/Contact.lean` and
`GeometricContact.lean` in full, `SpatialContact.lean` through its local
smooth first-jet construction, `PerturbedSpatialContact.lean` through
the complete perturbed spatial-contact inequality, and
`PerturbedTimeContact.lean` through the metric identity derivative and
null Ricci-input-action calculation. Read `Positivity/Reaction.lean`
through the tensor-square, sharp-reaction and square decomposition;
`PerturbedReaction.lean` at the collected reaction and replacement-error
statement. Read `PerturbedHeat.lean` through the reaction identity and
perturbed-null lower bound.

For the cancellation, read `Matrix/Evolution/Quadratic.lean` in full,
`QuadraticCancellation.lean` through the derivative, Ricci-weighted and
curvature-jet contractions, and `QuadraticReaction.lean` through the
curvature-reaction square calculation. Read `QuadraticHeat.lean` through
the complete mixed and vector heat cancellations. Read the actual heat
operator definition in `Tensor/HeatGradient.lean`, the divergence
identity and its proof in `Matrix/Divergence.lean`, the main heat theorem
in `Matrix/Evolution/M.lean`, and the heat theorem and reaction definition
for `P` in `Matrix/Evolution/P.lean` and `Matrix/Reaction/P.lean`.
These paths are relative to `Geometry/RicciFlow/`, with `Matrix/` paths
under `Harnack/`.

The prose proves annihilation of a null vector, displays the spatial
quadratic Laplacian with arbitrary first jets, and explains why second
test-field derivatives cancel. It gives the covariant heat convention,
the two divergence identities, all three tensor evolution equations and
the contractions with the prescribed skew jet. The resulting identity
retains `2/tau (M(W,W)+P(U,W))` and the explicit square of `PW+RU`.
The vector row vanishes for the unperturbed block and equals
`-alpha |W|^2` for the perturbed block, producing the favorable
`2 alpha/tau` term. The ordinary time derivative follows by canceling
the full Ricci input action at null contact.

The replacement-error explanation retains the reciprocal-time bound on
`M`, the spatial `psi |V|^2` term, and the use of `psi <= 1` and Young's
inequality. These give the error form stated in the existing strict
contact inequality. The full quantitative constant and global barrier
assembly remain to be reconciled with their final source consumers.

Directly inspected Chow et al., Part II, printed pp. 273-279 (PDF pp.
300-306), Lemmas 15.18-15.19 and equations (15.45)-(15.58).
The displayed curvature indices follow this library's convention;
the book's last-pair order must be translated when comparing formulas.
The new text includes the missing square and reciprocal-time correction
instead of referring only to unspecified nonnegative terms.
This bounded contact review does not close the tensor-evolution producer,
proper-exhaustion, derivative-estimate or global positivity reviews.

## Noncompact Localization

The global Harnack consumer has now been read in full in
`Harnack/Matrix/Positivity/Global.lean`, together with `StrictContact.lean`,
`Harnack/Noncompact/Localization.lean`, the explicit differential barriers
in `Barriers.lean`, and the entire `Exhaustion.lean` assembly. Read
`Exhaustion/Transfer.lean` through the connection and Hessian variation
estimates. The prose now gives the single compact sublevel
`rho <= T (C0 + C0^2/(2 delta) + 1)/epsilon`, the uniform initial interval,
and the strictly positive starting time for the compact first-contact
argument. It specifies the one-parameter perturbation limit. Thus neither
spatial compactness nor initial positivity is silently interchanged with
a point-dependent choice.

Read `Geometry/Riemannian/Distance/Smoothing.lean` in full and the
constant-shift construction in `Distance/Smoothing/Basic.lean`.
Replaced the ambiguous phrase "bounded-geometry slice" with the actual
complete bounded-curvature hypothesis. Added the heat-slice shift and
the explicit Hessian transfer via the three terms of connection
variation. The heat existence, displacement, gradient and time-one
Hessian producers still need substantive source and readability review;
their assembly alone is not accepted as their proof. The remaining
quantitative perturbation-error calculation is likewise still open.

## Heat Distance Smoothing

Expanded the smoothing input into its actual analytic route. Read
`Geometry/Riemannian/Heat/Hessian.lean` in full, including the harmonic
lift constants, Hessian conversion and dimension-one branch. Read
`Heat/HarmonicEstimate.lean`, `Regularization/Existence.lean`,
`CanonicalKernel.lean`, `CanonicalEvolution.lean`, `GradientLimit.lean`
and `Approximation.lean` in full; read `CompactData.lean` through the
compact-data Gaussian-energy argument and the growing-data consumer.
The short filenames in this list are under `Heat/Regularization/`.

Read the probability-average displacement calculation and the main
Gaussian-energy gradient theorem in `Heat/Regularization.lean`;
`Heat/Energy/Gaussian.lean`, `Comparison.lean` and `KarpLi.lean` in full;
and `GaussianWeight.lean` through its Hamilton-Jacobi calculation.
Read `Heat/Kernel/Conservation/Exhaustion.lean`,
`Kernel/Exhaustion/Gaussian.lean`, `Kernel/Exhaustion/Moment.lean`,
`Kernel/Moment.lean`, `Kernel/Gaussian/Estimate.lean` and
`Kernel/Gaussian/Dirichlet.lean` in full. These paths are relative to
`Geometry/Riemannian/`, with the `Kernel/` paths under `Heat/`.

For the static Harnack producer, read `Kernel/LiYau.lean` through the
logarithmic Laplacian and gradient evolution identities;
`LiYau/Maximum.lean`, `Comparison.lean`, `LocalBound.lean`,
`DistanceBound.lean`, `DomainDistanceBound.lean` and `GlobalBound.lean`
in full; and `Kernel/Exhaustion/GlobalHarnack.lean` through the
domain-local estimate and path integration. The text gives the
cutoff quadratic inequality, its mixed-term cancellation and the
positive starting-time limit. It distinguishes this static result
from the Ricci-flow matrix Harnack theorem. It also preserves the
order of the domain-exhaustion and radial-cutoff limits.

Read `Regularization/GrowingRegularity/Equation.lean`, `Smooth.lean`
and `KernelIntegral.lean` in full. The new proof explains domination
of every local kernel jet by a fixed later row and why its first
moment allows integration against growing initial data. Compact
approximations pass to a weak heat equation before smoothness is
used to identify the classical equation.

Directly inspected the primary source in
`references/ricci-flow/techniques-and-applications/part-iii.html`, which
is a PDF despite the extension: printed pp. 378-385, Proposition 26.49,
equations (26.128)-(26.152). The construction agrees with its heat
evolution and harmonic lift route. The implementation gives an explicit
one-sided Gaussian constant with denominator 192, sums scaled distance
shells to obtain a uniform square-root-time first moment, and passes
gradient bounds through compact data. The book uses a two-center volume
estimate and a fixed-radius tail integral. No novelty is asserted.

The expanded text includes conservation by support cutoffs, the weighted
two-set estimate, uniform first moments and initial trace, compact-data
Bochner comparison, Gaussian energy, the positive-part detector and
Hessian descent from the local harmonic lift. The constants in the
final gradient and Hessian bounds precede the manifold and center.
The Gaussian energy may depend on the compact approximation, which
does not contaminate the gradient comparison constant.

Read `Regularization/InitialGradient/Spectral.lean`, `Jets.lean`,
`Exhaustion.lean` and `Trace.lean` in full. The prose now derives
the initial gradient trace from the domain-independent multiplier
estimate, local elliptic powers and the passage of Lipschitz errors
to the exhaustion limit. It explains why this is joint in space
and time.

Read `Analysis/Parabolic/Interior/Uniform.lean`, `GlobalEstimate.lean`,
`LocalEstimate.lean` and `ScaleChoice.lean` in full. Expanded the
parabolic Hessian estimate: coefficient freezing, separated spatial
and time cutoff errors, the integrable quarter-power kernel moment,
gradient interpolation, time scale `q r^2`, and nested-cylinder
recurrence with coefficient `1/8` against growth `4^j`. The final
estimate removes the solution-dependent Hessian supremum. This
consumer uses the harmonic-coordinate producer already developed
in the chapter, without imposing injectivity on the original manifold.

This is a bounded review of those mechanisms and their displayed
consumers. The underlying Dirichlet spectral and elliptic-regularity
construction and high-order kernel-jet estimates still require
reconciliation with the chapter's analytic background; the source
traversal above is not a claim that every imported producer has been
independently reviewed.

## DeTurck Generator And Derivative Budget

Expanded the local generator proof from its weak divergence equation.
Read `Construction/DeTurckGeneratorRegularity.lean` at
`norm_coordinateQuotient_le_of_weak_equation` and
`exists_secondDerivatives_of_weak_equation`;
`Regularity/DeTurckLocalizedH2.lean` through the localized source and
generator graph estimate; and `Regularity/DeTurckHigherDomain.lean`
through the weak product rules and exact differentiated source.
These paths are relative to `Geometry/RicciFlow/Local/DeTurck/`.
The prose retains the translated principal coefficient, the quotient
test sign, the ellipticity buffer, and the source norm in the bound.
Read `Regularity/DeTurckDomainRegularity.lean` at the pairing limit and
bounded-quotient weak derivative construction, and at the closed graph
argument for a finite weak jet. The source uses a weak-dual cluster
point followed by Riesz representation; the prose gives the same
bounded functional and its uniquely determined test pairings.

Read `Regularity/DeTurckNestedLocalization.lean` at the distinguished
cutoff construction, five groups of lower-order source terms,
`generatorGraph_extend_localizedJet`, and the two-step spectral-scale
induction through its closed graph bounds. The larger cutoff equals
one on a neighborhood of the smaller support; one does not divide
by a cutoff that may vanish. The text states why regularity of all
probes on all localizations is the induction hypothesis.

Read `Regularity/DeTurckMetricDomain.lean` at the native directional
word expansion and the finite-jet Fourier decoder through continuous
realization. Corrected the exposition's ambiguous derivative budget:
continuous derivatives through order `s` require `2p+s <= k` and
`n < 4p`, not merely `2p <= k`. This is a prose correction; the source
has the stronger hypothesis. The Fourier integrability proof is now
included.

Read `Forcing/DeTurckTameComposition.lean` through the ordered product
bound. Read `Forcing/DeTurckResidual.lean` at the lower, trace and higher
input maps and their smooth-coordinate identities; these use orders
`r+1`, `2r+1`, `2r+2`, with forcing order `2r`. Read
`Jets/DeTurckJetAffine.lean` through the constant-plus-linear
decomposition, derivative weight argument, and identification of high
atoms as metric derivatives. Read `Jets/DeTurckSourceJet.lean` at its
weight-two source bounds and their ordered derivatives, and
`Jets/DeTurckRationalJet.lean` at the weight definitions.
Read `Forcing/DeTurckMixedForcing.lean` at coefficient extension near
a compact range, spatial affine action, constant-one augmentation,
time trace bound, and the ordered lower-source consumer. The prose
explains why the weight bound allows at most one unrestricted high
factor; it does not treat an arbitrary product of L2 factors as L2.

The local construction remains under review. This pass does not yet
accept its parameter regularity, continuation or Shi-estimate
producers, nor does it certify every imported elliptic lemma. No Lean
source was changed.

## Shi Localization And Energy Induction

Replaced the generic derivative-estimate sketch by its actual local
induction. Read `Curvature/Estimates/Derivative.lean` through the
local prefix induction and positive-time theorem;
`Shi/Induction.lean` at the half-window transport, product energy,
shifted step and initially controlled step; and
`Shi/Energy/ShiftedHeat.lean` at the scaled reaction bounds and
product-energy absorption. The paths in this paragraph are relative
to `Geometry/RicciFlow/`, with `Shi/` under `Curvature/Estimates/`.
Read `Shi/Energy/Bernstein.lean` through the actual tensor-norm
gradient calculation and cross-term argument, and
`Shi/Energy/GeneralHeat.lean` in full. The generic heat endpoint
remains to be reconciled with the chapter's preceding tensor
commutator discussion; this bounded pass does not certify its full
import tree.

The new proof fixes the scale at the target time, uses the past half
window, and retains natural subtraction in the initially controlled
orders. It gives the product `(8H^2+1+W_m)W_(m+1)`, the discarded
next-energy coefficient, the negative quadratic term and the cutoff
threshold. The nested radii end at half the initial radius. All final
constants precede the manifold, center and flow. The stronger local
prefix producer does not silently weaken the global hypotheses of
the second displayed theorem.

Read `Shi/Cutoff/Geometric.lean`, `SpatialSupport.lean` and
`Comparison.lean` in full; `Profile.lean` at the squared cutoff
derivative bounds; `Carrier/Recentered.lean` in full; and
`Carrier/BallRetention.lean` at its first-exit path argument and
compact carrier construction. The evolving retained radius and
initial carrier radius remain distinct. The text explains why the
exponential scale makes the cutoff nonincreasing, allowing a spatial
lower support to be held constant along the past-time interval.

Read `Shi/DistanceSupport/Energy.lean` and `ApproximateJets.lean` in
full; `SquareRoot.lean` through the scalar square-root expansion and
uniform radius choice; `JetBounds.lean` at the integrated actual
energy-jet estimates; and `Native.lean` at the geometric assembly
from `exists_shi_native_distance_upper_support` through its final
consumer. The earlier full-file output for `Native.lean` was truncated
and is not counted as a full-file review. Read
`Shi/Coordinates/UniformJoinedAtlas.lean` in full and
`Paths/JoinedVariation.lean` through its endpoint-jet construction
and actual time derivative. Inspected the energy-path sequence
producer and its use of positive-speed reparametrization.

The text develops the approximate path-energy route to an exactly
touching distance support: one finite chart subdivision, parallel
frames, joined coordinate variations, first and second energy jets,
uniform cubic errors, square-root jets, and a single convergent
subsequence before choosing the spatial point. The added quadratic
term changes the trace by at most the specified epsilon. Auxiliary
chart constants may depend on the metric; the resulting gradient
and trace bounds used for the cutoff do not.

Compared directly with Morgan-Tian's original `latex-source/flowbasics.tex`,
the proof of Theorem 3.29 and its product-energy claim and cutoff
proposition (printed pp. 52-57). The book uses running-time weights
and an exponential-map cutoff. The implementation uses fixed-scale
half windows and capped evolving distance supports. Both retain the
successive-energy product argument; no novelty is asserted.

Followed `Shi/Coordinates/Normal.lean` at its Hessian operations,
quadratic coordinate correction and normal-chart constructor;
`Frames/ODE.lean` in full and `Frames/Bounded.lean` at the uniform
mesh and bounded-frame assembly. The text now gives the second-jet
chart normalization, the mesh inequalities and preservation of frame
pairings. Read `Paths/JoinedDensity.lean` at the explicit position,
velocity, density and uniform Taylor consumer, and
`Paths/UniformTaylor.lean` through the compact tube, third-derivative
bound and line Taylor argument. Read the full energy-path sequence
producer in `Paths/Energy.lean` and
`Curvature/Derivatives/Heat/Endpoint.lean` in full. The latter extends
the interior inequality to included endpoints by continuity of the
actual norm energies and their derivatives on a nontrivial convex
interval.

Followed `Curvature/Derivatives/Heat/CorrectionGeneral.lean`,
`Heat/General.lean`, `CorrectionGeneral.lean` and `Evolution.lean`
in full, and `Reaction/Bounds.lean` at the recursive reaction
representation and its norm bounds. The evolution is built by
differentiating the preceding reaction and adding the actual time
and Laplacian commutators. Its contractions preserve total derivative
order. The squared-norm bridge combines this identity with Bochner
and the explicit inverse-metric correction at rank `4+m`; the
correction is bounded componentwise by
`2(m+4)n^(m+6) N_0 N_m^2`. This agrees with the proof's treatment
of that contribution. The prose keeps arbitrary dimension/order
constants where their exact numerical value is immaterial.

This resolves the displayed proof sketch and checks its principal
producers and consumers. It is not whole-chapter acceptance or a
claim that every imported tensor-calculus helper was independently
reviewed. The final sequential dependency/readability pass remains
pending.

## Busemann Exhaustion and Stationary Injectivity

Expanded the proof under "Why bounds on separate slices suffice" after
reading `Geometry/Riemannian/Soul/{Ray,BusemannConcavity,Horoball,
ExhaustionFunction,CompleteGeometry,Exhaustion,Injectivity}.lean` in full.
The argument constructs the Busemann limits with their actual negative
sign on rays, obtains concavity from normalized squared-distance
supports, and proves compactness of the common sublevels by a limiting
ray contradiction. The common ultrafilter is selected before the time
parameter; the existence of a limit at each time follows from properness.
Read `Comparison/Toponogov/Support/Hessian.lean`, `Tail.lean` and
`Global.lean` in full at this step. The tail nonsingularity and radial
index-form producers remain ordinary comparison prerequisites for the
final dependency pass; they are not claimed fully reviewed here.

Read `Comparison/Injectivity/Radius/{Basic,LowerSemicontinuity,
Stability,Nonconjugacy,CutLoop,TwoGeodesics,ConvexDescent}.lean`,
`Comparison/Injectivity/{Nonconjugacy,LocalInverse,Collision,
InverseRadius,ReturnDirection,FirstCollision,MovingEndpoint,ConvexLoop}.lean`
in full. The replacement now explains the compact stability of the
total exponential, attainment and equal radii of the first collision,
opposite terminal velocities, and the unequal-length shortcut bound
used after reversing the moving branches. It retains lower
semicontinuity rather than asserting differentiability of injectivity
radius. The weighted minimum is taken on a compact convex sublevel;
the moving point stays in that same sublevel by strict exhaustion
descent.

Read `Analysis/ODE/Jacobi/{LowerBound,ComparisonRadius}.lean` and
`Comparison/Volume/{ExponentialLower,Injectivity,Nonnegative}.lean`
in full. The text gives the actual cubic Jacobi remainder, a uniform
nonsingularity radius and the conservative determinant expansion
bound `1/(n! 2^n)` used in volume integration. The resulting positive
unit-ball volume constant depends on the component through the
minimum on the compact zero set; it is not dimension-only.

Directly inspected the archived Maeder-Baumdicker--Seidel manuscript,
printed pp. 15-19, 29-31 and 35-37: Lemmas 3.8, 3.13 and 4.10,
Corollary 4.12 and Lemma 5.1. The paper continues through successive
soul strata and proves a stronger comparison. The implemented smooth
argument uses a nonnegative convex exhaustion and a small linear
penalty to derive precisely the uniform positive bound needed here.
This specialization is now explained in the narrative. No source
discrepancy or novelty claim is inferred from the difference.

## Expanding Cylinders and Volume Passage

Replaced direct cylinder point picking by the actual threshold-region
selection followed by backward confinement of terminal balls. Read
`CurvatureControl/ThresholdPointPicking.lean`,
`Analysis/Parabolic/PointPicking.lean`,
`CurvatureControl/Cylinders/{Scalar,Expanding/FromVolume,Expanding/Selection}.lean`,
and `CurvatureControl/Distance/{Confinement,FiniteCalabi,FiniteContinuity,
RicciIntegralCutoff}.lean` in full. Read the Ricci-integral estimate and its
consumer in `Distance/RicciIntegral.lean`; the intervening parallel-field
construction is not claimed fully reviewed. The text distinguishes the
threshold set from the entire shorter moving cylinder and supplies the
strict-support minimum argument for confinement, avoiding circular use
of the sought fixed-ball bound.

Expanded fixed-initial-ball differentiation and volume propagation after
reading `InitialVolume.lean`,
`CurvatureControl/{Assembly,VolumeToCurvature,ScalarIntegral,BallVolume}.lean`,
`CurvatureControl/VolumeRatio/{Monotonicity,BallComparison}.lean`, and
`AncientVolume/Volume/{TerminalMonotonicity,Noncollapse,LimitLowerBound}.lean`.
These paths are under `Geometry/RicciFlow/Harnack/Noncompact/`, except the
explicit analysis path above. The positive ancient volume ratio is
propagated using additive distance comparison and decreasing fixed-set
volume, with two-sided metric comparison at the terminal endpoint; this
step does not invoke Harnack. The required bounded ancient zero-volume
theorem remains a substantive cross-chapter obligation.

Read `CurvatureControl/Cylinders/Expanding/{SmallBuffer,VolumeBounds}.lean`,
its `Volume/{Limit,Selection}.lean`, and
`AncientVolume/Splitting/CompleteCoverage.lean` in full. Read
`Splitting/LimitTransport.lean` at the inverse distortion producer
(lines 266--384). The prose now accounts for the factor two in radius on
moving to an interior time, producing coefficient `nu/4^n`, and then
preserves that coefficient in the complete limit. Forward embeddings
alone would give the wrong direction for this volume lower bound.
Completeness supplies compact limit balls; first-exit path lifting covers
source balls. Inverse comparison on source `3A`-balls and forward
comparison on limit `6A`-balls give two-sided distance control, followed
by calibrated Hausdorff-measure comparison and distortion tending to one.

Compared the corrected Kleiner--Lott journal archive directly at
Corollaries 44.1 and 45.1(a), equations (45.5)--(45.10), printed
pp. 2682--2685. Recorded the archive hash and local fixed-volume sign
misprint in `references/ricci-flow/kleiner-lott/provenance.md` under this
publication tree. Corrected the bibliography key and added the full entry.

## Scalar Cutoff Comparison

Read `CurvatureControl/{PointPicking,ScalarEstimate,ScalarCutoff,
ScalarContact,ScalarContactFinite,ScalarComparison,RightBounds}.lean`,
`Distance/{Cutoff,FiniteCutoff}.lean`, and
`Analysis/Parabolic/LowerSupportComparison.lean` in full. Expanded the
scalar proof to include the flat cutoff profile, explicit constants,
upper distance support becoming a lower cutoff support, the spatial
gradient cancellation, and the strict exponential maximum on one compact
terminal ball. The lower time support at a past maximum has nonnegative
derivative, which contradicts the strictly negative weighted derivative.
This explains why no differentiability of the maximum function or of
distance at cut points is assumed.

Directly inspected Chen's archived `0706.3081v2.pdf`, printed pp. 10--12,
Theorem 3.1, its proof and Corollary 3.2. The chapter explicitly identifies
the implemented scalar specialization under nonnegative Ricci curvature:
Chen's theorem concerns full curvature without that hypothesis and
localizes its square. No novelty claim is made. The source comparison
and these bounded producer checks do not accept the full chapter; the
ancient cone and pointed compactness constructions remain pending.

## Shared Squared-Distance Comparison

Added Section sec:rf-distance-comparison and
lem:rf-squared-distance-comparison before the flow analysis. It defines
the index form, obtains nonnegativity from an actual fixed-endpoint
piecewise smooth variation and the length-energy bound, and develops
the negative-index contradiction for an interior Jacobi zero.
The shortened minimizing tail then has a nonsingular radial endpoint by
reversal and Jacobi uniqueness. Its actual inverse exponential branch
provides the touching distance majorant.

Read the subject-level Toponogov export, Hinge, Triangle, Semiconcavity,
Global, Shift, Tail, Regular, IndexComparison, RadialHessian, and
Support/{Hessian,Initial,Radial}; read Volume/Conjugate/{NoConjugate,
Frame/Negative,Variation/Minimizing,Radial/Nonsingular} and
Analysis/Convex/UpperSupport. These reads follow the supplied geometric
prerequisites down through their substantive producers rather than
treating the paired comparison export as a proof.

The draft develops the affine Jacobi test, Hessian bound for the inverse
radius, exact shifted-square error 2/(1-theta), and arbitrarily small
upper-support error. It proves the scalar concavity criterion by a
perturbed chord with an interior minimum, then obtains the hinge from
the selected endpoint derivative and corresponding sides from two
successive chord inequalities. At the pole it uses the geodesic length
upper bound. Thus the same local argument applies to any constant-speed
geodesic, including the every-geodesic Busemann-level consumer; the paired
triangle export only needs minimizing sides. Ancient-model consumers now
refer to this precise shared result.

Directly read Morgan--Tian Theorem 2.4, printed p. 23 (PDF p. 66), and
Petersen Lemma 7.1.9, printed pp. 284--285 (PDF pp. 299--300).
The latter supplies the actual shifted-pole and reversal comparison.
The PDF offset differs from the later Petersen soul pages, so page labels
were checked directly.

**Source citation discrepancy:** several no-conjugacy/index files cite
Morgan--Tian Theorem 1.34, p. 19. In the archived 2007 book that result
is Bishop--Gromov relative volume comparison, not no interior conjugate
points. Directly inspected pp. 17--19. The mathematical no-conjugacy
argument is developed above; publication uses the relevant Petersen
locator. No Lean source or read-only reference was changed.

The underlying local exponential/ODE, parallel-transport and coordinate
variation infrastructure is ordinary geometric background. Its uses in
the broader compactness and analytic constructions are still reviewed
separately. This bounded comparison review does not accept this chapter.

## Retained Ball Volumes and Static Noncollapse

Added lem:rf-limit-static-noncollapse after the pointed-convergence
construction. The argument requires an already supplied convergence and
a complete limit slice; it does not claim to settle the construction of
the limit itself. Read Compactness/Convergence/Volume/{Noncollapse,
AtPoint,Convergence,Spheres} and Curvature/Uniform in full.

Developed source-ball coverage at arbitrary embedded limit centers using
the actual inverse maps and a first-exit length contradiction. Tangent
norm factors C and C inverse give volume Jacobian factors C to plus/minus
n and the two ball-volume inequalities. Positive-radius sphere nullity
follows by covering it with the smooth exponential image of the null
Euclidean tangent sphere. Dominated indicators on one compact larger
ball then give radius continuity at every positive radius, permitting
the distortion factor to tend to one.

For noncollapse, the draft explicitly chooses rho < a < r before taking
the eventual index. Uniform second metric jets give uniform curvature
norms on the compact closure of the a-ball. The strict gap between
r^(-2) and rho^(-2), together with source-ball coverage, verifies the
source antecedent on the whole source rho-ball. Ball-volume convergence
and rho increasing to r preserve kappa exactly. No source completeness,
curvature sign or uniform index over all centers/radii is silently used.

The shrinking-model limit, unbounded-scalar cylindrical reduction and
later noncollapsed limit in ancient-models now use this precise lemma;
the kappa/729 and kappa/27 constants remain those of their preceding
static reductions. Static implies parabolic noncollapse because the
parabolic antecedent includes the terminal ball bound.

Directly compared Kleiner--Lott Corollary 44.1, pp. 2682--2683, and
the previously inspected Appendix E, pp. 2848--2849. This develops a
limit-passage input; broader atlas construction, analytic estimates and
whole-chapter acceptance remain pending.

## Finite Compactness Embeddings

Expanded the actual finite-chart induction in sec:rf-compactness. Read
Stages/SourceEmbedding/{Finite,Extension,Separation,ChartContainment,
LocalReadout,LocalModels}, following the two-chart SourceEmbedding and
SourceSeparation producers. The old compact region A is contained in
the interior of a larger compact A', which lies in the current open
embedding domain. The new chart cutoff covers every identification
with A', including boundaries of the closed new coordinate piece.

The draft now derives actual inverse-coordinate containment using
uniform chart lower bounds and connected small source balls, without
source completeness. Retained local corrected-chart formulas give
distance approximation and, by composing source and limit transitions,
all-jet readout convergence in any overlap chart. Thus these properties
are induction invariants rather than assumptions about a previously
glued map.

Uniform distance convergence keeps collisions away from the compact
complement of the larger overlap. Inside it, exact agreement and old
injectivity give source equality if and only if quotient equality.
The union of the two retained interiors is therefore an open smooth
embedding. Its compact closure, local formulas and protected basepoint
formula persist. The old open domain may shrink at each step while its
retained compact set stays inside; this is now explicit.

Directly reread Morgan--Tian Theorem 5.6 proof, printed pp. 86--87
(PDF pp. 129--130). It summarizes this step by partitions of unity.
The draft develops the implementation's relative correction construction
and distinguishes finite patching from the later exhaustion diagonal;
maps into different source manifolds require no mutual agreement.

This resolves the finite embedding step's previous compression.
Atlas extraction, boundary escape, other analytic producers and the
full chapter review remain pending; no acceptance is inferred.

## Radius Exhaustion and Zero-Time Completeness

Replaced the compressed boundary-escape paragraph by the actual radius
construction. Read Overlap/{Coverage,CompactCoverage,Connectedness,
Radius}, Stages/BoundaryEscape, SourceEmbedding/Boundary, and
GeometricLimit/{BoundaryCoverage,SourceBallCoverage,Complete}.
The fixed finite source-ball covers remain an explicit input from chart
extraction; their existence is not inferred from separate finite covers
with unbounded cardinalities.

The draft follows a possibly changing covering chart by finite
pigeonhole and compact coordinate convergence. The upper Lipschitz
bound produces a zero-distance partner, giving compact auxiliary-radius
sublevels. It also proves quotient connectedness by transferring a
putative clopen partition to disjoint closed unions covering a connected
source ball. Taking basepoint components gives compact nested closures
and constant boundary radius.

Finite compact chart representatives make source basepoint distances
converge uniformly on each entire boundary. Boundary avoidance, an
embedding defined beyond the closure, and connectedness of source balls
then give actual whole-ball coverage. Coverage of a doubled source ball
and embedding injectivity trap each smaller Riemannian limit ball in a
fixed compact stage, proving Cauchy completeness.

The auxiliary radius is not identified with the Riemannian distance in
this argument. Neither source completeness nor existence of minimizing
source geodesics is used. Directly reread Morgan--Tian Theorem 5.9 and
Corollary 5.10, pp. 88--89 (PDF pp. 131--132), alongside the preceding
Theorem 5.6 construction.

The remaining compactness review is upstream: uniform controlled
coordinates and the fixed finite covering family, mixed-jet extraction
and smooth metric descent. The whole chapter is still pending.

## Uniform Covers and Injectivity

Expanded the fixed finite-cover producer after reading
Coordinates/{Covering,Ellipticity,Uniform}, Comparison/Covering and
Comparison/Injectivity/Uniform. Local relative volume comparison on a
compactly closed enlarged ball supplies a uniform lower volume for
each small center ball. A separated-center packing argument then gives
a cardinality bound by the model-volume ratio, with the basepoint
inserted and the index set padded uniformly.

The draft separately explains transport of base noncollapse to bounded
centers, Jacobi nonsingularity, and the global exponential collision
contradiction: a first collision yields iterated distinct radial sheets,
whereas tangent-ball volume packing bounds their number. The resulting
closed-ball injectivity radius supports the normal charts and their
two-sided ambient distance estimates. No completeness of source
manifolds is used; compact closure keeps all radial comparison inside
the controlled ball.

Direct source comparison used Morgan--Tian Theorem 1.34 p. 19 and
Theorem 5.6 pp. 86--87 (PDF pp. 60 and 129--130), plus the producers'
local injectivity and packing arguments. This is upstream construction
review; the Ricci-flow chapter remains pending.

## Mixed-Jet Metric Descent

Read Stages/{JetConvergence,QuotientJetConvergence,
QuotientMetricConvergence}, SourceEmbedding/{MetricConvergence,
SpacetimeMetricConvergence,LocalReadout}. The draft now explains the
actual local source readout formula: compact containment puts each
retained map in one source chart, the inverse readout converges to the
identity in every spatial jet, and the chain/product rules transfer
the original spacetime metric coefficients to the glued embeddings.
Finite covers give a common threshold on each compact, while diagonal
selection handles all mixed derivative orders. This closes the prior
gap between distance convergence and the frozen all-jet metric claim.
The construction and chapter remain pending pending full upstream
analytic review.

## Derivative and Time Bounds

Read Coordinates/JetBounds, DerivativeControl, InteriorDerivativeControl,
Coordinates/SpacetimeBounds/{SpatialBounds,NormalCharts,Bounds} and
MetricComparison/Coordinates. The draft now distinguishes finite-order
tail intersections for zero-time normal-coordinate jets from the
all-order diagonal argument. It records the Gauss identity and
normalized initial metric as the geometric inputs to the finite-order
pullback estimate.

For time transfer it states the actual pointwise Ricci contraction,
the metric evolution/Gronwall exponential comparison and the need for
a curvature bound at the fixed image point for every time. The mixed
time derivatives then come from differentiating the flow equation with
the local Shi bounds. Compared Morgan--Tian Proposition 5.14
pp. 90--91 and Theorem 5.15 pp. 91--92 (PDF pp. 133--134).
This closes the current producer-to-exposition interface; the chapter
remains pending until the complete source/readability pass.

## Full Compactness Reread And Atlas Correction

Reread the whole pointed-compactness exposition, including finite patching,
compact auxiliary-radius sublevels, source-ball coverage and completeness
at every interior time. This pass supersedes the earlier outstanding
geometric compactness items above; shared analytic estimates remain separate.

Found and corrected a substantive stale paragraph: the local injectivity
proof does not exclude finite loop periods by shortening a radial geodesic,
and its sheet count is not the finite-cover model-volume ratio. The count
is chosen from the transported noncollapse lower volume and upper pullback
mass, and the collision radius depends on that count. Finite periods are
excluded by strict convexity of the finite-orbit energy. The draft now
states this distinction and references the fully developed local metric
argument in the ancient chapter without assuming its ancient-flow result.

The existing native review fully inspected the remaining collision,
inverse-radius, returned-loop, confined lifting, smooth deck motion,
Jacobi pairing, radial convexity and finite-fiber volume producers. Its
bounded reconciliation found no additional defect in the ancient proof.
Added the first-collision compactness/gradient argument, smoothness of
radial deck motion and countable disjoint change-of-variables partition.

The normal-coordinate review followed the radial transport variation,
connection kernel, component jets, radial integral and matrix/Jacobi
parameter estimates. The ancient passage now derives the radial connection
integral and its derivative bounds; the Ricci-flow passage references that
local calculation. The triangular order restriction is l+m<=N, without
hidden derivative loss. Augmented linear ODE bounds and Gronwall are
ordinary background, not a remaining specialized proof obligation.

Read `Compactness/GeometricLimit/Overlap/{Coverage,SourceTransition,
Transition,Gluing,DistanceMetric,JetBounds,Smooth,MetricLimit,
MetricFamilyLimit,RicciFlow}.lean` in full. Source-ball coverage from a
compact coordinate closure gives fixed domains and compact targets for
the actual inverse transitions. Compact partners prove overlap openness;
metric preservation and the Christoffel transformation control every
transition jet. Unique continuous limits identify all smooth subsequences.
The quotient distance induces the chart topology; countably many open
chart bases give second countability. The draft distinguishes this distance
from the path metric constructed from the coefficient limits.

Displayed tensor compatibility, retained positivity and passage of the
coordinate Ricci equation using continuous inversion and mixed jets.
Corrected a malformed pullback that omitted the embedding differential;
the readout now explicitly uses the matching limit/source chart so that
its limit really is the identity. Independent rereads of the edited atlas,
injectivity and radial passages found no further substantive defect after
these notation corrections. This is bounded construction review, not
acceptance of the chapter or of all its upstream analytic inputs.

## Local Existence, Uniqueness And Continuation Reread

Reread the complete local-theory section after the earlier generator and
derivative-budget corrections. The spectral form/response and residual
calculations agree with the stated construction. Read
`DeTurck/Construction/QuasilinearDeTurck.lean:200-415`,
`Construction/DeTurckResponseMetric.lean` in full,
`Construction/DeTurckPositiveState.lean:1-160`,
`Forcing/DeTurckParameterForcing.lean:35-125,415-545` and
`Regularity/DeTurckTraceCutoff.lean:315-383`. These paths are relative to
`Geometry/RicciFlow/Local/`. The draft now fixes the trace-decoder norm
radius before the residual cutoff and forcing radius, explicitly retaining
the strict positive-metric margin. The source's principal cutoff constant
includes 1/radius; enlarging it preserves the mixed estimate and ensures
twice the forcing radius is smaller than the exactness radius.

The existing native parameter review identified a missing substantive
step in the former smooth-orbit paragraph. It followed
`Forcing/DeTurckParameterForcing`, `Construction/DeTurckBackgroundVariation`,
`Forcing/DeTurckParameterBackground`,
`Gauge/{DeTurckPullbackForcing,DeTurckPullbackResponse}`,
`Forcing/DeTurckSpatialParameter` and `Gauge/DeTurckSpatialRecovery` at
their actual equation, covariance, approximation, continuity and recovery
producers. The draft now gives the seed/background parameter equation,
the negative generator seed term and the positive generator-pullback
commutator in the transported zero-initial forcing. Background change
cancels the current second jet. Strong continuity, positive smooth
approximation and local uniqueness identify the actual pullback orbit
with the smooth implicit-function branch on the original time interval.
Smooth approximants need not themselves solve the equation. Local spanning
flows then recover smoothness into C([0,T]), before the equation gives
time regularity. The implicit-function theorem, Neumann inverse and local
ODE calculus are ordinary background; the specialized identification is
now exposed. The one-sided gauge construction has the negative field and
one interval for every derivative order, by ODE uniqueness of finite-order
extensions, not an intersection of shrinking existence intervals.

The native uniqueness review found another genuine compression: derivatives
of the connection difference cannot be absorbed by Young's inequality
in the old energy without first using the divergence flux. Read the actual
flux definition and bound in `Curvature/Energy/CurvatureDifferenceFlux.lean`
through line 220; the independent review checked its equation consumer
`CurvatureRateCoordinateAlgebra.lean:482` and
`Energy/Comparison/UniquenessClosure.lean:399,919`. The draft now displays
the flux, inverse-metric difference and derivative-free connection remainder,
integrates the flux by parts, and retains an ellipticity-dependent positive
dissipation coefficient. It no longer asserts an unnormalized coefficient
of one. The finite cutoff/density errors are controlled by the global
coordinate energy.

For continuation the independent review checked
`Connection/{RateEnergyAlgebra,DifferenceEvolution}` at the actual
connection-jet induction, `Energy/Comparison/ScalarMixedDerivative` at
uniform jet limits and joint smoothness, and `Continuation/Gluing`.
The draft now shows why order-m inverse-metric and curvature-coordinate
jets use only connection jets below m; the time rate of the missing
connection jet is then bounded before integration. Smooth positive endpoint
metrics and matching mixed derivatives follow. Independent rereads of the
edited local passages found no remaining substantive defect, with strict
trace margins and covariance for arbitrary smooth approximants clarified.

Directly inspected Morgan--Tian Theorem 3.11 pp. 39-40, Proposition 3.12
p. 40 and Proposition 4.12 p. 68 in the published PDF, and the original
`flowbasics.tex` local-theory proof. Its strictly parabolic existence sketch
does not itself supply the implemented spectral parameter construction or
the displayed three-tensor comparison energy. Recorded this source
distinction and the already documented pullback-sign correction without
claiming novelty or changing any formalization/reference artifact.
The local construction is now boundedly reconciled; whole-chapter
readability, remaining tensor/comparison prerequisites and acceptance are
still pending.

## Harnack Constants, Kernel Inputs And Marked Limits

Sequentially reread the Harnack, scalar-integral and volume-to-curvature
passages. The existing native numerical reviewer checked the actual
coefficients in `Harnack/Matrix/Positivity/PerturbedReaction.lean:362`,
`PerturbedHeat.lean:206,226`, `Matrix/Bounds/PrescribedJet.lean:90,125`
and `PerturbedTimeContact.lean:313,372,383,431` (relative to
`PoincareLib/Geometry/RicciFlow`). The draft now separates the reaction
loss from the spatial-jet loss, gives K_P and K_M, and derives D(tau)
and the polynomial constant C. The inverse-time term in M and the
inverse-square-time jet term have distinct origins. No bound on alpha
is assumed; alpha psi <= alpha uses only 0 <= psi <= 1. An independent
reread of the edited arithmetic found no remaining defect.

The lower heat-kernel review followed the Dirichlet resolvent and spectral
response through `Heat/Kernel/Regularity/{SpatialJets,RowJets,KernelJets,
SpacetimeJets}` and `Heat/Kernel/Exhaustion/{Regularity,AllTimeMoment}`
(relative to `PoincareLib/Geometry/Riemannian`). Read SpatialJets and
AllTimeMoment completely and the exact KernelJets factorization at
lines 193-231. The draft exposes coercive energy, compact self-adjoint
resolvent, operator-power bounds, fixed interior regions before the
containing domain, Riesz rows and the fixed-row factorization. These
give uniform joint jets on positive-time compact cylinders and identify
the smooth exhaustion limit. High-order constants depend on the fixed
smooth metric and charts, not merely dimension and a Ricci lower bound.
Ordinary spectral theory, Rellich compactness and local elliptic/Sobolev
regularity are background; the domain-uniform argument is developed.
Directly read the archived Evans PDF at printed pp. 286, 327, 332-333
(PDF pp. 301, 341, 346-347) and added exact theorem locators. The source
directory's checked compactness note records the zero-boundary remark
at printed p. 289. The reference mirror was not edited.

The previous smoothing argument used a later-time kernel row without
explaining its integrable first moment. Added the semigroup, conservation,
triangle inequality and Tonelli argument M_(s+t) <= M_s + sup M_t, then
finite subdivision into times at most one. This supplies all-time
integrability without claiming an all-time Gaussian bound. Independent
reread requested an explicit 0<t<=1 restriction on the square-root
displacement estimate; it was applied. The open-domain and boundary
regularity conventions were also clarified.

For the concentration limit, read `Geometry/Riemannian/Compactness/Pointed`,
`Geometry/Curvature/Integral/Concentration/FiberLimits`,
`Topology/MetricSpace/GromovHausdorff/Pointed/Convergence/ExpandingSubsets`
completely, the CornerModels definitions through line 180, Extraction/Radial,
and Limit/ClosedBallTransition:180-300. The existing native reviewer
followed finite-net packing, marked extraction, CrossRadius:328,801,
LengthLimit and expanding realizations. The former compactness invocation
omitted a necessary construction: the consecutive stage transition covers
the strict inner ball, and n>R+1 pulls all later radius-(R+1) points into
one compact stage. Its closed image contains the completed radius-R ball.
The draft now gives this proof of properness, approximate splits and
geodesics, and bounded-region convergence. Compact stages are not assumed
geodesic. The varying realization spaces need no mutual compatibility.
Near-images of the actual radius-3/2 fiber sections and compact-subset
convergence give K, both directional errors, the radial bound and basepoint.
No limiting defining function, noncollapse or curvature upper bound enters.
Finite-distance continuity transfers the required comparison and packing
inequalities. Independent reread of the actual expansion found no defect.

These bounded checks close the specific omissions above. They do not
by themselves accept the chapter or certify the complete book.

Completed the sequential reread of the full harmonic-coordinate section,
the normalization and distance-comparison opening, and the closing
interfaces. Reused `harmonic-coordinates-integration-v4.md` rather than
repeating its source traversal. The fixed metric's qualitative weak
regularity precedes uniform estimates; the small coefficient tolerance
precedes the metric; the Hessian divergence flux avoids curvature
derivatives; the Gaussian cancellation absorbs the half-Holder seminorm.
The radius S/128=2r and local surface specialization agree with the
reviewed construction. The closing interface retains the absolute
pinching clock and bounded-slab Harnack before the zero-volume-ratio
argument. No further substantive defect was found in this reread.
The new Evans citations initially failed the publication checker because
the key was absent from its bibliography; copied the existing archived
entry into the publication bibliography without editing references.

## Chapter Decision

The Ricci-flow chapter is accepted by the main integration reviewer after
the extinction calibration, with the exact draft digest recorded in its
JSON review. The complete text has received sequential readability passes
and the substantive producer reviews documented above. The final native
ancient-models reread also checked the consumer at ricci-flow.tex:3745-3968:
the bounded ancient zero-volume theorem uses only bounded-slab Harnack,
then supplies the slab-control contradiction needed for full slice-wise
Harnack. The fixed-factor and scalar-positivity corrections in the ancient
chapter preserve this order. That bounded predecessor argument is reviewed
independently of the ancient chapter's reduced-geometry inputs.

This decision supersedes the historical RF-HARMONIC-COORDINATES,
RF-LOCAL-ANALYSIS, RF-HARNACK-BLOCK, RF-HARNACK-GEOMETRY,
RF-ANCIENT-AVR, RF-COMPACTNESS-DETAIL and RF-PINCHING-CONTACT
next-action fields: their concrete mathematical obligations are reconciled
by the recorded expansions and rereads. It does not accept other chapters,
the whole book, source-link publication or final rendering. A changed
input or draft digest reopens the affected review.

## Remaining Publication

- The whole Ricci-flow text has now had sequential rereads, with concrete
  corrections recorded above. Preserve those reviewed arguments during
  integration; do not reopen ordinary background without a specific gap.
- Preserve the reviewed ancient bounded-flow zero-volume-ratio interface
  when integrating the ancient-models chapter.
- Update the finite outstanding-issues list and integrate the accepted
  digest when the remaining chapter reviews finish; final PDF/site,
  link and citation inspection remains a separate book-level gate.

No Lean build, make check, endpoint audit or comparator was run. Operator
direction 2418 requires reuse of pinned verification while source is unchanged.

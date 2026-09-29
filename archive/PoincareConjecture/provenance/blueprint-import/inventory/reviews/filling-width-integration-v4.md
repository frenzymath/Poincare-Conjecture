# Filling Width: Integration Review

Status: source and readability passes completed; the separate acceptance
decision and final draft digest are in `filling-width-v4.json`. The main
integration reviewer owns this review after the author finished. Source pin:
`751329327f4f582797bda8e6cffe7cdf7531cc1d`. The author pin remains recorded
separately in `filling-width-v4.json`. No Lean source was changed or rebuilt.

## Findings Corrected

1. The original M53 proof described transverse mod-two intersections. The
   implemented argument uses integral relative homology and intrinsic parity.
   `prop:filling-sphere-separation` now explains the relative fundamental-class
   lift, local parity propagation, two-puncture cylinder coordinates, primitive
   signed diagonal, and contradiction at the local sphere generator. Read:
   `EmbeddedSphere/Separation.lean`, `Separation/LocalParity.lean`,
   `Parity/ModelBoundary.lean` under `PoincareLib/Topology/Manifold/`.
2. The author's M56/M57 reconciliation incorrectly assigned the constructions
   to finite-history. New `sec:filling-component-ancestry` and
   `sec:filling-ancestry-transport` develop the actual forward ancestry and
   selected component geometry. Read the `Finite/` Main, PoincareConstructor,
   FiniteAncestry, EventGap, FiniteTrace, EventTrace, EventOverlap, GroupInduction
   files and `Transport/` Main, Adapters, Event/{AncestryInput,EventInput},
   Comparison/{ComponentGeometry,NeckSphereEmbedding,RetainedRegion} under
   `PoincareLib/Geometry/RicciFlow/Surgery/Ancestry/`. In particular the stored
   reference gap is proved using bounded curvature versus singular maximality;
   it is not assumed from event ordering. Only selected components are simply
   connected; the whole later slice can be disconnected or empty.
3. The short-disk proof claimed a quadratic area estimate. The actual estimate
   in `LoopSpace/Area/SmallDisks.lean` is linear, with `K = H*A*B` and threshold
   `min rho (min (eta/4) (eta/(K+1)))`. The draft now states and derives exactly
   that estimate. `DiskExtension.lean` fixes the time profile: one near the
   center and zero at the boundary. `ShortLoops/Triviality.lean` distinguishes
   contraction to varying constant loops from contraction to one constant
   family, the latter using connectedness and pi2-vanishing. The controlled
   collar derivative argument in Area/{ControlledContraction,Contraction/Time}
   now explains filling-area continuity.
4. The loop model and quotient were previously undefined or misdescribed.
   The revised text uses a map `q:I^2 -> S^2`, with exactly collapsed boundary
   fibers, the intrinsic first-jet topology, and jointly regular decorated
   families. Read `Topology/Homotopy/LoopSpace/{Basic,Family}.lean` and
   `Extinction/Width/Class/{Identification,IdentificationTheory}.lean`.
5. The noncompact universal-cover proof concerns **ordinary integral H3**, not
   compactly supported homology. The draft now gives the finite-cycle support,
   constant local orientation coefficient and Hurewicz argument from
   `Families/{NoncompactCover,NoncompactFreeClasses}.lean`. The compact branch
   develops the finite lifted-chain zero-diagonal trace argument read in
   `Families/CompactDeck/{FiniteModel,LiftedModel}.lean`,
   `CompactDeckFromComparison.lean`, `CoverFreeClasses.lean` and
   `LiftedFamilies/FrozenTransfer.lean`. These files are under
   `PoincareLib/AlgebraicTopology/HomotopyGroup/LoopSpace/`.
6. The least-sphere paragraph omitted the actual non-nullness argument. The
   revised text gives the all-non-null area infimum, its smooth energy
   comparison, the normalization `(E_alpha-4*pi)/2`, and the original-sequence
   annular replacement with explicit `a/12` errors. Read
   `MinimalSurface/Sphere/Minimizer/{Basic,Sequence}.lean`,
   `Minimizer/Smooth/Competitors.lean`, `AreaEnergy/Comparison/Basic.lean`, and
   `AlphaEnergy/Variation/Energy.lean`. It does not claim attainment in each
   prescribed free class. The variational and regularity review was completed
   as described below.
7. Fixed-map and minimal-sphere variation were claimed in metadata but absent
   from the prose. `sec:filling-sphere-variation` now derives the negative
   Ricci trace, metric-independent rank-deficient case, common integrable
   derivative bound, two-time exponential estimate, and logarithmic
   regularization through branches. Read `RicciFlow/Area/FixedMap/`
   {FixedMap,RicciTrace,GramDerivative} and `MinimalSphere/`
   {MinimalVariation,HarmonicCurvatureInequality,CurvatureIntegralBound,
   RegularizedCurvatureIntegral,IntrinsicRicciTrace}. The scalar lower bound
   can have either sign; the derivative is within the closed slab at endpoints.
8. `sec:filling-relative-square` now constructs both boundary deformations,
   including the exact null-homotopy parameter in the faithfulness direction.
   The compact-cover comparison now develops the finite selected-vertex
   induction, actual characteristic maps, cone calculation, open cover and
   Mayer--Vietoris comparison. Read `Families/{RelativeSurjective,
   RelativeFaithful}.lean` and `Comparison/Lefschetz/{OrderComplexLiftComparison,
   SupportedComparisonGluing,SupportedConeComparison,OrderComplexNeighborhoods}.lean`
   under `AlgebraicTopology/HomotopyGroup/LoopSpace/`.
9. The M54 calculation now explains the ball-filling isomorphism, paths from
   basepoints in a removed ball, both half-collar covers, clopen regions and
   composite retractions. Read `Surgery/GroupEffects/ConnectedSum/`
   {Reconstruction,Factors,RemoveBall,Coordinates} and `FactorData.lean`.
10. The admissible boundary homeomorphism was not assumed Lipschitz.
    `lem:filling-boundary-regularization` now gives the increasing angular
    lift, signed-length factorization, scalar annulus, almost-everywhere
    rank-one argument, exact gluing and area invariance. Read `LoopSpace/Area/`
    {Basic,Reparameterization,ParametrizedContinuity,ParametrizedCollarGluing,
    Boundary/Regularization,Boundary/IncreasingBoundaryRegularization,
    Annular/LengthArea,Annular/ScalarFactorArea,Collar/Gluing}. The new uniform
    collar proposition states the length-bounded input actually needed by
    the ramp approximation; the ramp draft now cites it.
11. The single pair contraction is now constructed by finite weighted chart
    operations and a tube neighborhood, with its finite-regularity
    qualification. It is not a discontinuous choice of a chart. Read
    `Topology/Homotopy/LoopSpace/Contraction/{Chart,Weighted,Finite,Local}.lean`.
12. M59 regular representatives now use the actual radial extension and its
    first-jet formula. Raw normalization transports the pole first; regular
    homotopies retain the original endpoint extensions because their observed
    jets agree. The continuous-value comparison explains finite chart error
    control and the two endpoint homotopies after cylinder approximation.
    Read `Families/{RadialLoops,RadialHomotopy,RadialFamilies,
    RegularRepresentatives,RawRegularization,RegularHomotopy,C1ValueComparison,
    C1HomotopyLifting}.lean` and `Comparison/FiniteChartApproximation.lean`.

## Variational Source Review

Read `MinimalSurface/Sphere/AreaEnergy/Comparison/C1.lean`: the draft now
shows metric majorization, uniformization, and the actual energy/area
inequality with dominated convergence through degenerate Gram matrices.
Read `AlphaEnergy/Minimizers.lean`, `Variation/{StrongConvergence,Attainment}.lean`
and `Critical/{Regularity,Holder,Smooth}.lean`. The text develops fixed-alpha
compactness, class retention, paired convex-chart replacements, strong
derivative convergence, supported variation, the same-map regularity gains,
and actual integral attainment. Global minimization over non-null maps is
explained, rather than attributed to the componentwise classical theorem.

Read `Minimizer/Compactness/{Interface,Basic,Bounded,Unbounded,Normalization,
Sequence,Equicontinuity}.lean` and `BubbleLimit/{Equation,StrongEquation}.lean`.
The text now gives the actual maximum-gradient normalization, density
one-half at the origin, retained subsequence and scales, first-jet compactness,
weighted-variation limit at zero gradients, energy exhaustion and puncture
removal. Read `Minimizer/Annular/{Basic,Replacement,Topology,Homotopy,Area}.lean`:
the replacement includes the two-parameter collar estimate, ball-extension
relative cap homotopy, unchanged outer map and original-class retention.

The background inputs are finite-dimensional compactness and standard
Sobolev/interior elliptic estimates, surface uniformization, harmonic puncture
removal and harmonic-sphere branch regularity. The specialized choices,
normalizations, class retention, same-map identification and area comparisons
are developed in the draft. The review is a source/exposition review, not a
new kernel audit of every imported analytic implementation lemma.

## Primary Source Comparison

Directly read the published Morgan--Tian PDF, printed pp. 424--428
(PDF pages 467--471). The original annular argument on p. 425 does not retain
the original approximating class correctly in its final sentence; the current
Lean constructor retains that class and derives the explicit smaller-area
contradiction. Claim 18.13 on p. 427 has a missing one-half in its displayed
metric variation; the formalization differentiates the square-root determinant
and obtains one negative Ricci trace, retaining the valid coarse constant four.
These are source corrections already documented in the imported M60 review,
not novelty claims by this book.

The Sacks--Uhlenbeck original was directly reread at
<https://math.jhu.edu/~js/Math748/sacks-uhlenbeck.pdf>: Theorem 1.6 (p. 5),
Theorem 2.1 and Propositions 2.3--2.4 (pp. 6--8), Main Estimate 3.2 and
Theorems 3.3, 3.6 (pp. 11--15), Theorems 4.4, 4.6--4.7 (pp. 16--18), and
Lemma 5.4 (pp. 21--22). Its domain-area-one energy convention differs from
the unit-round, half-energy convention in this chapter. Theorem 3.3 concerns
critical maps, not arbitrary small-area spheres; Proposition 2.4 is
componentwise; Lemma 5.4 permits splitting. None is cited as an unconditional
minimum in every prescribed free class. The imported record still correctly
states that original PDF bytes are not archived; no new archive/hash claim
is made. The publication-only uniformization citation is documented under
`references/complex-analysis/milicic/provenance.md`.

## Readability and Interfaces

The complete corrected chapter was reread in order. Objects and basepoints
are introduced before use; the three extremal operations are distinct;
nullity is pointwise, not a continuous choice of contractions; finite
ancestry does not make a later slice connected or nonempty. The common
initial metric/class is fixed before all targets, preserving the accepted
extinction interface. The independent readability pass prompted the explicit
finite chart contraction, radial-family argument, uniform collar proposition
and separation of the nontrivial-pi2 least-sphere conclusion from the
pi2-zero width identification.

The chapter's explicit predecessors are
`cor:foundations-homotopy-groups`, `prop:foundations-triangulation`, the
controlled global flow, and `thm:comparison-transport`. Acceptance does not
accept those entire chapters. Compare `ramps.tex`,
`sec:ramps-family-approximation`: its unrestricted raw families and combined
length bound now match `prop:filling-uniform-collars`. Compare
`annular-comparison.tex`, `sec:annular-interfaces`: it uses arbitrary free
near-minimizers and retains the short-or-area maximum before the extinction
step; neither a based competitor restriction nor minimum attainment is added.

The annular author's proposed Plateau dependency has been assigned to a
section of that chapter, before `sec:immersed-disk-comparison`. It is an M65
construction, beyond this chapter's filling infimum and least sphere. The
current source allows boundary branches and requires within-C1 boundary
regularity; the annular text and `AC-PLATEAU-CONTRACT` now record that exact
obligation. The active integration reviewer owns its expansion, including
boundary Gauss--Bonnet. It is still a whole-book gap, not an accepted result.

Final rendering and upstream/consumer chapter acceptance remain whole-book
gates. A passing publication checker is not mathematical acceptance, and no
Lean source, contract, dependency, toolchain or reference mirror was modified.

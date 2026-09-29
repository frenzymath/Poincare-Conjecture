# Annular Comparison: Integration Review

Status: source and mathematical readability passes completed; chapter
accepted with explicit predecessor results. The exact digest and decision
are in `annular-comparison-v4.json`. The author has finished and the
integration reviewer owns these corrections.
Source pin: `751329327f4f582797bda8e6cffe7cdf7531cc1d`.
The original author pin is retained in `annular-comparison-v4.json`.
No formalization file was changed, and no Lean build or audit was rerun.

## Plateau Construction and Boundary Branches

The proposed dependency on filling-width did not supply the M65 minimizing
disk. New `sec:annular-plateau` develops the actual normalized weak class,
three boundary pins, boundary equicontinuity, strong map and weak derivative
extraction, varying-metric lower semicontinuity, epsilon-conformal energy
comparison with every Lipschitz disk, and inner-variation conformality.
It then develops local replacements, power decay, the weighted Poisson
bootstrap for the same map, boundary half-cones with the exact monotone
label, transverse reflection and recovery of the remaining derivative.
The Cauchy gauge and holomorphic factor give finite branches; finite
branches exclude collapsed trace intervals and produce the homeomorphic
boundary label. Within-C1 regularity on the compact disk gives Lipschitzness.

Read under `Geometry/CurveShortening/Deformation/Plateau/`:
Attainment, AttainmentConclusion, MinimalDiskRecord;
Weak/Minimizer{Class,Existence,Conclusion,LipschitzClass,Extraction,
BoundaryCompactness,BoundaryEquicontinuity,EnergyLimit,Competitors,
ConformalVariation}; Energy/Competitors; InteriorRegularityEnergyInequality,
InteriorRegularityPowerDecay, InteriorRegularityEuler{AlphaOneM60,Interior};
Boundary/Regularity{LocalConclusion,HeinzC1,TomiRegularity,TomiBootstrap,
GradientRecovery,Reflection,FullDecay,RadialEnergy,CapturedCone,
HalfConeEnergy}. Read the actual half-cone diameter formula in
Boundary/RegularityHalfConeReplacement.

The former Gauss--Bonnet paragraph treated all branches as interior
punctures. New `sec:annular-disk-gauss-bonnet` instead defines the actual
logarithmic curvature density, radial flux and moving-boundary term.
It proves absolute curvature integrability by the residual tangent-plane
projection, subtracts interior logarithms in a genuine C1 potential, and
uses radial Stokes. At boundary branches it retains the half-disk factor,
even branch order, Holder-one-half residual frame and L2 derivatives.
A common sequence of horizontal slices and an explicit integration-by-parts
error bound yield the boundary flux inequality. The disk variation now
uses that inequality and the three-dimensional Ricci density with its
correct sign, without asserting immersion of the supplied disk.

Read under `Deformation/MinimalDisk/`: HartmanWintner,
StrictTraceBoundaryAlternative, StrictTraceFiniteBranches, StrictTrace;
and GaussBonnet/{Basic,Scalar,RadialStokes,FiniteCollar,CollarRegularity,
PotentialStokes,InteriorLog,MinimalDiskBoundary,HalfDiskCurvature,
FrameConnection}, Boundary/{Global,Log,Integrability,Geometry,Factor,
Subdivision,Collar}. The Boundary/{Parity,Order,Tangent,Curvature,Frame}
interfaces and RadialConnection identities were traced in their assembly;
this is not a separate kernel audit of every imported analytic lemma.

## Regional Normal Descent

The initial account did not explain why a long collision base is impossible.
`sec:small-area` now separates local focusing on an already short interval
from the later global conclusion. Regional first-contact heights are
measurable; a nested simple-loop curvature obstruction proves regional-ray
injectivity. On a length-q interval, the actual losses are q/100 for high
curvature, q/50 for collision removal and q/10 for full-height fibers.
The retained endpoint length exceeds 87q/100. Local inverse charts bound
the capacity of one or two short sides without differentiating the height.
Almost-everywhere transversality gives an actual return to the base.
Its central starting point produces a nested child losing at least q/10
of base length. The short-return curvature obstruction keeps every child
above r; an almost-minimal member of the set of lengths contradicts the
fixed decrease. The same construction excludes long two-side bases.

Read under `Comparison/IntrinsicComparison/`: Long/TwoSideRegion;
Regional/{NormalReturn,CentralReturn,RetainedEndpoints,EmbeddedContact,
RayInjectivity,CollisionFocusing,FirstContact};
Two/{SideRegionalReturn,SideRegionalCapacity,CurveEndpointProjection};
Central/{RegionalDescent,ReturnChild,BoundaryInterval};
Nested/{ReturnRegion,TransverseReturnLength}; Raw/InnerNormalReturn;
Constructed/{NoShortNormalReturn,NormalReturnCurvature};
Normal/ReturnRegionCurvature; Double/CollisionFocusing;
Local/ArcRetainedProducer. The missing historical derivation paths were
not used as proof authority. The radial and global constructions were
subsequently expanded as follows; sequential whole-chapter review remains.

## Confined Radial Focusing and Global Geometry

New `sec:annular-confined-focusing` precedes both uses of focusing.
The short boundary competitor gives an actual compact constrained
minimizer. The text develops side avoidance, last-base-contact tangency,
the convex terminal sector and the nested Gauss--Bonnet contradiction.
The uniqueness class includes every bounded confined radial vector.
The earliest noncanonical contact creates an acute digon; perturbation
in a compact inverse chart and first exit retain whole-segment confinement
and the radius bound. Compactness and uniqueness give the continuous
closed lift. Its Jacobi estimate, sine radial field and endpoint
orthogonality give the absolute-turning inequality.

The global argument now selects the annular Jordan region from the same
first-contact pair and both complementary arcs. The local-inverse
self-return argument retains the signed collar, open prefix stability,
and the closed stopping endpoint. The cyclic cover explicitly projects
two periods and retains the factor two in the turning budget.

Read under `Comparison/IntrinsicComparison/`: Global/{RayEmbedding,
CollisionFocusing}; Normal/{RayEmbedding,CollisionTransverse};
Prefix/Confinement; Prescribed/CollisionDisk; Nested/JordanRegions;
Wide/CollisionFocusing; Double/CollisionFocusing; Actual/NormalComparison;
Cyclic/{RetainedStripLosses,RetainedNormalDomain,FocusingCover};
Normal/Crossing; Collision/{Focusing,PolarLift,RadialExistence,BaseAvoidance,
LastContact,SideAvoidance}; Continuous/FocusingArc; Closed/BaseGeodesics;
Short/CollisionGeodesic; Base/ToVertexMinimizer;
Affine/CollisionBoundaryAvoidance; Compact/MinimizerGeodesic;
Smooth/LastContact; No/LastContactTail; Geodesic/SideAvoidance;
Confined/{PolarInjectivity,RadialUniqueness,DigonPerturbation};
Earliest/ConfinedContact; Radial/DigonPerturbation.
Also read `Comparison/Analysis/Injective/DomainClosure` and
`Comparison/Analysis/Radial/DigonFirstExit`. The terminal corner and
radial Jacobi inputs were traced through their consuming arguments;
this list does not claim a new kernel audit of their dependencies.

## Annular Analytic Ordering

The original prose placed boundary C1 before conformality, although that
boundary argument consumes conformality. The corrected account first
retains the integer relative phase offset and both Green identities,
then excludes label jumps using real-phase energy, including the angular
cut. Two weak stress identities, their two-cut assembly, Fourier-mode
uniqueness and independent modulus balance give conformality. Boundary
parameter cones replace the map and real phase together; the diameter
uses an affine chord in the original parameter, with phase H_i of that
chord. The same-map C1 construction is patched through two cuts.

The later closed-C2 upgrade is explicitly restricted to the smoothed
unlabelled boundary curves. It uses initial H2 from the reflected complex
gradient, metric-normal mixed traces, H1 forcing, H3 of the map, H2 forcing
via the two-dimensional L4 estimate, and H4 followed by closed-C2 recovery.
It does not assume a smooth boundary label or infer C2 for arbitrary C2
unlabelled curves by this smooth-coefficient argument.

Read under `Comparison/AnnularEvolution/Plateau/`:
Free/{WeakPhaseClass,PhaseBoundaryLabels,BoundaryParameterLabels,
BoundaryConeReplacement,PhaseBoundaryComparison,BoundaryAngularComparison,
PhaseRawConformality,PhaseStressZero,PhasePeriodicSecondStress,
LowerBoundaryC1,RadialCompletion};
Boundary/{WeakSeamContinuity,StressZero,StressTrigonometricModes};
Free/BoundaryCompactness/Ramp/LabelOscillation;
Regular/CurveBoundaryC1; Stabilization/Free/RampClosedC1;
Stabilization/Confined/Approximation; Free/ModulusConfinedApproximation;
Uniformization/Scalar/{FreeModulusApproximation,LocalFreeApproximation,
SmoothFreeApproximation,FreeClosedCylinder,CoverRegular,PotentialNoncritical}.
These assembly reads were followed by the scalar producer review below.

Read under `Comparison/RampTransport/Boundary/`:
Bootstrap{StripC2,ClosedC2,AnnulusChart,HarmonicChart,HalfBall,Compact,Mixed,
Neumann}. These supply the explicit finite bootstrap now in the draft.

## Scalar Annular Uniformization

New `sec:annular-uniformization` replaces the invocation of uniformization
with the actual construction. It defines the variational potential and its
classical boundary representative, the exponential radial barriers and the
conjugate flux. It retains the finite-energy boundary-circle approximation
which proves positivity and the exact energy-period identity. Properness
and complex openness give surjectivity before noncriticality. The unit
Jacobian integral, integer coverage, overlap cost and null angular cuts
give global injectivity. Removal for the actual local inverse then excludes
critical points. The closed gradient bound gives a Lipschitz inverse;
positive conjugate boundary speeds give the literal degree-one lifts.
The modulus is 2pi/P and the half-open fundamental rectangle covers the
physical annulus once, permitting the area comparison at deficient rank.

Read under `Uniformization/Scalar/`: Dirichlet, BoundaryH3,
RadialBarriers, FluxApproximation, PeriodPositive, EnergyPeriod,
LocalHarmonic, LocalIsothermal, CoverProper, CoverOpen, CoverSurjective,
CoverImageArea, AreaOverlap, IntegerNoOverlap, StripInjectivity,
ConjugateCriticalExclusion, BoundaryNoncritical, BoundaryAngularPositive,
InverseLipschitz, ClosedCover, ActualBoundaryCoordinates,
ClosedBoundaryLifts, CylinderArea, FreeClosedCylinder,
C1MetricMajorant, RelativeAreaApproximation, PeriodicRectangleEquality;
the higher approximation assemblies were read in the preceding pass.

The local isothermal construction calls the actual uniform harmonic-radius
producer after a local normalized Gauss-metric extension. Searching all
eighteen drafts found no exposition of that harmonic-coordinate argument.
Its producer is now developed in `ricci-flow`, Section
`sec:rf-harmonic-coordinates`, and the bounded annular interface is reviewed
in `harmonic-coordinates-integration-v4.md`. The remaining Ricci-flow
chapter and its other harmonic-coordinate consumers are still pending.

## Static Families, Filled Limits and Extinction Interface

The static paragraph incorrectly offered interpolation of the polygon's
parameter as a homotopy through C1 loops. Such intermediate polygonal
curves still have corners. The actual `Uniform/RawFamily` constructs the
homotopy between the original and already flattened families using the
controlled short-geodesic interpolator. The corrected text explains
uniform value closeness, joint continuity of values and first derivatives,
pointwise nullity, and the direction of filling-area transfer from C1 loops
to the raw polygon. Directly read `PolygonApproximation/Uniform/`
{CompactApproximation,RawFamily}, `Ramp/Approximation/Close/LoopFamilyHomotopy`,
`Comparison/FamilyAdapters` and `AreaComparison/Finite/NetsComplete`.
The same approximation, node and canonical ramp are retained by the later
construction; a parameter-space arc between nodes is not required.

Reviewed the actual weighted scalar inequality, fixed delayed grid,
conditional cell cutoffs, finite minimum, two transfer thresholds and
common circumference. The grid includes both initial cells and the full
final gap. Its cutoff is conditional on the required cell bounds, so no
circumference-independent good subset is assumed. The text retains the
weighted error `(G*d+U*m*e)/w(b)`, the exact profile multiplier `1/w(b)`,
the factor 5 from the original base dimension, and the terminal 9/16 versus
1/2 contradiction in the short branch.

The expanded filled-limit argument derives length and speed noncollapse
beyond T on the enlarged cell. A fixed-in-time constant-speed relabeling,
the quantitative slope bound `(rho/ell)^2+2*K*rho`, actual intrinsic-to-chart
recurrences and the coupled position/speed/slope equations supply smooth
compactness. One continuous manifold limit identifies every local derivative
limit. Boundary relabeling keeps each disk map and area; small C1 annuli
construct a disk for the limit before its filling infimum is compared.
The endpoint continuity paragraph now also states the sphere-height section
used to apply the predecessor's exact sphere-family continuity theorem.

Directly read under `Deformation/`: GoodTimes/{FiniteProfileComparison,
PointwiseTerminalAlternative,Family/Grid/GridAssembly,
Family/Cell/{Comparison,FillingLimit,Limit,Normalization}};
Limit/{FamilySlope,ActualSpatialBounds,Slope/Collapse,Coordinates/State};
the operator definitions in `Limit/Coordinates/Operator`; and
`Limit/SmoothLimit`'s state bounds, local extraction and final assembly
(lines 1--302 and 530 onward). Read AreaContinuity/{FillingLimit,Relabeling};
SweptArea/{ClosedTimeFilling,FillingTimeContinuity};
Transfer/{NetConclusion,NetAssembly,ShortLoops,AreaLoops}; Assembly and
Construction. Read the literal M65 raw input/output in
`Extinction/Width/Deformation/Data` and compared the exposition with the
accepted extinction chapter's endpoint argument.

The interface agrees: every terminal member has its own alternative,
the profile starts at the actual deformed initial area, and free homotopy
is preserved. A class near-minimizer is chosen before deformation.
The maximum of the small-loop and profile bounds remains in the annular
conclusion; the extinction chapter uses nontriviality and the short-family
contraction to prove profile nonnegativity before removing that maximum.
This bounded M65 interface review does not accept the ramp predecessor
or the remaining whole annular chapter.

The disk first variation was then followed through its actual
differentiable upper bound. The text now constructs an ambient motion
following the embedded loop with its exact parameter, moves the same
attained disk and boundary label, and differentiates half-energy. Equality
with filling area is needed only at the tested time; nearby area is
bounded by energy. The continuous within first jet supplies the boundary
flux, and conformality plus boundary-homeomorphism length invariance gives
the residual times original loop length. This avoids silently
differentiating an area infimum or requiring nonzero differential at a
branch point. Read `MinimalDisk/FillingArea/{Inequality,Barrier,Competitors}`,
`Energy`'s family motion and disk first-variation arguments, and the flux
interface. The generic perturbation paragraph now develops invertible
three-parameter blocks, compact zero capture, actual implicit zero charts
and equal-dimensional Sard for the projection onto parameters. Read
`Transfer/{ImmersedPerturbation,ImmersedPerturbationGeneric,
ImmersedPerturbationParameters,ImmersedPerturbationApproximation,
ImmersedComparison}`. This retains finite exceptional times and the
weighted residual comparison before the endpoint-area limit.

## Sequential Reading of the Annular Minimum and Small-Area Geometry

Reread the actual draft from its definitions through the ramp small-area
comparison as a connected mathematical argument. Checked free modulus and
relative phase before conformality; stress Fourier signs and zero mode;
the positive-period energy identity; proper open cover, area overlap
argument and inverse-removal order; positive literal boundary labels;
lifted competitor phase and both Green identities; separated auxiliary
affine phase before the first variation; integrated inequality before
removing separation. The harmonic-coordinate producer is now developed
and has a bounded review in `harmonic-coordinates-integration-v4.md`.

Added the missing relative-offset estimate after reading
`Plateau/Boundary/RealTraceOffset.lean` and
`Plateau/Free/WeakPhaseCompactness.lean` at production
`751329327f4f582797bda8e6cffe7cdf7531cc1d`. The constant test in the full
vertical Green identity bounds the difference of boundary means; affine
monotonicity and both label normalizations bound the offset. Closedness
of the period subgroup retains admissibility at the subsequential limit.

For the small-area argument checked the local-q collision estimate before
regional descent, one-side descent before exclusion of long two-side
regions, complementary cyclic arc selection, the two focusing scales,
closed-endpoint self-return exclusion and the final two-period cover.
Made explicit that the small base neighborhood has complementary arc
length greater than 2q; merely writing 2q<L0 does not state that choice.
The 2, 6 and 10 percent losses leave 41/50 of the boundary before the
99/100 endpoint metric factor. Ramp transport retains r/4, the 7/800
turning tolerance, smoothing gap and fixed threshold before circumference.
The source review of its mixed boundary regularity was retained.

Whole-chapter acceptance still requires the rest of the sequential reading
and explicit ramp-interface review. These checks do not accept that
predecessor or replace the remaining Plateau and deformation review.

## Global Disk Beltrami Construction

Sequential reading of the Plateau section found that its two sentences
about disk coordinates suppressed a substantial global construction.
Local harmonic coordinates do not imply a diffeomorphism preserving
the whole closed disk. New `sec:annular-disk-beltrami` develops the actual
positive-matrix coefficient, reflected compact coefficient, L2 Beurling
contraction, derivative-budget induction and smooth Neumann sum.
The Cauchy potential gives an exponential nonzero derivative and a closed
one-form with an explicit radial primitive. Properness, covering-space
uniqueness and the local inverse theorem make that primitive global.
Affine normalization, Liouville uniqueness, actual reflected removability
and the derivative limit at infinity force disk preservation.
The inverse differential gives the precise isothermal identity; the
area-to-energy change of variables cancels its conformal factor.

Directly read under
`Geometry/CurveShortening/Deformation/Analysis/Plateau/Beltrami/`:
L2, SmoothForcing, Coordinates, Primitive, Map, Proper, Global,
Normalization, Uniqueness, Inversion, Holomorphic, ReflectionLimit,
Disk, Annular, Isothermal, Sobolev and the derivative-budget estimates
and full geometric-decay induction in DerivativeBounds. Also read
`Plateau/CompetitorCoordinates.lean`. The Fourier multiplier and Cauchy
fundamental solution are ordinary analytic background; their localization,
smooth summation, global inversion and disk reflection are developed here.

Read the primary Fitzi--Wenger version-1 paper, Theorem 2.2 on p. 6
and Theorem 4.1 with proof on pp. 8--10; the comparison and bibliography
are recorded under `references/geometric-analysis/fitzi-wenger-2019/`.
The actual smooth-coefficient result is sufficient for both the
Lipschitz-disk comparison and the inner variations. A full measurable
Riemann mapping theorem is not asserted.

Sequentially read the remaining Plateau regularity, boundary branches,
Gauss--Bonnet, actual energy barrier and immersed perturbation paragraphs.
They retain the same weak derivatives, conformality before the boundary
bootstrap, the common slice sequence at boundary branches and an energy
upper barrier before taking a derivative of filling area. The new global
coordinate proof has been checked in the same order.

## Final Sequential Reading and Ramp Interface

Completed the connected reading of the good-time-grid, filled limit,
terminal transfer and fixed-class sections. Checked the enlarged cell
beyond T, a fixed-in-time relabeling, degree-one slope collapse,
intrinsic-to-coordinate derivatives and the same subsequence at both
area endpoints. The failing-cutoff argument is conditional on cell bounds,
so a circumference-independent good set is never assumed. The final
transfer keeps the 9/16 contradiction and chooses finitely many node
cutoffs before the single circumference and arbitrary member.

Read the predecessor's exact statements and compared the consuming
GridAssembly with Ramp/LocalEstimates/Uniform/DerivativeEstimates and
Ramp/Approximation/Family/ConclusionAssembly. Its initial length and
turning bounds precede circumference and reference time, the local window
is strictly after that reference, and the same supplied approximation
and canonical initial curves persist. Comparison/FamilyAdapters and
Ramp/CurveEstimates/C2/IntegratedEstimates supply the energy integral;
the ramp chapter now derives that estimate explicitly by an integrating
factor. Both excerpts match their annular consumers. This bounded
interface review does not discharge the ramp chapter's independent
local-existence and all-order estimate reviews.

The whole annular draft has received a sequential mathematical readability
pass, including the integration expansions. The subsequent ramp producer
review is now complete: see `ramps-integration-v4.md` and its pinned
acceptance record. It develops local C2 construction, fixed-label
regularity and continuation, the corrected quotient, all-order weighted
estimates and the exact supplied-family assembly. This resolves the
remaining predecessor review identified here. Final book integration
remains a separate gate; the syntactic checker is not substituted for it.

## Primary Sources and Remaining Review

Directly read Morrey's ICM lecture Sections 3--5, printed pp. 181--187,
from the archived PDF. Its Dirichlet integral is twice the energy convention
here. The bibliography and publication-only provenance now record the exact
edition. It provides comparison for weak attainment, conformal approximation
and interior regularity; it is not cited as the finite boundary-branch proof.

Directly read Morgan--Tian Lemma 19.2, printed pp. 438--439, and
Lemmas 19.45--19.54 with Claims 19.47--19.52, pp. 474--478.
The disk argument here retains branches instead of invoking their removal.
The regional argument uses an arclength-selected central interval, measurable
collision removal and an infimum descent with loss q/10, rather than the
printed finite maximal-triangle construction and loss 0.85. These are
implementation-route comparisons, not novelty claims.

Also directly read Lemma 19.15 and Corollary 19.16, pp. 447--449.
The printed proof uses analytic approximation, minimal-annulus existence
and finite branches, then a third disjoint curve. The current construction
uses a real weak phase, scalar annular coordinates and auxiliary-circle
separation with an affine phase excluding branches. Its detailed scalar
construction is not attributed to the printed lemma.

Directly read Claims 19.39--19.43 and Remark 19.42, pp. 470--473,
and Lemmas 19.53--19.54, Corollaries 19.55--19.56 and Claim 19.57,
pp. 478--481. The constrained shortest-path argument and the uniqueness
of short confined rays supply the geometric comparison. The actual
construction replaces the printed spray continuation with the explicit
earliest-digon first-exit argument, and proves a sine-radius inequality
using absolute turning. The printed Claim 19.43 uses radial contraction
and signed turning with an area term. The final loss accounting also
differs: the current separate losses are 2 percent, 6 percent and
10 percent, leaving 82 percent before stretching, rather than the
printed combined 84 percent retained set. These are checked route and
constant comparisons, not novelty claims.

Directly read Morgan--Tian pp. 449--464, including Definition 19.18,
Claims 19.19--19.23, Lemmas 19.24--19.25, Claims 19.26--19.28,
Remark 19.29, Lemmas 19.30--19.31, Claim 19.32 and the final assembly.
The actual proof chooses a fixed delayed grid instead of subsequential
moving intervals. It telescopes additive weighted errors; it does not
use the printed Claim 19.27 recurrence which places the new error inside
products multiplied by gap lengths. It passes endpoint areas through
filled smooth limits before applying comparison, instead of claiming
that continuity passes forward derivative inequalities to approximating
curves as on p. 461. The actual finite net uses direct small geodesic
annuli between nearby loop values, while pp. 461--462 describe annuli
swept along arcs in the parameter sphere.

Directly reread Lemaire, Section 5, Lemmas 5.1--5.4 and Remark 5.5,
printed pp. 99--102. Lemma 5.2 is on p. 99, not pp. 100--102.
Theorem 1.7 is not used as an unconditional theorem with no pi2 or
boundary restrictions. Original Heinz and Tomi papers have been identified
but not directly read in this integration pass; no such review is claimed.

## Acceptance Decision

The earlier partial-review notes above record the order in which gaps
were resolved; the final sequential passes and ramp acceptance supersede
their pending mathematical actions. There is no unresolved internal
mathematical finding at the reviewed digest. M64 and M65 are both
reconciled with precise exposition locations. Filling-width supplies its
accepted infimum and collar constructions; ramps supplies the accepted
solutions and estimates; the local harmonic-coordinate input has a
bounded source/readability review in the pending Ricci-flow chapter.
The consumer is the already calibrated extinction chapter, with the same
fixed initial class and retained terminal maximum.

Chapter acceptance does not accept the rest of Ricci-flow or the complete
book. Integrated bibliography rendering, final source links and inspected
PDF/site remain pending. Later changes to inputs or the reviewed digest
reopen affected review. The publication checker validates literal text
references and metadata, not this mathematical acceptance decision.

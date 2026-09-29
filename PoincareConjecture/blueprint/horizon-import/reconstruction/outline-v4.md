# Subject-based authoring division for objective revision 4

Main-agent authoring review: 2026-09-28. This division is approved for drafting,
not for publication acceptance. It supersedes the six-chapter scope in
`../outline.md`. The number of chapters follows the constructions below;
it is not a page, milestone, or session target. Further source discoveries
may require a split or an additional section. No chapter is yet accepted
against the revision-4 criteria.

## Reconstruction and boundaries

The starting point is `m90FinalAssemblyFromMilestones`, through
`Final/Providers.lean`, in the unchanged Lean tree at workspace baseline
`5950ef93a2a8035ef518a2062a094da966df809b`. The final smooth argument constructs
one normalized metric, one controlled surgery flow, its extinction event,
its actual finite reconstruction, and its sphere maps. The topological
argument separately constructs a compatible smooth model and transports the
smooth result through that model's chosen homeomorphism.

The initial evidence includes the recursively audited endpoint closure,
the actual provider proof, the ramp and annular-comparison constructions,
the scalar-comparison and extinction proofs, and the topology reconstruction
in `topology-discovery.md`. The old 97 declarations are useful entry points,
not a boundary. The broader source discovery is recorded separately; counts
cannot establish that the mathematics has been explained.

There are three kinds of supporting material. Ordinary background may be
stated precisely with an exact theorem reference: for example compactness of
a continuous image, covering-space lifting, or an appropriate standard
parabolic existence theorem. Implementation helpers such as instance
transport and finite-index equivalences may be combined into one mathematical
construction, preserving the objects they identify. Substantial constructions
on the actual route, including fixed-carrier limits, protected topological
modifications and uniform ramp estimates, require arguments in the book.
Calling such a construction a service, provider, or certificate does not
make it background. Each author must justify any background classification.

The chapter identifiers below are stable authoring keys, not milestone IDs.
Each chapter owns `drafts/KEY.tex` and `inventory/reviews/KEY-v4.json`.
Existing legacy chapters remain preliminary integration inputs. Authors may
read every Lean module needed to recover a proof, regardless of the old
inventory. They must record unresolved substantial dependencies in their
review artifact, with a precise proposed owner, rather than hide them in a
citation. Sources below are entry points, not exhaustive import lists.

## 1. Closed three-manifold topology and the Poincare problem (`foundations`)

Sections: the standard three-sphere and the two endpoint statements; closed
three-manifold topology used before flow; orientability and exclusion of
two-sided projective planes; the forward geometric and backward topological
arguments. Define topological versus smooth models, closedness, simple
connectedness, and basepoint conventions before using them.

State the exact topological consequences consumed by the flow and loop-class
arguments. Develop orientation and local homology, the finite CW structure,
the cap-duality argument for vanishing second homology, the coherent local
generators of third homology, and the Hurewicz steps giving vanishing second
homotopy and infinite-cyclic third homotopy. Account for the stronger CW
sphere-equivalence output separately from the nonzero class used later.
Follow the closed-topology and orientation constructions, rather than
assuming a sphere recognition theorem that already contains the conclusion.
Explain which general algebraic topology is background and which
dimension-three argument is supplied locally. Dependencies: ordinary
manifold and algebraic topology. Outputs: endpoint hypotheses, admissibility,
and the initial homotopy input for `filling-width` and `extinction`.
Entry points: `Topology/Manifold/Poincare/Final/Statement.lean`,
`Poincare/Final/Main.lean`, `Topology/Manifold/ThreeDimensional/` homology
and homotopy constructions, `Topology/CWComplex/ThreeDimensional/CWThreeSphere.lean`,
the M02 topology provider and M83 orientation exclusion.

## 2. Ricci flow and curvature estimates (`ricci-flow`)

Sections: normalized initial metrics; local existence, uniqueness, and
continuation; tensor evolution and scalar bounds; Hamilton--Ivey pinching;
Harnack estimates and pointed compactness. Define metric scaling, curvature
conventions, complete flow intervals, and the regularity of convergence.
State each estimate with its own dimensional and boundedness hypotheses.

Explain the normalized-metric scaling, the gauge/PDE construction behind
local existence, the tensor maximum principle and invariant pinching region,
and the exhaustion/diagonal construction of complete interior limits. Do not
replace these with a list of conclusions of a curvature package. Standard
analytic results may be cited only with the hypotheses needed by the actual
specialization. Outputs feed `reduced-geometry`, `ancient-models`, and
`ramps`. Entry points: local Ricci-flow theory, `RicciFlow/Pinching/`,
Harnack and compactness providers (M01, M03--M07).

## 3. Reduced geometry and noncollapsing (`reduced-geometry`)

Sections: backward action and minimizing curves; first and second variation;
reduced length, singular locus and volume; monotonicity and equality;
generalized spacetime gauges and rescaling; compact and generalized
noncollapsing. Define the actual unnormalized reduced volume, whose Euclidean
value is `(4*pi)^(n/2)`, and distinguish ordinary and generalized carriers.

Develop existence/variation, differential inequalities, measure transport
past the nonregular locus, and the contradiction yielding volume lower
bounds. Explain the gauge identification on the same spacetime and the
specific rescalings used downstream. Dependencies: `ricci-flow`.
Outputs: monotonicity, rigidity, generalized comparison and noncollapsing.
Entry points: `RicciFlow/ReducedGeometry/`, `Generalized/ReducedGeometry/`,
`Generalized/` gauge constructions (M08--M15).

## 4. Ancient solutions and singularity models (`ancient-models`)

Sections: ancient noncollapsed solutions; prescribed rescaling sequences;
asymptotic soliton limits; two- and three-dimensional classifications;
asymptotic volume and universal noncollapsing; normalized compactness and
local model certificates. Preserve the chosen carrier and scale sequence in
the limit construction. Separate the two-dimensional classification from
the three-dimensional one.

Explain the point-picking and convergence arguments, equality-rigidity step,
classification alternatives, and passage from those alternatives to local
neck/cap or positive-spaceform data. Dependencies: the two analytic chapters.
Outputs: model geometry for `neck-cap-topology` and `singular-limits`.
Classification of ancient solutions does not itself transfer a model to a
high-curvature point in a surgery flow; that requires the next blowup argument.
Entry points: `AncientKappa/{Theory,Rescaling,Asymptotic,Volume,Compactness}`,
`Soliton/{TwoDimensional,ThreeDimensional}` and canonical-model providers.
Correct milestone identities: M16 structure, M17 rescaling setup, M18
asymptotic limit, M19 two-dimensional classification, M20 three-dimensional
classification; then M21--M24.

Integration refinement: slice boundedness before asymptotic classification
uses a static positive-curvature neck-scale obstruction. Its exposition
must precede classification and cannot depend on M27 in the next chapter.
The ancient draft now develops whole-carrier escape, radial boundary
maxima, cutoff depth, circle-lift ambient separation and nesting, signed
Busemann flux, calibrated segments and uniform long-neck alignment.
The draft also develops the point-soul construction: convex exhaustion,
singleton rigidity, common neighborhood potentials, complete outward flow,
Euclidean coordinates and parametrization by actual distance. Its shared
Calabi, index-form, comparison and normal-coordinate inputs still require
reconciliation with the earlier geometric foundations. This is an actual
dependency refinement, not acceptance of the whole prerequisite chain.

## 5. Smooth necks, caps, and their global topology (`neck-cap-topology`)

Sections: collared balls and smooth sphere gluing; neck overlap geometry;
cap cores and encounters; global tubes and compact alternatives; full
canonical neighborhoods. Define actual neck/cap embeddings and the gluing
data, not merely informal pictures. Develop the sphere-isotopy/Schoenflies
inputs to the extent constructed in this project, directed overlap
continuation, and the finite encounter or covering argument for each global
alternative. Dependencies: manifold background and `ancient-models`.
Outputs: global canonical models for surgery and smooth ball/sphere gluing
for `sphere-reduction`. Entry points: `Topology/Manifold/NeckCap/` and
`RicciFlow/CanonicalNeighborhood/Ancient/` (M25--M27).

## 6. Singular limits and deep horns (`singular-limits`)

Sections: bounded-distance curvature and the cone obstruction; dense-time
path rebasing; generalized blowup limits and finite-slab extension; the
regular terminal region; ancient limits of deep horns and strong-neck
selection. Define the retained region, the terminal threshold and the
precise convergence domains. Explain the obstruction to the limiting cone,
inclusive dense-time control, the terminal regularity argument, and why a
horn limit cannot be a cap. Preserve the actual terminal constants, including
the factor `10^14` where it appears in the source.
Dependencies: `ricci-flow`, `reduced-geometry`, `ancient-models`,
`neck-cap-topology`. Output: controlled regular limits and embedded strong
necks in the same flow. Entry points: bounded-distance, generalized blowup,
singular-limit and deep-horn providers (M28--M32), with exact source paths
recorded by the author. These mechanisms require a chapter separate from
constructing a cap and performing metric surgery.

## 7. Resolving singularities by surgery (`surgery`)

Sections: existence, uniqueness and lifetime of the standard cap;
metric interpolation and post-surgery geometry; comparison maps and degree;
nonempty and vanishing continuation; cap persistence.
Introduce surgery slices, retained regions, scales and collars before the
operation. Explain the cap lifetime and energy uniqueness arguments and
the construction and estimates of the comparison maps.
Distinguish the metric surgery from the topological gluing theorem.
Dependencies: the preceding geometric chapters. Outputs: one controlled
surgery step, metric comparison and homotopy transport. Entry points:
`RicciFlow/Surgery/StandardCap/`, metric-surgery and comparison providers,
and continuation branches (M33--M44); filenames are verified by the author.

## 8. A global controlled surgery flow (`global-surgery`)

Sections: ordered parameter choices; noncollapsing and canonical-neighborhood
induction; volume loss and finite surgery counts; compatible finite prefixes
and the global schedule. Write out which constants are chosen before which
curves, intervals, or surgery scales. Explain why later refinements preserve
earlier controls and why no finite accumulation occurs.
Dependencies: `surgery`, `reduced-geometry`, `neck-cap-topology`.
Output: one flow with its exact initial identification, locally finite event
set, geometric controls and empty-slice permanence. Entry points:
`RicciFlow/Surgery/{CanonicalInduction,GlobalSchedule,Global}`,
volume and noncollapsing providers (M45--M52). The continuation branches
and persistence are supplied by `surgery`; cross-reference M83 from
`foundations`. Develop the action-minimizer and first-failure arguments in
the noncollapsing/canonical induction and the weighted cap/component count
and N+1-restart contradiction in the global existence proof.

## 9. Filling area and homotopy classes of loop families (`filling-width`)

Sections: surgery spheres and component homotopy; coherent loop-space
identifications; short-loop fillings; minimal disks and filling-area
continuity; family supremum and class infimum. Define raw null-loop families,
free versus based class labels, the chosen parameter sphere and filling
area. Explain the surgery fundamental-group factor/injection arguments and
nonzero class transport; prove the small-area/short-loop and continuity
steps used in the width construction. Distinguish attained family maxima
from generally unattained class infima.
Dependencies: `foundations`, surgery topology and standard minimal-surface
background with exact hypotheses. Outputs: a fixed coherent identification
system, filling-area estimates and finite nonnegative widths.
Entry points: loop-space compatibility, surgery component topology,
`Riemannian/MinimalSurface/`, and `Extinction/Width/Class/` (M53--M61).

## 10. Curve shortening and ramp approximations (`ramps`)

Sections: corrected moving-metric evolution; pure-normal local solutions
with fixed labels; continuation and regularization; positive-slope graph
ramps; uniform interior estimates; polygonal approximation of raw families.
Define product-circle circumference, slope, curvature, length and total
curvature. Preserve the two branches for C2 initial labels and smooth
initial labels, and the closed ambient-time endpoint.

Derive positive slope preservation before using a sign-guarded estimate.
Explain the regularized curvature/slope quotient including its forcing
term, and which bounds are uniform in circumference. Construct flattened
geodesic polygons, the actual C1 homotopy and continuous angular jets.
Dependencies: flow estimates and short-loop filling from `filling-width`.
Output: solutions and approximation families on the same supplied ambient
geometry. Entry points: `RicciFlow/CurveShortening/CorrectedEvolution.lean`
and `CurveShortening/Ramp/` (M62--M63). Exact source locators in
`Ramp/Main.lean` include Morgan--Tian pp. 437, 446--455, 481--495 and the
2015 correction pp. 6--9; authors must compare the actual formulas.

## 11. Annular comparison and width deformation (`annular-comparison`)

Sections: spanning annuli and projected ramp families; annular evolution
and least-area comparison; static approximation; deformation preserving
the specified homotopy class; transfer to raw near-minimizing families.
Define annular area and the approximation error before stating comparison.
Develop the geometric comparison and the selection/transfer argument;
retain the same approximation record when the theorem accepts a supplied
one. State dimension restrictions and exact error quantifiers.
Dependencies: `ramps`, `filling-width`. Output: the deformation estimate
consumed by smooth-time width comparison. Entry points:
`CurveShortening/Comparison/{Main,CompleteComparison}.lean`,
`Comparison/AnnularEvolution/`, and `Deformation/` (M64--M65).

## 12. Width comparison and finite extinction (`extinction`)

Sections: regular-time continuity and forward difference estimates; ancestry
and surgery jumps; scalar clock and strict-barrier comparison; finite-event
propagation; a fixed initial width and the negative comparison time; the
first empty event. Preserve the quantifier order: select the initial class
and its finite width before choosing the horizon, then construct its path
on the same flow. The nonnegative-width contradiction alone is not the
extinction proof.

Develop the exponential strict barrier in `Analysis/ODE/ForwardComparison.lean`,
event restart by the left lower limit, finite induction, and the explicit
negative-profile calculation. Dependencies: `global-surgery`,
`filling-width`, `annular-comparison`. Output: finite extinction with
permanence for the exact controlled flow. Entry points:
`Extinction/Width/{SmoothTime,Transport,ScalarClock,FinitePiece}` and
`Extinction/Global/` (M66--M71, M81). This chapter is the calibration
candidate: main-agent source and readability review must pass before other
chapter drafts are accepted. A detailed ODE proof alone does not pass it.

## 13. Reversing a finite surgery history (`finite-history`)

Sections: exact event ledger; successor components and no-surgery intervals;
local connected-sum assemblies; reverse induction and exact factor indices.
Define discarded versus surviving factors and their attachment data.
Develop well-founded successor induction, transport along an unchanged
interval, substitution of assemblies and terminal/first-event reindexing.
Dependencies: `global-surgery`, `extinction`, local surgery topology.
Output: a smooth finite connected-sum assembly of the actual initial slice
from the actual discarded factors. Entry points:
`Surgery/Reconstruction/Assembly/{HistoryIndices,Successors,ReverseInduction}`
and connected-sum assembly maps (M72, M82). Confirm full paths in metadata.

## 14. Sphere factors and connected-sum reduction (`sphere-reduction`)

Sections: factor fundamental groups; excluding sphere bundles by a lifted
circle projection; identifying simply connected positive spaceforms;
binary smooth sphere gluing; finite sphere-union induction; the smooth
endpoint. Prove factor simple connectedness from the exact assembly,
not from an independently chosen list. Explain the compact lifted-range
contradiction and the clopen component bookkeeping in a binary operation.
Dependencies: `finite-history`, `filling-width`, `neck-cap-topology`.
Output: the sphere diffeomorphism composed with the initial identification.
Entry points: `Surgery/SphereFactors/`, `ConnectedSum/SphereReduction.lean`
and `Poincare/` smooth assembly (M73--M75, with M82 in the exact ledger).

## 15. Protected Dehn disks and annuli (`dehn-surfaces`)

Sections: finite PL surfaces and marked boundary data; proper disk/annulus
constructions; protected cuts and projections; terminal-region arguments;
the generalized Dehn inputs for handle straightening. State embeddedness,
boundary parametrizations and protection conditions explicitly. Follow the
termination measure and surgery on intersections far enough to prove the
surface existence claimed; a generic appeal to Dehn's lemma is insufficient
for the project's relative, marked constructions.
Dependencies: ordinary PL topology, precisely delimited. Outputs:
marked-boundary disks, annuli and relative projection lemmas for compact
cores and handles. Entry points: `Topology/Manifold/Smoothing/Dehn/` and
the generalized-Dehn definition used by `HamiltonLowerHandles` (within M76).

## 16. Protected compact cores and prime replacement (`compact-cores`)

Sections: one simply connected end and two compact-set quantifiers;
protected PL domains; compression complexity and minimal cores; spherical
frontier alternatives; reducing a finite frontier to one sphere; protected
irreducible replacement. Explain the decrease under an essential disk,
the marked-cut-filling contradiction, and sphere-merging induction with its
preserved frontier/protection invariant. Separate connectedness proved by
the construction from the weaker exported predicate when appropriate.
Dependencies: `dehn-surfaces`. Outputs: Wall cores and the zero-, one-,
and two-period-lattice replacement cases for lower handles. Entry points:
`Smoothing/CompactCore/`, `PrimeReduction/`, and
`Triangulation/Handles/HamiltonGeometricInputs.lean` (within M76).

## 17. Relative rigidity of lattice handles (`relative-rigidity`)

Sections: lattice handle models and protected sets; incompressible torus
cuts; marked annulus hierarchies; relative ordinary projection; supported
straightening of the lower handles. Include the Brown locally flat
sphere-ball construction and relative boundary-proper PL approximation
before using the lower-handle argument. Define all marking and relative
conditions; distinguish the cardinality-zero, one and two models. Develop
the actual rigidity/hierarchy mechanism and explain why corrections agree
on protected regions. Dependencies: the two preceding PL chapters.
Output: lower-index chart-handle straightening with its exact relative
support. Entry points: `Smoothing/Rigidity/` and lower-handle applications,
including `lowerCases_of_wall_dehn_prime` (within M76).

The source review of the historical smoothing chapter exposes two additional
constructed inputs at `Triangulation/Handles/HamiltonLowerCasesFourInputs.lean`:
`hasBrownLocallyFlatSphereBalls` and
`hasHamiltonRelativeApproximationFamily`. Their entry points are
`Smoothing/Schoenflies/Spheres/LocallyFlatSphereBalls.lean` and
`Smoothing/RelativeApproximation/Regions/BoundaryProperApproximation.lean`.
Explain the bicollar, compactified complementary region and exact ball-pair
identification, then the retained interior approximation and homotopy pasting
that fixes the protected boundary. Preserve the supplied coordinate
structures and literal frontier. These inputs are not discharged by the
relative-rigidity theorem alone. If their substantive proofs require a
separate chapter, propose the split rather than omit them to preserve the
present chapter count.

## 18. A compatible smooth structure and the topological endpoint (`smoothing`)

Sections: Alexander region balls and index three; finite relative handle
assembly; supported overlap corrections; finite affine-star triangulation;
the Cairns smoothing bridge; transport to the original manifold. Define a
compatible smooth model and its chosen homeomorphism first. Explain how
the lower-handle outputs and the top-handle construction produce compatible
charts; verify the link/coface conditions needed for triangulation and the
actual hypotheses of smoothing. The final homeomorphism composition is then
a short argument. Dependencies: `relative-rigidity`, `sphere-reduction`.
In particular, account for re-realizing the finite triangulation with
independent vertices before the Cairns step, and for pulling the resulting
atlas back to the original manifold. Distinguish the full topological
consequences transported with the model from the simple-connectedness field
actually consumed by the endpoint transport.
Entry points: `Smoothing/{SmoothAtlas,Triangulation,Assembly,Compatible}`
and `Poincare/Smoothing/` (M76--M80, M90).

## Review and integration gate

Authors supply precise statements, definitions before use, substantial proof
mechanisms and exact cross-chapter inputs, plus per-section source evidence.
Lean names belong in metadata. No novelty claim is authorized without
comparison with the cited sources. A source discrepancy is recorded for
review; Lean is preserved. Missing references are proposed in the review
artifact for central bibliography integration.

The main agent reviews `extinction` as a whole calibration chapter first,
then applies the same source and readability standard to every chapter.
Integration must resolve all proposed interfaces and the complete milestone
register, remove duplicated legacy passages, order the actual chapter
inputs, update traceability and verify PDF/site links and citations. The
historical checker equating a selected inventory with prose is insufficient
for this gate. The full Lean build and recursive admission audit are reused
while their source tree is unchanged; further Lean checks require a concrete
verification gap or changed source.

# Relative PL torus rigidity progress report

Revision 67 constructs full fiberwise products on the same nonspherical,
irreducible index-zero stage. `Hierarchy/OriginalFiberwisePhaseProducts.lean`
retains both entire phase fibers, all ambient and tangential group injections,
both cut-side irreducibilities, finite models and both relative homotopies.
On each whole closed product, all target coordinates equal the actual
endpoint tangential map at the zero section together with the signed normal
coordinate. The prescribed producer consumes the original collapse and
zero-section fixation, without a supplied collar or extra flattening.

`Coverings/LinearTorus/` constructs a covering representative of every
continuous two-torus self-map whose actual based group map is injective.
The universal lifts, integer deck differences, matrix and based homotopy
are constructed internally. Explicit integer kernel loops force nonzero
determinant; the adjugate supplies surjectivity and finite kernel. Both
the full fiberwise statement and covering theorem pass independent formal
translation and alignment.

`Coverings/OneSheet/` constructs the exact-map homeomorphism from an actual
covering and identity homotopy. Its original-lattice consumer proves path
connectedness, inverse PL regularity in the original atlases and both
literal boundary-relative homotopies. The actual hierarchy covering is
still required. `Coordinates/Translations/` and
`Maps/Adjustments/Tangential.lean` construct PL target displacements and
supported tangential homotopies preserving the entire normal circle map.
Continuous real displacements between two finite PL target maps are proved
finite PL on their complete finite source.

The integrated 29-root audit passes 5,790 jobs and inspects 66,371 reachable
declarations, with no admissions in types or bodies and only `propext`,
`Classical.choice` and `Quot.sound`. The separate torus-lift audit inspects
19,965 declarations. `make check` passes 12 frozen contracts and 25,401 jobs.
Surface recognition, application of the surface covering to original phases,
subsequent marked cuts and regluing, and the index-one branch remain open.
The unchanged full predicate has not yet been constructed.

Revision 66 constructs the nonspherical, ambient-incompressible, irreducible
index-zero cut from the original source irreducibility, standard target,
PL map and identity-relative homotopy.
`Hierarchy/OriginalNonsphericalIncompressibleSlab.lean` minimizes residual
complexity and then component count. The actual prescribed-phase products,
source sphere filling and supported ball replacement strictly decrease the
second count when any component is a source PL sphere, without increasing
the first. Both finite models retain their literal surviving components.
`Topology/NonsphericalFrontierGroups.lean` constructs essential rims and
transports their nontrivial groups to every component basepoint.

`Topology/Gluing/` proves open-cover injection with disconnected overlap.
Compatible faithful permutation actions are constructed from the two actual
overlap injections, using componentwise transports and endpoint gauges;
the existing local-to-global path transport then proves ambient injection.
`Topology/CollarGluing/` constructs the full-frontier bicollar, open side
cover and simultaneous collapse directly from the original compact PL
domain. These yield ambient injection of both closed sides.

`Hierarchy/OriginalIrreducibleSlab.lean` consumes these constructions and
the nontrivial component groups to keep every original sphere filling
inside the selected side. It proves source PL irreducibility of both the
slab and its closed exterior, whole-frontier and both-side ambient group
injection, while retaining nonspherical finite phase models and both
relative homotopies. No source disk, sphere removal, collar, group gluing,
ambient injection or cut-irreducibility supplier is added.

The final focused root passes 5,534 jobs. The twenty-root recursive source
audit passes 5,770 jobs and inspects 65,802 declarations, with zero admissions
in types or bodies and only `propext`, `Classical.choice` and `Quot.sound`.
The open-cover, collar and component-cut audits separately inspect 14,268,
38,853 and 32,777 declarations. `make check` passes 12 frozen contracts and
25,401 jobs. Independent formal translation and comparison pass for both
the nonspherical slab and final irreducible-cut statement.

Surface recognition, further marked source cuts, terminal maps and regluing
remain. The independent index-one branch owns `Rigidity/IndexOne/`, and
surface recognition owns `Rigidity/Surfaces/`; the root retains index-zero
hierarchy and predicate assembly. Full rigidity and lower-handle acceptance
remain open.

# Revision 74 (2026-09-25): published source carriers and interval compression

The workspace now includes the source-side residual endpoint collapse and
ordered/oriented residual darts, plus the actual square product band and
closed attachment carriers. The interval branch also published relative phase
compression with an original-PL endpoint. `IndexOne.Audit` now checks 20 roots
and 64,244 reachable declarations with no admissions; the expanded source
producer audit checks 66,699 declarations with no admissions and only the
three standard axioms. These artifacts advance the two marked hierarchies but
do not yet construct the source square map/original-atlas torus certificate,
the final regluing, or `HasHamiltonRelativeTorusRigidity`.

Revision 65 constructs the index-zero slab with both complete phase fibers
injecting into both closed sides, from the original map, atlases and
identity-relative homotopy. `Hierarchy/OriginalBothSidesIncompressible.lean`
minimizes the sum of actual residual complexities. Each of the four possible
noninjective phase/side cases constructs an essential proper Dehn disk and
a strict decrease. Shifted circle coordinates and asymmetric supported
compression cover the complementary arc without a half-period restriction.
The retained model for the other phase has its own ambient domain, so its
literal component model survives when the compressed side changes.

`Products/Compression/PrescribedPhaseProducts.lean` constructs exact finite
original-chart products at prescribed phases, preserving both full fibers
and all slab sides. `Hierarchy/OriginalIncompressiblePhaseProducts.lean`
composes the two constructions: a single original-homotopy PL endpoint has
both-side injection, the exact frontier equation, and the full finite
products with signed normal-coordinate equations. No regular-value, collar,
compression or terminal-stage supplier is added.

The composed hierarchy and expanded seventeen-root recursive audit pass
5,719 focused jobs. The audit traverses 65,355 declarations, with no
admissions in types or bodies and only `propext`, `Classical.choice` and
`Quot.sound`. The prescribed-product audit separately passes 4,226 jobs
and checks 40,101 declarations. `make check` passes 12 frozen contracts and
25,401 jobs. Independent formal translation and comparison pass for the
both-side slab theorem. The composed product conclusion is checked directly
against the unchanged phase and side equations of its two producers.

This does not yet prove phase injection into the whole ambient torus or
identify the phases as tori. Same-stage sphere removal, ambient injection,
the subsequent marked hierarchy and regluing, and the index-one source
construction remain. The complete index-two result of revision 64 is
retained. The full frozen rigidity predicate and lower-handle acceptance
remain open.

Revision 64 constructs the complete index-two case from its original
premises. `Disks/SourceProperMeridian.lean` proves
`exists_source_proper_meridian`: the disk is PL in the original source
atlas, embedded, proper, and equal to `hamiltonStandardMeridianMap` on every
point of the prescribed rim. The original marked Dehn disk is transported
to a constructed finite collar model. The published standard proper-disk
argument is extended to that model's marked boundary, using its actual
collar, two separated annular graphs and a whole-rim ball-pair extension.
The Euclidean identity-atlas clause `hasHamiltonStandardProperDehnDisks`
cannot itself be applied to an arbitrary source atlas; the chartwise
construction reuses its published annulus and extension lemmas instead.

`General/IndexTwoRigidity.lean` consumes this disk in the original
`exists_source_meridian_rigidity` chain, then applies the constructed
lattice normalization and return transport. Its theorem
`exists_indexTwo_lattice_rigidity` proves the unchanged relative conclusion
for all coordinate sets of cardinalities two and one and all discrete full
rank-one lattices, with both original atlases and both boundary-relative
homotopies. There are no additional geometric suppliers.

The focused rigidity build passes 5,500 jobs. The fifteen-root recursive
`Disks/SourceDiskProducersAudit.lean` passes 5,653 jobs and reaches 65,142
declarations, with no admissions in types or bodies and only `propext`,
`Classical.choice` and `Quot.sound`. `make check` passes 12 frozen contracts
and 25,401 jobs. Independent statement translation and comparison cover
the arbitrary-lattice index-two conclusion; the finite-model lemmas are
internal constructions directly checked against their uses.

The index-zero and index-one source hierarchies and regluing still remain.
The general lattice transfer is already constructed and is now applied in
index two. The full frozen predicate and lower-handle acceptance remain
open. All changes stay under `Smoothing/Rigidity/`.

Revision 63 constructs the index-zero lower-phase incompressibility step.
`Hierarchy/OriginalLowerPhaseIncompressible.lean` proves
`exists_hamiltonZero_incompressible_lower_slab` from the original source
atlas, standard target atlas, PL map and identity-relative homotopy. It
constructs a homotopic PL map and an actual two-phase PL slab whose entire
lower phase injects on every based fundamental group; the upper phase is
unchanged. The proof constructs finite source component models, proves strict
decrease of the sum of truncated residual counts under an essential physical
compression, and minimizes that natural number over actual source slabs in
the original homotopy class. The marked Dehn theorem supplies the disk in
the noninjective branch. No compression, decrease or terminal-stage supplier
is assumed.

The focused hierarchy build passes 5,407 jobs. The expanded eleven-root
`Disks/SourceDiskProducersAudit.lean` passes 5,423 jobs and reaches 64,455
declarations, with no direct admissions and only `propext`, `Classical.choice`
and `Quot.sound`. `make check` passes all 12 frozen contracts and 25,349 jobs.
The finite-count and physical-compression lemmas are intermediate helpers;
their hypotheses and conclusions were compared directly during construction.
This one-sided result does not establish injection into the whole ambient
torus. Opposite-side compression, sphere removal in the same retained stage,
phase identification, the subsequent marked hierarchy and regluing remain;
so do the exact meridian-rim correction, index-one construction and arbitrary
lattice transfer. The frozen predicate and lower-handle acceptance stay open.

Revision 62 constructs proper embedded source disks by consuming the published
marked Dehn theorem. `General/SourceMeridianBoundaryData.lean` applies to every
discrete rank-one lattice and retains essentiality of the output rim.
`Disks/SourceMeridianBandDisk.lean` confines that rim to the original relatively
open signed meridian band and preserves its nontrivial first-coordinate class.
`Disks/OriginalSlabProperDisks.lean` constructs proper essential disks on both
sides and both phases of the original k=0 regular slab when phase inclusion
is noninjective. `Disks/OriginalSlabCompressionAlternative.lean` consumes the
disk in the physical compression chain, producing old and compressed finite
surface triangulations with Euler-count increase two, from the original
atlas, PL map and identity-relative homotopy. No disk supplier remains in
these alternatives. The focused compression build passes 5,388 jobs and
`make check` passes 12 frozen contracts and 25,232 jobs. The recursive audit
is `Disks/SourceDiskProducersAudit.lean`: all six roots pass, with 64,347
reachable declarations, no direct admissions in types or bodies, and only
`propext`, `Classical.choice` and `Quot.sound`.

The frozen rigidity predicate remains open. The marked meridian output still
needs chartwise prescribed-rim correction before `SourceMeridianRigidity`
applies. The standard proper-disk theorem at `ca239d133` proves this correction
only for subsets of Euclidean three-space with the identity atlas. The k=0
compression now has a constructed disk and physical Euler change, but still
requires a strictly decreasing complexity, iteration, incompressible-phase
identification and marked regluing; k=1 and arbitrary-lattice rigidity transfer
remain. No registry, CompactCore, Compatible or frozen contract was changed.

Revision 58 composes the published Dehn disk with the original terminal
proper-disk constructor and the proved finite tower fold. The new
`exists_source_folded_stage_marked_disk` theorem returns the actual folded
`StageMarkedDisk` at the original base subgroup, while retaining the exact
frontier equation and transported rim values. Its focused build and recursive
audit pass in 5,054 and 5,055 jobs; the folded producer reaches 62,652
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`. The rim is still transported rather than literally the
standard meridian, and the k=0/k=1 hierarchy/regluing and final frozen
predicate assembly remain open.

Revision 57 consumes Dehn commit `8e0cfa56d`, whose
`exists_marked_boundary_PL_loop_disk` theorem constructs the folded disk,
exact frontier equation, embedding, and finite-descent rim transport. The new
Rigidity bridge `Disks/OriginalMarkedBoundaryBridge.lean` exposes this output
without changing its hypotheses. Its focused build and recursive audit pass
in 5,054 and 5,055 jobs respectively; the audit reaches 62,651 declarations,
with no direct admissions and only `propext`, `Classical.choice`, and
`Quot.sound`. The producer still returns a base-path-transported rim rather
than the literal standard meridian rim, and the protected-surface and k=0/k=1
source hierarchy/regluing constructions remain open, so the frozen predicate
is not yet assembled.

Revision 56 records the Dehn owner’s local verification of the fixed
marked-boundary PL-loop theorem: self-paired circle removal, finite tower
descent, and the source-annulus equations now pass Lean without a surgery
supplier. The theorem is not yet published on shared `main`; protected
surfaces and the prescribed-rim disk clauses remain open, so no Rigidity
consumer can be integrated yet.

Revision 55 records shared PrimeReduction continuation `7c69dc5c4`, whose new
sphere-position and circle-tube roots compile in 4,574 focused jobs. This
upstream geometry does not expose the folded `StageMarkedDisk`, finite-decrease
witness, proper source meridian, or k=0/k=1 hierarchy, so Rigidity remains at
the same producer boundary and the frozen predicate is still unassembled.

Revision 54 records the shared Dehn registration `804fbc341` and its verified
workspace build: `lake build PoincareLib` completes 25,087 jobs. The terminal
marked-disk audit reaches 58,289 declarations and the conditional
source-meridian audit reaches 41,763, both with no direct admissions and only
`propext`, `Classical.choice`, and `Quot.sound`. The registration exposes the
source reduction modules but still no folded `StageMarkedDisk`, finite-decrease
witness, proper source meridian, or k=0/k=1 hierarchy, so the frozen rigidity
predicate remains unassembled.

Revision 53 records the shared workspace fast-forward through `b26921998`
(`918e60fc8` and its Dehn projection-reduction/reflection continuation). The
Rigidity roots build in 4,452 jobs; the source-meridian audit reaches 41,763
declarations and the source-strip audit reaches 34,869, with no direct
admissions and only the three standard axioms. The new Dehn geometry still
does not add the folded `StageMarkedDisk`, finite-decrease witness, proper
source meridian, or k=0/k=1 hierarchy.

Revision 52 records the shared workspace fast-forward to `918e60fc8`. The
PrimeReduction sphere-cap continuation and Dehn provenance metadata build
cleanly with all 12 frozen contracts and 25,054 Lean jobs. These upstream
changes do not add the folded `StageMarkedDisk`, finite-decrease witness,
proper source meridian, or k=0/k=1 hierarchy, so no Rigidity predicate or
registry change is made.

Revision 51 records the concrete producer handoff in project topic message
`2024`, naming commit `e23b25e9b` and the exact missing interface: an actual
original proper-meridian disk with its complete prescribed rim map. The
conditional consumer is ready; Dehn owns that producer, while the k=0/k=1
source hierarchy remains Rigidity-owned. No new supplier or registry change
was introduced.

Revision 50 adds `General/SourceMeridianRigidityAudit.lean` for the exact
conditional index-two consumer. Its fixed-period cut, Alexander extension,
regluing, and relative-homotopy chain reaches 41,763 declarations with no
direct admissions and only `propext`, `Classical.choice`, and `Quot.sound`;
the target build passes 4,398 jobs. This confirms that the existing consumer
is ready for the original proper-meridian producer, but does not turn that
producer into an assumption or close the frozen predicate.

Revision 49 consumes shared tip `af51e974e`, which registers the latest
Dehn/PrimeReduction support modules. The source-strip audit still passes at
the shared tip (five roots, 34,869 reachable declarations, no admissions and
no nonstandard axioms), and the focused source-strip build passes 3,085 jobs.
The registration contains no folded `StageMarkedDisk`, finite-decrease
producer, proper source meridian, or k=0/k=1 hierarchy, so no rigidity
predicate assembly is possible yet.

Revision 48 adds a recursive audit for the Rigidity-owned source-strip
triangulation package. The five roots (finite source-strip image
triangulations, disk count, and the two original tube-strip producers)
reach 34,869 declarations with no direct admissions and no nonstandard
axioms; the focused Lean build passes. This verifies the finite PL source
surfaces handed to Dehn's selected-arc tube construction. It still does
not construct the folded `StageMarkedDisk`, the source proper meridian, or
the k=0/k=1 marked hierarchy and regluing, so the frozen rigidity predicate
remains open.

Revision 47 reruns the Rigidity source-cut recursive audit on the current
shared tip. `exists_hamiltonZero_closed_source_circle_cut`, its face package,
and its compactness package have only `propext`, `Classical.choice`, and
`Quot.sound`. `make check` passes 12 frozen contracts and 25011 Lean jobs.
This verifies the existing source-cut carrier but does not discharge the
still-open folded `StageMarkedDisk`, proper meridian, or k=0/k=1 hierarchy.

Revision 46 rebases onto shared `2b39549c6`, which adds a constructed
protected sphere-system orbit minimum and returning-component exclusion in
PrimeReduction. The focused PrimeReduction returning-face root together with
the Rigidity source-cut root builds in 4326 jobs. This is upstream sphere
reduction only; it does not provide the Dehn folded `StageMarkedDisk`, source
proper meridian, or the k=0/k=1 hierarchy/regluing needed for the frozen
rigidity predicate.

Revision 45 consumes the shared continuation at `8e5327de8`: the Dehn
`Step.exists_ordinary_marked_projection` producer now constructs the complete
ordinary double-curve model after exceptional-point repair, and the circle
batch constructs actual self-paired incident joints and diamond maps. Focused
builds of `OrdinaryMarkedProjection`, `OriginalIncidentJoints`,
`JointDiamondMap`, and the protected surgery step pass 4462 jobs. The
protected operation still documents that ordinary crossings, selected-tube
assembly, component decrease, and geometric descent are separate; hence this
continuation does not yet supply the global non-injective fold or the initial
proper meridian. The k=0/k=1 marked hierarchy and regluing remain open.

Revision 44 rebases the Rigidity carrier onto shared main
`eee454420 Register published Dehn producer modules`. The registered Dehn
roots all build on this tip, including `OriginalDoubleArcSurgeryStep`,
`OriginalMovedProjection`, and the terminal marked-disk bridge; the full
`PoincareLib` root build passes 25009 jobs. The available source-side
termination theorem removes all non-self-paired interior circles, while its
result still permits self-paired components. The protected surgery API is
stage-local and the backward fold still requires the unresolved global
non-injective `one_step` producer. Therefore this registration supplies no
proper source meridian or k=0/k=1 marked hierarchy/regluing, and the frozen
rigidity predicate remains unconstructed.

Revision 43 rebases the Rigidity carrier onto shared main
`07d06209fa2cef5a099fb2ee92cb6dd133624ac3`. The new prime-reduction
sphere-system batch constructs contact-decreasing moves from an already
supplied finite `ChartwisePLSphere` system; it does not construct the source
phase's folded `StageMarkedDisk`, proper meridian, or marked hierarchy. The
actual source-cut module remains build-clean at 3587 jobs.

Revision 42 adds the compactness producer for the actual k=0 closed source
phase pullback. It derives compactness from the unchanged Hamilton lattice
domain and the closed period interval, so the later marked compression can
work inside a compact source carrier without adding a premise. The focused
managed build still passes 3587 jobs, and the recursive audit of the compact,
face, and source-cut declarations still reports only `propext`,
`Classical.choice`, and `Quot.sound`.
The rebased workspace `make check` also passes: all 12 frozen contracts and
24965 Lean jobs.

Revision 41 extends the Rigidity-owned closed source phase-cut construction
with the actual k=0 lower and upper source-face embeddings and their literal
projection identities. The new face theorem is checked from the unchanged
original-map phase, and its audit reports only `propext`, `Classical.choice`,
and `Quot.sound`.

The focused hierarchy build passes (3587 jobs), and the dedicated recursive
audit passes for both the source-cut and face declarations.

Revision 40 publishes the Rigidity-owned closed source phase-cut construction
`Hierarchy/Mathlib/ClosedCirclePullback.lean` and its actual closed-handle
specialization `Hierarchy/OriginalClosedCirclePullback.lean`. For any original
circle-valued phase map, the pullback over the complete period interval is
closed, its source projection is a quotient map and surjective, and its fibers
are exactly singleton points or the two corresponding endpoint faces. The
specialization applies this to `hamiltonZeroCircleMap phi` without adding a
premise or changing the frozen predicate; PL-manifold recognition,
compression, and hierarchy regluing remain subsequent obligations.

Focused managed builds passed for both new modules (1577 and 3587 jobs), and
the repository `make check` passed (12 frozen contracts, 24939 Lean jobs).

Revision 39 publishes the Rigidity-owned `OriginalProtectedPlaneEquation.lean`
extraction and its recursive audit, together with the completed interface of
`OriginalPhysicalEulerChange.lean` and its recursive audit, and the
released DoubleArc scheduling facade.  The actual source
slab compression now exposes whole-strip frontier openness and product
avoidance of the untouched upper phase.  The new producer triangulates the
old lower-phase frontier from the source `PLDomain`, identifies the cut
complement with the upper phase, and invokes the literal annulus-and-cap
subdivision to obtain geometric complexes satisfying
`Anew.surfaceEulerCount = Aold.surfaceEulerCount + 2`, together with the
constructed coordinate map's continuity, injectivity, and chartwise-PL data.

The bounded public declaration `PoincareMT.M76.Dehn.exists_free_point_height_crossing`
is published in `cbebdfb62ab96be4284232bc2fd79ea8f811ff00`. It is an exact
signature facade over the unchanged private crossing constructor, with no
registry edits or new geometric premise; its focused Lean build passes.

The new protected-plane extraction invokes the verified upstream
`Step.exists_original_protected_crossed_charts` producer and exposes its
whole-left-plane equation in a small result tailored to the backward fold. It
does not alter any Dehn declaration or add a conditional supplier. A fresh
source rebuild also exposed two existing errors in the released
`OriginalDoubleArcSurgeryProtectedEdges.lean`; those remain with the Dehn
owner for repair.

The same file now also exposes the post-motion form: the moved disk, its
left-source fixation, the exact map relation to the initial disk, and the
preserved whole-left-plane equation. This is the local geometric package
needed by the non-injective fold once the global surgery producer is repaired.

Revision 33 publishes `OriginalSlabMarkedPLFilling.lean`, its focused
recursive audit, `OriginalTerminalDiskFromMarkedPL.lean` with its audit, and
`OriginalTerminalMarkedDisk.lean` with its audit.

The new producer consumes the original slab compression-rim alternative. It
retains the injective branch and, in each noninjective branch, applies the
marked square PL approximation to construct an original-atlas PL square,
exact rim trace, and transported nontrivial rim class. It does not assert
disk embedding or properness.

Revision 29's source-phase residual consumer remains included below.

The terminal-disk bridge feeds each marked original-atlas PL square into the
imported finite-tower constructor with the literal basepoint and bottom
subgroup. It produces the finite tower and its terminal embedded proper disk;
the downward fold to the initial source stage is still separate.

The terminal marked-disk package now exposes that output directly as the
`StageMarkedDisk` record, preserving the exact rim, basepath, properness, and
bottom-subgroup exclusion for the next backward-fold consumer.

The injective backward-fold branch now composes an upper `StageMarkedDisk`
through one tower step whenever the projected map is globally embedded.  The
constructed lower record preserves its PL atlas map, embedding, inside and
exact frontier conditions, rim trace, basepath, and subgroup exclusion.  This
is the complete no-crossing branch; the non-injective branch still requires
the global double-curve surgery and strict residual descent.

The new consumer invokes the constructed Hamilton-zero source phase reduction,
extracts its original-atlas map certificate, and pairs it with the actual
common-subdivision square-annulus/strip witness at `L = 128`, `d = 1`. The
witness contains finite complexes, exact residual equations, strict surface
count decrease, and strict residual decrease.

Verification:

- focused managed Lean build: 3943 jobs, passed;
- terminal-disk bridge build: 4466 jobs, passed;
- terminal marked-disk package build: 4471 jobs, passed;
- recursive axiom audit: 34886 reachable declarations, no admissions, and
  `propext`, `Classical.choice`, `Quot.sound`;
- terminal-disk recursive audit: 58286 reachable declarations, no admissions,
  and `propext`, `Classical.choice`, `Quot.sound`;
- terminal marked-disk recursive audit: 58289 reachable declarations, no
  admissions, and `propext`, `Classical.choice`, `Quot.sound`;
- injective backward-fold build: 2854 jobs, passed;
- injective backward-fold recursive audit: 29730 reachable declarations, no
  admissions, and `propext`, `Classical.choice`, `Quot.sound`;
- physical Euler-change focused build: 4587 jobs, passed;
- physical Euler-change interface extension focused build: 4587 jobs, passed;
- physical Euler-change recursive audit: 59406 reachable declarations, no
  admissions, and `propext`, `Classical.choice`, `Quot.sound`;
- DoubleArc free-crossing facade focused Lean build: passed;
- protected-plane extraction focused Lean build: 3943 jobs, passed;
- protected-plane extraction recursive audit: 39108 reachable declarations,
  no admissions, and `propext`, `Classical.choice`, `Quot.sound`;
- workspace `make check`: 12 frozen contracts verified and 24939 Lean jobs,
  passed;
- published protected-plane extraction commit:
  `9e8708e7fa5b2ce0105ea44d333df5e85f285360`;
- published DoubleArc facade commit: `cbebdfb62ab96be4284232bc2fd79ea8f811ff00`.

The frozen `HasHamiltonRelativeTorusRigidity` predicate remains open. In
particular, the initial proper source meridian and the k=0/k=1 marked
hierarchy and regluing have not been constructed, and no conditional supplier
has been added.
# Revision 59 (2026-09-25): current Dehn projection boundary

The current shared tip includes Dehn's marked stage projection reduction and
reflection-insertion modules through `b26921998`.  They preserve the original
transported rim and its excluded whiskered class while reducing projection
fibres and paired-circle complexity; they do not identify that rim with
`hamiltonStandardMeridianMap`, nor do they construct the k=0/k=1 source
hierarchy or regluing.  The Rigidity folded-stage bridge therefore remains the
correct consumer boundary and no conditional facade was added.

`lake build PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalFoldedStageMarkedDiskAudit`
passes at 5,055 jobs.  The recursive audit reports 62,652 reachable
declarations, no direct admissions, and only `propext`, `Classical.choice`, and
`Quot.sound`.  The next concrete integration target is a source-atlas
standard-rim normalization theorem that consumes this transported-rim output;
only after that can the proper-meridian consumer and the two marked hierarchy
cases be assembled.

# Revision 60 (2026-09-25): source square-rim class verification

`General/SourceStandardRimNontrivial.lean` now proves
`squareRimLoop_class_ne_one`.  The proof identifies the literal square rim
with the period loop on `AddCircle (4 * 2)` through the checked
`HamiltonIndexOne.squareCircle` parametrization, then applies the imported
period-loop noncontractibility theorem.  This verifies the standard source
boundary class used by the meridian argument without adding a geometric
supplier or changing the frozen predicate.

The result also fixes the exact remaining interface boundary.  The existing
`exists_source_marked_boundary_disk` producer returns a new `gammaOut` and
proves `j z = gammaOut z`; it does not prove `gammaOut` equals the input
standard meridian pointwise.  Therefore the verified class lemma cannot be
used to claim an exact standard-rim proper disk.  The source-atlas
standard-rim normalization, the proper meridian, and the k=0/k=1 marked
hierarchy/regluing remain open.

Verification: focused `lake env lean
PoincareLib/Topology/Manifold/Smoothing/Rigidity/General/SourceStandardRimNontrivial.lean`
passes (only existing unused-tactic and proposition-instance linter warnings).
The dedicated recursive audit reaches 17,363 declarations, reports no direct
admissions, and finds only `propext`, `Classical.choice`, and `Quot.sound`.

# Revision 61 (2026-09-25): ownership handoff boundary

The shared tip still contains no theorem upgrading the transported `gammaOut`
to the prescribed `hamiltonStandardMeridianMap`, and no k=0/k=1 source
hierarchy producer.  The remaining work is therefore assigned at the original
module boundaries: the Dehn continuation owner must publish the exact-rim
proper source meridian (including arbitrary-lattice transfer), Rigidity must
consume it and construct the two marked Waldhausen hierarchies and regluing,
and `m76-import-and-continue` must wire the resulting unchanged predicate into
the lower-case registry and consumer.  The published class theorem, folded
stage bridge, and recursive audits are ready for that integration.

# Revision 68 (2026-09-25): constructed meridian and source phase frontier

This consolidates the subsequent published checkpoints. Earlier remaining-work
statements above describe their historical revisions, not the current frontier.

- `4cd73f3a00efb1ad79ed00a3dbee728557e04e53` constructs the exact prescribed
  proper source meridian and `exists_indexTwo_lattice_rigidity`, including
  arbitrary-lattice transfer, original atlases, and both literal boundary
  homotopies. Its recursive audit checked 65,142 declarations without admissions.
- `dbcf1ac1998ce9ba3140423038b586d64eaa2448` constructs both-side incompressible
  source phases and exact finite original products. Audit: 65,355 declarations.
- `da3f91f9a975319501286f47e0383c088e26368d` constructs simultaneous sphere
  removal, nontrivial component groups, whole-frontier and both-side ambient
  injections, and both irreducible source cut domains. Audit: 65,802 declarations.
- `9952f657712748f0d82aa49121c8bbf7f5d62b44` constructs the original full
  fiberwise phase products and based covering representatives of actual
  fundamental-group-injective two-torus maps. The one-sheet original-atlas
  consumer proves the frozen conclusion once an actual covering is constructed.
  Integrated audit: 29 roots, 66,371 declarations, no admissions, only
  `propext`, `Classical.choice`, and `Quot.sound`; focused build: 5,790 jobs.
  `make check`: 12 frozen contracts, 25,401 jobs. Independent statement
  translations and comparisons passed for the two new graph statements.
- `05a6ad7343c8f8b75f1314a6a1d141e7f871de17` constructs real displacement
  from an actual torus homotopy, finite original-chart collar extension,
  supported phase replacement, disconnected finite covering assembly, original
  target affine PL maps, and normalized compatible second-coordinate boundary
  lifts. Integrated audit: 35 roots, 66,517 declarations, no admissions and only
  the same three standard axioms; focused build: 5,802 jobs.
  `make check`: 12 frozen contracts, 25,403 jobs.

The audit command is `lake build
PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.SourceDiskProducersAudit`.
The command recursively inspects declaration bodies and types, in addition to
collecting each root's axioms. It does not allow auxiliary admissions.

The complete fixed-source torus recognition, subsequent marked surface
hierarchy, terminal regluing, and index-one rigidity remain open. The active
recognition continuation owner is `session_ce8ad967657a47578204cd9110782dcf`
(queued on `incompressible-torus-surface-recognition`) under
`Rigidity/Surfaces/`; its preceding session published candidate and injection
adapters but did not prove the classification or parametrization. The index-one owner is
`session_c49f129c44d34cd9a0c3e828b24b4bf0` under `Rigidity/IndexOne/`.
This session retains the index-zero marked hierarchy and final predicate
assembly. `m76-import-and-continue` retains CompactCore, Compatible, and
registries. No new supplier is added to `HasHamiltonRelativeTorusRigidity`.

The source route is Waldhausen 1968, Section 1.3, pp. 59--60 and Theorem 6.1,
pp. 77--79, with the Hamilton 1976 Lemma 3 application, pp. 65--67.

# Revision 69 (2026-09-25): covering installation and marked regular surface

Published `a12ba807d1e1c1fb57fd324fe9538608e72217d2`. The new installation
theorem combines the actual group-injective phase map, finite recognized torus
components, constructed covering representatives, and the supported PL
adjustment. It preserves the full product formula on a quarter collar and
proves the actual ambient map locally homeomorphic on that collar and its
zero section. The finite marked source package now retains the same selected
regular level together with compactness, all normalized interior and boundary
height charts, the complete halfspace/frontier equations, the whole old
frontier, and the entire rim in one common finite graph model with an original
PL inverse.

The integrated recursive audit reaches 66,574 declarations with no direct
admissions and only `propext`, `Classical.choice`, and `Quot.sound`; the focused
build has 5,823 jobs and `make check` passes all 12 frozen contracts and 25,450
library jobs. The finite marked package's dedicated audit reaches 32,946
declarations without admissions. These checked artifacts still stop at the
explicit recognition interface: a finite disjoint torus cover, torus
parametrizations, and their original-target PL certificates remain to be
constructed by the resumed Surfaces mission. The active continuation is queued
as `session_ce8ad967657a47578204cd9110782dcf`; the interval-torus owner remains
`session_c49f129c44d34cd9a0c3e828b24b4bf0`. No supplier or frozen declaration was
added.

# Revision 70 (2026-09-25): interval bicollar and retained annulus geometry

The workspace fast-forwarded to `f5e25ee05`. The interval branch now includes
the actual marked source bicollar, real-height and old-boundary endpoint
preservation, plus retained annulus and Kneser geometry. Its updated
`IndexOne.Audit` checks 17 roots and 34,774 reachable declarations with no
admissions and only the three standard axioms. The focused managed build and
workspace `make check` pass (12 frozen contracts, 25,450 jobs).

The surface-recognition continuation has separately published exact residual-
edge and essential-polygon intermediates with clean audits; the square quotient
and original-atlas torus parametrization are still unproved. The unchanged
rigidity predicate therefore remains open, and no conditional supplier has
been added.

# Revision 71 (2026-09-25): selected-family transport integration

The workspace now includes the published Dehn/prime-reduction transport at
`dbf4e274e`: connected-component no-L3 transport and selected-circle exterior
identity are available to the lower-handle source chain. The full workspace
gate passes again: all 12 frozen contracts and 25,450 Lean jobs. These modules
remain outside the Rigidity ownership boundary; this session only consumed the
published workspace state for coordination.

The surface continuation has now produced a checked paired-cycle artifact,
with distinct residual edges and their unique shared-edge supports. It is
continuing against the reviewed dual-tree boundary correction; no square
quotient or torus parametrization has yet been claimed.

# Revision 72 (2026-09-25): published Dehn annulus surgery

The workspace now includes `27724c784`, the Dehn branch's annulus surgery
continuation. It adds exact retained-cylinder contacts and charts, finite
component and graph-incidence decompositions, interior interval and polygon
component models, nested contractible fibers and properness, retained
exteriors and copied-rim stage correction, and the self-paired reflection and
trace-removal constructions. The unchanged `IndexOne.Audit` target passes
at this tip; this check is not a check of the new Dehn modules or a proof
of the interval rigidity endpoint.

The surface branch has since proved the primal-tree contraction internally,
but its commit is not yet reachable from the workspace tip. The square
quotient, original-atlas torus parametrization, index-zero/index-one marked
regluing, and the unchanged predicate remain open. No conditional supplier or
frozen declaration was added.

# Revision 73 (2026-09-25): exact square-to-torus descent

Published [the periodic-square target](/api/v2/forge/web/poincare-conjecture/workspace-poincare-conjecture/commit/2d4612583cc8bdc8a217cd4f23795fd4d7ae45b9) in
`Coordinates/PeriodicSquare.lean`. The checked construction proves the
closed-square projection is a quotient map onto `AddCircle p × AddCircle p`,
identifies its fibers with the equivalence generated by the two opposite-side
pairings (including corners), and descends any continuous surjective square
map with exactly those fibers to a torus homeomorphism. The managed build
passes 1,578 jobs, and the integrated source-producer audit passes 66,689
reachable declarations with no admissions and only the three standard axioms.
The source surface still must provide the square map and original-atlas PL
certificate; the unchanged rigidity predicate and lower-handle consumption
remain open.

# Revision 75 (2026-09-25): contracted boundary transport in the integrated audit

Fast-forwarded to `759cf81db`, which adds the corrected copied-side transport
lemma `contracted_boundary_side_endpoint_eq` after primal-tree contraction.
`SourceDiskProducersAudit` now imports and audits that theorem together with
the square descent and residual-edge chain: the focused build passes 5,838
jobs, reaches 66,701 declarations, and reports no direct admissions with only
`propext`, `Classical.choice`, and `Quot.sound`. The full `make check` passes
all 12 frozen contracts and 25,458 library jobs. The source square map,
original-atlas PL parametrization, marked regluing, and the unchanged
`HasHamiltonRelativeTorusRigidity` predicate remain open.

# Revision 76 (2026-09-25): residual boundary bridge to the periodic square

Fast-forwarded to `89ae0cc8f`, which adds `OriginalTorusPeriodicSquareBoundary`.
The four residual labels now have explicit square-side representatives, exact
opposite-side pairing, and compatibility with the boundary inventory's
Boolean involution. The surface audit passes 3,491 jobs and reaches 28,864
declarations with no admissions; the integrated source audit passes 5,840
jobs and reaches 66,716 declarations with no admissions, using only
`propext`, `Classical.choice`, and `Quot.sound`. The source surface map,
original-atlas PL parametrization, PhaseCoveringInstallation, both marked
regluing branches, and the unchanged rigidity predicate remain open.

# Revision 77 (2026-09-26): scaled residual corner trace

The new `Surfaces/OriginalTorusResidualCornerData.lean` package retains the
actual oriented residual side paths after the corrected primal-tree boundary
inventory. `ResidualCornerData` records both opposite endpoint identities and
finite-piecewise-affine witnesses in the original carrier. The companion
`OriginalTorusResidualCornerTrace.lean` scales those paths to an arbitrary
positive collar length, proving continuity, finite-piecewise-affine trace
witnesses, and exact opposite-corner transport on `Icc 0 p`.

The focused trace build passes 3,498 jobs. Its recursive audit reaches 29,020
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`. This is a checked boundary package for the remaining square
filling step; it does not classify the closed Euler-zero carrier or construct
the `SourceSquareMap`. The source square map, original-atlas parametrization,
PhaseCoveringInstallation, marked regluing, and unchanged rigidity predicate
remain open.

# Revision 78 (2026-09-26): closed-filling handoff contract

`Surfaces/OriginalTorusSquareMap.lean` now provides the noncomputable
constructor `SourceSquareMap.of_closed_filling`. It packages exactly the
remaining geometric output of the corrected cut: a continuous surjective map
on the square, equality on each opposite side pair, no fibers beyond the
periodic projection relation, and a finite-piecewise-affine representative in
the original carrier. The constructor proves the complete `Relation.EqvGen`
fiber statement and therefore hands its result directly to the existing
square-to-torus descent and `PhaseCoveringInstallation` consumers; it does not
assert the existence of the filling or classify the Euler-zero surface.

The focused constructor build passes 3,488 jobs. The dedicated recursive audit
passes 13,750 reachable declarations, reports no direct admissions, and allows
only `propext`, `Classical.choice`, and `Quot.sound`. The actual closed filling,
original-atlas parametrization, index-zero regluing, and unchanged rigidity
predicate remain open.

# Revision 89 (2026-09-26): exclude opposite-sheet interior collisions

`twoDiskMap_no_cross_fiber_interior` consumes the checked frontier
localization and proves that a point strictly inside either selected chart
cannot collide across sheets (the opposite point needs no interior
hypothesis).  Together with the existing
same-sheet injectivity, this gives the exact interior part of the glued-fiber
relation while retaining all boundary collisions for the side transition.

The focused build passes 2,586 jobs.  The recursive audit reaches 12,248
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`.  The full gate remains 26,474 jobs with all 12 frozen
contracts verified.  Constructing the interior periodic square itself,
original-atlas parametrization, index-zero regluing, and the unchanged
rigidity predicate remain open.

# Revision 79 (2026-09-26): source-map family handoff consumed by phase installation

`Surfaces/OriginalTorusSquareMap.lean` now exports
`SourceSquareMap.exists_family_ambient_data`. For a finite family of source
maps it packages the ambient finite-piecewise-affine representatives, exact
image equalities, and exact periodic fibers required by the phase hierarchy.
`Hierarchy/PhaseCoveringInstallation.lean` consumes this checked family
handoff directly, so a future closed-filling producer can enter the
installation chain without repeating coercion and image proofs. The focused
phase build passes 4,258 jobs; the closed-filling audit reaches 13,758
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`; and the workspace gate passes all 12 frozen contracts and
26,442 jobs.

This is an integration adapter, not the missing surface-recognition theorem:
the actual closed Euler-zero filling, original-atlas parametrization,
index-zero regluing, and unchanged `HasHamiltonRelativeTorusRigidity` remain
open. No supplier or frozen declaration was added.

# Revision 80 (2026-09-26): dependent source-family handoff

`SourceSquareMap.exists_dependent_family_ambient_data` now packages source
maps indexed by the two phase labels, and
`Hierarchy/TwoPhaseCoveringInstallation.lean` exposes
`exists_hamiltonZero_two_phase_coverings_of_source_square_maps`, consuming that
handoff directly. This closes the next producer-to-consumer adapter without
introducing a square map or a classification premise. The focused hierarchy
build passes 4,260 jobs; the recursive surface audit reaches 13,759
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`; and `make check` passes all 12 frozen contracts and 26,442
jobs. The actual closed filling, index-zero regluing, and frozen rigidity
predicate remain open.

# Revision 81 (2026-09-26): ambient source-map producer adapters

`SourceSquareMap.of_ambient_closed_filling` now converts an ambient square
map, its exact side and fiber equations, and a finite-piecewise-affine witness
into the existing source-square contract. The finite and dependent family
constructors expose the same conversion to both phase-covering consumers.
The focused source build passes 3,488 jobs, the phase hierarchy passes 4,260,
the recursive closed-filling audit reaches 13,765 declarations with no direct
admissions and only `propext`, `Classical.choice`, and `Quot.sound`, and the
workspace gate passes 12 frozen contracts and 26,465 jobs. The nonconditional
closed filling and index-zero rigidity clause remain open.

# Revision 82 (2026-09-26): copied-triangle quotient boundary

`OriginalTrianglePartialQuotient.lean` now provides
`partialProjectionHomeomorph_of_complete`. Given the explicit completeness
condition that every pair of copied carrier points with equal original
coordinate lies in the retained pointwise gluing relation, it constructs the
homeomorphism from the partial copied-triangle quotient to the original
surface. The focused build passes 2,531 jobs and its recursive audit reaches
14,450 declarations with no direct admissions and only `propext`,
`Classical.choice`, and `Quot.sound`. This is a checked conditional boundary;
the residual-side proof of completeness, the actual closed filling,
index-zero regluing, and unchanged `HasHamiltonRelativeTorusRigidity` remain
open.

# Revision 83 (2026-09-26): vertex-fiber pointwise gluing

`OriginalTrianglePointwiseCompleteness.lean` now proves
`pointwiseGlueRelation_complete_at_vertex`: when every shared original edge
is retained as a contact, the connected link at an original vertex identifies
any two copied carrier points represented by triangles containing that vertex.
The focused build passes 2,620 jobs; its recursive audit reaches 23,452
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`. The theorem covers the vertex-fiber case only; edge and
interior fibers, the nonconditional closed filling, index-zero regluing, and
the unchanged rigidity predicate remain open.

# Revision 84 (2026-09-26): exact copied-triangle fibers and residual re-gluing

The merged `Surfaces/Cuts` construction now proves exact pointwise fibers for
the original shared-edge contact relation, including the vertex case via
connected links and the edge/interior common-face cases. It then constructs
the selected-contact partial quotient, proves the remaining-edge regluing
relation has exactly the original projection fibers, and obtains the reglued
homeomorphism to the original surface. The focused Cuts build and recursive
audit pass 2,786 jobs and 33,116 reachable declarations with no direct
admissions, using only `propext`, `Classical.choice`, and `Quot.sound`. The
closed Euler-zero square filling, original-atlas square parametrization,
index-zero regluing, and unchanged rigidity predicate remain open.

# Revision 85 (2026-09-26): merged workspace gate after cut reconstruction

After merging the published copied-triangle cut and protected attachment
producers, `make check` passes all 12 frozen contracts and 26,474 Lean jobs.
The exact-fiber and regluing artifacts remain admission-free under their
focused recursive audit. The finite dual-tree square filling, its original
atlas PL representative, index-zero regluing, and unchanged
`HasHamiltonRelativeTorusRigidity` are still the active obligations.

# Revision 86 (2026-09-26): named closed-boundary attachment

`OriginalTorusClosedBoundaryAttachment.lean` packages the existing rooted
four-side producer as `ClosedBoundaryAttachment`. The record retains the
actual finite PL carrier, a common root, all four side traces, endpoint
equations, carrier containment, finite-piecewise-affine witnesses, and the
pointwise opposite-side equation. Its recursive audit reaches 29,136
reachable declarations with no direct admissions and only
`propext`, `Classical.choice`, and `Quot.sound`; `make check` passes all 12
frozen contracts and 26,474 jobs.

This is a checked boundary producer interface. It does not assert an
interior square extension, exact full-carrier fibers, an original-atlas torus
parametrization, index-zero regluing, or the unchanged rigidity predicate.
Those remain the next construction obligations.

# Revision 87 (2026-09-26): localize cross-sheet collisions to the rim

`OriginalTorusTwoDiskFiberBoundary.lean` adds the first collision invariant
for the checked pair of complementary rectangle charts.  From the exact
common-rim intersection and the four side-membership equivalences, every
cross-sheet equality in `twoDiskMap` is proved to lie on the frontier of the
unit square in both chart coordinates.  The result is exposed both for the
abstract `twoDiskFiber` relation and for the actual `twoDiskMap`, and the
frontier characterization is proved directly for the closed unit square.

The focused build passes 2,586 jobs.  The recursive audit reaches 12,193
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`; `make check` passes all 12 frozen contracts and 26,474 jobs.
This closes the boundary localization needed by the quotient step, while the
interior square filling, exact periodic fibers, original-atlas
parametrization, index-zero regluing, and unchanged rigidity predicate remain
open.

# Revision 88 (2026-09-26): construct the boundary transition relation

The same two-disk module now proves that every boundary point of either
rectangle chart maps into the common rim, and that each boundary point on the
first chart has a unique boundary preimage on the second chart.  The latter
uses only surjectivity and injectivity of the existing finite PL rectangle
homeomorphisms plus the cross-sheet collision localization; it retains the
actual pointwise ambient equality needed for side reparameterization.

The focused build remains 2,586 jobs.  The recursive audit now reaches 12,197
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`; the full workspace gate remains at 26,474 jobs with all 12
frozen contracts verified.  The transition is a boundary gluing input, not an
interior extension or a torus classification, so exact periodic fibers,
original-atlas parametrization, index-zero regluing, and the frozen rigidity
predicate remain open.

# Revision 89 (2026-09-26): reverse boundary transition uniqueness

`exists_unique_boundary_match_reverse` supplies the converse half of the
boundary transition relation: every boundary point on the second rectangle
chart has exactly one boundary point on the first chart with the same ambient
carrier value.  Together with the forward theorem, this gives the checked
two-sided boundary matching needed to pass from the complementary rectangle
charts to a copied-sheet quotient.  The focused build passes 2,586 jobs and
the recursive audit reaches 12,249 declarations with no direct admissions,
using only `propext`, `Classical.choice`, and `Quot.sound`.  The interior
periodic square filling, original-atlas PL representative, index-zero
regluing, and unchanged rigidity predicate remain open.

# Revision 90 (2026-09-26): package the two-sided boundary matching

`exists_boundary_match_bijection` packages the forward and reverse unique
boundary matches as a genuine bijection between the two rectangle frontiers,
with the ambient carrier equality retained pointwise.  This is the callable
transition object for the copied-sheet quotient; it uses the interior
no-cross-fiber theorem only to localize the transition to the rim and does
not assert an interior square filling or surface classification.  The focused
build passes 2,586 jobs; the recursive audit reaches 12,252 declarations with
no direct admissions and only `propext`, `Classical.choice`, and `Quot.sound`.
The closed periodic square map, original-atlas representative, index-zero
regluing, and unchanged rigidity predicate remain open.

# Revision 91 (2026-09-26): exact two-disk fiber cases

`twoDiskMap_fiber_iff_rim_or_same` combines same-sheet injectivity with the
cross-sheet boundary localization into an exact four-case fiber theorem for
the complementary rectangle map.  Same-sheet fibers are literal equality;
cross-sheet fibers are exactly rim points carrying the same ambient value.
The focused build passes 2,586 jobs and the recursive audit reaches 12,254
declarations with no direct admissions, using only `propext`,
`Classical.choice`, and `Quot.sound`.  The theorem is the copied-sheet fiber
input; the closed periodic square filling, original-atlas representative,
index-zero regluing, and unchanged rigidity predicate remain open.

# Revision 92 (2026-09-26): copied-sheet quotient homeomorphism

`OriginalTorusTwoDiskQuotient.lean` constructs the compact disjoint-union
ambient map for the two complementary rectangle charts and proves it is a
quotient map.  The `twoDiskFiber` setoid quotient has the same fibers by the
exact rim-or-same theorem, so the existing quotient-fiber utility produces a
homeomorphism from that copied-sheet quotient onto the covered carrier, with
the factorization retained pointwise.  Its recursive audit reaches 12,413
declarations with no direct admissions and only `propext`, `Classical.choice`,
and `Quot.sound`; the focused build passes 2,588 jobs.  This is still a
two-disk quotient: the closed periodic square filling, original-atlas PL
representative, index-zero regluing, and unchanged rigidity predicate remain
open.

# Revision 93 (2026-09-26): quotient-map gate for the copied sheets

The new `OriginalTorusTwoDiskQuotient` module proves continuity and the
compact-to-Hausdorff quotient property of the two-chart ambient map, defines
the `twoDiskFiber` setoid quotient, and obtains its homeomorphism to the
covered carrier by identical fibers.  The focused quotient build passes
2,588 jobs; its recursive audit reaches 12,413 declarations with no direct
admissions and only `propext`, `Classical.choice`, and `Quot.sound`.  The full
workspace gate passes all 12 frozen contracts and 26,474 jobs.  The actual
closed periodic square filling, original-atlas PL representative, index-zero
regluing, and unchanged rigidity predicate remain open.

# Revision 94 (2026-09-26): consume the exact rim fiber theorem in the quotient

The quotient proof now uses `twoDiskMap_fiber_iff_rim_or_same` in all four
sheet cases.  Cross-sheet quotient fibers therefore pass through the checked
frontier localization and boundary inventory, while same-sheet fibers remain
chart injectivity.  The focused quotient build passes 2,588 jobs; the
recursive audit reaches 12,957 declarations with no direct admissions and
only `propext`, `Classical.choice`, and `Quot.sound`.  The closed periodic
square filling, original-atlas PL representative, index-zero regluing, and
unchanged rigidity predicate remain open.
# Revision 95 (2026-09-26): finite PL representatives on the copied sheets

`OriginalTorusTwoDiskQuotient.lean` now proves
`exists_twoDiskMap_ambient_finite_piecewise_affine`.  Given the actual finite
PL rectangle charts on the complementary sheets, it extracts two ambient
finite-piecewise-affine maps and proves their pointwise agreement with the
two-sheet `twoDiskMap`, including the subtype coercions into the covered
carrier.  The quotient's exact rim-or-same fiber theorem remains the fiber
control used by the homeomorphism construction; no interior filling or torus
classification is assumed.

The focused quotient build passes 2,588 jobs.  Its recursive audit reaches
14,632 declarations with no direct admissions and only `propext`,
`Classical.choice`, and `Quot.sound`.  The closed periodic square filling,
single original-atlas square representative, index-zero regluing, and the
unchanged `HasHamiltonRelativeTorusRigidity` predicate remain open.

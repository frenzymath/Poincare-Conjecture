# Incompressible torus surface recognition

This revision records the checked progress on the corrected original-atlas
dual-tree cut.  It does not close the source square-map obligation.

## Published artifacts

- `0acd9e7d50b8559a49de2f8d21cfa0865b395492` records the copied-carrier
  reconstruction and the obstruction showing that the raw residual trace
  cannot itself be a periodic square boundary map.
- `c9ed2ac82fe0ead8229be0f4093d46fab5cb5995` defines the finite copied-side
  gluing relation, its setoid, fiber equality, and closedness.
- `985c174d2` defines finite selected copied-triangle carriers.  The carrier
  is compact, has a finite triangulation with affine original projection, and
  projects exactly to the selected original triangles.
- `bdcaf6e50` exposes `primalTreeContraction_subsingleton`, making the
  connected primal-tree quotient's single vertex class explicit and adding it
  to the residual-edge recursive audit.
- The residual finite-PL module now proves `residualEdgePath_image` and
  `residualEdgePath_isFinitePLBallPair`, and exports the corresponding
  `residualBoundarySourcePath_isFinitePLBallPair` for each of the four
  residual side labels.  These are exact segment images with the oriented
  endpoint pair, not a conditional square-map interface.
- `OriginalTriangleCopiedEdges.lean` now gives each separately labelled
  triangle sheet an actual affine copied-edge path.  Its image is exactly the
  copied ambient edge carrier, its first-coordinate image is exactly the
  original edge convex hull, and the copied side has a finite PL interval
  certificate.  These declarations are included in the residual recursive
  audit.
- `OriginalTriangleOwnerIntervals.lean` exposes the actual dual-tree owner
  triangle for every complementary graph edge, using the exact original
  coface edge label.  For an owner witness, the copied interval is proved to
  lie in that labelled triangle sheet and its two endpoint contacts are
  recorded exactly.  This is the local owner/attachment input for the four
  residual sides; it does not yet identify the sheet interval with the global
  leaf-cut rim.
- `OriginalTorusLeafCutDisk.lean` now also exports the incidence embedding
  whose range is the returned selected vertex set, together with the theorem
  that every triangle label maps into that selected set.  The geometric disk
  producer remains unchanged for existing consumers, while the new companion
  supplies the owner-membership data required by the rim attachment step.
- The same module now proves the generic selected/unselected dual-block
  contact inclusion into `vertexDualRim`.  Thus an edge joining a selected
  triangle label to its complementary unselected edge label has an actual
  interval carrier inside the disk rim, with no regular-neighborhood
  replacement.
- The companion disk witness now exposes the factorization through the full
  complementary-incidence embedding.  `complementary_edge_vertex_not_selected`
  proves that a residual complementary edge outside `D` maps to a genuinely
  unselected edge-centroid vertex.  Together with the contact inclusion this
  supplies the exact residual rim-side carrier needed for the four arcs.
- Commit `2eaab8462` adds `complementary_edge_owner_selected_unselected`: for
  every residual complementary edge it returns an actual triangle owner, the
  exact owner-edge inclusion, and the selected/unselected range facts.  This is
  the concrete input for choosing the four copied side intervals.
- The same owner module now exports `complementary_edge_owner_copied_data`,
  converting that abstract witness to an actual `Triangle K` and geometric
  edge subtype.  It returns the copied affine interval, its exact sheet
  inclusion, and both endpoint contacts, so the four side choices retain their
  original-atlas formulas.
- Commit `4b4a5987999029778bd845edfe666006174dd29c` adds the paired coface
  producer `exists_complementary_triangle_owner_pair` and
  `complementary_edge_owner_copied_pair_data`.  For each residual edge this
  returns the two distinct actual owner sheets, the common geometric edge, two
  finite PL copied intervals, exact endpoint contacts, and the unselected
  complementary edge-centroid witness.  The Boolean side copies therefore
  have separate geometric interval data before the disk rim is assembled.
- Commit `802375e2c665fb98b9f02d9b910fe0f657bb83b4` strengthens that pair
  package with an `IsFinitePLBallPair` certificate for each copied interval,
  retaining the exact endpoint image set needed by a closed-arc attachment.
- Commit `88b80734c` adds `OriginalTorusResidualSideArcs.lean`, which assembles the two residual labels
  and their two Boolean copies as four indexed closed side traces.  Each trace
  has an exact original edge-segment image, explicit endpoint evaluations, and
  an `IsFinitePLBallPair` certificate.  The separate audit reaches 29,101
  declarations with standard axioms only and no direct admissions.
- `OriginalTorusCopiedArcSeparation.lean` proves that the two distinct owner
  intervals for each residual edge are disjoint in the separated carrier under
  the injective original triangle labelling.  Its recursive audit reaches
  13,102 declarations with standard axioms only and no direct admissions.
- The ambient-type cleanup removes an accidental `[Fintype E]` requirement
  from the owner and copied-arc separation declarations, so they apply to the
  intended finite-dimensional ambient spaces without making the ambient point
  type finite.
- `OriginalTorusOwnerDualIntervals.lean` now returns, for every residual
  complementary edge, the exact owner edge and finite PL original dual
  interval, together with the selected owner and unselected residual
  incidence.  It also proves that the corresponding barycentric dual block
  lies in the actual leaf-cut rim.  Its recursive audit passes with standard
  axioms only and no direct admissions.
- `OriginalTorusLeafRimIntervals.lean` packages the selected/unselected rim
  interval itself: the two coface-centroid endpoints, finite PL ball-pair
  boundary, exact contact with all other vertex blocks, and inclusion in the
  leaf-cut rim.  Its recursive audit reaches 29,211 declarations with
  standard axioms only and no direct admissions.
- The same module now transports each complementary owner through the actual
  barycentric-subdivision adjacency.  `residual_owner_interval_on_leaf_rim`
  derives the subdivision face, endpoint cofaces, finite PL interval, contact
  equation, and leaf-rim inclusion from the original purity and coface data;
  it does not assume a rim interval as input.
- `OriginalTorusResidualOwnerArcs.lean` consumes both distinct residual labels
  and constructs both owner intervals, with their two orientation copies, from
  the actual owner witnesses.  Its recursive audit reaches 29,542
  declarations with standard axioms only and no direct admissions.
- `OriginalTorusResidualEndpointContraction.lean` specializes the primal-tree
  quotient to each indexed residual side, proving equality for arbitrary
  original edge endpoints and for the two copied orientations.  Its audit
  reaches 4,519 declarations with standard axioms only and no direct
  admissions.
- `OriginalTorusOwnerIntervalPaths.lean` converts each owner interval into an
  actual finite simplicial ambient path.  The paths retain injective vertices,
  exact coface-centroid endpoints, complete dual-block carriers, and the
  original finite PL incidence certificates for both residual labels and both
  orientation copies.  Its recursive audit reaches 30,441 declarations with
  standard axioms only and no direct admissions.
- `OriginalTorusFinitePLReturnPaths.lean` extracts the ambient return primitive
  from any finite PL ball pair: the convex model yields a finite
  piecewise-affine path between arbitrary carrier points, with both endpoint
  values and carrier containment proved in the original ambient space.  Its
  recursive audit reaches 28,862 declarations with standard axioms only and no
  direct admissions.
- `OriginalTorusOwnerReturnTransport.lean` instantiates that primitive on the
  actual barycentric leaf disk.  For both residual labels and both copied
  orientations, each pair of owner coface centroids now has an ambient finite
  PL path through the complete leaf-disk carrier.  Its recursive audit reaches
  29,587 declarations with standard axioms only and no direct admissions.
- `OriginalTorusPrimalTreeReturnPaths.lean` now realizes the selected primal
  tree as an actual walk in the original edge graph.  For every residual edge,
  the geometric edge segment followed by that walk is a literal closed path in
  the original carrier; reversing it supplies the opposite copied orientation.
  Its recursive audit reaches 13,617 declarations with standard axioms only
  and no direct admissions.
- `OriginalTorusClosedOwnerArcs.lean` now concatenates each actual owner rim
  interval with the reversed finite PL return path, producing a literal closed
  finite PL arc in the original leaf-disk carrier.  Its indexed companion
  `exists_four_closed_residual_owner_arcs` supplies all two residual labels and
  both Boolean copies from the actual dual-tree owner witnesses.  The theorem
  `exists_rooted_four_closed_owner_arcs` then transports all four loops through
  the actual convex disk carrier to one common basepoint, preserving finite
  piecewise-affinity and exact carrier containment.  The focused recursive audit
  reaches 29,811 declarations with standard axioms only and no direct
  admissions.
- `OriginalTorusMarkedRectangle.lean` adds the first concrete planar boundary
  operation: `exists_split_interval_at` cuts an actual finite PL boundary
  interval at an interior marked point into two finite PL ball pairs, with
  exact endpoint pairs, union equal to the original interval, and singleton
  intersection.  This is a verified input for the four-side rectangle chart;
  it does not package a conditional square map.  The same module now proves
  `exists_marked_boundary_rectangle`: two complementary actual rim arcs are
  split at interior PL marks into four cyclic arcs with exact singleton corner
  contacts and opposite-side disjointness, then extended by the existing
  four-arc rectangle theorem.  The owner wrapper instantiates its two marks
  from the actual distinct dual coface centroids and the selected rim.
- `OriginalTorusTwoDiskCharts.lean` packages the two-disk gluing primitive
  needed when a complementary disk pair is available: it produces a finite PL
  rectangle chart on each half with the same four side images.  The generic
  package is not used as a torus classification or as a replacement for the
  corrected dual-tree carrier.
- The same module now defines the disjoint-union map `twoDiskMap` onto the
  whole covered carrier.  Its `twoDiskFiber` relation is an equivalence, and
  `twoDiskMap_fiber_iff` plus `twoDiskMap_surjective` give exact fibers and
  surjectivity before any standard-square reparameterization.  The expanded
  recursive audit reaches 30,096 declarations with standard axioms only and
  no direct admissions.

`OriginalTrianglePartialQuotient.lean` now exposes the corrected partial
quotient of separated triangle sheets.  `partialProjection` is defined by
quotient lifting the original-coordinate projection; it is surjective and
continuous, and `partialProjection_isQuotientMap` supplies the compact finite
carrier quotient-map result.  `partialQuotient_mk_eq_iff` records exact
pointwise quotient fibers, while `partialProjection_fiber_coordinate` keeps
the original-coordinate invariant explicit.  Its recursive audit reaches
14,395 declarations with standard axioms only and no direct admissions.

The selected-carrier recursive audit reports standard axioms only
(`propext`, `Classical.choice`, and `Quot.sound`).

## Verification

The focused selected-carrier, primal-contraction, copied-edge, owner-interval,
residual finite-PL, residual-side-arc, copied-arc-separation, owner-dual,
leaf-rim/owner-arc/endpoint-contraction, owner-path, ambient-return-path,
owner-return-transport, primal-tree-return-path, and closed-owner-arc builds and
audits pass.  The closed-owner-arc audit reaches 29,811 declarations with
standard axioms only and no direct admissions.
The residual side-arc audit reaches 29,101 declarations, copied-arc separation
13,102, the owner/rim audit 29,502, the two-label owner-arc audit 29,542, and
the owner-path audit 30,441, the ambient-return-path audit 28,862, and the
owner-return-transport audit 29,587, and the primal-tree-return-path audit
13,617, all with standard axioms only and no direct admissions.  The focused
	build passes 3,488 jobs.  The marked-interval and marked-rectangle audit
	reaches 32,529 reachable declarations with standard axioms only and no direct
    admissions.  The two-disk chart and quotient-map audit reaches 30,096 declarations with
	standard axioms only and no direct admissions.  The
integrated `PoincareLib` build passes 26,450
jobs, and `make check` verifies all 12 frozen contracts successfully.

## Remaining obligation

The four closed owner arcs are indexed and rooted at one actual carrier point.
The copied-sheet partial quotient now has an audited, surjective quotient map
to the original carrier, but its residual side relation is still intentionally
left open.  The remaining construction is to attach the four residual sides
to this partial quotient, identify the resulting carrier quotient with the
standard `p = 64` square quotient, retain the original finite PL representative,
and invoke `PhaseCoveringInstallation`.
No classification or parametrization supplier was added.

# Revision 43 (2026-09-26): concrete four-side boundary map

`OriginalTorusSquareBoundaryMap.lean` now turns the audited rooted owner loops
into a scaled `p`-square boundary map.  It supplies one common endpoint for all
four closed side copies, pointwise equality of opposite copies, containment in
the actual leaf-disk carrier, and a finite piecewise-affine certificate on
each closed side.  The focused recursive audit reaches 29,127 declarations
with standard axioms only and no direct admissions.  This is only the boundary
layer: it does not claim a full-carrier extension or a `SourceSquareMap`.

The exact periodic `p = 64` square map and its full-carrier extension remain the
next obligation.  The partial copied-sheet quotient still needs its four
residual side attachments identified with the standard square quotient before
`PhaseCoveringInstallation` can consume it.  No classification or
parametrization supplier was added.

# Revision 44 (2026-09-26): retain owner traces in the boundary layer

`OriginalTorusClosedOwnerArcs.lean` now exposes
`exists_closed_owner_arc_with_trace`.  For each selected residual owner it
returns the actual two coface triangles, the finite PL rim path in the dual
block, the finite PL return path through the leaf-cut carrier, and their closed
concatenation with all four endpoint equations.  This removes the previous
loss of the rim trace at loop formation.

`OriginalTorusSquareBoundaryMap.lean` now retains the source loop formula for
each scaled side in addition to its finite PL certificate, common endpoint,
and opposite-side equality.  Its audit was tightened to inspect every
reachable declaration, reject missing declarations and `sorry`, and reject
nonstandard axioms; it passes at 29,127 reachable declarations with no direct
admissions.  The focused build and integrated `make check` pass (3,516 and
26,463 jobs respectively; all 12 frozen contracts verified).

## Progress

- [x] Preserve the selected owner-rim interval and return path as separate
  finite PL formulas with exact endpoint data.
- [x] Preserve each scaled boundary side's source-loop formula and run a
  strict recursive admission audit.

## Issues

- [ ] The four rooted loops still lie in the leaf-cut disk; this does not yet
  prove the essential side-pair quotient or identify the full carrier.

## Remaining

- [ ] Prove the primal-tree contraction as a geometric quotient of the copied
  disk, attach the four residual side traces, and construct the full `p = 64`
  `SourceSquareMap` with exact periodic fibers.
- [ ] Install that map through the existing phase-covering consumer.

## Why did I stop?

The requested full-carrier quotient is not yet proved.  The new artifacts are
checked inputs for that construction and do not justify claiming the mission
criterion.

## Next

Use `exists_closed_owner_arc_with_trace` to build the four marked rim arcs,
then prove their copied-sheet attachment relation before defining the total
square map.

# Revision 45 (2026-09-26): actual tube-end four-side chart

`OriginalTorusActualComplementDiskChart.lean` consumes the concrete
`FourSidedProperComplementDisk` from the tube construction.  It applies the
existing finite PL four-side extension to the actual outer/inner rim and arm
intervals, preserving the carrier image, injectivity, frontier image, all four
side images, and the four physical endpoint values.  The strict recursive audit
reaches 30,113 declarations with standard axioms only and no direct admissions.

## Progress

- [x] Turn the parent’s actual complementary-disk certificate into an original
  finite PL four-side chart with exact tube-end contacts.
- [x] Build and recursively audit the chart with no direct admissions.

## Issues

- [ ] The chart is an actual disk chart; it does not yet identify the copied
  residual sides with the full carrier quotient.

## Remaining

- [ ] Match the four residual side traces to the copied disk/tube-end charts,
  prove the geometric primal-tree quotient, and construct the full `p = 64`
  `SourceSquareMap` with exact periodic fibers.
- [ ] Install that map through the existing phase-covering consumer.

## Why did I stop?

- [x] The full-carrier quotient is still an open proof obligation; this chart is
  a concrete integration input and does not justify claiming the mission.

## Next

- [ ] Use the actual four-side chart together with the retained owner/rim traces
  to prove the side attachments before defining the total square map.

# Revision 46 (2026-09-26): finite PL marked-side transitions

`OriginalTorusMarkedSideTransitions.lean` now restricts each actual
finite-PL complementary-disk rectangle chart to a marked rim arc.  It
constructs the interval homeomorphisms directly, proves their finite PL
certificates, retains their pointwise ambient values, and supplies the finite
PL transition `e₀.trans e₁.symm` between the two disk parameters.  The strict
recursive audit reaches 28,901 declarations with only the standard axioms
`propext`, `Classical.choice`, and `Quot.sound`, with no direct admissions.

## Progress

- [x] Construct the actual finite PL interval parameters on a marked rim side.
- [x] Construct and audit the finite PL transition between the two disk-side parameters.

## Issues

- [ ] The transition only reparameterizes a common marked arc; it does not
  prove the two-dimensional primal-tree contraction or fill the periodic square.

## Remaining

- [ ] Apply the transition on all four marked arcs, prove the copied-sheet
  collision relation, and construct the full `p = 64` `SourceSquareMap` with
  exact periodic fibers.
- [ ] Install that map through the existing phase-covering consumer.

## Why did I stop?

- [x] The full-carrier quotient and its exact collision relation remain open;
  the new transition is a concrete side-matching input and not a substitute
  for that construction.

## Next

- [ ] Instantiate the transition on the parent’s tube-end charts and use the
  resulting pointwise side matches to assemble the four-sided periodic square.

# Revision 47 (2026-09-26): four-side endpoint chart package

`OriginalTorusMarkedRectangleSideCharts.lean` packages the actual marked
rectangle with four endpoint-parametrized finite PL interval homeomorphisms,
all eight endpoint equations, the complete boundary decomposition, and the
four whole-side membership equivalences for the finite PL square chart.  The
strict recursive audit reaches 32,520 declarations with standard axioms only
and no direct admissions.

## Progress

- [x] Construct the four finite PL side charts from the actual marked arcs.
- [x] Retain exact endpoint contacts and the square chart’s side equations.

## Issues

- [ ] This is still planar boundary data; it does not identify copied sheets
  after primal-tree contraction.

## Remaining

- [ ] Instantiate all four side charts on the selected tube/owner data and
  prove the copied-sheet collision and geometric attachment equations.
- [ ] Construct the total `p = 64` `SourceSquareMap` with exact periodic fibers.
- [ ] Install the resulting map through the existing phase-covering consumer.

## Why did I stop?

- [x] The parent collision certificate still needs to be matched to these
  concrete side carriers before the quotient map can be defined.

## Next

- [ ] Use the side-chart record to state and prove the first nonconditional
  copied-sheet attachment lemma, preserving pointwise values and endpoints.

# Revision 48 (2026-09-26): endpoint-controlled embedded return arcs

`OriginalTorusEmbeddedReturnArc.lean` pulls the affine chord in the convex
finite-PL ball model back through the original carrier chart.  It proves an
actual finite-piecewise-affine interval with the prescribed endpoints,
carrier containment, and `InjOn`; `OriginalTorusClosedOwnerArcs.lean` now
instantiates this for both the selected rim interval and its disk return
chord.  The focused source and recursive audits pass with only the three
standard axioms and no direct admissions; the full gate passes all 26,465
Lean jobs and all 12 frozen contracts.

## Progress

- [x] Replace arbitrary owner return paths by endpoint-controlled embedded
  finite PL arcs in the original carrier.
- [x] Publish the source theorem and its recursive admission audit.

## Issues

- [ ] Individual arc injectivity does not yet prove pairwise disjoint proper
  cuts or the copied-sheet attachment relation.

## Remaining

- [ ] Construct the pairwise-disjoint proper cuts of the copied leaf disk,
  extend them to the marked rectangle, and define the full `p = 64`
  `SourceSquareMap` with exact periodic fibers.
- [ ] Install that map through the existing phase-covering consumer.

## Why did I stop?

- [x] The full periodic filling and its no-extra-fiber proof remain open;
  this publication is a concrete cut input, not the recognition theorem.

## Next

- [ ] Use the embedded chords with the copied-sheet owner data to prove the
  first pairwise-disjoint proper cut and its exact rim attachments.

# Revision 49: faithful copied-triangle gluing

## Progress

- [x] `Surfaces/Cuts/` proves Hausdorff pointwise quotients, original-edge and two-stage reconstruction, retained-edge separation, and fresh leaf disk/map attachment with exact images and rims.
- [x] The focused build passes 2,786 jobs, the recursive audit checks 33,116 declarations with standard axioms and no admissions, and `make check` passes 26,474 jobs and 12 frozen contracts.
- [x] Execution: default xhigh was retained for independent quotient topology and geometric reconstruction; both native workers supplied checked proofs without escalation.

## Issues

- [x] Fixed-point contact chains prevent the overidentifications permitted by label-only reachability; the embedded dual-tree neighborhood remains distinct from the copied polygon.

## Remaining

- [ ] Construct the finite dual-tree induction and primal contraction, then the periodic square map and original-atlas phase installation.

## Why did I stop?

- [x] Checkpoint only; continuing the source construction.

## Next

- [ ] Assemble the fresh leaf attachments into a disk realizing the selected-contact quotient with every retained side and original map intact.

# Revisions 50-51: finite tree disk and original primal cuts

## Progress

- [x] Published `f4319b9ff73593ff87b239b9f3acb46e37d5b008`: finite triangle-tree induction, faithful selected quotient, exact retained rim, and no interior identifications; Roadmap PR 824 merged.
- [x] Constructed the actual primal disk, four prescribed original sectors, residual bridges and circles, surface block cover, and four-sided residual bands. The combined audit checks 36,039 declarations without admissions; `make check` passes 26,503 jobs and 12 contracts.
- [x] Execution: default xhigh retained for independent native geometric proofs; numerical producer queued as `incompressible-surface-euler-zero`, session `session_bc92ae55f7544ce5a9e6a116cc4f0d35`, pinned to PR 825.

## Issues

- [ ] Existing recognition candidates still assume residual count two.

## Remaining

- [ ] Derive that count, finish the copied cut disk and exact periodic square, then install PhaseCovering.

## Why did I stop?

- [x] Checkpoint only; continuing construction and integration.

## Next

- [ ] Glue separated residual halfbands and primal sectors, preserving exact source fibers and side parameters.

# Revision 52: entire cut disk and exact source fibers

## Progress

- [x] [Checked source](/api/v2/forge/web/poincare-conjecture/workspace-poincare-conjecture/commit/5b2b7ad15dd9edb9d4bbc37d129004f544e75a6a) constructs the entire finite PL cut disk from the original Euler-zero surface, with exact carrier image, rim saturation, four center fibers, paired spoke and bridge fibers, and singleton interior fibers.
- [x] The original frontier component, coherent signs, and based group transport are constructed; the focused audit checks 59,834 declarations without admissions, and `make check` passes 27,203 jobs and 12 frozen contracts.
- [x] Execution: default xhigh retained for independent native geometric proofs; the numerical owner continues the actual group-to-Euler argument.

## Issues

- [x] The earlier numerical certificate does not discharge Euler zero; its replacement must prove the rank bridge from the original hypotheses.

## Remaining

- [ ] Prove Euler zero and cyclic orientation compatibility, then construct the exact periodic square map and consume PhaseCovering.

## Why did I stop?

- [x] Checkpoint only; proof work continues in this session.

## Next

- [ ] Assemble the constructed long rim arcs with the original orientation into opposite side pairings.

# Compact Cores Revision 4: Bounded Integration Corrections

Main decision: accepted at the digest in `compact-cores-v4.json`. The
bounded-review history below records how the finite findings arose and
were resolved. Main completed the continuous whole-chapter read and
reread every replacement. The same-P Dehn export, relative interior and
whole-frontier identities match the completed relative-rigidity consumer.
Its zero-index puncture argument uses the universal protected-set Wall
quantifier, not an additional field. The sphere bound now refers to the
normalized system and uses actual global exception labels. No unresolved
internal finding remains. Final integrated coverage and rendering are
separate gates; no Lean build, audit or comparator was run.

Status: the initial four bounded prose corrections and the follow-up
counting/separation corrections below are implemented. Main has completed
its whole-chapter read; rereading the latest changes and the integration
decision remain pending. This note does not
mark the chapter accepted and does not change its JSON status. No Lean
files, contracts, references, or checkers were edited. No builds, audits,
or comparator runs were performed for this bounded task.

Scope: `blueprint-publication/drafts/compact-cores.tex`, specifically
`cc-local-pl-depth`, `cc-frontier-surface-depth`, and the marked-side
export to Hamilton lower handles. The separately owned zero-index
relative-rigidity producer was not reviewed or modified.

All producer paths below are relative to
`PoincareLib/Topology/Manifold/Smoothing/`.

## Disk Product for Compression

The former paragraph used the frontier-normal bicollar values
`h(d(Q), +/-epsilon)` as compression rims. The bicollar's own equations
place these curves off the frontier on opposite sides. The replacement
now uses the actual disk product, whose lateral annulus lies in the
frontier and whose two end disks replace its open strip. Embeddedness
and the frontier formula come from that product, not just from
embeddedness of the central disk and avoidance of the protected set.

Exact producers:

- `Rigidity/Disks/OriginalDiskProduct.lean:28`, `OriginalDiskProduct`:
  whole closed product embedding, central disk equation, and exact
  frontier preimage.
- `CompactCore/Surgery/ProtectedInteriorCompression.lean:27`,
  `PLDomain.exists_protected_interior_compression_with_collars`:
  protected product, cut carrier, inserted end disks, both frontier
  equations, and retained relative interiors.
- `CompactCore/Surgery/ExteriorDiskAttachment.lean:23`,
  `OriginalDiskProduct.exterior_attachment_geometry`: the corresponding
  exterior union and frontier formula.
- `CompactCore/Surgery/ProtectedCompressionGenus.lean:26`,
  `PLDomain.exists_protected_compression_genus_decrease`: select the
  literal disk side and retain the protected component with strict
  complexity decrease.

## One-Sided Filling and Orientation

Finite polygon descent has two outputs. It may find an essential
innermost circle, or it may remove every frontier preimage circle. The
draft now treats the latter: the residual disk lies on the interior
side, and the retained collar and approximation homotopies are pasted
as two radial annuli to restore the original essential rim pointwise.
An essential circle selected by descent need not belong to the initial
frontier component; essentiality is retained in the whole frontier.

Exact producers:

- `CompactCore/Disks/FrontierPolygonDescent.lean:23`,
  `PLDomain.exists_essential_filling_or_frontier_avoidance`: the two
  exhaustive descent outputs.
- `CompactCore/Disks/EmptyFrontierPolygonFilling.lean:42`,
  `exists_radial_two_annulus_filling`, and `:152`,
  `PLDomain.exists_proper_filling_of_empty_frontier_preimage`: same-side
  connectedness and restoration of the original complete rim.
- `CompactCore/Disks/EssentialProtectedFilling.lean:29`,
  `PLDomain.exists_essential_proper_filling_of_protected_filling`:
  assembly of both alternatives.
- `CompactCore/Disks/ProtectedCutFilling.lean:25`,
  `PLDomain.exists_protected_cut_filling`: lift the proper filling and
  essential rim to the literal closed cut side in the same lifted atlas.

The orientation paragraph now identifies the signs as those of the
ambient orientation double cover restricted to the frontier, with its
fixed outward coorientation. This explains why nullhomotopies in the
ambient protected region trivialize their monodromy even when they leave
the surface. Exact producers:

- `CompactCore/Orientation/CompatibleChartLabels.lean:48`,
  `exists_frontier_component_compatible_chart_labels`.
- `CompactCore/Orientation/Finite/OriginalComponentSigns.lean:22`,
  `exists_original_frontier_component_all_edge_signs`.

## Marked-Side Export

The lower-handle paragraph now states the enclosing-region output for
the same annulus or simultaneous disk pair, including the full attaching
patch, relative core interior, and strict transverse radius bound. It
then explains why that same region is the marked ball supplied to prime
replacement: one retained original chart contains it, the marked zero
gives an ambient interior point, and original-chart PL Alexander
recognition supplies its ball parametrization with the same frontier.

Exact producers:

- `Triangulation/Handles/HamiltonProtectedGeometricInputs.lean:63`,
  `HamiltonDehnEnclosingRegion`: exact enclosing-side fields.
- `Triangulation/Disks/HamiltonDehnProtectedBall.lean:31`,
  `HamiltonDehnEnclosingRegion.interior_nonempty`, and `:65`,
  `HamiltonDehnEnclosingRegion.markedProtectedBall`: the literal marked
  zero and conversion of the same region to the prime input.
- `Triangulation/Handles/HamiltonOriginalChartBall.lean:33`,
  `ChartwisePLSphere.ball_of_original_chart`: original-chart region
  recognition and return of the entire PL ball parametrization.
- `Triangulation/Handles/HamiltonIndexOneHandleStraightening.lean:82`
  and `HamiltonIndexTwoHandleStraightening.lean:78`: actual uses of
  `region.markedProtectedBall` before protected replacement.
- `Rigidity/Applications/HamiltonLowerHandles.lean:27`,
  `lowerCases_of_wall_dehn_prime`: fixed lattices, punctured/open-subspace
  Wall quantifiers, and universal chart-set replacement inputs.

## Remaining Review

At the end of the initial pass, main's whole-chapter mathematical and
readability review remained pending; the follow-up below records its
completion and the resulting corrections. Predecessor reconciliation,
acceptance, and authorized publication checks remain with main.
The existing half-space/frontier equations,
copied-primal-tree correction, two-foot sphere description, marked-ball
positions, relative identity maps, and lower-handle quantifiers yielded
no additional finite finding in this bounded pass. This is not an audit
of all their lower dependencies or of the prime index-case proofs.

## Follow-Up: Uniform Count and Two New Ports

Main's subsequent whole-chapter read identified an unrelated surface
tree-cotree calculation in the uniform three-dimensional sphere bound.
The bounded follow-up replaces that paragraph with the actual original-face
exception count and global component labels. The correct copied-primal-tree
paragraph in the frontier surface argument is retained.

The draft now defines `v` and `z` for the normalized admissible system.
The source preserves the sphere index set and hence `s`; it does not use
preservation of the original component counts through every surgery.
Finite normalization decreases total tetrahedral boundary excess and at
zero supplies actual disk sections and ball partitions.

For each original triangle, `m` normal arcs in `c <= 3` nonempty corner
families give `m-c` successor rectangles among `m+1` complement regions.
Thus at most four exceptional regions remain. Each connected region maps
to one global raw complement component. Components meeting the old boundary
are the image of its vertex labels. Outside the union of these two finite
sets, compatible prism coordinates form an interval bundle. The original
collars identify endpoint components with spheres. A sufficiently large
positive-width trim contains the whole compact cut component. Exchanging
endpoint components would give a spherical product and a forbidden
punctured-sphere model; the remaining invariant endpoint component has a
connected double cover and a nonzero mod-two first-homology class. Actual
coordinate and collar transport carries this class to the cut component.
An injective map from thick-cut components to raw complement components
then puts every zero-homology component into the finite label union.

Exact source scope (all under `PrimeReduction/` unless stated otherwise):

- `Tetrahedra/Normalization/OriginalRelativeNoL3FiniteNormalization.lean:22`,
  `HasNoPuncturedSphereComponents.exists_original_finite_relative_noL3_normalization`:
  full finite induction read, including the retained index type and zero
  excess disk/ball output.
- `Counting/PositionedRelativeSphereBound.lean:19` and
  `Counting/NormalizedRelativeSphereBound.lean:18`: full assembly read;
  the original-model bound is applied after the replacements.
- `Tetrahedra/Prisms/OriginalFaceEdgeGapFamily.lean:17`,
  `exists_original_face_edge_gap_family`: full successor rectangle and
  corner-family count interface and proof read.
- `Tetrahedra/Prisms/RegularFaceRegionLabels.lean:17,99`,
  `exists_exceptions_of_actual_rectangle_family` and
  `exists_original_face_rectangle_exceptions`: full actual-component
  count and at-most-four exception proof read.
- `Counting/OriginalExceptionalComponents.lean:30`,
  `exists_original_exceptional_component_bound`, and
  `Counting/OriginalMarkedBoundaryExceptions.lean:23`,
  `originalMarkedBoundaryComponents_finite_ncard`: full original-face and
  old-boundary label maps and cardinal bounds read.
- `Tetrahedra/Prisms/Bundles/OriginalNoL3ComponentHomology.lean:27`,
  `original_nonexceptional_noL3_component_homology_retract`: full endpoint,
  trim, interior containment, and homology transport assembly read.
- `Tetrahedra/Prisms/Bundles/NoL3EndpointComponent.lean:22,66`,
  `endpoint_component_invariant_of_noL3` and
  `endpoint_component_homology_retract_of_noL3`: full exchanged/invariant
  endpoint argument read. This pass did not reopen every lower bundle or
  punctured-sphere recognition construction.
- `Counting/OriginalNonexceptionalCutHomology.lean:21`,
  `OriginalTetrahedralCutFamily.exists_nonexceptional_cut_homology`, and
  `Counting/OriginalZeroHomologyExceptions.lean:11`,
  `ncard_zero_cut_components_le_original_exceptions`: full union of label
  sets, nonzero homology outside it, and zero-homology injection read.

The two-new-port explanation also incorrectly invoked the circle section
and retraction used earlier to prove that the empty cut is admissible.
That earlier argument is retained. The two-port paragraph now uses the
actual bounded-region separation mechanism: lift the inserted sphere,
exclude nesting of nonzero translates by a linear-functional maximum,
descend the entire closed region injectively, and locate collar endpoint
points on its two opposite sides. A connected cut component avoiding the
middle sphere cannot contain both ports.

Exact source scope:

- `Handles/BoundedSphereRegion.lean:58`,
  `ChartwisePLSphere.exists_lattice_bounded_region`: full lift, closure
  injectivity, frontier identities, and handle-containment proof read.
- `Triangulation/Coverings/HamiltonStandardDeckRegions.lean:106,141`
  (relative to the common smoothing prefix),
  `disjoint_closure_translate_of_disjoint_frontier` and
  `injOn_closure_of_injOn_connected_frontier`: full proofs and their
  bounded-region trichotomy and compact-translate helpers read.
- `Handles/SeparatedCollarPorts.lean:20`,
  `OriginalFiniteSphereCollar.not_both_ports_subset_of_lattice`: full
  regular-closed-region and actual collar endpoint argument read.
- `Handles/PrescribedIrreducibleCappedDomain.lean:20`: full assembled
  capped-sphere contradiction read; the two-port exclusion precedes the
  single-new-port ball construction.

The inspected sources supply both claimed inferences; no absent producer
was found in this bounded review. This is not an exhaustive lower-source
audit. Main has completed its whole-chapter read and must reread these
replacement paragraphs before making its integration decision. Acceptance,
JSON status, and publication checks remain outside this edit.

# Relative End-And-Cap Replacement

`Replacement.lean` proves the marked-ball step for complementary **boundary
disks**, including a compact support and an open fixed neighborhood of the
protected set. It does not yet construct the fillings of the actual annular
ends or identify their complementary boundary disks with the model caps.

## Checked Reduction

Let `B` and `L` be ambient diffeomorphisms of three-space, and write `Bball`
and `Lball` for their images of the unit closed ball. Let `g` be a smooth
injective immersion of the plane, and suppose that the images under `g` of
the closed disk of radius `r > 1` lie in both ball boundaries. The closing
disk is the image of the unit closed disk. A closed protected set `C` may
meet either filled ball only in this closing disk.

`exists_supported_boundary_replacement_of_local_inclusion` requires an open
neighborhood `V` of the enlarged closing disk such that
`Lball intersect V` is contained in `Bball`. It constructs an ambient
diffeomorphism taking `Bball` onto `Lball`, and taking the boundary of `Bball`
minus the open closing disk onto the corresponding closed boundary disk of
`Lball`. Its support is compact and disjoint from `C`; it fixes an open
neighborhood of `C` and the entire closed closing disk.

The proof compresses `Lball` into `V` while fixing the enlarged closing disk.
The compressed ball lies inside `Bball`. Marked-ball equivalence and supported
nested replacement give a map from `Bball` to the compressed ball. Undoing
compression gives the required map. Homeomorphisms preserve frontiers, and
injectivity preserves set difference, giving the exact boundary-disk image.
The nested version is `exists_supported_nested_boundary_replacement`.

`Side.lean` removes the need to assume local inclusion when a common exterior
approaches the enlarged closing disk. Near each interior point of the common
disk, the two sphere boundaries coincide. A sufficiently small connected
exterior neighborhood of the source ball avoids the target boundary and meets
the common exterior, so it lies outside the target ball. Taking complements
gives local inclusion. The open union of these neighborhoods covers any
strictly smaller closed disk. The theorem
`exists_supported_boundary_replacement_of_shared_exterior` shrinks the
enlarged radius while retaining radius greater than one and applies the
replacement construction.

These are intermediate consequences of the existing marked-ball theorems,
checked directly against their hypotheses and conclusions. They do not
replace the mission's geometric statement or its original acceptance target.

## Closing-Disk Coordinates

`ClosingDisk.lean` proves `exists_complementary_boundary_parametrization` in
the `Saddle.Caps` namespace. For any regular cap marking on an ambient ball,
it constructs a globally
smooth injective immersion of the plane whose image lies on that ball's
boundary. Its closed unit disk is exactly the complement of the marked open
cap, and deleting its open unit disk leaves exactly the marked closed cap.
Every enlarged parameter disk remains on the ball boundary.

The construction normalizes the cap to a round spherical cap and uses
stereographic coordinates from its center for the complementary disk. It
retains the global chart source and both open and closed disk images, unlike
an unspecified neighborhood chart alone. The local sphere-restriction step
follows `Attachment/DiskComplement.lean` within this mission's file ownership.

This constructs each closing-disk parametrization separately. It does not
prove that independently compressed actual and model balls have a common
closing disk. A ball obtained by compressing a sphere collar near an arbitrary
embedded disk can have a closing disk following that entire disk; it supplies
no planar capping comparison. The product structure must still be used to
construct a shared geometric terminal cap, or to prove the corresponding
relative disk comparison.

## Input Obstructions

`Obstruction.lean` proves three facts relevant to mission revision 1:

- An injective map fixing a set `W` and carrying `E` onto `M` forces
  `E intersect W = M intersect W`. Thus fixing a neighborhood of the band
  requires actual collar agreement, not only a common boundary circle.
- An end described over `Ico z0 z1`, with a cap at `z0 < z1`, contains no
  point at height `z1`. No injective map fixing a nonempty terminal circle
  can carry that end onto a closed cap containing the circle. The closed
  end must include its terminal slice.
- The existing `SphereSurgeryCoreCap` is nonflat: normalized height is
  positive in its open disk and zero at the rim. `CapPreservation` preserves
  this rounded cap; it does not identify it with a horizontal disk.

## Remaining Geometry

`Closing/Ends/CommonPreparation/IndividualReplacement.lean` now constructs a
replacement for each individual original terminal label from the cap leaf's
inputs. It derives the physical rim equality after the common horizontal
preparation, specializes the whole-end normalization to the original model
minimum or maximum, and conjugates back to flattened coordinates. Each result
has compact support, fixes the model band pointwise, and matches the whole
selected cap. The upper specialization uses height reflection and fixes the
terminal lower halfspace.

The quantifiers are `forall i, exists F`, not the leaf's `exists F, forall i`.
The maps need not preserve other caps on the same side. Composing these maps
does not prove the leaf: the first map can destroy the next cap's physical
height description. `Closing/Ends/Family/SlabNormalization.lean` already
normalizes the finite regular annuli simultaneously, including nested circles.
Extending that construction through all same-side cores while retaining
disjoint cap motions is the remaining simultaneous-normalization obligation.
The relative localization theorem requires control of the entire isotopy
trace; disjoint initial and final caps alone do not provide it.

The earlier marked-boundary route also retains the following obligations:

Match a slightly wider regular slab to obtain a collar outside each boundary
of the protected band. Use the actual rounded inserted caps and closed
annular ends. Construct smooth ambient ball fillings with a common enlarged
closing disk, prove local inclusion on the chosen side, and prove that the
band and the other ends meet the fillings only in the closing disk. Identify
the complementary boundary disks exactly with the actual end-and-cap disk
and the appropriate model cap, then apply the checked reduction.

The plane-truncated polynomial body has a corner at its rim, so its
topological ball property alone cannot supply an ambient smooth ball filling.
The concurrent `ModelBall` construction addresses a smooth model-side
filling; the common closing disk and the actual-end filling remain to be
constructed.

## References

Hatcher, *Notes on Basic 3-Manifold Topology* (2014), Section 1.1,
Theorem 1.1 and Lemma 1.3, printed pp. 4-5; archived at
`references/topology/hatcher-basic-3-manifolds/`, bibliography key
`Hatcher3M2014`. The compression and supported replacement proofs are in
`Attachment/Compression/` and `Morse/Surgery/Reverse/Assembly/Replacement/`.

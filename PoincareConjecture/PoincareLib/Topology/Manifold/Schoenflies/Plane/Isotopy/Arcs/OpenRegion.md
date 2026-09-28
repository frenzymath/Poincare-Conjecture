# Ordered circle matching in an open region

## Informal description

Let O be a connected open subset of the plane. Let c and d be ordered pairs
of disjoint smooth embedded circles. Choose ambient smooth disk
parametrizations for their bounded disks, all contained in O. Suppose the
two pairs have the same directed nesting relations. Then there is a smooth
ambient diffeomorphism carrying each c-circle onto its corresponding
d-circle and equal to the identity outside a compact subset of O.

## Informal proof

First match the outer disks in the nested case, then match the inner disks
inside the target outer disk. In the unnested case, first match the first
disks, then match the second disks in O minus the first target disk. This
complement is connected: apply the existing embedded-ball exterior theorem
to the open submanifold O. Both moves have compact support in O, so their
composition does as well. Ambient homeomorphisms preserve disk boundaries.

## Proposed formal statements

```lean
open Set Metric
open scoped Manifold ContDiff
namespace Poincare.Manifold.Schoenflies.PlaneArcs
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev UnitCircle := sphere (0 : E2) 1
theorem exists_supported_circle_pair_matching_in_open_region
    (c d : Fin 2 → UnitCircle → E2)
    (hc : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (c i))
    (hd : ∀ i, _root_.Manifold.IsSmoothEmbedding (𝓡 1) (𝓡 2) ∞ (d i))
    (A B : Fin 2 → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hA : ∀ i, A i '' sphere (0 : E2) 1 = range (c i))
    (hB : ∀ i, B i '' sphere (0 : E2) 1 = range (d i))
    (O : Set E2) (hO : IsOpen O) (hconn : IsConnected O)
    (hAO : ∀ i, A i '' closedBall (0 : E2) 1 ⊆ O)
    (hBO : ∀ i, B i '' closedBall (0 : E2) 1 ⊆ O)
    (hdisjc : Disjoint (range (c 0)) (range (c 1)))
    (hdisjd : Disjoint (range (d 0)) (range (d 1)))
    (hnest : ∀ i j, i ≠ j →
      (Plane.Isotopy.ArcPairs.NestedPair (c i) (c j) ↔
        Plane.Isotopy.ArcPairs.NestedPair (d i) (d j))) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      ∃ D : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x ∉ K, D x = x) ∧ ∀ i, D '' range (c i) = range (d i) := by
  sorry
end Poincare.Manifold.Schoenflies.PlaneArcs
```

## Informal translation

Let S1 and D denote the unit circle and open unit disk in the plane. A circle
u is nested inside v when an ambient smooth diffeomorphism F satisfies
F(S1) = v(S1) and u(S1) is contained in F(D).

Let c_i and d_i, for i = 0, 1, be smooth circle embeddings, and let A_i and
B_i be ambient smooth diffeomorphisms taking S1 onto their respective images.
Let O be open and connected and contain A_i(closed D) and B_i(closed D) for
both indices. Suppose each pair is disjoint and, for each i different from j,
c_i is nested inside c_j exactly when d_i is nested inside d_j. Then there
exist a compact subset K of O and an ambient smooth diffeomorphism H, equal
to the identity outside K, taking c_i(S1) onto d_i(S1) for both indices.

## Alignment review

The independent formal-only translator and prose-only reviewer accepted the
statement on 23 September 2026. The disk-complement and nested-case helpers
are intermediate lemmas checked directly against this argument.

## Application Boundary

The whole terminal saddle circles meet the protected Morse patch. Their
filled disks therefore cannot be contained in its complement. This primitive
applies to circles closed outside that patch only after their construction,
disk containment, and relative endpoint correspondence are proved. It does
not discharge the regular relative matching premise in `NestedSlab.lean`.

`RegionObstruction.not_forall_disk_covers_of_morse_patch` makes the obstruction
precise (the declaration is in the `PlaneArcs` namespace). For a continuous
local parametrization f with height `-x_0^2 + x_1^2`, take x = (u,0) with
u positive and sufficiently small. Its height is -u^2, and its planar image
lies in every prescribed open neighborhood N of the central image when u is
small. If the whole level is covered by two circle boundaries, one boundary
meets N; its filled disk therefore cannot be a subset of `(closure N)^c`.
This remains true after any common height-preserving flattening.

`not_forall_disk_covers_of_flattened_saddle` specializes the argument to an
actual sphere map, its open Morse chart, and a height-preserving ambient
diffeomorphism. The level sets in that theorem are the literal slices of the
flattened sphere image; they are not arbitrary set parameters. The height is
normalized so that the saddle is at zero.

The remaining geometric input is a supported matcher of the exterior arcs
relative to their endpoint germs. The angular interpolation in `Winding.lean`
constructs a continuous homotopy only; embeddedness of its intermediate arcs
is not among its conclusions. Applying interval isotopy extension requires
that additional construction, or a different relative disk argument.

The local differential step for the latter route is proved in
`BoundaryGerm/Differential.lean`: a smooth map fixing an open arc of the unit
circle has identity tangential derivative; if its derivative is injective
and its inward radial germ stays in the closed disk, its normal derivative
is positive. Consequently the derivative of the straight-line homotopy is
nonsingular on the fixed arc. `BoundaryGerm/Extension.lean` applies the existing
stationary germ extension to obtain a compactly supported extension near a
smaller arc, fixing the whole circle. These are implementation lemmas with
directly checked statements. They do not assume, or construct, the missing
matching family, and are not replacements for the terminal leaf.

## References

This auxiliary supports Hatcher, *Notes on Basic 3-Manifold Topology* (2014),
Theorem 1.1, proof pp. 2-5. It is not a separately numbered source result.
The existing source and bibliography entry are recorded under
`references/topology/hatcher/` and `Hatcher3M2014`.

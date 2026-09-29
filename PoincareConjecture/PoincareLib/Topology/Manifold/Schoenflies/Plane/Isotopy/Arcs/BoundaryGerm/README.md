# Disk isotopy relative to a boundary arc

## Informal statement

Two smooth ambient planar disks have smooth regular injective boundary
markings on [-r,r], with r > 1, agreeing pointwise on that enlarged arc.
Their filled sets coincide on an open neighborhood V of the enlarged arc.
Let C be their common marked [-1,1] arc. In any open set O containing both
disks minus C, there is a family of smooth ambient diffeomorphisms indexed
by all real t, with jointly smooth evaluation and inverse evaluation,
starting at the identity and matching the filled disks at t = 1. Every
member fixes the complement of one compact subset of O disjoint from C.

## Informal proof

Normalize both marked disks to round disks with hemisphere coordinates.
Align their marked coordinates by reflection and a tangent-plane linear
adjustment. Composing these normalizations constructs a disk match that
fixes the common enlarged arc pointwise.

In source-disk coordinates, the derivative of that map fixes the tangent
line. Equality of the filled-side germs forces its normal derivative to be
positive. The straight-line derivative is therefore nonsingular. Extend
this stationary germ near a smaller compact arc while fixing the entire
source circle, and compose with the inverse extension. The resulting disk
match fixes an ambient neighborhood of the smaller arc.

Compress the source disk into this fixed neighborhood, with support away
from the arc. Conjugating the compression by the disk match gives a second
compression into the same fixed set. Retain the entire smooth compression
flow, extend it from the sweep chart using its common compact support, and
form its commutator with the disk match. This starts at the identity, has
smooth evaluation and inverse evaluation, equals the disk match on the
source disk at time one, and has compact support in O away from C uniformly
for all real times.

## Proposed formal statement

```lean
open Set Metric
open scoped Manifold ContDiff
namespace Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
private abbrev E1 := EuclideanSpace Real (Fin 1)
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
theorem exists_supported_disk_isotopy_of_common_arc
    (A B : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    {r : Real} (hr : 1 < r)
    (f g : E1 → S1)
    (hfi : InjOn f (closedBall 0 r))
    (hfl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ f x)
    (hgi : InjOn g (closedBall 0 r))
    (hgl : ∀ x ∈ closedBall (0 : E1) r,
      IsLocalDiffeomorphAt (𝓡 1) (𝓡 1) ∞ g x)
    (hmark : ∀ x ∈ closedBall (0 : E1) r, A (f x) = B (g x))
    (V : Set E2) (hV : IsOpen V)
    (hmarkV : (fun x => A (f x)) '' closedBall (0 : E1) r ⊆ V)
    (hside : V ∩ (A '' closedBall 0 1) = V ∩ (B '' closedBall 0 1))
    (O : Set E2) (hO : IsOpen O)
    (hAO : (A '' closedBall (0 : E2) 1) \
      ((fun x => A (f x)) '' closedBall (0 : E1) 1) ⊆ O)
    (hBO : (B '' closedBall (0 : E2) 1) \
      ((fun x => A (f x)) '' closedBall (0 : E1) 1) ⊆ O) :
    ∃ K : Set E2, IsCompact K ∧ K ⊆ O ∧
      Disjoint K ((fun x => A (f x)) '' closedBall (0 : E1) 1) ∧
      ∃ Φ : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
        (∀ x, Φ 0 x = x) ∧
        ContDiff Real ∞ (fun z : Real × E2 => Φ z.1 z.2) ∧
        ContDiff Real ∞ (fun z : Real × E2 => (Φ z.1).symm z.2) ∧
        (∀ t x, x ∉ K → Φ t x = x) ∧
        Φ 1 '' (A '' closedBall 0 1) = B '' closedBall 0 1 := by
  obtain ⟨E, hE, W, hW, hmarkW, hEW⟩ :=
    exists_disk_matching_fixing_common_arc_neighborhood A B hr f g hfi hfl hgi hgl
      hmark V hV hmarkV hside
  obtain ⟨K, hK, hKO, hKarc, Φ, hΦ0, hΦs, hΦi, hΦfix, hΦ⟩ :=
    Compression.exists_supported_disk_isotopy_of_fixed_arc_neighborhood A E f
      (hfi.mono (closedBall_subset_closedBall hr.le))
      (fun x hx => hfl x (closedBall_subset_closedBall hr.le hx))
      hW hO hmarkW hEW hAO (by rwa [hE])
  exact ⟨K, hK, hKO, hKarc, Φ, hΦ0, hΦs, hΦi, hΦfix, (image_congr hΦ).trans hE⟩
end Poincare.Manifold.Schoenflies.PlaneArcs.BoundaryGerm
```

## Informal translation

Let A and B be smooth diffeomorphisms of the plane, and let D_A and D_B be
their images of the closed unit disk. Suppose r > 1 and f,g: R -> S1 are
injective on [-r,r] and smooth local diffeomorphisms at every point there.
Assume A(f(t)) = B(g(t)) for every t in [-r,r]. Put gamma(t) = A(f(t)) and
C = gamma([-1,1]). Suppose V is open, contains gamma([-r,r]), and satisfies
V intersect D_A = V intersect D_B. For every open O containing D_A minus C
and D_B minus C, there exist a compact K contained in O and disjoint from C,
and a family Phi_t of smooth ambient diffeomorphisms for all real t, such
that Phi_0 is the identity, both (t,x) -> Phi_t(x) and
(t,x) -> Phi_t inverse(x) are smooth, Phi_t(x) = x outside K for every real
t, and Phi_1 sends D_A onto D_B. Every Phi_t fixes the same open
neighborhood of C.

## Alignment review

An independent formal-only translator and prose-only reviewer accepted the
family statement on 23 September 2026, including all-real-time indexing,
joint smoothness of both evaluations, and the common compact support. Fixing
a common neighborhood follows because the support bound is compact and
disjoint from C. The endpoint-only predecessor also passed independent
alignment. The differential, germ-extension, coordinate, and localization
lemmas are implementation steps checked directly against the argument above.

## Application boundary

This theorem constructs the isotopy. No input is an isotopy, a matching
map, or a predicate asserting one. It is still a one-disk geometric lemma,
not the terminal saddle leaf. To apply it to the saddle, construct the
exterior closures and their common marked arcs, establish the filled-side
agreement and the support clearance, handle the second arc relative to the
first, and retain smooth dependence on height and labeled boundaries.

The whole-circle route is ruled out by
`PlaneArcs.not_forall_disk_covers_of_terminal_slices` in
`../TerminalRegionObstruction.lean`: it uses the corrected terminal data's
derived actual slice family. This obstructs the proposed disk-containment
step, not the existential terminal-geometric leaf itself.

## Unnested anchor clearance

`../UnnestedAnchor.lean` constructs a single static match for two ordered
pairs of disjoint filled disks. Each pair has a continuous connector on
[0,1], with endpoints in the respective disks, midpoint at the origin,
and interior avoiding both disk boundaries. The connector interior lies
outside both disks: otherwise connectedness and boundary avoidance put it
in one disk's interior, forcing the opposite endpoint into that closed disk.
Thus all four disks avoid the origin. The open-region matcher applies in
the punctured plane, and compactness of its support supplies a positive
square that it fixes.

The input ambient diffeomorphisms parametrize individual disks; the matching
map is constructed. Independent formal-only translation and prose-only
review accepted this statement on 23 September 2026. The radius is chosen
after the anchor data. This supplies neither clearance for a prescribed
Morse square nor a radius uniform as the height approaches zero. The nested
case and the terminal leaf remain open.

The same module's `exists_unnested_negative_morse_anchor_matching` derives
connector avoidance from the local negative Morse equation on both disk
boundaries. Its labeled contacts are the middle points of the two local
hyperbolas. The explicit transverse segment lies in the open square and
has Morse height strictly above the negative level in its interior. Thus
this specialization takes no connector as an input.

## Simultaneous unnested pair isotopy

`PairIsotopy.lean` constructs an isotopy matching two ordered pairs of
disjoint filled disks simultaneously. Each corresponding disk pair has
regular injective boundary markings agreeing on an enlarged interval and
equal filled sets near that enlarged common arc. The conclusion has one
compact support set disjoint from both smaller marked arcs, smooth forward
and inverse evaluation for all real times, identity at time zero, and both
filled-disk equalities at time one.

First apply the one-disk theorem to disk zero in the complement of the
second enlarged arc. It fixes a neighborhood of that arc, so the transported
second disk still has the required boundary marking and filled-side germ.
Apply the theorem again to that transported disk in the complement of the
first target disk. Composing the two families at the same time gives the
claimed isotopy; the union of their compact supports avoids both marks.

Independent formal-only translation and prose-only alignment review accepted
the statement on 23 September 2026. The ambient disk charts are geometric
inputs; there is no input matching map or isotopy. This theorem fixes a
neighborhood of the two small arcs, not a prescribed square or all of the
given germ neighborhoods. It handles disjoint filled disks, not nested ones,
and does not yet supply dependence on the saddle height.

## Terminal geometric record

`../Terminal/Geometry.lean` constructs `TerminalSaddleGeometry` from the exact
terminal leaf hypotheses. It combines the terminal flattening, filled model
matching, and annular end producers, chooses an orthonormal height frame,
and selects a sufficiently short slab. Its explicit model is the standard
sheared sphere, with seeds at its two minima and maximum.

This record does not assert that this model has the actual nesting type or
that the chosen end labels match model components. It is therefore not yet
`TerminalSaddleData` and cannot discharge the planar leaf. Both this producer
and the pair isotopy have standard-only axiom audits in `../Checks.lean`.

## Recovering geometric anchor hypotheses

`../Terminal/RibbonSides.lean` derives equality of the filled sides along a
shared ribbon edge. The ribbon joins the two disks of each disjoint pair;
its transverse interiors avoid the four boundary circles. Connectedness
places these interiors outside all four filled disks. The transverse
orientation then gives actual disk charts agreeing near each point of the
first edge, hence an open neighborhood where the filled sets agree.

`../Terminal/MorseSides.lean` obtains this boundary avoidance from the local
negative Morse equation. The transverse ribbon stays in the open Morse
square and has height strictly above the negative level in its interior.
The shared first hyperbola lies on the first disk boundaries, while the
opposite hyperbola lies in the second closed disks. These are geometric
containment hypotheses; no filled-side equality or isotopy is assumed.

`MarkingExtraction.lean` uses stereographic coordinates and a small affine
rescaling to produce regular injective boundary markings in a prescribed
circle neighborhood. Thus ambient disk charts agreeing near a circle point
yield the enlarged common markings required by the relative construction.

`../Terminal/RibbonIsotopy.lean` combines these steps: shared boundary edges
of a transverse ribbon, disjoint fillings, and interior boundary avoidance
produce an isotopy matching both disks. No boundary marking or local
filled-side equality is supplied. The stronger
`exists_disk_pair_isotopy_fixing_compact_shared_ribbon` chooses a positive
smaller ribbon width, derives coverage of its compact edges by the local
markings, and fixes one open neighborhood of the entire compact ribbon for
all real times. The midpoint statement follows as a corollary.

For larger protected sets, `PairRegion.lean` constructs a disk-pair isotopy
avoiding a prescribed closed set P, provided each source and target disk
meets P only in its smaller common marked arc. It fixes one open
neighborhood of all of P throughout the isotopy. The same module proves
that a compact ribbon joining disjoint disks meets them only on their own
edges, using boundary avoidance to exclude the interior. The new ribbon
producer proves the required edge containment by shrinking the width.
Preserving a prescribed width still requires markings covering those full
edges.

`../Terminal/MorseIsotopy.lean` instantiates this producer using the explicit
negative Morse ribbon. Its boundary avoidance follows from the Morse
equation, and the ribbon contains the origin. Consequently the isotopy also
fixes one open neighborhood of a positive closed square. This square is
chosen at the given regular height; no uniform radius approaching the saddle
is asserted.

## Height orientation obstruction

`../Terminal/ModelChart.lean` derives the exact saddle quadratic germ for
the terminal record's model chart from its matching and positive scale.
The chart center is critical, with both higher and lower nearby values.
For the standard shear it must be the unique saddle point.

`../Terminal/Orientation.lean` identifies preconnectedness of the exact
actual and model planar slices with preconnectedness of their source height
levels. `../Terminal/StandardOrientation.lean` proves that the standard
model's lower levels are disconnected and that, when the actual lower
levels are connected, every proposed terminal slab contains a height with
no planar matching. This excludes the standard model for that orientation.
It is not a refutation of the full leaf, which can also choose the nested
model. The data currently lists only unreflected models, while the terminal
cut-resolution theorem retains both height orientations.

## Regular height transport from a constructed anchor

`../RegularPairFamily.lean` constructs the full isotopy-time and height
family on a compact interval of regular circle pairs. Its inputs are the
smooth embedded circle families, disjoint within each pair, and the
geometric common-arc disk data at the initial height. It does not take an
initial matching map or ambient diffeomorphism family.

Let Q(u) be the constructed anchor isotopy, and U(z), W(z) the ambient
extensions of the actual and model circle families, both identity at the
initial height a. With tau = a + u * (z - a), set
Phi(u,z) = W(tau) Q(u) U(tau)^{-1}. At u = 0 this is identity for every
height; at u = 1 it matches the ordered circle sets. Both evaluations are
jointly smooth, and the union of three support bounds is compact and
uniform in both real parameters. Independent formal-only translation and
prose-only review accepted these quantifiers and this argument.

This transport construction does not preserve the anchor's marked arcs or
a protected Morse patch. Applying it across the singular height still
requires relative transports and a construction at the saddle level.

## References

This auxiliary is not separately numbered in Hatcher, *Notes on Basic
3-Manifold Topology* (2014). Its relative compression argument supports
Theorem 1.1, proof pp. 2-5, and follows the construction around Lemma 1.3,
printed p. 5. The source and bibliography are already recorded under
`references/topology/hatcher/` and `Hatcher3M2014`.

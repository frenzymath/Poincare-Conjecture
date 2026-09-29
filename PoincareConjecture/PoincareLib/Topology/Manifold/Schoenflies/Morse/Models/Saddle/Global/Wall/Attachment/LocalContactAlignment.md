# Filled Intersection From Local Contact

## Informal Description

Let A and B be smooth ambient images of the closed unit ball in R^3. Suppose
their boundary spheres intersect exactly in a common disk W, parametrized on
each sphere by a map from R^2 that is injective on the closed unit disk and a
local smooth diffeomorphism at each point of that disk. If some open
neighborhood of a point of W meets A intersect B only in W, then the entire
intersection A intersect B equals W.

## Informal Proof

Normalize each marked boundary disk to a round cap. Stereographic projection
identifies its complementary boundary patch with an open disk, proving that
the patch is connected. Each complementary patch therefore lies either
inside the other ball or outside its closed ball. The first case would put
the entire first ball inside the second: the connected unbounded exterior
of the second ball avoids the first boundary and thus also its filled ball.
The local contact excludes containment in either direction, because every
boundary point is a limit of interior points. Thus both complementary
patches are exterior. Connectedness of each ball interior now excludes any
intersection of interiors, leaving exactly W.

## Proposed Formal Statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.TouchingBalls

open Set Metric Function
open scoped Manifold ContDiff

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

example
    (A B : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (f g : E2 → S2)
    (hfi : InjOn f (closedBall 0 1)) (hgi : InjOn g (closedBall 0 1))
    (hfl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ f x)
    (hgl : ∀ x ∈ closedBall (0 : E2) 1,
      IsLocalDiffeomorphAt (𝓡 2) (𝓡 2) ∞ g x)
    (hmark : (fun x => A (f x)) '' closedBall (0 : E2) 1 =
      (fun x => B (g x)) '' closedBall (0 : E2) 1)
    (hmeet : (A '' sphere (0 : E3) 1) ∩ (B '' sphere (0 : E3) 1) =
      (fun x => A (f x)) '' closedBall (0 : E2) 1)
    {U : Set E3} (hU : IsOpen U) {p : E3} (hpU : p ∈ U)
    (hp : p ∈ (fun x => A (f x)) '' closedBall (0 : E2) 1)
    (hlocal : U ∩ ((A '' closedBall (0 : E3) 1) ∩ (B '' closedBall (0 : E3) 1)) ⊆
      (fun x => A (f x)) '' closedBall (0 : E2) 1) :
    (A '' closedBall (0 : E3) 1) ∩ (B '' closedBall (0 : E3) 1) =
      (fun x => A (f x)) '' closedBall (0 : E2) 1 := by
  exact Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.filled_intersection_of_local_contact
    A B f g hfi hgi hfl hgl hmark hmeet hU hpU hp hlocal
```

## Formal-To-Informal Translation

Let A and B be smooth diffeomorphisms of R^3, and let f and g map R^2 to the
unit sphere. Assume that f and g are injective on the closed unit disk and
are local smooth diffeomorphisms at every point of that disk. Their images
under A and B define the same subset W, and the two ambient images of the
unit sphere intersect exactly in W. Suppose U is open, p belongs to U and W,
and U intersect A(closed unit ball) intersect B(closed unit ball) is contained
in W. Then A(closed unit ball) intersect B(closed unit ball) equals W.

## Alignment Review

Accepted by separate local translation and comparison passes. The ambient
images, both markings, exact boundary intersection, one local contact point,
and exact filled intersection agree. No global smoothness of f or g away
from the marked disk is assumed. Native dispatch was attempted with the full
formal statement, but failed with `agent thread limit reached`; the local
passes are the documented fallback, not an independent external review.

This is an intermediate geometric prerequisite. The original terminal saddle
producer still needs actual compatible closures and the final boundary
comparison; this theorem does not discharge those obligations.

## References

This auxiliary local-to-global intersection lemma is not separately numbered
in the source. It supports the marked-ball attachment used in Hatcher,
Theorem 1.1, pp. 1-5, and Lemma 1.3 with the following corner paragraph, p. 5.

```bibtex
@misc{Hatcher3M2014,
  author = {Hatcher, Allen},
  title = {Notes on Basic 3-Manifold Topology},
  year = {2014},
  note = {Online notes; Theorem 1.1, pp. 1--5; sphere extension, p. 5;
    Proposition 1.6, p. 11. Retrieved 21 September 2026},
  url = {https://pi.math.cornell.edu/~hatcher/3M/3Mfds2014.pdf}
}
```

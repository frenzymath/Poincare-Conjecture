# Fixed exterior arcs and protected graph levels

## Informal description

Let delta be positive, r < rho, and let a fixed planar curve gamma be
continuous at gamma's parameter A(0). Suppose A and B are continuous at zero,
A(0) < B(0), and gamma(A(0)) belongs to the closed square of radius r.
For any function h from the plane to the reals, no family of planar maps can
both fix the closed square of radius rho pointwise and send the restricted
curve gamma([A(t),B(t)]) into height level t of h wherever its image is in
that square, for every t in [-delta,delta].

## Informal proof

The initial endpoint is in the interior of the larger square. Continuity of
gamma gives a parameter s strictly between A(0) and B(0) whose image is
still in that square. Continuity of A and B retains s strictly between A(t)
and B(t) for all sufficiently small t. Every proposed map fixes gamma(s).
The level condition at zero and at a sufficiently small positive t would
give both h(gamma(s)) = 0 and h(gamma(s)) = t, a contradiction.

## Proposed formal statements

```lean
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Coordinates
open Set
namespace Poincare.Manifold.Schoenflies.PlaneArcs
theorem not_exists_fixed_square_graph_matching
    {delta r rho : Real} (hdelta : 0 < delta) (hrho : r < rho)
    (gamma : Real -> EuclideanSpace Real (Fin 2)) (A B : Real -> Real)
    (hgamma : ContinuousAt gamma (A 0))
    (hA : ContinuousAt A 0) (hB : ContinuousAt B 0)
    (hAB : A 0 < B 0)
    (hcontact : gamma (A 0) ∈ SaddleLevel.closedSquare r)
    (h : EuclideanSpace Real (Fin 2) -> Real) :
    ¬ ∃ Phi : Real -> EuclideanSpace Real (Fin 2) -> EuclideanSpace Real (Fin 2),
      (∀ t x, x ∈ SaddleLevel.closedSquare rho -> Phi t x = x) ∧
      (∀ t ∈ Icc (-delta) delta, ∀ s ∈ Icc (A t) (B t),
        Phi t (gamma s) ∈ SaddleLevel.closedSquare rho -> h (Phi t (gamma s)) = t) := by
  sorry
end Poincare.Manifold.Schoenflies.PlaneArcs
```

## Mission implication

The published `exists_terminal_flattened_band_level_sets` retains
`(D ∘ g ∘ e)` on its central patch. It does not identify that transformed
patch with the original Morse graph. A fixed exterior arc through the smaller
square cannot simultaneously have the asserted graph-level description in
the larger fixed square. To obtain relative matching, retain unflattened
moving arcs near the square, or protect a smaller region disjoint from the
flattened strips and retain the intervening transformed patch. Neither
correction supplies the still-missing initial relative arc matching.

## Informal translation

For a real a, let Q_a be the set of points whose two coordinates have absolute
value at most a. Let delta > 0 and r < rho. Suppose gamma is continuous at
A(0), A and B are continuous at zero, A(0) < B(0), and gamma(A(0)) is in Q_r.
For every function h from the plane to the reals, there is no family Phi_t of
planar maps indexed by all real t satisfying both of the following conditions:
each Phi_t fixes Q_rho pointwise; for every t in [-delta,delta] and every s in
[A(t),B(t)], membership of Phi_t(gamma(s)) in Q_rho implies
h(Phi_t(gamma(s))) = t.

## Alignment review

The independent formal-only translator and prose-only reviewer accepted the
complete statement on 23 September 2026. No smoothness or injectivity of the
maps, or regularity of h, is needed.

The SHA-256 of the candidate declaration from `theorem` through `sorry`,
including its final newline, is
`593e4d60d2f638dc94e3a13bf397ccd2c9aaefdf8a5dd4a52a1ee46e1bb2ba99`.

## Verification

Lean 4.33.1 checked `Arcs.Checks`, including the obstruction, in 3,344 jobs.
Its recursive axiom audit contains only `propext`, `Classical.choice`, and
`Quot.sound`. `make check` passed the 12 frozen-contract hashes and the
20,304-job workspace build on 23 September 2026.

## References

This elementary continuity obstruction is not taken from a published source.
The geometric application concerns the transformed central patch in
`SphereMorseReduction.exists_terminal_flattened_band_level_sets`, specifically
the first level identity in its conclusion.

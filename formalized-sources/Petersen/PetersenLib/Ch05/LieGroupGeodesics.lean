import PetersenLib.Ch04.BiinvariantMetrics

/-!
# Petersen Ch. 5, §5.2 — Geodesics of a bi-invariant metric on a Lie group

Petersen's Example (§5.2, GTM 171, 3rd ed.): on a Lie group `G` with a
left-invariant metric, an integral curve of a left-invariant vector field `X` is
a geodesic iff `∇_X X ≡ 0`; and for a *bi-invariant* metric the Levi-Civita
connection of two left-invariant fields is `∇_Y X = ½ [Y, X]`, so
`∇_X X = ½ [X, X] = 0` — every left-invariant field is a geodesic field.

Following the algebraic modelling of the project's biinvariant material
(`PetersenLib.Ch04.BiinvariantMetrics`), the Lie algebra `𝔤` is a real inner
product space `V`, the Lie bracket is carried as an explicit real-bilinear map
`bracket : V →ₗ[ℝ] V →ₗ[ℝ] V`, and bi-invariance is encoded by the alternating
hypothesis `hskew : ∀ x, [x, x] = 0` (which yields `bracket_skew`, the
antisymmetry `[x, y] = −[y, x]`). The Koszul characterisation of the
Levi-Civita connection at the Lie-algebra level is `∇_y x := ½ [y, x]`
(`biinvariantConnectionCurvature`, clause (a)); the content here is that its
self-value `∇_x x = ½ [x, x]` vanishes.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.2, Example
(Lie groups with bi-invariant metrics).
-/

noncomputable section

namespace PetersenLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {bracket : V →ₗ[ℝ] V →ₗ[ℝ] V}

/-- **Math.** Petersen §5.2, Example (Lie groups with a bi-invariant metric):
a left-invariant vector field `X` on a Lie group is a geodesic field, because
the Levi-Civita connection of a bi-invariant metric satisfies
`∇_X X = ½ [X, X] = 0`.

Modelled at the Lie-algebra level as in `PetersenLib.Ch04.BiinvariantMetrics`:
with the Koszul-characterised connection value `∇_y x := (2⁻¹ : ℝ) • [y, x]`
(clause (a) of `biinvariantConnectionCurvature`), the self-value
`∇_x x = (2⁻¹ : ℝ) • [x, x]` vanishes, using only the alternating hypothesis
`hskew : ∀ x, [x, x] = 0` of a bi-invariant metric. Stated in the
`½ • bracket` form so that it reads as the geodesic condition
`∇_X X = ½ [X, X] = 0`. -/
theorem leftInvariantGeodesicFields (hskew : ∀ x : V, bracket x x = 0) (x : V) :
    (2⁻¹ : ℝ) • bracket x x = 0 := by
  rw [hskew x, smul_zero]

end PetersenLib

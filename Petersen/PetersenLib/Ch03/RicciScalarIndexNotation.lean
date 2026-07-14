import PetersenLib.Ch03.GramFrame

/-!
# Petersen Ch. 3, §3.1.6 — index notation for `Ric` and `scal`

Remark 3.1.7 (`rem:pet-ch3-ricci-scalar-index-notation`): the coordinate
contractions of the curvature tensor,
`Ric_{ij} = R^k_{ikj} = g^{kl} R_{kijl}` and `scal = g^{ij} Ric_{ij}`.

Both are read off the **Gram-inverse trace formula** (`trace_eq_sum_gramInv`):
for any family `v` of tangent vectors at `p` with invertible Gram matrix
`G_{ij} = g(v_i, v_j)`, the trace of an endomorphism `S` is
`tr S = ∑_{ij} (G⁻¹)_{ij} g(S(v_i), v_j)`, and the entries `(G⁻¹)_{ij}` are
exactly the inverse-metric components `g^{ij}` in the frame `v`. Applying it to
`S = (x ↦ R(x, v_i) v_j)` (whose trace is `Ric(v_i, v_j)`) gives the Ricci
contraction; applying it to the Ricci endomorphism gives the scalar
contraction.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.6.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-- **Math.** **Remark 3.1.7 — index notation for `Ric` and `scal`**
(Petersen §3.1.6, `rem:pet-ch3-ricci-scalar-index-notation`). In a smooth frame
`F_1, …, F_n` whose Gram matrix `G(q)_{kl} = g(F_k, F_l)(q)` is invertible at
`q` (e.g. a chart coordinate frame), write `g^{kl} := (G⁻¹)_{kl}` for the
inverse-metric components (`cramerInverse` is the matrix inverse when `det ≠ 0`)
and `R_{kijl} := R(F_k, X, Y, F_l) = g(R(F_k, X) Y, F_l)` for the fully-lowered
curvature components (`curvatureTensorFour`). Then the Ricci and scalar
curvatures are the index contractions

* `Ric_{ij} = g^{kl} R_{kijl}`, contracting the `(0,4)`-curvature tensor against
  the inverse metric over its outer slots, and
* `scal = g^{ij} Ric_{ij}`, contracting the Ricci tensor against the inverse
  metric.

Both are the Gram-inverse trace formula specialised: the Ricci contraction is
the trace `Ric(X,Y) = tr(x ↦ R(x, X) Y)` written through `G⁻¹`
(`ricciCurvature_eval_eq_sum_gramInv`), and the scalar contraction is the trace
of the Ricci endomorphism written through `G⁻¹`
(`scalarCurvature_eq_sum_gramInv`). -/
theorem ricciScalar_indexNotation (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i))
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) {q : M}
    (hdet : (gramMatrixField g F q).det ≠ 0) :
    RicciCurvature D.toAffineConnection q (X q) (Y q)
        = ∑ k, ∑ l, cramerInverse (gramMatrixField g F q) k l
            * curvatureTensorFour D (F k) X Y (F l) q
      ∧ scalarCurvature D q
        = ∑ k, ∑ l, cramerInverse (gramMatrixField g F q) k l
            * RicciCurvature D.toAffineConnection q (F k q) (F l q) :=
  ⟨ricciCurvature_eval_eq_sum_gramInv D hF hX hY hdet,
    scalarCurvature_eq_sum_gramInv D hdet⟩

end PetersenLib

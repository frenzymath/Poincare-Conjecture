import PetersenLib.Ch02.CovariantAdjoint

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.29 (geodesic unit fields and integrability)

Let `X` be a unit vector field on `(M, g)` with `∇_X X = 0` (a *geodesic* unit
field: its integral curves are geodesics). Petersen asks to show

1. `X` is locally a gradient field iff the orthogonal distribution `X^⊥` is
   integrable;
2. `X^⊥` is integrable near `p` if it has an integral submanifold through `p`
   (hint: show `L_X θ_X = 0`);
3. exhibit such an `X` on `S³` that is not a gradient field.

We formalize the **reachable algebraic core** — the hint of part (2): for a
geodesic unit field `X`, the Lie derivative of its dual `1`-form
`θ_X = i_X g` (`dualOneForm`) along `X` vanishes,
`L_X θ_X = 0` (`exercise2_5_29`). This is exactly the identity that, combined
with `θ_X(X) = |X|² = 1`, forces `dθ_X` to annihilate `X` and thereby makes the
orthogonal distribution `X^⊥` involutive along its integral submanifolds.

The proof is Petersen's, purely from the connection axioms:
`(L_X θ_X)(Y) = D_X\,g(X,Y) − g(X,[X,Y])`; metric compatibility with `∇_X X = 0`
gives `D_X\,g(X,Y) = g(X, ∇_X Y)`; torsion-freeness gives
`g(X,[X,Y]) = g(X, ∇_X Y) − g(X, ∇_Y X)`; and unit length gives `g(X, ∇_Y X) = 0`
(differentiate `g(X,X) = 1`). The two `g(X, ∇_X Y)` cancel.

The integrability conclusions (Frobenius) of parts (1)–(2) and the `S³`
construction of part (3) require the integral-manifold / Frobenius machinery,
unavailable in the manifold API, and are not formalized.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 29.
-/

open scoped Manifold ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** For a unit vector field `X` (`|X|² = 1`) and the Levi-Civita
connection, the covariant derivative of `X` in any direction `Y` is orthogonal to
`X`: `g(∇_Y X, X) = 0`.  (Differentiate the constant `g(X,X) = 1`.) -/
theorem RiemannianConnection.metricInner_cov_unit_orthogonal
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X)
    (hunit : ∀ q, g.metricInner q (X q) (X q) = 1) (p : M) :
    g.metricInner p (D.cov p (Y p) X) (X p) = 0 := by
  have hcompat := D.metric_compat hX hX p (Y p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have hconst : directionalDerivative Y (fun q => g.metricInner q (X q) (X q)) p = 0 := by
    rw [show (fun q => g.metricInner q (X q) (X q)) = fun _ => (1 : ℝ) from funext hunit]
    exact directionalDerivative_const Y 1 p
  rw [hconst, g.metricInner_comm p (X p) (D.cov p (Y p) X)] at hcompat
  linarith

/-- **Math.** Exercise 2.5.29 (algebraic core): for a geodesic unit vector field
`X` (`|X| = 1`, `∇_X X = 0`) on `(M, g)`, the Lie derivative of its dual
`1`-form `θ_X = i_X g` along `X` vanishes, `L_X θ_X = 0`. -/
theorem exercise2_5_29
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hunit : ∀ q, g.metricInner q (X q) (X q) = 1)
    (hgeo : ∀ q, D.cov q (X q) X = 0) (p : M) :
    lieDerivativeTensor I X (dualOneForm g X) ![Y] p = 0 := by
  rw [lieDerivativeTensor_formula, Fin.sum_univ_one]
  -- The two `dualOneForm` evaluations: `θ_X(Y) = g(X,Y)` and the updated slot.
  have hθY : (dualOneForm g X ![Y]) = fun q => g.metricInner q (X q) (Y q) := rfl
  have key : dualOneForm g X (Function.update (![Y] : Fin 1 → Π x : M, TangentSpace I x) 0
        (lieDerivativeVectorField I X (![Y] 0))) p
      = g.metricInner p (X p) (lieDerivativeVectorField I X Y p) := by
    simp only [dualOneForm_apply, Function.update_self, Matrix.cons_val_zero]
  rw [hθY, key]
  -- Metric compatibility along `X`, with `∇_X X = 0`.
  have hcompat := D.metric_compat hX hY p (X p)
  rw [dirTangent_eq_directionalDerivative, hgeo p, g.metricInner_zero_left] at hcompat
  -- Torsion-freeness: `[X,Y] = ∇_X Y − ∇_Y X`.
  have htf := D.torsion_free hX hY p
  -- `g(X, ∇_Y X) = 0` from unit length.
  have hunit0 := D.metricInner_cov_unit_orthogonal (Y := Y) hX hunit p
  rw [hcompat, ← htf, g.metricInner_sub_right,
    g.metricInner_comm p (X p) (D.cov p (Y p) X), hunit0]
  ring

end PetersenLib

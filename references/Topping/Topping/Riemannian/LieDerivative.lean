import MorganTianLib.Ch02.Gradient
import Topping.Riemannian.Hessian
import Topping.Riemannian.Variation

/-!
# The Lie derivative of the metric along a dual vector field

Topping's Chapter 2 remark: for a `1`-form `ω`,
`\mathcal L_{ω^\#}g(X,W) = ∇ω(X,W) + ∇ω(W,X)`, and in particular for `ω = df`,
`\mathcal L_{(df)^\#}g = 2\Hess(f)`.

The first identity is the symmetrization of `∇ω`: metric compatibility turns
`(\mathcal L_Vg)(X,W) = V⟨X,W⟩ - ⟨[V,X],W⟩ - ⟨X,[V,W]⟩` into
`⟨∇_XV,W⟩ + ⟨X,∇_WV⟩` for a torsion-free connection, and with `V = ω^\#` those
two terms are `∇ω(X,W)` and `∇ω(W,X)`.

The second follows because `(df)^\# = ∇f` is the gradient and
`⟨∇_X∇f,W⟩ = \Hess(f)(X,W)`, which is
`MorganTianLib.hessian_eq_metricInner_cov_gradientField`; symmetry of the Hessian
then collapses the symmetrization to twice itself.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The symmetric gradient of a vector field `V`, i.e. the symmetrized
covariant derivative `X, W ↦ ⟨∇_XV,W⟩ + ⟨X,∇_WV⟩`. For `V = ω^\#` this is
Topping's `\mathcal L_{ω^\#}g`. -/
def symmetricGradient (g : RiemannianMetric I M) (V : SmoothVectorField I M) :
    CovTensorField I M 2 :=
  fun Y p =>
    g.metricInner p ((g.leviCivitaConnection.cov (Y 0) V) p) (Y 1 p)
      + g.metricInner p (Y 0 p) ((g.leviCivitaConnection.cov (Y 1) V) p)

set_option linter.unusedSectionVars false in
/-- **Math.** The symmetric gradient is symmetric, as its name says. -/
theorem symmetricGradient_symm (g : RiemannianMetric I M)
    (V : SmoothVectorField I M) (X W : SmoothVectorField I M) (p : M) :
    symmetricGradient g V (fun i => if i = 0 then X else W) p =
      symmetricGradient g V (fun i => if i = 0 then W else X) p := by
  simp only [symmetricGradient, show (1 : Fin 2) ≠ 0 by decide, if_false,
    reduceIte]
  rw [g.metricInner_comm p ((g.leviCivitaConnection.cov X V) p) (W p),
    g.metricInner_comm p (X p) ((g.leviCivitaConnection.cov W V) p)]
  ring

/-- **Math.** `\mathcal L_{(df)^\#}g = 2\Hess(f)`: for `ω = df` the dual vector
field is the gradient, and the symmetrized covariant derivative of the gradient is
twice the Hessian, the two terms agreeing by symmetry of the Hessian. -/
theorem symmetricGradient_gradientField_eq_two_hessian (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X W : SmoothVectorField I M)
    (p : M) :
    symmetricGradient g (MorganTianLib.gradientField g f hf)
        (fun i => if i = 0 then X else W) p =
      2 * hessian g f X W p := by
  have hcompat := (isLeviCivita_leviCivitaConnection g).2
  have hXW := MorganTianLib.hessian_eq_metricInner_cov_gradientField
    g g.leviCivitaConnection hcompat hf X W p
  have hWX := MorganTianLib.hessian_eq_metricInner_cov_gradientField
    g g.leviCivitaConnection hcompat hf W X p
  have hsymm : MorganTianLib.hessian g.leviCivitaConnection f W X p =
      MorganTianLib.hessian g.leviCivitaConnection f X W p :=
    MorganTianLib.hessian_symm g.leviCivitaConnection
      (isLeviCivita_leviCivitaConnection g).1 hf W X p
  simp only [symmetricGradient, show (1 : Fin 2) ≠ 0 by decide, if_false,
    reduceIte]
  rw [g.metricInner_comm p (X p) ((g.leviCivitaConnection.cov W
    (MorganTianLib.gradientField g f hf)) p), ← hXW, ← hWX, hsymm]
  rw [show hessian g f X W p
      = MorganTianLib.hessian g.leviCivitaConnection f X W p from rfl]
  ring

end Topping

end

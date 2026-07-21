import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import DoCarmoLib.Riemannian.Variation.Energy
import DoCarmoLib.Riemannian.Variation.FirstVariation

/-!
# `E'(s)` by differentiation under the integral sign — chart-free

do Carmo, *Riemannian Geometry*, Ch. 9, §2, Prop. 2.4 (`prop:dc-ch9-2-4`), the step
"differentiating under the integral sign".

WORK IN PROGRESS — see the session report.
-/

open Set Riemannian Filter MeasureTheory
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ### `E'(s₀) = 2∫⟨D/∂s ∂f/∂t, ∂f/∂t⟩ dt`

The pointwise input is `IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner_self`
(`Variation/CovariantField.lean`), metric compatibility at `V = W` along a curve: applied
along the **transversal** `σ ↦ f(σ, t)` with `V = ∂f/∂t` it gives
`∂/∂s⟨∂f/∂t, ∂f/∂t⟩ = 2⟨D/∂s ∂f/∂t, ∂f/∂t⟩`.  A transversal is a curve like any other, and
that lemma is chart-free, so no chart and no two-parameter surface object appear. -/

/-- **Math.** do Carmo Ch. 9, `prop:dc-ch9-2-4`, **the differentiation under the integral
sign**, chart-free:
$$E'(s_0)
  = \int_a^b \frac{\partial}{\partial s}\Big\langle\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle\Big|_{s_0} dt
  = 2\int_a^b \Big\langle\frac{D}{\partial s}\frac{\partial f}{\partial t},\frac{\partial f}{\partial t}\Big\rangle\Big|_{s_0} dt .$$

`f` is a variation, `T` its `t`-velocity field `∂f/∂t` (`hvel`), and `DsT` the covariant
`s`-derivative `D/∂s ∂f/∂t`, presented — as everywhere in this file — as the covariant pair
`(T, DsT)` along each **transversal** `σ ↦ f(σ, t)` (`hslice`).

The pointwise input is `hasDerivAt_metricInner_self`; the exchange is mathlib's
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, whose domination
hypothesis is discharged by the caller via `bound`.  Nothing is chart-fixed. -/
theorem hasDerivAt_dcEnergy_of_dominated
    {g : RiemannianMetric I M} {f : ℝ × ℝ → M} {T DsT : ℝ × ℝ → E}
    {s₀ a b ε : ℝ} {bound : ℝ → ℝ}
    (hε : 0 < ε)
    (hvel : ∀ σ t, T (σ, t) = DCVelocity (I := I) (fun τ => f (σ, τ)) t)
    (hslice : ∀ t ∈ uIoc a b, IsCovariantDerivFieldAlongOn (I := I) g
      (fun σ => f (σ, t)) (fun σ => T (σ, t)) (fun σ => DsT (σ, t)) (s₀ - ε) (s₀ + ε))
    (hsdiff : ∀ t ∈ uIoc a b, IsChartDifferentiableOn (I := I)
      (fun σ => f (σ, t)) (s₀ - ε) (s₀ + ε))
    (hscont : ∀ t ∈ uIoc a b, ∀ σ ∈ Icc (s₀ - ε) (s₀ + ε),
      ContinuousAt (fun σ' => f (σ', t)) σ)
    (hF_meas : ∀ᶠ σ in nhds s₀, AEStronglyMeasurable
      (fun t => g.metricInner (f (σ, t)) (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)))
      (volume.restrict (uIoc a b)))
    (hF_int : IntervalIntegrable
      (fun t => g.metricInner (f (s₀, t)) (T (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      volume a b)
    (hF'_meas : AEStronglyMeasurable
      (fun t => 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t)))
      (volume.restrict (uIoc a b)))
    (h_bound : ∀ t ∈ uIoc a b, ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖
        ≤ bound t)
    (hbound_int : IntervalIntegrable bound volume a b) :
    HasDerivAt (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)
      (∫ t in a..b, 2 * g.metricInner (f (s₀, t))
        (DsT (s₀, t) : TangentSpace I (f (s₀, t))) (T (s₀, t))) s₀ := by
  have hmem : Ioo (s₀ - ε) (s₀ + ε) ∈ nhds s₀ :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have hderiv : ∀ᵐ t, t ∈ uIoc a b → ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      HasDerivAt (fun σ' => g.metricInner (f (σ', t))
          (T (σ', t) : TangentSpace I (f (σ', t))) (T (σ', t)))
        (2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))) σ := by
    filter_upwards with t ht σ hσ
    exact (hslice t ht).hasDerivAt_metricInner_self (hsdiff t ht) (hscont t ht) hσ
  have hbd : ∀ᵐ t, t ∈ uIoc a b → ∀ σ ∈ Ioo (s₀ - ε) (s₀ + ε),
      ‖2 * g.metricInner (f (σ, t)) (DsT (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t))‖
        ≤ bound t := by
    filter_upwards with t ht σ hσ using h_bound t ht σ hσ
  have hE : (fun σ => DCEnergy (I := I) g (fun t => f (σ, t)) a b)
      = fun σ => ∫ t in a..b,
          g.metricInner (f (σ, t)) (T (σ, t) : TangentSpace I (f (σ, t))) (T (σ, t)) := by
    funext σ
    simp only [DCEnergy]
    simp_rw [← hvel]
  rw [hE]
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hmem hF_meas hF_int hF'_meas hbd hbound_int hderiv).2

end Riemannian.Variation

import Topping.ParabolicPDE.ParabolicHolder

/-!
# Continuity from parabolic Holder control

Separate positive-exponent spatial and temporal Holder bounds combine into a
genuine continuity producer on the full space-time product.  This is a
chart-free analytic consumer: it adds no PDE existence or manifold structure.
-/

namespace Topping
namespace ParabolicPDE

open Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

variable {X T V : Type*}
  [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]

/-- Positive spatial and temporal Holder exponents imply continuity on the
full space-time product. -/
theorem ParabolicHolderControl.continuous
    {u : X × T → V} {Cs α Ct β : ℝ≥0}
    (h : ParabolicHolderControl u Set.univ Cs α Ct β)
    (hα : 0 < α) (hβ : 0 < β) :
    Continuous u := by
  rw [EMetric.continuous_iff']
  intro z ε hε
  rcases z with ⟨x, t⟩
  have hdistX : Tendsto (fun y : X × T => edist y.1 x) (𝓝 (x, t)) (𝓝 0) := by
    have hc : Continuous (fun y : X × T => edist y.1 x) :=
      continuous_edist.comp (continuous_fst.prodMk continuous_const)
    simpa [edist_self] using (hc.continuousAt : ContinuousAt _ (x, t)).tendsto
  have hdistT : Tendsto (fun y : X × T => edist y.2 t) (𝓝 (x, t)) (𝓝 0) := by
    have hc : Continuous (fun y : X × T => edist y.2 t) :=
      continuous_edist.comp (continuous_snd.prodMk continuous_const)
    simpa [edist_self] using (hc.continuousAt : ContinuousAt _ (x, t)).tendsto
  have hsp : Tendsto
      (fun y : X × T => (Cs : ℝ≥0∞) * edist y.1 x ^ (α : ℝ))
      (𝓝 (x, t)) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (c := (Cs : ℝ≥0∞)) ENNReal.coe_ne_top hα).comp hdistX
  have htp : Tendsto
      (fun y : X × T => (Ct : ℝ≥0∞) * edist y.2 t ^ (β : ℝ))
      (𝓝 (x, t)) (𝓝 0) :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos
      (c := (Ct : ℝ≥0∞)) ENNReal.coe_ne_top hβ).comp hdistT
  have hsum := hsp.add htp
  have hev : ∀ᶠ y in 𝓝 (x, t),
      (Cs : ℝ≥0∞) * edist y.1 x ^ (α : ℝ) +
        (Ct : ℝ≥0∞) * edist y.2 t ^ (β : ℝ) < ε := by
    have hm : Set.Iio ε ∈ 𝓝 (0 : ℝ≥0∞) := Iio_mem_nhds hε
    have hm' : Set.Iio ε ∈ 𝓝 ((0 : ℝ≥0∞) + 0) := by simpa using hm
    change Set.Iio ε ∈ Filter.map
      (fun y : X × T => (Cs : ℝ≥0∞) * edist y.1 x ^ (α : ℝ) +
        (Ct : ℝ≥0∞) * edist y.2 t ^ (β : ℝ)) (𝓝 (x, t))
    exact hsum hm'
  filter_upwards [hev] with y hy
  exact (h.edist_le_split (by trivial) (by trivial)).trans_lt hy

end
end ParabolicPDE
end Topping

#print axioms Topping.ParabolicPDE.ParabolicHolderControl.continuous

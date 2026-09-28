import Topping.ParabolicPDE.ParabolicHolder

/-!
# Restricted continuity from parabolic Holder control

Positive spatial and temporal Holder exponents give continuity on a prescribed
time domain.  The estimate is checked in the ambient product and then
restricted with `nhdsWithin`; no boundedness or PDE existence assumption is
needed.
-/

namespace Topping
namespace ParabolicPDE

open Filter Set
open scoped NNReal ENNReal Topology

noncomputable section

variable {X T V : Type*}
  [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]

/-- Positive-exponent parabolic Holder control implies continuity on the
space-time region whose time coordinate lies in `J`. -/
theorem ParabolicHolderControl.continuousOn_prod_of_positive
    {J : Set T} {u : X × T → V} {Cs α Ct β : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β)
    (hα : 0 < α) (hβ : 0 < β) :
    ContinuousOn u (Set.univ ×ˢ J) := by
  intro z hz
  rcases z with ⟨x, t⟩
  rcases hz with ⟨-, ht⟩
  rw [ContinuousWithinAt]
  apply (EMetric.tendsto_nhds (u := u) (a := u (x, t))).2
  intro ε hε
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
  have hev : ∀ᶠ y in 𝓝[Set.univ ×ˢ J] (x, t),
      (Cs : ℝ≥0∞) * edist y.1 x ^ (α : ℝ) +
        (Ct : ℝ≥0∞) * edist y.2 t ^ (β : ℝ) < ε := by
    have hm : Set.Iio ε ∈ 𝓝 (0 : ℝ≥0∞) := Iio_mem_nhds hε
    have hm' : Set.Iio ε ∈ 𝓝 ((0 : ℝ≥0∞) + 0) := by simpa using hm
    have hev' : ∀ᶠ y in 𝓝 (x, t),
        (Cs : ℝ≥0∞) * edist y.1 x ^ (α : ℝ) +
          (Ct : ℝ≥0∞) * edist y.2 t ^ (β : ℝ) < ε := by
      change Set.Iio ε ∈ Filter.map
        (fun y : X × T => (Cs : ℝ≥0∞) * edist y.1 x ^ (α : ℝ) +
          (Ct : ℝ≥0∞) * edist y.2 t ^ (β : ℝ)) (𝓝 (x, t))
      exact hsum hm'
    exact Filter.Eventually.filter_mono nhdsWithin_le_nhds hev'
  filter_upwards [hev, self_mem_nhdsWithin] with y hy hyJ
  exact (h.edist_le_split hyJ.2 ht).trans_lt hy

end
end ParabolicPDE
end Topping

#print axioms Topping.ParabolicPDE.ParabolicHolderControl.continuousOn_prod_of_positive

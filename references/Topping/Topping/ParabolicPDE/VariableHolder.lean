import Topping.ParabolicPDE.VariableSectionNemytskii
import Mathlib.Topology.MetricSpace.HolderNorm

/-!
# Holder control for variable-coefficient section maps

This file supplies the elementary product estimate needed before a genuine
chartwise Schauder construction.  A Holder operator field applied to a bounded
Holder section is Holder, with the expected two product terms.  The estimate
is then summed over the finite jet indices.
-/

namespace Topping

open scoped BoundedContinuousFunction BigOperators NNReal ENNReal Topology

noncomputable section

variable {T E V : Type*} [PseudoMetricSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ## A Holder product estimate -/

theorem holderWith_clm_apply
    {r CF Cu BF Bu : ℝ≥0}
    {F : T → (E →L[ℝ] V)} {u : T → E}
    (hF : HolderWith CF r F) (hu : HolderWith Cu r u)
    (hFbound : ∀ t, ‖F t‖ ≤ BF) (hubound : ∀ t, ‖u t‖ ≤ Bu) :
    HolderWith (BF * Cu + CF * Bu) r (fun t => F t (u t)) := by
  intro t s
  simp only [edist_dist]
  rw [ENNReal.coe_nnreal_eq]
  rw [ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg]
  calc
    ENNReal.ofReal (dist (F t (u t)) (F s (u s))) ≤
        ENNReal.ofReal ((BF * Cu + CF * Bu : ℝ) * dist t s ^ (r : ℝ)) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        dist (F t (u t)) (F s (u s)) ≤
            dist (F t (u t)) (F t (u s)) +
              dist (F t (u s)) (F s (u s)) := dist_triangle _ _ _
        _ ≤ ‖F t‖ * dist (u t) (u s) +
              ‖u s‖ * dist (F t) (F s) := by
          apply add_le_add ((F t).dist_le_opNorm _ _)
          calc
            dist (F t (u s)) (F s (u s)) =
                ‖(F t - F s) (u s)‖ := by rw [dist_eq_norm, sub_apply]
            _ ≤ ‖F t - F s‖ * ‖u s‖ := (F t - F s).le_opNorm _
            _ = ‖u s‖ * dist (F t) (F s) := by
              rw [dist_eq_norm]
              ring
        _ ≤ (BF : ℝ) * (Cu : ℝ) * dist t s ^ (r : ℝ) +
              (Bu : ℝ) * (CF : ℝ) * dist t s ^ (r : ℝ) := by
          have hu' := hu.dist_le t s
          have hF' := hF.dist_le t s
          exact add_le_add
            (by
              calc
                ‖F t‖ * dist (u t) (u s) ≤
                    (BF : ℝ) * (Cu * dist t s ^ (r : ℝ)) := by
                  exact mul_le_mul (hFbound t) hu' (by positivity) (by positivity)
                _ = (BF : ℝ) * (Cu : ℝ) * dist t s ^ (r : ℝ) := by ring)
            (by
              calc
                ‖u s‖ * dist (F t) (F s) ≤
                    (Bu : ℝ) * (CF * dist t s ^ (r : ℝ)) := by
                  exact mul_le_mul (hubound s) hF' (by positivity) (by positivity)
                _ = (Bu : ℝ) * (CF : ℝ) * dist t s ^ (r : ℝ) := by ring)
        _ = ((BF * Cu + CF * Bu : ℝ≥0) : ℝ) *
              dist t s ^ (r : ℝ) := by
          simp only [NNReal.coe_add, NNReal.coe_mul]
          ring
    _ = ENNReal.ofReal (↑(BF * Cu + CF * Bu)) *
          ENNReal.ofReal (dist t s ^ (r : ℝ)) := by
      rw [ENNReal.ofReal_mul' (p := (BF * Cu + CF * Bu : ℝ))
        (by positivity : 0 ≤ dist t s ^ (r : ℝ))]
      congr 1

/-! The second term above uses the operator difference estimate. -/

theorem holderWith_clm_apply' 
    {r CF Cu BF Bu : ℝ≥0}
    {F : T → (E →L[ℝ] V)} {u : T → E}
    (hF : HolderWith CF r F) (hu : HolderWith Cu r u)
    (hFbound : ∀ t, ‖F t‖ ≤ BF) (hubound : ∀ t, ‖u t‖ ≤ Bu) :
    HolderWith (BF * Cu + CF * Bu) r (fun t => F t (u t)) :=
  holderWith_clm_apply hF hu hFbound hubound

/-! ## Finite sums and the second-order evaluator -/

omit [NormedSpace ℝ V] in
theorem HolderWith.finset_sum
    {ι : Type*} {s : Finset ι}
    {r : ℝ≥0} {C : ι → ℝ≥0} {f : ι → T → V}
    (hf : ∀ i ∈ s, HolderWith (C i) r (f i)) :
    HolderWith (∑ i ∈ s, C i) r (fun t => ∑ i ∈ s, f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [HolderWith]
  | @insert i s hi ih =>
      have hi' := hf i (by simp)
      have hs' : ∀ j ∈ s, HolderWith (C j) r (f j) := by
        intro j hj
        exact hf j (by simp [hj])
      convert hi'.add (ih hs') using 1
      · rfl
      · rw [Finset.sum_insert hi]
      · funext t
        rw [Finset.sum_insert hi]
        simp only [Pi.add_apply]

namespace VectorSecondOrderCoefficients

variable {T : Type*} [PseudoMetricSpace T]
  {ι : Type*} [Fintype ι] {V : Type*}
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]

theorem holderWith_variableSectionApplyJetArgs
    {r : ℝ≥0}
    (A : VectorSecondOrderCoefficients T ι V)
    (value : T → V) (first : ι → T → V) (second : ι → ι → T → V)
    (𝓥 𝓥₀ 𝓒 𝓒₀ : ℝ≥0)
    (𝓕 𝓕₀ : ι → ℝ≥0) (𝓢 𝓢₀ : ι → ι → ℝ≥0)
    (𝓐 𝓐₀ : ι → ι → ℝ≥0) (𝓑 𝓑₀ : ι → ℝ≥0)
    (hv : HolderWith 𝓥 r (fun t => value t))
    (hfirst : ∀ i, HolderWith (𝓕 i) r (fun t => first i t))
    (hsecond : ∀ i k, HolderWith (𝓢 i k) r (fun t => second i k t))
    (hA : ∀ i k, HolderWith (𝓐 i k) r (fun t => A.a t i k))
    (hB : ∀ i, HolderWith (𝓑 i) r (fun t => A.b t i))
    (hC : HolderWith 𝓒 r (fun t => A.c t))
    (hA_bound : ∀ i k t, ‖A.a t i k‖ ≤ 𝓐₀ i k)
    (hB_bound : ∀ i t, ‖A.b t i‖ ≤ 𝓑₀ i)
    (hC_bound : ∀ t, ‖A.c t‖ ≤ 𝓒₀)
    (hvalue_bound : ∀ t, ‖value t‖ ≤ 𝓥₀)
    (hfirst_bound : ∀ i t, ‖first i t‖ ≤ 𝓕₀ i)
    (hsecond_bound : ∀ i k t, ‖second i k t‖ ≤ 𝓢₀ i k) :
    HolderWith
      ((∑ i, ∑ k, (𝓐₀ i k * 𝓢 i k + 𝓐 i k * 𝓢₀ i k)) +
        (∑ i, (𝓑₀ i * 𝓕 i + 𝓑 i * 𝓕₀ i)) +
          (𝓒₀ * 𝓥 + 𝓒 * 𝓥₀)) r
      (fun t => A.applyJetArgs t (value t)
        (fun i => first i t) (fun i k => second i k t)) := by
  have hA' : ∀ i k, HolderWith
      (𝓐₀ i k * 𝓢 i k + 𝓐 i k * 𝓢₀ i k) r
      (fun t => A.a t i k (second i k t)) := by
    intro i k
    exact holderWith_clm_apply (hA i k) (hsecond i k)
      (hA_bound i k)
      (hsecond_bound i k)
  have hB' : ∀ i, HolderWith
      (𝓑₀ i * 𝓕 i + 𝓑 i * 𝓕₀ i) r
      (fun t => A.b t i (first i t)) := by
    intro i
    exact holderWith_clm_apply (hB i) (hfirst i)
      (hB_bound i)
      (hfirst_bound i)
  have hC' : HolderWith (𝓒₀ * 𝓥 + 𝓒 * 𝓥₀) r
      (fun t => A.c t (value t)) :=
    holderWith_clm_apply hC hv hC_bound hvalue_bound
  have hsumA := HolderWith.finset_sum (s := Finset.univ)
    (fun i hi => HolderWith.finset_sum (s := Finset.univ)
      (fun k hk => hA' i k))
  have hsumB := HolderWith.finset_sum (s := Finset.univ)
    (fun i hi => hB' i)
  have htotal := hsumA.add hsumB |>.add hC'
  convert htotal using 1
  · rfl
  · funext t
    simp [VectorSecondOrderCoefficients.applyJetArgs]

end VectorSecondOrderCoefficients

end
end Topping

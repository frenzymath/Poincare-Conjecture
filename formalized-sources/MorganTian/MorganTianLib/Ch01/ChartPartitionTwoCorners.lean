import MorganTianLib.Ch01.ChartPartitionCorner

open Set Metric Riemannian
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A chart partition with slack through two prescribed, distinct
interior times. Both corners occur as partition vertices. -/
theorem exists_chart_partition_slack_through_two [I.Boundaryless]
    {γ : ℝ → M} {O : Set ℝ} {a c d b : ℝ}
    (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hO : IsOpen O) (hKO : Icc a b ⊆ O) (hγ : ContinuousOn γ O) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (α : ℕ → M) (r : ℝ) (k l : ℕ),
      0 < N ∧ 0 < r ∧ τ 0 = a ∧ τ N = b ∧
      0 < k ∧ k < l ∧ l < N ∧ τ k = c ∧ τ l = d ∧
      (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc a b) ∧
      (∀ i < N, ∀ t ∈ Ioo (τ i - r) (τ (i + 1) + r),
        t ∈ O ∧ γ t ∈ (chartAt H (α i)).source ∧
          extChartAt I (α i) (γ t) ∈ interior (extChartAt I (α i)).target) := by
  have hIcc1 : Icc a d ⊆ Icc a b := Icc_subset_Icc le_rfl hdb.le
  have hIcc2 : Icc d b ⊆ Icc a b := Icc_subset_Icc (hac.trans hcd).le le_rfl
  obtain ⟨N₁, τ₁, α₁, r₁, k₁, hN₁, hr₁, hτ₁0, hτ₁N, hk₁0, hk₁N,
    hτ₁k, hmono₁, hmem₁, hpiece₁⟩ :=
    exists_chart_partition_slack_through (I := I) hac hcd hO (hIcc1.trans hKO) hγ
  obtain ⟨N₂, τ₂, α₂, r₂, hN₂, hr₂, hτ₂0, hτ₂N, -, hmono₂, hmem₂, -, hpiece₂⟩ :=
    exists_chart_partition_slack_interior (I := I) hdb hO (hIcc2.trans hKO) hγ
  set τ : ℕ → ℝ := fun i => if i ≤ N₁ then τ₁ i else τ₂ (i - N₁) with hτdef
  set α : ℕ → M := fun i => if i < N₁ then α₁ i else α₂ (i - N₁) with hαdef
  -- unfolding facts for `τ` and `α`
  have hτ_le : ∀ i, i ≤ N₁ → τ i = τ₁ i := by
    intro i hi; rw [hτdef]; exact if_pos hi
  have hτ_ge : ∀ i, N₁ ≤ i → τ i = τ₂ (i - N₁) := by
    intro i hi
    rcases eq_or_lt_of_le hi with heq | hlt
    · rw [← heq, hτ_le N₁ le_rfl, hτ₁N, Nat.sub_self, hτ₂0]
    · rw [hτdef]; exact if_neg (by omega)
  have hα_lt : ∀ i, i < N₁ → α i = α₁ i := by
    intro i hi; rw [hαdef]; exact if_pos hi
  have hα_ge : ∀ i, N₁ ≤ i → α i = α₂ (i - N₁) := by
    intro i hi; rw [hαdef]; exact if_neg (by omega)
  refine ⟨N₁ + N₂, τ, α, min r₁ r₂, k₁, N₁, by omega, lt_min hr₁ hr₂,
    (hτ_le 0 (Nat.zero_le _)).trans hτ₁0, ?_, hk₁0, hk₁N, by omega,
    (hτ_le k₁ hk₁N.le).trans hτ₁k, (hτ_le N₁ le_rfl).trans hτ₁N, ?_, ?_, ?_⟩
  · -- τ (N₁ + N₂) = b
    rw [hτ_ge (N₁ + N₂) (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hτ₂N]
  · -- strict monotonicity
    intro i
    by_cases h : i + 1 ≤ N₁
    · rw [hτ_le i (by omega), hτ_le (i + 1) h]
      exact hmono₁ i
    · have hiN : N₁ ≤ i := by omega
      rw [hτ_ge i hiN, hτ_ge (i + 1) (by omega)]
      have heq : i + 1 - N₁ = (i - N₁) + 1 := by omega
      rw [heq]
      exact hmono₂ (i - N₁)
  · -- membership
    intro i hi
    by_cases h : i ≤ N₁
    · rw [hτ_le i h]
      exact hIcc1 (hmem₁ i h)
    · rw [hτ_ge i (by omega)]
      exact hIcc2 (hmem₂ (i - N₁) (by omega))
  · -- the slack clause
    intro i hi t ht
    by_cases h : i < N₁
    · have e1 : τ i = τ₁ i := hτ_le i h.le
      have e2 : τ (i + 1) = τ₁ (i + 1) := hτ_le (i + 1) h
      have e3 : α i = α₁ i := hα_lt i h
      rw [e1, e2] at ht
      have hsub : Ioo (τ₁ i - min r₁ r₂) (τ₁ (i + 1) + min r₁ r₂)
          ⊆ Ioo (τ₁ i - r₁) (τ₁ (i + 1) + r₁) :=
        Ioo_subset_Ioo (by linarith [min_le_left r₁ r₂]) (by linarith [min_le_left r₁ r₂])
      rw [e3]
      exact hpiece₁ i h t (hsub ht)
    · have hiN : N₁ ≤ i := by omega
      have e1 : τ i = τ₂ (i - N₁) := hτ_ge i hiN
      have e2 : τ (i + 1) = τ₂ ((i - N₁) + 1) := by
        rw [hτ_ge (i + 1) (by omega)]
        congr 1
        omega
      have e3 : α i = α₂ (i - N₁) := hα_ge i hiN
      rw [e1, e2] at ht
      have hsub : Ioo (τ₂ (i - N₁) - min r₁ r₂) (τ₂ ((i - N₁) + 1) + min r₁ r₂)
          ⊆ Ioo (τ₂ (i - N₁) - r₂) (τ₂ ((i - N₁) + 1) + r₂) :=
        Ioo_subset_Ioo (by linarith [min_le_right r₁ r₂]) (by linarith [min_le_right r₁ r₂])
      have hiN2 : i - N₁ < N₂ := by omega
      rw [e3]
      exact hpiece₂ (i - N₁) hiN2 t (hsub ht)

end MorganTianLib
end

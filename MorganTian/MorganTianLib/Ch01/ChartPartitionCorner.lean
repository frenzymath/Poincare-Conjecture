/-
Copyright (c) 2026 Archon Horizon. All rights reserved.
Released under Apache 2.0 license.
-/
import MorganTianLib.Ch01.ChartPartitionSlack

/-!
# Poincaré Ch. 1 — a chart partition with slack through a prescribed interior time

`exists_chart_partition_slack_interior` (`Ch01/ChartPartitionSlack.lean`) partitions `[a, b]`
into a **uniform** grid with slack `r`; nothing forces the grid to land on any prescribed interior
point. The assembly of the second variation (blueprint node
`prop:minimal-geodesic-no-conjugate`) needs strictly more: the comparison test field built there
has a **corner** at the conjugate time `c ∈ (a, b)` — it is built separately (and only) smoothly
on `[a, c]` and on `[c, b]`, matching continuously but *not* differentiably across `c` — so the
chart partition driving the piecewise second-variation computation must have `c` itself as one of
its partition points `τ k`, while still allowing genuinely independent charts and slack radii on
the two sides of the corner.

## The construction

Apply `exists_chart_partition_slack_interior` **twice**: once to `[a, c]` and once to `[c, b]`,
both against the *same* open set `O ⊇ Icc a b ⊇ Icc a c ∪ Icc c b` and the same continuous `γ`.
This is the key point: the slack clause of each call is stated on an *enlarged open* interval
that already sticks out past the shared endpoint `c` of its own sub-partition, so no gluing or
continuity argument at `c` is needed — the two certificates simply overlap there.

Concatenating the two partitions — indices `0, …, N₁` from the left partition (landing on `c` at
index `N₁`) followed by indices `N₁+1, …, N₁+N₂` from the right partition (re-indexed by
subtracting `N₁`) — gives a single strictly increasing partition of `[a, b]` through `c`, with
`k := N₁` the index where `τ k = c`, and slack `r := min r₁ r₂` (the smaller of the two slacks,
so that the enlarged piece of *either* sub-partition is still covered by its own certificate).
-/

open Set Metric Riemannian
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** **Chart partition with slack, through a prescribed interior time.**
Given a curve `γ` continuous on an open `O ⊇ [a, b]` and a time `c` strictly between `a` and `b`,
there is a strictly increasing partition `a = τ 0 < ⋯ < τ N = b` of `[a, b]`, passing through `c`
at some interior index `k` (`τ k = c`, `0 < k < N`), chart centres `α i`, and a single slack
`r > 0` such that every enlarged open piece `Ioo (τ i - r) (τ (i+1) + r)` is carried by `γ` into
the `i`-th chart source, with chart image in the interior of the chart target.

Obtained by applying `exists_chart_partition_slack_interior` on `[a, c]` and on `[c, b]` and
concatenating the two partitions at `c`; see the module docstring for why the slack survives the
concatenation. -/
theorem exists_chart_partition_slack_through [I.Boundaryless] {γ : ℝ → M} {O : Set ℝ} {a c b : ℝ}
    (hac : a < c) (hcb : c < b) (hO : IsOpen O) (hKO : Icc a b ⊆ O) (hγ : ContinuousOn γ O) :
    ∃ (N : ℕ) (τ : ℕ → ℝ) (α : ℕ → M) (r : ℝ) (k : ℕ),
      0 < N ∧ 0 < r ∧ τ 0 = a ∧ τ N = b ∧
      0 < k ∧ k < N ∧ τ k = c ∧
      (∀ i, τ i < τ (i + 1)) ∧
      (∀ i ≤ N, τ i ∈ Icc a b) ∧
      (∀ i < N, ∀ t ∈ Ioo (τ i - r) (τ (i + 1) + r),
        t ∈ O ∧ γ t ∈ (chartAt H (α i)).source ∧
          extChartAt I (α i) (γ t) ∈ interior (extChartAt I (α i)).target) := by
  have hIcc1 : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb.le
  have hIcc2 : Icc c b ⊆ Icc a b := Icc_subset_Icc hac.le le_rfl
  have hKO1 : Icc a c ⊆ O := hIcc1.trans hKO
  have hKO2 : Icc c b ⊆ O := hIcc2.trans hKO
  obtain ⟨N₁, τ₁, α₁, r₁, hN₁, hr₁, hτ₁0, hτ₁N, -, hmono₁, hmem₁, -, hpiece₁⟩ :=
    exists_chart_partition_slack_interior (I := I) hac hO hKO1 hγ
  obtain ⟨N₂, τ₂, α₂, r₂, hN₂, hr₂, hτ₂0, hτ₂N, -, hmono₂, hmem₂, -, hpiece₂⟩ :=
    exists_chart_partition_slack_interior (I := I) hcb hO hKO2 hγ
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
  refine ⟨N₁ + N₂, τ, α, min r₁ r₂, N₁, by omega, lt_min hr₁ hr₂,
    (hτ_le 0 (Nat.zero_le _)).trans hτ₁0, ?_, hN₁, by omega,
    (hτ_le N₁ le_rfl).trans hτ₁N, ?_, ?_, ?_⟩
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

#print axioms MorganTianLib.exists_chart_partition_slack_through

end

import MorganTianLib.Ch01.FinitePieceIndexForm
import MorganTianLib.Ch01.ChartPartitionTwoCorners

/-! # The index form of three matching smooth pieces -/

open Set Filter Riemannian Riemannian.Geodesic Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [CompleteSpace E] [T2Space (TangentBundle I M)]
local notation "𝔼" => EuclideanSpace ℝ (Fin (finrank ℝ E))

/-- **Math.** A minimizing geodesic has nonnegative index form on a field
with two corners. Each smooth piece extends to a neighborhood of the whole
geodesic interval; only its values on its own subinterval enter the integral. -/
theorem indexForm_threePieces_nonneg_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b c d : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W₀ W₁ W₂ : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b) (hc : 0 < c) (hcd : c < d) (hd : d < 1)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) = if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    (hW₀ : ContDiffOn ℝ 3 W₀ (Ioo a b))
    (hW₁ : ContDiffOn ℝ 3 W₁ (Ioo a b))
    (hW₂ : ContDiffOn ℝ 3 W₂ (Ioo a b))
    (hW0 : W₀ 0 = 0) (hW1 : W₂ 1 = 0)
    (hmatchc : W₀ c = W₁ c) (hmatchd : W₁ d = W₂ d) :
    0 ≤ indexForm (frameCurvOp (I := I) g γ e) 0 c W₀ (deriv W₀) W₀ (deriv W₀)
      + indexForm (frameCurvOp (I := I) g γ e) c d W₁ (deriv W₁) W₁ (deriv W₁)
      + indexForm (frameCurvOp (I := I) g γ e) d 1 W₂ (deriv W₂) W₂ (deriv W₂) := by
  classical
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo a b := fun t ht =>
    ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  obtain ⟨N, τ, β, r, k, l, hN, hr, hτ0, hτN, hk0, hkl, hlN, hτk, hτl,
    hmono, hτmem, hslack⟩ :=
    exists_chart_partition_slack_through_two (I := I) hc hcd hd isOpen_Ioo hsub
      (fun t ht => (hγc t (Ioo_subset_Icc_self ht)).continuousWithinAt)
  let W : ℕ → ℝ → 𝔼 := fun i => if i < k then W₀ else if i < l then W₁ else W₂
  let Wg := glueCoeff c W₀ (glueCoeff d W₁ W₂)
  have hsm : StrictMono τ := strictMono_nat_of_lt_succ hmono
  have hW : ∀ i < N, ContDiffOn ℝ 3 (W i) (Ioo a b) := by
    intro i _
    dsimp [W]
    split_ifs <;> assumption
  have hmatch : ∀ i < N, ∀ t ∈ Icc (τ i) (τ (i + 1)), Wg t = W i t := by
    intro i _ t ht
    dsimp [Wg, W]
    by_cases hik : i < k
    · rw [if_pos hik, glueCoeff_of_le (ht.2.trans (hτk ▸ hsm.monotone hik))]
    · rw [if_neg hik]
      have hct : c ≤ t := (hτk ▸ hsm.monotone (le_of_not_gt hik)).trans ht.1
      have hout : glueCoeff c W₀ (glueCoeff d W₁ W₂) t = glueCoeff d W₁ W₂ t := by
        rcases hct.eq_or_lt with heq | hlt
        · subst t
          rw [glueCoeff_of_le le_rfl, glueCoeff_of_le hcd.le, hmatchc]
        · exact glueCoeff_of_lt hlt
      rw [hout]
      by_cases hil : i < l
      · rw [if_pos hil, glueCoeff_of_le (ht.2.trans (hτl ▸ hsm.monotone hil))]
      · rw [if_neg hil]
        have hdt : d ≤ t := (hτl ▸ hsm.monotone (le_of_not_gt hil)).trans ht.1
        rcases hdt.eq_or_lt with heq | hlt
        · subst t
          rw [glueCoeff_of_le le_rfl, hmatchd]
        · exact glueCoeff_of_lt hlt
  have hnn := sum_indexForm_nonneg_of_minimizing (I := I) g hg ha hb hN hr hmono
    hτ0 hτN hτmem hgeo hγc hPar horth hmin hW hmatch
    (by simpa [Wg, glueCoeff_of_le hc.le] using hW0)
    (by simpa [Wg, glueCoeff_of_lt (hc.trans (hcd.trans hd)),
      glueCoeff_of_lt (hcd.trans hd), glueCoeff_of_lt hd] using hW1) hslack
  let R := frameCurvOp (I := I) g γ e
  let F := fun (V : ℝ → 𝔼) => indexIntegrand R V (deriv V) V (deriv V)
  have hcont (V : ℝ → 𝔼) (hV : ContDiffOn ℝ 3 V (Ioo a b)) :
      ContinuousOn (F V) (Ioo a b) :=
    continuousOn_indexIntegrand
      ((continuousOn_frameCurvOp hPar hgeo hγc).mono Ioo_subset_Icc_self)
      hV.continuousOn ((hV.deriv_of_isOpen (m := 2) isOpen_Ioo (by norm_num)).continuousOn)
      hV.continuousOn ((hV.deriv_of_isOpen (m := 2) isOpen_Ioo (by norm_num)).continuousOn)
  have hint (V : ℝ → 𝔼) (hV : ContDiffOn ℝ 3 V (Ioo a b)) (i : ℕ) (hi : i < N) :
      IntervalIntegrable (F V) volume (τ i) (τ (i + 1)) := by
    apply ContinuousOn.intervalIntegrable ((hcont V hV).mono ?_)
    rw [uIcc_of_le (hmono i).le]
    exact fun t ht => hsub ⟨(hτmem i hi.le).1.trans ht.1,
      ht.2.trans (hτmem (i + 1) hi).2⟩
  let A := fun i => indexForm R (τ i) (τ (i + 1))
    (W i) (deriv (W i)) (W i) (deriv (W i))
  have hs0 : ∑ i ∈ Finset.range k, A i = indexForm R 0 c W₀ (deriv W₀) W₀ (deriv W₀) := by
    calc
      _ = ∑ i ∈ Finset.range k, ∫ t in (τ i)..(τ (i + 1)), F W₀ t := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [A, W, if_pos (Finset.mem_range.mp hi), indexForm, F]
      _ = _ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals
          (fun i hi => hint W₀ hW₀ i (hi.trans (hkl.trans hlN))), hτ0, hτk]
        rfl
  have hs1 : ∑ i ∈ Finset.Ico k l, A i = indexForm R c d W₁ (deriv W₁) W₁ (deriv W₁) := by
    calc
      _ = ∑ i ∈ Finset.Ico k l, ∫ t in (τ i)..(τ (i + 1)), F W₁ t := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        simp only [A, W, if_neg (not_lt.mpr hi'.1), if_pos hi'.2, indexForm, F]
      _ = _ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals_Ico hkl.le
          (fun i hi => hint W₁ hW₁ i (hi.2.trans hlN)), hτk, hτl]
        rfl
  have hs2 : ∑ i ∈ Finset.Ico l N, A i = indexForm R d 1 W₂ (deriv W₂) W₂ (deriv W₂) := by
    calc
      _ = ∑ i ∈ Finset.Ico l N, ∫ t in (τ i)..(τ (i + 1)), F W₂ t := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_Ico.mp hi
        simp only [A, W, if_neg (not_lt.mpr (hkl.le.trans hi'.1)),
          if_neg (not_lt.mpr hi'.1), indexForm, F]
      _ = _ := by
        rw [intervalIntegral.sum_integral_adjacent_intervals_Ico hlN.le
          (fun i hi => hint W₂ hW₂ i hi.2), hτl, hτN]
        rfl
  change 0 ≤ ∑ i ∈ Finset.range N, A i at hnn
  have hsplit : ∑ i ∈ Finset.range N, A i =
      (∑ i ∈ Finset.range k, A i) + (∑ i ∈ Finset.Ico k l, A i) +
        ∑ i ∈ Finset.Ico l N, A i := by
    simp only [Finset.range_eq_Ico]
    rw [Finset.sum_Ico_consecutive A (Nat.zero_le k) hkl.le,
      Finset.sum_Ico_consecutive A (Nat.zero_le l) hlN.le]
  rwa [hsplit, hs0, hs1, hs2] at hnn

end MorganTianLib

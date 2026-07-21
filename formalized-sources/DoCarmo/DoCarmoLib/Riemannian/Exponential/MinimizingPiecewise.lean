import DoCarmoLib.Riemannian.Exponential.Minimizing

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

/-!
# Radial geodesics minimize among piecewise differentiable curves
(do Carmo Ch. 3, Prop. 3.6, piecewise competitors)

do Carmo's Proposition 3.6 compares the radial geodesic against **piecewise**
differentiable curves. This file extends the smoothed-radius comparison of
`DoCarmoLib.Riemannian.Exponential.Minimizing` from a single differentiable
piece to a partition `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n`: the `g_p`-radius gain telescopes
over the pieces, each estimated by `gauss_radius_comparison` (whose interior
one-sided form is exactly what a corner of a piecewise curve needs).

## Main statements

* `gauss_radius_comparison_piecewise` — the telescoped radius comparison:
  `√⟨w(τ n)⟩_p − √⟨w(τ 0)⟩_p ≤ ∑ i, ∫_{τ i}^{τ(i+1)} |ċ|`, abstract in the
  chart reading `f` of the exponential map.
* `gauss_radius_reach_piecewise` — the piecewise reach estimate: the
  `g_p`-radius reached at **any** time `t₁` is dominated by the total length
  (do Carmo's escape case for piecewise competitors).
* `exists_expMap_ray_length_ball` — the radial geodesic `t ↦ exp_p(t v)`,
  `t ∈ [0,1]`, has chart-read length `√⟨v, v⟩_p`.
* `exists_minimizing_geodesic_ball_piecewise` — **the minimizing property
  against piecewise competitors, polar form**: for every partition of `[0,1]`
  and every competing polar lift `w`, continuous on `[0,1]` and `C¹` on each
  piece, `ℓ(t ↦ exp_p(t v)) ≤ ∑ i, ℓ_{[τ i, τ(i+1)]}(exp_p ∘ w)`.
* `exists_minimizing_geodesic_normal_ball_piecewise` — the same for an
  arbitrary piecewise differentiable curve `c : [0,1] → B` in a normal ball,
  with per-piece one-sided differentiable chart readings (do Carmo Ch. 3,
  Prop. 3.6, the case `c([0,1]) ⊂ B`, piecewise competitors).
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Exponential

/-! ## Partition combinatorics -/

/-- A finite partition `τ 0 ≤ τ 1 ≤ ⋯ ≤ τ n` is monotone below `n`. -/
theorem partition_le {n : ℕ} {τ : ℕ → ℝ} (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    {i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) : τ i ≤ τ j := by
  induction j with
  | zero => exact Nat.le_zero.mp hij ▸ le_rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · exact le_rfl
    · exact (ih (Nat.lt_succ_iff.mp hik) ((Nat.le_succ k).trans hjn)).trans
        (hτ k (Nat.lt_of_succ_le hjn))

/-- Every time in the span of a partition lies in one of its pieces. -/
theorem exists_partition_piece_mem {τ : ℕ → ℝ} {n : ℕ}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1)) (hn : 0 < n) {t : ℝ}
    (ht : t ∈ Icc (τ 0) (τ n)) :
    ∃ k < n, t ∈ Icc (τ k) (τ (k + 1)) := by
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact ⟨0, Nat.zero_lt_one, ht⟩
    · rcases le_total t (τ m) with hle | hge
      · obtain ⟨k, hk, hmem⟩ :=
          ih (fun i hi => hτ i (hi.trans m.lt_succ_self)) hm ⟨ht.1, hle⟩
        exact ⟨k, hk.trans m.lt_succ_self, hmem⟩
      · exact ⟨m, m.lt_succ_self, hge, ht.2⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

open Riemannian.Geodesic

/-! ## The telescoped radius comparison -/

/-- **Math.** **The piecewise smoothed-radius comparison** (do Carmo Ch. 3,
the integral estimate (2) in the proof of Prop. 3.6, for piecewise
differentiable competitors), abstract in the chart reading `f` of the
exponential map. For a partition `τ 0 ≤ ⋯ ≤ τ n` of the time interval and a
path `w`, continuous on `[τ 0, τ n]` and differentiable on the interior of
each piece with derivative `w' i` extending continuously to the closed piece,
the total `g_p`-radius gain telescopes over the pieces:

`√⟨w(τ n)⟩_p − √⟨w(τ 0)⟩_p ≤ ∑ i, ∫_{τ i}^{τ(i+1)} √⟨ċ(t), ċ(t)⟩_{c(t)} dt`,

each piece being estimated by `gauss_radius_comparison`. -/
theorem gauss_radius_comparison_piecewise (g : RiemannianMetric I M) (p : M)
    (f : E → E) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {n : ℕ} {τ : ℕ → ℝ} {w : ℝ → E} {w' : ℕ → ℝ → E}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hw_cont : ContinuousOn w (Icc (τ 0) (τ n)))
    (hw : ∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)), HasDerivAt w (w' i t) t)
    (hw' : ∀ i < n, ContinuousOn (w' i) (Icc (τ i) (τ (i + 1))))
    (hwball : ∀ t ∈ Icc (τ 0) (τ n), ‖w t‖ < ρ) :
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w (τ n)) (w (τ n)))
      - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w (τ 0)) (w (τ 0)))
      ≤ ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
          Real.sqrt (chartMetricInner (I := I) g p (f (w t))
            (fderiv ℝ f (w t) (w' i t)) (fderiv ℝ f (w t) (w' i t))) := by
  classical
  set F : ℕ → ℝ := fun i => Real.sqrt
    (chartMetricInner (I := I) g p (extChartAt I p p) (w (τ i)) (w (τ i))) with hFdef
  calc F n - F 0
      = ∑ i ∈ Finset.range n, (F (i + 1) - F i) := (Finset.sum_range_sub F n).symm
    _ ≤ ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
          Real.sqrt (chartMetricInner (I := I) g p (f (w t))
            (fderiv ℝ f (w t) (w' i t)) (fderiv ℝ f (w t) (w' i t))) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hin : i < n := Finset.mem_range.mp hi
        have hsub : Icc (τ i) (τ (i + 1)) ⊆ Icc (τ 0) (τ n) :=
          Icc_subset_Icc (partition_le hτ (Nat.zero_le i) hin.le)
            (partition_le hτ hin le_rfl)
        exact gauss_radius_comparison (I := I) g p f htgt hC1 hradial (hτ i hin)
          (hw_cont.mono hsub) (hw i hin) (hw' i hin)
          (fun t ht => hwball t (hsub ht))

/-- **Math.** **The piecewise reach estimate** (do Carmo Ch. 3, the escape
case in the proof of Prop. 3.6, piecewise competitors): under the hypotheses
of `gauss_radius_comparison_piecewise`, the `g_p`-radius reached by the polar
lift at **any** time `t₁` is dominated by the total length of the composed
curve. The time `t₁` lies in some piece `k`; the radius gain up to `t₁` is the
telescoped gain over the first `k` pieces plus the reach inside piece `k`, and
the remaining pieces contribute nonnegatively. -/
theorem gauss_radius_reach_piecewise (g : RiemannianMetric I M) (p : M)
    (f : E → E) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {n : ℕ} {τ : ℕ → ℝ} {w : ℝ → E} {w' : ℕ → ℝ → E}
    (hτ : ∀ i < n, τ i ≤ τ (i + 1))
    (hw_cont : ContinuousOn w (Icc (τ 0) (τ n)))
    (hw : ∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)), HasDerivAt w (w' i t) t)
    (hw' : ∀ i < n, ContinuousOn (w' i) (Icc (τ i) (τ (i + 1))))
    (hwball : ∀ t ∈ Icc (τ 0) (τ n), ‖w t‖ < ρ)
    (hn : 0 < n) {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (τ 0) (τ n)) :
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t₁) (w t₁))
      - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w (τ 0)) (w (τ 0)))
      ≤ ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
          Real.sqrt (chartMetricInner (I := I) g p (f (w t))
            (fderiv ℝ f (w t) (w' i t)) (fderiv ℝ f (w t) (w' i t))) := by
  classical
  obtain ⟨k, hk, hmem⟩ := exists_partition_piece_mem hτ hn ht₁
  set F : ℕ → ℝ := fun i => Real.sqrt
    (chartMetricInner (I := I) g p (extChartAt I p p) (w (τ i)) (w (τ i))) with hFdef
  set L : ℕ → ℝ := fun i => ∫ t in τ i..τ (i + 1),
    Real.sqrt (chartMetricInner (I := I) g p (f (w t))
      (fderiv ℝ f (w t) (w' i t)) (fderiv ℝ f (w t) (w' i t))) with hLdef
  -- each piece has nonnegative length
  have hL_nonneg : ∀ i < n, 0 ≤ L i := by
    intro i hi
    refine intervalIntegral.integral_nonneg (hτ i hi) fun t _ => Real.sqrt_nonneg _
  -- pieces of the partition sit inside the span
  have hsub : ∀ i < n, Icc (τ i) (τ (i + 1)) ⊆ Icc (τ 0) (τ n) := fun i hi =>
    Icc_subset_Icc (partition_le hτ (Nat.zero_le i) hi.le) (partition_le hτ hi le_rfl)
  -- telescoped gain over the first `k` pieces
  have hfirst : F k - F 0 ≤ ∑ i ∈ Finset.range k, L i := by
    have hτ' : ∀ i < k, τ i ≤ τ (i + 1) := fun i hi => hτ i (hi.trans hk)
    have hsubk : Icc (τ 0) (τ k) ⊆ Icc (τ 0) (τ n) :=
      Icc_subset_Icc le_rfl (partition_le hτ hk.le le_rfl)
    exact gauss_radius_comparison_piecewise (I := I) g p f htgt hC1 hradial hτ'
      (hw_cont.mono hsubk) (fun i hi => hw i (hi.trans hk))
      (fun i hi => hw' i (hi.trans hk)) (fun t ht => hwball t (hsubk ht))
  -- reach inside piece `k`
  have hlast : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
      (w t₁) (w t₁)) - F k ≤ L k :=
    gauss_radius_reach (I := I) g p f htgt hC1 hradial
      (hw_cont.mono (hsub k hk)) (hw k hk) (hw' k hk)
      (fun t ht => hwball t (hsub k hk ht)) hmem
  -- assemble: the first `k+1` pieces already dominate, the rest are nonnegative
  have hk1 : ∑ i ∈ Finset.range (k + 1), L i ≤ ∑ i ∈ Finset.range n, L i := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.succ_le_of_lt hk)) fun i hi _ => ?_
    exact hL_nonneg i (Finset.mem_range.mp hi)
  calc Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t₁) (w t₁)) - F 0
      = (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t₁) (w t₁))
          - F k) + (F k - F 0) := by ring
    _ ≤ L k + ∑ i ∈ Finset.range k, L i := add_le_add hlast hfirst
    _ = ∑ i ∈ Finset.range (k + 1), L i := by rw [Finset.sum_range_succ]; ring
    _ ≤ ∑ i ∈ Finset.range n, L i := hk1

/-! ## The minimizing property against piecewise competitors -/

/-- **Math.** **The radial geodesic has chart-read length `√⟨v, v⟩_p`**
(do Carmo Ch. 3, `ℓ(γ) = r(1)` in the proof of Prop. 3.6, unnormalized form):
there is `ρ > 0` such that for `‖v‖ < ρ` the chart-read length of
`t ↦ exp_p(t v)`, `t ∈ [0, 1]`, equals `√⟨v, v⟩_p`. Integration of the
constant ray speed `exists_expMap_ray_speed_ball`. -/
theorem exists_expMap_ray_length_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v : E, ‖v‖ < ρ →
        (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)))
          = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
  classical
  obtain ⟨ρ, hρ, hdom, hsrc, hray⟩ := exists_expMap_ray_speed_ball (I := I) g p
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  intro v hv
  have hEq : EqOn (fun t : ℝ => Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
        (fderiv ℝ (fun u : E =>
          extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
        (fderiv ℝ (fun u : E =>
          extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)))
      (fun _ : ℝ => Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v))
      (uIcc (0 : ℝ) 1) := by
    intro t ht
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    exact congrArg Real.sqrt (hray v hv t ht)
  rw [intervalIntegral.integral_congr hEq, intervalIntegral.integral_const]
  norm_num

/-- **Math.** **Radial geodesics minimize against piecewise competitors on the
Gauss ball** (do Carmo Ch. 3, Proposition 3.6, polar form, piecewise
competitors). There is `ρ > 0` such that for every `v` with `‖v‖ < ρ`, every
partition `0 = τ 0 ≤ ⋯ ≤ τ n = 1` and every competing polar lift
`w : [0, 1] → B_ρ(0) ⊂ T_pM` — continuous, differentiable on the interior of
each piece with derivative `w' i` extending continuously to the closed piece —
with `w(0) = 0`, `w(1) = v`, the chart-read length of the radial geodesic
`γ(t) = exp_p(t v)` is at most the total chart-read length of
`c(t) = exp_p(w(t))`:

`ℓ(γ) = √⟨v, v⟩_p ≤ ∑ i, ∫_{τ i}^{τ(i+1)} √⟨ċ, ċ⟩ dt = ℓ(c)`. -/
theorem exists_minimizing_geodesic_ball_piecewise (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ v : E, ‖v‖ < ρ → ∀ (n : ℕ) (τ : ℕ → ℝ) (w : ℝ → E) (w' : ℕ → ℝ → E),
        τ 0 = 0 → τ n = 1 → (∀ i < n, τ i ≤ τ (i + 1)) →
        ContinuousOn w (Icc (0 : ℝ) 1) →
        (∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)), HasDerivAt w (w' i t) t) →
        (∀ i < n, ContinuousOn (w' i) (Icc (τ i) (τ (i + 1)))) →
        (∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ) →
        w 0 = 0 → w 1 = v →
        (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)
            (fderiv ℝ (fun u : E =>
              extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (t • v) v)))
          ≤ ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
              Real.sqrt (chartMetricInner (I := I) g p
                (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
                (fderiv ℝ (fun u : E =>
                  extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t)
                  (w' i t))
                (fderiv ℝ (fun u : E =>
                  extChartAt I p (expMap (I := I) g p (u : TangentSpace I p))) (w t)
                  (w' i t)))) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hradial⟩ :=
    exists_gauss_radial_lower_bound_ball (I := I) g p
  obtain ⟨ρ₂, hρ₂, hdom₂, hsrc₂, hC1⟩ :=
    exists_contDiffOn_extChartAt_expMap_ball (I := I) g p
  obtain ⟨ρ₃, hρ₃, hdom₃, hsrc₃, hraylen⟩ :=
    exists_expMap_ray_length_ball (I := I) g p
  set ρ : ℝ := min ρ₁ (min ρ₂ ρ₃) with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ (lt_min hρ₂ hρ₃)
  have hρρ₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρρ₂ : ρ ≤ ρ₂ := (min_le_right _ _).trans (min_le_left _ _)
  have hρρ₃ : ρ ≤ ρ₃ := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, fun u hu => hdom₁ u (hu.trans_le hρρ₁),
    fun u hu => hsrc₁ u (hu.trans_le hρρ₁), ?_⟩
  intro v hv n τ w w' hτ0 hτn hτ hwc hw hw' hwball hw0 hw1
  rw [hraylen v (hv.trans_le hρρ₃)]
  have hcomp := gauss_radius_comparison_piecewise (I := I) g p
    (fun u : E => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
    (ρ := ρ)
    (fun u hu => (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc₁ u (hu.trans_le hρρ₁)))
    (hC1.mono (ball_subset_ball hρρ₂))
    (fun v' ξ hv' => hradial v' ξ (hv'.trans_le hρρ₁))
    hτ (by rw [hτ0, hτn]; exact hwc) hw hw'
    (by rw [hτ0, hτn]; exact hwball)
  rw [hτ0, hτn, hw0, hw1, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero]
    at hcomp
  exact hcomp

/-- **Math.** **Radial geodesics minimize among piecewise differentiable
curves in a normal ball** (do Carmo Ch. 3, Proposition 3.6, the case
`c([0,1]) ⊂ B`, piecewise competitors). There is `ε > 0` such that `exp_p` is
injective on `B_ε(0) ⊂ T_pM` with open image (so `B = exp_p(B_ε(0))` is a
normal ball), and for every `v` with `‖v‖ < ε`, every partition
`0 = τ 0 < ⋯ < τ n = 1`, and every continuous curve `c : [0, 1] → B` from `p`
to `exp_p(v)` whose chart reading `t ↦ φ_p(c(t))` is differentiable on each
closed piece in the one-sided sense (`HasDerivWithinAt`, do Carmo's piecewise
differentiability) with piece derivatives `u' i` continuous on the closed
piece, the chart-read length of the radial geodesic `γ(t) = exp_p(t v)` is at
most the total chart-read length of `c`:

`ℓ(γ) ≤ ∑ i, ∫_{τ i}^{τ(i+1)} √⟨u'ᵢ(t), u'ᵢ(t)⟩_{c(t)} dt = ℓ(c)`. -/
theorem exists_minimizing_geodesic_normal_ball_piecewise
    (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ u : E, ‖u‖ < ε → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ε →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun z : E => expMap (I := I) g p (z : TangentSpace I p))
        (ball (0 : E) ε) ∧
      IsOpen ((fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
        ball (0 : E) ε) ∧
      (∀ v : E, ‖v‖ < ε →
        ∀ (c : ℝ → M) (n : ℕ) (τ : ℕ → ℝ) (u' : ℕ → ℝ → E),
        τ 0 = 0 → τ n = 1 → (∀ i < n, τ i < τ (i + 1)) →
        ContinuousOn c (Icc (0 : ℝ) 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, c t ∈
          (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
            ball (0 : E) ε) →
        (∀ i < n, ∀ t ∈ Icc (τ i) (τ (i + 1)),
          HasDerivWithinAt (fun s : ℝ => extChartAt I p (c s)) (u' i t)
            (Icc (τ i) (τ (i + 1))) t) →
        (∀ i < n, ContinuousOn (u' i) (Icc (τ i) (τ (i + 1)))) →
        c 0 = p → c 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
            (extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
            (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (t • v) v)
            (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (t • v) v)))
          ≤ ∑ i ∈ Finset.range n, ∫ t in τ i..τ (i + 1),
              Real.sqrt (chartMetricInner (I := I) g p
                (extChartAt I p (c t)) (u' i t) (u' i t))) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρ, hρ, hdomρ, hsrcρ, hmin⟩ :=
    exists_minimizing_geodesic_ball_piecewise (I := I) g p
  obtain ⟨ρe, hρe, hdome, hsrce, hequiv⟩ :=
    exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun z => extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)) with hfdef
  set ε : ℝ := min ε₁ (min ρ ρe) with hεdef
  have hε : 0 < ε := lt_min hε₁ (lt_min hρ hρe)
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hερ : ε ≤ ρ := (min_le_right _ _).trans (min_le_left _ _)
  have hερe : ε ≤ ρe := (min_le_right _ _).trans (min_le_right _ _)
  -- the chart image of the `ε`-ball is open
  have hopen_f : IsOpen (f '' ball (0 : E) ε) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨D', hD'⟩ := hequiv z ((mem_ball_zero_iff.mp hz).trans_le hερe)
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (isOpen_ball.mem_nhds hz)
  -- the image of `exp_p` is the chart pull-back of the image of `f`
  have himg : (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
        ball (0 : E) ε
      = (extChartAt I p).source ∩ extChartAt I p ⁻¹' (f '' ball (0 : E) ε) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hsrcz : expMap (I := I) g p (z : TangentSpace I p) ∈
          (chartAt H p).source :=
        hsrc₁ z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
      exact ⟨by rw [extChartAt_source]; exact hsrcz, ⟨z, hz, rfl⟩⟩
    · rintro ⟨hxsrc, ⟨z, hz, hfz⟩⟩
      refine ⟨z, hz, ?_⟩
      have hsrcz : expMap (I := I) g p (z : TangentSpace I p) ∈
          (extChartAt I p).source := by
        rw [extChartAt_source]
        exact hsrc₁ z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
      exact (extChartAt I p).injOn hsrcz hxsrc hfz
  have hopen_exp : IsOpen ((fun z : E => expMap (I := I) g p
      (z : TangentSpace I p)) '' ball (0 : E) ε) := by
    rw [himg]
    exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
      (isOpen_extChartAt_source p) hopen_f
  refine ⟨ε, hε, fun u hu => hdom₁ u (hu.trans_le hεε₁),
    fun u hu => hsrc₁ u (hu.trans_le hεε₁),
    hinj₁.mono (ball_subset_ball hεε₁), hopen_exp, ?_⟩
  intro v hv c n τ u' hτ0 hτn hτs hc_cont hcball hu hu'_cont hc0 hc1
  have hτ : ∀ i < n, τ i ≤ τ (i + 1) := fun i hi => (hτs i hi).le
  -- pieces of the partition sit inside `[0, 1]`
  have hpiece_sub : ∀ i < n, Icc (τ i) (τ (i + 1)) ⊆ Icc (0 : ℝ) 1 := by
    intro i hi
    refine Icc_subset_Icc ?_ ?_
    · rw [← hτ0]; exact partition_le hτ (Nat.zero_le i) hi.le
    · rw [← hτn]; exact partition_le hτ hi le_rfl
  -- the chart reading of the curve, and its polar lift through `finv`
  set u : ℝ → E := fun t => extChartAt I p (c t) with hudef
  set w : ℝ → E := fun t => finv (u t) with hwdef
  -- pointwise polar description
  have hpolar : ∀ t ∈ Icc (0 : ℝ) 1, w t ∈ ball (0 : E) ε ∧ f (w t) = u t := by
    intro t ht
    obtain ⟨z, hz, hcz⟩ := hcball t ht
    have hwz : w t = z := by
      rw [hwdef]
      show finv (u t) = z
      rw [hudef]
      show finv (extChartAt I p (c t)) = z
      rw [← hcz]
      exact hlinv z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
    constructor
    · rw [hwz]; exact hz
    · rw [hwz, hfdef]
      show extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)) = u t
      rw [hudef]
      show _ = extChartAt I p (c t)
      rw [← hcz]
  have hu_mem : ∀ t ∈ Icc (0 : ℝ) 1, u t ∈ f '' ball (0 : E) ε := by
    intro t ht
    obtain ⟨hwball, hfw⟩ := hpolar t ht
    exact ⟨w t, hwball, hfw⟩
  -- the curve stays in the chart source
  have hc_src : ∀ t ∈ Icc (0 : ℝ) 1, c t ∈ (extChartAt I p).source := by
    intro t ht
    obtain ⟨z, hz, hcz⟩ := hcball t ht
    rw [extChartAt_source, ← hcz]
    exact hsrc₁ z ((mem_ball_zero_iff.mp hz).trans_le hεε₁)
  -- continuity of the chart reading and of the polar lift
  have hu_cont : ContinuousOn u (Icc (0 : ℝ) 1) :=
    (continuousOn_extChartAt (I := I) p).comp hc_cont hc_src
  have hsub : f '' ball (0 : E) ε ⊆ f '' ball (0 : E) ε₁ :=
    image_mono (ball_subset_ball hεε₁)
  have hfinvC1' : ContDiffOn ℝ 1 finv (f '' ball (0 : E) ε) := hfinvC1.mono hsub
  have hw_cont : ContinuousOn w (Icc (0 : ℝ) 1) :=
    hfinvC1'.continuousOn.comp hu_cont hu_mem
  have hfinv_diff : ∀ y ∈ f '' ball (0 : E) ε,
      HasFDerivAt finv (fderiv ℝ finv y) y := by
    intro y hy
    exact ((hfinvC1'.contDiffAt (hopen_f.mem_nhds hy)).differentiableAt
      one_ne_zero).hasFDerivAt
  -- the polar lift is differentiable inside each piece
  have hw_deriv : ∀ i < n, ∀ t ∈ Ioo (τ i) (τ (i + 1)),
      HasDerivAt w (fderiv ℝ finv (u t) (u' i t)) t := by
    intro i hi t ht
    have ht' : t ∈ Icc (τ i) (τ (i + 1)) := Ioo_subset_Icc_self ht
    have hu_at : HasDerivAt u (u' i t) t :=
      (hu i hi t ht').hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    exact (hfinv_diff (u t) (hu_mem t (hpiece_sub i hi ht'))).comp_hasDerivAt t hu_at
  -- the piece derivatives of the polar lift are continuous on the closed pieces
  have hw'_cont : ∀ i < n, ContinuousOn
      (fun t => fderiv ℝ finv (u t) (u' i t)) (Icc (τ i) (τ (i + 1))) := by
    intro i hi
    have h1 : ContinuousOn (fun t => fderiv ℝ finv (u t)) (Icc (τ i) (τ (i + 1))) :=
      (hfinvC1'.continuousOn_fderiv_of_isOpen hopen_f le_rfl).comp
        (hu_cont.mono (hpiece_sub i hi))
        (fun t ht => hu_mem t (hpiece_sub i hi ht))
    exact h1.clm_apply (hu'_cont i hi)
  have hw_ball : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ := fun t ht =>
    (mem_ball_zero_iff.mp (hpolar t ht).1).trans_le hερ
  -- endpoints of the polar lift
  have hw0 : w 0 = 0 := by
    have hf0 : f 0 = extChartAt I p p := by
      rw [hfdef]
      show extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p)) = _
      exact congrArg (extChartAt I p) (expMap_zero (I := I) g p)
    rw [hwdef]
    show finv (u 0) = 0
    rw [hudef]
    show finv (extChartAt I p (c 0)) = 0
    rw [hc0, ← hf0]
    exact hlinv 0 (by rw [norm_zero]; exact hε₁)
  have hw1 : w 1 = v := by
    rw [hwdef]
    show finv (u 1) = v
    rw [hudef]
    show finv (extChartAt I p (c 1)) = v
    rw [hc1]
    exact hlinv v (hv.trans_le hεε₁)
  -- the piecewise polar-form minimizing property
  have hcore := hmin v (hv.trans_le hερ) n τ w
    (fun i t => fderiv ℝ finv (u t) (u' i t))
    hτ0 hτn hτ hw_cont hw_deriv hw'_cont hw_ball hw0 hw1
  refine hcore.trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
  have hin : i < n := Finset.mem_range.mp hi
  -- identify the two length integrands on piece `i`
  have hIcc : uIcc (τ i) (τ (i + 1)) = Icc (τ i) (τ (i + 1)) :=
    uIcc_of_le (hτ i hin)
  refine intervalIntegral.integral_congr ?_
  intro t ht
  rw [hIcc] at ht
  have ht01 : t ∈ Icc (0 : ℝ) 1 := hpiece_sub i hin ht
  obtain ⟨hwball, hfw⟩ := hpolar t ht01
  -- the foot: `exp_p (w t) = c t` in the chart
  have hfoot : extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p))
      = extChartAt I p (c t) := hfw
  -- the velocity: `d f (w t) (fderiv finv (u t) (u' i t)) = u' i t` by
  -- uniqueness of derivatives within the piece
  have hf_diff : HasFDerivAt f (fderiv ℝ f (w t)) (w t) := by
    have hball₁ : w t ∈ ball (0 : E) ε₁ := ball_subset_ball hεε₁ hwball
    exact ((hfC1.contDiffAt (isOpen_ball.mem_nhds hball₁)).differentiableAt
      one_ne_zero).hasFDerivAt
  have hw_within : HasDerivWithinAt w (fderiv ℝ finv (u t) (u' i t))
      (Icc (τ i) (τ (i + 1))) t :=
    (hfinv_diff (u t) (hu_mem t ht01)).comp_hasDerivWithinAt t (hu i hin t ht)
  have h2' : HasDerivWithinAt u
      (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' i t)))
      (Icc (τ i) (τ (i + 1))) t := by
    refine (hf_diff.comp_hasDerivWithinAt t hw_within).congr ?_ (hpolar t ht01).2.symm
    intro s hs
    exact ((hpolar s (hpiece_sub i hin hs)).2).symm
  have h1' : HasDerivWithinAt u (u' i t) (Icc (τ i) (τ (i + 1))) t := hu i hin t ht
  have huniq : fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' i t)) = u' i t :=
    (uniqueDiffOn_Icc (hτs i hin) t ht).eq_deriv _ h2' h1'
  show Real.sqrt (chartMetricInner (I := I) g p
      (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
      (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' i t)))
      (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' i t))))
    = Real.sqrt (chartMetricInner (I := I) g p
      (extChartAt I p (c t)) (u' i t) (u' i t))
  rw [hfoot, huniq]

end Exponential
end Riemannian

end

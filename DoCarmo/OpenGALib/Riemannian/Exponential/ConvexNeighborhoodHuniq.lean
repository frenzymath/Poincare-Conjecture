import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodProp42
import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodUniqueness
import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodInterior
import OpenGALib.Riemannian.Exponential.RayGeodesic
import OpenGALib.Riemannian.Exponential.NormalBallEDist

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: discharging `Huniq` of do Carmo Proposition 4.2 (Ch. 3, §4)

`exists_stronglyConvex_closedBall_of_uniq` (`ConvexNeighborhoodProp42.lean`) reduces do Carmo's
Proposition 4.2 (for the closed ball) to the single hypothesis `Huniq`: two minimizing geodesics
on `Icc 0 1` joining the same endpoints near `p` coincide.  The *injectivity engine*
`exists_movingBase_geodesic_uniqueness` (`ConvexNeighborhoodUniqueness.lean`) does this for
competitors already presented on an **open** window `⊋ [0,1]` with a **bounded chart-`p` velocity**.

This file supplies the missing *presentation* (`I-0213`) and closes `Huniq`:

* `exists_geodesic_window_of_isGeodesicOn_Icc` — every geodesic on the closed `Icc 0 1`, whose
  endpoint values are known points, extends to a geodesic on an open window `(lo, hi)` with
  `lo < 0 < 1 < hi`, agreeing with it on `[0,1]`.  Completeness-free: the two one-sided endpoint
  prolongations (`IsGeodesicOn.exists_forward_extension_of_tendsto`, one after a time reversal) take
  the *known* endpoint value as the limit hypothesis, so no `[CompleteSpace M]` is needed.

The velocity bound and the final assembly follow below.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **An `Icc 0 1` geodesic extends to an open time window** (do Carmo Ch. 3, §4, the
presentation step of Prop. 4.2, `I-0213`).  A continuous intrinsic geodesic `α` on the *closed*
interval `[0,1]` extends to a continuous intrinsic geodesic `γ` on an *open* window `(lo, hi)` with
`lo < 0 < 1 < hi`, agreeing with `α` on `[0,1]`.

The endpoint values `α 0`, `α 1` are known points (not Cauchy limits), so the completeness-free
forward prolongation `IsGeodesicOn.exists_forward_extension_of_tendsto` applies at each end — once
forward past `1` with limit `α 1`, once (after the time reversal `t ↦ α (-t)`) forward past `0` with
limit `α 0`.  The two one-sided extensions are glued at the interior time `1/2`, where they both
equal `α`. -/
theorem exists_geodesic_window_of_isGeodesicOn_Icc
    (g : RiemannianMetric I M') {α : ℝ → M'}
    (hgeo : IsGeodesicOn (I := I) g α (Icc 0 1)) (hcont : ContinuousOn α (Icc 0 1)) :
    ∃ (lo hi : ℝ) (γ : ℝ → M'), lo < 0 ∧ 1 < hi ∧
      IsGeodesicOn (I := I) g γ (Ioo lo hi) ∧ ContinuousOn γ (Ioo lo hi) ∧
      Set.EqOn γ α (Icc 0 1) := by
  classical
  have h01 : (0 : ℝ) < 1 := one_pos
  -- restrict to the open interval
  have hgeoO : IsGeodesicOn (I := I) g α (Ioo 0 1) := hgeo.mono Ioo_subset_Icc_self
  have hcontO : ContinuousOn α (Ioo 0 1) := hcont.mono Ioo_subset_Icc_self
  have hne01 : (𝓝[Ioo (0 : ℝ) 1] 1).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo h01.ne]; exact ⟨h01.le, le_rfl⟩
  have hne00 : (𝓝[Ioo (0 : ℝ) 1] 0).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo h01.ne]; exact ⟨le_rfl, h01.le⟩
  -- forward extension past `1`
  have htend1 : Tendsto α (𝓝[Ioo 0 1] 1) (𝓝 (α 1)) :=
    (hcont 1 ⟨h01.le, le_rfl⟩).tendsto.mono_left (nhdsWithin_mono 1 Ioo_subset_Icc_self)
  obtain ⟨δ₁, hδ₁, γf, hγfcont, hγfgeo, hγfeq⟩ :=
    IsGeodesicOn.exists_forward_extension_of_tendsto (I := I) g h01 hgeoO hcontO (α 1) htend1
  -- backward extension: reflect, extend past `0`, reflect back
  set αrev : ℝ → M' := fun t => α (-t) with hαrev_def
  have hmapsrev : MapsTo (fun t : ℝ => -t) (Ioo (-1) 0) (Ioo (0 : ℝ) 1) := by
    intro t ht; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have hgeorevO : IsGeodesicOn (I := I) g αrev (Ioo (-1) 0) :=
    (isGeodesicOn_comp_neg (I := I) hgeoO).mono (fun t ht => hmapsrev ht)
  have hcontrevO : ContinuousOn αrev (Ioo (-1) 0) :=
    hcontO.comp continuous_neg.continuousOn (fun t ht => hmapsrev ht)
  have htend0 : Tendsto αrev (𝓝[Ioo (-1) 0] 0) (𝓝 (αrev 0)) := by
    have hmaps : MapsTo (fun t : ℝ => -t) (Ioo (-1) 0) (Icc (0 : ℝ) 1) :=
      fun t ht => Ioo_subset_Icc_self (hmapsrev ht)
    have h2 : ContinuousWithinAt α (Icc 0 1) ((fun t : ℝ => -t) 0) := by
      simpa using (hcont 0 ⟨le_rfl, h01.le⟩)
    have hcw : ContinuousWithinAt (fun t : ℝ => α (-t)) (Ioo (-1) 0) 0 :=
      h2.comp continuous_neg.continuousWithinAt hmaps
    exact hcw.tendsto
  obtain ⟨δ₀, hδ₀, ρe, hρecont, hρegeo, hρeeq⟩ :=
    IsGeodesicOn.exists_forward_extension_of_tendsto (I := I) g
      (show (-1 : ℝ) < 0 by norm_num) hgeorevO hcontrevO (αrev 0) htend0
  -- reflect the backward extension: `γb t = ρe (-t)` is a geodesic on `(-δ₀, 1)`
  set γb : ℝ → M' := fun t => ρe (-t) with hγb_def
  have hmapb : MapsTo (fun t : ℝ => -t) (Ioo (-δ₀) 1) (Ioo (-1) (0 + δ₀)) := by
    intro t ht; exact ⟨by linarith [ht.2], by simpa using (by linarith [ht.1] : -t < δ₀)⟩
  have hγbgeo : IsGeodesicOn (I := I) g γb (Ioo (-δ₀) 1) :=
    (isGeodesicOn_comp_neg (I := I) hρegeo).mono (fun t ht => hmapb ht)
  have hγbcont : ContinuousOn γb (Ioo (-δ₀) 1) :=
    hρecont.comp continuous_neg.continuousOn (fun t ht => hmapb ht)
  -- both one-sided extensions agree with `α` on `(0,1)`
  have hγbeq : Set.EqOn γb α (Ioo 0 1) := by
    intro t ht
    have hnt : -t ∈ Ioo (-1) 0 := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    show ρe (-t) = α t
    rw [hρeeq hnt]; show α (- -t) = α t; rw [neg_neg]
  -- endpoint pinning: the extensions take the correct endpoint values
  have hγb0 : γb 0 = α 0 := by
    have hcb : Tendsto γb (𝓝[Ioo 0 1] 0) (𝓝 (γb 0)) :=
      ((hγbcont 0 ⟨by linarith, h01⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨by linarith, h01⟩)).continuousWithinAt.tendsto
    have hcb' : Tendsto α (𝓝[Ioo 0 1] 0) (𝓝 (γb 0)) :=
      hcb.congr' (eventuallyEq_nhdsWithin_of_eqOn hγbeq)
    have hα0 : Tendsto α (𝓝[Ioo 0 1] 0) (𝓝 (α 0)) :=
      (hcont 0 ⟨le_rfl, h01.le⟩).tendsto.mono_left (nhdsWithin_mono 0 Ioo_subset_Icc_self)
    exact tendsto_nhds_unique hcb' hα0
  have hγf1 : γf 1 = α 1 := by
    have hcf : Tendsto γf (𝓝[Ioo 0 1] 1) (𝓝 (γf 1)) :=
      ((hγfcont 1 ⟨h01, by linarith⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨h01, by linarith⟩)).continuousWithinAt.tendsto
    have hcf' : Tendsto α (𝓝[Ioo 0 1] 1) (𝓝 (γf 1)) :=
      hcf.congr' (eventuallyEq_nhdsWithin_of_eqOn hγfeq)
    exact tendsto_nhds_unique hcf' htend1
  -- glue at `1/2`
  set γ : ℝ → M' := fun t => if t < (1 : ℝ) / 2 then γb t else γf t with hγ_def
  have hhalf01 : (1 : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hovl : Set.EqOn γb γf (Ioo 0 1) := fun t ht => (hγbeq ht).trans (hγfeq ht).symm
  -- `γ` agrees with `γb` near every `t < 1` and with `γf` near every `t > 0`
  have hglueb : ∀ t : ℝ, t < 1 / 2 → γ =ᶠ[𝓝 t] γb := by
    intro t ht
    filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Iio ((1:ℝ)/2) from ht)] with t' ht'
    show (if t' < (1:ℝ) / 2 then γb t' else γf t') = γb t'
    exact if_pos ht'
  have hgluef : ∀ t : ℝ, 1 / 2 ≤ t → t < 1 + δ₁ → γ =ᶠ[𝓝 t] γf := by
    intro t ht htu
    filter_upwards [Ioo_mem_nhds (show (0:ℝ) < t by linarith) htu] with t' ht'
    show (if t' < (1:ℝ) / 2 then γb t' else γf t') = γf t'
    by_cases h : t' < 1 / 2
    · rw [if_pos h]; exact hovl ⟨ht'.1, by linarith [h]⟩
    · rw [if_neg h]
  refine ⟨-δ₀, 1 + δ₁, γ, by linarith, by linarith, ?_, ?_, ?_⟩
  · -- geodesic on the whole window
    intro t ht
    by_cases htlt : t < 1 / 2
    · exact hasGeodesicEquationAt_congr_of_eventuallyEq (hglueb t htlt)
        (hγbgeo t ⟨ht.1, by linarith [htlt]⟩)
    · rw [not_lt] at htlt
      exact hasGeodesicEquationAt_congr_of_eventuallyEq (hgluef t htlt ht.2)
        (hγfgeo t ⟨by linarith [htlt], ht.2⟩)
  · -- continuity on the whole window
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    by_cases htlt : t < 1 / 2
    · exact ((hγbcont t ⟨ht.1, by linarith [htlt]⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨ht.1, by linarith [htlt]⟩)).congr (hglueb t htlt).symm
    · rw [not_lt] at htlt
      exact ((hγfcont t ⟨by linarith [htlt], ht.2⟩).continuousAt
        (isOpen_Ioo.mem_nhds ⟨by linarith [htlt], ht.2⟩)).congr (hgluef t htlt ht.2).symm
  · -- agreement with `α` on `[0,1]`
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · -- `t = 0`
      have : γ t = γb t := by
        show (if t < (1:ℝ) / 2 then γb t else γf t) = γb t
        exact if_pos (by rw [← h0]; norm_num)
      rw [this, ← h0]; exact hγb0
    rcases eq_or_lt_of_le ht.2 with h1 | h1
    · -- `t = 1`
      have : γ t = γf t := by
        show (if t < (1:ℝ) / 2 then γb t else γf t) = γf t
        exact if_neg (by rw [h1]; norm_num)
      rw [this, h1]; exact hγf1
    · -- interior
      have htIoo : t ∈ Ioo (0 : ℝ) 1 := ⟨h0, h1⟩
      by_cases htlt : t < 1 / 2
      · have : γ t = γb t := by
          show (if t < (1:ℝ) / 2 then γb t else γf t) = γb t
          exact if_pos htlt
        rw [this]; exact hγbeq htIoo
      · have : γ t = γf t := by
          show (if t < (1:ℝ) / 2 then γb t else γf t) = γf t
          exact if_neg htlt
        rw [this]; exact hγfeq htIoo

/-- **Math.** **A minimizing geodesic has speed equal to the distance it realizes** (do Carmo Ch. 3,
Prop. 3.6 corollary, local form). If `γ` is a continuous geodesic on an open window `(lo, hi)` with
`lo < 0 < 1 < hi`, joining `q₁ = γ 0` to `q₂ = γ 1`, and *distance-realizing* on `[0,1]`
(`d(γ s, γ t) = |s-t| · d(q₁,q₂)`), then its constant chart speed at `0` is exactly the distance:
`√⟨γ'(0), γ'(0)⟩_g = d(q₁, q₂)`.

The `≥` half is the length bound `IsGeodesicOn.dist_le` (`d(q₁,q₂) ≤ √S`).  The `≤` half is the local
minimizing property of geodesics: rescale the velocity by a small `κ` so the exponential ray
`η(s) = exp_{q₁}(s·(κ w))` exists (`exists_isGeodesicOn_expMap_ray`); it is a geodesic through `q₁`
with the same chart velocity as the rescaled curve `s ↦ γ(κ s)`, so the two coincide near `0`
(intrinsic uniqueness); the radial isometry `exists_edist_expMap_ball` then reads
`d(q₁, γ(κ s)) = s·κ·√S` for small `s`, while the distance-realizing hypothesis reads it as
`κ·s·d(q₁,q₂)` — equal for `s, κ > 0`. -/
theorem sqrt_speedSq_eq_dist_of_minimizing
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist)
    {γ : ℝ → M'} {lo hi : ℝ} {q₁ q₂ : M'}
    (hlo : lo < 0) (hhi : 1 < hi)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo lo hi))
    (hcont : ContinuousOn γ (Ioo lo hi))
    (hγ0 : γ 0 = q₁) (hγ1 : γ 1 = q₂)
    (hmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist q₁ q₂) :
    Real.sqrt (speedSq (I := I) g γ 0) = dist q₁ q₂ := by
  classical
  have h0mem : (0 : ℝ) ∈ Ioo lo hi := ⟨hlo, by linarith⟩
  have h1mem : (1 : ℝ) ∈ Ioo lo hi := ⟨by linarith, hhi⟩
  have hcont0 : ContinuousAt γ 0 := (hcont 0 h0mem).continuousAt (isOpen_Ioo.mem_nhds h0mem)
  have hsrc1 : γ 0 ∈ (chartAt H q₁).source := by rw [hγ0]; exact mem_chart_source H q₁
  -- the squared speed read in the chart at `q₁`
  set wx : E := deriv (chartReading (I := I) q₁ γ) 0 with hwx_def
  have hS : speedSq (I := I) g γ 0 =
      chartMetricInner (I := I) g q₁ (extChartAt I q₁ q₁) wx wx := by
    have h := (hgeo 0 h0mem).speedSq_eq_chartMetricInner_of_mem_source (I := I) hcont0 hsrc1
    have hcr0 : chartReading (I := I) q₁ γ 0 = extChartAt I q₁ q₁ := by
      show extChartAt I q₁ (γ 0) = extChartAt I q₁ q₁; rw [hγ0]
    rw [hcr0] at h; exact h
  set S : ℝ := speedSq (I := I) g γ 0 with hS_def
  have hSnn : 0 ≤ S := by
    rw [hS]; exact chartMetricInner_self_nonneg_of_mem_target (I := I) g q₁
      (mem_extChartAt_target q₁) wx
  -- the length lower bound `d(q₁, q₂) ≤ √S`
  have hd01 : dist (γ 0) (γ 1) = dist q₁ q₂ := by
    have := hmin 0 ⟨le_rfl, zero_le_one⟩ 1 ⟨zero_le_one, le_rfl⟩
    rwa [show |(0 : ℝ) - 1| = 1 by norm_num, one_mul] at this
  have hlower : dist q₁ q₂ ≤ Real.sqrt S := by
    have h := IsGeodesicOn.dist_le (I := I) g hg hgeo isOpen_Ioo isPreconnected_Ioo hcont
      h0mem h1mem zero_le_one
    rw [hd01, sub_zero, mul_one] at h
    exact h
  -- the differentiability of the chart reading at `0` with value `wx`
  have huγ : HasDerivAt (chartReading (I := I) q₁ γ) wx 0 :=
    (((hgeo 0 h0mem).solvesGeodesicODEAt (I := I) hcont0 hsrc1).1).self_of_nhds
  by_cases hwx : wx = 0
  · -- degenerate: zero velocity forces `S = 0` and `d(q₁,q₂) = 0`
    have hS0 : S = 0 := by rw [hS, hwx, chartMetricInner_zero_left]
    have hd0 : dist q₁ q₂ = 0 :=
      le_antisymm (by rw [hS0, Real.sqrt_zero] at hlower; exact hlower) dist_nonneg
    rw [hS0, Real.sqrt_zero, hd0]
  · -- nondegenerate: identify with an exponential ray and use the radial isometry
    have hwxpos : 0 < ‖wx‖ := norm_pos_iff.mpr hwx
    obtain ⟨ρ, b, hρ, hb, hadm, hray⟩ := exists_isGeodesicOn_expMap_ray (I := I) g q₁
    obtain ⟨ε, δe, hε, hδe, -, -, -, -, hedist, -⟩ := exists_edist_expMap_ball (I := I) g hg q₁
    -- rescale the velocity into the ray ball
    set κ : ℝ := min 1 (ρ / (2 * ‖wx‖)) with hκ_def
    have hκpos : 0 < κ := lt_min one_pos (by positivity)
    have hκ1 : κ ≤ 1 := min_le_left _ _
    set u : E := κ • wx with hu_def
    have hupos : 0 < ‖u‖ := by rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos hκpos]; positivity
    have huρ : ‖u‖ < ρ := by
      rw [hu_def, norm_smul, Real.norm_eq_abs, abs_of_pos hκpos]
      have hκle : κ ≤ ρ / (2 * ‖wx‖) := min_le_right _ _
      calc κ * ‖wx‖ ≤ (ρ / (2 * ‖wx‖)) * ‖wx‖ := by
            exact mul_le_mul_of_nonneg_right hκle (norm_nonneg _)
        _ = ρ / 2 := by field_simp
        _ < ρ := by linarith
    obtain ⟨hη0, hηvel, hηcont, hηgeo⟩ := hray u huρ
    set η : ℝ → M' := fun t : ℝ => expMap (I := I) g q₁ ((t • u : E) : TangentSpace I q₁)
      with hη_def
    -- the rescaled curve `δ(t) = γ(κ t)`
    set δ : ℝ → M' := fun t : ℝ => γ (κ * t + 0) with hδ_def
    have hδgeoALL : IsGeodesicOn (I := I) g δ ((fun t : ℝ => κ * t + 0) ⁻¹' Ioo lo hi) :=
      isGeodesicOn_comp_affine (I := I) hgeo
    -- the common window `W = (-c, c)`
    set c : ℝ := min (min (-lo) hi) b with hc_def
    have hcpos : 0 < c := lt_min (lt_min (by linarith) (by linarith)) (by linarith)
    have hc_nlo : c ≤ -lo := (min_le_left _ _).trans (min_le_left _ _)
    have hc_hi : c ≤ hi := (min_le_left _ _).trans (min_le_right _ _)
    have hc_b : c ≤ b := min_le_right _ _
    set W : Set ℝ := Ioo (-c) c with hW_def
    have h0W : (0 : ℝ) ∈ W := ⟨by linarith, hcpos⟩
    -- `κ·(-c, c) ⊆ (lo, hi)`, so `W ⊆ (κ·+0)⁻¹'(lo,hi)`
    have hWpre : W ⊆ (fun t : ℝ => κ * t + 0) ⁻¹' Ioo lo hi := by
      intro t ht
      have habs : |κ * t| < c := by
        rw [abs_mul, abs_of_pos hκpos]
        have htabs : |t| < c := abs_lt.mpr ⟨ht.1, ht.2⟩
        calc κ * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hκ1 (abs_nonneg _)
          _ = |t| := one_mul _
          _ < c := htabs
      have hb2 := abs_lt.mp habs
      refine ⟨by simp only [add_zero]; linarith [hb2.1, hc_nlo], by simp only [add_zero]; linarith [hb2.2, hc_hi]⟩
    have hWb : W ⊆ Ioo (-b) b :=
      Ioo_subset_Ioo (by linarith [hc_b]) (by linarith [hc_b])
    have hδgeoW : IsGeodesicOn (I := I) g δ W := hδgeoALL.mono hWpre
    have hηgeoW : IsGeodesicOn (I := I) g η W := hηgeo.mono hWb
    have hδcontW : ContinuousOn δ W := by
      refine hcont.comp (Continuous.continuousOn (by fun_prop)) ?_
      intro t ht; exact hWpre ht
    have hηcontW : ContinuousOn η W := hηcont.mono hWb
    -- endpoints and velocities match at `0`
    have hδ0 : δ 0 = q₁ := by
      show γ (κ * 0 + 0) = q₁; rw [show κ * 0 + 0 = 0 by ring, hγ0]
    have hδη0 : δ 0 = η 0 := by rw [hδ0, hη0]
    have hsrcδ0 : δ 0 ∈ (chartAt H q₁).source := by rw [hδ0]; exact mem_chart_source H q₁
    -- velocity of `δ` at `0` is `κ • wx`
    have hφ : HasDerivAt (fun t : ℝ => κ * t + 0) κ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul κ).add_const 0
    have hδvel : HasDerivAt (chartReading (I := I) q₁ δ) (κ • wx) 0 := by
      set A : ℝ → ℝ := fun t : ℝ => κ * t + 0 with hA_def
      have huγ' : HasDerivAt (chartReading (I := I) q₁ γ) wx (A 0) := by
        have hA0 : A 0 = 0 := by simp [hA_def]
        rw [hA0]; exact huγ
      exact huγ'.scomp (0 : ℝ) hφ
    have hηvel' : HasDerivAt (chartReading (I := I) q₁ η) u 0 := hηvel
    have hderiv_match : deriv (chartReading (I := I) q₁ δ) 0
        = deriv (chartReading (I := I) q₁ η) 0 := by
      rw [hδvel.deriv, hηvel'.deriv, hu_def]
    -- intrinsic uniqueness: `δ = η` on `W`
    have hδηW : Set.EqOn δ η W :=
      IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := q₁)
        isOpen_Ioo isPreconnected_Ioo hδgeoW hηgeoW hδcontW hηcontW h0W hδη0 hsrcδ0 hderiv_match
    -- pick a small time `t₀ > 0`
    set t₀ : ℝ := min (c / 2) (min (ε / (2 * ‖u‖)) (1 / (2 * κ))) with ht₀_def
    have ht₀pos : 0 < t₀ := lt_min (by linarith) (lt_min (by positivity) (by positivity))
    have ht₀W : t₀ ∈ W := ⟨by linarith [ht₀pos], by
      have : t₀ ≤ c / 2 := min_le_left _ _; linarith⟩
    have ht₀u : ‖t₀ • u‖ < ε := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht₀pos]
      have ht₀le : t₀ ≤ ε / (2 * ‖u‖) := (min_le_right _ _).trans (min_le_left _ _)
      calc t₀ * ‖u‖ ≤ (ε / (2 * ‖u‖)) * ‖u‖ := mul_le_mul_of_nonneg_right ht₀le (norm_nonneg _)
        _ = ε / 2 := by field_simp
        _ < ε := by linarith
    have hκt₀mem : κ * t₀ + 0 ∈ Icc (0 : ℝ) 1 := by
      have ht₀le : t₀ ≤ 1 / (2 * κ) := (min_le_right _ _).trans (min_le_right _ _)
      refine ⟨by simp only [add_zero]; positivity, ?_⟩
      simp only [add_zero]
      have : κ * t₀ ≤ κ * (1 / (2 * κ)) := mul_le_mul_of_nonneg_left ht₀le hκpos.le
      have h2 : κ * (1 / (2 * κ)) = 1 / 2 := by field_simp
      rw [h2] at this; linarith
    -- the radial isometry reads `d(q₁, η t₀) = √⟨t₀ u, t₀ u⟩`
    have hηt₀eq : η t₀ = expMap (I := I) g q₁ ((t₀ • u : E) : TangentSpace I q₁) := rfl
    have hedist_t₀ := hedist (t₀ • u) ht₀u
    have hdist_η : dist q₁ (η t₀)
        = Real.sqrt (chartMetricInner (I := I) g q₁ (extChartAt I q₁ q₁) (t₀ • u) (t₀ • u)) := by
      rw [hηt₀eq]
      have h := hedist_t₀
      rw [edist_dist] at h
      exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp h
    -- expand the chart-Gram value to `(t₀ κ)² · S`
    have hGram_expand :
        chartMetricInner (I := I) g q₁ (extChartAt I q₁ q₁) (t₀ • u) (t₀ • u)
          = (t₀ * κ) ^ 2 * S := by
      rw [chartMetricInner_smul_left, chartMetricInner_smul_right, hu_def,
        chartMetricInner_smul_left, chartMetricInner_smul_right, ← hS]
      ring
    have hsqrt_expand :
        Real.sqrt (chartMetricInner (I := I) g q₁ (extChartAt I q₁ q₁) (t₀ • u) (t₀ • u))
          = t₀ * κ * Real.sqrt S := by
      rw [hGram_expand, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    -- distance from the minimizing hypothesis
    have hdist_δ : dist q₁ (δ t₀) = (κ * t₀ + 0) * dist q₁ q₂ := by
      have h := hmin 0 ⟨le_rfl, zero_le_one⟩ (κ * t₀ + 0) hκt₀mem
      rw [hγ0] at h
      have hnn : (0 : ℝ) ≤ κ * t₀ + 0 := hκt₀mem.1
      rw [show |(0 : ℝ) - (κ * t₀ + 0)| = κ * t₀ + 0 by rw [abs_of_nonpos (by linarith)]; ring] at h
      exact h
    -- combine: `κ t₀ · d = t₀ κ · √S`, cancel `κ t₀ > 0`
    have hδt₀ : dist q₁ (δ t₀) = dist q₁ (η t₀) := by rw [hδηW ht₀W]
    have hkey : (κ * t₀ + 0) * dist q₁ q₂ = t₀ * κ * Real.sqrt S := by
      rw [← hdist_δ, hδt₀, hdist_η, hsqrt_expand]
    have hcancel : dist q₁ q₂ = Real.sqrt S := by
      have hpos : 0 < t₀ * κ := by positivity
      have h2 : t₀ * κ * dist q₁ q₂ = t₀ * κ * Real.sqrt S := by
        have hcoef : κ * t₀ + 0 = t₀ * κ := by ring
        rw [hcoef] at hkey; exact hkey
      exact mul_left_cancel₀ (ne_of_gt hpos) h2
    exact hcancel.symm

/-- **Math.** **Convex neighborhoods (do Carmo Proposition 4.2), unconditionally.** For every point
`p` of a Riemannian manifold there is `β > 0` such that the closed geodesic ball `closedBall p β` is
strongly convex (`def:dc-ch3-4-2-stronglyconvex`): any two of its points are joined by a *unique*
minimizing geodesic whose open arc lies in the ball.

This discharges the last hypothesis `Huniq` of `exists_stronglyConvex_closedBall_of_uniq`.  Two
minimizing geodesics `α, β'` on `[0,1]` joining the same `q₁, q₂` near `p` are each extended to an
open window (`exists_geodesic_window_of_isGeodesicOn_Icc`); their common speed equals `d(q₁,q₂)`
(`sqrt_speedSq_eq_dist_of_minimizing`), so — the ball being small — the chart-`p` initial velocities
have norm `< ρw` (`exists_sq_norm_deriv_le_speedSq`); the base-uniform injectivity engine
`exists_movingBase_geodesic_uniqueness` then forces `α = β'` on `[0,1]`.  The closed ball is used
deliberately (the open-ball statement is unsatisfiable at a boundary diagonal, `I-0197`). -/
theorem exists_stronglyConvex_closedBall (g : RiemannianMetric I M') (hg : g.IsRiemannianDist)
    (p : M') :
    ∃ β : ℝ, 0 < β ∧ StronglyConvex (I := I) g (closedBall p β) := by
  classical
  refine exists_stronglyConvex_closedBall_of_uniq (I := I) g hg p ?_
  -- the injectivity engine and the chart-velocity Gram bound, anchored at `p`
  obtain ⟨βe, ρw, hβe, hρw, Heng⟩ := exists_movingBase_geodesic_uniqueness (I := I) g p
  obtain ⟨c, V, hc, hVnhd, hVtgt, hbound⟩ := exists_sq_norm_deriv_le_speedSq (I := I) g p
  -- a closed ball inside the chart source that reads into `V`
  have hnhd : (chartAt H p).source ∩ extChartAt I p ⁻¹' V ∈ 𝓝 p :=
    inter_mem ((chartAt H p).open_source.mem_nhds (mem_chart_source H p))
      ((continuousAt_extChartAt p).preimage_mem_nhds hVnhd)
  obtain ⟨β₀, hβ₀, hβ₀sub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhd
  refine ⟨min (min β₀ βe) (ρw / (2 * Real.sqrt c + 1)),
    lt_min (lt_min hβ₀ hβe) (by positivity), ?_⟩
  set βU : ℝ := min (min β₀ βe) (ρw / (2 * Real.sqrt c + 1)) with hβU_def
  have hβU_β₀ : βU ≤ β₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hβU_βe : βU ≤ βe := (min_le_left _ _).trans (min_le_right _ _)
  have hβU_ρ : βU ≤ ρw / (2 * Real.sqrt c + 1) := min_le_right _ _
  intro q₁ q₂ α β' hpq₁ hpq₂ hα0 hα1 hαgeo hαmin hβ'0 hβ'1 hβ'geo hβ'min
  -- membership of `q₁` in the reading ball and chart source
  have hq₁ball : q₁ ∈ closedBall p β₀ :=
    mem_closedBall.mpr (by rw [dist_comm]; exact hpq₁.trans hβU_β₀)
  have hqsrc : q₁ ∈ (chartAt H p).source := (hβ₀sub hq₁ball).1
  have hq₁V : extChartAt I p q₁ ∈ V := (hβ₀sub hq₁ball).2
  have hq₁e : q₁ ∈ closedBall p βe :=
    mem_closedBall.mpr (by rw [dist_comm]; exact hpq₁.trans hβU_βe)
  have hq₂e : q₂ ∈ closedBall p βe :=
    mem_closedBall.mpr (by rw [dist_comm]; exact hpq₂.trans hβU_βe)
  -- build, for a competitor, an open-window geodesic with bounded chart-`p` velocity
  have hbuild : ∀ ζ : ℝ → M', ζ 0 = q₁ → ζ 1 = q₂ → IsGeodesicOn (I := I) g ζ (Icc 0 1) →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, dist (ζ s) (ζ t) = |s - t| * dist q₁ q₂) →
      ∃ (γ : ℝ → M') (w : E) (lo hi : ℝ), lo < 0 ∧ 1 < hi ∧
        IsGeodesicOn (I := I) g γ (Ioo lo hi) ∧ ContinuousOn γ (Ioo lo hi) ∧
        γ 0 = q₁ ∧ γ 1 = q₂ ∧
        HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 ∧ ‖w‖ < ρw ∧
        Set.EqOn γ ζ (Icc 0 1) := by
    intro ζ hζ0 hζ1 hζgeo hζmin
    -- continuity from the Lipschitz (minimizing) property
    have hcontζ : ContinuousOn ζ (Icc (0 : ℝ) 1) := by
      rw [Metric.continuousOn_iff]
      intro b hb ε hε
      refine ⟨ε / (dist q₁ q₂ + 1), by positivity, ?_⟩
      intro a ha hab
      rw [hζmin a ha b hb, ← Real.dist_eq]
      calc dist a b * dist q₁ q₂ ≤ ε / (dist q₁ q₂ + 1) * dist q₁ q₂ :=
            mul_le_mul_of_nonneg_right hab.le dist_nonneg
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [hε, dist_nonneg (x := q₁) (y := q₂)]
    obtain ⟨lo, hi, γ, hlo, hhi, hγgeo, hγcont, hγeq⟩ :=
      exists_geodesic_window_of_isGeodesicOn_Icc (I := I) g hζgeo hcontζ
    have hγ0 : γ 0 = q₁ := by rw [hγeq ⟨le_rfl, zero_le_one⟩, hζ0]
    have hγ1 : γ 1 = q₂ := by rw [hγeq ⟨zero_le_one, le_rfl⟩, hζ1]
    have hγmin : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist q₁ q₂ := by
      intro s hs t ht; rw [hγeq hs, hγeq ht]; exact hζmin s hs t ht
    have h0mem : (0 : ℝ) ∈ Ioo lo hi := ⟨hlo, by linarith⟩
    have hγ0src : γ 0 ∈ (chartAt H p).source := by rw [hγ0]; exact hqsrc
    have hcont0 : ContinuousAt γ 0 := (hγcont 0 h0mem).continuousAt (isOpen_Ioo.mem_nhds h0mem)
    set w : E := deriv (chartReading (I := I) p γ) 0 with hw_def
    have hwderiv : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 :=
      (((hγgeo 0 h0mem).solvesGeodesicODEAt (I := I) hcont0 hγ0src).1).self_of_nhds
    have hspeed : Real.sqrt (speedSq (I := I) g γ 0) = dist q₁ q₂ :=
      sqrt_speedSq_eq_dist_of_minimizing (I := I) g hg hlo hhi hγgeo hγcont hγ0 hγ1 hγmin
    have hq₁V' : extChartAt I p (γ 0) ∈ V := by rw [hγ0]; exact hq₁V
    have hwbd : ‖w‖ ^ 2 ≤ c * speedSq (I := I) g γ 0 := hbound hcont0 hγ0src hq₁V' hwderiv
    have hwnorm : ‖w‖ ≤ Real.sqrt c * dist q₁ q₂ := by
      have h1 : ‖w‖ ≤ Real.sqrt (c * speedSq (I := I) g γ 0) := by
        rw [← Real.sqrt_sq (norm_nonneg w)]; exact Real.sqrt_le_sqrt hwbd
      rwa [Real.sqrt_mul hc.le, hspeed] at h1
    have hdist2βU : dist q₁ q₂ ≤ 2 * βU := by
      calc dist q₁ q₂ ≤ dist q₁ p + dist p q₂ := dist_triangle _ _ _
        _ ≤ βU + βU := by
            refine add_le_add ?_ hpq₂
            rw [dist_comm]; exact hpq₁
        _ = 2 * βU := by ring
    have hwρw : ‖w‖ < ρw := by
      have hscnn : (0 : ℝ) ≤ Real.sqrt c := Real.sqrt_nonneg _
      have hstep : Real.sqrt c * dist q₁ q₂ ≤ Real.sqrt c * (2 * βU) :=
        mul_le_mul_of_nonneg_left hdist2βU hscnn
      have hfin : Real.sqrt c * (2 * βU) < ρw := by
        have hβUle : βU ≤ ρw / (2 * Real.sqrt c + 1) := hβU_ρ
        have hden : (0 : ℝ) < 2 * Real.sqrt c + 1 := by positivity
        have : 2 * Real.sqrt c * βU ≤ 2 * Real.sqrt c * (ρw / (2 * Real.sqrt c + 1)) :=
          mul_le_mul_of_nonneg_left hβUle (by positivity)
        have hrw : 2 * Real.sqrt c * (ρw / (2 * Real.sqrt c + 1)) < ρw := by
          rw [← mul_div_assoc, div_lt_iff₀ hden]
          nlinarith [hρw, hscnn, mul_nonneg hscnn hρw.le]
        nlinarith [this, hrw]
      exact lt_of_le_of_lt hwnorm (lt_of_le_of_lt hstep hfin)
    exact ⟨γ, w, lo, hi, hlo, hhi, hγgeo, hγcont, hγ0, hγ1, hwderiv, hwρw, hγeq⟩
  -- assemble both competitors through the injectivity engine
  obtain ⟨γα, wα, loα, hiα, hloα, hhiα, hgeoα, hcontα, hγα0, hγα1, hwα, hwαρ, heqα⟩ :=
    hbuild α hα0 hα1 hαgeo hαmin
  obtain ⟨γβ, wβ, loβ, hiβ, hloβ, hhiβ, hgeoβ, hcontβ, hγβ0, hγβ1, hwβ, hwβρ, heqβ⟩ :=
    hbuild β' hβ'0 hβ'1 hβ'geo hβ'min
  have hEng : Set.EqOn γα γβ (Icc 0 1) :=
    Heng q₁ hq₁e q₂ hq₂e γα γβ wα wβ loα hiα loβ hiβ hloα hhiα hgeoα hcontα hγα0 hγα1 hwα hwαρ
      hloβ hhiβ hgeoβ hcontβ hγβ0 hγβ1 hwβ hwβρ
  intro s hs
  rw [← heqβ hs, ← hEng hs]
  exact heqα hs

end Exponential

end Riemannian

end

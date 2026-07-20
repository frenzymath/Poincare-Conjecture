import PetersenLib.Ch05.GeodesicSmoothness
import PetersenLib.Ch05.PiecewiseArclength
import PetersenLib.Riemannian.Geodesic.HopfRinow

/-!
# Petersen Ch. 5, Corollary 5.7.2 — complete manifolds have segments everywhere

`cor:pet-ch5-complete-segment-exists`: if `(M, g)` is complete, any two points of
`M` are joined by a **segment** in Petersen's sense (`IsSegment`).

The vendored do Carmo cone supplies the minimizing geodesic
(`Exponential.exists_minimizing_geodesic_unitInterval`, Hopf–Rinow f)): a global
geodesic `γ` with `γ 0 = p`, `γ 1 = q` and `d(γ s, γ t) = |s - t| · d(p, q)` in
the *ambient* metric. Turning it into a Petersen segment needs three things.

1. **Regularity.** `IsGeodesic` is a `C¹`/second-order-ODE condition, whereas
   `IsPiecewiseSmoothCurve` demands `C^∞` on each piece of a partition. This is
   `IsGeodesic.isPiecewiseSmoothCurve` (`PetersenLib/Ch05/GeodesicSmoothness.lean`).
2. **Constant speed.** A geodesic has constant squared speed
   (`curveSpeedSq_eqOn_const`), so `L(γ|_[0,t]) = k · t` with
   `k = √(g(γ̇, γ̇))` — this is the third `IsSegment` clause outright.
3. **Length = Petersen distance.** Only the *forward* half of the distance
   bridge (`riemannianEDist_le_ofReal_riemannianDistance`, i.e.
   `d(p,q) ≤ |pq|`) is available, and the reverse half is not needed: the
   minimizing curve is one we *construct*, so it is its own competitor. The
   squeeze is
   `k = L(γ) ≥ |pq| ≥ d(p, q) = k`,
   whose last equality is the local content: rescaling time by a small `κ`
   identifies `γ` with a short radial ray `t ↦ exp_p(t u)`
   (`IsGeodesicOn.exists_eqOn_expMap_ray`), whose Petersen length is `|u|_g`
   (`exists_curveLength_expMap_ray`) and whose ambient distance from `p` is also
   `|u|_g` (`Exponential.exists_edist_expMap_ball`); comparing with
   `d(p, γ κ) = κ · d(p, q)` pins `k = d(p, q)`.

The main statement is `PetersenLib.completeManifold_allPointsJoinedBySegment`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [ConnectedSpace M]

/-- **Math.** Petersen Ch. 5, Corollary 5.7.2
(`cor:pet-ch5-complete-segment-exists`): on a **complete** connected Riemannian
manifold whose metric-space structure is the Riemannian distance of `g`, any two
points `p, q` are joined by a **segment**: a curve `γ : [0, 1] → M` with
`γ 0 = p`, `γ 1 = q` which is piecewise `C^∞`, realizes the Riemannian distance
between its endpoints (`L(γ) = |pq|`), and is parametrized proportionally to arc
length.

This is Hopf–Rinow f) (`Exponential.exists_minimizing_geodesic_unitInterval`)
promoted to Petersen's language: the minimizing geodesic is upgraded to a
piecewise `C^∞` curve (`IsGeodesic.isPiecewiseSmoothCurve`), its constant speed
`k` gives the proportional parametrization, and the squeeze
`k = L(γ) ≥ |pq| ≥ d(p, q) = k` — whose last step is the local identification of
`γ` with a short radial ray — identifies its length with the Petersen
distance. -/
theorem completeManifold_allPointsJoinedBySegment (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) [CompleteSpace M] (p q : M) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = q ∧ IsSegment (I := I) g γ 0 1 := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI hRM : IsRiemannianManifold I M := hg
  -- Hopf–Rinow f): a global minimizing geodesic on `[0, 1]`
  have hp : ∀ v : TangentSpace I p, ∃ γ : ℝ → M, γ 0 = p ∧
      HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ := by
    intro v
    obtain ⟨γ, h0, hv, hc, hgeo⟩ := Geodesic.exists_global_geodesic (I := I) g hg p v
    exact ⟨γ, h0, hv, hc, hgeo⟩
  obtain ⟨γ, hγ0, hγ1, hγc, hγgeo, hdist⟩ :=
    Exponential.exists_minimizing_geodesic_unitInterval (I := I) g hg p hp q
  refine ⟨γ, hγ0, hγ1, ?_⟩
  -- (1) regularity
  have hpw : IsPiecewiseSmoothCurve (I := I) γ 0 1 :=
    IsGeodesic.isPiecewiseSmoothCurve (I := I) g hγgeo hγc zero_le_one
  -- (2) constant speed
  have hconst : ∀ t : ℝ, curveSpeedSq (I := I) g γ t = curveSpeedSq (I := I) g γ 0 := by
    intro t
    exact curveSpeedSq_eqOn_const (I := I) g isOpen_univ ordConnected_univ
      hγc.continuousOn (Geodesic.IsGeodesic.isGeodesicOn hγgeo univ) (mem_univ t) (mem_univ 0)
  set k : ℝ := Real.sqrt (curveSpeedSq (I := I) g γ 0) with hkdef
  have hk0 : 0 ≤ k := Real.sqrt_nonneg _
  have hlen : ∀ a b : ℝ, curveLength (I := I) g γ a b = (b - a) * k := by
    intro a b
    have hfun : (fun t : ℝ => Real.sqrt (curveSpeedSq (I := I) g γ t)) = fun _ : ℝ => k := by
      funext t; rw [hkdef, hconst t]
    show (∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g γ t)) = (b - a) * k
    rw [hfun, intervalIntegral.integral_const, smul_eq_mul]
  -- (3) the speed `k` is the ambient distance `d(p, q)`
  obtain ⟨ε₁, hε₁, hcl₀⟩ := exists_curveLength_expMap_ray (I := I) g p
  -- `PetersenLib.expMap` is `PetersenLib.Exponential.expMap` by `rfl` (`expMap_eq`)
  have hcl : ∀ v : E, ‖v‖ < ε₁ →
      curveLength (I := I) g
          (fun t : ℝ => Exponential.expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 0 1
        = Real.sqrt (g.metricInner p v v) := hcl₀
  obtain ⟨ε₂, δ₂, hε₂, hδ₂, -, -, -, -, hedist, -⟩ :=
    Exponential.exists_edist_expMap_ball (I := I) g hg p
  obtain ⟨δ, hδ, hmain⟩ :=
    IsGeodesicOn.exists_eqOn_expMap_ray (I := I) g isOpen_univ
      (Geodesic.IsGeodesic.isGeodesicOn hγgeo univ) hγc.continuousOn (mem_univ (0 : ℝ))
      (ε := min ε₁ ε₂) (lt_min hε₁ hε₂)
  set κ : ℝ := min δ 1 with hκdef
  have hκ0 : 0 < κ := lt_min hδ one_pos
  have hκ1 : κ ≤ 1 := min_le_right _ _
  obtain ⟨u, hu, heq⟩ := hmain κ (by rw [abs_of_pos hκ0]; exact min_le_left _ _)
  have hu₁ : ‖u‖ < ε₁ := hu.trans_le (min_le_left _ _)
  have hu₂ : ‖u‖ < ε₂ := hu.trans_le (min_le_right _ _)
  set ray : ℝ → M := fun t : ℝ =>
    Exponential.expMap (I := I) g p ((t • u : E) : TangentSpace I p) with hraydef
  have heq' : ∀ t ∈ Icc (0 : ℝ) 1, γ (κ * t) = ray t := by
    intro t ht
    have := heq t ht
    rw [add_zero, hγ0] at this
    exact this
  -- the length of `γ` over `[0, κ]` computed twice
  have hlen₁ : curveLength (I := I) g (fun t : ℝ => γ (κ * t + 0)) 0 1
      = curveLength (I := I) g γ 0 κ := by
    rw [curveLength_comp_mul_add (I := I) g γ hκ0.le 0 0 1]
    norm_num
  have hlen₂ : curveLength (I := I) g (fun t : ℝ => γ (κ * t + 0)) 0 1
      = curveLength (I := I) g ray 0 1 := by
    refine curveLength_congr_Icc (I := I) g (fun t ht => ?_)
      (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one)
    rw [add_zero]
    exact heq' t ht
  have hK : κ * k = Real.sqrt (g.metricInner p u u) := by
    have h := hlen₁.symm.trans hlen₂
    rw [hlen 0 κ, hraydef, hcl u hu₁] at h
    rw [← h]; ring
  -- the ambient distance from `p` to `γ κ = exp_p u`, computed twice
  have hchart : chartMetricInner (I := I) g p (extChartAt I p p) u u = g.metricInner p u u := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) u u,
      trivializationAt_symm_self]
  have hγκ : γ κ = Exponential.expMap (I := I) g p (u : TangentSpace I p) := by
    have := heq' 1 (right_mem_Icc.mpr zero_le_one)
    rw [mul_one] at this
    rw [this, hraydef]
    simp
  have hdistκ : dist p (γ κ) = κ * dist p q := by
    have h := hdist 0 (left_mem_Icc.mpr zero_le_one) κ ⟨hκ0.le, hκ1⟩
    rw [hγ0] at h
    rw [h, zero_sub, abs_neg, abs_of_pos hκ0]
  have hdistray : dist p (γ κ) = Real.sqrt (g.metricInner p u u) := by
    have h : edist p (γ κ) = ENNReal.ofReal (Real.sqrt (g.metricInner p u u)) := by
      rw [hγκ, hedist u hu₂, hchart]
    rw [edist_dist] at h
    exact (ENNReal.ofReal_eq_ofReal_iff dist_nonneg (Real.sqrt_nonneg _)).mp h
  have hkd : k = dist p q := by
    have h : κ * k = κ * dist p q := by rw [hK, ← hdistray, hdistκ]
    exact mul_left_cancel₀ hκ0.ne' h
  -- (4) the squeeze `k = L(γ) ≥ |pq| ≥ d(p, q) = k`
  have hlen01 : curveLength (I := I) g γ 0 1 = k := by rw [hlen 0 1]; ring
  have hle₁ : riemannianDistance (I := I) g p q ≤ k := by
    rw [← hlen01]
    exact riemannianDistance_le_curveLength (I := I) g hpw hγ0 hγ1
  have hle₂ : dist p q ≤ riemannianDistance (I := I) g p q := by
    have hb : ENNReal.ofReal (dist p q)
        ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) := by
      calc ENNReal.ofReal (dist p q) = edist p q := (edist_dist p q).symm
        _ = Manifold.riemannianEDist I p q := IsRiemannianManifold.out (I := I) p q
        _ ≤ ENNReal.ofReal (riemannianDistance (I := I) g p q) :=
            riemannianEDist_le_ofReal_riemannianDistance (I := I) g p q
    exact (ENNReal.ofReal_le_ofReal_iff
      (riemannianDistance_nonneg (I := I) g p q)).mp hb
  have hdisteq : riemannianDistance (I := I) g p q = k :=
    le_antisymm hle₁ (by rw [hkd]; exact hle₂)
  refine ⟨hpw, ?_, k, hk0, fun t _ => ?_⟩
  · rw [hlen01, hγ0, hγ1, hdisteq]
  · rw [hlen 0 t]; ring

end PetersenLib

import OpenGALib.Riemannian.Exponential.UniformSegmentLength
import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodVelocity

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The joining geodesic with metric payload (do Carmo Ch. 3, §4)

The totally-normal-neighborhood theorem `exists_totallyNormal_c1_diffeo` (do Carmo Thm 3.7)
joins any two points `q₁, q₂` of a neighborhood `W ∋ p` by a geodesic segment
`γ(s) = φ_p⁻¹((Z(φ_p q₁, T⁻¹ • w)(sT))₁)`, uniquely among small joining velocities `w`. But
its exposed conclusion carries no *metric* content: it certifies `γ` a geodesic on `[0,1]` with
initial chart velocity `w`, but not the length `γ` realizes nor the distance it bounds.

This file bolts the metric payload of `UniformSegmentLength.lean` onto that joining geodesic.
Using the raw spray-flow predicate now exposed by `exists_totallyNormal_c1_diffeo`, and the
velocity-smallness of the inverse pair map (`exists_closedBall_forall_ginvSnd_norm_lt`,
do Carmo's `exp_p⁻¹ p = 0` made uniform), the main result

* `exists_convex_join_ball`

produces, for every `p`, a radius `β > 0` such that any two points of `closedBall p β` are joined
by a geodesic `γ` on an *open* time window `(lo, hi) ⊋ [0,1]` with:
- the arclength-proportional length `ℓ(γ|[0,t]) = √⟨w,w⟩_{p,φ_p q₁} · t` (constant speed);
- the radial *upper* bound `d(q₁, q₂) ≤ √⟨w,w⟩_{p,φ_p q₁}` (the `≤` half of Prop 3.6, base-uniform);
- the chart-velocity data `HasDerivAt` at every interior time, and `w ≠ 0` off the diagonal.

This is exactly the input the minimizing-from-arclength machinery
(`edist_segment_of_arclength`, `isGeodesicOn_of_arclength_edist`) and the interior-arc deduction
(`exists_forall_minimizing_geodesic_interior_ball`) consume. What is *not* here — and is the sole
residual crux of `prop:dc-ch3-4-2` — is the matching *lower* bound
`d(q₁, q₂) ≥ √⟨w,w⟩_{p,φ_p q₁}` (radial geodesics realize the distance), whose base-uniform form
requires transporting the Gauss estimate to the moving-base flow family.
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

/-- **Math.** **The totally-normal joining geodesic carries the Proposition 3.6 metric payload,
base-uniformly.** For every `p` there is `β > 0` such that any `q₁, q₂ ∈ closedBall p β` are joined
by a geodesic `γ` on an open window `(lo, hi) ⊋ [0,1]` whose length over `[0,t]` is
`√⟨w,w⟩_{p,φ_p q₁} · t` (constant speed) and whose endpoints satisfy the radial upper bound
`d(q₁, q₂) ≤ √⟨w,w⟩_{p,φ_p q₁}`. The joining chart velocity `w` is available with `HasDerivAt` at
`0` and at every interior time, and is nonzero off the diagonal. This is the metric-laden joining
geodesic that the convex-neighborhood assembly consumes — everything except the matching lower
distance bound. -/
theorem exists_convex_join_ball (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M')
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ β : ℝ, 0 < β ∧ closedBall p β ⊆ (chartAt H p).source ∧
      ∀ q₁ ∈ closedBall p β, ∀ q₂ ∈ closedBall p β,
        ∃ (γ : ℝ → M') (w : E) (lo hi : ℝ),
          lo < 0 ∧ 1 < hi ∧
          γ 0 = q₁ ∧ γ 1 = q₂ ∧ (q₁ ≠ q₂ → w ≠ 0) ∧ ‖w‖ < ρ ∧
          IsGeodesicOn (I := I) g γ (Ioo lo hi) ∧
          ContinuousOn γ (Ioo lo hi) ∧
          HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 ∧
          (∀ t₀ ∈ Ioo (0 : ℝ) 1, ∃ w₀ : E,
            HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w₀ t₀) ∧
          (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
            ⟨g.toRiemannianMetric⟩
           (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I γ 0 t
              = ENNReal.ofReal
                  (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q₁) w w) * t)) ∧
           edist q₁ q₂ ≤ ENNReal.ofReal
             (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q₁) w w))) := by
  classical
  obtain ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδpos, hδ₁pos, hTpos, hWchart,
    hmem, hcover, hGC1, hGinj, hGopen, hGleft, hGright, hGinvC1, hrange, hdiag,
    rF, εF, hrF, hεF, hTεF, hflow⟩ := exists_totallyNormal_c1_diffeo (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  -- velocity smallness of the joining chart velocity `w = (Ginv(φ_p q₁, φ_p q₂))₂`
  obtain ⟨βv, hβvpos, hβvsrc, hvsmall⟩ :=
    exists_closedBall_forall_ginvSnd_norm_lt (I := I) p (Ginv := Ginv)
      (U := (fun x : E × E => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1))
        '' (ball (extChartAt I p p) δ₁ ×ˢ ball (0 : E) δ))
      hGopen (hrange p hpW p hpW) hGinvC1.continuousOn hdiag (r := min (T * rF) ρ)
      (lt_min (by positivity) hρ)
  -- a base neighborhood forcing `φ_p q ∈ ball y₀ rF` and `q ∈ W`
  have hnhd : extChartAt I p ⁻¹' ball y₀ rF ∩ W ∈ 𝓝 p := by
    refine inter_mem ?_ (hWopen.mem_nhds hpW)
    exact (continuousAt_extChartAt (I := I) p).preimage_mem_nhds
      (isOpen_ball.mem_nhds (by rw [hy₀def]; exact mem_ball_self hrF))
  obtain ⟨βb, hβbpos, hβbsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhd
  refine ⟨min βv βb, lt_min hβvpos hβbpos, ?_, ?_⟩
  · exact (closedBall_subset_closedBall (min_le_left _ _)).trans hβvsrc
  intro q₁ hq₁ q₂ hq₂
  have hq₁v : q₁ ∈ closedBall p βv := closedBall_subset_closedBall (min_le_left _ _) hq₁
  have hq₂v : q₂ ∈ closedBall p βv := closedBall_subset_closedBall (min_le_left _ _) hq₂
  have hq₁b : q₁ ∈ closedBall p βb := closedBall_subset_closedBall (min_le_right _ _) hq₁
  have hq₂b : q₂ ∈ closedBall p βb := closedBall_subset_closedBall (min_le_right _ _) hq₂
  have hq₁W : q₁ ∈ W := (hβbsub hq₁b).2
  have hq₂W : q₂ ∈ W := (hβbsub hq₂b).2
  have hq₁src : q₁ ∈ (chartAt H p).source := hWsub hq₁W
  have hq₁srcE : q₁ ∈ (extChartAt I p).source := by rw [extChartAt_source]; exact hq₁src
  -- the joining velocity `w`
  obtain ⟨w, hwδ, hjoin, hwGinv, huniq⟩ := hcover q₁ hq₁W q₂ hq₂W
  -- velocity smallness applied to `w`
  have hwmin : ‖w‖ < min (T * rF) ρ := by rw [hwGinv]; exact hvsmall q₁ hq₁v q₂ hq₂v
  have hwsmall : ‖w‖ < T * rF := lt_of_lt_of_le hwmin (min_le_left _ _)
  have hwρ : ‖w‖ < ρ := lt_of_lt_of_le hwmin (min_le_right _ _)
  -- the flow-membership of `(φ_p q₁, T⁻¹ • w)` in the raw closed ball of radius `rF`
  have hmemF : ((extChartAt I p q₁, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) rF := by
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le ?_ ?_
    · rw [← hy₀def]
      exact le_of_lt (mem_ball.mp (hβbsub hq₁b).1)
    · rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hTpos.le,
        inv_mul_le_iff₀ hTpos]
      linarith [hwsmall]
  -- the descent to an open-window geodesic
  obtain ⟨hγ0, hγcont, hγgeo, hγread, hγd0, hγdIoo⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hTpos hTεF hflow hmemF
  set γ : ℝ → M' := fun s : ℝ =>
    (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (s * T)).1) with hγdef
  have hεFT : (1 : ℝ) < εF / T := (one_lt_div hTpos).mpr hTεF
  have hεFTpos : 0 < εF / T := lt_trans one_pos hεFT
  -- endpoints
  have hγ0q : γ 0 = q₁ := by
    show (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (0 * T)).1) = q₁
    rw [zero_mul, (hflow _ hmemF).1]
    exact (extChartAt I p).left_inv hq₁srcE
  have hγ1q : γ 1 = q₂ := by
    show (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (1 * T)).1) = q₂
    rw [one_mul]; exact hjoin
  -- the metric payload
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hlen : ∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I γ 0 t
      = ENNReal.ofReal
          (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q₁) w w) * t) := by
    intro t ht
    exact Geodesic.pathELength_uniform_flow_segment_Ioo_le_one (I := I) g p hTpos hTεF hflow
      hmemF ht
  have hup : edist q₁ q₂ ≤ ENNReal.ofReal
      (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q₁) w w)) := by
    have h := Geodesic.edist_uniform_flow_segment_le (I := I) g hg p hTpos hTεF hflow hmemF
    rw [show ((extChartAt I p).symm (extChartAt I p q₁)) = q₁ from
        (extChartAt I p).left_inv hq₁srcE] at h
    rw [show ((extChartAt I p).symm
          ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (1 * T)).1)) = q₂ from by
        rw [one_mul]; exact hjoin] at h
    exact h
  refine ⟨γ, w, -(εF / T), εF / T, by linarith, hεFT, hγ0q, hγ1q, ?_, hwρ,
    hγgeo, hγcont, hγd0, ?_, hlen, hup⟩
  · -- `w ≠ 0` off the diagonal: `w = 0` forces length `0`, hence `q₁ = q₂`
    intro hne hw0
    apply hne
    have h0 : chartMetricInner (I := I) g p (extChartAt I p q₁) w w = 0 := by
      rw [hw0]; simp [chartMetricInner]
    rw [h0, Real.sqrt_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero, edist_eq_zero] at hup
    exact hup
  · -- interior chart velocities
    intro t₀ ht₀
    refine ⟨T • (Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) (t₀ * T)).2, ?_⟩
    exact hγdIoo t₀ ⟨by linarith [ht₀.1], lt_trans ht₀.2 hεFT⟩

import DoCarmoLib.Riemannian.Exponential.MovingBaseRayODE
import DoCarmoLib.Riemannian.Exponential.MovingBaseGauss

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The moving-base flow reading of `exp` as an abstract Gauss package (do Carmo Ch. 3, §3–4)

`RayODE.lean` packages, at the *fixed* base `p`, the analytic input the Gauss lemma needs
(`exists_expMap_ray_ode_ball`): the chart reading `f = φ_p ∘ exp_p` is `C²` on a ball,
`(df)₀ = id`, and each ray velocity solves the chart-`p` geodesic equation. Its ray step
descends the coordinate spray trajectory to a `maximalGeodesic` witness *anchored at the chart
centre `φ_p p`*, so it cannot be reused at a moving base `q ≠ p`.

This file assembles the **base-uniform** analogue for the *flow reading*
`f_y : w ↦ (Z (y, T⁻¹ • w) T)₁` of the coordinate geodesic spray flow `Z` through a free base
point `y = φ_p q ∈ (extChartAt I p).target`. Obtaining the local spray flow once
(`exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow`) and feeding it to the three base-free
linchpins of `MovingBaseRayODE.lean`

* `geodesicFlow_eqOn_of_zero_velocity` (zero-velocity equilibrium ⇒ `f_y 0 = y`);
* `geodesicFlow_fst_fibre_time_movingBase` (the ray reparametrization
  `f_y(a • u) = (Z (y, T⁻¹ • u)(a T))₁`, the moving-base replacement of `RayODE`'s `key`);
* `contDiffOn_two_movingBase_flowReading` (the reading is `C²`),

the ray-velocity computation of `RayODE` ports verbatim, replacing `key` by the reparametrization.
The results:

* `exists_movingBase_ray_ode_ball` — thresholds `η, ρ > 0`, `b > 1` such that for every base `y`
  within `η` of `φ_p p` the reading `f_y` is `C²` on `B_ρ(0)`, lands in the chart target with foot
  in the tangent trivialization base set, has `(df_y)₀ = id`, and satisfies the chart-`p` geodesic
  ODE along every ray. These are exactly the six abstract hypotheses of `gauss_surface_computation_at`.
* `exists_movingBase_gauss_radial_lower_bound` — chaining `gauss_surface_computation_at` and
  `gauss_radial_lower_bound_at`, the reading is a radial isometry onto the Gram form based at `y`
  and does not shrink radial components: the base-uniform Cauchy–Schwarz inequality
  `⟨v, ξ⟩_y² ≤ ⟨v, v⟩_y · ⟨(df_y)_v ξ, (df_y)_v ξ⟩_{f_y v}` that the reach estimate
  `gauss_radius_reach_at` consumes. This is the analytic heart of the lower-bound crux `Hlb` of
  `prop:dc-ch3-4-2`: the abstract package is consumed downstream purely through its `(df_y)₀ = id`
  and ray-ODE clauses (ODE uniqueness identifies any chart geodesic through `y` with a ray of
  `f_y`), so no closed form of `f_y` need be exposed.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian
namespace Exponential

open Riemannian.Geodesic Riemannian.FlowDependence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

set_option maxHeartbeats 4000000 in
/-- **Math.** **The moving-base flow reading of `exp` is `C²` on a ball and satisfies the
geodesic ODE along rays** (do Carmo Ch. 3, §3–4; the base-uniform analytic package for the Gauss
lemma). There are thresholds `η, ρ > 0` and `b > 1` such that for every base point `y` within `η`
of the chart centre `φ_p p` the flow reading `f_y : w ↦ (Z (y, T⁻¹ • w) T)₁` of the coordinate
geodesic spray satisfies:

* `f_y 0 = y` (the zero-velocity equilibrium);
* `f_y` is `C²` on `B_ρ(0)`;
* `f_y` maps `B_ρ(0)` into the chart target, with foot in the tangent trivialization base set;
* `(df_y)_0 = id`;
* along every ray the velocity `t' ↦ (df_y)_{t'•u}(u)` solves the chart-`p` geodesic equation
  `V̇ = −Γ_p(V, V)(f_y(t•u))`.

These are exactly the six abstract hypotheses of `gauss_surface_computation_at`. The proof obtains
the local spray flow once and ports the ray-velocity computation of `exists_expMap_ray_ode_ball`,
replacing the manifold descent `key` by the base-free ray reparametrization
`geodesicFlow_fst_fibre_time_movingBase` and the zero-velocity value by
`geodesicFlow_eqOn_of_zero_velocity`. -/
theorem exists_movingBase_ray_ode_ball (g : RiemannianMetric I M) (p : M) :
    ∃ (η ρ b r ε T : ℝ) (Z : E × E → ℝ → E × E),
      0 < η ∧ 0 < ρ ∧ 1 < b ∧ 0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ∀ y : E, dist y (extChartAt I p p) < η →
        (∀ w : E, ‖w‖ < ρ →
          ((y, T⁻¹ • w) : E × E) ∈
            closedBall ((extChartAt I p p, (0 : E)) : E × E) r) ∧
        ∃ f : E → E,
          (∀ w : E, f w = (Z ((y, T⁻¹ • w) : E × E) T).1) ∧
          f 0 = y ∧
          ContDiffOn ℝ 2 f (ball (0 : E) ρ) ∧
          fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E ∧
          (∀ w' : E, ‖w'‖ < ρ → f w' ∈ (extChartAt I p).target) ∧
          (∀ w' : E, ‖w'‖ < ρ →
            (extChartAt I p).symm (f w') ∈ (trivializationAt E (TangentSpace I) p).baseSet) ∧
          (∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
            HasDerivAt
              (fun t' : ℝ => fderiv ℝ f (t' • u) u)
              (- Geodesic.chartChristoffelContraction (I := I) g p
                  (fderiv ℝ f (t • u) u) (fderiv ℝ f (t • u) u) (f (t • u))) t) := by
  classical
  obtain ⟨r, ε, T, Z, L, σ, τ, hT, hr, hε, hTε, hflow, hLip, hmax, hσ_ball, hC1τ, hC2τ⟩ :=
    exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow (I := I) g p
  obtain ⟨η, ρv, b', hηpos, hρvpos, hb1', hkey⟩ :=
    geodesicFlow_fst_fibre_time_movingBase (I := I) g p hr hT hTε hflow hLip
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set η₀ : ℝ := min η r with hη₀def
  set ρ : ℝ := min (r * T) (T * ρv) with hρdef
  set b : ℝ := min b' (ε / T) with hbdef
  have hη₀pos : 0 < η₀ := lt_min hηpos hr
  have hρpos : 0 < ρ := lt_min (by positivity) (by positivity)
  have hb1 : 1 < b := lt_min hb1' ((one_lt_div hT).mpr hTε)
  have hρ_le_rT : ρ ≤ r * T := min_le_left _ _
  have hρ_le_Tρv : ρ ≤ T * ρv := min_le_right _ _
  refine ⟨η₀, ρ, b, r, ε, T, Z, hη₀pos, hρpos, hb1, hr, hε, hT, hTε, hflow, ?_⟩
  intro y hy
  have hy_η : dist y (extChartAt I p p) < η := lt_of_lt_of_le hy (min_le_left _ _)
  have hy_r : dist y (extChartAt I p p) < r := lt_of_lt_of_le hy (min_le_right _ _)
  set f : E → E := fun w : E => (Z ((y, T⁻¹ • w) : E × E) T).1 with hfdef
  -- flow-ball membership of the rescaled initial condition
  have hmem : ∀ w : E, ‖w‖ < ρ → ((y, T⁻¹ • w) : E × E) ∈ closedBall z₀ r := by
    intro w hw
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    refine max_le hy_r.le ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_le_iff₀ hT]
    calc ‖w‖ ≤ ρ := hw.le
      _ ≤ r * T := hρ_le_rT
      _ = T * r := mul_comm r T
  have hmem0 : ((y, (0 : E)) : E × E) ∈ closedBall z₀ r := by
    have h := hmem 0 (by rw [norm_zero]; exact hρpos)
    rwa [smul_zero] at h
  -- the moving-base ray identification (replaces `RayODE`'s manifold descent `key`)
  have key : ∀ (u : E) (a : ℝ), ‖u‖ < ρ → |a| < b →
      f (a • u) = (Z ((y, T⁻¹ • u) : E × E) (a * T)).1 := by
    intro u a hu ha
    have ha' : |a| < b' := lt_of_lt_of_le ha (min_le_left _ _)
    have hnorm : ‖T⁻¹ • u‖ < ρv := by
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_lt_iff₀ hT]
      exact lt_of_lt_of_le hu hρ_le_Tρv
    show (Z ((y, T⁻¹ • (a • u)) : E × E) T).1 = (Z ((y, T⁻¹ • u) : E × E) (a * T)).1
    rw [smul_comm T⁻¹ a u]
    exact hkey y (T⁻¹ • u) hy_η hnorm a ha'
  -- the reading is `C²` on `B_ρ(0)` (via the σ-form of `contDiffOn_two_movingBase_flowReading`)
  have hC2 : ContDiffOn ℝ 2 f (ball (0 : E) ρ) := by
    have hC2σ := contDiffOn_two_movingBase_flowReading (I := I) g p hT hC1τ hC2τ hy_r
    refine (hC2σ.mono (ball_subset_ball hρ_le_rT)).congr (fun x hx => ?_)
    have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
    show (Z ((y, T⁻¹ • x) : E × E) T).1
        = (σ ((y, T⁻¹ • x) : E × E) ⟨T, ⟨hT.le, le_rfl⟩⟩).1
    rw [hσ_ball ((y, T⁻¹ • x) : E × E) (hmem x hxρ) ⟨T, ⟨hT.le, le_rfl⟩⟩]
  -- the chart velocity along a ray is the rescaled flow velocity
  have hvel : ∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
      fderiv ℝ f (t • u) u
        = T • (Z ((y, T⁻¹ • u) : E × E) (t * T)).2 := by
    intro u t hu ht htu
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem u hu)
    have htT : t * T ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hT]
      have htεT : |t| < ε / T := lt_of_lt_of_le ht (min_le_right _ _)
      calc |t| * T < (ε / T) * T := mul_lt_mul_of_pos_right htεT hT
        _ = ε := by field_simp
    have hdiff : DifferentiableAt ℝ f (t • u) :=
      (hC2.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr htu))).differentiableAt
        (by norm_num)
    have hray : HasDerivAt (fun a : ℝ => a • u) u t := by
      simpa using (hasDerivAt_id t).smul_const u
    have h₁ : HasDerivAt (fun a : ℝ => f (a • u)) (fderiv ℝ f (t • u) u) t := by
      simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt t hray
    have hZs : HasDerivAt (Z ((y, T⁻¹ • u) : E × E))
        (geodesicSprayCoord (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2) (t * T) :=
      (hzd _ (Ioo_subset_Icc_self htT)).hasDerivAt (Icc_mem_nhds htT.1 htT.2)
    have hcomp : HasDerivAt
        (fun a : ℝ => Z ((y, T⁻¹ • u) : E × E) (a * T))
        (T • geodesicSprayCoord (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2) t :=
      hZs.scomp t (hasDerivAt_mul_const T)
    have h₂ : HasDerivAt
        (fun a : ℝ => (Z ((y, T⁻¹ • u) : E × E) (a * T)).1)
        (T • (Z ((y, T⁻¹ • u) : E × E) (t * T)).2) t := by
      have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [geodesicSprayCoord_def] using hfst
    have hev : (fun a : ℝ => f (a • u)) =ᶠ[𝓝 t]
        (fun a : ℝ => (Z ((y, T⁻¹ • u) : E × E) (a * T)).1) := by
      have hopen : IsOpen {a : ℝ | |a| < b} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds ht] with a ha
      exact key u a hu ha
    exact h₁.unique (h₂.congr_of_eventuallyEq hev)
  -- `f 0 = y`
  have hf0 : f 0 = y := by
    have hequil := geodesicFlow_eqOn_of_zero_velocity (I := I) g p hε hflow hmem0
    have hTIoo : T ∈ Ioo (-ε) ε := ⟨by linarith [hε, hT], hTε⟩
    have hZT := hequil T hTIoo
    show (Z ((y, T⁻¹ • (0 : E)) : E × E) T).1 = y
    rw [smul_zero, hZT]
  -- `(df_y)_0 = id`
  have hfd0 : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E := by
    have haux : ∀ u : E, ‖u‖ < ρ → fderiv ℝ f 0 u = u := by
      intro u hu
      obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem u hu)
      have h0u : ‖(0 : ℝ) • u‖ < ρ := by rw [zero_smul, norm_zero]; exact hρpos
      have h0b : |(0 : ℝ)| < b := by rw [abs_zero]; exact lt_trans one_pos hb1
      have hv := hvel u 0 hu h0b h0u
      rw [zero_smul] at hv
      rw [hv, zero_mul, hz0]
      show T • (T⁻¹ • u) = u
      rw [smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
    refine ContinuousLinearMap.ext fun u => ?_
    rcases eq_or_ne u 0 with rfl | hu0
    · simp
    · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
      set c : ℝ := ρ / (2 * ‖u‖) with hcdef
      have hc : 0 < c := by positivity
      have hcu : ‖c • u‖ < ρ := by
        rw [norm_smul, Real.norm_of_nonneg hc.le, hcdef, div_mul_eq_mul_div,
          div_lt_iff₀ (by positivity)]
        nlinarith
      have h := haux (c • u) hcu
      rw [map_smul] at h
      have h' := smul_right_injective E hc.ne' h
      simpa using h'
  -- the chart target and base-set clauses
  have htarget : ∀ w' : E, ‖w'‖ < ρ → f w' ∈ (extChartAt I p).target := by
    intro w' hw'
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem w' hw')
    have hTmem : T ∈ Icc (-ε) ε := ⟨by linarith [hε, hT], hTε.le⟩
    exact (hzmem T hTmem).1
  have hbase : ∀ w' : E, ‖w'‖ < ρ →
      (extChartAt I p).symm (f w') ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    intro w' hw'
    have hfoot : (extChartAt I p).symm (f w') ∈ (chartAt H p).source := by
      have h := (extChartAt I p).map_target (htarget w' hw')
      rwa [extChartAt_source] at h
    rw [TangentBundle.trivializationAt_baseSet]; exact hfoot
  -- the geodesic ODE for the ray velocity
  have hODE : ∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
      HasDerivAt (fun t' : ℝ => fderiv ℝ f (t' • u) u)
        (- Geodesic.chartChristoffelContraction (I := I) g p
            (fderiv ℝ f (t • u) u) (fderiv ℝ f (t • u) u)
            (f (t • u))) t := by
    intro u t hu ht htu
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem u hu)
    have htT : t * T ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hT]
      have htεT : |t| < ε / T := lt_of_lt_of_le ht (min_le_right _ _)
      calc |t| * T < (ε / T) * T := mul_lt_mul_of_pos_right htεT hT
        _ = ε := by field_simp
    have hev : (fun t' : ℝ => fderiv ℝ f (t' • u) u) =ᶠ[𝓝 t]
        (fun t' : ℝ =>
          T • (Z ((y, T⁻¹ • u) : E × E) (t' * T)).2) := by
      have hopen : IsOpen {t' : ℝ | |t'| < b ∧ ‖t' • u‖ < ρ} := by
        refine (isOpen_lt continuous_abs continuous_const).inter ?_
        exact isOpen_lt (continuous_id.smul continuous_const).norm continuous_const
      filter_upwards [hopen.mem_nhds ⟨ht, htu⟩] with t' ht'
      exact hvel u t' hu ht'.1 ht'.2
    have hZs : HasDerivAt (Z ((y, T⁻¹ • u) : E × E))
        (geodesicSprayCoord (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2) (t * T) :=
      (hzd _ (Ioo_subset_Icc_self htT)).hasDerivAt (Icc_mem_nhds htT.1 htT.2)
    have hcomp : HasDerivAt
        (fun t' : ℝ => Z ((y, T⁻¹ • u) : E × E) (t' * T))
        (T • geodesicSprayCoord (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2) t :=
      hZs.scomp t (hasDerivAt_mul_const T)
    have hsnd : HasDerivAt
        (fun t' : ℝ => (Z ((y, T⁻¹ • u) : E × E) (t' * T)).2)
        (T • (- Geodesic.chartChristoffelContraction (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1)) t := by
      have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [geodesicSprayCoord_def] using h
    have h₂ : HasDerivAt
        (fun t' : ℝ => T • (Z ((y, T⁻¹ • u) : E × E) (t' * T)).2)
        (T • (T • (- Geodesic.chartChristoffelContraction (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1))) t :=
      hsnd.const_smul T
    have hfval : f (t • u) = (Z ((y, T⁻¹ • u) : E × E) (t * T)).1 := key u t hu ht
    have hvelval : fderiv ℝ f (t • u) u
        = T • (Z ((y, T⁻¹ • u) : E × E) (t * T)).2 := hvel u t hu ht htu
    have hD : T • (T • (- Geodesic.chartChristoffelContraction (I := I) g p
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((y, T⁻¹ • u) : E × E) (t * T)).1))
        = - Geodesic.chartChristoffelContraction (I := I) g p
            (fderiv ℝ f (t • u) u) (fderiv ℝ f (t • u) u) (f (t • u)) := by
      rw [hvelval, hfval, Geodesic.chartChristoffelContraction_smul_smul,
        smul_neg, smul_neg, smul_smul]
    exact hD ▸ (h₂.congr_of_eventuallyEq hev)
  exact ⟨hmem, f, fun _ => rfl, hf0, hC2, hfd0, htarget, hbase, hODE⟩

/-- **Math.** **The base-uniform Gauss radial lower bound** (do Carmo Ch. 3, the Cauchy–Schwarz
inequality driving Proposition 3.6, base-generalized and made uniform over the base). There are
thresholds `η, ρ > 0` such that for every base point `y` within `η` of the chart centre that lies
in the chart target, the flow reading `f_y` is a radial isometry onto the Gram form based at `y`
and does not shrink radial components:
`⟨v, ξ⟩_y² ≤ ⟨v, v⟩_y · ⟨(df_y)_v ξ, (df_y)_v ξ⟩_{f_y v}` for `‖v‖ < ρ`. This is the exact
`hradial` hypothesis the reach estimate `gauss_radius_reach_at` consumes, obtained by chaining
`gauss_surface_computation_at` (the surface identity) and `gauss_radial_lower_bound_at` on the
abstract package `exists_movingBase_ray_ode_ball`. It is the analytic heart of the lower-bound crux
`Hlb` of `prop:dc-ch3-4-2`. -/
theorem exists_movingBase_gauss_radial_lower_bound (g : RiemannianMetric I M) (p : M) :
    ∃ η ρ : ℝ, 0 < η ∧ 0 < ρ ∧
      ∀ y : E, dist y (extChartAt I p p) < η → y ∈ (extChartAt I p).target →
        ∃ f : E → E,
          f 0 = y ∧
          ContDiffOn ℝ 1 f (ball (0 : E) ρ) ∧
          (∀ w' : E, ‖w'‖ < ρ → f w' ∈ (extChartAt I p).target) ∧
          (∀ v ξ : E, ‖v‖ < ρ →
            chartMetricInner (I := I) g p y v ξ ^ 2
              ≤ chartMetricInner (I := I) g p y v v
                * chartMetricInner (I := I) g p (f v)
                    (fderiv ℝ f v ξ) (fderiv ℝ f v ξ)) := by
  obtain ⟨η, ρ, b, r, ε, T, Z, hηpos, hρpos, hb1, hr, hε, hT, hTε, hflow, H⟩ :=
    exists_movingBase_ray_ode_ball (I := I) g p
  refine ⟨η, ρ, hηpos, hρpos, ?_⟩
  intro y hy hytgt
  obtain ⟨hmem, f, hf_eq, hf0, hC2, hfd0, htarget, hbase, hODE⟩ := H y hy
  have hgauss : ∀ v w : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (f v) (fderiv ℝ f v v) (fderiv ℝ f v w)
        = chartMetricInner (I := I) g p y v w := fun v w hv =>
    gauss_surface_computation_at (I := I) g p f y hb1 hC2 hf0 hfd0 htarget hbase hODE v w hv
  refine ⟨f, hf0, hC2.of_le (by norm_num), htarget, fun v ξ hv => ?_⟩
  exact gauss_radial_lower_bound_at (I := I) g p f y hytgt htarget hgauss v ξ hv

end Exponential
end Riemannian

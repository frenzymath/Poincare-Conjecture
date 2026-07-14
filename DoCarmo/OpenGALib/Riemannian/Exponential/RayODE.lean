import OpenGALib.Riemannian.Geodesic.FlowC2Dependence
import OpenGALib.Riemannian.Exponential.C2Ball

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3

/-!
# The geodesic ODE along rays of the exponential chart reading

For the Gauss lemma (do Carmo Ch. 3, Lemma 3.5) the parametrized surface
`f(t,s) = exp_p(t·v(s))` is differentiated *in the fixed chart at `p`*: one needs,
besides the `C²` regularity of the chart reading
`f : w ↦ φ_p(exp_p(w))` (`exists_contDiffOn_two_extChartAt_expMap_ball`), the fact
that each ray curve `t ↦ f(t·u)` satisfies the **chart-coordinate geodesic
equation**: its velocity `V(t) = (df)_{t·u}(u)` obeys

`V̇(t) = −Γ_p(V(t), V(t))(f(t·u))`,

and `(df)_0 = id`. This file provides these facts on a common ball:

* `exists_expMap_ray_ode_ball` — there are `ρ > 0` and `b > 1` such that on the
  ball `B_ρ(0) ⊂ T_pM` the chart reading is `C²`, scaled vectors `a • u`
  (`‖u‖ < ρ`, `|a| < b`) lie in the exponential domain with image in the chart,
  `(df)_0 = id`, and along every ray the velocity satisfies the geodesic ODE.

Route: the uniform local flow `Z` of the coordinate spray
(`exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow`) is rescaled in fibre and
time, `ζ(s) = (Z₁(aTs), aT·Z₂(aTs))` with initial data `(φ_p(p), a•u)`; this is again
a spray trajectory, so `maximalGeodesic_eq_witness_of_mem_chart` identifies
`exp_p(a•u)` with `Z₁(aT)` for `|a| < ε/T`. Differentiating the identification in
`a` gives the velocity `(df)_{t·u}(u) = T·Z₂(tT)` and, through the spray ODE for
`Z`, the geodesic equation for the velocity.
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

set_option maxHeartbeats 1000000 in
/-- **Math.** **The chart reading of `exp_p` is `C²` on a ball and satisfies the
geodesic ODE along rays** (do Carmo Ch. 3, §2–3; the analytic package for the Gauss
lemma 3.5). There are `ρ > 0` and `b > 1` such that, writing
`f : w ↦ φ_p(exp_p(w))` for the chart reading of the exponential map:

* scaled vectors stay admissible: for `‖u‖ < ρ` and `|a| < b`, `a • u` lies in the
  exponential domain and `exp_p(a • u)` stays in the chart at `p`;
* `f` is `C²` on the ball `B_ρ(0)`;
* `(df)_0 = id` (do Carmo Ch. 3, Prop. 2.9, the derivative computation at `0`);
* **the ray velocity solves the chart geodesic equation**: for `‖u‖ < ρ`,
  `|t| < b`, `‖t • u‖ < ρ`, the velocity `t' ↦ (df)_{t'•u}(u)` has derivative
  `−Γ_p((df)_{t•u}(u), (df)_{t•u}(u))(f(t•u))` at `t`. Together with the chain rule
  this says each ray `t ↦ f(t·u)` is a chart-coordinate geodesic. -/
theorem exists_expMap_ray_ode_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ b : ℝ, 0 < ρ ∧ 1 < b ∧
      (∀ (u : E) (a : ℝ), ‖u‖ < ρ → |a| < b →
        ((a • u : E) : TangentSpace I p) ∈ expDomain (I := I) g p ∧
        expMap (I := I) g p ((a • u : E) : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ContDiffOn ℝ 2
        (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
        (ball (0 : E) ρ) ∧
      fderiv ℝ
          (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) 0
        = ContinuousLinearMap.id ℝ E ∧
      (∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
        HasDerivAt
          (fun t' : ℝ => fderiv ℝ
            (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
            (t' • u) u)
          (- Geodesic.chartChristoffelContraction (I := I) g p
              (fderiv ℝ (fun w : E =>
                extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
              (fderiv ℝ (fun w : E =>
                extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) (t • u) u)
              (extChartAt I p
                (expMap (I := I) g p ((t • u : E) : TangentSpace I p))))
          t) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hC2₁⟩ :=
    exists_contDiffOn_two_extChartAt_expMap_ball (I := I) g p
  obtain ⟨r, ε, T, Z, L, σ, τ, hT, hr, hε, hTε, hflow, hLip, hmax, hσ_ball,
    hC1τ, hC2τ⟩ :=
    exists_uniform_geodesic_flow_hasStrictFDerivAt_opFlow (I := I) g p
  set f : E → E :=
    fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  set z₀ : E × E := ((extChartAt I p p, (0 : E)) : E × E) with hz₀def
  set ρ : ℝ := min ρ₁ (r * T) with hρdef
  set b : ℝ := ε / T with hbdef
  have hρpos : 0 < ρ := lt_min hρ₁ (by positivity)
  have hb1 : 1 < b := (one_lt_div hT).mpr hTε
  have hρ_le₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρ_le₂ : ρ ≤ r * T := min_le_right _ _
  -- the rescaled initial condition lies in the flow ball
  have hmem_flowball : ∀ u : E, ‖u‖ ≤ r * T →
      ((extChartAt I p p, T⁻¹ • u) : E × E) ∈ closedBall z₀ r := by
    intro u hu
    rw [mem_closedBall, hz₀def, Prod.dist_eq]
    simp only [dist_self, dist_zero_right]
    refine max_le hr.le ?_
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hT.le, inv_mul_le_iff₀ hT]
    calc ‖u‖ ≤ r * T := hu
      _ = T * r := mul_comm r T
  -- the identification: `exp_p(a • u)` is computed by the rescaled flow trajectory
  have key : ∀ (u : E) (a : ℝ), ‖u‖ ≤ r * T → |a| < b →
      ((a • u : E) : TangentSpace I p) ∈ expDomain (I := I) g p ∧
      expMap (I := I) g p ((a • u : E) : TangentSpace I p) ∈ (chartAt H p).source ∧
      extChartAt I p (expMap (I := I) g p ((a • u : E) : TangentSpace I p))
        = (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T)).1 := by
    intro u a hu ha
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem_flowball u hu)
    have haT : |a * T| < ε := by
      rw [abs_mul, abs_of_pos hT]
      calc |a| * T < b * T := mul_lt_mul_of_pos_right ha hT
        _ = ε := by rw [hbdef, div_mul_cancel₀ _ hT.ne']
    -- the fibre/time-rescaled trajectory
    set S : (E × E) →L[ℝ] E × E :=
      (ContinuousLinearMap.fst ℝ E E).prod
        ((a * T) • ContinuousLinearMap.snd ℝ E E) with hSdef
    set ζ : ℝ → E × E := fun s =>
      S (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)) with hζdef
    set J : Set ℝ := {s : ℝ | a * T * s ∈ Ioo (-ε) ε} with hJdef
    have hJo : IsOpen J := isOpen_Ioo.preimage (continuous_const.mul continuous_id)
    have hJconv : Convex ℝ J := by
      intro x hx y hy θ₁ θ₂ hθ₁ hθ₂ hθ
      have hmem : θ₁ • (a * T * x) + θ₂ • (a * T * y) ∈ Ioo (-ε) ε :=
        (convex_Ioo (-ε) ε) hx hy hθ₁ hθ₂ hθ
      have harith : a * T * (θ₁ • x + θ₂ • y)
          = θ₁ • (a * T * x) + θ₂ • (a * T * y) := by
        simp only [smul_eq_mul]; ring
      show a * T * (θ₁ • x + θ₂ • y) ∈ Ioo (-ε) ε
      rw [harith]; exact hmem
    have hJc : IsPreconnected J := hJconv.isPreconnected
    have h0J : (0 : ℝ) ∈ J := by
      show a * T * 0 ∈ Ioo (-ε) ε
      rw [mul_zero]
      exact ⟨neg_lt_zero.mpr hε, hε⟩
    have h1J : (1 : ℝ) ∈ J := by
      show a * T * 1 ∈ Ioo (-ε) ε
      rw [mul_one]
      exact mem_Ioo.mpr (abs_lt.mp haT)
    -- initial value of the rescaled trajectory
    have hζ0 : ζ 0 = ((extChartAt I p p,
        ((a • u : E) : TangentSpace I p)) : E × E) := by
      rw [hζdef]
      simp only [mul_zero]
      rw [hz0]
      refine Prod.ext rfl ?_
      show (a * T) • (T⁻¹ • u) = a • u
      rw [smul_smul, mul_assoc, mul_inv_cancel₀ hT.ne', mul_one]
    -- the rescaled trajectory solves the spray ODE
    have hζd : ∀ s ∈ J, HasDerivAt ζ
        (geodesicSprayCoord (I := I) g p (ζ s).1 (ζ s).2) s := by
      intro s hs
      have hsIoo : a * T * s ∈ Ioo (-ε) ε := hs
      have hZs : HasDerivAt (Z ((extChartAt I p p, T⁻¹ • u) : E × E))
          (geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).1
            (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2) (a * T * s) :=
        (hzd _ (Ioo_subset_Icc_self hsIoo)).hasDerivAt (Icc_mem_nhds hsIoo.1 hsIoo.2)
      have hlin : HasDerivAt (fun s' : ℝ => a * T * s') (a * T) s := by
        simpa using (hasDerivAt_id s).const_mul (a * T)
      have hcomp : HasDerivAt
          (fun s' : ℝ => Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s'))
          ((a * T) • geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).1
            (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2) s :=
        hZs.scomp s hlin
      have hSd : HasDerivAt ζ
          (S ((a * T) • geodesicSprayCoord (I := I) g p
            (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).1
            (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2)) s :=
        S.hasFDerivAt.comp_hasDerivAt s hcomp
      refine hSd.congr_deriv ?_
      -- compute both sides componentwise
      rw [geodesicSprayCoord_def, geodesicSprayCoord_def]
      have hζs1 : (ζ s).1
          = (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).1 := rfl
      have hζs2 : (ζ s).2
          = (a * T) • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2 := rfl
      rw [hζs1, hζs2]
      refine Prod.ext ?_ ?_
      · show (a * T) • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2
          = (a * T) • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2
        rfl
      · show (a * T) • ((a * T) •
            (- Geodesic.chartChristoffelContraction (I := I) g p
              (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2
              (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2
              (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).1))
          = - Geodesic.chartChristoffelContraction (I := I) g p
              ((a * T) • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2)
              ((a * T) • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).2)
              (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T * s)).1
        rw [Geodesic.chartChristoffelContraction_smul_smul]
        rw [smul_neg, smul_neg, smul_smul]
    -- membership in the tangent chart target
    have hζmem : ∀ s ∈ J, ζ s ∈
        (extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).target := by
      intro s hs
      have hsIoo : a * T * s ∈ Ioo (-ε) ε := hs
      rw [extChartAt_tangent_target (I := I) p]
      have hZmem := hzmem _ (Ioo_subset_Icc_self hsIoo)
      exact ⟨hZmem.1, mem_univ _⟩
    -- the geodesic witness and its consequences
    obtain ⟨hwit, hwsrc, hwchart⟩ :=
      isGeodesicOnWithInitial_of_hasDerivAt_sprayCoord (I := I) g p
        ((a • u : E) : TangentSpace I p) hζ0 hζd hζmem
    have hdom : ((a • u : E) : TangentSpace I p) ∈ expDomain (I := I) g p :=
      subset_maximalGeodesicInterval_of_witness (I := I) hwit hJo hJc h0J h1J
    have hval : maximalGeodesic (I := I) g p ((a • u : E) : TangentSpace I p) 1
        = ((extChartAt I.tangent (⟨p, (0 : E)⟩ : TangentBundle I M)).symm
            (ζ 1)).proj :=
      maximalGeodesic_eq_witness_of_mem_chart (I := I) hwit hJo hJc h0J hwsrc h1J
    refine ⟨hdom, ?_, ?_⟩
    · show maximalGeodesic (I := I) g p ((a • u : E) : TangentSpace I p) 1 ∈ _
      rw [hval]
      exact hwsrc 1 h1J
    · show extChartAt I p
          (maximalGeodesic (I := I) g p ((a • u : E) : TangentSpace I p) 1) = _
      rw [hval, hwchart 1 h1J]
      show (ζ 1).1 = _
      rw [hζdef]
      simp only [mul_one]
      rfl
  -- the chart velocity along a ray is the rescaled flow velocity
  have hvel : ∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
      fderiv ℝ f (t • u) u
        = T • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2 := by
    intro u t hu ht htu
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem_flowball u (hu.le.trans hρ_le₂))
    have htT : t * T ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hT]
      calc |t| * T < b * T := mul_lt_mul_of_pos_right ht hT
        _ = ε := by rw [hbdef, div_mul_cancel₀ _ hT.ne']
    -- chain-rule derivative of the ray
    have hdiff : DifferentiableAt ℝ f (t • u) :=
      (hC2₁.contDiffAt (isOpen_ball.mem_nhds
        (mem_ball_zero_iff.mpr (lt_of_lt_of_le htu hρ_le₁)))).differentiableAt
        (by norm_num)
    have hray : HasDerivAt (fun a : ℝ => a • u) u t := by
      simpa using (hasDerivAt_id t).smul_const u
    have h₁ : HasDerivAt (fun a : ℝ => f (a • u)) (fderiv ℝ f (t • u) u) t := by
      simpa [Function.comp_def] using hdiff.hasFDerivAt.comp_hasDerivAt t hray
    -- flow-form derivative of the ray
    have hZs : HasDerivAt (Z ((extChartAt I p p, T⁻¹ • u) : E × E))
        (geodesicSprayCoord (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2) (t * T) :=
      (hzd _ (Ioo_subset_Icc_self htT)).hasDerivAt (Icc_mem_nhds htT.1 htT.2)
    have hcomp : HasDerivAt
        (fun a : ℝ => Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T))
        (T • geodesicSprayCoord (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2) t :=
      hZs.scomp t (hasDerivAt_mul_const T)
    have h₂ : HasDerivAt
        (fun a : ℝ => (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T)).1)
        (T • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2) t := by
      have hfst := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [geodesicSprayCoord_def] using hfst
    -- the two forms agree near `t`
    have hev : (fun a : ℝ => f (a • u)) =ᶠ[𝓝 t]
        (fun a : ℝ => (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (a * T)).1) := by
      have hopen : IsOpen {a : ℝ | |a| < b} :=
        isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds ht] with a ha
      exact (key u a (hu.le.trans hρ_le₂) ha).2.2
    exact h₁.unique (h₂.congr_of_eventuallyEq hev)
  -- `(df)_0 = id`
  have hfd0 : fderiv ℝ f 0 = ContinuousLinearMap.id ℝ E := by
    have haux : ∀ u : E, ‖u‖ < ρ → fderiv ℝ f 0 u = u := by
      intro u hu
      obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem_flowball u (hu.le.trans hρ_le₂))
      have h0u : ‖(0 : ℝ) • u‖ < ρ := by
        rw [zero_smul, norm_zero]; exact hρpos
      have h0b : |(0 : ℝ)| < b := by
        rw [abs_zero]; exact lt_trans one_pos hb1
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
  -- the geodesic ODE for the ray velocity
  have hODE : ∀ (u : E) (t : ℝ), ‖u‖ < ρ → |t| < b → ‖t • u‖ < ρ →
      HasDerivAt (fun t' : ℝ => fderiv ℝ f (t' • u) u)
        (- Geodesic.chartChristoffelContraction (I := I) g p
            (fderiv ℝ f (t • u) u) (fderiv ℝ f (t • u) u)
            (f (t • u))) t := by
    intro u t hu ht htu
    obtain ⟨hz0, hzd, hzmem⟩ := hflow _ (hmem_flowball u (hu.le.trans hρ_le₂))
    have htT : t * T ∈ Ioo (-ε) ε := by
      rw [mem_Ioo, ← abs_lt, abs_mul, abs_of_pos hT]
      calc |t| * T < b * T := mul_lt_mul_of_pos_right ht hT
        _ = ε := by rw [hbdef, div_mul_cancel₀ _ hT.ne']
    -- the velocity agrees with the flow velocity near `t`
    have hev : (fun t' : ℝ => fderiv ℝ f (t' • u) u) =ᶠ[𝓝 t]
        (fun t' : ℝ =>
          T • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t' * T)).2) := by
      have hopen : IsOpen {t' : ℝ | |t'| < b ∧ ‖t' • u‖ < ρ} := by
        refine (isOpen_lt continuous_abs continuous_const).inter ?_
        exact isOpen_lt (continuous_id.smul continuous_const).norm continuous_const
      filter_upwards [hopen.mem_nhds ⟨ht, htu⟩] with t' ht'
      exact hvel u t' hu ht'.1 ht'.2
    -- flow-form derivative of the velocity
    have hZs : HasDerivAt (Z ((extChartAt I p p, T⁻¹ • u) : E × E))
        (geodesicSprayCoord (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2) (t * T) :=
      (hzd _ (Ioo_subset_Icc_self htT)).hasDerivAt (Icc_mem_nhds htT.1 htT.2)
    have hcomp : HasDerivAt
        (fun t' : ℝ => Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t' * T))
        (T • geodesicSprayCoord (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2) t :=
      hZs.scomp t (hasDerivAt_mul_const T)
    have hsnd : HasDerivAt
        (fun t' : ℝ => (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t' * T)).2)
        (T • (- Geodesic.chartChristoffelContraction (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1)) t := by
      have h := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t hcomp
      simpa [geodesicSprayCoord_def] using h
    have h₂ : HasDerivAt
        (fun t' : ℝ =>
          T • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t' * T)).2)
        (T • (T • (- Geodesic.chartChristoffelContraction (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1))) t :=
      hsnd.const_smul T
    -- identify the derivative with the Christoffel form
    have hfval : f (t • u)
        = (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1 :=
      (key u t (hu.le.trans hρ_le₂) ht).2.2
    have hvelval : fderiv ℝ f (t • u) u
        = T • (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2 :=
      hvel u t hu ht htu
    have hD : T • (T • (- Geodesic.chartChristoffelContraction (I := I) g p
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).2
          (Z ((extChartAt I p p, T⁻¹ • u) : E × E) (t * T)).1))
        = - Geodesic.chartChristoffelContraction (I := I) g p
            (fderiv ℝ f (t • u) u) (fderiv ℝ f (t • u) u) (f (t • u)) := by
      rw [hvelval, hfval, Geodesic.chartChristoffelContraction_smul_smul,
        smul_neg, smul_neg, smul_smul]
    exact hD ▸ (h₂.congr_of_eventuallyEq hev)
  refine ⟨ρ, b, hρpos, hb1, ?_, hC2₁.mono (ball_subset_ball hρ_le₁), hfd0, hODE⟩
  intro u a hu ha
  exact ⟨(key u a (hu.le.trans hρ_le₂) ha).1, (key u a (hu.le.trans hρ_le₂) ha).2.1⟩

end Exponential
end Riemannian

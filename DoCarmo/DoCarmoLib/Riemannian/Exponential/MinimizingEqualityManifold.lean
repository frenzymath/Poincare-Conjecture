import DoCarmoLib.Riemannian.Exponential.MinimizingEquality
import DoCarmoLib.Riemannian.Exponential.NormalBallEDist
import DoCarmoLib.Riemannian.Exponential.RayGeodesic
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback

/-!
# The equality case of the minimizing property, in the manifold
(do Carmo Ch. 3, Prop. 3.6, equality analysis, manifold stage)

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 3.6, equality clause: if a
`C¹` competitor `σ : [0,1] → M` from `p` to `exp_p v` stays in a Gauss ball
image `exp_p(B_ρ(0))` and realizes the length `√⟨v,v⟩_p` of the radial
geodesic, then `σ` is a **monotone reparametrization of the radial geodesic**
`τ ↦ exp_p(τ v)`; in particular `σ([0,1]) = exp_p([0,1] · v)` — do Carmo's
`c([0,1]) = γ([0,1])`.

This is the transport of the polar equality analysis
(`exists_gauss_equality_ray_ball`, `exists_gauss_equality_radial_ball`) to the
manifold statement, through the `C¹` local inverse of `exp_p`
(`exists_c1_local_diffeomorphism_expMap`):

* the **polar lift** `w = exp_p⁻¹ ∘ σ` (read through the chart at `p`) is a
  `C¹` curve in `B_ρ(0)` with `w(0) = 0`, `w(1) = v`;
* the mathlib `pathELength` of `σ` is bridged to the chart integral of the
  polar speed (`pathELength_eq_ofReal_integral_chartMetricInner` plus the
  chain rule), so length equality becomes the FTC-form hypothesis of the
  polar equality lemmas;
* the ray lemma gives `w(t) = (r(t)/r(1)) · v` with `r(t) = |w(t)|_p`, and
  the radial lemma makes `r` monotone (its derivative is the nonnegative
  speed), so `s(t) = r(t)/r(1)` is the desired monotone reparametrization;
* the image equality follows from the intermediate value theorem applied to
  the continuous monotone radius.

The main theorems:

* `exists_gauss_equality_manifold_ball` — the equality case for competitors
  confined to the Gauss ball;
* `exists_gauss_equality_geodesic_ball` — an arclength-proportional confined
  competitor **is** the radial geodesic `t ↦ exp_p(tv)`, satisfying the
  intrinsic geodesic equation on `(0,1)` (the normal-ball core of do Carmo's
  Corollary 3.9);
* `exists_forall_mem_expMap_ball_of_pathELength_lt` — **confinement**: a
  short enough `C¹` curve from `p` stays in `exp_p(B_ρ'(0))`, by the escape
  estimate applied to reparametrized truncations;
* `exists_gauss_equality_manifold`, `exists_gauss_equality_geodesic` — the
  same equality statements with **no** stay-in-ball hypothesis: equality
  competitors are automatically confined.

The remaining gap to do Carmo's full Prop. 3.6 equality clause is the
piecewise-`C¹` version (splitting the competitor at its vertices).
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The equality case of the minimizing property, in the manifold**
(do Carmo Ch. 3, Prop. 3.6, equality clause, `C¹` case). There is a Gauss ball
radius `ρ > 0` at `p` (with `exp_p` defined, landing in the chart at `p`, and
injective on `B_ρ(0)`) such that every `C¹` competitor `σ : [0,1] → M` from
`p` to `exp_p v` (`‖v‖ < ρ`) that stays in `exp_p(B_ρ(0))` and realizes the
radial length — `pathELength σ = √⟨v,v⟩_p` — is a **monotone reparametrization
of the radial geodesic**: there is a continuous monotone `s : [0,1] → [0,1]`
with `s(0) = 0`, `s(1) = 1` and `σ(t) = exp_p(s(t) · v)` for all `t`; in
particular `σ([0,1]) = exp_p([0,1] · v)` (do Carmo's `c([0,1]) = γ([0,1])`).

The polar lift `w = exp_p⁻¹ ∘ σ` realizes the FTC-form equality, so the ray
lemma (`exists_gauss_equality_ray_ball`) forces `w(t) = (r(t)/r(1)) · v` with
`r = |w|_p`, and the radial lemma (`exists_gauss_equality_radial_ball`) makes
`r` monotone; the image equality is the intermediate value theorem for `r`. -/
theorem exists_gauss_equality_manifold_ball [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ v : E, ‖v‖ < ρ → ∀ σ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∀ t ∈ Icc (0 : ℝ) 1, σ t ∈
          (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) ρ) →
        Manifold.pathELength I σ 0 1
          = ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v)) →
        ∃ s : ℝ → ℝ,
          ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          (∀ t ∈ Icc (0 : ℝ) 1, s t ∈ Icc (0 : ℝ) 1 ∧
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
            = ENNReal.ofReal (s t * Real.sqrt
                (chartMetricInner (I := I) g p (extChartAt I p p) v v))) ∧
          σ '' Icc 0 1
            = (fun τ : ℝ => expMap (I := I) g p ((τ • v : E) : TangentSpace I p)) ''
                Icc 0 1) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρy, hρy, hdomy, hsrcy, hray⟩ :=
    exists_gauss_equality_ray_ball (I := I) g p
  obtain ⟨ρr, hρr, hdomr, hsrcr, hradial⟩ :=
    exists_gauss_equality_radial_ball (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  set ρ : ℝ := min ε₁ (min ρy ρr) with hρdef
  have hρ : 0 < ρ := lt_min hε₁ (lt_min hρy hρr)
  have hρε₁ : ρ ≤ ε₁ := min_le_left _ _
  have hρρy : ρ ≤ ρy := (min_le_right _ _).trans (min_le_left _ _)
  have hρρr : ρ ≤ ρr := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ, hρ, fun w hw => hdom₁ w (hw.trans_le hρε₁),
    fun w hw => hsrc₁ w (hw.trans_le hρε₁),
    hinj₁.mono (ball_subset_ball hρε₁), ?_⟩
  intro v hv σ hσ hσ0 hσ1 htrace hlen
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  -- the polar lift of the competitor through the local inverse of `exp_p`
  set w : ℝ → E := fun t => finv (extChartAt I p (σ t)) with hw_def
  -- each point of the competitor comes from a unique parameter in the ball
  have hwt : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ ∧
      expMap (I := I) g p (w t : TangentSpace I p) = σ t := by
    intro t ht
    obtain ⟨x, hx, hxe⟩ := htrace t ht
    have hxball : ‖x‖ < ρ := by simpa [mem_ball_zero_iff] using hx
    have hwx : w t = x := by
      rw [hw_def]
      simp only
      rw [← hxe]
      exact hlinv x (hxball.trans_le hρε₁)
    rw [hwx]
    exact ⟨hxball, hxe⟩
  have hsrcσ : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ (chartAt H p).source := by
    intro t ht
    obtain ⟨hwb, hwe⟩ := hwt t ht
    rw [← hwe]
    exact hsrc₁ (w t) (hwb.trans_le hρε₁)
  -- regularity of the chart reading and of the polar lift
  have huC1 : ContDiffOn ℝ 1 (fun t => extChartAt I p (σ t)) (Icc 0 1) :=
    contDiffOn_extChartAt_comp hσ hsrcσ
  have humaps : MapsTo (fun t => extChartAt I p (σ t)) (Icc (0 : ℝ) 1)
      ((fun z : E => extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) ''
        ball (0 : E) ε₁) := by
    intro t ht
    obtain ⟨hwb, hwe⟩ := hwt t ht
    exact ⟨w t, mem_ball_zero_iff.mpr (hwb.trans_le hρε₁),
      congrArg (extChartAt I p) hwe⟩
  have hwC1 : ContDiffOn ℝ 1 w (Icc 0 1) := by
    have h := hfinvC1.comp huC1 humaps
    exact h.congr fun t _ => by rw [hw_def]; rfl
  have hwcont : ContinuousOn w (Icc (0 : ℝ) 1) := hwC1.continuousOn
  have hw'cont : ContinuousOn (derivWithin w (Icc 0 1)) (Icc (0 : ℝ) 1) :=
    hwC1.continuousOn_derivWithin (uniqueDiffOn_Icc one_pos) le_rfl
  have hw'deriv : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt w (derivWithin w (Icc 0 1) t) t := by
    intro t ht
    have h1 : HasDerivWithinAt w (derivWithin w (Icc 0 1) t) (Icc 0 1) t :=
      (hwC1.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt
    exact h1.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  -- endpoint values of the polar lift
  have hw0 : w 0 = 0 := by
    have h : extChartAt I p (σ 0)
        = extChartAt I p (expMap (I := I) g p ((0 : E) : TangentSpace I p)) := by
      rw [hσ0]
      exact (congrArg (extChartAt I p) (expMap_zero (I := I) g p)).symm
    rw [hw_def]
    simp only
    rw [h]
    exact hlinv 0 (by simpa using hε₁)
  have hw1 : w 1 = v := by
    have h : extChartAt I p (σ 1)
        = extChartAt I p (expMap (I := I) g p (v : TangentSpace I p)) := by
      rw [hσ1]
    rw [hw_def]
    simp only
    rw [h]
    exact hlinv v (hv.trans_le hρε₁)
  -- the chain rule: the chart velocity of `σ` is `Df_{w(t)}(w'(t))`
  have hchain : ∀ t ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun s => extChartAt I p (σ s))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t)) t := by
    intro t ht
    have hwb : ‖w t‖ < ρ := (hwt t (Ioo_subset_Icc_self ht)).1
    have hf_at : HasFDerivAt (fun z : E =>
        extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t))
        (w t) :=
      ((hfC1.contDiffAt (isOpen_ball.mem_nhds
        (mem_ball_zero_iff.mpr (hwb.trans_le hρε₁)))).differentiableAt
          one_ne_zero).hasFDerivAt
    have hcomp : HasDerivAt (fun s => extChartAt I p
        (expMap (I := I) g p (w s : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t)) t :=
      hf_at.comp_hasDerivAt t (hw'deriv t ht)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
    rw [(hwt s hs).2]
  have hu'eq : ∀ t ∈ Ioo (0 : ℝ) 1,
      derivWithin (fun s => extChartAt I p (σ s)) (Icc 0 1) t
        = fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t) := by
    intro t ht
    exact (hchain t ht).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc one_pos t (Ioo_subset_Icc_self ht))
  -- the length bridge: `pathELength σ` is the chart integral of the polar speed
  have hbridge := pathELength_eq_ofReal_integral_chartMetricInner (I := I) g
    zero_le_one hσ hsrcσ
  have hIcongr : (∫ t in (0 : ℝ)..1, Real.sqrt
      (chartMetricInner (I := I) g p (extChartAt I p (σ t))
        (derivWithin (fun s => extChartAt I p (σ s)) (Icc 0 1) t)
        (derivWithin (fun s => extChartAt I p (σ s)) (Icc 0 1) t)))
      = ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc 0 1) t))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc 0 1) t))) := by
    rw [intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_of_le zero_le_one,
      MeasureTheory.integral_Ioc_eq_integral_Ioo,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [hu'eq t ht, (hwt t (Ioo_subset_Icc_self ht)).2]
  -- real equality of the polar-speed integral with the radius gain
  have hInonneg : (0 : ℝ) ≤ ∫ t in (0 : ℝ)..1, Real.sqrt
      (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t))) :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => Real.sqrt_nonneg _
  have heqI : (∫ t in (0 : ℝ)..1, Real.sqrt
      (chartMetricInner (I := I) g p
        (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t))
        (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
          (w t) (derivWithin w (Icc 0 1) t))))
      = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
    have h1 : ENNReal.ofReal (∫ t in (0 : ℝ)..1, Real.sqrt
        (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc 0 1) t))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc 0 1) t))))
        = ENNReal.ofReal (Real.sqrt
            (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
      rw [← hIcongr, ← hbridge]
      exact hlen
    exact (ENNReal.ofReal_eq_ofReal_iff hInonneg (Real.sqrt_nonneg _)).mp h1
  -- the FTC-form equality hypothesis of the polar lemmas
  have hFTC : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w 1) (w 1))
      - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w 0) (w 0))
      = ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc 0 1) t))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w t) (derivWithin w (Icc 0 1) t))) := by
    rw [hw1, hw0, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero, heqI]
  -- ball bounds for the polar lemmas
  have hwball_y : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρy :=
    fun t ht => ((hwt t ht).1).trans_le hρρy
  have hwball_r : ∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρr :=
    fun t ht => ((hwt t ht).1).trans_le hρρr
  -- the polar equality lemmas: the ray identity and the monotone radius
  have hraykey := hray w (derivWithin w (Icc 0 1)) hwcont hw'deriv hw'cont
    hwball_y hw0 hFTC
  have hradialkey := (hradial w (derivWithin w (Icc 0 1)) 0 1 one_pos hwcont
    hw'deriv hw'cont hwball_r hFTC).1
  -- the radius of the polar lift: continuous, nonnegative, monotone
  have hrcont : ContinuousOn (fun t => Real.sqrt
      (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)))
      (Icc (0 : ℝ) 1) := by
    refine Real.continuous_sqrt.comp_continuousOn ?_
    exact continuousOn_chartMetricInner_along (I := I) g p continuousOn_const
      hwcont hwcont fun t _ => mem_extChartAt_target p
  have hrmono : MonotoneOn (fun t => Real.sqrt
      (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)))
      (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hrcont ?_ ?_
    · rw [interior_Icc]
      exact fun t ht => ((hradialkey t ht).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      rw [(hradialkey t ht).deriv]
      exact Real.sqrt_nonneg _
  have hr0 : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
      (w 0) (w 0)) = 0 := by
    rw [hw0, chartMetricInner_zero_left, Real.sqrt_zero]
  -- the running length: `pathELength σ 0 t` equals the radius of the polar lift
  have hfderivcont : ContinuousOn (fun t => fderiv ℝ (fun z : E =>
      extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t))
      (Icc (0 : ℝ) 1) := by
    refine (hfC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hwcont ?_
    exact fun t ht => mem_ball_zero_iff.mpr (((hwt t ht).1).trans_le hρε₁)
  have hspeedcont : ContinuousOn (fun t => Real.sqrt (chartMetricInner (I := I) g p
      (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
      (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
        (w t) (derivWithin w (Icc 0 1) t))
      (fderiv ℝ (fun z : E =>
          extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
        (w t) (derivWithin w (Icc 0 1) t)))) (Icc (0 : ℝ) 1) := by
    refine Real.continuous_sqrt.comp_continuousOn ?_
    refine continuousOn_chartMetricInner_along (I := I) g p ?_
      (hfderivcont.clm_apply hw'cont) (hfderivcont.clm_apply hw'cont) ?_
    · refine (huC1.continuousOn).congr fun t ht => ?_
      exact congrArg (extChartAt I p) (hwt t ht).2
    · intro t ht
      have hmem : expMap (I := I) g p (w t : TangentSpace I p)
          ∈ (extChartAt I p).source := by
        rw [extChartAt_source]
        exact hsrc₁ (w t) (((hwt t ht).1).trans_le hρε₁)
      exact (extChartAt I p).map_source hmem
  have hrunning : ∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w t) (w t))) := by
    intro t ht
    rcases ht.1.eq_or_lt with rfl | ht0
    · rw [Manifold.pathELength_self, hw0, chartMetricInner_zero_left,
        Real.sqrt_zero, ENNReal.ofReal_zero]
    · have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl ht.2
      have hbridge_t := pathELength_eq_ofReal_integral_chartMetricInner (I := I) g
        ht0.le (hσ.mono hsub) fun τ hτ => hsrcσ τ (hsub hτ)
      rw [hbridge_t]
      congr 1
      have hIcongr_t : (∫ τ in (0 : ℝ)..t, Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p (σ τ))
            (derivWithin (fun s => extChartAt I p (σ s)) (Icc 0 t) τ)
            (derivWithin (fun s => extChartAt I p (σ s)) (Icc 0 t) τ)))
          = ∫ τ in (0 : ℝ)..t, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w τ : TangentSpace I p)))
              (fderiv ℝ (fun z : E =>
                  extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                (w τ) (derivWithin w (Icc 0 1) τ))
              (fderiv ℝ (fun z : E =>
                  extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
                (w τ) (derivWithin w (Icc 0 1) τ))) := by
        rw [intervalIntegral.integral_of_le ht0.le,
          intervalIntegral.integral_of_le ht0.le,
          MeasureTheory.integral_Ioc_eq_integral_Ioo,
          MeasureTheory.integral_Ioc_eq_integral_Ioo]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo fun τ hτ => ?_
        have hτ1 : τ ∈ Ioo (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans_le ht.2⟩
        have hd : derivWithin (fun s => extChartAt I p (σ s)) (Icc 0 t) τ
            = fderiv ℝ (fun z : E =>
                extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
              (w τ) (derivWithin w (Icc 0 1) τ) :=
          (hchain τ hτ1).hasDerivWithinAt.derivWithin
            (uniqueDiffOn_Icc ht0 τ (Ioo_subset_Icc_self hτ))
        rw [hd, (hwt τ (Ioo_subset_Icc_self hτ1)).2]
      rw [hIcongr_t]
      have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
        (f := fun s : ℝ => Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w s) (w s)))
        (f' := fun τ : ℝ => Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w τ : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w τ) (derivWithin w (Icc 0 1) τ))
          (fderiv ℝ (fun z : E =>
              extChartAt I p (expMap (I := I) g p (z : TangentSpace I p)))
            (w τ) (derivWithin w (Icc 0 1) τ))))
        ht0.le (hrcont.mono hsub)
        (fun τ hτ => ((hradialkey τ ⟨hτ.1, hτ.2.trans_le ht.2⟩).hasDerivWithinAt))
        ((hspeedcont.mono hsub).intervalIntegrable_of_Icc ht0.le)
      rw [hftc]
      simp only [hr0, sub_zero]
  -- final assembly, splitting on the degenerate direction `v = 0`
  by_cases hv0 : v = 0
  · -- degenerate case: the competitor is constant at `p`
    subst hv0
    have hwzero : ∀ t ∈ Icc (0 : ℝ) 1, w t = 0 := by
      intro t ht
      have h := hraykey t ht
      rw [hw1] at h
      simpa using h
    have hσconst : ∀ t ∈ Icc (0 : ℝ) 1, σ t = p := by
      intro t ht
      rw [← (hwt t ht).2, hwzero t ht]
      exact expMap_zero (I := I) g p
    have hexp0 : ∀ τ : ℝ, expMap (I := I) g p ((τ • (0 : E) : E) : TangentSpace I p)
        = p := by
      intro τ
      rw [smul_zero]
      exact expMap_zero (I := I) g p
    refine ⟨fun t => t, continuousOn_id, monotone_id.monotoneOn _, rfl, rfl,
      fun t ht => ⟨ht, by rw [hσconst t ht, hexp0 t]⟩, ?_, ?_⟩
    · intro t ht
      rw [hrunning t ht, hwzero t ht, chartMetricInner_zero_left, Real.sqrt_zero,
        mul_zero]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        simp only [hexp0]
        exact (hσconst t ht).symm⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by
        simp only [hexp0]
        exact hσconst 0 ⟨le_rfl, zero_le_one⟩⟩
  · -- nondegenerate case: reparametrize by the normalized radius
    have hQv_pos : 0 < chartMetricInner (I := I) g p (extChartAt I p p) v v := by
      have h1 := hgramV _ (mem_of_mem_nhds hVc) v
      have h2 : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      nlinarith [sq_nonneg ‖v‖]
    have hr1 : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w 1) (w 1))
        = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
      rw [hw1]
    have hr1pos : 0 < Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p p) (w 1) (w 1)) := by
      rw [hr1]
      exact Real.sqrt_pos.mpr hQv_pos
    -- the reparametrization: the normalized radius
    set s : ℝ → ℝ := fun t => Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p p) (w t) (w t))
      / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (w 1) (w 1)) with hs_def
    have hskey : ∀ t ∈ Icc (0 : ℝ) 1,
        σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p) := by
      intro t ht
      have h := hraykey t ht
      rw [← (hwt t ht).2]
      congr 1
      rw [hs_def]
      simp only
      rw [← hw1]
      exact h
    have hsnn : ∀ t ∈ Icc (0 : ℝ) 1, 0 ≤ s t := by
      intro t ht
      exact div_nonneg (Real.sqrt_nonneg _) hr1pos.le
    have hsle1 : ∀ t ∈ Icc (0 : ℝ) 1, s t ≤ 1 := by
      intro t ht
      rw [hs_def]
      simp only
      rw [div_le_one hr1pos]
      exact hrmono ht (right_mem_Icc.mpr zero_le_one) ht.2
    have hscont : ContinuousOn s (Icc (0 : ℝ) 1) := hrcont.div_const _
    have hsmono : MonotoneOn s (Icc (0 : ℝ) 1) := by
      intro x hx y hy hxy
      exact div_le_div_of_nonneg_right (hrmono hx hy hxy) hr1pos.le
    have hs0 : s 0 = 0 := by
      rw [hs_def]
      simp only
      rw [hr0, zero_div]
    have hs1 : s 1 = 1 := div_self hr1pos.ne'
    refine ⟨s, hscont, hsmono, hs0, hs1,
      fun t ht => ⟨⟨hsnn t ht, hsle1 t ht⟩, hskey t ht⟩, ?_, ?_⟩
    · intro t ht
      rw [hrunning t ht]
      congr 1
      rw [hs_def]
      simp only
      rw [← hr1, div_mul_cancel₀ _ hr1pos.ne']
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨s t, ⟨hsnn t ht, hsle1 t ht⟩, (hskey t ht).symm⟩
    · rintro ⟨τ, hτ, rfl⟩
      -- the intermediate value theorem: some time realizes the radius `τ · r(1)`
      have hmem : τ * Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p p) (w 1) (w 1))
          ∈ Icc (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w 0) (w 0)))
            (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w 1) (w 1))) := by
        constructor
        · rw [hr0]
          exact mul_nonneg hτ.1 hr1pos.le
        · calc τ * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
              (w 1) (w 1))
              ≤ 1 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w 1) (w 1)) :=
                mul_le_mul_of_nonneg_right hτ.2 hr1pos.le
            _ = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w 1) (w 1)) := one_mul _
      obtain ⟨t, htI, hrt⟩ := intermediate_value_Icc zero_le_one hrcont hmem
      refine ⟨t, htI, ?_⟩
      rw [hskey t htI]
      congr 2
      have hrt' : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (w t) (w t))
          = τ * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w 1) (w 1)) := hrt
      rw [hs_def]
      simp only
      rw [hrt']
      exact mul_div_cancel_right₀ τ hr1pos.ne'

/-- **Math.** **An arclength-proportional competitor realizing the radial length
IS the radial geodesic** (do Carmo Ch. 3, Prop. 3.6 equality clause together
with the normal-ball core of Cor. 3.9, `C¹` case). There is a Gauss ball
radius `ρ > 0` at `p` such that every `C¹` curve `σ : [0,1] → M` from `p` to
`exp_p v` (`‖v‖ < ρ`) that stays in `exp_p(B_ρ(0))` and is **parametrized
proportionally to arc length while realizing the radial length** — i.e.
`pathELength σ 0 t = t · √⟨v,v⟩_p` for all `t ∈ [0,1]` — coincides with the
radial geodesic **with matching parametrization**: `σ(t) = exp_p(t v)` for all
`t ∈ [0,1]`; in particular `σ` satisfies the intrinsic geodesic equation on
`(0,1)`.

This is the step of do Carmo's Corollary 3.9 that turns the equality case of
the minimizing property into the geodesic property: the running-length export
of `exists_gauss_equality_manifold_ball` pins the monotone reparametrization
to `s(t) = t`, and the geodesic equation transfers from the radial geodesic
(`exists_isGeodesicOn_expMap_ray`) by locality of the moving-foot equation. -/
theorem exists_gauss_equality_geodesic_ball [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ v : E, ‖v‖ < ρ → ∀ σ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∀ t ∈ Icc (0 : ℝ) 1, σ t ∈
          (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) ρ) →
        (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
          = ENNReal.ofReal (t * Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v))) →
        (∀ t ∈ Icc (0 : ℝ) 1,
          σ t = expMap (I := I) g p ((t • v : E) : TangentSpace I p)) ∧
        IsGeodesicOn (I := I) g σ (Ioo 0 1)) := by
  classical
  obtain ⟨ρ₀, hρ₀, hdom₀, hsrc₀, hinj₀, hkey⟩ :=
    exists_gauss_equality_manifold_ball (I := I) g p
  obtain ⟨ρg, bg, hρg, hbg, hdombg, hgeo⟩ :=
    exists_isGeodesicOn_expMap_ray (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  set ρ : ℝ := min ρ₀ ρg with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hρg
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρρg : ρ ≤ ρg := min_le_right _ _
  refine ⟨ρ, hρ, fun w hw => hdom₀ w (hw.trans_le hρρ₀),
    fun w hw => hsrc₀ w (hw.trans_le hρρ₀),
    hinj₀.mono (ball_subset_ball hρρ₀), ?_⟩
  intro v hv σ hσ hσ0 hσ1 htrace harc
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have hlen : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
    have h := harc 1 (right_mem_Icc.mpr zero_le_one)
    rwa [one_mul] at h
  have htrace' : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈
      (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        ball (0 : E) ρ₀ :=
    fun t ht => Set.image_mono (ball_subset_ball hρρ₀) (htrace t ht)
  obtain ⟨s, hscont, hsmono, hs0, hs1, hpt, hrun, himg⟩ :=
    hkey v (hv.trans_le hρρ₀) σ hσ hσ0 hσ1 htrace' hlen
  have hptv : ∀ t ∈ Icc (0 : ℝ) 1,
      σ t = expMap (I := I) g p ((t • v : E) : TangentSpace I p) := by
    intro t ht
    by_cases hv0 : v = 0
    · subst hv0
      have h1 := (hpt t ht).2
      rw [h1, smul_zero, smul_zero]
    · have hQv_pos : 0 < chartMetricInner (I := I) g p (extChartAt I p p) v v := by
        have h1 := hgramV _ (mem_of_mem_nhds hVc) v
        have h2 : 0 < ‖v‖ := norm_pos_iff.mpr hv0
        nlinarith [sq_nonneg ‖v‖]
      have hRpos : 0 < Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v) :=
        Real.sqrt_pos.mpr hQv_pos
      have h1 : ENNReal.ofReal (s t * Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v))
          = ENNReal.ofReal (t * Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
        rw [← hrun t ht, harc t ht]
      have h2 : s t * Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v)
          = t * Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v) :=
        (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (hpt t ht).1.1 hRpos.le)
          (mul_nonneg ht.1 hRpos.le)).mp h1
      have h3 : s t = t := mul_right_cancel₀ hRpos.ne' h2
      rw [(hpt t ht).2, h3]
  refine ⟨hptv, ?_⟩
  intro t ht
  have hray_geo := (hgeo v (hv.trans_le hρρg)).2.2.2
  refine hasGeodesicEquationAt_congr_of_eventuallyEq ?_
    (hray_geo t ⟨by linarith [ht.1, hbg], by linarith [ht.2, hbg]⟩)
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with τ hτ
  exact hptv τ hτ

/-- **Math.** **Confinement: a short curve from `p` stays in the Gauss ball**
(do Carmo Ch. 3, Prop. 3.6, escape-case reduction). For every target radius
`ρ' > 0` there is a length threshold `δ > 0` such that every `C¹` curve
`σ : [0,1] → M` starting at `p` with `pathELength σ < δ` stays in
`exp_p(B_{ρ'}(0))` at every time. Truncating at time `t` and reparametrizing
to `[0,1]` (`pathELength_comp_of_monotoneOn`), a curve whose point at time `t`
escaped the `δ`-sublevel image would have cost at least `δ` by the escape
estimate of `exists_le_pathELength`; the Gram bound converts the sublevel set
into a norm ball of radius `√c · δ < ρ'`. -/
theorem exists_forall_mem_expMap_ball_of_pathELength_lt [T2Space M]
    (g : RiemannianMetric I M) (p : M) {ρ' : ℝ} (hρ' : 0 < ρ') :
    ∃ δ : ℝ, 0 < δ ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ σ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = p →
        Manifold.pathELength I σ 0 1 < ENNReal.ofReal δ →
        ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈
          (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) ρ') := by
  classical
  obtain ⟨ε, c, hε, hc, hdom, hsrc, hinj, hopen, hmain⟩ :=
    exists_le_pathELength (I := I) g p
  obtain ⟨hlow, hesc_r, hesc_δ, hgram⟩ := hmain
  set ρ'' : ℝ := min ρ' ε with hρ''def
  have hρ'' : 0 < ρ'' := lt_min hρ' hε
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  set δ : ℝ := ρ'' / (Real.sqrt c + 1) with hδdef
  have hδ : 0 < δ := div_pos hρ'' (by linarith)
  have hscδ : Real.sqrt c * δ < ρ'' := by
    have h2 : (Real.sqrt c + 1) * δ = ρ'' := by
      rw [hδdef]
      field_simp
    nlinarith [hδ, h2]
  have hscδε : Real.sqrt c * δ < ε := hscδ.trans_le (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  intro σ hσ hσ0 hlen t ht
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  -- the truncation of `σ` at time `t`, reparametrized to `[0,1]`
  set f : ℝ → ℝ := fun τ => t * τ with hfdef
  have hf0 : f 0 = 0 := mul_zero t
  have hf1 : f 1 = t := mul_one t
  have hfmaps : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro τ hτ
    exact ⟨mul_nonneg ht.1 hτ.1,
      le_trans (mul_le_mul ht.2 hτ.2 hτ.1 zero_le_one) (by norm_num)⟩
  have hfsmooth : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) 1 f (Icc (0 : ℝ) 1) :=
    contMDiffOn_iff_contDiffOn.mpr ((contDiff_const.mul contDiff_id).contDiffOn)
  have hστ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 (σ ∘ f) (Icc (0 : ℝ) 1) :=
    hσ.comp hfsmooth hfmaps
  have hσf0 : (σ ∘ f) 0 = p := by
    show σ (f 0) = p
    rw [hf0, hσ0]
  have hfmono : MonotoneOn f (Icc (0 : ℝ) 1) := by
    intro a _ b _ hab
    exact mul_le_mul_of_nonneg_left hab ht.1
  have hfdiff : DifferentiableOn ℝ f (Icc (0 : ℝ) 1) :=
    (differentiable_id.const_mul t).differentiableOn
  have hσmdiff : MDifferentiableOn 𝓘(ℝ, ℝ) I σ (Icc (f 0) (f 1)) := by
    rw [hf0, hf1]
    exact (hσ.mdifferentiableOn one_ne_zero).mono (Icc_subset_Icc le_rfl ht.2)
  have hreparam : Manifold.pathELength I (σ ∘ f) 0 1
      = Manifold.pathELength I σ 0 t := by
    have h := Manifold.pathELength_comp_of_monotoneOn (I := I) (γ := σ)
      zero_le_one hfmono hfdiff hσmdiff
    rw [hf0, hf1] at h
    exact h
  -- the truncation is short, so its endpoint cannot escape the sublevel image
  have hshort : Manifold.pathELength I (σ ∘ f) 0 1 < ENNReal.ofReal δ := by
    rw [hreparam]
    exact lt_of_le_of_lt (Manifold.pathELength_mono le_rfl ht.2) hlen
  have hin : (σ ∘ f) 1 ∈
      (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        {z : E | z ∈ ball (0 : E) ε ∧
          Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z z) < δ} := by
    by_contra hout
    obtain ⟨T, hT, -, hcost⟩ := hesc_δ δ hδ hscδε (σ ∘ f) hστ hσf0 hout
    have h1 : ENNReal.ofReal δ ≤ Manifold.pathELength I (σ ∘ f) 0 1 :=
      le_trans le_self_add hcost
    exact absurd h1 (not_le.mpr hshort)
  -- the sublevel set sits inside the norm ball of radius `√c · δ < ρ'`
  obtain ⟨z, ⟨hzball, hzQ⟩, hze⟩ := hin
  have hQz_nonneg : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z z :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) z
  have hQz : chartMetricInner (I := I) g p (extChartAt I p p) z z < δ ^ 2 := by
    nlinarith [Real.sq_sqrt hQz_nonneg, Real.sqrt_nonneg
      (chartMetricInner (I := I) g p (extChartAt I p p) z z)]
  have hznorm : ‖z‖ < ρ' := by
    have h1 := hgram z
    have h2 : ‖z‖ ^ 2 < (Real.sqrt c * δ) ^ 2 := by
      have h3 : (Real.sqrt c * δ) ^ 2 = c * δ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hc.le]
      nlinarith
    have h4 : ‖z‖ < Real.sqrt c * δ := by
      nlinarith [norm_nonneg z, mul_pos hsc hδ]
    exact h4.trans (hscδ.trans_le (min_le_left _ _))
  have hσt : σ t = (σ ∘ f) 1 := by
    show σ t = σ (f 1)
    rw [hf1]
  rw [hσt, ← hze]
  exact ⟨z, mem_ball_zero_iff.mpr hznorm, rfl⟩

/-- **Math.** **The equality case of the minimizing property, in the manifold,
without the confinement hypothesis** (do Carmo Ch. 3, Prop. 3.6, equality
clause, `C¹` case, with the escape case handled). There is `ρ > 0` such that
every `C¹` competitor `σ : [0,1] → M` from `p` to `exp_p v` (`‖v‖ < ρ`) that
realizes the radial length `√⟨v,v⟩_p` — with no assumption on where it
travels — is a monotone reparametrization of the radial geodesic, with the
running-length identity and do Carmo's image equality. A curve that left the
Gauss ball would already be longer than the radial geodesic
(`exists_forall_mem_expMap_ball_of_pathELength_lt`), so the equality
competitor is confined and `exists_gauss_equality_manifold_ball` applies. -/
theorem exists_gauss_equality_manifold [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ v : E, ‖v‖ < ρ → ∀ σ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        Manifold.pathELength I σ 0 1
          = ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v)) →
        ∃ s : ℝ → ℝ,
          ContinuousOn s (Icc 0 1) ∧ MonotoneOn s (Icc 0 1) ∧
          s 0 = 0 ∧ s 1 = 1 ∧
          (∀ t ∈ Icc (0 : ℝ) 1, s t ∈ Icc (0 : ℝ) 1 ∧
            σ t = expMap (I := I) g p ((s t • v : E) : TangentSpace I p)) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
            = ENNReal.ofReal (s t * Real.sqrt
                (chartMetricInner (I := I) g p (extChartAt I p p) v v))) ∧
          σ '' Icc 0 1
            = (fun τ : ℝ => expMap (I := I) g p ((τ • v : E) : TangentSpace I p)) ''
                Icc 0 1) := by
  classical
  obtain ⟨ρ₀, hρ₀, hdom₀, hsrc₀, hinj₀, hkey⟩ :=
    exists_gauss_equality_manifold_ball (I := I) g p
  obtain ⟨δ, hδ, hconf⟩ :=
    exists_forall_mem_expMap_ball_of_pathELength_lt (I := I) g p hρ₀
  obtain ⟨εQ, hεQ, hQlt⟩ :=
    exists_forall_chartMetricInner_self_lt (I := I) g p
      (θ := δ ^ 2) (by positivity)
  set ρ : ℝ := min ρ₀ εQ with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hεQ
  have hρρ₀ : ρ ≤ ρ₀ := min_le_left _ _
  have hρεQ : ρ ≤ εQ := min_le_right _ _
  refine ⟨ρ, hρ, fun w hw => hdom₀ w (hw.trans_le hρρ₀),
    fun w hw => hsrc₀ w (hw.trans_le hρρ₀),
    hinj₀.mono (ball_subset_ball hρρ₀), ?_⟩
  intro v hv σ hσ hσ0 hσ1 hlen
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have hQv_nonneg : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) v
  have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v < δ ^ 2 :=
    hQlt v (hv.trans_le hρεQ)
  have hlt : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)
      < δ := by
    nlinarith [Real.sq_sqrt hQv_nonneg, Real.sqrt_nonneg
      (chartMetricInner (I := I) g p (extChartAt I p p) v v), hδ]
  have htrace := hconf σ hσ hσ0 (by
    rw [hlen]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hlt)
  exact hkey v (hv.trans_le hρρ₀) σ hσ hσ0 hσ1 htrace hlen

/-- **Math.** **An arclength-proportional minimizer from `p` is the radial
geodesic, without the confinement hypothesis** (do Carmo Ch. 3, Prop. 3.6
equality clause + Cor. 3.9, normal-ball core, `C¹` case, escape handled).
There is `ρ > 0` such that every `C¹` curve `σ : [0,1] → M` from `p` to
`exp_p v` (`‖v‖ < ρ`) with `pathELength σ 0 t = t · √⟨v,v⟩_p` for all
`t ∈ [0,1]` satisfies `σ(t) = exp_p(t v)` on `[0,1]` and the intrinsic
geodesic equation on `(0,1)`. -/
theorem exists_gauss_equality_geodesic [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ρ) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       ∀ v : E, ‖v‖ < ρ → ∀ σ : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
        σ 0 = p →
        σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
        (∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I σ 0 t
          = ENNReal.ofReal (t * Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v))) →
        (∀ t ∈ Icc (0 : ℝ) 1,
          σ t = expMap (I := I) g p ((t • v : E) : TangentSpace I p)) ∧
        IsGeodesicOn (I := I) g σ (Ioo 0 1)) := by
  classical
  obtain ⟨ρ₁, hρ₁, hdom₁, hsrc₁, hinj₁, hkey⟩ :=
    exists_gauss_equality_geodesic_ball (I := I) g p
  obtain ⟨δ, hδ, hconf⟩ :=
    exists_forall_mem_expMap_ball_of_pathELength_lt (I := I) g p hρ₁
  obtain ⟨εQ, hεQ, hQlt⟩ :=
    exists_forall_chartMetricInner_self_lt (I := I) g p
      (θ := δ ^ 2) (by positivity)
  set ρ : ℝ := min ρ₁ εQ with hρdef
  have hρ : 0 < ρ := lt_min hρ₁ hεQ
  have hρρ₁ : ρ ≤ ρ₁ := min_le_left _ _
  have hρεQ : ρ ≤ εQ := min_le_right _ _
  refine ⟨ρ, hρ, fun w hw => hdom₁ w (hw.trans_le hρρ₁),
    fun w hw => hsrc₁ w (hw.trans_le hρρ₁),
    hinj₁.mono (ball_subset_ball hρρ₁), ?_⟩
  intro v hv σ hσ hσ0 hσ1 harc
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  have hQv_nonneg : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v :=
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) v
  have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v < δ ^ 2 :=
    hQlt v (hv.trans_le hρεQ)
  have hlt : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)
      < δ := by
    nlinarith [Real.sq_sqrt hQv_nonneg, Real.sqrt_nonneg
      (chartMetricInner (I := I) g p (extChartAt I p p) v v), hδ]
  have hlen : Manifold.pathELength I σ 0 1
      = ENNReal.ofReal (Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
    have h := harc 1 (right_mem_Icc.mpr zero_le_one)
    rwa [one_mul] at h
  have htrace := hconf σ hσ hσ0 (by
    rw [hlen]
    exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hlt)
  exact hkey v (hv.trans_le hρρ₁) σ hσ hσ0 hσ1 htrace harc

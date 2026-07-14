import OpenGALib.Riemannian.Exponential.Minimizing
import OpenGALib.Riemannian.Exponential.LocalDiffeo
import OpenGALib.Riemannian.Geodesic.HopfRinow.CurveReadback
import OpenGALib.Riemannian.Geodesic.HopfRinow.GramBound
import OpenGALib.Riemannian.Metric.RiemannianDistance

/-!
# The metric normal ball (do Carmo Ch. 3, Prop. 3.6, metric form; Ch. 7 §2)

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 3.6 states that radial
geodesics locally minimize arc length; Ch. 7 §2 consumes it through the metric
identity `d(p, exp_p v) = |v|_p` on a normal ball, together with the *escape
estimate*: any competitor leaving the normal ball is longer than a definite
threshold. This file derives both from the chart-polar Gauss-lemma stack
(`Minimizing.lean`) and the length bridge (`CurveReadback.lean`):

* `exists_isOpen_expMap_image` — `exp_p` maps open subsets of a small ball
  onto open subsets of `M` (and their chart readings onto open subsets of `E`).
* `exists_forall_chartMetricInner_self_lt` — smallness transfer: coordinate-
  small vectors are `g_p`-small.
* `exists_pathELength_expMap_ray` — the radial curve `t ↦ exp_p(t v)` is `C¹`
  with `ℓ(exp_p(t v), t ∈ [0,1]) = √⟨v, v⟩_p` (do Carmo's `ℓ(γ) = |v|`).
* `exists_le_pathELength` — **the competitor bound** (do Carmo Ch. 3,
  Prop. 3.6 + the escape case, metric-ready form): every `C¹` curve from `p`
  to `exp_p v` has length at least `√⟨v, v⟩_p`, and every `C¹` curve from `p`
  ending outside `exp_p(B_r(0))` has length at least `r/√c` (`c` the Gram
  comparison constant at `p`).
* `exists_edist_expMap_ball` — **the metric normal ball** (the form consumed
  by Hopf–Rinow, do Carmo Ch. 7, Theorem 2.8): under the standing hypothesis
  `g.IsRiemannianDist`, there are `ε, δ > 0` with
  `edist p (exp_p v) = √⟨v, v⟩_p` for `‖v‖ < ε`, and
  `edist p q ≥ δ` for every `q ∉ exp_p(B_ε(0))`.

Competitors are single `C¹` paths (mathlib's `riemannianEDist` takes the
infimum over `C¹` paths), so the single-piece comparison
`exists_gauss_radius_comparison_ball` suffices; do Carmo's piecewise
competitors are handled by `MinimizingPiecewise.lean` for the blueprint-faithful
statement of Prop. 3.6 itself.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

set_option linter.unusedSectionVars false

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** `exp_p` is an **open map on small balls** (do Carmo Ch. 3,
Prop. 2.9, openness clause, localized): there is `ρ > 0` such that for every
open `V ⊆ B_ρ(0) ⊂ T_pM`, both the chart reading `φ_p(exp_p(V))` and the image
`exp_p(V)` are open. The derivative of the chart reading is an invertible
strict derivative at every point of the ball. -/
theorem exists_isOpen_expMap_image (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ w : E, ‖w‖ < ρ → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ρ →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ∀ V ⊆ ball (0 : E) ρ, IsOpen V →
        IsOpen ((fun w : E =>
            extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) '' V) ∧
        IsOpen ((fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' V) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρe, hρe, hdome, hsrce, hequiv⟩ :=
    exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  refine ⟨min ε₁ ρe, lt_min hε₁ hρe,
    fun w hw => hdom₁ w (hw.trans_le (min_le_left _ _)),
    fun w hw => hsrc₁ w (hw.trans_le (min_le_left _ _)), ?_⟩
  intro V hV hVopen
  have hVε₁ : V ⊆ ball (0 : E) ε₁ :=
    hV.trans (ball_subset_ball (min_le_left _ _))
  have hVρe : V ⊆ ball (0 : E) ρe :=
    hV.trans (ball_subset_ball (min_le_right _ _))
  -- the chart image is open: invertible strict derivative at every point of `V`
  have hopen_f : IsOpen (f '' V) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨w, hw, rfl⟩
    obtain ⟨D', hD'⟩ := hequiv w (mem_ball_zero_iff.mp (hVρe hw))
    rw [← hD'.map_nhds_eq_of_equiv]
    exact image_mem_map (hVopen.mem_nhds hw)
  refine ⟨hopen_f, ?_⟩
  -- the image of `exp_p` is the chart pull-back of the image of `f`
  have himg : (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' V
      = (extChartAt I p).source ∩ extChartAt I p ⁻¹' (f '' V) := by
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hsrcw : expMap (I := I) g p (w : TangentSpace I p) ∈
          (chartAt H p).source :=
        hsrc₁ w (mem_ball_zero_iff.mp (hVε₁ hw))
      exact ⟨by rw [extChartAt_source]; exact hsrcw, ⟨w, hw, rfl⟩⟩
    · rintro ⟨hxsrc, ⟨w, hw, hfw⟩⟩
      refine ⟨w, hw, ?_⟩
      have hsrcw : expMap (I := I) g p (w : TangentSpace I p) ∈
          (extChartAt I p).source := by
        rw [extChartAt_source]
        exact hsrc₁ w (mem_ball_zero_iff.mp (hVε₁ hw))
      exact (extChartAt I p).injOn hsrcw hxsrc hfw
  rw [himg]
  exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage
    (isOpen_extChartAt_source p) hopen_f

/-- **Math.** Smallness transfer at the base point: for any threshold `θ > 0`,
coordinate vectors of small enough norm have `g_p`-squared-length below `θ`.
The Gram quadratic form at the chart image of `p` is continuous and vanishes
at `0`. -/
theorem exists_forall_chartMetricInner_self_lt (g : RiemannianMetric I M) (p : M)
    {θ : ℝ} (hθ : 0 < θ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ w : E, ‖w‖ < ε →
      chartMetricInner (I := I) g p (extChartAt I p p) w w < θ := by
  classical
  have hcont : Continuous fun w : E =>
      chartMetricInner (I := I) g p (extChartAt I p p) w w := by
    simp only [chartMetricInner_def]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    have hci : Continuous fun w : E => Geodesic.chartCoord (E := E) i w := by
      simpa only [Geodesic.chartCoordFunctional_apply] using
        (Geodesic.chartCoordFunctional (E := E) i).continuous
    have hcj : Continuous fun w : E => Geodesic.chartCoord (E := E) j w := by
      simpa only [Geodesic.chartCoordFunctional_apply] using
        (Geodesic.chartCoordFunctional (E := E) j).continuous
    exact (continuous_const.mul hci).mul hcj
  have h0 : chartMetricInner (I := I) g p (extChartAt I p p) 0 0 = 0 :=
    chartMetricInner_zero_left (I := I) g p _ _
  have hev : ∀ᶠ w in 𝓝 (0 : E),
      chartMetricInner (I := I) g p (extChartAt I p p) w w < θ := by
    have := hcont.continuousAt (x := (0 : E))
    exact this.eventually_lt_const (by simpa [h0] using hθ)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  exact ⟨ε, hε, fun w hw => hball w (by rwa [mem_ball_zero_iff])⟩

/-- **Math.** **The radial curve is `C¹` with chart-read length `√⟨v, v⟩_p`**
(do Carmo Ch. 3, the identity `ℓ(γ) = |v|` for the radial geodesic
`γ(t) = exp_p(tv)`, expressed through mathlib's `pathELength` under the
Riemannian-bundle instance of `g`). -/
theorem exists_pathELength_expMap_ray (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ε →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      ∀ v : E, ‖v‖ < ε →
        ContMDiffOn 𝓘(ℝ, ℝ) I 1
          (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p))
          (Icc 0 1) ∧
        (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨g.toRiemannianMetric⟩
         Manifold.pathELength I
            (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 0 1
          = ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v))) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρs, hρs, hdoms, hsrcs, hray⟩ := exists_expMap_ray_speed_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  set ε : ℝ := min ε₁ ρs with hεdef
  have hε : 0 < ε := lt_min hε₁ hρs
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hερs : ε ≤ ρs := min_le_right _ _
  refine ⟨ε, hε, fun w hw => hdom₁ w (hw.trans_le hεε₁),
    fun w hw => hsrc₁ w (hw.trans_le hεε₁), ?_⟩
  intro v hv
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- norms of the points on the segment
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, ‖t • v‖ < ε := by
    intro t ht
    calc ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1 * ‖v‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg v)
          rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
      _ < ε := by rw [one_mul]; exact hv
  -- the radial curve is `C¹`: `(extChartAt p).symm ∘ f ∘ (t ↦ t • v)`
  have hradC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) (Icc 0 1) := by
    have hsm : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 (fun t : ℝ => t • v) (Icc 0 1) :=
      contMDiffOn_iff_contDiffOn.mpr ((contDiff_id.smul contDiff_const).contDiffOn)
    have hfM : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f (ball (0 : E) ε₁) :=
      contMDiffOn_iff_contDiffOn.mpr hfC1
    have hsymm : ContMDiffOn 𝓘(ℝ, E) I 1 (extChartAt I p).symm (extChartAt I p).target :=
      contMDiffOn_extChartAt_symm p
    have h1 : MapsTo (fun t : ℝ => t • v) (Icc 0 1) (ball (0 : E) ε₁) := fun t ht =>
      mem_ball_zero_iff.mpr ((hseg t ht).trans_le hεε₁)
    have h2 : MapsTo (f ∘ fun t : ℝ => t • v) (Icc 0 1) (extChartAt I p).target := by
      intro t ht
      exact (extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hsrc₁ (t • v) ((hseg t ht).trans_le hεε₁))
    refine ((hsymm.comp (hfM.comp hsm h1) h2).congr ?_)
    intro t ht
    show expMap (I := I) g p ((t • v : E) : TangentSpace I p)
      = (extChartAt I p).symm (f (t • v))
    rw [hfdef]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc₁ (t • v) ((hseg t ht).trans_le hεε₁))).symm
  refine ⟨hradC1, ?_⟩
  -- length via the chart bridge
  have hsrcrad : ∀ t ∈ Icc (0 : ℝ) 1,
      expMap (I := I) g p ((t • v : E) : TangentSpace I p) ∈ (chartAt H p).source :=
    fun t ht => hsrc₁ (t • v) ((hseg t ht).trans_le hεε₁)
  rw [Geodesic.pathELength_eq_ofReal_integral_chartMetricInner (I := I) g zero_le_one
    hradC1 hsrcrad]
  congr 1
  -- the chart-read speed is constantly `√⟨v, v⟩_p` on the interior
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1,
      derivWithin (fun s : ℝ =>
        extChartAt I p (expMap (I := I) g p ((s • v : E) : TangentSpace I p)))
        (Icc 0 1) t = fderiv ℝ f (t • v) v := by
    intro t ht
    have hf_at : HasFDerivAt f (fderiv ℝ f (t • v)) (t • v) :=
      ((hfC1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
        ((hseg t (Ioo_subset_Icc_self ht)).trans_le hεε₁)))).differentiableAt
          one_ne_zero).hasFDerivAt
    have hsmul : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    have hcomb : HasDerivAt (fun s : ℝ => f (s • v)) (fderiv ℝ f (t • v) v) t := by
      simpa [Function.comp_def] using hf_at.comp_hasDerivAt t hsmul
    exact hcomb.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc zero_lt_one t (Ioo_subset_Icc_self ht))
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun _ =>
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v))
      (fun t ht => by
        rw [hderiv t ht]
        rw [hray v (hv.trans_le hερs) t (Ioo_subset_Icc_self ht)]),
    setIntegral_const]
  simp [Real.volume_real_Ioo]

/-- **Math.** **The competitor bound** (do Carmo Ch. 3, Prop. 3.6 together with
its escape case, single-`C¹`-piece form). There are `ε > 0` and a Gram
comparison constant `c > 0` at `p` such that, with `exp_p` injective on
`B_ε(0) ⊂ T_pM` and open on sub-balls:

* every `C¹` curve `σ : [0,1] → M` from `p` to `exp_p v` (`‖v‖ < ε`) has
  `pathELength` at least the `g_p`-length `√⟨v, v⟩_p` of the radial geodesic
  (the competitor either stays in the normal ball — the Gauss radius
  comparison applies to its polar lift — or leaves it, which already costs
  more than `√⟨v, v⟩_p`);
* every `C¹` curve from `p` ending outside `exp_p(B_r(0))` (`0 < r ≤ ε`) has
  `pathELength` at least `r/√c` (the escape estimate).

Competitors are single `C¹` paths, matching mathlib's `riemannianEDist`. -/
theorem exists_le_pathELength [T2Space M] (g : RiemannianMetric I M) (p : M) :
    ∃ (ε c : ℝ), 0 < ε ∧ 0 < c ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ε →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ε) ∧
      (∀ r : ℝ, r ≤ ε →
        IsOpen ((fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
          ball (0 : E) r)) ∧
      (letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨g.toRiemannianMetric⟩
       (∀ v : E, ‖v‖ < ε → ∀ σ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
          σ 0 = p → σ 1 = expMap (I := I) g p (v : TangentSpace I p) →
          ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v))
            ≤ Manifold.pathELength I σ 0 1) ∧
       (∀ r : ℝ, 0 < r → r ≤ ε → ∀ σ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) →
          σ 0 = p →
          σ 1 ∉ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            ball (0 : E) r →
          ENNReal.ofReal (r / Real.sqrt c) ≤ Manifold.pathELength I σ 0 1) ∧
       (∀ δ : ℝ, 0 < δ → Real.sqrt c * δ < ε →
          ∀ σ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = p →
          σ 1 ∉ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
            {v : E | v ∈ ball (0 : E) ε ∧
              Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) < δ} →
          ∃ T ∈ Icc (0 : ℝ) 1, (∃ z : E, ‖z‖ < ε ∧
              Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z z) = δ ∧
              σ T = expMap (I := I) g p (z : TangentSpace I p)) ∧
            ENNReal.ofReal δ + Manifold.pathELength I σ T 1
              ≤ Manifold.pathELength I σ 0 1) ∧
       (∀ w : E,
          ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) w w)) := by
  classical
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨ρc, hρc, hdomc, hsrcc, hcomp⟩ :=
    exists_gauss_radius_comparison_ball (I := I) g p
  obtain ⟨ρo, hρo, hdomo, hsrco, hopen⟩ := exists_isOpen_expMap_image (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  have hgram0 : ∀ w : E,
      ‖w‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) w w :=
    fun w => hgramV _ (mem_of_mem_nhds hVc) w
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  -- radii: `ρ` fits inside every input radius; `r'` is the escape radius,
  -- `ρ''` an intermediate open ball on which the inverse chart data is `C¹`
  set ρ : ℝ := min (min ε₁ ρc) ρo with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hε₁ hρc) hρo
  have hρε₁ : ρ ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρρc : ρ ≤ ρc := (min_le_left _ _).trans (min_le_right _ _)
  have hρρo : ρ ≤ ρo := min_le_right _ _
  set r' : ℝ := ρ / 2 with hr'def
  set ρ'' : ℝ := 3 * ρ / 4 with hρ''def
  have hr' : 0 < r' := by positivity
  have hr'ρ'' : r' < ρ'' := by rw [hr'def, hρ''def]; linarith
  have hρ''ρ : ρ'' < ρ := by rw [hρ''def]; linarith
  have hr'ε₁ : r' < ε₁ := lt_of_lt_of_le (hr'ρ''.trans hρ''ρ) hρε₁
  have hr'ρc : r' < ρc := lt_of_lt_of_le (hr'ρ''.trans hρ''ρ) hρρc
  -- the escape neighborhood `U` and the ambient `C¹`-inverse region
  set U : Set M :=
    (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' ball (0 : E) r'
    with hUdef
  have hUopen : IsOpen U :=
    (hopen (ball (0 : E) r') (ball_subset_ball
      (le_of_lt ((hr'ρ''.trans hρ''ρ).trans_le hρρo))) isOpen_ball).2
  have hfopen : IsOpen (f '' ball (0 : E) ρ'') :=
    (hopen (ball (0 : E) ρ'') (ball_subset_ball (hρ''ρ.le.trans hρρo)) isOpen_ball).1
  have hfinvC1'' : ContDiffOn ℝ 1 finv (f '' ball (0 : E) ρ'') :=
    hfinvC1.mono (image_mono (ball_subset_ball (hρ''ρ.le.trans hρε₁)))
  have hfinv_fderiv_cont : ContinuousOn (fderiv ℝ finv) (f '' ball (0 : E) ρ'') :=
    hfinvC1''.continuousOn_fderiv_of_isOpen hfopen le_rfl
  have hpU : p ∈ U :=
    ⟨0, mem_ball_zero_iff.mpr (by simpa using hr'), expMap_zero (I := I) g p⟩
  -- membership in `U` gives the polar description through `finv`
  have hpolar : ∀ x ∈ U, ∃ z : E, ‖z‖ < r' ∧
      x = expMap (I := I) g p (z : TangentSpace I p) := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨z, mem_ball_zero_iff.mp hz, rfl⟩
  -- ## The core comparison: a curve staying in the closed `r'`-region on `[0, τ]`
  -- is at least as long as the `g_p`-radius of its polar endpoint
  have hcore : ∀ (σ : ℝ → M) (τ : ℝ), 0 < τ → τ ≤ 1 →
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = p →
      (∀ t ∈ Icc (0 : ℝ) τ, ∃ z : E, ‖z‖ ≤ r' ∧
        σ t = expMap (I := I) g p (z : TangentSpace I p)) →
      ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (finv (extChartAt I p (σ τ))) (finv (extChartAt I p (σ τ)))))
        ≤ Manifold.pathELength I σ 0 τ := by
    intro σ τ hτ0 hτ1 hσ hσ0 hstay
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hτ1
    have hsrcσ : ∀ t ∈ Icc (0 : ℝ) τ, σ t ∈ (chartAt H p).source := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      rw [hσt]
      exact hsrc₁ z (hz.trans_lt hr'ε₁)
    set u : ℝ → E := fun s => extChartAt I p (σ s) with hudef
    set u' : ℝ → E := derivWithin u (Icc 0 τ) with hu'def
    have huC1 : ContDiffOn ℝ 1 u (Icc 0 τ) :=
      Geodesic.contDiffOn_extChartAt_comp (hσ.mono hsub) hsrcσ
    have hu'cont : ContinuousOn u' (Icc 0 τ) :=
      huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hτ0) le_rfl
    have hu'deriv : ∀ t ∈ Ioo (0 : ℝ) τ, HasDerivAt u (u' t) t := by
      intro t ht
      exact ((huC1.differentiableOn one_ne_zero t
        (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    -- the polar lift
    set w : ℝ → E := fun s => finv (u s) with hwdef
    have hwz : ∀ t ∈ Icc (0 : ℝ) τ, ‖w t‖ ≤ r' ∧ f (w t) = u t := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      have hut : u t = f z := by rw [hudef]; simp only; rw [hσt]
      have hwt : w t = z := by
        rw [hwdef]; simp only; rw [hut]
        exact hlinv z (hz.trans_lt hr'ε₁)
      rw [hwt]
      exact ⟨hz, by rw [← hut]⟩
    have humem : ∀ t ∈ Icc (0 : ℝ) τ, u t ∈ f '' ball (0 : E) ρ'' := by
      intro t ht
      exact ⟨w t, mem_ball_zero_iff.mpr ((hwz t ht).1.trans_lt hr'ρ''), (hwz t ht).2⟩
    have hw_cont : ContinuousOn w (Icc 0 τ) :=
      (hfinvC1''.continuousOn).comp huC1.continuousOn humem
    have hw_deriv : ∀ t ∈ Ioo (0 : ℝ) τ,
        HasDerivAt w (fderiv ℝ finv (u t) (u' t)) t := by
      intro t ht
      have hfinv_at : HasFDerivAt finv (fderiv ℝ finv (u t)) (u t) :=
        ((hfinvC1''.contDiffAt (hfopen.mem_nhds
          (humem t (Ioo_subset_Icc_self ht)))).differentiableAt
            one_ne_zero).hasFDerivAt
      simpa [Function.comp_def] using hfinv_at.comp_hasDerivAt t (hu'deriv t ht)
    have hw'_cont : ContinuousOn (fun t => fderiv ℝ finv (u t) (u' t)) (Icc 0 τ) :=
      (hfinv_fderiv_cont.comp huC1.continuousOn humem).clm_apply hu'cont
    have hwball : ∀ t ∈ Icc (0 : ℝ) τ, ‖w t‖ < ρc :=
      fun t ht => ((hwz t ht).1).trans_lt hr'ρc
    -- the Gauss radius comparison applied to the polar lift
    have hcompare := hcomp w (fun t => fderiv ℝ finv (u t) (u' t)) 0 τ hτ0.le
      hw_cont hw_deriv hw'_cont hwball
    -- the base point of the lift is the origin
    have hw0 : w 0 = 0 := by
      have hu0 : u 0 = f 0 := by
        rw [hudef, hfdef]; simp only; rw [hσ0]
        exact congrArg (extChartAt I p) (expMap_zero (I := I) g p).symm
      rw [hwdef]; simp only; rw [hu0]
      exact hlinv 0 (by simpa using hε₁)
    rw [hw0, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero] at hcompare
    -- identify the comparison integrand with the chart-read speed of `σ`
    have hcongr : (∫ t in (0 : ℝ)..τ, Real.sqrt (chartMetricInner (I := I) g p
          (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
          (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t)
            (fderiv ℝ finv (u t) (u' t)))
          (fderiv ℝ (fun z : E =>
            extChartAt I p (expMap (I := I) g p (z : TangentSpace I p))) (w t)
            (fderiv ℝ finv (u t) (u' t)))))
        = ∫ t in (0 : ℝ)..τ, Real.sqrt (chartMetricInner (I := I) g p
            (u t) (u' t) (u' t)) := by
      rw [intervalIntegral.integral_of_le hτ0.le,
        intervalIntegral.integral_of_le hτ0.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
      have htIcc : t ∈ Icc (0 : ℝ) τ := Ioo_subset_Icc_self ht
      -- chain rule: `f ∘ w = u` near `t`, so `Df(w t)(w' t) = u'(t)`
      have hf_at : HasFDerivAt f (fderiv ℝ f (w t)) (w t) :=
        ((hfC1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
          (((hwz t htIcc).1).trans_lt hr'ε₁)))).differentiableAt
            one_ne_zero).hasFDerivAt
      have hfw : HasDerivAt (fun s => f (w s))
          (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))) t := by
        simpa [Function.comp_def] using hf_at.comp_hasDerivAt t (hw_deriv t ht)
      have hfw_u : HasDerivAt u
          (fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t))) t := by
        refine hfw.congr_of_eventuallyEq ?_
        filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
        exact ((hwz s hs).2).symm
      have hfd : fderiv ℝ f (w t) (fderiv ℝ finv (u t) (u' t)) = u' t :=
        hfw_u.unique (hu'deriv t ht)
      have hbase : extChartAt I p
          (expMap (I := I) g p (w t : TangentSpace I p)) = u t := (hwz t htIcc).2
      rw [hbase, hfd]
    rw [hcongr] at hcompare
    -- convert to `pathELength` and extend the interval
    have hlen : Manifold.pathELength I σ 0 τ
        = ENNReal.ofReal (∫ t in (0 : ℝ)..τ, Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' t) (u' t))) :=
      Geodesic.pathELength_eq_ofReal_integral_chartMetricInner (I := I) g hτ0.le
        (hσ.mono hsub) hsrcσ
    calc ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
          (finv (extChartAt I p (σ τ))) (finv (extChartAt I p (σ τ)))))
        ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..τ, Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' t) (u' t))) :=
          ENNReal.ofReal_le_ofReal hcompare
      _ = Manifold.pathELength I σ 0 τ := hlen.symm
  -- `exp_p` is continuous on the closed `r'`-ball (through the chart and `f`)
  have hexp_cont : ContinuousOn
      (fun z : E => expMap (I := I) g p (z : TangentSpace I p))
      (closedBall (0 : E) r') := by
    have h1 : ContinuousOn f (closedBall (0 : E) r') :=
      hfC1.continuousOn.mono (closedBall_subset_ball hr'ε₁)
    have h2 : ContinuousOn (extChartAt I p).symm (extChartAt I p).target :=
      continuousOn_extChartAt_symm p
    have hmap : MapsTo f (closedBall (0 : E) r') (extChartAt I p).target := by
      intro z hz
      exact (extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hsrc₁ z ((mem_closedBall_zero_iff.mp hz).trans_lt hr'ε₁))
    refine (h2.comp h1 hmap).congr ?_
    intro z hz
    show expMap (I := I) g p (z : TangentSpace I p) = (extChartAt I p).symm (f z)
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrc₁ z ((mem_closedBall_zero_iff.mp hz).trans_lt hr'ε₁))).symm
  -- ## First exit: a curve leaving `U` stays in the closed region up to a first
  -- exit time, where it sits exactly on the coordinate `r'`-sphere
  have hfirstexit : ∀ σ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = p →
      (∃ t ∈ Icc (0 : ℝ) 1, σ t ∉ U) →
      ∃ T ∈ Ioc (0 : ℝ) 1, (∃ z₀ : E, ‖z₀‖ = r' ∧
          σ T = expMap (I := I) g p (z₀ : TangentSpace I p)) ∧
        ∀ t ∈ Icc (0 : ℝ) T, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = expMap (I := I) g p (z : TangentSpace I p) := by
    rintro σ hσ hσ0 ⟨t₀, ht₀, ht₀U⟩
    set A : Set ℝ := Icc (0 : ℝ) 1 ∩ σ ⁻¹' Uᶜ with hAdef
    have hA_closed : IsClosed A :=
      hσ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
        hUopen.isClosed_compl
    have hA_ne : A.Nonempty := ⟨t₀, ht₀, ht₀U⟩
    have hA_bdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    set T : ℝ := sInf A with hTdef
    have hTA : T ∈ A := hA_closed.csInf_mem hA_ne hA_bdd
    have hT01 : T ∈ Icc (0 : ℝ) 1 := hTA.1
    have hT_pos : 0 < T := by
      rcases eq_or_lt_of_le hT01.1 with h | h
      · exact absurd (h ▸ (hσ0 ▸ hpU) : σ T ∈ U) hTA.2
      · exact h
    have hbefore : ∀ t, 0 ≤ t → t < T → σ t ∈ U := by
      intro t ht0 htT
      by_contra hnot
      exact absurd (csInf_le hA_bdd ⟨⟨ht0, htT.le.trans hT01.2⟩, hnot⟩)
        (not_le.mpr htT)
    -- the exit point lies on the closed `r'`-sphere via compactness
    set K : Set M :=
      (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) ''
        closedBall (0 : E) r' with hKdef
    have hKclosed : IsClosed K :=
      ((isCompact_closedBall (0 : E) r').image_of_continuousOn hexp_cont).isClosed
    have hUK : U ⊆ K := image_mono ball_subset_closedBall
    have hσT_K : σ T ∈ K := by
      have hne : (𝓝[Ioo (0 : ℝ) T] T).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by
          rw [closure_Ioo hT_pos.ne]
          exact right_mem_Icc.mpr hT_pos.le)
      have htend : Tendsto σ (𝓝[Ioo (0 : ℝ) T] T) (𝓝 (σ T)) :=
        ((hσ.continuousOn T hT01).mono
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hT01.2))).tendsto
      exact hKclosed.mem_of_tendsto htend
        (eventually_nhdsWithin_of_forall fun t ht => hUK (hbefore t ht.1.le ht.2))
    obtain ⟨z₀, hz₀mem, hz₀eq⟩ := hσT_K
    have hz₀norm : ‖z₀‖ = r' := by
      rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz₀mem) with h | h
      · exact absurd (⟨z₀, mem_ball_zero_iff.mpr h, hz₀eq⟩ : σ T ∈ U) hTA.2
      · exact h
    -- the curve stays in the closed region on `[0, T]`, exiting exactly at `T`
    have hstayT : ∀ t ∈ Icc (0 : ℝ) T, ∃ z : E, ‖z‖ ≤ r' ∧
        σ t = expMap (I := I) g p (z : TangentSpace I p) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with rfl | htT
      · exact ⟨z₀, hz₀norm.le, hz₀eq.symm⟩
      · obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hbefore t ht.1 htT)
        exact ⟨z, hz.le, hzeq⟩
    exact ⟨T, ⟨hT_pos, hT01.2⟩, ⟨z₀, hz₀norm, hz₀eq.symm⟩, hstayT⟩
  -- ## The escape estimate: leaving `U` costs at least `r'/√c`
  have hexit : ∀ σ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = p →
      (∃ t ∈ Icc (0 : ℝ) 1, σ t ∉ U) →
      ENNReal.ofReal (r' / Real.sqrt c) ≤ Manifold.pathELength I σ 0 1 := by
    intro σ hσ hσ0 hex
    obtain ⟨T, hT, ⟨z₀, hz₀norm, hz₀eq⟩, hstayT⟩ := hfirstexit σ hσ hσ0 hex
    have hbound := hcore σ T hT.1 hT.2 hσ hσ0 hstayT
    -- the polar endpoint is `z₀`, of `g_p`-radius at least `r'/√c`
    have hwT : finv (extChartAt I p (σ T)) = z₀ := by
      rw [hz₀eq]
      exact hlinv z₀ (hz₀norm ▸ hr'ε₁)
    rw [hwT] at hbound
    refine le_trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hbound)
      (Manifold.pathELength_mono le_rfl hT.2)
    -- `r'/√c ≤ √⟨z₀, z₀⟩_p` from the Gram lower bound
    have hQ0 : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀ :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p
        (mem_extChartAt_target p) z₀
    have h2 : r' ^ 2 / c ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀ := by
      rw [div_le_iff₀ hc, mul_comm]
      calc r' ^ 2 = ‖z₀‖ ^ 2 := by rw [hz₀norm]
        _ ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀ := hgram0 z₀
    calc r' / Real.sqrt c = Real.sqrt (r' ^ 2 / c) := by
          rw [Real.sqrt_div (by positivity) c, Real.sqrt_sq hr'.le]
      _ ≤ Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z₀ z₀) :=
          Real.sqrt_le_sqrt h2
  -- ## smallness: coordinate-`ε` vectors are `g_p`-shorter than the escape cost
  obtain ⟨ε₂, hε₂, hQsmall⟩ := exists_forall_chartMetricInner_self_lt (I := I) g p
    (θ := (r' / Real.sqrt c) ^ 2) (by positivity)
  set ε : ℝ := min r' ε₂ with hεdef
  have hε : 0 < ε := lt_min hr' hε₂
  have hεr' : ε ≤ r' := min_le_left _ _
  have hεε₂ : ε ≤ ε₂ := min_le_right _ _
  have hεε₁ : ε < ε₁ := lt_of_le_of_lt hεr' hr'ε₁
  refine ⟨ε, c, hε, hc,
    fun w hw => hdom₁ w (hw.trans hεε₁),
    fun w hw => hsrc₁ w (hw.trans hεε₁),
    hinj₁.mono (ball_subset_ball hεε₁.le),
    fun r hr => (hopen (ball (0 : E) r) (ball_subset_ball
      (hr.trans (hεr'.trans (le_of_lt ((hr'ρ''.trans hρ''ρ).trans_le hρρo)))))
      isOpen_ball).2, ?_, ?_, ?_, hgram0⟩
  -- ### endpoint bound
  · intro v hv σ hσ hσ0 hσ1
    by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ U
    · -- staying case: the polar endpoint is `v` itself
      have hstay' : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = expMap (I := I) g p (z : TangentSpace I p) := by
        intro t ht
        obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hstay t ht)
        exact ⟨z, hz.le, hzeq⟩
      have hbound := hcore σ 1 one_pos le_rfl hσ hσ0 hstay'
      have hwv : finv (extChartAt I p (σ 1)) = v := by
        rw [hσ1]
        exact hlinv v (hv.trans hεε₁)
      rwa [hwv] at hbound
    · -- escape case: the curve is longer than `r'/√c > √⟨v,v⟩_p`
      push_neg at hstay
      have hbound := hexit σ hσ hσ0 hstay
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
      have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v
          < (r' / Real.sqrt c) ^ 2 := hQsmall v (hv.trans_le hεε₂)
      calc Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)
          ≤ Real.sqrt ((r' / Real.sqrt c) ^ 2) := Real.sqrt_le_sqrt hQv.le
        _ = r' / Real.sqrt c := Real.sqrt_sq (by positivity)
  -- ### escape bound for sub-balls
  · intro r hr hrε σ hσ hσ0 hσ1
    by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ U
    · -- staying case: the polar endpoint has norm at least `r`
      have hstay' : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z : E, ‖z‖ ≤ r' ∧
          σ t = expMap (I := I) g p (z : TangentSpace I p) := by
        intro t ht
        obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hstay t ht)
        exact ⟨z, hz.le, hzeq⟩
      have hbound := hcore σ 1 one_pos le_rfl hσ hσ0 hstay'
      obtain ⟨z₁, hz₁, hz₁eq⟩ := hpolar (σ 1) (hstay 1 (right_mem_Icc.mpr zero_le_one))
      have hwz₁ : finv (extChartAt I p (σ 1)) = z₁ := by
        rw [hz₁eq]
        exact hlinv z₁ (hz₁.trans hr'ε₁)
      rw [hwz₁] at hbound
      have hz₁r : r ≤ ‖z₁‖ := by
        by_contra hlt
        exact hσ1 ⟨z₁, mem_ball_zero_iff.mpr (not_le.mp hlt), hz₁eq.symm⟩
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hbound
      have hQ0 : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁ :=
        chartMetricInner_self_nonneg_of_mem_target (I := I) g p
          (mem_extChartAt_target p) z₁
      have h2 : r ^ 2 / c
          ≤ chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁ := by
        rw [div_le_iff₀ hc, mul_comm]
        calc r ^ 2 ≤ ‖z₁‖ ^ 2 := by
              refine pow_le_pow_left₀ hr.le hz₁r 2
          _ ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁ :=
              hgram0 z₁
      calc r / Real.sqrt c = Real.sqrt (r ^ 2 / c) := by
            rw [Real.sqrt_div (by positivity) c, Real.sqrt_sq hr.le]
        _ ≤ Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z₁ z₁) :=
            Real.sqrt_le_sqrt h2
    · -- escape case: leaving `U` costs `r'/√c ≥ r/√c`
      push_neg at hstay
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hexit σ hσ hσ0 hstay)
      gcongr
      exact hrε.trans hεr'
  -- ### δ-sphere first crossing with length additivity
  · intro δ hδ hδε σ hσ hσ0 hσ1
    have hQnonneg : ∀ v : E,
        0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v := fun v =>
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p
        (mem_extChartAt_target p) v
    -- continuity of the Gram quadratic form at the pole
    have hQcont : Continuous fun v : E =>
        chartMetricInner (I := I) g p (extChartAt I p p) v v := by
      have hfun : (fun v : E => chartMetricInner (I := I) g p (extChartAt I p p) v v)
          = fun v : E => ∑ i, ∑ j, chartGramOnE (I := I) g p i j (extChartAt I p p)
              * Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j v := by
        funext v
        simp only [chartMetricInner_def]
      rw [hfun]
      refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
      have hci : Continuous fun v : E => Geodesic.chartCoord (E := E) i v := by
        have h := (Geodesic.chartCoordFunctional (E := E) i).continuous
        simpa only [Geodesic.chartCoordFunctional_apply] using h
      have hcj : Continuous fun v : E => Geodesic.chartCoord (E := E) j v := by
        have h := (Geodesic.chartCoordFunctional (E := E) j).continuous
        simpa only [Geodesic.chartCoordFunctional_apply] using h
      exact (continuous_const.mul hci).mul hcj
    -- the `g_p`-radius controls the coordinate radius through the Gram bound
    have hnorm_le : ∀ v : E,
        Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) ≤ δ →
        ‖v‖ ≤ Real.sqrt c * δ := by
      intro v hv
      have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v ≤ δ ^ 2 :=
        calc chartMetricInner (I := I) g p (extChartAt I p p) v v
            = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) ^ 2 :=
              (Real.sq_sqrt (hQnonneg v)).symm
          _ ≤ δ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hv 2
      have h1 : ‖v‖ ^ 2 ≤ c * δ ^ 2 :=
        (hgram0 v).trans (mul_le_mul_of_nonneg_left hQv hc.le)
      calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
        _ ≤ Real.sqrt (c * δ ^ 2) := Real.sqrt_le_sqrt h1
        _ = Real.sqrt c * δ := by rw [Real.sqrt_mul hc.le, Real.sqrt_sq hδ.le]
    -- the open `δ`-region and its compact envelope
    set W : Set E := {v : E | v ∈ ball (0 : E) ε ∧
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) < δ}
      with hWdef
    set Uδ : Set M :=
      (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) '' W with hUδdef
    have hWopen : IsOpen W :=
      isOpen_ball.inter (isOpen_lt (Real.continuous_sqrt.comp hQcont) continuous_const)
    have hWρo : W ⊆ ball (0 : E) ρo := fun v hv =>
      ball_subset_ball
        (hεr'.trans (le_of_lt ((hr'ρ''.trans hρ''ρ).trans_le hρρo))) hv.1
    have hUδopen : IsOpen Uδ := (hopen W hWρo hWopen).2
    have hpUδ : p ∈ Uδ := by
      refine ⟨0, ⟨mem_ball_zero_iff.mpr (by simpa using hε), ?_⟩,
        expMap_zero (I := I) g p⟩
      rw [chartMetricInner_zero_left, Real.sqrt_zero]
      exact hδ
    -- first exit time from the `δ`-region
    set A : Set ℝ := Icc (0 : ℝ) 1 ∩ σ ⁻¹' Uδᶜ with hAdef
    have hA_closed : IsClosed A :=
      hσ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc
        hUδopen.isClosed_compl
    have hA_ne : A.Nonempty := ⟨1, right_mem_Icc.mpr zero_le_one, hσ1⟩
    have hA_bdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    set T : ℝ := sInf A with hTdef
    have hTA : T ∈ A := hA_closed.csInf_mem hA_ne hA_bdd
    have hT01 : T ∈ Icc (0 : ℝ) 1 := hTA.1
    have hT_pos : 0 < T := by
      rcases eq_or_lt_of_le hT01.1 with h | h
      · exact absurd (h ▸ (hσ0 ▸ hpUδ) : σ T ∈ Uδ) hTA.2
      · exact h
    have hbefore : ∀ t, 0 ≤ t → t < T → σ t ∈ Uδ := by
      intro t ht0 htT
      by_contra hnot
      exact absurd (csInf_le hA_bdd ⟨⟨ht0, htT.le.trans hT01.2⟩, hnot⟩)
        (not_le.mpr htT)
    -- the compact envelope: closed coordinate ball ∩ closed `g_p`-sublevel
    set Wc : Set E := closedBall (0 : E) (Real.sqrt c * δ) ∩
      {v : E | Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) ≤ δ}
      with hWcdef
    have hWWc : W ⊆ Wc := fun v hv =>
      ⟨mem_closedBall_zero_iff.mpr (hnorm_le v hv.2.le), hv.2.le⟩
    have hWc_cpt : IsCompact Wc :=
      (isCompact_closedBall _ _).inter_right
        (isClosed_le (Real.continuous_sqrt.comp hQcont) continuous_const)
    have hWcr' : Wc ⊆ closedBall (0 : E) r' := fun v hv =>
      mem_closedBall_zero_iff.mpr
        ((mem_closedBall_zero_iff.mp hv.1).trans (hδε.le.trans hεr'))
    set Kδ : Set M :=
      (fun z : E => expMap (I := I) g p (z : TangentSpace I p)) '' Wc with hKδdef
    have hKδ_closed : IsClosed Kδ :=
      (hWc_cpt.image_of_continuousOn (hexp_cont.mono hWcr')).isClosed
    have hUδKδ : Uδ ⊆ Kδ := image_mono hWWc
    -- the exit point sits exactly on the `g_p`-radius-`δ` sphere
    have hσT_Kδ : σ T ∈ Kδ := by
      have hne : (𝓝[Ioo (0 : ℝ) T] T).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by
          rw [closure_Ioo hT_pos.ne]
          exact right_mem_Icc.mpr hT_pos.le)
      have htend : Tendsto σ (𝓝[Ioo (0 : ℝ) T] T) (𝓝 (σ T)) :=
        ((hσ.continuousOn T hT01).mono
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hT01.2))).tendsto
      exact hKδ_closed.mem_of_tendsto htend
        (eventually_nhdsWithin_of_forall fun t ht => hUδKδ (hbefore t ht.1.le ht.2))
    obtain ⟨z, hz_mem, hz_eq⟩ := hσT_Kδ
    have hz_ε : ‖z‖ < ε :=
      (mem_closedBall_zero_iff.mp hz_mem.1).trans_lt hδε
    have hzQ : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z z)
        = δ := by
      have hzle : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z z)
          ≤ δ := hz_mem.2
      rcases lt_or_eq_of_le hzle with h | h
      · exact absurd (⟨z, ⟨mem_ball_zero_iff.mpr hz_ε, h⟩, hz_eq⟩ : σ T ∈ Uδ) hTA.2
      · exact h
    -- the curve stays in the closed `r'`-region up to `T`
    have hstayT : ∀ t ∈ Icc (0 : ℝ) T, ∃ z' : E, ‖z'‖ ≤ r' ∧
        σ t = expMap (I := I) g p (z' : TangentSpace I p) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with rfl | htT
      · exact ⟨z, (hz_ε.trans_le hεr').le, hz_eq.symm⟩
      · obtain ⟨w', hw'W, hw'eq⟩ := hbefore t ht.1 htT
        exact ⟨w', (mem_ball_zero_iff.mp hw'W.1).le.trans hεr', hw'eq.symm⟩
    -- the initial piece is at least `δ` long; split at `T`
    have hbound := hcore σ T hT_pos hT01.2 hσ hσ0 hstayT
    have hwT : finv (extChartAt I p (σ T)) = z := by
      rw [← hz_eq]
      exact hlinv z (hz_ε.trans hεε₁)
    rw [hwT, hzQ] at hbound
    refine ⟨T, hT01, ⟨z, hz_ε, hzQ, hz_eq.symm⟩, ?_⟩
    calc ENNReal.ofReal δ + Manifold.pathELength I σ T 1
        ≤ Manifold.pathELength I σ 0 T + Manifold.pathELength I σ T 1 :=
          add_le_add hbound le_rfl
      _ = Manifold.pathELength I σ 0 1 :=
          Manifold.pathELength_add hT01.1 hT01.2

section MetricNormalBall

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-- **Math.** **The metric normal ball** (do Carmo Ch. 3, Prop. 3.6, metric form;
the geometry consumed by the Hopf–Rinow theorem, do Carmo Ch. 7, Theorem 2.8).
Under the standing hypothesis that the ambient distance is the Riemannian
distance of `g`, there are `ε, δ > 0` such that `exp_p` is injective and open
on `B_ε(0) ⊂ T_pM` and:

* `d(p, exp_p v) = √⟨v, v⟩_p` for every `‖v‖ < ε` (radial geodesics realize
  the distance: the radial curve gives `≤`; the Gauss comparison applied to
  the polar lift of any `C¹` competitor, together with the escape estimate,
  gives `≥`);
* `d(p, q) ≥ δ` for every `q` outside the normal ball `exp_p(B_ε(0))` — so
  the normal ball contains the metric ball of radius `δ`. -/
theorem exists_edist_expMap_ball (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M') :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ w : E, ‖w‖ < ε →
        expMap (I := I) g p (w : TangentSpace I p) ∈ (chartAt H p).source) ∧
      Set.InjOn (fun w : E => expMap (I := I) g p (w : TangentSpace I p))
        (ball (0 : E) ε) ∧
      IsOpen ((fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        ball (0 : E) ε) ∧
      (∀ v : E, ‖v‖ < ε →
        edist p (expMap (I := I) g p (v : TangentSpace I p))
          = ENNReal.ofReal (Real.sqrt
              (chartMetricInner (I := I) g p (extChartAt I p p) v v))) ∧
      (∀ q : M', q ∉ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
          ball (0 : E) ε →
        ENNReal.ofReal δ ≤ edist p q) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  obtain ⟨εA, hεA, hdomA, hsrcA, hray⟩ := exists_pathELength_expMap_ray (I := I) g p
  obtain ⟨εB, c, hεB, hc, hdomB, hsrcB, hinjB, hopenB, hlower, hescape, -⟩ :=
    exists_le_pathELength (I := I) g p
  set ε : ℝ := min εA εB with hεdef
  have hε : 0 < ε := lt_min hεA hεB
  have hεεA : ε ≤ εA := min_le_left _ _
  have hεεB : ε ≤ εB := min_le_right _ _
  refine ⟨ε, ε / Real.sqrt c, hε, by positivity,
    fun w hw => hdomA w (hw.trans_le hεεA),
    fun w hw => hsrcA w (hw.trans_le hεεA),
    hinjB.mono (ball_subset_ball hεεB),
    hopenB ε hεεB, ?_, ?_⟩
  · -- the distance to `exp_p v` is the `g_p`-norm of `v`
    intro v hv
    have hvA : ‖v‖ < εA := hv.trans_le hεεA
    have hvB : ‖v‖ < εB := hv.trans_le hεεB
    obtain ⟨hC1, hlen⟩ := hray v hvA
    refine le_antisymm ?_ ?_
    · -- `≤`: the radial curve is a competitor of the right length
      rw [IsRiemannianManifold.out (I := I) p
        (expMap (I := I) g p (v : TangentSpace I p))]
      have h0 : (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 0
          = p := by
        show expMap (I := I) g p (((0 : ℝ) • v : E) : TangentSpace I p) = p
        rw [zero_smul]
        exact expMap_zero (I := I) g p
      have h1 : (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 1
          = expMap (I := I) g p (v : TangentSpace I p) := by
        show expMap (I := I) g p (((1 : ℝ) • v : E) : TangentSpace I p)
          = expMap (I := I) g p (v : TangentSpace I p)
        rw [one_smul]
      exact (Manifold.riemannianEDist_le_pathELength hC1 h0 h1 zero_le_one).trans_eq
        hlen
    · -- `≥`: every `C¹` competitor is at least as long as the radial geodesic
      rw [IsRiemannianManifold.out (I := I) p
        (expMap (I := I) g p (v : TangentSpace I p))]
      by_contra hlt
      push_neg at hlt
      obtain ⟨σ, hσ0, hσ1, hσC1, hσlen⟩ :=
        Manifold.exists_lt_of_riemannianEDist_lt hlt
      exact absurd hσlen (not_lt.mpr (hlower v hvB σ hσC1 hσ0 hσ1))
  · -- points outside the normal ball are at distance at least `δ`
    intro q hq
    rw [IsRiemannianManifold.out (I := I) p q]
    by_contra hlt
    push_neg at hlt
    obtain ⟨σ, hσ0, hσ1, hσC1, hσlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt
    have hout : σ 1 ∉ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        ball (0 : E) ε := by rw [hσ1]; exact hq
    exact absurd hσlen (not_lt.mpr (hescape ε hε hεεB σ hσC1 hσ0 hout))

/-- **Math.** **Sphere-minimum distance decomposition** (do Carmo Ch. 7, proof
of Theorem 2.8: the geodesic-sphere step). Under the standing hypothesis
`g.IsRiemannianDist` there are `ε, c > 0` (depending only on `p`) such that for
every `δ > 0` with `√c · δ < ε` and every `q` with `d(p, q) ≥ δ`, there is a
geodesic-sphere point `x₀ = exp_p z`, `|z|_p = δ`, with

* `d(p, q) = δ + d(x₀, q)` — **the decomposition** — and
* `x₀` minimizes `d(·, q)` among all points of the geodesic sphere
  `S_δ(p) = exp_p {|z|_p = δ}`.

`≤` is the triangle inequality through `x₀`, radial geodesics realizing
`d(p, x₀) = δ` (`exists_edist_expMap_ball`); `≥` holds because every `C¹`
competitor from `p` to `q` first crosses `S_δ(p)`, paying at least
`δ + d(crossing point, q) ≥ δ + d(x₀, q)` (`exists_le_pathELength`,
first-crossing clause); `x₀` exists because the sphere is compact and
`d(·, q)` is continuous. -/
theorem exists_normalSphere_min_edist (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M') :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ∀ (q : M') (δ : ℝ), 0 < δ → Real.sqrt c * δ < ε →
        ENNReal.ofReal δ ≤ edist p q →
        ∃ z : E, ‖z‖ ≤ Real.sqrt c * δ ∧ ‖z‖ < ε ∧
          Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z z) = δ ∧
          edist p (expMap (I := I) g p (z : TangentSpace I p))
            = ENNReal.ofReal δ ∧
          edist p q = ENNReal.ofReal δ
            + edist (expMap (I := I) g p (z : TangentSpace I p)) q ∧
          ∀ z' : E, ‖z'‖ < ε →
            Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) z' z') = δ →
            edist (expMap (I := I) g p (z : TangentSpace I p)) q
              ≤ edist (expMap (I := I) g p (z' : TangentSpace I p)) q := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  haveI : Nontrivial E :=
    Module.nontrivial_of_finrank_pos (R := ℝ)
      (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  obtain ⟨εD, δD, hεD, hδD, hdomD, hsrcD, hinjD, hopenD, hedistD, hescD⟩ :=
    exists_edist_expMap_ball (I := I) g hg p
  obtain ⟨εB, c, hεB, hc, hdomB, hsrcB, hinjB, hopenB, hlower, hesc, hcross, hgram⟩ :=
    exists_le_pathELength (I := I) g p
  obtain ⟨εC, hεC, hdomC, hsrcC, hinjC, hopenC, hfC1, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  set ε : ℝ := min (min εD εB) (εC / 2) with hεdef
  have hε : 0 < ε := lt_min (lt_min hεD hεB) (by positivity)
  have hεεD : ε ≤ εD := (min_le_left _ _).trans (min_le_left _ _)
  have hεεB : ε ≤ εB := (min_le_left _ _).trans (min_le_right _ _)
  have hεεC2 : ε ≤ εC / 2 := min_le_right _ _
  have hεC2εC : εC / 2 < εC := by linarith
  -- `exp_p` is continuous on the closed `εC/2`-ball (through the chart)
  have hexp_cont : ContinuousOn
      (fun z : E => expMap (I := I) g p (z : TangentSpace I p))
      (closedBall (0 : E) (εC / 2)) := by
    have h1 : ContinuousOn f (closedBall (0 : E) (εC / 2)) :=
      hfC1.continuousOn.mono (closedBall_subset_ball hεC2εC)
    have h2 : ContinuousOn (extChartAt I p).symm (extChartAt I p).target :=
      continuousOn_extChartAt_symm p
    have hmap : MapsTo f (closedBall (0 : E) (εC / 2)) (extChartAt I p).target := by
      intro z hz
      exact (extChartAt I p).map_source (by
        rw [extChartAt_source]
        exact hsrcC z ((mem_closedBall_zero_iff.mp hz).trans_lt hεC2εC))
    refine (h2.comp h1 hmap).congr ?_
    intro z hz
    show expMap (I := I) g p (z : TangentSpace I p) = (extChartAt I p).symm (f z)
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]
      exact hsrcC z ((mem_closedBall_zero_iff.mp hz).trans_lt hεC2εC))).symm
  refine ⟨ε, c, hε, hc, fun w hw => hdomD w (hw.trans_le hεεD), ?_⟩
  intro q δ hδ hδε hδq
  have hQnonneg : ∀ v : E,
      0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v := fun v =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) v
  -- the Gram bound turns `g_p`-radius `δ` into coordinate radius `√c·δ`
  have hnorm_le : ∀ v : E,
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) ≤ δ →
      ‖v‖ ≤ Real.sqrt c * δ := by
    intro v hv
    have hQv : chartMetricInner (I := I) g p (extChartAt I p p) v v ≤ δ ^ 2 :=
      calc chartMetricInner (I := I) g p (extChartAt I p p) v v
          = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) ^ 2 :=
            (Real.sq_sqrt (hQnonneg v)).symm
        _ ≤ δ ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hv 2
    have h1 : ‖v‖ ^ 2 ≤ c * δ ^ 2 :=
      (hgram v).trans (mul_le_mul_of_nonneg_left hQv hc.le)
    calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
      _ ≤ Real.sqrt (c * δ ^ 2) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt c * δ := by rw [Real.sqrt_mul hc.le, Real.sqrt_sq hδ.le]
  -- continuity of the Gram quadratic form (closedness of the sphere level)
  have hQcont : Continuous fun v : E =>
      chartMetricInner (I := I) g p (extChartAt I p p) v v := by
    have hfun : (fun v : E => chartMetricInner (I := I) g p (extChartAt I p p) v v)
        = fun v : E => ∑ i, ∑ j, chartGramOnE (I := I) g p i j (extChartAt I p p)
            * Geodesic.chartCoord (E := E) i v * Geodesic.chartCoord (E := E) j v := by
      funext v
      simp only [chartMetricInner_def]
    rw [hfun]
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    have hci : Continuous fun v : E => Geodesic.chartCoord (E := E) i v := by
      have h := (Geodesic.chartCoordFunctional (E := E) i).continuous
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    have hcj : Continuous fun v : E => Geodesic.chartCoord (E := E) j v := by
      have h := (Geodesic.chartCoordFunctional (E := E) j).continuous
      simpa only [Geodesic.chartCoordFunctional_apply] using h
    exact (continuous_const.mul hci).mul hcj
  -- the coordinate `g_p`-sphere of radius `δ` is compact …
  set S : Set E := closedBall (0 : E) (Real.sqrt c * δ) ∩
    {v : E | Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) = δ}
    with hSdef
  have hS_cpt : IsCompact S :=
    (isCompact_closedBall _ _).inter_right
      (isClosed_eq (Real.continuous_sqrt.comp hQcont) continuous_const)
  -- … and nonempty: scale any unit vector to `g_p`-radius exactly `δ`
  have hS_ne : S.Nonempty := by
    obtain ⟨w₀, hw₀⟩ :=
      NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1) |>.mpr zero_le_one
    have hw₀norm : ‖w₀‖ = 1 := mem_sphere_zero_iff_norm.mp hw₀
    have hQw₀pos : 0 < chartMetricInner (I := I) g p (extChartAt I p p) w₀ w₀ := by
      rcases lt_or_eq_of_le (hQnonneg w₀) with h | h
      · exact h
      · exfalso
        have h1 := hgram w₀
        rw [← h, mul_zero, hw₀norm] at h1
        norm_num at h1
    have hsq : 0 < Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) w₀ w₀) :=
      Real.sqrt_pos.mpr hQw₀pos
    set t : ℝ :=
      δ / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) w₀ w₀) with htdef
    have ht : 0 < t := div_pos hδ hsq
    have hlevel : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
        (t • w₀) (t • w₀)) = δ := by
      have hquad : chartMetricInner (I := I) g p (extChartAt I p p) (t • w₀) (t • w₀)
          = t ^ 2 * chartMetricInner (I := I) g p (extChartAt I p p) w₀ w₀ := by
        rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
        ring
      rw [hquad, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le, htdef,
        div_mul_cancel₀ δ hsq.ne']
    exact ⟨t • w₀, mem_closedBall_zero_iff.mpr (hnorm_le (t • w₀) hlevel.le), hlevel⟩
  -- `d(·, q)` attains its minimum on the compact sphere
  have hSr : S ⊆ closedBall (0 : E) (εC / 2) := fun v hv =>
    mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp hv.1).trans (hδε.le.trans hεεC2))
  have hcont_edist : ContinuousOn
      (fun z : E => edist (expMap (I := I) g p (z : TangentSpace I p)) q) S :=
    continuous_edist.comp_continuousOn
      ((hexp_cont.mono hSr).prodMk continuousOn_const)
  obtain ⟨z₀, hz₀S, hz₀min⟩ := hS_cpt.exists_isMinOn hS_ne hcont_edist
  have hz₀ε : ‖z₀‖ < ε := (mem_closedBall_zero_iff.mp hz₀S.1).trans_lt hδε
  have hpx₀ : edist p (expMap (I := I) g p (z₀ : TangentSpace I p))
      = ENNReal.ofReal δ := by
    have h := hedistD z₀ (hz₀ε.trans_le hεεD)
    rw [hz₀S.2] at h
    exact h
  -- `≤`: triangle inequality through the radial realization at `x₀`
  have hle : edist p q ≤ ENNReal.ofReal δ
      + edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q := by
    calc edist p q
        ≤ edist p (expMap (I := I) g p (z₀ : TangentSpace I p))
          + edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q :=
          edist_triangle _ _ _
      _ = ENNReal.ofReal δ
          + edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q := by rw [hpx₀]
  -- `≥`: every competitor crosses the sphere, paying `δ + d(x₀, q)`
  have hge : ENNReal.ofReal δ
      + edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q ≤ edist p q := by
    by_contra hlt
    have hlt' : Manifold.riemannianEDist I p q < ENNReal.ofReal δ
        + edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q := by
      rw [← IsRiemannianManifold.out (I := I) p q]
      exact not_le.mp hlt
    obtain ⟨σ, hσ0, hσ1, hσC1, hσlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt hlt'
    -- `q` lies outside the open `δ`-region: else `d(p, q) < δ`
    have hqout : σ 1 ∉ (fun w : E => expMap (I := I) g p (w : TangentSpace I p)) ''
        {v : E | v ∈ ball (0 : E) εB ∧
          Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) < δ} := by
      rw [hσ1]
      rintro ⟨v, ⟨hvB, hvQ⟩, rfl⟩
      have hvε : ‖v‖ < ε := (hnorm_le v hvQ.le).trans_lt hδε
      have hd := hedistD v (hvε.trans_le hεεD)
      have hlt2 : edist p (expMap (I := I) g p (v : TangentSpace I p))
          < ENNReal.ofReal δ := by
        rw [hd]
        exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr hvQ
      exact absurd hδq (not_le.mpr hlt2)
    obtain ⟨T, hT01, ⟨z, hzB, hzQ, hσT⟩, hsplit⟩ :=
      hcross δ hδ (hδε.trans_le hεεB) σ hσC1 hσ0 hqout
    -- the crossing point is a sphere point, so it pays at least `d(x₀, q)`
    have hzS : z ∈ S := ⟨mem_closedBall_zero_iff.mpr (hnorm_le z hzQ.le), hzQ⟩
    have hxq : edist (expMap (I := I) g p (z : TangentSpace I p)) q
        ≤ Manifold.pathELength I σ T 1 := by
      rw [IsRiemannianManifold.out (I := I) _ q]
      exact Manifold.riemannianEDist_le_pathELength
        (hσC1.mono (Icc_subset_Icc hT01.1 le_rfl)) hσT hσ1 hT01.2
    have hmin : edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q
        ≤ edist (expMap (I := I) g p (z : TangentSpace I p)) q :=
      isMinOn_iff.mp hz₀min z hzS
    have hchain : ENNReal.ofReal δ
        + edist (expMap (I := I) g p (z₀ : TangentSpace I p)) q
        ≤ Manifold.pathELength I σ 0 1 :=
      le_trans (add_le_add le_rfl (hmin.trans hxq)) hsplit
    exact absurd hchain (not_le.mpr hσlen)
  exact ⟨z₀, mem_closedBall_zero_iff.mp hz₀S.1, hz₀ε, hz₀S.2, hpx₀,
    le_antisymm hle hge, fun z' hz'ε hz'Q =>
    isMinOn_iff.mp hz₀min z'
      ⟨mem_closedBall_zero_iff.mpr (hnorm_le z' hz'Q.le), hz'Q⟩⟩

end MetricNormalBall

end Exponential

end Riemannian

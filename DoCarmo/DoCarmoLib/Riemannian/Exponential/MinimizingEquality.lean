import DoCarmoLib.Riemannian.Exponential.Minimizing
import DoCarmoLib.Riemannian.Exponential.LocalDiffeo
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.GramBound

/-!
# The equality case of the Gauss radius comparison
(do Carmo Ch. 3, Prop. 3.6, equality analysis, pointwise stage)

do Carmo, *Riemannian Geometry*, Ch. 3, Proposition 3.6: if a competing curve
from `p` to `exp_p v` realizes the length `|v|_p` of the radial geodesic, its
image **is** the radial segment. The analytic mechanism is that equality in the
integrated radius comparison forces equality, at every time, in the pointwise
radial lower bound
$$\langle v, \xi\rangle_p^2 \le \langle v,v\rangle_p\,
  \big|(d\exp_p)_v(\xi)\big|^2,$$
and equality there forces `ξ` to be **radial**: the normal component `ξ_N` of
`ξ` has `(d exp_p)_v(ξ_N)` of vanishing length by the Gauss lemma expansion,
hence vanishes by positive definiteness of the metric near `p`, hence `ξ_N = 0`
by invertibility of `(d exp_p)_v`. This file provides the pointwise stage:

* `radial_equality_forcing` — the abstract forcing step: equality in the
  radial bound at `(v, ξ)` implies
  `ξ = (⟨v,ξ⟩_p / ⟨v,v⟩_p) • v`.
* `gauss_radius_equality_ftc` — equality in the integrated radius comparison
  on `[a, b]` propagates to every subinterval: the radius of the polar lift
  satisfies `r(t) = r(a) + ∫_a^t |ċ|` for **all** `t`, so `r` is
  differentiable with `r' = |ċ| ≥ 0` on the interior.
* `exists_gauss_equality_radial_ball` — the instantiated statement on a Gauss
  ball of `exp_p`: a `C¹` polar competitor realizing equality has, at every
  interior time where it is away from the origin, a **radial, outward**
  velocity: `w'(t) = (⟨w,w'⟩_p / ⟨w,w⟩_p) • w(t)` with `⟨w,w'⟩_p ≥ 0`.

The remaining (global) stage — the direction `w/|w|_p` is constant on the set
`{w ≠ 0}`, the radius is monotone, and the image of the competitor is the
radial segment — consumes these pointwise facts.
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

/-- **Math.** **The radial forcing step**: if the radial lower bound
`⟨v,ξ⟩_p² ≤ ⟨v,v⟩_p · |Df_v(ξ)|²` holds with **equality** at `(v, ξ)` — where
`f` satisfies the Gauss identity `⟨Df_v(v), Df_v(ξ')⟩_{f(v)} = ⟨v,ξ'⟩_p` at
`v`, the metric at `f(v)` is definite, and `Df_v` is injective — then `ξ` is
radial: `ξ = (⟨v,ξ⟩_p / ⟨v,v⟩_p) • v`. Decompose `ξ = λv + ξ_N` with
`⟨v,ξ_N⟩_p = 0`; the Gauss identity kills the cross terms, so equality forces
`|Df_v(ξ_N)|² = 0`, hence `Df_v(ξ_N) = 0` by definiteness and `ξ_N = 0` by
injectivity. -/
theorem radial_equality_forcing (g : RiemannianMetric I M) (p : M)
    (f : E → E) {v ξ : E}
    (hgauss : ∀ ξ' : E, chartMetricInner (I := I) g p (f v)
        (fderiv ℝ f v v) (fderiv ℝ f v ξ')
      = chartMetricInner (I := I) g p (extChartAt I p p) v ξ')
    (hQpos : 0 < chartMetricInner (I := I) g p (extChartAt I p p) v v)
    (hdef : ∀ z : E, chartMetricInner (I := I) g p (f v) z z = 0 → z = 0)
    (hinj : Function.Injective (fderiv ℝ f v))
    (heq : chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
      = chartMetricInner (I := I) g p (extChartAt I p p) v v
        * chartMetricInner (I := I) g p (f v)
            (fderiv ℝ f v ξ) (fderiv ℝ f v ξ)) :
    ξ = (chartMetricInner (I := I) g p (extChartAt I p p) v ξ
        / chartMetricInner (I := I) g p (extChartAt I p p) v v) • v := by
  classical
  set Qv := chartMetricInner (I := I) g p (extChartAt I p p) v v with hQv
  set Qξ := chartMetricInner (I := I) g p (extChartAt I p p) v ξ with hQξ
  set lam : ℝ := Qξ / Qv with hlam
  set ξN : E := ξ - lam • v with hξN
  have hξdecomp : ξ = lam • v + ξN := by rw [hξN]; abel
  have hlamQv : lam * Qv = Qξ := by
    rw [hlam, div_mul_cancel₀ _ hQpos.ne']
  -- the normal component is `g_p`-orthogonal to `v`
  have hQξN : chartMetricInner (I := I) g p (extChartAt I p p) v ξN = 0 := by
    rw [hξN, sub_eq_add_neg, chartMetricInner_add_right, ← neg_one_smul ℝ (lam • v),
      smul_smul, chartMetricInner_smul_right]
    rw [← hQξ, ← hQv]
    linear_combination -hlamQv
  -- expand `|Df(ξ)|²` through the Gauss identity
  have hDξ : fderiv ℝ f v ξ = lam • fderiv ℝ f v v + fderiv ℝ f v ξN := by
    conv_lhs => rw [hξdecomp]
    rw [map_add, map_smul]
  have hexpand : chartMetricInner (I := I) g p (f v)
      (fderiv ℝ f v ξ) (fderiv ℝ f v ξ)
      = lam ^ 2 * Qv + chartMetricInner (I := I) g p (f v)
          (fderiv ℝ f v ξN) (fderiv ℝ f v ξN) := by
    rw [hDξ, chartMetricInner_add_left, chartMetricInner_add_right,
      chartMetricInner_add_right, chartMetricInner_smul_left,
      chartMetricInner_smul_left, chartMetricInner_smul_right,
      chartMetricInner_symm (I := I) g p _ (fderiv ℝ f v ξN)
        (lam • fderiv ℝ f v v)]
    rw [chartMetricInner_smul_left, hgauss v, hgauss ξN, hQξN]
    ring
  -- equality forces the normal image to have vanishing squared length
  have hzero : chartMetricInner (I := I) g p (f v)
      (fderiv ℝ f v ξN) (fderiv ℝ f v ξN) = 0 := by
    have h1 : Qξ ^ 2 = Qv * (lam ^ 2 * Qv + chartMetricInner (I := I) g p (f v)
        (fderiv ℝ f v ξN) (fderiv ℝ f v ξN)) := by
      rw [← hexpand]; exact heq
    have h2 : Qv * (lam ^ 2 * Qv) = Qξ ^ 2 := by
      rw [← hlamQv]; ring
    nlinarith [hQpos]
  -- definiteness at `f(v)` and injectivity of `Df_v` kill the normal part
  have hDξN : fderiv ℝ f v ξN = 0 := hdef _ hzero
  have hξN0 : ξN = 0 := by
    apply hinj
    rw [hDξN, map_zero]
  rw [hξdecomp, hξN0, add_zero, hlam, hQξ, hQv]

/-- **Math.** **Equality propagates to every subinterval, in FTC form**: if
the Gauss radius comparison on `[a, b]` holds with equality, then for every
`t ∈ [a, b]` the radius of the polar lift satisfies
`r(t) = r(a) + ∫_a^t |ċ|`; in particular `r` is differentiable on `(a, b)`
with derivative the (nonnegative) speed. The point is that the comparison
holds on every subinterval, and a monotone deficit vanishing at both ends
vanishes identically. -/
theorem gauss_radius_equality_ftc (g : RiemannianMetric I M) (p : M)
    (f : E → E) {ρ : ℝ}
    (htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target)
    (hC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ))
    (hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ))
    {w w' : ℝ → E} {a b : ℝ}
    (hw_cont : ContinuousOn w (Icc a b))
    (hw : ∀ t ∈ Ioo a b, HasDerivAt w (w' t) t)
    (hw' : ContinuousOn w' (Icc a b))
    (hwball : ∀ t ∈ Icc a b, ‖w t‖ < ρ)
    (heq : Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w b) (w b))
        - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w a) (w a))
      = ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t)))) :
    (∀ t ∈ Icc a b,
      Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t))
        = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w a) (w a))
          + ∫ s in a..t, Real.sqrt (chartMetricInner (I := I) g p (f (w s))
              (fderiv ℝ f (w s) (w' s)) (fderiv ℝ f (w s) (w' s)))) ∧
    (∀ t ∈ Ioo a b,
      HasDerivAt (fun s => Real.sqrt
          (chartMetricInner (I := I) g p (extChartAt I p p) (w s) (w s)))
        (Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t)))) t) := by
  classical
  set r : ℝ → ℝ := fun t =>
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t))
    with hrdef
  set speed : ℝ → ℝ := fun t =>
    Real.sqrt (chartMetricInner (I := I) g p (f (w t))
      (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) with hspeeddef
  -- the speed integrand is continuous on `[a, b]`
  have hwmem : ∀ t ∈ Icc a b, w t ∈ ball (0 : E) ρ :=
    fun t ht => mem_ball_zero_iff.mpr (hwball t ht)
  have hspeed_cont : ContinuousOn speed (Icc a b) := by
    have hfw : ContinuousOn (fun t => f (w t)) (Icc a b) :=
      hC1.continuousOn.comp hw_cont hwmem
    have hdf : ContinuousOn (fun t => fderiv ℝ f (w t)) (Icc a b) :=
      (hC1.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).comp hw_cont hwmem
    have happ : ContinuousOn (fun t => fderiv ℝ f (w t) (w' t)) (Icc a b) :=
      hdf.clm_apply hw'
    have htgt' : ∀ t ∈ Icc a b, f (w t) ∈ (extChartAt I p).target :=
      fun t ht => htgt (w t) (hwball t ht)
    exact Real.continuous_sqrt.comp_continuousOn
      (continuousOn_chartMetricInner_along (I := I) g p hfw happ happ htgt')
  -- the comparison on every subinterval
  have hsub : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b →
      r d - r c ≤ ∫ t in c..d, speed t := by
    intro c d hac hcd hdb
    exact gauss_radius_comparison (I := I) g p f htgt hC1 hradial hcd
      (hw_cont.mono (Icc_subset_Icc hac hdb))
      (fun t ht => hw t ⟨hac.trans_lt ht.1, ht.2.trans_le hdb⟩)
      (hw'.mono (Icc_subset_Icc hac hdb))
      (fun t ht => hwball t ⟨hac.trans ht.1, ht.2.trans hdb⟩)
  -- integrability of the speed on subintervals
  have hint : ∀ c d : ℝ, a ≤ c → c ≤ d → d ≤ b →
      IntervalIntegrable speed volume c d := by
    intro c d hac hcd hdb
    refine (hspeed_cont.mono (Icc_subset_Icc hac hdb)).intervalIntegrable_of_Icc hcd
  -- the FTC identity at every time
  have hftc : ∀ t ∈ Icc a b, r t = r a + ∫ s in a..t, speed s := by
    intro t ht
    have h1 : r t - r a ≤ ∫ s in a..t, speed s := hsub a t le_rfl ht.1 ht.2
    have h2 : r b - r t ≤ ∫ s in t..b, speed s := hsub t b ht.1 ht.2 le_rfl
    have hadd : (∫ s in a..t, speed s) + ∫ s in t..b, speed s
        = ∫ s in a..b, speed s :=
      intervalIntegral.integral_add_adjacent_intervals
        (hint a t le_rfl ht.1 ht.2) (hint t b ht.1 ht.2 le_rfl)
    have hb : r b - r a = ∫ s in a..b, speed s := heq
    linarith
  refine ⟨hftc, ?_⟩
  -- differentiate the FTC identity at interior times
  intro t ht
  have htmem : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  have hcontAt : ContinuousAt speed t :=
    (hspeed_cont.mono Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds ht.1 ht.2)
  have hmeasAt : StronglyMeasurableAtFilter speed (𝓝 t) volume :=
    ⟨Ioo a b, Ioo_mem_nhds ht.1 ht.2,
      (hspeed_cont.mono Ioo_subset_Icc_self).aestronglyMeasurable measurableSet_Ioo⟩
  have hI : HasDerivAt (fun u => ∫ s in a..u, speed s) (speed t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hint a t le_rfl ht.1.le ht.2.le) hmeasAt hcontAt
  have hI' : HasDerivAt (fun u => r a + ∫ s in a..u, speed s) (speed t) t :=
    hI.const_add (r a)
  refine hI'.congr_of_eventuallyEq ?_
  filter_upwards [htmem] with s hs
  exact hftc s hs

/-- **Math.** **The pointwise equality case on a Gauss ball of `exp_p`**
(do Carmo Ch. 3, Prop. 3.6, equality analysis, pointwise stage). There is
`ρ > 0` such that for every `C¹` polar competitor `w : [a,b] → B_ρ(0)` whose
chart-read length realizes the radius gain with **equality**,
$$\sqrt{\langle w(b),w(b)\rangle_p} - \sqrt{\langle w(a),w(a)\rangle_p}
  = \int_a^b |\dot c|,$$
at every interior time `t` with `w(t) ≠ 0` the velocity is **radial and
outward**:
$$w'(t) = \frac{\langle w(t),w'(t)\rangle_p}{\langle w(t),w(t)\rangle_p}
  \, w(t), \qquad \langle w(t),w'(t)\rangle_p \ge 0.$$
This is the pointwise input for the equality clause of do Carmo's
Proposition 3.6: it forces the competitor to run along a fixed ray through
the origin. -/
theorem exists_gauss_equality_radial_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ (w w' : ℝ → E) (a b : ℝ), a < b →
        ContinuousOn w (Icc a b) →
        (∀ t ∈ Ioo a b, HasDerivAt w (w' t) t) →
        ContinuousOn w' (Icc a b) →
        (∀ t ∈ Icc a b, ‖w t‖ < ρ) →
        (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w b) (w b))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w a) (w a))
          = ∫ t in a..b, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t)))) →
        (∀ t ∈ Ioo a b,
          HasDerivAt (fun s => Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p p) (w s) (w s)))
            (Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t)))) t) ∧
        ∀ t ∈ Ioo a b, w t ≠ 0 →
          0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t) ∧
          w' t = (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t)
              / chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t))
            • w t) := by
  classical
  obtain ⟨ρg, hρg, hdomg, hsrcg, hgauss⟩ := exists_gauss_lemma_ball (I := I) g p
  obtain ⟨ρr, hρr, hdomr, hsrcr, hradial⟩ :=
    exists_gauss_radial_lower_bound_ball (I := I) g p
  obtain ⟨ρe, hρe, hdome, hsrce, hequiv⟩ :=
    exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
  obtain ⟨ε₁, hε₁, hdom₁, hsrc₁, hinj₁, hopenM₁, hfC1₁, finv, hlinv, hfinvC1⟩ :=
    exists_c1_local_diffeomorphism_expMap (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  set f : E → E :=
    fun u => extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)) with hfdef
  have hgram0 : ∀ z : E,
      ‖z‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z z :=
    fun z => hgramV _ (mem_of_mem_nhds hVc) z
  -- `f` is continuous at `0` with `f 0` the pole, so a small ball lands in `Vc`
  have hf0 : f 0 = extChartAt I p p := by
    rw [hfdef]
    exact congrArg (extChartAt I p) (expMap_zero (I := I) g p)
  have hfc : ContinuousAt f 0 :=
    hfC1₁.continuousOn.continuousAt (isOpen_ball.mem_nhds (by simpa using hε₁))
  obtain ⟨ρv, hρv, hfV⟩ : ∃ ρv : ℝ, 0 < ρv ∧ ∀ z : E, ‖z‖ < ρv → f z ∈ Vc := by
    have h1 : Vc ∈ 𝓝 (f 0) := by rw [hf0]; exact hVc
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hfc h1)
    exact ⟨δ, hδ, fun z hz => hδsub (by simpa [dist_eq_norm] using hz)⟩
  set ρ : ℝ := min (min ρg ρr) (min ρe (min ρv ε₁)) with hρdef
  have hρ : 0 < ρ := lt_min (lt_min hρg hρr) (lt_min hρe (lt_min hρv hε₁))
  have hρρg : ρ ≤ ρg := (min_le_left _ _).trans (min_le_left _ _)
  have hρρr : ρ ≤ ρr := (min_le_left _ _).trans (min_le_right _ _)
  have hρρe : ρ ≤ ρe := (min_le_right _ _).trans (min_le_left _ _)
  have hρρv : ρ ≤ ρv :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hρε₁ : ρ ≤ ε₁ :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have htgt : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target := by
    intro u hu
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrcg u (hu.trans_le hρρg))
  have hfC1 : ContDiffOn ℝ 1 f (ball (0 : E) ρ) :=
    hfC1₁.mono (ball_subset_ball hρε₁)
  refine ⟨ρ, hρ, fun u hu => hdomg u (hu.trans_le hρρg),
    fun u hu => hsrcg u (hu.trans_le hρρg), ?_⟩
  intro w w' a b _hab hw_cont hw hw' hwball heq
  have hradialρ : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p (extChartAt I p p) v ξ ^ 2
        ≤ chartMetricInner (I := I) g p (extChartAt I p p) v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ) :=
    fun v ξ hv => hradial v ξ (hv.trans_le hρρr)
  obtain ⟨hftc, hderiv⟩ := gauss_radius_equality_ftc (I := I) g p f htgt hfC1
    hradialρ hw_cont hw hw' hwball heq
  refine ⟨hderiv, ?_⟩
  intro t ht hwt0
  have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  -- positivity of the pole Gram form at `w t`
  have hQpos : 0 < chartMetricInner (I := I) g p (extChartAt I p p)
      (w t) (w t) := by
    have h1 := hgram0 (w t)
    have h2 : 0 < ‖w t‖ ^ 2 := by positivity
    nlinarith
  -- the radius is differentiable at `t` by the product rule, with derivative
  -- `⟨w,w'⟩_p / r`
  have hQderiv : HasDerivAt (fun s => chartMetricInner (I := I) g p
      (extChartAt I p p) (w s) (w s))
      (2 * chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t)) t := by
    have h := hasDerivAt_chartMetricInner_const_base (I := I) g p
      (extChartAt I p p) (hw t ht) (hw t ht)
    have hsymm : chartMetricInner (I := I) g p (extChartAt I p p) (w' t) (w t)
        = chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t) :=
      chartMetricInner_symm (I := I) g p _ _ _
    rw [hsymm] at h
    convert h using 1
    ring
  have hrderiv : HasDerivAt (fun s => Real.sqrt (chartMetricInner (I := I) g p
      (extChartAt I p p) (w s) (w s)))
      (2 * chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t)
        / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w t) (w t)))) t :=
    hQderiv.sqrt hQpos.ne'
  -- identify the two derivatives of the radius
  have hspeedt := hderiv t ht
  have hderiv_eq : 2 * chartMetricInner (I := I) g p (extChartAt I p p)
        (w t) (w' t)
        / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
            (w t) (w t)))
      = Real.sqrt (chartMetricInner (I := I) g p (f (w t))
          (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) :=
    hrderiv.unique hspeedt
  have hrpos : 0 < Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
      (w t) (w t)) := Real.sqrt_pos.mpr hQpos
  -- the inner product `⟨w,w'⟩_p` is nonnegative and realizes the speed
  have hQww' : chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t)
      = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t))
        * Real.sqrt (chartMetricInner (I := I) g p (f (w t))
            (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t))) := by
    have h2r : (2 : ℝ) * Real.sqrt (chartMetricInner (I := I) g p
        (extChartAt I p p) (w t) (w t)) ≠ 0 := by positivity
    field_simp at hderiv_eq
    linarith [hderiv_eq]
  have hQww'_nonneg : 0 ≤ chartMetricInner (I := I) g p (extChartAt I p p)
      (w t) (w' t) := by
    rw [hQww']
    positivity
  -- equality in the radial lower bound at `(w t, w' t)`
  have heqpt : chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w' t) ^ 2
      = chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)
        * chartMetricInner (I := I) g p (f (w t))
            (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t)) := by
    have hQfnonneg : 0 ≤ chartMetricInner (I := I) g p (f (w t))
        (fderiv ℝ f (w t) (w' t)) (fderiv ℝ f (w t) (w' t)) :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p
        (htgt (w t) (hwball t htIcc)) _
    rw [hQww']
    rw [mul_pow, Real.sq_sqrt hQpos.le, Real.sq_sqrt hQfnonneg]
  -- the forcing step: the velocity is radial
  have hgausst : ∀ ξ' : E, chartMetricInner (I := I) g p (f (w t))
      (fderiv ℝ f (w t) (w t)) (fderiv ℝ f (w t) ξ')
      = chartMetricInner (I := I) g p (extChartAt I p p) (w t) ξ' := by
    intro ξ'
    exact hgauss (w t) ξ' ((hwball t htIcc).trans_le hρρg)
  have hdef : ∀ z : E, chartMetricInner (I := I) g p (f (w t)) z z = 0 →
      z = 0 := by
    intro z hz
    have h1 := hgramV (f (w t)) (hfV (w t) ((hwball t htIcc).trans_le hρρv)) z
    rw [hz, mul_zero] at h1
    have h2 : ‖z‖ = 0 := by nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
    exact norm_eq_zero.mp h2
  have hinj : Function.Injective (fderiv ℝ f (w t)) := by
    obtain ⟨D', hD'⟩ := hequiv (w t) ((hwball t htIcc).trans_le hρρe)
    have hfd : fderiv ℝ f (w t) = (D' : E →L[ℝ] E) := hD'.hasFDerivAt.fderiv
    rw [hfd]
    exact D'.injective
  exact ⟨hQww'_nonneg, radial_equality_forcing (I := I) g p f hgausst hQpos
    hdef hinj heqpt⟩

/-- **Math.** **The equality case in polar form: the competitor runs along the
ray** (do Carmo Ch. 3, Prop. 3.6, equality analysis, global stage, polar
form). There is `ρ > 0` (a Gauss ball for `exp_p`) such that every `C¹` polar
competitor `w : [0,1] → B_ρ(0)` with `w(0) = 0` that realizes the radius
comparison with **equality** satisfies, for every `t ∈ [0,1]`,
$$w(t) = \frac{|w(t)|_p}{|w(1)|_p}\,w(1) :$$
the competitor traces the radial segment from `0` to `w(1)` (with monotone
radius), so its image in the manifold is the image of the radial geodesic.
The proof integrates the pointwise stage: past the last time `t_*` at which
the radius vanishes, the normalized lift `w/|w|_p` has vanishing derivative —
its derivative combines `r' = ⟨w,w'⟩_p/r` with the radial velocity
`w' = (⟨w,w'⟩_p/⟨w,w⟩_p)w` — hence is constant; before `t_*` the monotone
radius forces `w = 0`. -/
theorem exists_gauss_equality_ray_ball (g : RiemannianMetric I M) (p : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      (∀ u : E, ‖u‖ < ρ → (u : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      (∀ u : E, ‖u‖ < ρ →
        expMap (I := I) g p (u : TangentSpace I p) ∈ (chartAt H p).source) ∧
      (∀ (w w' : ℝ → E),
        ContinuousOn w (Icc (0 : ℝ) 1) →
        (∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt w (w' t) t) →
        ContinuousOn w' (Icc (0 : ℝ) 1) →
        (∀ t ∈ Icc (0 : ℝ) 1, ‖w t‖ < ρ) →
        w 0 = 0 →
        (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w 1) (w 1))
            - Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w 0) (w 0))
          = ∫ t in (0 : ℝ)..1, Real.sqrt (chartMetricInner (I := I) g p
              (extChartAt I p (expMap (I := I) g p (w t : TangentSpace I p)))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t))
              (fderiv ℝ (fun u : E =>
                extChartAt I p (expMap (I := I) g p (u : TangentSpace I p)))
                (w t) (w' t)))) →
        ∀ t ∈ Icc (0 : ℝ) 1,
          w t = (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w t) (w t))
              / Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w 1) (w 1))) • w 1) := by
  classical
  obtain ⟨ρ, hρ, hdom, hsrc, hkey⟩ := exists_gauss_equality_radial_ball (I := I) g p
  obtain ⟨c, Vc, hc, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  have hgram0 : ∀ z : E,
      ‖z‖ ^ 2 ≤ c * chartMetricInner (I := I) g p (extChartAt I p p) z z :=
    fun z => hgramV _ (mem_of_mem_nhds hVc) z
  have hQnonneg : ∀ z : E,
      0 ≤ chartMetricInner (I := I) g p (extChartAt I p p) z z := fun z =>
    chartMetricInner_self_nonneg_of_mem_target (I := I) g p
      (mem_extChartAt_target p) z
  have hQzero : ∀ z : E,
      chartMetricInner (I := I) g p (extChartAt I p p) z z = 0 → z = 0 := by
    intro z hz
    have h1 := hgram0 z
    rw [hz, mul_zero] at h1
    have h2 : ‖z‖ = 0 := by nlinarith [norm_nonneg z, sq_nonneg ‖z‖]
    exact norm_eq_zero.mp h2
  refine ⟨ρ, hρ, hdom, hsrc, ?_⟩
  intro w w' hw_cont hw hw' hwball hw0 heq
  obtain ⟨hderiv, hrad⟩ :=
    hkey w w' 0 1 one_pos hw_cont hw hw' hwball heq
  set r : ℝ → ℝ := fun t =>
    Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t))
    with hrdef
  have hr_nonneg : ∀ t, 0 ≤ r t := fun t => Real.sqrt_nonneg _
  have hrsq : ∀ t, chartMetricInner (I := I) g p (extChartAt I p p) (w t) (w t)
      = r t ^ 2 := fun t => (Real.sq_sqrt (hQnonneg (w t))).symm
  have hrzero_w : ∀ t, r t = 0 → w t = 0 := by
    intro t ht
    refine hQzero (w t) ?_
    rw [hrsq t, ht]
    norm_num
  -- continuity of the radius
  have hr_cont : ContinuousOn r (Icc (0 : ℝ) 1) := by
    refine Real.continuous_sqrt.comp_continuousOn ?_
    exact continuousOn_chartMetricInner_along (I := I) g p
      continuousOn_const hw_cont hw_cont
      (fun t _ => mem_extChartAt_target p)
  -- monotonicity of the radius: its derivative is a square root
  have hrmono : MonotoneOn r (Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hr_cont ?_ ?_
    · intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      exact Real.sqrt_nonneg _
  have hr0 : r 0 = 0 := by
    rw [hrdef]
    simp only
    rw [hw0, chartMetricInner_zero_left, Real.sqrt_zero]
  rcases eq_or_lt_of_le (hr_nonneg 1) with hr1 | hr1
  · -- degenerate endpoint: the whole lift is squeezed to the origin
    intro t ht
    have hrt : r t = 0 :=
      le_antisymm (hr1 ▸ hrmono ht (right_mem_Icc.mpr zero_le_one) ht.2)
        (hr_nonneg t)
    rw [hrzero_w t hrt, hrzero_w 1 hr1.symm, smul_zero]
  · -- the last vanishing time of the radius
    set S : Set ℝ := Icc (0 : ℝ) 1 ∩ r ⁻¹' {0} with hSdef
    have hS_closed : IsClosed S :=
      hr_cont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
    have hS_ne : S.Nonempty := ⟨0, ⟨le_rfl, zero_le_one⟩, hr0⟩
    have hS_bdd : BddAbove S := ⟨1, fun x hx => hx.1.2⟩
    set tstar : ℝ := sSup S with htstardef
    have htstarS : tstar ∈ S := hS_closed.csSup_mem hS_ne hS_bdd
    have htstar01 : tstar ∈ Icc (0 : ℝ) 1 := htstarS.1
    have hrtstar : r tstar = 0 := htstarS.2
    have htstar1 : tstar < 1 := by
      rcases eq_or_lt_of_le htstar01.2 with h | h
      · exact absurd (h ▸ hrtstar) hr1.ne'
      · exact h
    -- past the last vanishing time the radius is positive
    have hrpos : ∀ t, tstar < t → t ≤ 1 → 0 < r t := by
      intro t htl htu
      rcases eq_or_lt_of_le (hr_nonneg t) with h | h
      · exact absurd (le_csSup hS_bdd
          ⟨⟨htstar01.1.trans htl.le, htu⟩, h.symm⟩) (not_le.mpr htl)
      · exact h
    -- the normalized lift has vanishing derivative past `tstar`
    set eta : ℝ → E := fun t => (r t)⁻¹ • w t with hetadef
    have heta_deriv : ∀ x ∈ Ioo tstar 1, HasDerivAt eta 0 x := by
      intro x hx
      have hx01 : x ∈ Ioo (0 : ℝ) 1 := ⟨htstar01.1.trans_lt hx.1, hx.2⟩
      have hrx : 0 < r x := hrpos x hx.1 hx.2.le
      have hQx : 0 < chartMetricInner (I := I) g p (extChartAt I p p)
          (w x) (w x) := by
        rw [hrsq x]
        positivity
      have hwx0 : w x ≠ 0 := by
        intro h0
        rw [h0, chartMetricInner_zero_left] at hQx
        exact lt_irrefl 0 hQx
      obtain ⟨hnonneg, hradx⟩ := hrad x hx01 hwx0
      -- derivative of the squared radius
      have hQd : HasDerivAt (fun s => chartMetricInner (I := I) g p
          (extChartAt I p p) (w s) (w s))
          (2 * chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x))
          x := by
        have h := hasDerivAt_chartMetricInner_const_base (I := I) g p
          (extChartAt I p p) (hw x hx01) (hw x hx01)
        have hsymm : chartMetricInner (I := I) g p (extChartAt I p p)
            (w' x) (w x)
            = chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x) :=
          chartMetricInner_symm (I := I) g p _ _ _
        rw [hsymm] at h
        convert h using 1
        ring
      have hrd : HasDerivAt r
          (2 * chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x)
            / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w x) (w x)))) x := hQd.sqrt hQx.ne'
      have hrinv : HasDerivAt (fun s => (r s)⁻¹)
          (-(2 * chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w' x)
            / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w x) (w x)))) / r x ^ 2) x := hrd.inv hrx.ne'
      have heta : HasDerivAt eta
          ((r x)⁻¹ • w' x
            + (-(2 * chartMetricInner (I := I) g p (extChartAt I p p)
                (w x) (w' x)
              / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                  (w x) (w x)))) / r x ^ 2) • w x) x :=
        hrinv.smul (hw x hx01)
      -- the derivative vanishes: substitute the radial velocity
      have hscalar : (r x)⁻¹ * (chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w' x)
            / chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w x))
          + (-(2 * chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w' x)
            / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w x) (w x)))) / r x ^ 2) = 0 := by
        rw [hrsq x, Real.sqrt_sq (hr_nonneg x)]
        field_simp
        ring
      have hsub : (r x)⁻¹ • w' x
          = ((r x)⁻¹ * (chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w' x)
            / chartMetricInner (I := I) g p (extChartAt I p p) (w x) (w x)))
            • w x := by
        conv_lhs => rw [hradx]
        rw [smul_smul]
      have hzero : (r x)⁻¹ • w' x
          + (-(2 * chartMetricInner (I := I) g p (extChartAt I p p)
              (w x) (w' x)
            / (2 * Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p)
                (w x) (w x)))) / r x ^ 2) • w x = 0 := by
        rw [hsub, ← add_smul, hscalar, zero_smul]
      rw [hzero] at heta
      exact heta
    -- the normalized lift is constant past `tstar`
    have heta_const : ∀ t, tstar < t → t ≤ 1 → eta t = eta 1 := by
      intro t htl htu
      rcases eq_or_lt_of_le htu with rfl | htu'
      · rfl
      · have hconst := constant_of_has_deriv_right_zero
          (f := eta) (a := t) (b := 1)
          (by
            refine ((hr_cont.mono (Icc_subset_Icc (htstar01.1.trans htl.le)
              le_rfl)).inv₀ ?_).smul
              (hw_cont.mono (Icc_subset_Icc (htstar01.1.trans htl.le) le_rfl))
            intro s hs
            exact (hrpos s (htl.trans_le hs.1) hs.2).ne')
          (fun x hx => (heta_deriv x ⟨htl.trans_le hx.1, hx.2⟩).hasDerivWithinAt)
        exact (hconst 1 (right_mem_Icc.mpr htu)).symm
    -- assemble the ray identity
    intro t ht
    rcases le_or_gt t tstar with htle | htgt
    · -- before the last vanishing time the lift is at the origin
      have hrt : r t = 0 :=
        le_antisymm (hrtstar ▸ hrmono ht htstar01 htle) (hr_nonneg t)
      rw [hrzero_w t hrt, chartMetricInner_zero_left, Real.sqrt_zero, zero_div,
        zero_smul]
    · -- past it, the constancy of the direction gives the ray identity
      have hetat : eta t = eta 1 := heta_const t htgt ht.2
      have hrt : 0 < r t := hrpos t htgt ht.2
      have hwt : w t = r t • eta 1 := by
        rw [← hetat, hetadef]
        simp only
        rw [smul_smul, mul_inv_cancel₀ hrt.ne', one_smul]
      show w t = (r t / r 1) • w 1
      rw [hwt, hetadef]
      simp only
      rw [smul_smul, div_eq_mul_inv]

end Exponential

end Riemannian

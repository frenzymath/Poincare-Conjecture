import PetersenLib.Ch05.ShortGeodesics
import OpenGALib.Riemannian.Exponential.RayODE
import OpenGALib.Riemannian.Geodesic.ChartFlow

/-!
# Petersen Ch. 5, §5.5.2 — `C^∞` regularity of the radial geodesic, and the distance
upper bound

Closing the documented `C^∞`-ODE gap of §5.2 **for the single radial geodesic**
`t ↦ exp_p(t v)` — which is all the metric theory of §5.5 actually needs.  The
vendored do Carmo cone already establishes that the ray is `C¹` with
`Manifold.pathELength = ofReal √(g_p(v,v))` (`exists_pathELength_expMap_ray`) and
that its chart reading solves the coordinate geodesic ODE
(`exists_expMap_ray_ode_ball`).  The only missing regularity is `C^∞`, and it is a
**single-curve** bootstrap, *not* the smooth-dependence-on-initial-conditions
result:

* `contDiffOn_of_hasDerivAt_smoothField` — a differentiable solution `z` of an
  autonomous ODE `z' = Φ(z)` with `Φ` smooth (`C^∞`) on an open set through which
  `z` passes is itself `C^∞`.  Proof: bootstrap `deriv z = Φ ∘ z` up the
  `contDiffOn_succ_iff_deriv_of_isOpen` ladder — each order gains one from the
  previous via the smooth field.

Applied to `z(t) = (φ_p(exp_p(tv)), (dφ_p exp_p)_{tv}(v))` — position and chart
velocity of the ray — which solves `z' = geodesicSprayCoord g p (z.1) (z.2)` with
the coordinate spray `C^∞` (`contDiffOn_geodesicSprayCoord_prod`), this yields:

* `exists_contMDiffOn_expMap_ray` — near `p` the radial geodesic is `C^∞` on
  `[0, 1]`, hence a Petersen piecewise-`C^∞` competitor.

With `pathELength_eq_ofReal_curveLength` this turns the vendored `pathELength`
computation into `curveLength (t ↦ exp_p(tv)) = √(g_p(v,v))`, giving the distance
upper bound and, combined with the lower bound `expMap_riemannianDistance_ge`,
Petersen Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`):
`d(p, exp_p v) = |v|_g`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open Riemannian Riemannian.Geodesic Riemannian.Exponential

/-- **Math.** **ODE regularity bootstrap.**  Let `Φ : F → F` be `C^∞` on an open
set `Ω`, and let `z : ℝ → F` be a solution of the autonomous ODE `z'(t) = Φ(z t)`
on an open set `J ⊆ ℝ` whose trajectory stays in `Ω`.  Then `z` is `C^∞` on `J`.

This is the single-trajectory smoothness of an ODE with smooth right-hand side —
obtained by bootstrapping `deriv z = Φ ∘ z` up the smoothness ladder, gaining one
order of differentiability at each step — and is *independent* of the (harder)
smooth dependence of the flow on initial conditions. -/
theorem contDiffOn_of_hasDerivAt_smoothField
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : F → F} {Ω : Set F} (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    {z : ℝ → F} {J : Set ℝ} (hJ : IsOpen J)
    (hz : ∀ t ∈ J, HasDerivAt z (Φ (z t)) t) (hmaps : ∀ t ∈ J, z t ∈ Ω) :
    ContDiffOn ℝ ∞ z J := by
  rw [contDiffOn_infty]
  have hmapsto : MapsTo z J Ω := hmaps
  intro n
  induction n with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun t ht => (hz t ht).continuousAt.continuousWithinAt
  | succ k ih =>
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen hJ]
    refine ⟨fun t ht => (hz t ht).differentiableAt.differentiableWithinAt, ?_, ?_⟩
    · intro hk
      exact absurd hk (by simp)
    · have hcomp : ContDiffOn ℝ k (fun t => Φ (z t)) J :=
        (hΦ.of_le (by exact_mod_cast le_top)).comp ih hmapsto
      exact hcomp.congr (fun t ht => (hz t ht).deriv)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space M] [ConnectedSpace M]

/-- **Math.** **The radial geodesic is `C^∞` on `[0, 1]`** (closing the §5.2
`C^∞`-ODE gap for the single ray, all that §5.5's metric theory needs).  There is
`ε > 0` such that for every `v` with `‖v‖ < ε` the radial geodesic
`t ↦ exp_p(t v)` is `C^∞` on `[0, 1]`, hence a Petersen piecewise-`C^∞` competitor
curve.

The chart position `y(t) = φ_p(exp_p(tv))` and chart velocity
`V(t) = (dφ_p exp_p)_{tv}(v)` assemble into `z = (y, V) : ℝ → E × E`, which solves
the first-order geodesic-spray ODE `z' = geodesicSprayCoord g p (z.1) (z.2)`
(`exists_expMap_ray_ode_ball`).  The coordinate spray is `C^∞`
(`contDiffOn_geodesicSprayCoord_prod`), so the single-trajectory bootstrap
`contDiffOn_of_hasDerivAt_smoothField` upgrades the `C¹` ray to `C^∞`; composing
with the smooth inverse chart lifts it to the manifold. -/
theorem exists_contMDiffOn_expMap_ray (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : E, ‖v‖ < ε →
        ContMDiffOn 𝓘(ℝ, ℝ) I ∞
          (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p))
          (Icc 0 1) := by
  obtain ⟨ρ, b, hρ, hb, hadm, hC2, -, hODE⟩ :=
    Exponential.exists_expMap_ray_ode_ball (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (Exponential.expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  refine ⟨ρ / b, by positivity, ?_⟩
  intro v hv
  simp only [expMap_eq]
  have hvρ : ‖v‖ < ρ := hv.trans (div_lt_self hρ hb)
  -- scaled vectors on `|t| < b` stay in the `C²` ball
  have htv : ∀ t : ℝ, |t| < b → ‖t • v‖ < ρ := by
    intro t ht
    calc ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ < b * (ρ / b) := mul_lt_mul'' ht hv (abs_nonneg t) (norm_nonneg v)
      _ = ρ := by field_simp
  have hΦsmooth : ContDiffOn ℝ ∞
      (fun ζ : E × E => geodesicSprayCoord (I := I) g p ζ.1 ζ.2)
      ((extChartAt I p).target ×ˢ (univ : Set E)) :=
    contDiffOn_geodesicSprayCoord_prod (I := I) g p
  -- the phase-space trajectory `t ↦ (chart position, chart velocity)` solves the spray ODE
  have hz_deriv : ∀ t ∈ Ioo (-b) b,
      HasDerivAt (fun s : ℝ => (f (s • v), fderiv ℝ f (s • v) v))
        (geodesicSprayCoord (I := I) g p (f (t • v)) (fderiv ℝ f (t • v) v)) t := by
    intro t ht
    have ht' : |t| < b := abs_lt.mpr ⟨ht.1, ht.2⟩
    have htvρ : ‖t • v‖ < ρ := htv t ht'
    have hf_at : HasFDerivAt f (fderiv ℝ f (t • v)) (t • v) :=
      ((hC2.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr htvρ))).differentiableAt
        (by norm_num)).hasFDerivAt
    have hray : HasDerivAt (fun s : ℝ => s • v) v t := by
      simpa using (hasDerivAt_id t).smul_const v
    have hy : HasDerivAt (fun s : ℝ => f (s • v)) (fderiv ℝ f (t • v) v) t := by
      simpa [Function.comp_def] using hf_at.comp_hasDerivAt t hray
    rw [geodesicSprayCoord_def]
    exact hy.prodMk (hODE v t hvρ ht' htvρ)
  have hz_maps : ∀ t ∈ Ioo (-b) b,
      (f (t • v), fderiv ℝ f (t • v) v) ∈ (extChartAt I p).target ×ˢ (univ : Set E) := by
    intro t ht
    have ht' : |t| < b := abs_lt.mpr ⟨ht.1, ht.2⟩
    refine mem_prod.mpr ⟨?_, mem_univ _⟩
    show f (t • v) ∈ (extChartAt I p).target
    simp only [hfdef]
    refine (extChartAt I p).map_source ?_
    rw [extChartAt_source]
    exact (hadm v t hvρ ht').2
  have hz_smooth : ContDiffOn ℝ ∞
      (fun s : ℝ => (f (s • v), fderiv ℝ f (s • v) v)) (Ioo (-b) b) :=
    contDiffOn_of_hasDerivAt_smoothField hΦsmooth isOpen_Ioo hz_deriv hz_maps
  have hy_smooth : ContDiffOn ℝ ∞ (fun s : ℝ => f (s • v)) (Ioo (-b) b) := hz_smooth.fst
  -- lift the chart position to the manifold through the smooth inverse chart
  have hyM : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => f (s • v)) (Ioo (-b) b) :=
    contMDiffOn_iff_contDiffOn.mpr hy_smooth
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (extChartAt I p).target :=
    contMDiffOn_extChartAt_symm p
  have hmapsY : MapsTo (fun s : ℝ => f (s • v)) (Ioo (-b) b) (extChartAt I p).target :=
    fun t ht => (mem_prod.mp (hz_maps t ht)).1
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I ∞
      (fun t : ℝ => Exponential.expMap (I := I) g p ((t • v : E) : TangentSpace I p))
      (Ioo (-b) b) := by
    refine (hsymm.comp hyM hmapsY).congr ?_
    intro t ht
    have ht' : |t| < b := abs_lt.mpr ⟨ht.1, ht.2⟩
    show Exponential.expMap (I := I) g p ((t • v : E) : TangentSpace I p)
        = (extChartAt I p).symm (f (t • v))
    simp only [hfdef]
    exact ((extChartAt I p).left_inv (by
      rw [extChartAt_source]; exact (hadm v t hvρ ht').2)).symm
  exact hgamma.mono (Icc_subset_Ioo (by linarith) hb)

/-- **Math.** **The radial geodesic realizes the distance from above.**  There is
`ε > 0` such that for every `v` with `‖v‖ < ε`,
`d(p, exp_p v) ≤ |v|_g = √(g_p(v, v))`: the radial geodesic `t ↦ exp_p(tv)` is a
Petersen competitor of length exactly `|v|_g`.  Its `C^∞` regularity
(`exists_contMDiffOn_expMap_ray`) makes it an admissible curve, and its Petersen
length equals the vendored `pathELength = ofReal |v|_g` through the length bridge
`pathELength_eq_ofReal_curveLength`. -/
theorem exists_curveLength_expMap_ray (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : E, ‖v‖ < ε →
        curveLength (I := I) g
            (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 0 1
          = Real.sqrt (g.metricInner p v v) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ε₁, hε₁, hsmooth⟩ := exists_contMDiffOn_expMap_ray (I := I) g p
  obtain ⟨ε₂, hε₂, -, -, hlen⟩ := Exponential.exists_pathELength_expMap_ray (I := I) g p
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun v hv => ?_⟩
  set γ : ℝ → M := fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p) with hγdef
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) := hsmooth v (hv.trans_le (min_le_left _ _))
  obtain ⟨-, hpath⟩ := hlen v (hv.trans_le (min_le_right _ _))
  simp only [← expMap_eq] at hpath
  -- the Petersen length equals the vendored `pathELength`, computed to `√⟨v, v⟩_p`
  have hbridge := pathELength_eq_ofReal_curveLength (I := I) g zero_le_one hsm
  have hcl : curveLength (I := I) g γ 0 1
      = Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v) := by
    have heq : ENNReal.ofReal (curveLength (I := I) g γ 0 1)
        = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p p) v v)) := by
      rw [← hbridge, hpath]
    have := congrArg ENNReal.toReal heq
    rwa [ENNReal.toReal_ofReal (curveLength_nonneg (I := I) g γ zero_le_one),
      ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at this
  -- the chart-Gram pairing at the origin is the intrinsic inner product
  have hchart : chartMetricInner (I := I) g p (extChartAt I p p) v v = g.metricInner p v v := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) v v,
      trivializationAt_symm_self]
    -- the shared lemma yields `Riemannian.RiemannianMetric.metricInner`; Petersen's
    -- `metricInner` is the same projection `g.inner`.
    simp only [Riemannian.RiemannianMetric.metricInner_apply,
      PetersenLib.RiemannianMetric.metricInner_apply]
  rw [hcl, hchart]

/-- **Math.** **The radial geodesic realizes the distance from above.**  There is
`ε > 0` such that for every `v` with `‖v‖ < ε`,
`d(p, exp_p v) ≤ |v|_g = √(g_p(v, v))`: the radial geodesic `t ↦ exp_p(tv)` is a
Petersen competitor of length exactly `|v|_g`
(`exists_curveLength_expMap_ray`). -/
theorem exists_expMap_riemannianDistance_le (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : E, ‖v‖ < ε →
        riemannianDistance (I := I) g p (expMap (I := I) g p (v : TangentSpace I p))
          ≤ Real.sqrt (g.metricInner p v v) := by
  obtain ⟨ε₁, hε₁, hsmooth⟩ := exists_contMDiffOn_expMap_ray (I := I) g p
  obtain ⟨ε₂, hε₂, hcl⟩ := exists_curveLength_expMap_ray (I := I) g p
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun v hv => ?_⟩
  set γ : ℝ → M := fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p) with hγdef
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) := hsmooth v (hv.trans_le (min_le_left _ _))
  have h0 : γ 0 = p := by
    show expMap (I := I) g p (((0 : ℝ) • v : E) : TangentSpace I p) = p
    rw [zero_smul]; exact expMap_zero (I := I) g p
  have h1 : γ 1 = expMap (I := I) g p (v : TangentSpace I p) := by
    show expMap (I := I) g p (((1 : ℝ) • v : E) : TangentSpace I p) = _
    rw [one_smul]
  calc riemannianDistance (I := I) g p (expMap (I := I) g p (v : TangentSpace I p))
      ≤ curveLength (I := I) g γ 0 1 :=
        riemannianDistance_le_curveLength (I := I) g
          (ContMDiffOn.isPiecewiseSmoothCurve zero_le_one hsm) h0 h1
    _ = Real.sqrt (g.metricInner p v v) := hcl v (hv.trans_le (min_le_right _ _))

/-- **Math.** Petersen Ch. 5, **Theorem 5.5.4** (`thm:pet-ch5-short-geodesics-segments`):
**short geodesics are segments.**  There is `ε > 0` such that the model ball
`B_ε(0) ⊂ T_pM` lies in the exponential domain and, for every `v` with `‖v‖ < ε`,

`d(p, exp_p v) = |v|_g = √(g_p(v, v))` :

the radial geodesic `t ↦ exp_p(tv)` realizes the Riemannian distance, so it is a
segment.  The lower bound is `expMap_riemannianDistance_ge` (no curve is shorter
than the radial geodesic); the upper bound is `exists_expMap_riemannianDistance_le`
(the radial geodesic, now known `C^∞`, is a competitor of exactly this length). -/
theorem expMap_riemannianDistance_eq (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ∀ v : E, ‖v‖ < ε →
        riemannianDistance (I := I) g p (expMap (I := I) g p (v : TangentSpace I p))
          = Real.sqrt (g.metricInner p v v) := by
  obtain ⟨ε₁, hε₁, hdom, hge⟩ := expMap_riemannianDistance_ge (I := I) g p
  obtain ⟨ε₂, hε₂, hle⟩ := exists_expMap_riemannianDistance_le (I := I) g p
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun w hw => hdom w (hw.trans_le (min_le_left _ _)),
    fun v hv => le_antisymm (hle v (hv.trans_le (min_le_right _ _)))
      (hge v (hv.trans_le (min_le_left _ _)))⟩

/-- **Math.** Petersen Ch. 5, **Theorem 5.5.4**, existence half
(`thm:pet-ch5-short-geodesics-segments`): **short geodesics are segments.**  There
is `ε > 0` such that for every `v` with `‖v‖ < ε` the radial geodesic
`γ(t) = exp_p(tv)`, `t ∈ [0, 1]`, is a Petersen **segment** from `p` to `exp_p v`:
it is piecewise-`C^∞`, its length `|v|_g` equals `d(p, exp_p v)`, and it is
parametrized proportionally to arc length with speed `|v|_g`
(`L(γ)|_0^t = |v|_g · t`).

The constant-speed clause is the homogeneity `exp_p(tsv) = exp_p(s·(tv))`: the
restriction to `[0, t]` is, after the affine reparametrization `s ↦ ts`, the radial
geodesic of `tv`, whose length is `|tv|_g = t·|v|_g`
(`exists_curveLength_expMap_ray` + `curveLength_comp_mul_add`).  Uniqueness of the
segment and `exp_p(B_ε) = B(p, ε)` (the remaining clauses of Petersen's Thm 5.5.4)
are not proved here. -/
theorem exists_expMap_isSegment (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ v : E, ‖v‖ < ε →
        IsSegment (I := I) g
          (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) 0 1 := by
  obtain ⟨ε₁, hε₁, hsmooth⟩ := exists_contMDiffOn_expMap_ray (I := I) g p
  obtain ⟨ε₂, hε₂, hcl⟩ := exists_curveLength_expMap_ray (I := I) g p
  obtain ⟨ε₃, hε₃, -, heq⟩ := expMap_riemannianDistance_eq (I := I) g p
  refine ⟨min ε₁ (min ε₂ ε₃), lt_min hε₁ (lt_min hε₂ hε₃), fun v hv => ?_⟩
  have hv1 : ‖v‖ < ε₁ := hv.trans_le (min_le_left _ _)
  have hv2 : ‖v‖ < ε₂ := hv.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hv3 : ‖v‖ < ε₃ := hv.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set γ : ℝ → M := fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p) with hγdef
  have hsm : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ (Icc 0 1) := hsmooth v hv1
  have h0 : γ 0 = p := by
    show expMap (I := I) g p (((0 : ℝ) • v : E) : TangentSpace I p) = p
    rw [zero_smul]; exact expMap_zero (I := I) g p
  have h1 : γ 1 = expMap (I := I) g p (v : TangentSpace I p) := by
    show expMap (I := I) g p (((1 : ℝ) • v : E) : TangentSpace I p) = _
    rw [one_smul]
  refine ⟨ContMDiffOn.isPiecewiseSmoothCurve zero_le_one hsm, ?_, ?_⟩
  · -- the length realizes the distance between the endpoints
    rw [h0, h1, heq v hv3]
    exact hcl v hv2
  · -- proportional-to-arclength parametrization with speed `|v|_g`
    refine ⟨Real.sqrt (g.metricInner p v v), Real.sqrt_nonneg _, fun t ht => ?_⟩
    have htnn : (0 : ℝ) ≤ t := ht.1
    have htvε : ‖t • v‖ < ε₂ := by
      calc ‖t • v‖ = |t| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖v‖ := by
            gcongr; rw [abs_le]; exact ⟨by linarith [ht.1], ht.2⟩
        _ < ε₂ := by rw [one_mul]; exact hv2
    -- reparametrize `[0, t]` to `[0, 1]` as the radial geodesic of `t • v`
    have hstep := curveLength_comp_mul_add (I := I) g γ htnn 0 0 1
    simp only [mul_zero, mul_one, add_zero] at hstep
    have hηeq : (fun s : ℝ => γ (t * s))
        = fun s : ℝ => expMap (I := I) g p ((s • (t • v) : E) : TangentSpace I p) := by
      funext s
      show expMap (I := I) g p (((t * s) • v : E) : TangentSpace I p)
          = expMap (I := I) g p ((s • (t • v) : E) : TangentSpace I p)
      rw [smul_smul, mul_comm s t]
    rw [← hstep, hηeq, hcl (t • v) htvε, sub_zero]
    have hmi : g.metricInner p ((t • v : E) : TangentSpace I p) ((t • v : E) : TangentSpace I p)
        = t ^ 2 * g.metricInner p v v :=
      g.metricInner_smul_left p t v (t • v) ▸ g.metricInner_smul_right p t v v ▸ by ring
    rw [hmi, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq htnn, mul_comm]

end PetersenLib

end

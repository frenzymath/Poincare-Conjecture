import PetersenLib.Ch05.FixedPointTotallyGeodesic
import PetersenLib.Ch05.ExponentialMap

/-!
# Petersen Ch. 5, §5.6 — the fixed-point set is *locally* an exponential image of a subspace

This file supplies the **submanifold half** of Prop. 5.6.5
(`prop:pet-ch5-fixed-point-totally-geodesic`), the half left open by
`Ch05/FixedPointTotallyGeodesic.lean` (which proves the totally-geodesic half,
`fixedPointSetComponent_totallyGeodesic`).

Petersen's second paragraph reads: *let `ε > 0` be such that
`exp_p : B(0, ε) → B(p, ε)` is a diffeomorphism; if `q ∈ Fix(S) ∩ B(p, ε)` the
unique segment `c` from `p` to `q` has both endpoints fixed by every `F ∈ S`, so
`F ∘ c` is a segment from `p` to `q` of the same length inside `B(p, ε)`, hence
`F ∘ c = c` by uniqueness, hence `c ⊆ Fix(S)`; therefore
`exp_p : V_p ∩ B(0, ε) → Fix(S) ∩ B(p, ε)` is a bijection, exhibiting `Fix(S)`
near `p` as the image of a linear subspace.*

The main results:

* `exists_isometry_fixedPoint_expMap_iff` — the two-way analytic core.  There is
  an intrinsic radius `ε > 0` at `p` such that for **every** Riemannian isometry
  `F` fixing `p` and every `v` with `|v|_g < ε`,
  `F (exp_p v) = exp_p v ↔ DF_p v = v`.
  The `←` direction is `exists_isometry_fix_expMap`; the new content is `→`,
  proved exactly as Petersen does: `F ∘ (radial ray of v)` is a segment from `p`
  to `exp_p v`, so normal-ball rigidity (Thm. 5.5.4, `expMap_isSegment_unique`)
  identifies it with the radial ray of `v` itself, and differentiating at `t = 0`
  gives `DF_p v = v`.

* `exists_expMap_bijOn_fixedPointSet` — Petersen's bijection.  There is `ε > 0`
  with
  `exp_p : {v | |v|_g < ε} ∩ V_p  ≃  Fix(S) ∩ B(p, ε)`
  a bijection (`Set.BijOn`), where `V_p = fixedTangentSubspace S p` is the fixed
  tangent subspace.  Injectivity comes from `expMap_localDiffeomorphism`
  (Prop. 5.5.1 (1)).

* `exists_expMap_bijOn_fixedPointSetComponent` — the same bijection with the
  target sharpened to the **connected component** of `Fix(S)` through `p`,
  intersected with `B(p, ε)`: every point of `Fix(S) ∩ B(p, ε)` is joined to `p`
  by a radial ray inside `Fix(S)`, so it lies in that component.

## What this does and does not claim

These statements exhibit the fixed-point set near `p` as the `exp_p`-image of a
linear subspace of `T_pM`, which is the geometric content Petersen extracts.
They do **not** register `Fix(S)` (or its components) as a term of a Lean
manifold/submanifold class: turning the bijection into a chart requires knowing
that `exp_p` restricted to `V_p ∩ B(0, ε)` is a `C^∞` diffeomorphism onto its
image with the smooth structure of the ambient `M`, which is not asserted here.

Everything is quantified over the **intrinsic** ball `{v | |v|_g < ε}` and the
Riemannian ball `metricBall g p ε`, never over `expDomain`/`injectivityRadius`,
so the chart artifact of `rem:pet-ch5-injectivity-radius-chart-artifact` does not
touch these statements.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

namespace PetersenLib

open PetersenLib.Geodesic PetersenLib.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ## The two-way core -/

/-- **Math.** Petersen Ch. 5, Prop. 5.6.5, second paragraph (the converse half of
`exists_isometry_fix_expMap`).  At every `p ∈ M` there is an intrinsic radius
`ε > 0` such that, for every Riemannian isometry `F` with `F p = p` and every
`v ∈ T_pM` with `|v|_g < ε`:

`F (exp_p v) = exp_p v  ↔  DF_p v = v`.

The direction `←` is `exists_isometry_fix_expMap`.  For `→`: the radial ray
`c : t ↦ exp_p(t v)` is a segment from `p` to `exp_p v` (Thm. 5.5.4,
`expMap_isSegment_unique`), `F` preserves the Riemannian distance
(Prop. 5.6.1 (3)–(4)) and hence carries `c` to a segment `F ∘ c` from
`F p = p` to `F (exp_p v) = exp_p v`; normal-ball rigidity then forces
`F ∘ c = c` on `[0, 1]`, and differentiating at `t = 0` gives
`DF_p v = velocity c 0 = v`. -/
theorem exists_isometry_fixedPoint_expMap_iff [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ F : M → M, IsRiemannianIsometry g g F → F p = p →
        ∀ v : E, Real.sqrt (g.metricInner p v v) < ε →
          (F (expMap (I := I) g p (v : TangentSpace I p))
              = expMap (I := I) g p (v : TangentSpace I p)
            ↔ mfderiv I I F p (v : TangentSpace I p) = (v : TangentSpace I p)) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ε₁, hε₁, -, hfix⟩ := exists_isometry_fix_expMap (I := I) g hg p
  obtain ⟨ε₀, hε₀, -, -, huniq⟩ := expMap_isSegment_unique (I := I) g hg p
  obtain ⟨ρ, b, hρ, hb, -, hray⟩ := exists_isGeodesicOn_expMap_ray (I := I) g p
  obtain ⟨cc, V, hcc, hVmem, -, hcoercV⟩ := exists_sq_norm_le_chartMetricInner (I := I) g p
  have hchart : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w = g.metricInner p w w := by
    intro w
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self]
  have hcoercPole : ∀ w : E, ‖w‖ ≤ Real.sqrt cc * Real.sqrt (g.metricInner p w w) := by
    intro w
    have h1 := hcoercV (extChartAt I p p) (mem_of_mem_nhds hVmem) w
    rw [hchart w] at h1
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (cc * g.metricInner p w w) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt cc * Real.sqrt (g.metricInner p w w) := Real.sqrt_mul hcc.le _
  set ε : ℝ := min ε₁ (min ε₀ (ρ / (Real.sqrt cc + 1))) with hεdef
  have hε : 0 < ε := lt_min hε₁ (lt_min hε₀ (by positivity))
  have hεε₁ : ε ≤ ε₁ := min_le_left _ _
  have hεε₀ : ε ≤ ε₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcoerc : ∀ v : E, Real.sqrt (g.metricInner p v v) < ε → ‖v‖ < ρ := by
    intro v hv
    have h1 : Real.sqrt (g.metricInner p v v) < ρ / (Real.sqrt cc + 1) :=
      hv.trans_le (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [Real.sqrt_nonneg (g.metricInner p v v), Real.sqrt_nonneg cc, hcoercPole v]
  refine ⟨ε, hε, fun F hFiso hFp v hv => ⟨fun hFe => ?_, fun hDF => ?_⟩⟩
  swap
  · exact hfix F hFiso hFp v (lt_of_lt_of_le hv hεε₁) hDF
  -- the new direction: `F` fixes the endpoint ⟹ `DF_p` fixes the initial velocity
  set c : ℝ → M := fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p) with hc
  have hvε₀ : Real.sqrt (g.metricInner p v v) < ε₀ := lt_of_lt_of_le hv hεε₀
  have hvρ : ‖v‖ < ρ := hcoerc v hv
  obtain ⟨hcseg, hcuniq⟩ := huniq v hvε₀
  have hFloc : IsLocalRiemannianIsometry g g F := hFiso.isLocalRiemannianIsometry
  obtain ⟨G, hGloc, hGF⟩ := hFiso.exists_leftInverse_isLocalRiemannianIsometry
  have hdistpres : ∀ q q' : M, riemannianDistance (I := I) g (F q) (F q')
      = riemannianDistance (I := I) g q q' :=
    fun q q' => localIsometry_distancePreserving hFloc hGloc hGF q q'
  have hc0 : c 0 = p := by
    rw [hc]; simp only [zero_smul]; exact expMap_zero (I := I) g p
  have hc1 : c 1 = expMap (I := I) g p (v : TangentSpace I p) := by
    rw [hc]; simp only [one_smul]
  have hFcseg : IsSegment (I := I) g (F ∘ c) 0 1 := by
    obtain ⟨hpw, hlen, k, hk0, hk⟩ := hcseg
    refine ⟨isPiecewiseSmoothCurve_comp hFloc.contMDiff hpw, ?_, k, hk0, ?_⟩
    · rw [localIsometry_curveLength_piecewise hFloc hpw, hlen]
      simp only [Function.comp_apply]
      exact (hdistpres _ _).symm
    · intro t ht
      rw [localIsometry_curveLength_piecewise hFloc (hpw.mono le_rfl ht.1 ht.2)]
      exact hk t ht
  have hFc0 : (F ∘ c) 0 = p := by simp [hc0, hFp]
  have hFc1 : (F ∘ c) 1 = expMap (I := I) g p (v : TangentSpace I p) := by
    simp only [Function.comp_apply, hc1, hFe]
  have hkey : ∀ t ∈ Icc (0 : ℝ) 1,
      (F ∘ c) t = expMap (I := I) g p ((t • v : E) : TangentSpace I p) :=
    hcuniq (F ∘ c) hFcseg hFc0 hFc1
  -- differentiate at `t = 0`
  have hcderiv : HasDerivAt
      (fun t : ℝ => extChartAt I p (expMap (I := I) g p ((t • v : E) : TangentSpace I p)))
      v 0 := (hray v hvρ).2.1
  have hcmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0 := by
    rw [mdifferentiableAt_iff]
    constructor
    · have hcont := (hray v hvρ).2.2.1
      have hopen : IsOpen (Ioo (-b) b) := isOpen_Ioo
      have h0 : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, by linarith⟩
      exact (hcont.continuousAt (hopen.mem_nhds h0))
    · have hd : DifferentiableAt ℝ
          (fun t : ℝ => extChartAt I p
            (expMap (I := I) g p ((t • v : E) : TangentSpace I p))) 0 :=
        hcderiv.differentiableAt
      have hwrite : writtenInExtChartAt 𝓘(ℝ, ℝ) I 0 c
          = Geodesic.chartLocalCurve (I := I) c 0 := by
        funext s; simp [writtenInExtChartAt, Geodesic.chartLocalCurve]
      have hclc : Geodesic.chartLocalCurve (I := I) c 0
          = fun t : ℝ => extChartAt I p
              (expMap (I := I) g p ((t • v : E) : TangentSpace I p)) := by
        funext s; rw [Geodesic.chartLocalCurve_def, hc0]
      rw [hwrite, hclc]
      simpa [ModelWithCorners.range_eq_univ] using hd.differentiableWithinAt
  have hvel_c : velocity (I := I) c 0 = v := by
    have h1 := hasDerivAt_chartLocalCurve (I := I) hcmdiff
    have h2 : Geodesic.chartLocalCurve (I := I) c 0
        = fun t : ℝ => extChartAt I p
            (expMap (I := I) g p ((t • v : E) : TangentSpace I p)) := by
      funext s; rw [Geodesic.chartLocalCurve_def, hc0]
    rw [h2] at h1
    exact h1.unique hcderiv
  have hFcmdiff : MDifferentiableAt 𝓘(ℝ, ℝ) I (F ∘ c) 0 :=
    (hFloc.mdifferentiableAt (c 0)).comp 0 hcmdiff
  have hvel_Fc : velocity (I := I) (F ∘ c) 0 = mfderiv I I F p (v : TangentSpace I p) := by
    rw [velocity_comp 0 (hFloc.mdifferentiableAt (c 0)) hcmdiff, hvel_c, hc0]
  have hL : HasDerivAt (fun s : ℝ => extChartAt I p (F (c s)))
      (mfderiv I I F p (v : TangentSpace I p)) 0 := by
    have h1 := hasDerivAt_chartLocalCurve (I := I) hFcmdiff
    rw [hvel_Fc] at h1
    have h2 : Geodesic.chartLocalCurve (I := I) (F ∘ c) 0
        = fun s : ℝ => extChartAt I p (F (c s)) := by
      funext s
      rw [Geodesic.chartLocalCurve_def]
      simp only [Function.comp_apply, hc0, hFp]
    rwa [h2] at h1
  have hcongr : ∀ s ∈ Icc (0 : ℝ) 1, (fun s : ℝ => extChartAt I p (F (c s))) s
      = (fun t : ℝ => extChartAt I p
          (expMap (I := I) g p ((t • v : E) : TangentSpace I p))) s := by
    intro s hs
    simp only []
    rw [show F (c s) = expMap (I := I) g p ((s • v : E) : TangentSpace I p) from hkey s hs]
  have hLw : HasDerivWithinAt (fun s : ℝ => extChartAt I p (F (c s)))
      (mfderiv I I F p (v : TangentSpace I p)) (Icc 0 1) 0 := hL.hasDerivWithinAt
  have hRw : HasDerivWithinAt (fun s : ℝ => extChartAt I p (F (c s))) v (Icc 0 1) 0 :=
    (hcderiv.hasDerivWithinAt).congr hcongr (hcongr 0 (by norm_num))
  have hU : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
    uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) 0 (by norm_num)
  exact hU.eq_deriv _ hLw hRw

/-! ## Petersen's bijection -/

/-- **Math.** Petersen Ch. 5, Prop. 5.6.5 — the **submanifold half**.  Let
`S ⊂ Iso(M, g)` and let `p ∈ Fix(S)`.  There is an intrinsic radius `ε > 0` such
that `exp_p` restricts to a **bijection**

`{v ∈ T_pM ∣ |v|_g < ε} ∩ V_p  →  Fix(S) ∩ B(p, ε)`,

where `V_p = fixedTangentSubspace S p` is the subspace of `T_pM` fixed by every
`DF_p`, `F ∈ S`.  This exhibits `Fix(S)` near `p` as the `exp_p`-image of a
linear subspace of `T_pM` — the statement identified in the blueprint as the
missing half of Prop. 5.6.5.

*Maps into*: if `v ∈ V_p` is short, every `F ∈ S` fixes `p` and `v`, hence fixes
`exp_p v` (`exists_isometry_fixedPoint_expMap_iff`, `←`); and `exp_p v` lies in
`B(p, ε)` since `exp_p` carries the intrinsic ball onto the metric ball
(Thm. 5.5.4).

*Onto*: any `q ∈ Fix(S) ∩ B(p, ε)` is `q = exp_p v` for some short `v`, and each
`F ∈ S` fixes `q`, so `DF_p v = v` (`exists_isometry_fixedPoint_expMap_iff`, `→`);
that is, `v ∈ V_p`.

*Injective*: `exp_p` is injective on a normal ball (Prop. 5.5.1 (1),
`expMap_localDiffeomorphism`), and `ε` is chosen small enough — via the chart
Gram bound `‖v‖ ≤ √c · |v|_g` — that the intrinsic `ε`-ball sits inside it. -/
theorem exists_expMap_bijOn_fixedPointSet [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (S : Set (M → M)) (hS : ∀ F ∈ S, IsRiemannianIsometry g g F)
    (p : M) (hp : p ∈ fixedPointSet S) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ ≤ ε →
      Set.BijOn (fun v : E => expMap (I := I) g p (v : TangentSpace I p))
        {v : E | Real.sqrt (g.metricInner p v v) < δ ∧
          (v : TangentSpace I p) ∈ fixedTangentSubspace (I := I) S p}
        (fixedPointSet S ∩ metricBall (I := I) g p δ) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ε₂, hε₂, hiff⟩ := exists_isometry_fixedPoint_expMap_iff (I := I) g hg p
  obtain ⟨ε₀, hε₀, -, hball, -⟩ := expMap_isSegment_unique (I := I) g hg p
  obtain ⟨ρ, hρ, -, hinj, -, -⟩ := expMap_localDiffeomorphism (I := I) g p
  obtain ⟨cc, V, hcc, hVmem, -, hcoercV⟩ := exists_sq_norm_le_chartMetricInner (I := I) g p
  have hchart : ∀ w : E,
      chartMetricInner (I := I) g p (extChartAt I p p) w w = g.metricInner p w w := by
    intro w
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self]
  have hcoercPole : ∀ w : E, ‖w‖ ≤ Real.sqrt cc * Real.sqrt (g.metricInner p w w) := by
    intro w
    have h1 := hcoercV (extChartAt I p p) (mem_of_mem_nhds hVmem) w
    rw [hchart w] at h1
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := (Real.sqrt_sq (norm_nonneg w)).symm
      _ ≤ Real.sqrt (cc * g.metricInner p w w) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt cc * Real.sqrt (g.metricInner p w w) := Real.sqrt_mul hcc.le _
  set ε : ℝ := min ε₂ (min ε₀ (ρ / (Real.sqrt cc + 1))) with hεdef
  have hε : 0 < ε := lt_min hε₂ (lt_min hε₀ (by positivity))
  have hεε₂ : ε ≤ ε₂ := min_le_left _ _
  have hεε₀ : ε ≤ ε₀ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hcoerc : ∀ v : E, Real.sqrt (g.metricInner p v v) < ε → ‖v‖ < ρ := by
    intro v hv
    have h1 : Real.sqrt (g.metricInner p v v) < ρ / (Real.sqrt cc + 1) :=
      hv.trans_le (le_trans (min_le_right _ _) (min_le_right _ _))
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [Real.sqrt_nonneg (g.metricInner p v v), Real.sqrt_nonneg cc, hcoercPole v]
  refine ⟨ε, hε, fun δ hδ hδε => ⟨?_, ?_, ?_⟩⟩
  · -- maps into
    rintro v ⟨hv, hvV⟩
    have hvε : Real.sqrt (g.metricInner p v v) < ε := lt_of_lt_of_le hv hδε
    refine ⟨fun F hF => ?_, ?_⟩
    · exact (hiff F (hS F hF) (hp F hF) v (lt_of_lt_of_le hvε hεε₂)).2 (hvV F hF)
    · rw [← hball δ hδ (le_trans hδε hεε₀)]; exact ⟨v, hv, rfl⟩
  · -- injective
    intro v hv w hw hvw
    exact hinj (mem_ball_zero_iff.2 (hcoerc v (lt_of_lt_of_le hv.1 hδε)))
      (mem_ball_zero_iff.2 (hcoerc w (lt_of_lt_of_le hw.1 hδε))) hvw
  · -- onto
    rintro q ⟨hqFix, hqball⟩
    rw [← hball δ hδ (le_trans hδε hεε₀)] at hqball
    obtain ⟨v, hv, rfl⟩ := hqball
    refine ⟨v, ⟨hv, fun F hF => ?_⟩, rfl⟩
    exact (hiff F (hS F hF) (hp F hF) v
      (lt_of_lt_of_le (lt_of_lt_of_le hv hδε) hεε₂)).1 (hqFix F hF)

/-- **Math.** Petersen Ch. 5, Prop. 5.6.5, with the target of the bijection
sharpened from `Fix(S) ∩ B(p, ε)` to `C ∩ B(p, ε)`, where `C` is the connected
component of `Fix(S)` through `p`.  Indeed the two sets coincide: every point of
`Fix(S) ∩ B(p, ε)` is `exp_p v` for a short `v ∈ V_p`, and the radial ray
`t ↦ exp_p(t v)`, `t ∈ [0, 1]`, is then a continuous path inside `Fix(S)` from
`p` to it (`fixedPointSetComponent_totallyGeodesic`'s mechanism), so it lies in
`C`.

So each component of `Fix(S)` is, near any of its points `p`, exactly the
`exp_p`-image of the linear subspace `V_p ⊂ T_pM` — Petersen's "totally geodesic
submanifold" picture, with the totally-geodesic half supplied by
`fixedPointSetComponent_totallyGeodesic`. -/
theorem exists_expMap_bijOn_fixedPointSetComponent [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (S : Set (M → M)) (hS : ∀ F ∈ S, IsRiemannianIsometry g g F)
    (p : M) (hp : p ∈ fixedPointSet S) :
    ∃ ε : ℝ, 0 < ε ∧
      Set.BijOn (fun v : E => expMap (I := I) g p (v : TangentSpace I p))
        {v : E | Real.sqrt (g.metricInner p v v) < ε ∧
          (v : TangentSpace I p) ∈ fixedTangentSubspace (I := I) S p}
        (connectedComponentIn (fixedPointSet S) p ∩ metricBall (I := I) g p ε) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ε₃, hε₃, hbij⟩ := exists_expMap_bijOn_fixedPointSet (I := I) g hg S hS p hp
  obtain ⟨ε₄, hε₄, hcont, hfix⟩ := exists_isometry_fix_expMap (I := I) g hg p
  set ε : ℝ := min ε₃ ε₄ with hεdef
  have hε : 0 < ε := lt_min hε₃ hε₄
  have hεε₃ : ε ≤ ε₃ := min_le_left _ _
  have hεε₄ : ε ≤ ε₄ := min_le_right _ _
  -- On the `ε`-ball, `Fix(S)` and the component through `p` agree.
  have hcomp : ∀ v : E, Real.sqrt (g.metricInner p v v) < ε →
      (v : TangentSpace I p) ∈ fixedTangentSubspace (I := I) S p →
      expMap (I := I) g p (v : TangentSpace I p)
        ∈ connectedComponentIn (fixedPointSet S) p := by
    intro v hv hvV
    have hvε₄ : Real.sqrt (g.metricInner p v v) < ε₄ := lt_of_lt_of_le hv hεε₄
    have hray : ∀ t ∈ Icc (0 : ℝ) 1,
        expMap (I := I) g p ((t • v : E) : TangentSpace I p) ∈ fixedPointSet S := by
      intro t ht F hF
      refine hfix F (hS F hF) (hp F hF) (t • v) ?_ ?_
      · have hsm : g.metricInner p ((t • v : E) : TangentSpace I p)
            ((t • v : E) : TangentSpace I p) = t ^ 2 * g.metricInner p v v := by
          rw [RiemannianMetric.metricInner_smul_left, RiemannianMetric.metricInner_smul_right]
          ring
        rw [hsm, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
        have h1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
        calc |t| * Real.sqrt (g.metricInner p v v)
            ≤ 1 * Real.sqrt (g.metricInner p v v) :=
              mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
          _ = Real.sqrt (g.metricInner p v v) := one_mul _
          _ < ε₄ := hvε₄
      · rw [map_smul, hvV F hF]
    have himg : (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) '' Icc 0 1
        ⊆ connectedComponentIn (fixedPointSet S) p := by
      have hpre : IsPreconnected
          ((fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) '' Icc 0 1) :=
        (isPreconnected_Icc).image _ (hcont v hvε₄)
      have hsub : (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) '' Icc 0 1
          ⊆ fixedPointSet S := by
        rintro _ ⟨t, ht, rfl⟩; exact hray t ht
      have hmem : p ∈ (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p))
          '' Icc 0 1 := ⟨0, by norm_num, by
            simp only [zero_smul]; exact expMap_zero (I := I) g p⟩
      exact hpre.subset_connectedComponentIn hmem hsub
    exact himg ⟨1, by norm_num, by simp only [one_smul]⟩
  obtain ⟨hmaps, hinj, hsurj⟩ := hbij ε hε hεε₃
  refine ⟨ε, hε, ?_, hinj, ?_⟩
  · rintro v ⟨hv, hvV⟩
    exact ⟨hcomp v hv hvV, (hmaps ⟨hv, hvV⟩).2⟩
  · rintro q ⟨hqC, hqball⟩
    exact hsurj ⟨connectedComponentIn_subset _ _ hqC, hqball⟩

end PetersenLib

end

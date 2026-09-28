import PetersenLib.Ch05.TotallyGeodesic
import PetersenLib.Ch05.ShortSegmentRigidity
import PetersenLib.Ch05.LocalIsometry
import PetersenLib.Ch05.DistanceSegments
import PetersenLib.Riemannian.Exponential.RayGeodesic

/-!
# Petersen Ch. 5, §5.6 — the fixed-point set of a family of isometries

Proposition 5.6.5 (`prop:pet-ch5-fixed-point-totally-geodesic`): for a set
`S ⊂ Iso(M, g)` of Riemannian isometries, each connected component of the fixed
point set `Fix(S)` is **totally geodesic**, with tangent distribution the
`+1`-eigenspace intersection

`V_p = {v ∈ T_pM | DF_p v = v for all F ∈ S}`.

* `fixedTangentSubspace` — the distribution `V`, a submodule of `T_pM`.

* `IsRiemannianIsometry.exists_leftInverse_isLocalRiemannianIsometry` — the
  inverse of a Riemannian isometry is a local Riemannian isometry; this feeds the
  distance-*preserving* clause (Prop. 5.6.1 (4)) below.

* `exists_isometry_fix_expMap` — the analytic core.  At every `p` there is an
  intrinsic radius `ε > 0` such that any isometry `F` with `F p = p` and
  `DF_p v = v` fixes `exp_p v`, for every `v` with `|v|_g < ε`.

* `fixedPointSetComponent_totallyGeodesic` — the node itself.

Petersen argues the core by exp-naturality: `F ∘ c` is a geodesic with the same
initial data as the radial geodesic `c`, hence equals it.  Naturality of `exp`
(Prop. 5.6.1 (1)–(2)) is not available at this layer, so we instead run
Petersen's own second paragraph as the proof of the first: `F ∘ c` is a
**segment** of the same length from `p` to `F(exp_p v)`, so the normal-ball
rigidity of Thm. 5.5.4 (`expMap_isSegment_unique`) forces it to be the radial
geodesic `t ↦ exp_p(t v')` of some `v'` in the same ball, and differentiating at
`t = 0` gives `v' = DF_p v = v`.  Only clauses (3)–(4) of Prop. 5.6.1
(distance decreasing / distance preserving) are used.

This file proves the totally geodesic **property** of each component together
with the distribution `V`; it does not assert that `Fix(S)` is a submanifold
(Petersen's bijection `exp_p : V ∩ B → Fix(S) ∩ B`), which `IsTotallyGeodesic`
does not require.
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

/-! ## The fixed tangent distribution -/

/-- **Math.** Petersen Ch. 5, Prop. 5.6.5: the **fixed tangent subspace**
`V_p = {v ∈ T_pM | DF_p v = v for all F ∈ S}`, the intersection over `F ∈ S` of
the `+1`-eigenspaces of the differentials `DF_p`.  It is the candidate tangent
distribution of the fixed point set `Fix(S)`. -/
def fixedTangentSubspace (S : Set (M → M)) (p : M) : Submodule ℝ (TangentSpace I p) where
  carrier := {v : TangentSpace I p | ∀ F ∈ S, mfderiv I I F p v = v}
  add_mem' := by
    intro a b ha hb F hF
    simp only [map_add, ha F hF, hb F hF]
  zero_mem' := by intro F hF; simp only [map_zero]
  smul_mem' := by
    intro c a ha F hF
    simp only [map_smul, ha F hF]

/-! ## The inverse of a Riemannian isometry -/

/-- **Math.** A Riemannian isometry `F : (M, g) → (M, g)` — a diffeomorphism
whose differential preserves the metric — admits a **left inverse which is
itself a local Riemannian isometry**, namely the inverse diffeomorphism.  This
supplies the bijectivity hypothesis of Prop. 5.6.1 (4), upgrading the distance
decreasing clause (3) to distance preservation. -/
theorem IsRiemannianIsometry.exists_leftInverse_isLocalRiemannianIsometry
    {g : RiemannianMetric I M} {F : M → M} (hF : IsRiemannianIsometry g g F) :
    ∃ G : M → M, IsLocalRiemannianIsometry g g G ∧ Function.LeftInverse G F := by
  obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hF
  have hΦd : MDifferentiable I I (Φ : M → M) := Φ.contMDiff.mdifferentiable (by norm_num)
  have hΦsd : MDifferentiable I I (Φ.symm : M → M) :=
    Φ.symm.contMDiff.mdifferentiable (by norm_num)
  refine ⟨(Φ.symm : M → M), ⟨Φ.symm.contMDiff, ?_, fun q => ?_⟩, fun z => ?_⟩
  · intro q u v
    have hFsq : F (Φ.symm q) = q := by rw [← hΦ]; exact Φ.apply_symm_apply q
    have hchain : ∀ w : TangentSpace I q,
        mfderiv I I F (Φ.symm q) (mfderiv I I (Φ.symm : M → M) q w) = w := by
      intro w
      have h1 : mfderiv I I (F ∘ (Φ.symm : M → M)) q w
          = mfderiv I I F ((Φ.symm : M → M) q) (mfderiv I I (Φ.symm : M → M) q w) := by
        refine mfderiv_comp_apply q ?_ (hΦsd q) w
        rw [← hΦ]; exact hΦd _
      have hid : (F ∘ (Φ.symm : M → M)) = id := by
        funext z; rw [← hΦ]; exact Φ.apply_symm_apply z
      rw [hid, mfderiv_id] at h1
      exact h1.symm
    have h := hpres (Φ.symm q) (mfderiv I I (Φ.symm : M → M) q u)
      (mfderiv I I (Φ.symm : M → M) q v)
    rw [hchain u, hchain v, hFsq] at h
    exact h.symm
  · rw [← Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ.symm (by norm_num) (x := q)]
    exact (Φ.symm.mfderivToContinuousLinearEquiv (by norm_num) q).bijective
  · rw [← hΦ]; exact Φ.symm_apply_apply z

/-! ## The analytic core: short radial geodesics of fixed vectors are fixed -/

/-- **Math.** Petersen Ch. 5, Prop. 5.6.5, first paragraph.  At every `p ∈ M`
there is an intrinsic radius `ε > 0` such that, for `|v|_g < ε`:

* the radial ray `t ↦ exp_p(t v)` is continuous on `[0, 1]`;
* **every** Riemannian isometry `F` fixing `p` whose differential fixes `v`
  (`DF_p v = v`) also fixes the endpoint: `F (exp_p v) = exp_p v`.

The radius comes from the normal-ball form of Thm. 5.5.4
(`expMap_isSegment_unique`): on `|v|_g < ε` the ray `c : t ↦ exp_p(t v)` is a
segment, `exp_p` maps the intrinsic ball onto the metric ball, and any segment
from `p` to `exp_p v` **is** that ray.  Since `F` preserves distance
(Prop. 5.6.1 (3)–(4)), `F ∘ c` is a segment from `p` to `F(exp_p v)`, which lies
in the same metric ball, hence `F ∘ c` is the radial ray `t ↦ exp_p(t v')` of
some `v'` in the ball.  Differentiating at `t = 0` inside `[0, 1]` gives
`v' = DF_p v = v`, so `F (exp_p v) = exp_p v'  = exp_p v`. -/
theorem exists_isometry_fix_expMap [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ v : E, Real.sqrt (g.metricInner p v v) < ε →
        ContinuousOn (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p))
          (Icc 0 1)) ∧
      ∀ F : M → M, IsRiemannianIsometry g g F → F p = p →
        ∀ v : E, Real.sqrt (g.metricInner p v v) < ε →
          mfderiv I I F p (v : TangentSpace I p) = (v : TangentSpace I p) →
            F (expMap (I := I) g p (v : TangentSpace I p))
              = expMap (I := I) g p (v : TangentSpace I p) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ε₀, hε₀, hdom, hball, huniq⟩ := expMap_isSegment_unique (I := I) g hg p
  obtain ⟨ρ, b, hρ, hb, hadm, hray⟩ := exists_isGeodesicOn_expMap_ray (I := I) g p
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
  set ε : ℝ := min ε₀ (ρ / (Real.sqrt cc + 1)) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεε₀ : ε ≤ ε₀ := min_le_left _ _
  have hcoerc : ∀ v : E, Real.sqrt (g.metricInner p v v) < ε → ‖v‖ < ρ := by
    intro v hv
    have h1 : Real.sqrt (g.metricInner p v v) < ρ / (Real.sqrt cc + 1) :=
      hv.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [Real.sqrt_nonneg (g.metricInner p v v), Real.sqrt_nonneg cc, hcoercPole v]
  refine ⟨ε, hε, ?_, ?_⟩
  · intro v hv
    have hvρ : ‖v‖ < ρ := hcoerc v hv
    have hcont := (hray v hvρ).2.2.1
    refine hcont.mono ?_
    intro t ht
    rcases ht with ⟨h0, h1⟩
    exact ⟨by linarith, by linarith⟩
  intro F hFiso hFp v hv hDF
  set c : ℝ → M := fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p) with hc
  have hvε₀ : Real.sqrt (g.metricInner p v v) < ε₀ := lt_of_lt_of_le hv hεε₀
  have hvρ : ‖v‖ < ρ := hcoerc v hv
  obtain ⟨hcseg, hcuniq⟩ := huniq v hvε₀
  have hFloc : IsLocalRiemannianIsometry g g F := hFiso.isLocalRiemannianIsometry
  obtain ⟨G, hGloc, hGF⟩ := hFiso.exists_leftInverse_isLocalRiemannianIsometry
  have hc0 : c 0 = p := by
    rw [hc]; simp only [zero_smul]; exact expMap_zero (I := I) g p
  have hc1 : c 1 = expMap (I := I) g p (v : TangentSpace I p) := by
    rw [hc]; simp only [one_smul]
  have hdistpres : ∀ q q' : M, riemannianDistance (I := I) g (F q) (F q')
      = riemannianDistance (I := I) g q q' :=
    fun q q' => localIsometry_distancePreserving hFloc hGloc hGF q q'
  have hmemball : expMap (I := I) g p (v : TangentSpace I p) ∈ metricBall (I := I) g p ε := by
    rw [← hball ε hε hεε₀]
    exact ⟨v, hv, rfl⟩
  have hFmemball : F (expMap (I := I) g p (v : TangentSpace I p))
      ∈ metricBall (I := I) g p ε := by
    have h := hdistpres p (expMap (I := I) g p (v : TangentSpace I p))
    rw [hFp] at h
    show riemannianDistance (I := I) g p _ < ε
    rw [h]
    exact hmemball
  rw [← hball ε hε hεε₀] at hFmemball
  obtain ⟨v', hv', hv'eq⟩ := hFmemball
  have hv'ε₀ : Real.sqrt (g.metricInner p v' v') < ε₀ := lt_of_lt_of_le hv' hεε₀
  have hv'ρ : ‖v'‖ < ρ := hcoerc v' hv'
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
  have hFc1 : (F ∘ c) 1 = expMap (I := I) g p (v' : TangentSpace I p) := by
    simp only [Function.comp_apply, hc1, hv'eq]
  have hkey : ∀ t ∈ Icc (0 : ℝ) 1,
      (F ∘ c) t = expMap (I := I) g p ((t • v' : E) : TangentSpace I p) :=
    (huniq v' hv'ε₀).2 (F ∘ c) hFcseg hFc0 hFc1
  have hvv' : (v : E) = v' := by
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
      · have : DifferentiableAt ℝ
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
        simpa [ModelWithCorners.range_eq_univ] using this.differentiableWithinAt
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
    have hvel_Fc : velocity (I := I) (F ∘ c) 0 = v := by
      rw [velocity_comp 0 (hFloc.mdifferentiableAt (c 0)) hcmdiff, hvel_c, hc0]
      exact hDF
    have hL : HasDerivAt (fun s : ℝ => extChartAt I p (F (c s))) v 0 := by
      have h1 := hasDerivAt_chartLocalCurve (I := I) hFcmdiff
      rw [hvel_Fc] at h1
      have h2 : Geodesic.chartLocalCurve (I := I) (F ∘ c) 0
          = fun s : ℝ => extChartAt I p (F (c s)) := by
        funext s
        rw [Geodesic.chartLocalCurve_def]
        simp only [Function.comp_apply, hc0, hFp]
      rwa [h2] at h1
    have hR : HasDerivAt
        (fun t : ℝ => extChartAt I p (expMap (I := I) g p ((t • v' : E) : TangentSpace I p)))
        v' 0 := (hray v' hv'ρ).2.1
    have hcongr : ∀ s ∈ Icc (0 : ℝ) 1, (fun s : ℝ => extChartAt I p (F (c s))) s
        = (fun t : ℝ => extChartAt I p
            (expMap (I := I) g p ((t • v' : E) : TangentSpace I p))) s := by
      intro s hs
      simp only []
      rw [show F (c s) = expMap (I := I) g p ((s • v' : E) : TangentSpace I p) from hkey s hs]
    have hLw : HasDerivWithinAt (fun s : ℝ => extChartAt I p (F (c s))) v (Icc 0 1) 0 :=
      hL.hasDerivWithinAt
    have hRw : HasDerivWithinAt (fun s : ℝ => extChartAt I p (F (c s))) v' (Icc 0 1) 0 :=
      (hR.hasDerivWithinAt).congr hcongr (hcongr 0 (by norm_num))
    have hU : UniqueDiffWithinAt ℝ (Icc (0 : ℝ) 1) 0 :=
      uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1) 0 (by norm_num)
    exact hU.eq_deriv _ hLw hRw
  have h1 := hkey 1 (by norm_num)
  simp only [Function.comp_apply, hc, one_smul] at h1
  rw [h1, ← hvv']

/-! ## Proposition 5.6.5 -/

/-- **Math.** Petersen Ch. 5, Prop. 5.6.5
(`prop:pet-ch5-fixed-point-totally-geodesic`): for a family `S` of Riemannian
isometries of `(M, g)`, each **connected component of the fixed point set
`Fix(S)` is totally geodesic**, with tangent distribution the fixed tangent
subspace `V_p = {v | DF_p v = v for all F ∈ S}`.

Given `p` in the component and `v ∈ V_p` short enough, every `F ∈ S` fixes `p`
and `v`, hence fixes `exp_p(t v)` for all `t ∈ [0, 1]` (each `t v` again lies in
`V_p` and is no longer than `v`).  The ray therefore lies in `Fix(S)`; being a
continuous image of `[0, 1]` it is preconnected and meets the component at `p`,
so it lies in the component.  Evaluating at `t = 1` puts `exp_p v` there. -/
theorem fixedPointSetComponent_totallyGeodesic [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (S : Set (M → M)) (hS : ∀ F ∈ S, IsRiemannianIsometry g g F) (x : M) :
    IsTotallyGeodesic (I := I) g (connectedComponentIn (fixedPointSet S) x)
      (fixedTangentSubspace (I := I) S) := by
  classical
  intro p hp
  have hpFix : p ∈ fixedPointSet S := connectedComponentIn_subset _ _ hp
  obtain ⟨ε, hε, hcont, hfix⟩ := exists_isometry_fix_expMap (I := I) g hg p
  obtain ⟨mu, hmu, hub⟩ := exists_forall_chartMetricInner_le (I := I) g
    (α := p) (C := {p}) isCompact_singleton
    (by simp [mem_chart_source H p])
  have hpole : ∀ w : E, g.metricInner p w w ≤ mu * ‖w‖ ^ 2 := by
    intro w
    have h1 := hub p rfl w
    rwa [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) w w,
      trivializationAt_symm_self] at h1
  have hsub : Metric.ball (0 : E) (ε / (Real.sqrt mu + 1))
      ⊆ {v : E | Real.sqrt (g.metricInner p v v) < ε} := by
    intro w hw
    rw [mem_ball_zero_iff] at hw
    show Real.sqrt (g.metricInner p w w) < ε
    calc Real.sqrt (g.metricInner p w w)
        ≤ Real.sqrt (mu * ‖w‖ ^ 2) := Real.sqrt_le_sqrt (hpole w)
      _ = Real.sqrt mu * ‖w‖ := by
          rw [Real.sqrt_mul hmu.le, Real.sqrt_sq (norm_nonneg w)]
      _ < ε := by
          rw [lt_div_iff₀ (by positivity)] at hw
          nlinarith [Real.sqrt_nonneg mu, norm_nonneg w]
  have hW : {v : E | Real.sqrt (g.metricInner p v v) < ε} ∈ 𝓝 (0 : TangentSpace I p) :=
    Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : E) (by positivity : (0:ℝ) < ε / (Real.sqrt mu + 1))) hsub
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hW] with v hv hvT
  have hray : ∀ t ∈ Icc (0 : ℝ) 1,
      expMap (I := I) g p ((t • v : E) : TangentSpace I p) ∈ fixedPointSet S := by
    intro t ht F hF
    refine hfix F (hS F hF) (hpFix F hF) (t • v) ?_ ?_
    · have hsm : g.metricInner p ((t • v : E) : TangentSpace I p)
          ((t • v : E) : TangentSpace I p) = t ^ 2 * g.metricInner p v v := by
        rw [RiemannianMetric.metricInner_smul_left, RiemannianMetric.metricInner_smul_right]
        ring
      rw [hsm, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
      have h1 : |t| ≤ 1 := by rw [abs_le]; constructor <;> [linarith [ht.1]; linarith [ht.2]]
      calc |t| * Real.sqrt (g.metricInner p v v)
          ≤ 1 * Real.sqrt (g.metricInner p v v) := by
            exact mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg _)
        _ = Real.sqrt (g.metricInner p v v) := one_mul _
        _ < ε := hv
    · have hvF := hvT F hF
      rw [map_smul, hvF]
  have himg : (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) '' Icc 0 1
      ⊆ connectedComponentIn (fixedPointSet S) x := by
    have hpre : IsPreconnected
        ((fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) '' Icc 0 1) :=
      (isPreconnected_Icc).image _ (hcont v hv)
    have hsub : (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p)) '' Icc 0 1
        ⊆ fixedPointSet S := by
      rintro _ ⟨t, ht, rfl⟩; exact hray t ht
    have hmem : p ∈ (fun t : ℝ => expMap (I := I) g p ((t • v : E) : TangentSpace I p))
        '' Icc 0 1 := ⟨0, by norm_num, by
          simp only [zero_smul]; exact expMap_zero (I := I) g p⟩
    have := hpre.subset_connectedComponentIn hmem hsub
    exact this.trans (by rw [connectedComponentIn_eq hp])
  exact himg ⟨1, by norm_num, by simp only [one_smul]⟩

end PetersenLib

end

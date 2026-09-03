import MorganTianLib.Ch02.LengthComparison
import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Morgan--Tian Ch. 3 - fixed-time distance contraction

The distance argument in Chapter 3 has two logically separate parts.  The
Ricci-flow equation and a sign condition on Ricci produce a pointwise
quadratic-form inequality; the metric argument below turns that inequality
into a path-length and intrinsic-distance inequality.  Keeping this bridge
separate makes the geometric producer explicit and avoids baking a target
distance estimate into a hypothesis.
-/

open scoped ContDiff Manifold Topology Bundle ENNReal
open Set Riemannian Manifold Bundle

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** The later metric is no larger than the earlier metric as a
quadratic form on every tangent fibre. -/
def MetricInnerLE (g₀ g₁ : RiemannianMetric I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p),
    g₁.metricInner p v v ≤ g₀.metricInner p v v

/-- **Math.** The speed of a curve measured by an explicitly supplied metric. -/
noncomputable def metricCurveSpeed (g : RiemannianMetric I M)
    (c : ℝ → M) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (g.metricInner (c t)
    (mfderiv 𝓘(ℝ, ℝ) I c t 1)
    (mfderiv 𝓘(ℝ, ℝ) I c t 1)))

/-- **Math.** The extended length of a curve measured by an explicitly
supplied metric. This explicit integral can compare two metrics on one
manifold without typeclass ambiguity. -/
noncomputable def metricPathLength (g : RiemannianMetric I M)
    (c : ℝ → M) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, metricCurveSpeed g c t

/-- **Math.** The length integral of a path on the unit interval, measured by
an explicitly supplied metric. -/
noncomputable def metricPathIntegral (g : RiemannianMetric I M)
    {x y : M} (γ : Path x y) : ℝ≥0∞ :=
  ∫⁻ t, ENNReal.ofReal (Real.sqrt (g.metricInner (γ t)
    (mfderiv% γ t 1) (mfderiv% γ t 1)))

/-- **Math.** The intrinsic extended distance of an explicitly supplied
metric, defined as the infimum of the lengths of `C^1` paths. -/
noncomputable def metricIntrinsicEDist (g : RiemannianMetric I M)
    (x y : M) : ℝ≥0∞ :=
  ⨅ (γ : Path x y) (_ : CMDiff 1 γ), metricPathIntegral g γ

/-- **Math.** The fibre `ENorm` associated with an explicitly supplied metric,
used only to bridge the explicit length to Mathlib's path length. -/
@[reducible] noncomputable def metricENorm (g : RiemannianMetric I M) :
    ∀ x : M, ENorm (TangentSpace I x) :=
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  fun _ => SeminormedAddGroup.toContinuousENorm.toENorm

/-- **Math.** A pointwise quadratic-form contraction makes the identity map a
differential metric contraction. -/
theorem metricInnerLE_identity_differential
    {g₀ g₁ : RiemannianMetric I M} (h : MetricInnerLE g₀ g₁) :
    Riemannian.DCShrinksMetricOn g₀ g₁ id (Set.univ : Set M) := by
  intro p hp v
  simpa only [mfderiv_id, id_eq, ContinuousLinearMap.id_apply] using h p v

/-- **Math.** Along a Ricci flow with nonnegative Ricci curvature, a later
metric is no larger than an earlier metric as a quadratic form. -/
theorem metricInnerLE_of_isRicciFlowOn_nonnegativeRicci
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : ∀ t ∈ J, ∀ (p : M) (v : TangentSpace I p),
      0 ≤ ricciTensorAt (g t) p v v)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ J) (ht₁ : t₁ ∈ J) (ht : t₀ ≤ t₁) :
    MetricInnerLE (g t₀) (g t₁) := by
  intro p v
  let f : ℝ → ℝ := fun t => (g t).metricInner p v v
  have hsub : Icc t₀ t₁ ⊆ J :=
    hflow.ordConnected.out ht₀ ht₁
  have hderiv : ∀ t ∈ Icc t₀ t₁,
      HasDerivWithinAt f (-2 * ricciTensorAt (g t) p v v)
        (Icc t₀ t₁) t := by
    intro t htI
    exact (hflow.equation t (hsub htI) p v v).mono hsub
  have hf_cont : ContinuousOn f (Icc t₀ t₁) := by
    intro t htI
    exact (hderiv t htI).continuousWithinAt
  have hf_diff : DifferentiableOn ℝ f (interior (Icc t₀ t₁)) := by
    intro t htI
    have htIcc : t ∈ Icc t₀ t₁ := interior_subset htI
    exact ((hderiv t htIcc).differentiableWithinAt.differentiableAt
      ((mem_interior_iff_mem_nhds).mp htI)).differentiableWithinAt
  have hf_nonpos : ∀ t ∈ interior (Icc t₀ t₁), deriv f t ≤ 0 := by
    intro t htI
    have htIcc : t ∈ Icc t₀ t₁ := interior_subset htI
    have hAt := (hderiv t htIcc).hasDerivAt
      ((mem_interior_iff_mem_nhds).mp htI)
    rw [hAt.deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num)
      (hRic t (hsub htIcc) p v)
  exact antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁)
    hf_cont hf_diff hf_nonpos ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht

/-- **Math.** Under a pointwise metric contraction, the speed of every curve
is no greater in the later metric. -/
theorem metricCurveSpeed_metricInnerLE
    {g₀ g₁ : RiemannianMetric I M} (h : MetricInnerLE g₀ g₁)
    (c : ℝ → M) (t : ℝ) :
    metricCurveSpeed g₁ c t ≤ metricCurveSpeed g₀ c t := by
  unfold metricCurveSpeed
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (h (c t)
    (mfderiv 𝓘(ℝ, ℝ) I c t 1)))

/-- **Math.** Under a pointwise metric contraction, every curve has no greater
explicit length in the later metric. -/
theorem metricPathLength_metricInnerLE
    {g₀ g₁ : RiemannianMetric I M} (h : MetricInnerLE g₀ g₁)
    (c : ℝ → M) (a b : ℝ) :
    metricPathLength g₁ c a b ≤ metricPathLength g₀ c a b := by
  unfold metricPathLength
  exact MeasureTheory.lintegral_mono (fun t =>
    metricCurveSpeed_metricInnerLE (I := I) h c t)

/-- **Math.** A pointwise metric contraction decreases the length integral of
every `C^1` candidate path. -/
theorem metricPathIntegral_metricInnerLE
    {g₀ g₁ : RiemannianMetric I M} (h : MetricInnerLE g₀ g₁)
    {x y : M} (γ : Path x y) :
    metricPathIntegral g₁ γ ≤ metricPathIntegral g₀ γ := by
  unfold metricPathIntegral
  exact MeasureTheory.lintegral_mono (fun t =>
    ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (h (γ t)
      (mfderiv% γ t 1))))

/-- **Math.** A positive quadratic-form factor `A²` scales every explicit
path length by at most `A`.  This is the bilipschitz path-length adapter used
when a metric distortion estimate is available. -/
theorem metricPathIntegral_metricInnerLE_mul
    {g₀ g₁ : RiemannianMetric I M} {A : ℝ} (hA : 0 < A)
    (h : ∀ (p : M) (v : TangentSpace I p),
      g₁.metricInner p v v ≤ A ^ 2 * g₀.metricInner p v v)
    {x y : M} (gamma : Path x y) :
    metricPathIntegral g₁ gamma ≤
      ENNReal.ofReal A * metricPathIntegral g₀ gamma := by
  unfold metricPathIntegral
  calc
    (∫⁻ t, ENNReal.ofReal (Real.sqrt (g₁.metricInner (gamma t)
      (mfderiv% gamma t 1) (mfderiv% gamma t 1)))) ≤
        ∫⁻ t, ENNReal.ofReal A * ENNReal.ofReal (Real.sqrt (g₀.metricInner
          (gamma t) (mfderiv% gamma t 1) (mfderiv% gamma t 1))) := by
      apply MeasureTheory.lintegral_mono
      intro t
      change ENNReal.ofReal (Real.sqrt (g₁.metricInner (gamma t)
          (mfderiv% gamma t 1) (mfderiv% gamma t 1))) ≤
        ENNReal.ofReal A * ENNReal.ofReal (Real.sqrt (g₀.metricInner
          (gamma t) (mfderiv% gamma t 1) (mfderiv% gamma t 1)))
      rw [← ENNReal.ofReal_mul hA.le]
      apply ENNReal.ofReal_le_ofReal
      have h0 : 0 ≤ g₀.metricInner (gamma t)
          (mfderiv% gamma t 1) (mfderiv% gamma t 1) :=
        g₀.metricInner_self_nonneg (gamma t) _
      have hsqrt : Real.sqrt (g₁.metricInner (gamma t)
          (mfderiv% gamma t 1) (mfderiv% gamma t 1)) ≤
          A * Real.sqrt (g₀.metricInner (gamma t)
            (mfderiv% gamma t 1) (mfderiv% gamma t 1)) := by
        apply (Real.sqrt_le_left
          (mul_nonneg hA.le (Real.sqrt_nonneg _))).2
        calc
          g₁.metricInner (gamma t) (mfderiv% gamma t 1)
              (mfderiv% gamma t 1) ≤
              A ^ 2 * g₀.metricInner (gamma t) (mfderiv% gamma t 1)
                (mfderiv% gamma t 1) :=
            h (gamma t) (mfderiv% gamma t 1)
          _ = (A * Real.sqrt (g₀.metricInner (gamma t)
              (mfderiv% gamma t 1) (mfderiv% gamma t 1))) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt h0]
      exact hsqrt
    _ = ENNReal.ofReal A *
        (∫⁻ t, ENNReal.ofReal (Real.sqrt (g₀.metricInner (gamma t)
          (mfderiv% gamma t 1) (mfderiv% gamma t 1)))) := by
      rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Math.** A pointwise quadratic-form contraction decreases the intrinsic
extended distance between every pair of points. -/
theorem metricIntrinsicEDist_metricInnerLE
    {g₀ g₁ : RiemannianMetric I M} (h : MetricInnerLE g₀ g₁)
    (x y : M) :
    metricIntrinsicEDist g₁ x y ≤ metricIntrinsicEDist g₀ x y := by
  unfold metricIntrinsicEDist
  apply iInf_mono
  intro γ
  apply iInf_mono
  intro hγ
  exact metricPathIntegral_metricInnerLE h γ

/-- **Math.** A positive quadratic-form factor `A²` scales the explicit
intrinsic extended distance by at most `A`. -/
theorem metricIntrinsicEDist_metricInnerLE_mul
    {g₀ g₁ : RiemannianMetric I M} {A : ℝ} (hA : 0 < A)
    (h : ∀ (p : M) (v : TangentSpace I p),
      g₁.metricInner p v v ≤ A ^ 2 * g₀.metricInner p v v)
    (x y : M) :
    metricIntrinsicEDist g₁ x y ≤
      ENNReal.ofReal A * metricIntrinsicEDist g₀ x y := by
  unfold metricIntrinsicEDist
  calc
    (⨅ (gamma : Path x y) (_ : CMDiff 1 gamma), metricPathIntegral g₁ gamma) ≤
        ⨅ (gamma : Path x y) (_ : CMDiff 1 gamma),
          ENNReal.ofReal A * metricPathIntegral g₀ gamma := by
      apply iInf_mono
      intro gamma
      apply iInf_mono
      intro hgamma
      exact metricPathIntegral_metricInnerLE_mul hA h gamma
    _ = ENNReal.ofReal A *
        (⨅ (gamma : Path x y) (_ : CMDiff 1 gamma), metricPathIntegral g₀ gamma) := by
      rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hA))
        ENNReal.ofReal_ne_top]
      congr 1
      funext gamma
      rw [ENNReal.mul_iInf_of_ne (ne_of_gt (ENNReal.ofReal_pos.mpr hA))
        ENNReal.ofReal_ne_top]

/-- **Math.** On a connected manifold, the intrinsic distance between any two
fixed points is non-increasing along a Ricci flow with nonnegative Ricci
curvature. This is Morgan--Tian's distance monotonicity lemma. -/
theorem distance_nonincreasing_of_isRicciFlowOn_nonnegativeRicci
    [ConnectedSpace M]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J)
    (hRic : ∀ t ∈ J, ∀ (p : M) (v : TangentSpace I p),
      0 ≤ ricciTensorAt (g t) p v v)
    (x y : M) :
    AntitoneOn (fun t => metricIntrinsicEDist (g t) x y) J := by
  intro t₀ ht₀ t₁ ht₁ ht
  exact metricIntrinsicEDist_metricInnerLE
    (metricInnerLE_of_isRicciFlowOn_nonnegativeRicci
      hflow hRic ht₀ ht₁ ht) x y

/-- **Math.** The explicit metric length agrees with Mathlib's path length
when the fibre bundle is instantiated by the same metric. -/
theorem metricPathLength_eq_pathELength
    (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) :
    metricPathLength g c a b =
      @Manifold.pathELength E _ _ H _ I M _ _ (metricENorm g) c a b := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := metricENorm g
  rw [metricPathLength,
    @Manifold.pathELength_eq_lintegral_mfderiv_Icc E _ _ H _ I M _ _
      (metricENorm g)]
  apply MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  unfold metricCurveSpeed
  exact (Riemannian.enorm_tangent_eq_sqrt_metricInner g (c t)
    (mfderiv 𝓘(ℝ, ℝ) I c t 1)).symm

/-- **Math.** The explicit intrinsic distance agrees with Mathlib's
Riemannian extended distance when the tangent norms come from the same metric. -/
theorem metricIntrinsicEDist_eq_riemannianEDist
    (g : RiemannianMetric I M) (x y : M) :
    metricIntrinsicEDist g x y =
      @Manifold.riemannianEDist E _ _ H _ I M _ _ (metricENorm g) x y := by
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI instE : ∀ x : M, ENorm (TangentSpace I x) := metricENorm g
  rw [Manifold.riemannianEDist]
  unfold metricIntrinsicEDist metricPathIntegral
  congr with γ
  congr with hγ
  apply MeasureTheory.lintegral_congr
  intro t
  exact (Riemannian.enorm_tangent_eq_sqrt_metricInner g (γ t)
    (mfderiv% γ t 1)).symm

end MorganTianLib

end

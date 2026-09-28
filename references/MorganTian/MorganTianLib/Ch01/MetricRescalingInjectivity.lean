import MorganTianLib.Ch01.MetricRescaling
import MorganTianLib.Ch01.CutTimeMeasurable
import MorganTianLib.Ch01.InjectivityRadiusAgreement

open Set Filter Riemannian Riemannian.Geodesic
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [T3Space M] [PreconnectedSpace M]

/-- **Math.** The genuine metric-space structure canonically induced by `g`. -/
@[reducible] noncomputable def canonicalMetricSpace
    (g : RiemannianMetric I M) : MetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    riemannianMetric_isContinuousRiemannianBundle g
  MetricSpace.ofRiemannianMetric I M

/-- **Math.** The canonical metric space has Riemannian distance induced by `g`. -/
theorem canonicalMetricSpace_isRiemannianDist (g : RiemannianMetric I M) :
    letI : MetricSpace M := canonicalMetricSpace g
    g.IsRiemannianDist := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : MetricSpace M := canonicalMetricSpace g
  exact ⟨fun _ _ => rfl⟩

/-- **Math.** Completeness of the canonical metric is invariant under constant rescaling. -/
theorem rescaledMetric_canonicalCompleteSpace_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    (letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc);
      CompleteSpace M) ↔
      (letI : MetricSpace M := canonicalMetricSpace g;
        CompleteSpace M) := by
  simpa only [canonicalMetricSpace] using rescaledMetric_completeSpace_iff g c hc

/-- **Math.** The globally defined radial geodesic for the canonical metric of `g`. -/
noncomputable def canonicalGlobalGeodesic
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (v : TangentSpace I p) : ℝ → M :=
  letI : MetricSpace M := canonicalMetricSpace g
  letI : CompleteSpace M := hcomplete
  globalGeodesic (I := I) g (canonicalMetricSpace_isRiemannianDist g) p v

/-- **Math.** Constant metric rescaling leaves canonical global geodesics unchanged. -/
theorem rescaledMetric_canonicalGlobalGeodesic
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (v : TangentSpace I p) :
    canonicalGlobalGeodesic (rescaledMetric g c hc)
        ((rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete) p v =
      canonicalGlobalGeodesic g hcomplete p v := by
  let hnew := (rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete
  have hgeo : Riemannian.Geodesic.IsGeodesic (I := I) (rescaledMetric g c hc)
      (canonicalGlobalGeodesic g hcomplete p v) := by
    letI : MetricSpace M := canonicalMetricSpace g
    letI : CompleteSpace M := hcomplete
    change Riemannian.Geodesic.IsGeodesic (I := I) (rescaledMetric g c hc)
      (globalGeodesic (I := I) g (canonicalMetricSpace_isRiemannianDist g) p v)
    apply (rescaledMetric_isGeodesic_iff g c hc _).2
    exact isGeodesic_globalGeodesic g (canonicalMetricSpace_isRiemannianDist g) p v
  have hcont : Continuous (canonicalGlobalGeodesic g hcomplete p v) := by
    letI : MetricSpace M := canonicalMetricSpace g
    letI : CompleteSpace M := hcomplete
    change Continuous
      (globalGeodesic (I := I) g (canonicalMetricSpace_isRiemannianDist g) p v)
    exact continuous_globalGeodesic g (canonicalMetricSpace_isRiemannianDist g) p v
  have hzero : canonicalGlobalGeodesic g hcomplete p v 0 = p := by
    letI : MetricSpace M := canonicalMetricSpace g
    letI : CompleteSpace M := hcomplete
    change globalGeodesic (I := I) g
      (canonicalMetricSpace_isRiemannianDist g) p v 0 = p
    exact globalGeodesic_zero g (canonicalMetricSpace_isRiemannianDist g) p v
  have hderiv : HasDerivAt
      (fun t => extChartAt I p (canonicalGlobalGeodesic g hcomplete p v t))
      (v : E) 0 := by
    letI : MetricSpace M := canonicalMetricSpace g
    letI : CompleteSpace M := hcomplete
    change HasDerivAt
      (fun t => extChartAt I p
        (globalGeodesic (I := I) g
          (canonicalMetricSpace_isRiemannianDist g) p v t))
      (v : E) 0
    exact hasDerivAt_chartReading_globalGeodesic
      g (canonicalMetricSpace_isRiemannianDist g) p v
  letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc)
  letI : CompleteSpace M := hnew
  change globalGeodesic (I := I) (rescaledMetric g c hc)
      (canonicalMetricSpace_isRiemannianDist (rescaledMetric g c hc)) p v =
    canonicalGlobalGeodesic g hcomplete p v
  exact (globalGeodesic_eq (rescaledMetric g c hc)
    (canonicalMetricSpace_isRiemannianDist (rescaledMetric g c hc))
    hgeo hcont hzero hderiv).symm

/-- **Math.** The canonical distance for `c g` is `sqrt c` times that for `g`. -/
theorem rescaledMetric_canonicalDist
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p q : M) :
    (letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc);
      dist p q) =
      Real.sqrt c *
        (letI : MetricSpace M := canonicalMetricSpace g;
          dist p q) := by
  simpa only [canonicalMetricSpace] using rescaledMetric_dist g c hc p q

/-- **Math.** The minimizing condition formed using the canonical metric of `g`. -/
def canonicalIsMinimizingUpTo
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (v : TangentSpace I p) (t : ℝ) : Prop :=
  letI : MetricSpace M := canonicalMetricSpace g
  letI : CompleteSpace M := hcomplete
  IsMinimizingUpTo (I := I) g (canonicalMetricSpace_isRiemannianDist g) p v t

/-- **Math.** Constant metric rescaling preserves minimizing times for each fixed vector. -/
theorem rescaledMetric_canonicalIsMinimizingUpTo_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (v : TangentSpace I p) (t : ℝ) :
    canonicalIsMinimizingUpTo (rescaledMetric g c hc)
        ((rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete) p v t ↔
      canonicalIsMinimizingUpTo g hcomplete p v t := by
  let hnew := (rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete
  change
    (letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc);
      dist p (canonicalGlobalGeodesic (rescaledMetric g c hc) hnew p v t) =
        Real.sqrt ((rescaledMetric g c hc).metricInner p v v) * t) ↔
      (letI : MetricSpace M := canonicalMetricSpace g;
        dist p (canonicalGlobalGeodesic g hcomplete p v t) =
          Real.sqrt (g.metricInner p v v) * t)
  rw [rescaledMetric_canonicalDist g c hc p,
    rescaledMetric_canonicalGlobalGeodesic g c hc hcomplete p v,
    rescaledMetric_metricInner, Real.sqrt_mul hc.le]
  constructor <;> intro h
  · nlinarith [Real.sqrt_pos.2 hc]
  · nlinarith [Real.sqrt_pos.2 hc]

/-- **Math.** The exponential map formed using the canonical metric of `g`. -/
noncomputable def canonicalExpMap
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (v : TangentSpace I p) : M :=
  canonicalGlobalGeodesic g hcomplete p v 1

/-- **Math.** Constant metric rescaling leaves the canonical exponential map unchanged. -/
theorem rescaledMetric_canonicalExpMap
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (v : TangentSpace I p) :
    canonicalExpMap (rescaledMetric g c hc)
        ((rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete) p v =
      canonicalExpMap g hcomplete p v := by
  exact congrFun (rescaledMetric_canonicalGlobalGeodesic
    g c hc hcomplete p v) 1

/-- **Math.** The Riemannian tangent ball, with its canonical metric instance hidden. -/
def canonicalMetricTangentBall
    (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set E :=
  letI : MetricSpace M := canonicalMetricSpace g
  metricTangentBall (I := I) g p r

/-- **Math.** Scaling both the metric and radius identifies their tangent balls. -/
theorem rescaledMetric_canonicalMetricTangentBall
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) (p : M) (r : ℝ) :
    canonicalMetricTangentBall (rescaledMetric g c hc) p (Real.sqrt c * r) =
      canonicalMetricTangentBall g p r := by
  ext v
  change Real.sqrt (c * g.metricInner p (v : TangentSpace I p) v) <
      Real.sqrt c * r ↔
    Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r
  rw [Real.sqrt_mul hc.le]
  exact mul_lt_mul_iff_right₀ (Real.sqrt_pos.2 hc)

/-- **Math.** The metric-ball exponential predicate for the canonical metric of `g`. -/
def canonicalMetricExpBallDiffeomorph
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (r : ℝ) : Prop :=
  0 < r ∧
    Set.InjOn
      (fun v : E => canonicalExpMap g hcomplete p (v : TangentSpace I p))
      (canonicalMetricTangentBall g p r) ∧
    ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun v : E => canonicalExpMap g hcomplete p (v : TangentSpace I p))
      (canonicalMetricTangentBall g p r) ∧
    IsOpen
      ((fun v : E => canonicalExpMap g hcomplete p (v : TangentSpace I p)) ''
        canonicalMetricTangentBall g p r) ∧
    ∃ inv : M → E,
      ContMDiffOn I 𝓘(ℝ, E) ∞ inv
        ((fun v : E => canonicalExpMap g hcomplete p (v : TangentSpace I p)) ''
          canonicalMetricTangentBall g p r) ∧
      ∀ v ∈ canonicalMetricTangentBall g p r,
        inv (canonicalExpMap g hcomplete p (v : TangentSpace I p)) = v

/-- **Math.** Admissible metric exponential balls correspond under radius rescaling. -/
theorem rescaledMetric_canonicalMetricExpBallDiffeomorph_iff
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (r : ℝ) :
    canonicalMetricExpBallDiffeomorph (rescaledMetric g c hc)
        ((rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete)
        p (Real.sqrt c * r) ↔
      canonicalMetricExpBallDiffeomorph g hcomplete p r := by
  let hnew := (rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete
  have hexp : (fun v : E =>
      canonicalExpMap (rescaledMetric g c hc) hnew p (v : TangentSpace I p)) =
      (fun v : E => canonicalExpMap g hcomplete p (v : TangentSpace I p)) := by
    funext v
    exact rescaledMetric_canonicalExpMap g c hc hcomplete p v
  unfold canonicalMetricExpBallDiffeomorph
  rw [hexp, rescaledMetric_canonicalMetricTangentBall g c hc p r]
  simp_rw [rescaledMetric_canonicalExpMap g c hc hcomplete p]
  exact and_congr (mul_pos_iff_of_pos_left (Real.sqrt_pos.2 hc)) (Iff.rfl)

/-- **Math.** The canonical facade is the existing metric exponential-ball predicate. -/
theorem canonicalMetricExpBallDiffeomorph_iff
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) (r : ℝ) :
    canonicalMetricExpBallDiffeomorph g hcomplete p r ↔
      (letI : MetricSpace M := canonicalMetricSpace g;
        letI : CompleteSpace M := hcomplete;
        metricExpBallDiffeomorph
          (I := I) g (canonicalMetricSpace_isRiemannianDist g) p r) := by
  rfl

/-- **Math.** The metric-ball injectivity radius for the canonical metric of `g`. -/
noncomputable def canonicalMetricBookInjectivityRadius
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // canonicalMetricExpBallDiffeomorph g hcomplete p r},
    ENNReal.ofReal (r : ℝ)

/-- **Math.** The canonical facade is the existing metric-ball injectivity radius. -/
theorem canonicalMetricBookInjectivityRadius_eq
    (g : RiemannianMetric I M)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) :
    canonicalMetricBookInjectivityRadius g hcomplete p =
      (letI : MetricSpace M := canonicalMetricSpace g;
        letI : CompleteSpace M := hcomplete;
        metricBookInjectivityRadius
          (I := I) g (canonicalMetricSpace_isRiemannianDist g) p) := by
  rfl

/-- **Math.** Constant metric rescaling multiplies the canonical metric-ball
injectivity radius by `sqrt c`. Blueprint: `lem:metric-rescaling` (item 6). -/
theorem rescaledMetric_canonicalMetricBookInjectivityRadius
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c)
    (hcomplete : letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
    (p : M) :
    canonicalMetricBookInjectivityRadius (rescaledMetric g c hc)
        ((rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete) p =
      ENNReal.ofReal (Real.sqrt c) *
        canonicalMetricBookInjectivityRadius g hcomplete p := by
  let hnew := (rescaledMetric_canonicalCompleteSpace_iff g c hc).2 hcomplete
  let a : ℝ := Real.sqrt c
  have ha : 0 < a := Real.sqrt_pos.2 hc
  unfold canonicalMetricBookInjectivityRadius
  apply le_antisymm
  · refine iSup_le fun s => ?_
    let r : ℝ := (s : ℝ) / a
    have hscale : a * r = (s : ℝ) := by
      dsimp only [r]
      field_simp
    have hr : canonicalMetricExpBallDiffeomorph g hcomplete p r :=
      (rescaledMetric_canonicalMetricExpBallDiffeomorph_iff
        g c hc hcomplete p r).1 (by
          simpa only [a, hscale] using s.property)
    let rs : {r : ℝ // canonicalMetricExpBallDiffeomorph g hcomplete p r} := ⟨r, hr⟩
    calc
      ENNReal.ofReal (s : ℝ) = ENNReal.ofReal (a * r) := by rw [hscale]
      _ = ENNReal.ofReal a * ENNReal.ofReal r := ENNReal.ofReal_mul ha.le
      _ ≤ ENNReal.ofReal a *
          ⨆ t : {t : ℝ // canonicalMetricExpBallDiffeomorph g hcomplete p t},
            ENNReal.ofReal (t : ℝ) :=
        mul_le_mul_right (le_iSup
          (fun t : {t : ℝ // canonicalMetricExpBallDiffeomorph g hcomplete p t} =>
            ENNReal.ofReal (t : ℝ)) rs) _
  · rw [ENNReal.mul_iSup]
    refine iSup_le fun r => ?_
    have hr : canonicalMetricExpBallDiffeomorph (rescaledMetric g c hc)
        hnew p (a * (r : ℝ)) := by
      simpa only [a] using
        (rescaledMetric_canonicalMetricExpBallDiffeomorph_iff
          g c hc hcomplete p (r : ℝ)).2 r.property
    let s : {s : ℝ // canonicalMetricExpBallDiffeomorph (rescaledMetric g c hc)
        hnew p s} := ⟨a * (r : ℝ), hr⟩
    calc
      ENNReal.ofReal a * ENNReal.ofReal (r : ℝ) =
          ENNReal.ofReal (a * (r : ℝ)) := (ENNReal.ofReal_mul ha.le).symm
      _ ≤ ⨆ t : {t : ℝ // canonicalMetricExpBallDiffeomorph
          (rescaledMetric g c hc) hnew p t}, ENNReal.ofReal (t : ℝ) :=
        le_iSup
          (fun t : {t : ℝ // canonicalMetricExpBallDiffeomorph
            (rescaledMetric g c hc) hnew p t} => ENNReal.ofReal (t : ℝ)) s

/-! ### Intrinsic injectivity radius without completeness -/

section IntrinsicInjectivity

variable {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [SigmaCompactSpace N] [T2Space N]

/-- **Math.** The open tangent ball measured by `g_p`, independent of any
global completeness assumption. -/
def intrinsicMetricTangentBall (g : RiemannianMetric I N)
    (p : N) (r : ℝ) : Set E :=
  {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r}

/-- **Math.** The intrinsic exponential map is a diffeomorphism into the
manifold on the metric tangent ball of radius `r`. The domain clause ensures
that the junk extension of the intrinsic exponential map is never used. -/
def intrinsicMetricExpBallDiffeomorph (g : RiemannianMetric I N)
    (p : N) (r : ℝ) : Prop :=
  0 < r ∧
    (∀ v : E, v ∈ intrinsicMetricTangentBall (I := I) g p r →
      (v : TangentSpace I p) ∈
        Riemannian.Exponential.expDomainIntrinsic (I := I) g p) ∧
    Set.InjOn
      (fun v : E => Riemannian.Exponential.expMapIntrinsic
        (I := I) g p (v : TangentSpace I p))
      (intrinsicMetricTangentBall (I := I) g p r) ∧
    ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun v : E => Riemannian.Exponential.expMapIntrinsic
        (I := I) g p (v : TangentSpace I p))
      (intrinsicMetricTangentBall (I := I) g p r) ∧
    IsOpen
      ((fun v : E => Riemannian.Exponential.expMapIntrinsic
        (I := I) g p (v : TangentSpace I p)) ''
        intrinsicMetricTangentBall (I := I) g p r) ∧
    ∃ inv : N → E,
      ContMDiffOn I 𝓘(ℝ, E) ∞ inv
        ((fun v : E => Riemannian.Exponential.expMapIntrinsic
          (I := I) g p (v : TangentSpace I p)) ''
          intrinsicMetricTangentBall (I := I) g p r) ∧
      ∀ v ∈ intrinsicMetricTangentBall (I := I) g p r,
        inv (Riemannian.Exponential.expMapIntrinsic
          (I := I) g p (v : TangentSpace I p)) = v

/-- **Math.** The injectivity radius defined from genuine intrinsic
exponential-map balls, with no completeness hypothesis. -/
noncomputable def intrinsicMetricBookInjectivityRadius
    (g : RiemannianMetric I N) (p : N) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // intrinsicMetricExpBallDiffeomorph (I := I) g p r},
    ENNReal.ofReal (r : ℝ)

/-- **Math.** Scaling the metric and radius identifies intrinsic tangent balls. -/
theorem rescaledMetric_intrinsicMetricTangentBall
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c) (p : N) (r : ℝ) :
    intrinsicMetricTangentBall (I := I) (rescaledMetric g c hc) p
        (Real.sqrt c * r) =
      intrinsicMetricTangentBall (I := I) g p r := by
  ext v
  change Real.sqrt (c * g.metricInner p (v : TangentSpace I p) v) <
      Real.sqrt c * r ↔
    Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r
  rw [Real.sqrt_mul hc.le]
  exact mul_lt_mul_iff_right₀ (Real.sqrt_pos.2 hc)

/-- **Math.** Intrinsic exponential balls correspond under positive constant
metric rescaling, including their natural-domain condition. -/
theorem rescaledMetric_intrinsicMetricExpBallDiffeomorph_iff
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c)
    (p : N) (r : ℝ) :
    intrinsicMetricExpBallDiffeomorph (I := I) (rescaledMetric g c hc)
        p (Real.sqrt c * r) ↔
      intrinsicMetricExpBallDiffeomorph (I := I) g p r := by
  have hexp : (fun v : E => Riemannian.Exponential.expMapIntrinsic
      (I := I) (rescaledMetric g c hc) p (v : TangentSpace I p)) =
      (fun v : E => Riemannian.Exponential.expMapIntrinsic
        (I := I) g p (v : TangentSpace I p)) := by
    funext v
    exact rescaledMetric_expMapIntrinsic g c hc p v
  unfold intrinsicMetricExpBallDiffeomorph
  rw [hexp, rescaledMetric_intrinsicMetricTangentBall g c hc p r,
    rescaledMetric_expDomainIntrinsic g c hc p]
  simp_rw [rescaledMetric_expMapIntrinsic g c hc p]
  exact and_congr (mul_pos_iff_of_pos_left (Real.sqrt_pos.2 hc)) (Iff.rfl)

/-- **Math.** For every Riemannian manifold, without completeness,
`inj_(M,cg)(p) = sqrt(c) inj_(M,g)(p)` for the intrinsic exponential-map
definition. Blueprint: `lem:metric-rescaling` (item 6). -/
theorem rescaledMetric_intrinsicMetricBookInjectivityRadius
    (g : RiemannianMetric I N) (c : ℝ) (hc : 0 < c) (p : N) :
    intrinsicMetricBookInjectivityRadius (I := I) (rescaledMetric g c hc) p =
      ENNReal.ofReal (Real.sqrt c) *
        intrinsicMetricBookInjectivityRadius (I := I) g p := by
  let a : ℝ := Real.sqrt c
  have ha : 0 < a := Real.sqrt_pos.2 hc
  unfold intrinsicMetricBookInjectivityRadius
  apply le_antisymm
  · refine iSup_le fun s => ?_
    let r : ℝ := (s : ℝ) / a
    have hscale : a * r = (s : ℝ) := by
      dsimp only [r]
      field_simp
    have hr : intrinsicMetricExpBallDiffeomorph (I := I) g p r :=
      (rescaledMetric_intrinsicMetricExpBallDiffeomorph_iff
        g c hc p r).1 (by simpa only [a, hscale] using s.property)
    let rs : {r : ℝ // intrinsicMetricExpBallDiffeomorph (I := I) g p r} := ⟨r, hr⟩
    calc
      ENNReal.ofReal (s : ℝ) = ENNReal.ofReal (a * r) := by rw [hscale]
      _ = ENNReal.ofReal a * ENNReal.ofReal r := ENNReal.ofReal_mul ha.le
      _ ≤ ENNReal.ofReal a *
          ⨆ t : {t : ℝ // intrinsicMetricExpBallDiffeomorph (I := I) g p t},
            ENNReal.ofReal (t : ℝ) :=
        mul_le_mul_right (le_iSup
          (fun t : {t : ℝ // intrinsicMetricExpBallDiffeomorph (I := I) g p t} =>
            ENNReal.ofReal (t : ℝ)) rs) _
  · rw [ENNReal.mul_iSup]
    refine iSup_le fun r => ?_
    have hr : intrinsicMetricExpBallDiffeomorph (I := I) (rescaledMetric g c hc)
        p (a * (r : ℝ)) := by
      simpa only [a] using
        (rescaledMetric_intrinsicMetricExpBallDiffeomorph_iff
          g c hc p (r : ℝ)).2 r.property
    let s : {s : ℝ // intrinsicMetricExpBallDiffeomorph
        (I := I) (rescaledMetric g c hc) p s} := ⟨a * (r : ℝ), hr⟩
    calc
      ENNReal.ofReal a * ENNReal.ofReal (r : ℝ) =
          ENNReal.ofReal (a * (r : ℝ)) := (ENNReal.ofReal_mul ha.le).symm
      _ ≤ ⨆ t : {t : ℝ // intrinsicMetricExpBallDiffeomorph
          (I := I) (rescaledMetric g c hc) p t}, ENNReal.ofReal (t : ℝ) :=
        le_iSup
          (fun t : {t : ℝ // intrinsicMetricExpBallDiffeomorph
            (I := I) (rescaledMetric g c hc) p t} => ENNReal.ofReal (t : ℝ)) s

end IntrinsicInjectivity

/-- **Math.** All six constant-rescaling laws in `lem:metric-rescaling`,
grouped into the single proposition used by the blueprint anchor. -/
structure MetricRescalingLaws
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [Nonempty M]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) : Prop where
  christoffel : ∀ (α : M) (i j k : Fin (Module.finrank ℝ E)) (y : E),
    y ∈ (extChartAt I α).target →
      chartChristoffel (I := I) (rescaledMetric g c hc) α i j k y =
        chartChristoffel (I := I) g α i j k y
  connection :
    (rescaledMetric g c hc).leviCivitaConnection = g.leviCivitaConnection
  geodesics : ∀ γ : ℝ → M,
    Riemannian.Geodesic.IsGeodesic (I := I) (rescaledMetric g c hc) γ ↔
      Riemannian.Geodesic.IsGeodesic (I := I) g γ
  exponential : ∀ (p : M) (v : TangentSpace I p),
    (letI : MetricSpace M := canonicalMetricSpace g;
      Riemannian.Exponential.expMapIntrinsic
          (I := I) (rescaledMetric g c hc) p v =
        Riemannian.Exponential.expMapIntrinsic (I := I) g p v)
  curvature : ∀ X Y Z : SmoothVectorField I M,
    (rescaledMetric g c hc).leviCivitaConnection.curvature X Y Z =
      g.leviCivitaConnection.curvature X Y Z
  curvatureForm : ∀ (p : M) (v w z t : TangentSpace I p),
    curvatureFormAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection p v w z t =
      c * curvatureFormAt g g.leviCivitaConnection p v w z t
  sectionalCurvature : ∀ (p : M) (v w : TangentSpace I p),
    sectionalCurvatureAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection p v w =
      sectionalCurvatureAt g g.leviCivitaConnection p v w / c
  curvatureOperatorNorm : ∀
      (hLC : g.leviCivitaConnection.IsLeviCivita g)
      (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
        (rescaledMetric g c hc)) (p : M) (K : ℝ),
    HasCurvatureOperatorNormLeAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p (K / c) ↔
      HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
        hLC p K
  ricci : ∀
      (hLC : g.leviCivitaConnection.IsLeviCivita g)
      (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
        (rescaledMetric g c hc)) (p : M) (v w : TangentSpace I p),
    ricciAt (rescaledMetric g c hc)
        (rescaledMetric g c hc).leviCivitaConnection hLC' p v w =
      ricciAt g g.leviCivitaConnection hLC p v w
  ricciLowerBound : ∀
      (hLC : g.leviCivitaConnection.IsLeviCivita g)
      (hLC' : (rescaledMetric g c hc).leviCivitaConnection.IsLeviCivita
        (rescaledMetric g c hc)) (p : M) (k : ℝ),
    (∀ v : TangentSpace I p,
      ((Module.finrank ℝ E : ℝ) - 1) * k * g.metricInner p v v ≤
        ricciAt g g.leviCivitaConnection hLC p v v) ↔
    (∀ v : TangentSpace I p,
      ((Module.finrank ℝ E : ℝ) - 1) * (k / c) *
          (rescaledMetric g c hc).metricInner p v v ≤
        ricciAt (rescaledMetric g c hc)
          (rescaledMetric g c hc).leviCivitaConnection hLC' p v v)
  distance : ∀ p q : M,
    (letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc);
      dist p q) =
      Real.sqrt c * (letI : MetricSpace M := canonicalMetricSpace g; dist p q)
  balls : ∀ (p : M) (r : ℝ),
    (letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc);
      Metric.ball p (Real.sqrt c * r)) =
      (letI : MetricSpace M := canonicalMetricSpace g; Metric.ball p r)
  completeness :
    (letI : MetricSpace M := canonicalMetricSpace (rescaledMetric g c hc);
      CompleteSpace M) ↔
      (letI : MetricSpace M := canonicalMetricSpace g; CompleteSpace M)
  volume :
    riemannianMeasure (I := I) (rescaledMetric g c hc) μ =
      ENNReal.ofReal (c ^ ((Module.finrank ℝ E : ℝ) / 2)) •
        riemannianMeasure (I := I) g μ
  injectivityRadius : ∀ p : M,
    (letI : MetricSpace M := canonicalMetricSpace g;
      intrinsicMetricBookInjectivityRadius (I := I) (rescaledMetric g c hc) p) =
      ENNReal.ofReal (Real.sqrt c) *
        (letI : MetricSpace M := canonicalMetricSpace g;
          intrinsicMetricBookInjectivityRadius (I := I) g p)

/-- **Math.** Positive constant rescaling satisfies every law listed in
`lem:metric-rescaling`. -/
theorem metricRescalingLaws
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [Nonempty M]
    (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (c : ℝ) (hc : 0 < c) :
    MetricRescalingLaws μ g c hc := by
  refine
    { christoffel := fun α i j k y hy =>
        rescaledMetric_chartChristoffel g c hc α i j k y hy
      connection := rescaledMetric_leviCivitaConnection g c hc
      geodesics := fun γ => rescaledMetric_isGeodesic_iff g c hc γ
      exponential := fun p v => by
        letI : MetricSpace M := canonicalMetricSpace g
        exact rescaledMetric_expMapIntrinsic g c hc p v
      curvature := fun X Y Z => rescaledMetric_curvature g c hc X Y Z
      curvatureForm := fun p v w z t =>
        rescaledMetric_curvatureFormAt g c hc p v w z t
      sectionalCurvature := fun p v w =>
        rescaledMetric_sectionalCurvatureAt g c hc p v w
      curvatureOperatorNorm := fun hLC hLC' p K =>
        rescaledMetric_hasCurvatureOperatorNormLeAt_div_iff g c hc
          hLC hLC' p K
      ricci := fun hLC hLC' p v w =>
        rescaledMetric_ricciAt g c hc hLC hLC' p v w
      ricciLowerBound := fun hLC hLC' p k =>
        rescaledMetric_ricciLowerBoundAt_iff g c hc hLC hLC' p k
      distance := fun p q => rescaledMetric_canonicalDist g c hc p q
      balls := fun p r => by
        simpa only [canonicalMetricSpace] using rescaledMetric_ball g c hc p r
      completeness := rescaledMetric_canonicalCompleteSpace_iff g c hc
      volume := rescaledMetric_riemannianMeasure_rpow μ g c hc
      injectivityRadius := fun p => by
        letI : MetricSpace M := canonicalMetricSpace g
        exact rescaledMetric_intrinsicMetricBookInjectivityRadius g c hc p }

end MorganTianLib

end

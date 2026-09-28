import MorganTianLib.Ch01.ExpSegmentDiffeomorph
import MorganTianLib.Ch01.MetricEuclideanEquiv

/-!
# The norm convention in the two injectivity-radius definitions

`bookInjectivityRadius` uses balls for the fixed norm on the model space `E`, whereas
`injectivityRadius` uses the Riemannian norm `sqrt (g.metricInner p v v)` on the
tangent fibre.  These are not definitionally the same norm.  This file records the
correct metric-ball replacement and the precise conditional bridge to the book
definition.  An unconditional equality would require an additional norm
compatibility hypothesis (or a change of coordinates to a `g_p`-orthonormal frame).
-/

open Set Metric Riemannian
open scoped ContDiff Manifold Topology Bundle ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M]

/-- **Math.** The open tangent-fibre ball measured by the Riemannian metric at `p`.

This is the ball that occurs in the metric definition of injectivity radius. -/
def metricTangentBall (g : RiemannianMetric I M) (p : M) (r : ℝ) : Set E :=
  {v : E | Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r}

@[simp]
theorem mem_metricTangentBall (g : RiemannianMetric I M) (p : M) (r : ℝ) (v : E) :
    v ∈ metricTangentBall (I := I) g p r ↔
      Real.sqrt (g.metricInner p (v : TangentSpace I p) v) < r := Iff.rfl

/-- **Math.** The injectivity-ball predicate with the Riemannian (rather than model) norm. -/
def metricExpBallDiffeomorph (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) (r : ℝ) : Prop :=
  0 < r ∧
    Set.InjOn
      (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p))
      (metricTangentBall (I := I) g p r) ∧
    ContMDiffOn 𝓘(ℝ, E) I ∞
      (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p))
      (metricTangentBall (I := I) g p r) ∧
    IsOpen
      ((fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p)) ''
        metricTangentBall (I := I) g p r) ∧
    ∃ inv : M → E,
      ContMDiffOn I 𝓘(ℝ, E) ∞ inv
        ((fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p)) ''
          metricTangentBall (I := I) g p r) ∧
      ∀ v ∈ metricTangentBall (I := I) g p r,
        inv (expMapGlobal (I := I) g hg p (v : TangentSpace I p)) = v

/-- **Math.** The corrected book-style radius, with balls measured by `g_p`. -/
def metricBookInjectivityRadius (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) : ℝ≥0∞ :=
  ⨆ r : {r : ℝ // metricExpBallDiffeomorph (I := I) g hg p r},
    ENNReal.ofReal (r : ℝ)

/-- **Math.** A `g_p`-orthonormal frame transports an ordinary Euclidean ball exactly to a
metric tangent ball.  This is the coordinate change needed before comparing a
ball-based definition with `injectivityRadius`. -/
theorem gpEuclideanEquiv_image_ball_eq_metricTangentBall
    (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    gpEuclideanEquiv (I := I) g p '' Metric.ball
        (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r =
      metricTangentBall (I := I) g p r := by
  apply Set.Subset.antisymm
  · rintro v ⟨x, hx, rfl⟩
    rw [mem_metricTangentBall, gpEuclideanEquiv_metricNorm]
    simpa [Metric.mem_ball, dist_zero_right] using hx
  · intro v hv
    have hpre : gpEuclideanEquiv (I := I) g p ⁻¹' metricTangentBall (I := I) g p r =
        Metric.ball (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) r :=
      gpEuclideanEquiv_preimage_metricBall (I := I) g p r
    refine ⟨(gpEuclideanEquiv (I := I) g p).symm v, ?_,
      (gpEuclideanEquiv (I := I) g p).apply_symm_apply v⟩
    rw [← hpre]
    change gpEuclideanEquiv (I := I) g p
        ((gpEuclideanEquiv (I := I) g p).symm v) ∈
      metricTangentBall (I := I) g p r
    simpa using hv

/-- **Math.** Every metric tangent ball whose radius is below the metric
injectivity radius lies in the metric segment domain.  This is the radial part
of the corrected injectivity-radius comparison and uses no model-space norm. -/
theorem metricTangentBall_subset_segmentDomain_of_le_injectivityRadius
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {r : ℝ}
    (hri : ENNReal.ofReal r ≤ injectivityRadius (I := I) g hg p) :
    metricTangentBall (I := I) g p r ⊆ segmentDomain (I := I) g hg p := by
  intro v hv
  by_cases hv0 : (v : TangentSpace I p) = 0
  · simpa [hv0] using zero_mem_segmentDomain (I := I) g hg p
  let a : ℝ := Real.sqrt (g.metricInner p (v : TangentSpace I p) v)
  have ha : 0 < a := by
    dsimp [a]
    exact Real.sqrt_pos.2 (g.metricInner_self_pos p _ hv0)
  let u : TangentSpace I p := (a⁻¹) • (v : TangentSpace I p)
  have hvdecomp : (v : TangentSpace I p) = a • u := by
    have hsmul :
        (a • ((a⁻¹) • (v : TangentSpace I p)) : TangentSpace I p) =
          (v : TangentSpace I p) := by
      rw [← mul_smul, mul_inv_cancel₀ (ne_of_gt ha), one_smul]
    exact hsmul.symm
  have huunit : g.metricInner p u u = 1 := by
    have hsq : a ^ 2 = g.metricInner p (v : TangentSpace I p) v := by
      dsimp [a]
      exact Real.sq_sqrt (g.metricInner_self_nonneg p _)
    calc
      g.metricInner p u u =
          g.metricInner p ((a⁻¹) • (v : TangentSpace I p))
            ((a⁻¹) • (v : TangentSpace I p)) := by rfl
      _ = (a⁻¹ * a⁻¹) * g.metricInner p (v : TangentSpace I p) v :=
        metricInner_smul_self (I := I) g p a⁻¹ (v : TangentSpace I p)
      _ = 1 := by
        rw [← hsq]
        field_simp
  have hav : a < r := by
    exact hv
  have hlt_r : ENNReal.ofReal a < ENNReal.ofReal r :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha.le).2 hav
  have hcut : injectivityRadius (I := I) g hg p ≤
      cutTime (I := I) g hg p u :=
    injectivityRadius_le_cutTime (I := I) g hg p huunit
  have hlt : ENNReal.ofReal a < cutTime (I := I) g hg p u :=
    lt_of_lt_of_le hlt_r (hri.trans hcut)
  change (v : TangentSpace I p) ∈ segmentDomain (I := I) g hg p
  rw [hvdecomp]
  exact (smul_mem_segmentDomain_iff_lt_cutTime (I := I) g hg p ha).2 hlt

/-- **Math.** A metric tangent ball below the metric injectivity radius maps
away from the cut locus.  This is the cut-locus half of the corrected
metric/book comparison. -/
theorem expMapGlobal_image_metricTangentBall_subset_cutLocus_compl_of_le_injectivityRadius
    [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {r : ℝ}
    (hri : ENNReal.ofReal r ≤ injectivityRadius (I := I) g hg p) :
    (fun v : E => expMapGlobal (I := I) g hg p (v : TangentSpace I p)) ''
        metricTangentBall (I := I) g p r ⊆
      (cutLocus (I := I) g hg p)ᶜ := by
  intro q hq
  rcases hq with ⟨v, hv, rfl⟩
  intro hcut
  have hvseg := metricTangentBall_subset_segmentDomain_of_le_injectivityRadius
    (I := I) g hg p hri hv
  exact (Set.disjoint_left.mp (disjoint_cutLocus_image_segmentDomain
    (I := I) g hg p)) hcut ⟨v, hvseg, rfl⟩

theorem isOpen_metricTangentBall (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    IsOpen (metricTangentBall (I := I) g p r) := by
  exact isOpen_lt (continuous_metricNorm (I := I) g p) continuous_const

/-- **Math.** Every positive metric ball whose radius is at most the metric injectivity
radius inherits the diffeomorphism onto its image from the exponential diffeomorphism on
the full segment domain. -/
theorem metricExpBallDiffeomorph_of_le_injectivityRadius
    [ConnectedSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {r : ℝ} (hr : 0 < r)
    (hri : ENNReal.ofReal r ≤ injectivityRadius (I := I) g hg p) :
    metricExpBallDiffeomorph (I := I) g hg p r := by
  classical
  let F : E → M := fun v =>
    expMapGlobal (I := I) g hg p (v : TangentSpace I p)
  let U := segmentDomainOpens (I := I) g hg p
  let V := cutLocusComplementOpens (I := I) g hg p
  let D := expMapGlobal_segmentDomain_diffeomorph (I := I) g hg p
  have hBseg : metricTangentBall (I := I) g p r ⊆
      segmentDomain (I := I) g hg p :=
    metricTangentBall_subset_segmentDomain_of_le_injectivityRadius
      (I := I) g hg p hri
  have hBV : F '' metricTangentBall (I := I) g p r ⊆
      (cutLocus (I := I) g hg p)ᶜ := by
    simpa only [F] using
      expMapGlobal_image_metricTangentBall_subset_cutLocus_compl_of_le_injectivityRadius
        (I := I) g hg p hri
  let inv : M → E := fun q =>
    if hq : q ∈ (cutLocus (I := I) g hg p)ᶜ then
      ((D.symm ⟨q, hq⟩ : U) : E)
    else 0
  have hinj : Set.InjOn F (metricTangentBall (I := I) g p r) := by
    intro v hv w hw heq
    exact injOn_expMapGlobal_segmentDomain (I := I) g hg p
      (hBseg hv) (hBseg hw) heq
  have hsmooth : ContMDiffOn 𝓘(ℝ, E) I ∞ F
      (metricTangentBall (I := I) g p r) := by
    exact (Riemannian.Exponential.contMDiff_expMapGlobal g hg p).contMDiffOn
  have hopen : IsOpen (F '' metricTangentBall (I := I) g p r) := by
    let B : Set U := (Subtype.val : U → E) ⁻¹'
      metricTangentBall (I := I) g p r
    have hBopen : IsOpen B :=
      (isOpen_metricTangentBall (I := I) g p r).preimage continuous_subtype_val
    have hDBopen : IsOpen (D '' B) := D.toHomeomorph.isOpenMap B hBopen
    have hvalOpen : IsOpen ((Subtype.val : V → M) '' (D '' B)) :=
      (isClosed_cutLocus (I := I) g hg p).isOpen_compl.isOpenMap_subtype_val
        (D '' B) hDBopen
    have heq : (Subtype.val : V → M) '' (D '' B) =
        F '' metricTangentBall (I := I) g p r := by
      ext q
      constructor
      · rintro ⟨y, ⟨x, hxB, rfl⟩, rfl⟩
        refine ⟨(x : E), hxB, ?_⟩
        exact (congrArg Subtype.val
          (expMapGlobal_segmentDomain_diffeomorph_apply
            (I := I) g hg p x)).symm
      · rintro ⟨v, hvB, rfl⟩
        let x : U := ⟨v, hBseg hvB⟩
        refine ⟨D x, ⟨x, hvB, rfl⟩, ?_⟩
        simpa only [F] using congrArg Subtype.val
          (expMapGlobal_segmentDomain_diffeomorph_apply
            (I := I) g hg p x)
    rw [← heq]
    exact hvalOpen
  have hinvSmooth : ContMDiffOn I 𝓘(ℝ, E) ∞ inv
      (F '' metricTangentBall (I := I) g p r) := by
    have hrestrict : ContMDiff I 𝓘(ℝ, E) ∞
        (fun y : V => inv (y : M)) := by
      have hD : ContMDiff I 𝓘(ℝ, E) ∞
          (Subtype.val ∘ D.symm) :=
        (contMDiff_subtype_val : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
          (Subtype.val : U → E)).comp D.symm.contMDiff
      have heq : (fun y : V => inv (y : M)) = Subtype.val ∘ D.symm := by
        funext y
        change (if hq : (y : M) ∈ (cutLocus (I := I) g hg p)ᶜ then
            ((D.symm ⟨(y : M), hq⟩ : U) : E) else 0) =
          ((D.symm y : U) : E)
        have hyV : (y : M) ∈ (cutLocus (I := I) g hg p)ᶜ := y.property
        rw [dif_pos hyV]
      rw [heq]
      exact hD
    intro q hq
    have hqV : q ∈ (cutLocus (I := I) g hg p)ᶜ := hBV hq
    have hqsub : ContMDiffAt I 𝓘(ℝ, E) ∞
        (fun y : V => inv (y : M)) ⟨q, hqV⟩ :=
      hrestrict.contMDiffAt
    exact (contMDiffAt_subtype_iff.mp hqsub).contMDiffWithinAt
  have hinvLeft : ∀ v ∈ metricTangentBall (I := I) g p r,
      inv (F v) = v := by
    intro v hv
    have hvseg : v ∈ segmentDomain (I := I) g hg p := hBseg hv
    have hvV : F v ∈ (cutLocus (I := I) g hg p)ᶜ :=
      hBV ⟨v, hv, rfl⟩
    let x : U := ⟨v, hvseg⟩
    have hDx : D x = ⟨F v, hvV⟩ := by
      apply Subtype.ext
      simpa only [D, F] using congrArg Subtype.val
        (expMapGlobal_segmentDomain_diffeomorph_apply
          (I := I) g hg p x)
    simp only [inv, dif_pos hvV]
    rw [← hDx, D.symm_apply_apply]
  exact ⟨hr, hinj, hsmooth, hopen, inv, hinvSmooth, hinvLeft⟩

/-! A metric-ball diffeomorphism supplies precisely the local inverse needed in the
book segment-domain predicate.  Keeping this as a separate lemma makes the converse
radius comparison independent of any choice of inverse outside the image. -/
theorem mem_bookSegmentDomain_of_metricExpBallDiffeomorph
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M) (r : ℝ)
    (hball : metricExpBallDiffeomorph (I := I) g hg p r)
    {v : E} (hv : v ∈ metricTangentBall (I := I) g p r)
    (hmin : IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) 1) :
    (v : TangentSpace I p) ∈ bookSegmentDomain (I := I) g hg p := by
  classical
  rcases hball with ⟨hr, hinj, hsmooth, hopen, inv, hinvSmooth, hinvLeft⟩
  let F : E → M := fun x =>
    expMapGlobal (I := I) g hg p (x : TangentSpace I p)
  let P : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
    { toPartialEquiv :=
        { toFun := F
          invFun := inv
          source := metricTangentBall (I := I) g p r
          target := F '' metricTangentBall (I := I) g p r
          map_source' := by
            intro x hx
            exact ⟨x, hx, rfl⟩
          map_target' := by
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            rw [hinvLeft x hx]
            exact hx
          left_inv' := by
            intro x hx
            exact hinvLeft x hx
          right_inv' := by
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            rw [hinvLeft x hx] }
      open_source := isOpen_metricTangentBall (I := I) g p r
      open_target := hopen
      contMDiffOn_toFun := by simpa only [F] using hsmooth
      contMDiffOn_invFun := hinvSmooth }
  have hlocal : IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ F (v : E) := by
    change IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (P : E → M) (v : E)
    exact PartialDiffeomorph.isLocalDiffeomorphAt
      (I := 𝓘(ℝ, E)) (J := I) (M := E) (N := M) (n := ∞) P hv
  have huniq : ∀ w : TangentSpace I p,
      IsMinimizingUpTo (I := I) g hg p w 1 →
        expMapGlobal (I := I) g hg p w =
          expMapGlobal (I := I) g hg p (v : TangentSpace I p) → w = v := by
    intro w hw hweq
    have hdistv : dist p (expMapGlobal (I := I) g hg p
        (v : TangentSpace I p)) =
        Real.sqrt (g.metricInner p (v : TangentSpace I p) v) := by
      simpa only [IsMinimizingUpTo,
        globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p
          (v : TangentSpace I p) 1, one_smul, mul_one] using hmin
    have hdistw : dist p (expMapGlobal (I := I) g hg p w) =
        Real.sqrt (g.metricInner p w w) := by
      simpa only [IsMinimizingUpTo,
        globalGeodesic_eq_expMapGlobal_smul (I := I) g hg p w 1,
        one_smul, mul_one] using hw
    have hnormeq : Real.sqrt (g.metricInner p w w) =
        Real.sqrt (g.metricInner p (v : TangentSpace I p) v) := by
      calc
        Real.sqrt (g.metricInner p w w) =
            dist p (expMapGlobal (I := I) g hg p w) := hdistw.symm
        _ = dist p (expMapGlobal (I := I) g hg p
            (v : TangentSpace I p)) := by rw [hweq]
        _ = Real.sqrt (g.metricInner p (v : TangentSpace I p) v) := hdistv
    have hwball : w ∈ metricTangentBall (I := I) g p r := by
      change Real.sqrt (g.metricInner p w w) < r
      rw [hnormeq]
      exact hv
    have hEq : F (w : E) = F v := by simpa only [F] using hweq
    have := hinj hwball hv hEq
    exact this
  exact ⟨hmin, huniq, by simpa only [F] using hlocal⟩

/-- **Math.** If the fixed model norm already is the metric norm at `p`, the two ball
predicates are literally the same.  This is the missing hypothesis in the
unrestricted metric/book radius remark. -/
theorem metricTangentBall_eq_modelBall_of_norm_compat
    (g : RiemannianMetric I M) (p : M)
    (hnorm : ∀ v : E,
      Real.sqrt (g.metricInner p (v : TangentSpace I p) v) = ‖v‖) (r : ℝ) :
    metricTangentBall (I := I) g p r = Metric.ball (0 : E) r := by
  ext v
  rw [mem_metricTangentBall, Metric.mem_ball, dist_zero_right, hnorm]

/-- **Math.** Under norm compatibility, replacing the model ball by the metric ball does
not change the differential-geometric radius predicate. -/
theorem metricExpBallDiffeomorph_iff_of_norm_compat
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (hnorm : ∀ v : E,
      Real.sqrt (g.metricInner p (v : TangentSpace I p) v) = ‖v‖) (r : ℝ) :
    metricExpBallDiffeomorph (I := I) g hg p r ↔
      expBallDiffeomorph (I := I) g hg p r := by
  rw [metricExpBallDiffeomorph, expBallDiffeomorph,
    metricTangentBall_eq_modelBall_of_norm_compat (I := I) g p hnorm r]

/-- **Math.** Consequently, the corrected metric-ball radius agrees with the existing
book radius whenever the model norm is explicitly identified with `g_p`. -/
theorem metricBookInjectivityRadius_eq_bookInjectivityRadius_of_norm_compat
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (hnorm : ∀ v : E,
      Real.sqrt (g.metricInner p (v : TangentSpace I p) v) = ‖v‖) :
    metricBookInjectivityRadius (I := I) g hg p =
      bookInjectivityRadius (I := I) g hg p := by
  unfold metricBookInjectivityRadius bookInjectivityRadius
  apply le_antisymm
  · refine iSup_le fun r => ?_
    let s : {s : ℝ // expBallDiffeomorph (I := I) g hg p s} :=
      ⟨r, (metricExpBallDiffeomorph_iff_of_norm_compat
        (I := I) g hg p hnorm r).mp r.property⟩
    exact le_iSup (fun t : {t : ℝ // expBallDiffeomorph (I := I) g hg p t} =>
      ENNReal.ofReal (t : ℝ)) s
  · refine iSup_le fun r => ?_
    let s : {s : ℝ // metricExpBallDiffeomorph (I := I) g hg p s} :=
      ⟨r, (metricExpBallDiffeomorph_iff_of_norm_compat
        (I := I) g hg p hnorm r).mpr r.property⟩
    exact le_iSup (fun t : {t : ℝ // metricExpBallDiffeomorph (I := I) g hg p t} =>
      ENNReal.ofReal (t : ℝ)) s

end MorganTianLib

end

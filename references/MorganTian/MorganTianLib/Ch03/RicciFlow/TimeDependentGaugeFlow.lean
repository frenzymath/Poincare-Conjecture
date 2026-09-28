import MorganTianLib.Ch02.FlowBox

/-!
# Morgan--Tian Ch. 3 -- the non-autonomous Hamilton gauge flow

The DeTurck gauge vector field depends on time.  This file records the
standard autonomous suspension on `M x R`: a smooth time-dependent section
`V` is lifted to the vector field `(V,1)`.  Morgan--Tian's compact flow-box
theorem then gives one uniform box through the compact slice `M x {t₀}`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Function Riemannian

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Smooth time-dependent sections -/

/-- **Math.** A smooth time-dependent tangent vector field on `M`.

The section witness is stated directly in the tangent bundle.  This is the
intrinsic regularity needed by the suspension construction; no fixed chart or
coordinate representative is part of the data.
-/
structure SmoothTimeDependentVectorField where
  toFun : (q : M × ℝ) → TangentSpace I q.1
  smooth : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
    (fun q => (⟨q.1, toFun q⟩ : TangentBundle I M))

namespace SmoothTimeDependentVectorField

instance : CoeFun (SmoothTimeDependentVectorField (I := I) (M := M))
    (fun _ => (q : M × ℝ) → TangentSpace I q.1) :=
  ⟨SmoothTimeDependentVectorField.toFun⟩

@[simp] theorem coe_mk (f : (q : M × ℝ) → TangentSpace I q.1) (h) :
    ⇑(⟨f, h⟩ : SmoothTimeDependentVectorField (I := I) (M := M)) = f :=
  rfl

end SmoothTimeDependentVectorField

/-! ## The autonomous suspension -/

/-- **Math.** The autonomous suspension of a time-dependent field, with unit speed in
the time coordinate. -/
noncomputable def SmoothTimeDependentVectorField.suspension
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) :
    SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) where
  toFun := fun q => (V q, (1 : ℝ))
  smooth := by
    have hV : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : M × ℝ => (⟨q.1, V q⟩ : TangentBundle I M)) :=
      V.smooth
    let hone : SmoothVectorField 𝓘(ℝ, ℝ) ℝ :=
      SmoothVectorField.const (1 : ℝ)
    have htime : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : M × ℝ => (⟨q.2, hone q.2⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      hone.smooth.comp contMDiff_snd
    exact contMDiff_equivTangentBundleProd_symm.comp (hV.prodMk htime)

@[simp] theorem suspension_apply
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) (q : M × ℝ) :
    V.suspension q = (V q, (1 : ℝ)) :=
  rfl

@[simp] theorem suspension_time_derivative
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) (q : M × ℝ) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) (Prod.snd : M × ℝ → ℝ) q
      (V.suspension q) = 1 := by
  rw [mfderiv_snd]
  change (V.suspension q).2 = 1
  rfl

/-! ## Compact-slice flow boxes -/

/-- **Math.** The data produced by the suspended flow-box argument near a time slice.
The `integral_curve` field is retained explicitly because later gauge
arguments need the ODE, while `time_coord` records the non-autonomous
reparametrisation `t₀ + s`.
-/
structure TimeDependentFlowBox
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) (t₀ : ℝ) where
  eta : ℝ
  U : Set (M × ℝ)
  Φ : (M × ℝ) → ℝ → (M × ℝ)
  eta_pos : 0 < eta
  isOpen_U : IsOpen U
  slice_subset : (Set.univ : Set M) ×ˢ ({t₀} : Set ℝ) ⊆ U
  apply_zero : ∀ x ∈ U, Φ x 0 = x
  integral_curve : ∀ x ∈ U,
    IsMIntegralCurveOn (Φ x) (fun q => V.suspension q) (Ioo (-eta) eta)
  continuousOn : ContinuousOn ↿Φ (U ×ˢ Ioo (-eta) eta)
  time_coord : ∀ x ∈ U, ∀ s ∈ Ioo (-eta) eta,
    (Φ x s).2 = x.2 + s

private theorem time_coord_of_integral_curve
    (V : SmoothTimeDependentVectorField (I := I) (M := M))
    {eta : ℝ} (heta : 0 < eta) {U : Set (M × ℝ)}
    {Φ : (M × ℝ) → ℝ → (M × ℝ)}
    (hzero : ∀ x ∈ U, Φ x 0 = x)
    (hcurve : ∀ x ∈ U,
      IsMIntegralCurveOn (Φ x) (fun q => V.suspension q) (Ioo (-eta) eta))
    {x : M × ℝ} (hx : x ∈ U) {s : ℝ} (hs : s ∈ Ioo (-eta) eta) :
    (Φ x s).2 = x.2 + s := by
  have hderiv : ∀ u ∈ Ioo (-eta) eta,
      HasDerivWithinAt (fun r => (Φ x r).2 - (x.2 + r))
        0 (Ioo (-eta) eta) u := by
    intro u hu
    have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
        (Φ x) u ((1 : ℝ →L[ℝ] ℝ).smulRight (V.suspension (Φ x u))) :=
      (hcurve x hx u hu).hasMFDerivAt (Ioo_mem_nhds hu.1 hu.2)
    have htime : HasDerivAt (fun r => (Φ x r).2) 1 u := by
      have hcomp :=
        MorganTianLib.hasDerivAt_comp_of_hasMFDerivAt
          (M := M × ℝ) (I := I.prod 𝓘(ℝ, ℝ))
          (F := (Prod.snd : M × ℝ → ℝ)) contMDiff_snd hγ
      convert hcomp using 1
      exact (suspension_time_derivative V (Φ x u)).symm
    have hlin : HasDerivAt (fun r : ℝ => x.2 + r) 1 u :=
      (hasDerivAt_id u).const_add x.2
    have hsub' := htime.sub hlin
    have hfun :
        (fun r => (Φ x r).2 - (x.2 + r)) =
          (fun r => (Φ x r).2) - (fun r => x.2 + r) := by
      funext r
      rfl
    have hsub : HasDerivAt
        (fun r => (Φ x r).2 - (x.2 + r)) 0 u := by
      rw [hfun]
      simpa only [sub_self] using hsub'
    exact hsub.hasDerivWithinAt
  have h0mem : (0 : ℝ) ∈ Ioo (-eta) eta :=
    ⟨neg_neg_iff_pos.mpr heta, heta⟩
  have hbound :
      ‖((Φ x s).2 - (x.2 + s)) - ((Φ x 0).2 - (x.2 + 0))‖ ≤
        0 * ‖s - 0‖ :=
    (convex_Ioo (-eta) eta).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun r => (Φ x r).2 - (x.2 + r)) (f' := fun _ => 0)
      hderiv (fun _ _ => by simp) h0mem hs
  rw [zero_mul, hzero x hx] at hbound
  have hzero' := norm_le_zero_iff.mp hbound
  linarith

/-- **Math.** A uniform smooth flow box for a time-dependent vector field through the
compact slice `M × {t₀}`. -/
theorem exists_timeDependentFlowBox [CompactSpace M]
    (V : SmoothTimeDependentVectorField (I := I) (M := M)) (t₀ : ℝ) :
    Nonempty (TimeDependentFlowBox (I := I) (M := M) V t₀) := by
  let K : Set (M × ℝ) := (Set.univ : Set M) ×ˢ ({t₀} : Set ℝ)
  have hK : IsCompact K := by
    dsimp [K]
    exact isCompact_univ.prod isCompact_singleton
  obtain ⟨eta, U, Φ, heta, hopen, hKsub, hzero, hcurve, hcont⟩ :=
    MorganTianLib.exists_localFlow_of_isCompact V.suspension hK
  have htime : ∀ x ∈ U, ∀ s ∈ Ioo (-eta) eta,
      (Φ x s).2 = x.2 + s := by
    intro x hx s hs
    exact time_coord_of_integral_curve V heta hzero hcurve hx hs
  exact ⟨⟨eta, U, Φ, heta, hopen, hKsub, hzero, hcurve, hcont, htime⟩⟩

/-- **Math.** Along a trajectory starting on the distinguished slice, the
second coordinate is exactly `t₀ + s`. -/
theorem TimeDependentFlowBox.time_coord_of_mem_slice
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    {x : M × ℝ}
    (hx : x ∈ (Set.univ : Set M) ×ˢ ({t₀} : Set ℝ))
    {s : ℝ} (hs : s ∈ Ioo (-B.eta) B.eta) :
    (B.Φ x s).2 = t₀ + s := by
  rw [B.time_coord x (B.slice_subset hx) s hs]
  simpa only [mem_singleton_iff] using congrArg (fun r : ℝ => r + s) hx.2

/-- **Math.** The spatial projection of a suspended trajectory has the
manifold derivative prescribed by the time-dependent field. -/
theorem TimeDependentFlowBox.hasMFDerivAt_fst
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    {x : M × ℝ} (hx : x ∈ B.U)
    {s : ℝ} (hs : s ∈ Ioo (-B.eta) B.eta) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun r => (B.Φ x r).1) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V (B.Φ x s))) := by
  have hγ : HasMFDerivAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, ℝ))
      (B.Φ x) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight (V.suspension (B.Φ x s))) :=
    (B.integral_curve x hx s hs).hasMFDerivAt
      (Ioo_mem_nhds hs.1 hs.2)
  have hfst : HasMFDerivAt (I.prod 𝓘(ℝ, ℝ)) I
      (Prod.fst : M × ℝ → M) (B.Φ x s)
      (ContinuousLinearMap.fst ℝ (TangentSpace I (B.Φ x s).1)
        (TangentSpace 𝓘(ℝ, ℝ) (B.Φ x s).2)) :=
    _root_.hasMFDerivAt_fst (B.Φ x s)
  have hcomp := HasMFDerivAt.comp s hfst hγ
  convert hcomp using 1
  · rfl
  · ext
    rfl

/-- **Math.** On the distinguished slice, the preceding spatial derivative
uses the original time parameter `t₀ + s`. -/
theorem TimeDependentFlowBox.hasMFDerivAt_fst_of_mem_slice
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀)
    {x : M × ℝ}
    (hx : x ∈ (Set.univ : Set M) ×ˢ ({t₀} : Set ℝ))
    {s : ℝ} (hs : s ∈ Ioo (-B.eta) B.eta) :
  HasMFDerivAt 𝓘(ℝ, ℝ) I (fun r => (B.Φ x r).1) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (V ((B.Φ x s).1, t₀ + s))) := by
  have h := B.hasMFDerivAt_fst (B.slice_subset hx) hs
  have harg : B.Φ x s = ((B.Φ x s).1, t₀ + s) := by
    apply Prod.ext
    · rfl
    · exact B.time_coord_of_mem_slice hx hs
  rw [harg] at h
  exact h

/-! ## The spatial non-autonomous flow -/

/-- **Math.** The spatial flow starting at time `t₀`, obtained by restricting
the suspended flow to the compact initial slice. -/
def TimeDependentFlowBox.spatialFlow
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀) :
    M → ℝ → M :=
  fun p s => (B.Φ (p, t₀) s).1

/-- **Math.** The spatial flow starts at its prescribed point. -/
@[simp] theorem TimeDependentFlowBox.spatialFlow_zero
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀) (p : M) :
    B.spatialFlow p 0 = p := by
  change (B.Φ (p, t₀) 0).1 = p
  have hslice : (p, t₀) ∈ (Set.univ : Set M) ×ˢ ({t₀} : Set ℝ) := by
    simp
  exact congrArg Prod.fst (B.apply_zero (p, t₀) (B.slice_subset hslice))

/-- **Math.** The spatial flow solves the original non-autonomous ODE at
time `t₀ + s`. -/
theorem TimeDependentFlowBox.spatialFlow_hasMFDerivAt
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀) (p : M)
    {s : ℝ} (hs : s ∈ Ioo (-B.eta) B.eta) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (B.spatialFlow p) s
      ((1 : ℝ →L[ℝ] ℝ).smulRight
        (V (B.spatialFlow p s, t₀ + s))) := by
  change HasMFDerivAt 𝓘(ℝ, ℝ) I (fun r => (B.Φ (p, t₀) r).1) s
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      (V ((B.Φ (p, t₀) s).1, t₀ + s)))
  exact B.hasMFDerivAt_fst_of_mem_slice (x := (p, t₀)) (by simp) hs

/-- **Math.** The spatial non-autonomous flow depends jointly continuously
on its initial point and elapsed time. -/
theorem TimeDependentFlowBox.continuousOn_spatialFlow
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B : TimeDependentFlowBox (I := I) (M := M) V t₀) :
    ContinuousOn ↿B.spatialFlow
      ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta) := by
  let A : M × ℝ → (M × ℝ) × ℝ := fun q => ((q.1, t₀), q.2)
  have hA : Continuous A :=
    (continuous_fst.prodMk continuous_const).prodMk continuous_snd
  have hmaps : MapsTo A
      ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta)
      (B.U ×ˢ Ioo (-B.eta) B.eta) := by
    rintro q hq
    refine ⟨B.slice_subset (by simp [A]), hq.2⟩
  have hfull : ContinuousOn
      (fun q : M × ℝ => B.Φ (q.1, t₀) q.2)
      ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta) := by
    exact B.continuousOn.comp hA.continuousOn hmaps
  change ContinuousOn (fun q : M × ℝ => B.spatialFlow q.1 q.2)
    ((Set.univ : Set M) ×ˢ Ioo (-B.eta) B.eta)
  exact (continuous_fst.continuousOn.comp hfull (fun _ _ => mem_univ _)).congr
    (fun q hq => rfl)

/-! ## Uniqueness on the common flow-box interval -/

/-- **Math.** Two compact-slice flow boxes for the same time-dependent vector
field agree on the common interval of existence.  This is the non-autonomous
ODE uniqueness step used when local Hamilton-gauge charts are glued. -/
theorem TimeDependentFlowBox.eqOn_of_common
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B₁ B₂ : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (p : M) :
    EqOn (fun s => B₁.Φ (p, t₀) s) (fun s => B₂.Φ (p, t₀) s)
      (Ioo (-min B₁.eta B₂.eta) (min B₁.eta B₂.eta)) := by
  have hmin : 0 < min B₁.eta B₂.eta :=
    lt_min B₁.eta_pos B₂.eta_pos
  have hsub₁ : Ioo (-min B₁.eta B₂.eta) (min B₁.eta B₂.eta) ⊆
      Ioo (-B₁.eta) B₁.eta := by
    intro s hs
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_left _ _)) hs.1,
      lt_of_lt_of_le hs.2 (min_le_left _ _)⟩
  have hsub₂ : Ioo (-min B₁.eta B₂.eta) (min B₁.eta B₂.eta) ⊆
      Ioo (-B₂.eta) B₂.eta := by
    intro s hs
    exact ⟨lt_of_le_of_lt (neg_le_neg (min_le_right _ _)) hs.1,
      lt_of_lt_of_le hs.2 (min_le_right _ _)⟩
  have hslice₁ : (p, t₀) ∈ B₁.U := by
    exact B₁.slice_subset (by simp)
  have hslice₂ : (p, t₀) ∈ B₂.U := by
    exact B₂.slice_subset (by simp)
  have hV : CMDiff 1
      (fun q : M × ℝ =>
        (⟨q, V.suspension q⟩ :
          TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
    exact (V.suspension.smooth.of_le (by norm_num))
  have hcurve₁ : IsMIntegralCurveOn
      (B₁.Φ (p, t₀)) (fun q => V.suspension q)
      (Ioo (-min B₁.eta B₂.eta) (min B₁.eta B₂.eta)) :=
    (B₁.integral_curve (p, t₀) hslice₁).mono hsub₁
  have hcurve₂ : IsMIntegralCurveOn
      (B₂.Φ (p, t₀)) (fun q => V.suspension q)
      (Ioo (-min B₁.eta B₂.eta) (min B₁.eta B₂.eta)) :=
    (B₂.integral_curve (p, t₀) hslice₂).mono hsub₂
  have hzero : (B₁.Φ (p, t₀) 0) = (B₂.Φ (p, t₀) 0) := by
    rw [B₁.apply_zero (p, t₀) hslice₁, B₂.apply_zero (p, t₀) hslice₂]
  exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (mem_Ioo.mpr ⟨neg_neg_iff_pos.mpr hmin, hmin⟩) hV hcurve₁ hcurve₂ hzero

/-- **Math.** The spatial projections of two such flow boxes also agree on
their common interval. -/
theorem TimeDependentFlowBox.spatialFlow_eq_of_common
    {V : SmoothTimeDependentVectorField (I := I) (M := M)} {t₀ : ℝ}
    (B₁ B₂ : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (p : M) :
    EqOn (B₁.spatialFlow p) (B₂.spatialFlow p)
      (Ioo (-min B₁.eta B₂.eta) (min B₁.eta B₂.eta)) := by
  intro s hs
  exact congrArg Prod.fst (B₁.eqOn_of_common B₂ p hs)

/-! ## Inverse maps from overlapping time slices -/

/-- **Math.** If two compact-slice flow boxes are based at times related by
`t₁ = t₀ + s`, and both the forward and reverse elapsed times lie in their
respective boxes, then the two spatial flows are inverse at those times.

The proof translates the first suspended integral curve by `s`, intersects
its interval with the second box, and applies uniqueness on that open
interval.  No global completeness or parameter-dependent smoothness is
assumed. -/
theorem TimeDependentFlowBox.spatialFlow_comp_inverse_of_common
    {V : SmoothTimeDependentVectorField (I := I) (M := M)}
    {t₀ t₁ s : ℝ}
    (B₀ : TimeDependentFlowBox (I := I) (M := M) V t₀)
    (B₁ : TimeDependentFlowBox (I := I) (M := M) V t₁)
    (ht : t₁ = t₀ + s) (p : M)
    (hs₀ : s ∈ Ioo (-B₀.eta) B₀.eta)
    (hs₁ : -s ∈ Ioo (-B₁.eta) B₁.eta) :
    B₁.spatialFlow (B₀.spatialFlow p s) (-s) = p := by
  let a : ℝ := max (-B₁.eta) (-B₀.eta - s)
  let b : ℝ := min B₁.eta (B₀.eta - s)
  have ha0 : a < 0 := by
    dsimp [a]
    rw [max_lt_iff]
    constructor
    · exact neg_lt_zero.mpr B₁.eta_pos
    · linarith [hs₀.1]
  have h0b : 0 < b := by
    dsimp [b]
    rw [lt_min_iff]
    constructor
    · exact B₁.eta_pos
    · linarith [hs₀.2]
  have has : a < -s := by
    dsimp [a]
    rw [max_lt_iff]
    constructor
    · exact hs₁.1
    · linarith [B₀.eta_pos]
  have hsb : -s < b := by
    dsimp [b]
    rw [lt_min_iff]
    constructor
    · exact hs₁.2
    · linarith [B₀.eta_pos]
  have hslice₀ : (p, t₀) ∈ B₀.U := B₀.slice_subset (by simp)
  let q : M × ℝ := (B₀.spatialFlow p s, t₁)
  have hq : q ∈ B₁.U := by
    apply B₁.slice_subset
    simp [q]
  have hqeq : B₀.Φ (p, t₀) s = q := by
    apply Prod.ext
    · rfl
    · exact (B₀.time_coord_of_mem_slice (x := (p, t₀)) (by simp) hs₀).trans ht.symm
  have hshift_subset : Ioo a b ⊆
      {r : ℝ | r + s ∈ Ioo (-B₀.eta) B₀.eta} := by
    intro r hr
    change r + s ∈ Ioo (-B₀.eta) B₀.eta
    constructor
    · have hle : -B₀.eta - s ≤ a := by
        dsimp [a]
        exact le_max_right _ _
      linarith [hr.1]
    · have hle : b ≤ B₀.eta - s := by
        dsimp [b]
        exact min_le_right _ _
      linarith [hr.2]
  have hbox1_subset : Ioo a b ⊆ Ioo (-B₁.eta) B₁.eta := by
    intro r hr
    constructor
    · exact lt_of_le_of_lt (by
        dsimp [a]
        exact le_max_left _ _) hr.1
    · exact lt_of_lt_of_le hr.2 (by
        dsimp [b]
        exact min_le_left _ _)
  let γ₀ : ℝ → M × ℝ := B₀.Φ (p, t₀)
  have hcurve₀ : IsMIntegralCurveOn (γ₀ ∘ (· + s))
      (fun z => V.suspension z) (Ioo a b) := by
    have h := (B₀.integral_curve (p, t₀) hslice₀).comp_add s
    exact h.mono hshift_subset
  have hcurve₁ : IsMIntegralCurveOn (B₁.Φ q)
      (fun z => V.suspension z) (Ioo a b) :=
    (B₁.integral_curve q hq).mono hbox1_subset
  have hzero : (γ₀ ∘ (· + s)) 0 = B₁.Φ q 0 := by
    calc
      (γ₀ ∘ (· + s)) 0 = B₀.Φ (p, t₀) s := by
        simp [γ₀, Function.comp_apply]
      _ = q := hqeq
      _ = B₁.Φ q 0 := (B₁.apply_zero q hq).symm
  have hV : CMDiff 1
      (fun z : M × ℝ =>
        (⟨z, V.suspension z⟩ :
          TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ))) := by
    exact (V.suspension.smooth.of_le (by norm_num))
  have heq := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
    (t₀ := (0 : ℝ)) (a := a) (b := b)
    (mem_Ioo.mpr ⟨ha0, h0b⟩) hV hcurve₀ hcurve₁ hzero
  have hval := heq (mem_Ioo.mpr ⟨has, hsb⟩)
  have hfst := congrArg Prod.fst hval
  have hleft : ((γ₀ ∘ (· + s)) (-s)).1 = p := by
    simp [γ₀, Function.comp_apply, B₀.apply_zero (p, t₀) hslice₀]
  have hright : (B₁.Φ q (-s)).1 =
      B₁.spatialFlow (B₀.spatialFlow p s) (-s) := by
    rfl
  rw [hleft, hright] at hfst
  exact hfst.symm

end MorganTianLib

end

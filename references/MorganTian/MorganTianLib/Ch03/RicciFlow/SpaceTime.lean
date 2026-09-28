import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# Morgan--Tian Ch. 3 - product space-time

This module packages the product space-time of a Ricci flow. The carrier is
`M x J`, while `spaceTimeSet` places it in the smooth ambient manifold
`M x R`. Horizontal tangent vectors have zero time component, and the
horizontal metric at `(p, t)` is `g(t)` at `p`.

Parabolic neighborhoods deliberately freeze the spatial ball at their central
time. Their other time slices therefore need not be metric balls for the metric
at those times, exactly as in the book.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace ENNReal
open Bundle Manifold Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The product space-time associated to a manifold and a time set. -/
abbrev RicciFlowSpaceTime (M : Type*) (J : Set ℝ) :=
  M × J

/-- **Math.** Product space-time as the subset `M x J` of the ambient smooth
manifold `M x R`. -/
def spaceTimeSet (M : Type*) (J : Set ℝ) : Set (M × ℝ) :=
  (Set.univ : Set M) ×ˢ J

/-- **Math.** The ambient point corresponding to a point of product space-time. -/
def RicciFlowSpaceTime.toAmbient {J : Set ℝ}
    (q : RicciFlowSpaceTime M J) : M × ℝ :=
  (q.1, q.2.1)

/-- **Math.** The `t` time-slice of product space-time. -/
def timeSlice (J : Set ℝ) (t : J) : Set (RicciFlowSpaceTime M J) :=
  {q | q.2 = t}

/-- **Math.** The `t` time-slice, modeled on the original manifold `M`. -/
abbrev RicciFlowTimeSlice (M : Type*) (J : Set ℝ) (_t : J) :=
  M

/-- **Math.** The canonical identification of the `t` time-slice with `M`. -/
def timeSliceEquiv (J : Set ℝ) (t : J) :
    RicciFlowTimeSlice M J t ≃ ↥(timeSlice (M := M) J t) where
  toFun p := ⟨(p, t), rfl⟩
  invFun q := q.1.1
  left_inv _ := rfl
  right_inv q := by
    rcases q with ⟨⟨p, s⟩, hs⟩
    change s = t at hs
    subst s
    rfl

/-- **Math.** The smooth realization of the `t` time-slice inside ambient
product space-time. -/
def timeSliceEmbedding {J : Set ℝ} (t : J)
    (p : RicciFlowTimeSlice M J t) : M × ℝ :=
  (p, t.1)

omit [IsManifold I ∞ M] in
/-- **Math.** The canonical realization of a time-slice is smooth. -/
theorem timeSliceEmbedding_contMDiff {J : Set ℝ} (t : J) :
    ContMDiff I (I.prod 𝓘(ℝ, ℝ)) ∞ (timeSliceEmbedding (M := M) t) :=
  contMDiff_id.prodMk contMDiff_const

omit [IsManifold I ∞ M] in
/-- **Math.** The canonical realization of a time-slice is a topological
embedding. -/
theorem timeSliceEmbedding_isEmbedding {J : Set ℝ} (t : J) :
    Topology.IsEmbedding (timeSliceEmbedding (M := M) t) :=
  isEmbedding_graph continuous_const

omit [TopologicalSpace M] [IsManifold I ∞ M] in
/-- **Math.** The image of the canonical slice realization is `M x {t}`. -/
theorem range_timeSliceEmbedding {J : Set ℝ} (t : J) :
    Set.range (timeSliceEmbedding (M := M) t) =
      (Set.univ : Set M) ×ˢ ({t.1} : Set ℝ) := by
  ext q
  constructor
  · rintro ⟨p, rfl⟩
    simp [timeSliceEmbedding]
  · rintro ⟨_, ht⟩
    refine ⟨q.1, ?_⟩
    simp only [timeSliceEmbedding]
    exact Prod.ext rfl (Set.mem_singleton_iff.mp ht).symm

/-- **Math.** Under `timeSliceEquiv`, the Riemannian metric on the `t`
time-slice is `g(t)`. -/
abbrev timeSliceMetric (g : ℝ → RiemannianMetric I M) {J : Set ℝ} (t : J) :
    RiemannianMetric I (RicciFlowTimeSlice M J t) :=
  g t.1

/-- **Math.** The horizontal tangent fiber at a point of product space-time. -/
abbrev HorizontalTangent {J : Set ℝ} (q : RicciFlowSpaceTime M J) :=
  HorizontalTangentSpace I M q.toAmbient

/-- **Math.** A horizontal tangent vector at an ambient space-time point
includes into the product tangent space with zero time component. -/
def horizontalTangentInclusionAt (z : M × ℝ) :
    HorizontalTangentSpace I M z →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) z :=
  ContinuousLinearMap.inl ℝ (TangentSpace I z.1)
    (TangentSpace 𝓘(ℝ, ℝ) z.2)

/-- **Math.** A horizontal tangent vector includes into the tangent space of
the ambient product with zero time component. -/
abbrev horizontalTangentInclusion {J : Set ℝ} (q : RicciFlowSpaceTime M J) :
    HorizontalTangent (I := I) q →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) q.toAmbient :=
  horizontalTangentInclusionAt (I := I) q.toAmbient

omit [IsManifold I ∞ M] in
/-- **Math.** The derivative of the canonical time-slice realization is the
horizontal tangent inclusion. -/
theorem mfderiv_timeSliceEmbedding {J : Set ℝ} (t : J)
    (p : RicciFlowTimeSlice M J t) :
    mfderiv I (I.prod 𝓘(ℝ, ℝ)) (timeSliceEmbedding (M := M) t) p =
      horizontalTangentInclusionAt (I := I) (p, t.1) := by
  change mfderiv I (I.prod 𝓘(ℝ, ℝ)) (fun x : M => (x, t.1)) p =
    ContinuousLinearMap.inl ℝ (TangentSpace I p)
      (TangentSpace 𝓘(ℝ, ℝ) t.1)
  exact mfderiv_prod_left

omit [IsManifold I ∞ M] in
/-- **Math.** The horizontal tangent inclusion is fiberwise injective. -/
theorem horizontalTangentInclusion_injective {J : Set ℝ}
    (q : RicciFlowSpaceTime M J) :
    Function.Injective (horizontalTangentInclusion (I := I) q) := by
  intro v w h
  exact congrArg Prod.fst h

omit [IsManifold I ∞ M] in
/-- **Math.** The horizontal tangent bundle has the same rank as `TM`. -/
theorem horizontalTangent_finrank {J : Set ℝ} (q : RicciFlowSpaceTime M J) :
    Module.finrank ℝ (HorizontalTangent (I := I) q) = Module.finrank ℝ E :=
  rfl

private def zeroTimeTangent
    (q : TangentBundle I M × TangentBundle 𝓘(ℝ, ℝ) ℝ) :
    TangentBundle I M × TangentBundle 𝓘(ℝ, ℝ) ℝ :=
  (q.1, Bundle.zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ)) q.2.1)

private theorem zeroTimeTangent_contMDiff :
    ContMDiff (I.tangent.prod 𝓘(ℝ, ℝ).tangent)
      (I.tangent.prod 𝓘(ℝ, ℝ).tangent) ∞
      (zeroTimeTangent (I := I) (M := M)) := by
  apply contMDiff_fst.prodMk
  exact (Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ, ℝ))).comp
    ((Bundle.contMDiff_proj (TangentSpace 𝓘(ℝ, ℝ))).comp contMDiff_snd)

/-- **Math.** The fiberwise projection of `T(M x R)` onto the horizontal
tangent bundle. Its image consists exactly of vectors with zero time
component. -/
def horizontalProjection
    (q : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) :
    TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) :=
  (equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ).symm
    (zeroTimeTangent ((equivTangentBundleProd I M 𝓘(ℝ, ℝ) ℝ) q))

/-- **Math.** The horizontal bundle projection is smooth. -/
theorem horizontalProjection_contMDiff :
    ContMDiff (I.prod 𝓘(ℝ, ℝ)).tangent (I.prod 𝓘(ℝ, ℝ)).tangent ∞
      (horizontalProjection (I := I) (M := M)) := by
  exact contMDiff_equivTangentBundleProd_symm.comp
    (zeroTimeTangent_contMDiff.comp contMDiff_equivTangentBundleProd)

omit [IsManifold I ∞ M] in
/-- **Math.** The linear horizontal projection on one tangent fiber. -/
def horizontalProjectionAt (z : M × ℝ) :
    TangentSpace (I.prod 𝓘(ℝ, ℝ)) z →L[ℝ]
      TangentSpace (I.prod 𝓘(ℝ, ℝ)) z :=
  (ContinuousLinearMap.inl ℝ E ℝ) ∘L (ContinuousLinearMap.fst ℝ E ℝ)

omit [IsManifold I ∞ M] in
/-- **Math.** The image of the fiberwise projection is the horizontal tangent
space. -/
theorem range_horizontalProjectionAt (z : M × ℝ) :
    Set.range (horizontalProjectionAt (I := I) z) =
      Set.range (horizontalTangentInclusionAt (I := I) z) := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨w.1, rfl⟩
  · rintro ⟨w, rfl⟩
    exact ⟨(w, 0), rfl⟩

omit [IsManifold I ∞ M] in
/-- **Math.** A tangent vector is horizontal when its time component is zero. -/
def IsHorizontalTangentVector
    (q : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) : Prop :=
  q.2.2 = 0

omit [IsManifold I ∞ M] in
/-- **Math.** The horizontal projection acts by deleting the time component. -/
theorem horizontalProjection_apply
    (q : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) :
    horizontalProjection (I := I) (M := M) q = ⟨q.1, (q.2.1, 0)⟩ := by
  simp [horizontalProjection, zeroTimeTangent, equivTangentBundleProd]

omit [IsManifold I ∞ M] in
/-- **Math.** The horizontal bundle is the fixed-point bundle of its smooth
projection. -/
theorem horizontalProjection_fixed_iff
    (q : TangentBundle (I.prod 𝓘(ℝ, ℝ)) (M × ℝ)) :
    horizontalProjection (I := I) (M := M) q = q ↔
      IsHorizontalTangentVector q := by
  rw [horizontalProjection_apply]
  constructor
  · intro h
    exact (congrArg (fun v => v.2.2) h).symm
  · intro h
    rcases q with ⟨z, ⟨v, a⟩⟩
    change a = 0 at h
    subst a
    rfl

omit [IsManifold I ∞ M] in
/-- **Math.** The horizontal bundle is exactly the image of the smooth
fiberwise projection. -/
theorem range_horizontalProjection :
    Set.range (horizontalProjection (I := I) (M := M)) =
      {q | IsHorizontalTangentVector q} := by
  ext q
  constructor
  · rintro ⟨v, rfl⟩
    simp [IsHorizontalTangentVector, horizontalProjection_apply]
  · intro hq
    exact ⟨q, (horizontalProjection_fixed_iff q).2 hq⟩

/-- **Math.** The horizontal metric at `(p, t)` is the metric `g(t)` at `p`. -/
def horizontalMetric (g : ℝ → RiemannianMetric I M) {J : Set ℝ}
    (q : RicciFlowSpaceTime M J) (v w : HorizontalTangent (I := I) q) : ℝ :=
  (g q.2.1).metricInner q.1 v w

/-- **Math.** The horizontal metric on the `t` time-slice is exactly `g(t)`. -/
theorem horizontalMetric_timeSlice (g : ℝ → RiemannianMetric I M)
    {J : Set ℝ} (t : J) (p : RicciFlowTimeSlice M J t)
    (v w : TangentSpace I p) :
    horizontalMetric (I := I) g (p, t) v w =
      (timeSliceMetric g t).metricInner p v w :=
  rfl

section SmoothFlow

variable [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The horizontal metric of a Ricci flow is a smooth section on its
product space-time. -/
theorem IsRicciFlowOn.horizontalMetric_smooth
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} (h : IsRicciFlowOn g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection g) ((Set.univ : Set M) ×ˢ J) :=
  h.smooth

end SmoothFlow

end MorganTianLib

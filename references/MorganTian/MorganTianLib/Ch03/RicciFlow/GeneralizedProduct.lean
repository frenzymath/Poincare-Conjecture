import MorganTianLib.Ch03.RicciFlow.SpaceTime

/-!
# Morgan--Tian Ch. 3 - the product-flow bridge

The book observes that an ordinary Ricci flow is a generalized Ricci flow on
the product space-time.  The public `GeneralizedSpaceTime` interface in this
project deliberately fixes the ambient model to
`modelWithCornersEuclideanHalfSpace (n + 1)`.  A product `M x R`, however, is
naturally modelled on `I.prod 𝓘(ℝ, ℝ)` for the model `I` of `M`; identifying the
two models (and transporting the boundary charts for an arbitrary interval)
is a separate geometric construction.

This file records the canonical product data at its natural model and proves
the part of the bridge that is independent of that model identification.  In
particular, no `GeneralizedSpaceTime` or `GeneralizedRicciFlow` is silently
manufactured from a target-shaped existence assumption.  The final
model-equivalence construction remains an explicit downstream obligation.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Canonical product geometry -/

/-- **Math.** The product-space-time time function, namely projection to the
second coordinate. -/
def productSpaceTimeTime : M × ℝ → ℝ := Prod.snd

/-- **Math.** The positive unit time vector field on the product space-time.
Its horizontal component is zero and its time component is one. -/
noncomputable def productSpaceTimeTimeVector :
    SmoothVectorField (I.prod 𝓘(ℝ, ℝ)) (M × ℝ) where
  toFun := fun _ => (0, 1)
  smooth := by
    have hzero : ContMDiff (I.prod 𝓘(ℝ, ℝ)) (I.prod 𝓘(ℝ, E)) ∞
        (fun q : M × ℝ =>
          (⟨q.1, (0 : TangentSpace I q.1)⟩ : TangentBundle I M)) :=
      (SmoothVectorField.zero (I := I) (M := M)).smooth.comp contMDiff_fst
    let hone : SmoothVectorField 𝓘(ℝ, ℝ) ℝ :=
      SmoothVectorField.const (1 : ℝ)
    have htime : ContMDiff (I.prod 𝓘(ℝ, ℝ))
        (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun q : M × ℝ =>
          (⟨q.2, hone q.2⟩ :
            TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      hone.smooth.comp contMDiff_snd
    exact contMDiff_equivTangentBundleProd_symm.comp (hzero.prodMk htime)

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem productSpaceTimeTime_apply (q : M × ℝ) :
    productSpaceTimeTime (M := M) q = q.2 :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem productSpaceTimeTimeVector_apply (q : M × ℝ) :
    productSpaceTimeTimeVector (I := I) (M := M) q = (0, 1) :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The derivative of the product time function is the second
projection on each product tangent fiber. -/
theorem productSpaceTimeTime_mfderiv_timeVector_formula (q : M × ℝ) :
    mfderiv (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
        (productSpaceTimeTime (M := M)) q =
      ContinuousLinearMap.snd ℝ (TangentSpace I q.1)
        (TangentSpace 𝓘(ℝ, ℝ) q.2) := by
  exact mfderiv_snd

/-- **Math.** The product time-slice is the usual horizontal slice
`M x {t}`. -/
def productSpaceTimeSlice (t : ℝ) : Set (M × ℝ) :=
  (Set.univ : Set M) ×ˢ ({t} : Set ℝ)

omit [TopologicalSpace M] [SigmaCompactSpace M] [T2Space M] in
theorem mem_productSpaceTimeSlice_iff (q : M × ℝ) (t : ℝ) :
    q ∈ productSpaceTimeSlice (M := M) t ↔ q.2 = t := by
  simp [productSpaceTimeSlice]

/-! ## The flow contract on the product model -/

/-- **Math.** Product-form generalized Ricci-flow data for an ordinary flow.

The metric section is canonically `horizontalMetricSection g`; its two fields
are exactly the joint smoothness and the ordinary Ricci-flow equation on the
chosen time set.  The geometric time function and vector field are the
canonical definitions above.  This is a data contract with a checked
constructor: the constructor below obtains all fields from `IsRicciFlowOn`. -/
structure ProductGeneralizedRicciFlow
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop where
  /-- The time set is an interval. -/
  time_ordConnected : J.OrdConnected
  /-- The time interval has at least two points. -/
  time_nontrivial : J.Nontrivial
  metric_smooth : IsSmoothMetricFamilyOn (I := I) (M := M) g J
  ricci_equation : IsRicciFlowEquationOn (I := I) (M := M) g J

/-- **Math.** Every ordinary Ricci flow supplies the product-form generalized
Ricci-flow data. -/
theorem ProductGeneralizedRicciFlow.of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn (I := I) (M := M) g J) :
    ProductGeneralizedRicciFlow (I := I) (M := M) g J := by
  exact ⟨hflow.ordConnected, hflow.nontrivial, hflow.smooth, hflow.equation⟩

/-- **Math.** The product-flow contract retains exactly the ordinary Ricci-flow
interval and equation data. -/
theorem ProductGeneralizedRicciFlow.to_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (h : ProductGeneralizedRicciFlow (I := I) (M := M) g J) :
    IsRicciFlowOn (I := I) (M := M) g J := by
  exact ⟨h.time_ordConnected, h.time_nontrivial, h.metric_smooth, h.ricci_equation⟩

/-- **Math.** The metric section used by the product-flow bridge is the
horizontal metric induced by the ordinary family. -/
def ProductGeneralizedRicciFlow.metricSection
    {g : ℝ → RiemannianMetric I M} :
    (M × ℝ) → TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M × ℝ =>
        HorizontalTangentSpace I M q →L[ℝ]
          HorizontalTangentSpace I M q →L[ℝ] ℝ) :=
  MorganTianLib.horizontalMetricSection (I := I) (M := M) g

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
@[simp]
theorem ProductGeneralizedRicciFlow.metricSection_apply
    {g : ℝ → RiemannianMetric I M} (q : M × ℝ) :
    (ProductGeneralizedRicciFlow.metricSection (I := I) (M := M) (g := g) q).2 =
      (g q.2).inner q.1 :=
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The metric section exposed by the product bridge is definitionally
the canonical horizontal metric section of the ordinary family. -/
theorem ProductGeneralizedRicciFlow.metricSection_eq_horizontalMetricSection
    {g : ℝ → RiemannianMetric I M} (q : M × ℝ) :
    ProductGeneralizedRicciFlow.metricSection (I := I) (M := M) (g := g) q =
      MorganTianLib.horizontalMetricSection (I := I) (M := M) g q :=
  rfl

/-- **Math.** The smooth metric-section field in a product flow is precisely
the smoothness field supplied by the ordinary flow. -/
theorem ProductGeneralizedRicciFlow.metricSection_smooth
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (h : ProductGeneralizedRicciFlow (I := I) (M := M) g J) :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (ProductGeneralizedRicciFlow.metricSection (I := I) (M := M) (g := g))
      ((Set.univ : Set M) ×ˢ J) :=
  h.metric_smooth

/-- **Math.** The equation field in the product-flow bridge is exactly the
ordinary metric evolution equation on the time set. -/
theorem ProductGeneralizedRicciFlow.metricSection_ricci_equation
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (h : ProductGeneralizedRicciFlow (I := I) (M := M) g J) :
    IsRicciFlowEquationOn (I := I) (M := M) g J :=
  h.ricci_equation

end MorganTianLib

end

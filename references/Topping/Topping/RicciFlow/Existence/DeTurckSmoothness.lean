import Topping.RicciFlow.Existence.Linearisation
import Topping.Riemannian.FrameTrace
import Topping.Riemannian.SmoothTensor
import DoCarmoLib.Riemannian.TensorBundle.MusicalIso
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation

/-!
# Smooth components of the Ricci and DeTurck operators

The fixed-frame symbol calculation in `Linearisation` is independent of the
regularity needed by the geometric operator.  This file supplies that
regularity directly from the smooth metric pairing and the smooth Ricci tensor
producer.  In particular, the DeTurck vector-field predicate is retained as an
explicit source-facing contract; no smoothness assumption is hidden in it.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## The metric-dual DeTurck field

The one-form `δG_g(T)` is represented by an arbitrary tuple-valued field in
the basic tensor API.  A chosen smooth DeTurck vector field is therefore more
than notation: its duality equation forces the one-form to be pointwise
linear, and determines the field uniquely.  These elementary producers make
that dependency explicit without asserting that the resulting pointwise field
is smooth.
-/

omit [I.Boundaryless] in
/-- **Math.** A DeTurck duality witness forces pointwise linearity of the
one-form `δG_g(T)`.  This is the missing algebraic premise needed to identify
the witness with the pointwise metric dual. -/
theorem isPointwiseLinear_deTurckOneForm_of_isDeTurckVectorFieldFor
    (g T : RiemannianMetric I M) (V : SmoothVectorField I M)
    (hV : IsDeTurckVectorFieldFor g T V) (p : M) :
    IsPointwiseLinear T (deTurckOneForm g T) p := by
  constructor
  · intro v w
    change oneFormCovec g (deTurckOneForm g T) p (v + w) =
      oneFormCovec g (deTurckOneForm g T) p v +
        oneFormCovec g (deTurckOneForm g T) p w
    calc
      oneFormCovec g (deTurckOneForm g T) p (v + w) =
          T.metricInner p (V p) (v + w) := (hV p (v + w)).symm
      _ = T.metricInner p (V p) v + T.metricInner p (V p) w :=
        T.metricInner_add_right p (V p) v w
      _ = oneFormCovec g (deTurckOneForm g T) p v +
          oneFormCovec g (deTurckOneForm g T) p w := by
        rw [hV p v, hV p w]
  · intro c v
    change oneFormCovec g (deTurckOneForm g T) p (c • v) =
      c * oneFormCovec g (deTurckOneForm g T) p v
    calc
      oneFormCovec g (deTurckOneForm g T) p (c • v) =
          T.metricInner p (V p) (c • v) := (hV p (c • v)).symm
      _ = c * T.metricInner p (V p) v := T.metricInner_smul_right p c (V p) v
      _ = c * oneFormCovec g (deTurckOneForm g T) p v := by
        rw [hV p v]

omit [I.Boundaryless] in
/-- **Math.** The chosen DeTurck vector field is the pointwise `T`-metric dual
of `δG_g(T)`. -/
theorem deTurckVectorField_eq_oneFormSharp_of_isDeTurckVectorFieldFor
    (g T : RiemannianMetric I M) (V : SmoothVectorField I M)
    (hV : IsDeTurckVectorFieldFor g T V) :
    ∀ p : M, V p = oneFormSharp T (deTurckOneForm g T) p := by
  intro p
  have hlin := isPointwiseLinear_deTurckOneForm_of_isDeTurckVectorFieldFor
    g T V hV p
  apply (T.metricInner_eq_iff_eq p _ _).mp
  intro w
  rw [metricInner_oneFormSharp T (deTurckOneForm g T) p hlin w]
  simpa [oneFormCovec] using hV p w

/-! The next theorem packages the canonical pointwise candidate.  Its smooth
status is deliberately left to the separate section-space producer. -/

def deTurckVectorFieldCandidate (g T : RiemannianMetric I M) (p : M) :
    TangentSpace I p :=
  oneFormSharp T (deTurckOneForm g T) p

/-! ## A smooth section producer for the metric dual

`CovTensorField` is intentionally an unbundled operation on global smooth
vector fields.  To feed its pointwise dual to the Riesz-section engine we must
make the two missing facts explicit: the operation is tensorial in its single
slot, and its components on smooth fields are smooth.  The first fact turns
`oneFormCovec` into a genuine continuous linear functional; the second fact is
then exactly what the chart-frame Riesz producer consumes.
-/

omit [I.Boundaryless] in
/-- **Math.** A pointwise multilinear covariant `1`-tensor gives a linear
functional on each tangent fibre (the `oneFormCovec` representation agrees with
the tensor's `pointwiseValue`). -/
theorem isPointwiseLinear_of_isPointwiseMultilinear
    (g : RiemannianMetric I M) (om : CovTensorField I M 1) (p : M)
    (hA : IsPointwiseMultilinear om p) :
    IsPointwiseLinear g om p := by
  refine ⟨?_, ?_⟩
  · intro v w
    have h := hA.add 0 (fun _ => v) v w
    change pointwiseValue om p (fun _ => v + w) =
      pointwiseValue om p (fun _ => v) + pointwiseValue om p (fun _ => w)
    have huv : Function.update (fun _ : Fin 1 => v) 0 (v + w) =
        (fun _ => v + w) := by
      funext i
      fin_cases i
      rfl
    have hu : Function.update (fun _ : Fin 1 => v) 0 v =
        (fun _ => v) := by
      funext i
      fin_cases i
      rfl
    have hw : Function.update (fun _ : Fin 1 => v) 0 w =
        (fun _ => w) := by
      funext i
      fin_cases i
      rfl
    calc
      pointwiseValue om p (fun _ => v + w) =
          pointwiseValue om p (Function.update (fun _ : Fin 1 => v) 0 (v + w)) := by
            rw [huv]
      _ = pointwiseValue om p (Function.update (fun _ : Fin 1 => v) 0 v) +
          pointwiseValue om p (Function.update (fun _ : Fin 1 => v) 0 w) := h
      _ = pointwiseValue om p (fun _ => v) + pointwiseValue om p (fun _ => w) := by
            rw [hu, hw]
  · intro c v
    have h := hA.smul 0 (fun _ => v) c v
    change pointwiseValue om p (fun _ => c • v) =
      c * pointwiseValue om p (fun _ => v)
    have huv : Function.update (fun _ : Fin 1 => v) 0 (c • v) =
        (fun _ => c • v) := by
      funext i
      fin_cases i
      rfl
    have hu : Function.update (fun _ : Fin 1 => v) 0 v =
        (fun _ => v) := by
      funext i
      fin_cases i
      rfl
    calc
      pointwiseValue om p (fun _ => c • v) =
          pointwiseValue om p (Function.update (fun _ : Fin 1 => v) 0 (c • v)) := by
            rw [huv]
      _ = c * pointwiseValue om p (Function.update (fun _ : Fin 1 => v) 0 v) := h
      _ = c * pointwiseValue om p (fun _ => v) := by rw [hu]

omit [I.Boundaryless] in
/-- **Math.** Package a pointwise-linear `oneFormCovec` as a continuous linear
functional.  Continuity is automatic on the finite-dimensional tangent fibre. -/
noncomputable def oneFormCovecContinuousLinearMap
    (g : RiemannianMetric I M) (om : CovTensorField I M 1) (p : M)
    (hlin : IsPointwiseLinear g om p) :
    TangentSpace I p →L[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : T2Space (TangentSpace I p) :=
    TopologicalSpace.t2Space_of_metrizableSpace
  LinearMap.toContinuousLinearMap
    { toFun := oneFormCovec g om p
      map_add' := hlin.1
      map_smul' := by
        intro c v
        simpa [smul_eq_mul] using hlin.2 c v }

omit [I.Boundaryless] in
@[simp] theorem oneFormCovecContinuousLinearMap_apply
    (g : RiemannianMetric I M) (om : CovTensorField I M 1) (p : M)
    (hlin : IsPointwiseLinear g om p) (v : TangentSpace I p) :
    oneFormCovecContinuousLinearMap g om p hlin v = oneFormCovec g om p v :=
  by
    simp [oneFormCovecContinuousLinearMap, LinearMap.coe_toContinuousLinearMap']

omit [I.Boundaryless] in
/-- **Math.** The basis-sum `oneFormSharp` is the Riesz inverse of the
continuous covector obtained from `oneFormCovec`. -/
theorem oneFormSharp_eq_metricRiesz
    (g : RiemannianMetric I M) (om : CovTensorField I M 1) (p : M)
    (hlin : IsPointwiseLinear g om p) :
    oneFormSharp g om p =
      g.metricRiesz p (oneFormCovecContinuousLinearMap g om p hlin) := by
  apply (g.metricInner_eq_iff_eq p _ _).mp
  intro w
  rw [metricInner_oneFormSharp g om p hlin w, g.metricRiesz_inner]
  simp [oneFormCovecContinuousLinearMap, LinearMap.coe_toContinuousLinearMap']

omit [I.Boundaryless] in
/-- **Math.** Tensoriality lets a chart-frame value of `oneFormCovec` be read
through any smooth extension agreeing with that frame at the base point. -/
theorem oneFormCovec_eq_apply_of_eq_at
    (g : RiemannianMetric I M) (om : CovTensorField I M 1) (p : M)
    (hA : IsPointwiseTensorial om p) (Z : SmoothVectorField I M)
    (v : TangentSpace I p) (hZ : Z p = v) :
    oneFormCovec g om p v = om (fun _ => Z) p := by
  unfold oneFormCovec
  symm
  apply hA
  intro i
  simp [hZ]

omit [I.Boundaryless] in
/-- **Math.** If a covariant `1`-tensor has smooth components and is pointwise
multilinear, its metric dual is a smooth tangent-bundle section. -/
theorem oneFormSharp_section_contMDiffAt_of_hasSmoothComponents
    (g : RiemannianMetric I M) (om : CovTensorField I M 1)
    (hA : ∀ p : M, IsPointwiseMultilinear om p)
    (hSmooth : HasSmoothComponents om) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, oneFormSharp g om y⟩ : TangentBundle I M)) p := by
  let hlin : ∀ y : M, IsPointwiseLinear g om y :=
    fun y => isPointwiseLinear_of_isPointwiseMultilinear g om y (hA y)
  let Φ : ∀ y : M, TangentSpace I y →L[ℝ] ℝ :=
    fun y => oneFormCovecContinuousLinearMap g om y (hlin y)
  have hx : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  have hRiesz :=
    Riemannian.Tensor.metricRiesz_section_contMDiffAt_of_within
      (I := I) g (α := p) hx (Φ := Φ) (by
        intro j
        obtain ⟨Z, hZ⟩ := Riemannian.exists_smoothVectorField_eventuallyEq
          (I := I)
          (σ := fun q => Riemannian.Tensor.chartBasisVecFiber (I := I) p j q)
          (s := (trivializationAt E (TangentSpace I) p).baseSet) hbaseopen
          (Riemannian.Tensor.chartBasisVec_contMDiffOn (I := I) p j) hx
        have hsmooth : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
            (om (fun _ => Z))
            (trivializationAt E (TangentSpace I) p).baseSet p :=
          (hSmooth (fun _ => Z) p).contMDiffWithinAt
        have heq :
            (fun y => Φ y
              (Riemannian.Tensor.chartBasisVecFiber (I := I) p j y))
              =ᶠ[nhds p] (om (fun _ => Z)) := by
          filter_upwards [hZ] with y hy
          rw [oneFormCovecContinuousLinearMap_apply]
          exact oneFormCovec_eq_apply_of_eq_at g om y (hA y).tensorial Z _ hy
        exact hsmooth.congr_of_eventuallyEq
          (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds)
  refine hRiesz.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall (fun y => by
    change (⟨y, oneFormSharp g om y⟩ : TangentBundle I M) =
      (⟨y, g.metricRiesz y (Φ y)⟩ : TangentBundle I M)
    congr 1
    exact (oneFormSharp_eq_metricRiesz g om y (hlin y)))

omit [I.Boundaryless] in
/-- **Math.** Produce the smooth DeTurck vector field from the genuine smooth
one-form data.  The two hypotheses are the remaining section-level inputs, not
a target-shaped smooth-vector-field assumption. -/
noncomputable def deTurckVectorFieldOfSmoothOneForm
    (g T : RiemannianMetric I M)
    (hA : ∀ p : M, IsPointwiseMultilinear (deTurckOneForm g T) p)
    (hSmooth : HasSmoothComponents (deTurckOneForm g T)) :
    SmoothVectorField I M where
  toFun := fun p => oneFormSharp T (deTurckOneForm g T) p
  smooth := fun p =>
    oneFormSharp_section_contMDiffAt_of_hasSmoothComponents T
      (deTurckOneForm g T) hA hSmooth p

omit [I.Boundaryless] in
/-- **Math.** The produced section satisfies the DeTurck metric-duality
equation, hence is an admissible witness for `deTurckModification`. -/
theorem isDeTurckVectorFieldFor_deTurckVectorFieldOfSmoothOneForm
    (g T : RiemannianMetric I M)
    (hA : ∀ p : M, IsPointwiseMultilinear (deTurckOneForm g T) p)
    (hSmooth : HasSmoothComponents (deTurckOneForm g T)) :
    IsDeTurckVectorFieldFor g T
      (deTurckVectorFieldOfSmoothOneForm g T hA hSmooth) := by
  intro p w
  exact metricInner_oneFormSharp T (deTurckOneForm g T) p
    (isPointwiseLinear_of_isPointwiseMultilinear T
      (deTurckOneForm g T) p (hA p)) w

/-- **Math.** The Ricci-flow tensor `-2 Ric(g)` has smooth components. -/
theorem hasSmoothComponents_ricciFlowOperator (g : RiemannianMetric I M) :
    HasSmoothComponents (ricciFlowOperator g) := by
  intro Y
  have hc : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => (-2 : ℝ)) :=
    contMDiff_const
  change ContMDiff I 𝓘(ℝ, ℝ) ∞
    (fun p => (-2 : ℝ) * ricciTensorField g Y p)
  convert hc.mul (hasSmoothComponents_ricciTensorField g Y) using 1
  rfl

omit [I.Boundaryless] in
/-- **Math.** The symmetric covariant derivative of a smooth vector field has
smooth components, by smoothness of the metric pairing. -/
theorem hasSmoothComponents_symmetricGradient
    (g : RiemannianMetric I M) (V : SmoothVectorField I M) :
    HasSmoothComponents (symmetricGradient g V) := by
  intro Y
  exact
    (g.metricInner_field_contMDiff
      (g.leviCivitaConnection.cov (Y 0) V) (Y 1)).add
      (g.metricInner_field_contMDiff
        (Y 0) (g.leviCivitaConnection.cov (Y 1) V))

/-- **Math.** The DeTurck modification has smooth components whenever its chosen
vector-field witness satisfies the source duality predicate. -/
theorem hasSmoothComponents_deTurckModification
    (g T : RiemannianMetric I M) (V : SmoothVectorField I M)
    (hV : IsDeTurckVectorFieldFor g T V) :
    HasSmoothComponents (deTurckModification g T V hV) := by
  intro Y
  exact
    (hasSmoothComponents_ricciFlowOperator g Y).add
      (hasSmoothComponents_symmetricGradient g V Y)

/-- **Math.** Pointwise, Topping's tensor-field DeTurck modification is the
Morgan--Tian Ricci--DeTurck variation.  The `hV` witness is retained because it
is part of the source-facing `deTurckModification` contract, although the
pointwise expansion itself does not use it. -/
theorem pointwiseValue_deTurckModification_eq_ricciDeTurckVariation
    (g T : RiemannianMetric I M) (V : SmoothVectorField I M)
    (hV : IsDeTurckVectorFieldFor g T V) (p : M)
    (v w : TangentSpace I p) :
    pointwiseValue (deTurckModification g T V hV) p ![v, w] =
      MorganTianLib.ricciDeTurckVariation g V p v w := by
  have hricci : ricciTensorAt g p v w =
      MorganTianLib.ricciTensorAt g p v w := by
    rw [ricciTensorAt_eq_ricciAt]
    exact MorganTianLib.ricciAt_leviCivita_eq_ricciTensorAt
      g (isLeviCivita_leviCivitaConnection g) p v w
  simp [pointwiseValue, deTurckModification, ricciFlowOperator,
    MorganTianLib.ricciDeTurckVariation,
    MorganTianLib.metricLieDerivativeAt,
    symmetricGradient, ricciTensorField,
    MorganTianLib.extendVector_apply, hricci]

#print axioms isPointwiseLinear_deTurckOneForm_of_isDeTurckVectorFieldFor
#print axioms deTurckVectorField_eq_oneFormSharp_of_isDeTurckVectorFieldFor
#print axioms oneFormSharp_section_contMDiffAt_of_hasSmoothComponents
#print axioms deTurckVectorFieldOfSmoothOneForm
#print axioms isDeTurckVectorFieldFor_deTurckVectorFieldOfSmoothOneForm
#print axioms hasSmoothComponents_ricciFlowOperator
#print axioms hasSmoothComponents_symmetricGradient
#print axioms hasSmoothComponents_deTurckModification
#print axioms pointwiseValue_deTurckModification_eq_ricciDeTurckVariation

end Topping

end

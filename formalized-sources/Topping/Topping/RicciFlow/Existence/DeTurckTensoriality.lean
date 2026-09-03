import Topping.Riemannian.SmoothTrace
import Topping.RicciFlow.Existence.Linearisation

/-!
# Tensoriality of the DeTurck one-form

`gravitationTensor` and `divergence` are represented in the basic Topping API
by maps on tuples of smooth vector fields.  This module records the genuine
two-field presentation of the gravitation tensor and feeds it through the
rank-three covariant-derivative/trace bridges.  The only section-level input
left explicit is smoothness of the metric trace of `metricTensorField T`.
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

/-! ### The two-field presentation -/

/-- **Math.** The two-field presentation of `G_g(metricTensorField T)`. -/
def gravitationTensorTwoField (g T : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) : M → ℝ :=
  fun q => gravitationTensor g (metricTensorField T)
    (fun i => if i = 0 then X else Y) q

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
@[simp] theorem gravitationTensorTwoField_apply
    (g T : RiemannianMetric I M) (X Y : SmoothVectorField I M) (q : M) :
    gravitationTensorTwoField g T X Y q =
      T.metricInner q (X q) (Y q)
        - (1 / 2 : ℝ) * trace₂ g (metricTensorField T) q
            * g.metricInner q (X q) (Y q) := by
  simp [gravitationTensorTwoField, gravitationTensor_apply, metricTensorField]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** The tuple and two-field presentations of the gravitation tensor agree. -/
theorem gravitationTensor_eq_twoField
    (g T : RiemannianMetric I M)
    (Y : Fin 2 → SmoothVectorField I M) (q : M) :
    gravitationTensor g (metricTensorField T) Y q =
      gravitationTensorTwoField g T (Y 0) (Y 1) q := by
  simp [gravitationTensorTwoField, gravitationTensor_apply, metricTensorField]

/-! ### Covariant tensor and smooth-component producers -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** `G_g(metricTensorField T)` is a genuine covariant two-tensor. -/
theorem isCovariantTensor2_gravitationTensorTwoField
    (g T : RiemannianMetric I M) :
    IsCovariantTensor2 (gravitationTensorTwoField g T) where
  add_left X₁ X₂ Y q := by
    simp only [gravitationTensorTwoField_apply, SmoothVectorField.add_apply,
      RiemannianMetric.metricInner_add_left]
    ring
  add_right X Y₁ Y₂ q := by
    simp only [gravitationTensorTwoField_apply, SmoothVectorField.add_apply,
      RiemannianMetric.metricInner_add_right]
    ring
  smul_left f hf X Y q := by
    simp only [gravitationTensorTwoField_apply, SmoothVectorField.smul_apply,
      RiemannianMetric.metricInner_smul_left]
    ring
  smul_right f hf X Y q := by
    simp only [gravitationTensorTwoField_apply, SmoothVectorField.smul_apply,
      RiemannianMetric.metricInner_smul_right]
    ring

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Smooth components of the two-field gravitation tensor from a smooth trace. -/
theorem gravitationTensorTwoField_contMDiff_of_trace
    (g T : RiemannianMetric I M)
    (htrace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (trace₂ g (metricTensorField T)))
    (X Y : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (gravitationTensorTwoField g T X Y) := by
  rw [show gravitationTensorTwoField g T X Y =
      fun q => T.metricInner q (X q) (Y q)
        - (1 / 2 : ℝ) * trace₂ g (metricTensorField T) q
            * g.metricInner q (X q) (Y q) from by
        funext q
        exact gravitationTensorTwoField_apply g T X Y q]
  exact (T.metricInner_field_contMDiff X Y).sub
    ((contMDiff_const.mul htrace).mul (g.metricInner_field_contMDiff X Y))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** Tuple-based smooth components of `G_g(metricTensorField T)`. -/
theorem hasSmoothComponents_gravitationTensor_of_trace
    (g T : RiemannianMetric I M)
    (htrace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (trace₂ g (metricTensorField T))) :
    HasSmoothComponents (gravitationTensor g (metricTensorField T)) := by
  intro Y
  have hXY := gravitationTensorTwoField_contMDiff_of_trace g T htrace
    (Y 0) (Y 1)
  have hrep : gravitationTensor g (metricTensorField T) Y =
      gravitationTensorTwoField g T (Y 0) (Y 1) := by
    funext q
    exact (gravitationTensor_eq_twoField g T Y q)
  rw [hrep]
  exact hXY

/-- **Math.** The gravitation tensor of two Riemannian metrics has smooth
components. -/
theorem hasSmoothComponents_gravitationTensor_metricTensorField
    (g T : RiemannianMetric I M) :
    HasSmoothComponents (gravitationTensor g (metricTensorField T)) :=
  hasSmoothComponents_gravitationTensor_of_trace g T
    (contMDiff_trace₂_metricTensorField g T)

/-! ### The DeTurck one-form boundary -/

omit [I.Boundaryless] in
/-- **Math.** The covariant derivative of `G_g(metricTensorField T)` is pointwise
multilinear whenever the metric trace has smooth components. -/
theorem isPointwiseMultilinear_covDeriv_gravitationTensor
    (g T : RiemannianMetric I M)
    (htrace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (trace₂ g (metricTensorField T)))
    (p : M) :
    IsPointwiseMultilinear
      (covDeriv g.leviCivitaConnection
        (gravitationTensor g (metricTensorField T))) p := by
  let S : SmoothVectorField I M → SmoothVectorField I M → (M → ℝ) :=
    gravitationTensorTwoField g T
  have hS : IsCovariantTensor2 S :=
    isCovariantTensor2_gravitationTensorTwoField g T
  have hsm : ∀ X Y, ContMDiff I 𝓘(ℝ, ℝ) ∞ (S X Y) := by
    intro X Y
    exact gravitationTensorTwoField_contMDiff_of_trace g T htrace X Y
  have hrep : ∀ (Y : Fin 2 → SmoothVectorField I M) (q : M),
      gravitationTensor g (metricTensorField T) Y q =
        S (Y 0) (Y 1) q := by
    intro Y q
    exact gravitationTensor_eq_twoField g T Y q
  exact isPointwiseMultilinear_covDeriv_of_isCovariantTensor2
    g.leviCivitaConnection S hS hsm
    (gravitationTensor g (metricTensorField T)) hrep p

/-! The trace producer itself is useful as a boundary adapter: callers that
already have a covariant-derivative witness need not reproduce the gravitation
representation or its smooth-trace assumptions. -/

omit [I.Boundaryless] in
/-- **Math.** A pointwise multilinear covariant derivative yields a pointwise
multilinear DeTurck one-form after the metric trace. -/
theorem isPointwiseMultilinear_deTurckOneForm_of_covariantDerivative
    (g T : RiemannianMetric I M)
    (hD : ∀ q : M, IsPointwiseMultilinear
      (covDeriv g.leviCivitaConnection
        (gravitationTensor g (metricTensorField T))) q)
    (p : M) :
    IsPointwiseMultilinear (deTurckOneForm g T) p := by
  change IsPointwiseMultilinear
    (divergence g g.leviCivitaConnection
      (gravitationTensor g (metricTensorField T))) p
  exact isPointwiseMultilinear_divergence_of_covariantDerivative
    g g.leviCivitaConnection hD p

omit [I.Boundaryless] in
/-- **Math.** A smooth metric trace gives pointwise multilinearity of the DeTurck
one-form, with no target-shaped vector-field assumption. -/
theorem isPointwiseMultilinear_deTurckOneForm_of_trace
    (g T : RiemannianMetric I M)
    (htrace : ContMDiff I 𝓘(ℝ, ℝ) ∞ (trace₂ g (metricTensorField T)))
    (p : M) :
    IsPointwiseMultilinear (deTurckOneForm g T) p := by
  apply isPointwiseMultilinear_deTurckOneForm_of_covariantDerivative g T
  intro q
  exact isPointwiseMultilinear_covDeriv_gravitationTensor g T htrace q

/-- **Math.** The DeTurck one-form is pointwise multilinear for every pair of
Riemannian metrics. -/
theorem isPointwiseMultilinear_deTurckOneForm
    (g T : RiemannianMetric I M) (p : M) :
    IsPointwiseMultilinear (deTurckOneForm g T) p :=
  isPointwiseMultilinear_deTurckOneForm_of_trace g T
    (contMDiff_trace₂_metricTensorField g T) p

#print axioms isCovariantTensor2_gravitationTensorTwoField
#print axioms hasSmoothComponents_gravitationTensor_of_trace
#print axioms hasSmoothComponents_gravitationTensor_metricTensorField
#print axioms isPointwiseMultilinear_deTurckOneForm_of_covariantDerivative
#print axioms isPointwiseMultilinear_deTurckOneForm_of_trace
#print axioms isPointwiseMultilinear_deTurckOneForm

end Topping

end

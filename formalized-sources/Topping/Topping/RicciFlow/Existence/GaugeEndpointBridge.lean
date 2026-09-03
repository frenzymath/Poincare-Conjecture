import Topping.RicciFlow.Existence.EndpointSmoothMetric
import Topping.RicciFlow.Existence.GaugePullback

/-!
# Fixed-gauge transport of endpoint data

The endpoint coefficient argument is naturally expressed in the tangent fibre
at a fixed base point.  A Hamilton gauge changes that fibre by the derivative
of a diffeomorphism.  This file records the resulting algebraic transport and
the corresponding one-sided limit theorem for a *fixed* gauge.  The gauge is
not allowed to depend on the endpoint parameter here; the moving-gauge limit
requires a separate continuity theorem for the diffeomorphism family.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Fibre transport -/

/-- **Math.** Pull an endpoint fibre form back along a fixed smooth
diffeomorphism.  Positivity is preserved because the differential of a
diffeomorphism is injective at every point.
-/
noncomputable def endpointFiberBilinearFormPullback
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (φ : Diffeomorph I I M M ∞) (p : M) :
    EndpointFiberBilinearForm (TangentSpace I p) := by
  let D : TangentSpace I p →L[ℝ] TangentSpace I (φ p) := mfderiv I I φ p
  have hD : Function.Injective D := by
    exact (φ.mfderivToContinuousLinearEquiv (by simp) p).injective
  exact
    { inner := fun v w => (B (φ p)).inner (D v) (D w)
      add_left := by
        intro v₁ v₂ w
        simp only [map_add]
        exact (B (φ p)).add_left (D v₁) (D v₂) (D w)
      smul_left := by
        intro c v w
        simp only [map_smul]
        exact (B (φ p)).smul_left c (D v) (D w)
      add_right := by
        intro v w₁ w₂
        simp only [map_add]
        exact (B (φ p)).add_right (D v) (D w₁) (D w₂)
      smul_right := by
        intro c v w
        simp only [map_smul]
        exact (B (φ p)).smul_right c (D v) (D w)
      symm := by
        intro v w
        exact (B (φ p)).symm (D v) (D w)
      pos := by
        intro v hv
        apply (B (φ p)).pos (D v)
        intro hzero
        apply hv
        apply hD
        simpa using hzero }

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem endpointFiberBilinearFormPullback_inner
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (φ : Diffeomorph I I M M ∞) (p : M)
    (v w : TangentSpace I p) :
    (endpointFiberBilinearFormPullback (I := I) B φ p).inner v w =
      (B (φ p)).inner (mfderiv I I φ p v) (mfderiv I I φ p w) := by
  rfl

/-! ## Quantitative transport -/

/-- **Math.** Two-sided quadratic comparison bounds on an endpoint field are
preserved by a fixed gauge, with the reference metric pulled back by the same
diffeomorphism.
-/
theorem endpointFiberBilinearFormPullback_bounds
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (g₀ : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞)
    {c C : ℝ}
    (hLower : ∀ (q : M) (x : TangentSpace I q),
      c * g₀.metricInner q x x ≤ (B q).inner x x)
    (hUpper : ∀ (q : M) (x : TangentSpace I q),
      (B q).inner x x ≤ C * g₀.metricInner q x x) :
    ∀ (p : M) (v : TangentSpace I p),
      c * (gaugePullbackMetric g₀ φ).metricInner p v v ≤
          (endpointFiberBilinearFormPullback B φ p).inner v v ∧
        (endpointFiberBilinearFormPullback B φ p).inner v v ≤
          C * (gaugePullbackMetric g₀ φ).metricInner p v v := by
  intro p v
  constructor
  · simpa only [gaugePullbackMetric_metricInner,
      MorganTianLib.gaugePullbackValue,
      endpointFiberBilinearFormPullback_inner] using
      hLower (φ p) (mfderiv I I φ p v)
  · simpa only [gaugePullbackMetric_metricInner,
      MorganTianLib.gaugePullbackValue,
      endpointFiberBilinearFormPullback_inner] using
      hUpper (φ p) (mfderiv I I φ p v)

/-! ## Endpoint-filter transport -/

/-- **Math.** A fixed gauge transports any fibrewise endpoint coefficient
limit to the corresponding coefficient of the concrete pullback metric.
The filter is arbitrary; in particular this specializes to the interior-left
filter used by the restart consumers.
-/
theorem tendsto_gaugePullbackMetric_metricInner_of_endpointField
    {ι : Type*} {l : Filter ι}
    {g : ι → RiemannianMetric I M}
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (φ : Diffeomorph I I M M ∞)
    (hLimit : ∀ (q : M) (x y : TangentSpace I q),
      Tendsto (fun i => (g i).metricInner q x y)
        l (𝓝 ((B q).inner x y)))
    (p : M) (v w : TangentSpace I p) :
    Tendsto (fun i => (gaugePullbackMetric (g i) φ).metricInner p v w)
      l (𝓝 ((endpointFiberBilinearFormPullback B φ p).inner v w)) := by
  simpa only [gaugePullbackMetric_metricInner,
    MorganTianLib.gaugePullbackValue,
    endpointFiberBilinearFormPullback_inner] using
    hLimit (φ p) (mfderiv I I φ p v) (mfderiv I I φ p w)

/-- **Math.** If an endpoint field is realized by a smooth endpoint metric,
the fixed-gauge pullback of that metric is the metric represented by the
transported endpoint fibre form, coefficientwise.
-/
theorem gaugePullbackMetric_smoothEndpointMetric_metricInner
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p)))
    (φ : Diffeomorph I I M M ∞) (p : M)
    (v w : TangentSpace I p) :
    (gaugePullbackMetric (smoothEndpointMetric gRef B hSmooth) φ).metricInner p v w =
      (endpointFiberBilinearFormPullback B φ p).inner v w := by
  simp only [gaugePullbackMetric_metricInner,
    MorganTianLib.gaugePullbackValue,
    smoothEndpointMetric_metricInner,
    endpointFiberBilinearFormPullback_inner]

/-- **Math.** The preceding coefficientwise identification turns the fixed-gauge
endpoint limit into convergence to the concrete pullback of the smooth
endpoint metric.
-/
theorem tendsto_gaugePullbackMetric_smoothEndpointMetric_of_endpointField
    {ι : Type*} {l : Filter ι}
    {g : ι → RiemannianMetric I M}
    (gRef : RiemannianMetric I M)
    (B : (q : M) → EndpointFiberBilinearForm (TangentSpace I q))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p)))
    (φ : Diffeomorph I I M M ∞)
    (hLimit : ∀ (q : M) (x y : TangentSpace I q),
      Tendsto (fun i => (g i).metricInner q x y)
        l (𝓝 ((B q).inner x y)))
    (p : M) (v w : TangentSpace I p) :
    Tendsto (fun i => (gaugePullbackMetric (g i) φ).metricInner p v w)
      l (𝓝 ((gaugePullbackMetric (smoothEndpointMetric gRef B hSmooth) φ).metricInner p v w)) := by
  rw [gaugePullbackMetric_smoothEndpointMetric_metricInner gRef B hSmooth φ p v w]
  exact tendsto_gaugePullbackMetric_metricInner_of_endpointField B φ hLimit p v w

#print axioms endpointFiberBilinearFormPullback
#print axioms endpointFiberBilinearFormPullback_bounds
#print axioms tendsto_gaugePullbackMetric_metricInner_of_endpointField
#print axioms gaugePullbackMetric_smoothEndpointMetric_metricInner
#print axioms tendsto_gaugePullbackMetric_smoothEndpointMetric_of_endpointField

end Topping

end

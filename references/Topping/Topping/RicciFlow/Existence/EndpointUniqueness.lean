import Topping.RicciFlow.Existence.EndpointSmoothMetric
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge

/-!
# Uniqueness of endpoint fibre forms

The endpoint coefficient argument chooses a limit on each tangent fibre.  The
limit is unique, so any two forms carrying the same coefficient-limit witness
are equal.  These lemmas are deliberately independent of the smooth endpoint
bootstrap: they apply before a base-point-dependent family is assembled.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Filter Riemannian

noncomputable section

namespace Topping

namespace EndpointFiberBilinearForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Extensionality for the fibre-local bilinear-form structure. -/
theorem ext
    {B₁ B₂ : EndpointFiberBilinearForm V}
    (h : ∀ v w : V, B₁.inner v w = B₂.inner v w) : B₁ = B₂ := by
  cases B₁ with
  | mk inner₁ add₁ smul₁ add₁' smul₁' symm₁ pos₁ =>
    cases B₂ with
    | mk inner₂ add₂ smul₂ add₂' smul₂' symm₂ pos₂ =>
      simp only at h
      have hinter : inner₁ = inner₂ := funext fun v => funext (h v)
      subst inner₂
      rfl

end EndpointFiberBilinearForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Two endpoint forms on a fixed tangent fibre are equal when they represent
the same one-sided coefficient limits. -/
theorem endpointFiberBilinearForm_eq_of_tendsto
    {g : ℝ → RiemannianMetric I M} {T : ℝ} (hT : 0 < T)
    {p : M} {B₁ B₂ : EndpointFiberBilinearForm (TangentSpace I p)}
    (h₁ : ∀ v w : TangentSpace I p,
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 (B₁.inner v w)))
    (h₂ : ∀ v w : TangentSpace I p,
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 (B₂.inner v w))) :
    B₁ = B₂ := by
  apply EndpointFiberBilinearForm.ext
  intro v w
  have hne : NeBot (nhdsWithin T (Iio T)) := by
    exact nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  exact tendsto_nhds_unique' hne (h₁ v w) (h₂ v w)

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The globally indexed endpoint field is pointwise unique. -/
theorem globalEndpointFiberBilinearForm_eq_of_tendsto
    {g : ℝ → RiemannianMetric I M} {T : ℝ} (hT : 0 < T)
    {B₁ B₂ : (p : M) → EndpointFiberBilinearForm (TangentSpace I p)}
    (h₁ : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B₁ p).inner v w)))
    (h₂ : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B₂ p).inner v w))) :
    B₁ = B₂ := by
  funext p
  apply endpointFiberBilinearForm_eq_of_tendsto hT
  · exact h₁ p
  · exact h₂ p

/-- **Math.** Smooth endpoint metrics realizing the same coefficient limits
are equal as bundled Riemannian metrics. -/
theorem smoothEndpointMetric_eq_of_same_limit
    {g : ℝ → RiemannianMetric I M} {T : ℝ} (hT : 0 < T)
    (gRef : RiemannianMetric I M)
    {B₁ B₂ : (p : M) → EndpointFiberBilinearForm (TangentSpace I p)}
    (hSmooth₁ : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B₁ p)))
    (hSmooth₂ : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B₂ p)))
    (h₁ : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B₁ p).inner v w)))
    (h₂ : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B₂ p).inner v w))) :
    smoothEndpointMetric gRef B₁ hSmooth₁ =
      smoothEndpointMetric gRef B₂ hSmooth₂ := by
  have hB : B₁ = B₂ :=
    globalEndpointFiberBilinearForm_eq_of_tendsto hT h₁ h₂
  subst B₂
  apply MorganTianLib.riemannianMetric_eq_of_metricInner_eq
  intro p v w
  simp only [smoothEndpointMetric_metricInner]


end Topping

end

import Topping.RicciFlow.Existence.EndpointMetric
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1

/-!
# Smooth endpoint metric reconstruction

The coefficient-limit argument first produces one positive bilinear form on
each tangent fibre.  This file performs the remaining bundled construction:
finite-dimensionality turns the forms into continuous linear maps, and an
explicit joint-smoothness witness turns the globally indexed field into a
`RiemannianMetric`.  No smoothness of endpoint coefficients is inferred from
pointwise limits; it remains the analytic input to the constructor.
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

/-! ## Fibrewise continuous-linear realization -/

namespace EndpointFiberBilinearForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

noncomputable def toLinearMap (B : EndpointFiberBilinearForm V) (v : V) :
    V →ₗ[ℝ] ℝ where
  toFun := B.inner v
  map_add' := B.add_right v
  map_smul' := by
    intro c w
    simpa [smul_eq_mul] using B.smul_right c v w

noncomputable def toContinuousLinearMap (B : EndpointFiberBilinearForm V) :
    V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => LinearMap.toContinuousLinearMap (B.toLinearMap v)
      map_add' := by
        intro v w
        ext z
        exact B.add_left v w z
      map_smul' := by
        intro c v
        ext z
        exact B.smul_left c v z }

@[simp] theorem toContinuousLinearMap_apply
    (B : EndpointFiberBilinearForm V) (v w : V) :
    B.toContinuousLinearMap v w = B.inner v w := rfl

@[simp] theorem toContinuousLinearMap_symm
    (B : EndpointFiberBilinearForm V) (v w : V) :
    B.toContinuousLinearMap v w = B.toContinuousLinearMap w v := by
  simp only [toContinuousLinearMap_apply]
  exact B.symm v w

end EndpointFiberBilinearForm

/-! ## Global smooth reconstruction -/

/- The tangent-fibre normed structures are induced by a reference metric.
Keeping this local instance inside the definition lets callers state the
smoothness hypothesis without carrying a second metric typeclass. -/
noncomputable def endpointInner
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (p : M) : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨gRef.toRiemannianMetric⟩
  exact (B p).toContinuousLinearMap

@[simp] theorem endpointInner_apply
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (p : M) (v w : TangentSpace I p) :
    endpointInner gRef B p v w = (B p).inner v w := by
  simp [endpointInner]

/-- **Math.** Construct a smooth positive-definite endpoint metric from a
globally indexed family of endpoint forms and its joint smoothness witness.
The reference metric supplies the existing tangent-fibre topologies; all
metric algebra and von Neumann boundedness are proved from the endpoint forms.
-/
noncomputable def smoothEndpointMetric
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p))) :
    RiemannianMetric I M := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨gRef.toRiemannianMetric⟩
  exact
    { inner := endpointInner gRef B
      symm := by
        intro p v w
        exact (B p).symm v w
      pos := by
        intro p v hv
        exact (B p).pos v hv
      isVonNBounded := by
        intro p
        exact isVonNBounded_of_posDef
          (endpointInner gRef B p)
          (fun v hv => (B p).pos v hv)
      contMDiff := hSmooth }

@[simp] theorem smoothEndpointMetric_metricInner
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p)))
    (p : M) (v w : TangentSpace I p) :
    (smoothEndpointMetric gRef B hSmooth).metricInner p v w = (B p).inner v w := by
  change endpointInner gRef B p v w = (B p).inner v w
  simp

theorem smoothEndpointMetric_tendsto_of_endpointField
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p)))
    (hLimit : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B p).inner v w))) :
    ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T))
        (𝓝 ((smoothEndpointMetric gRef B hSmooth).metricInner p v w)) := by
  intro p v w
  simpa only [smoothEndpointMetric_metricInner gRef B hSmooth p v w] using
    hLimit p v w

/-- **Math.** The global endpoint family supplied by the coefficient-limit
producer becomes an actual positive-definite metric as soon as the single
joint smoothness statement for that family is available. -/
theorem exists_smoothEndpointMetric_of_globalEndpointField
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (gRef : RiemannianMetric I M)
    (B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p))
    (hLimit : ∀ (p : M) (v w : TangentSpace I p),
      Tendsto (fun t => (g t).metricInner p v w)
        (nhdsWithin T (Iio T)) (𝓝 ((B p).inner v w)))
    (hSmooth : ContMDiff I
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p => TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) p (endpointInner gRef B p))) :
    ∃ gT : RiemannianMetric I M,
      (∀ (p : M) (v w : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p v w)
          (nhdsWithin T (Iio T)) (𝓝 (gT.metricInner p v w))) := by
  refine ⟨smoothEndpointMetric gRef B hSmooth, ?_⟩
  intro p v w
  exact smoothEndpointMetric_tendsto_of_endpointField
    gRef B hSmooth hLimit p v w

#print axioms smoothEndpointMetric
#print axioms smoothEndpointMetric_tendsto_of_endpointField
#print axioms exists_smoothEndpointMetric_of_globalEndpointField

end Topping

end

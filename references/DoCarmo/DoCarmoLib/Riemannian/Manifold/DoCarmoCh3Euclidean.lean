import DoCarmoLib.Riemannian.Manifold.EuclideanFlat
import DoCarmoLib.Riemannian.Connection.ChartChristoffel
import DoCarmoLib.Riemannian.Exponential.Intrinsic

/-!
# Euclidean geodesics and exponential map

This file formalizes do Carmo Ch. 3, Example 2.10.  On a finite-dimensional
real inner-product space the chart frame is constant, hence the Christoffel
symbols of the Euclidean metric vanish.  The geodesics are affine lines and
the intrinsic exponential map is translation by the tangent vector.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff RealInnerProductSpace

noncomputable section

set_option linter.unusedSectionVars false

namespace Riemannian

open Riemannian.Tensor

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Module.Finite ℝ F] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)]

/-- **Math.** In the canonical chart on a vector space, the chart frame is the
fixed model-space basis. -/
theorem euclidean_chartBasisVecFiber (α x : F)
    (i : Fin (Module.finrank ℝ F)) :
    chartBasisVecFiber (I := 𝓘(ℝ, F)) α i x = (Module.finBasis ℝ F) i := by
  rw [chartBasisVecFiber]
  rw [← Bundle.Trivialization.symmL_apply (R := ℝ)
    (trivializationAt F (TangentSpace 𝓘(ℝ, F)) α) (by simp)
    ((Module.finBasis ℝ F) i)]
  rw [TangentBundle.symmL_model_space]
  rfl

/-- **Math.** The Euclidean chart Gram matrix is constant. -/
theorem euclidean_chartGramMatrix (α x : F)
    (i j : Fin (Module.finrank ℝ F)) :
    chartGramMatrix (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) α x i j
      = @inner ℝ F _ ((Module.finBasis ℝ F) i) ((Module.finBasis ℝ F) j) := by
  rw [chartGramMatrix_apply, euclidean_chartBasisVecFiber,
    euclidean_chartBasisVecFiber]
  rfl

/-- **Math.** The pulled-back Euclidean Gram entries are constant functions of
the chart coordinate. -/
theorem euclidean_chartGramOnE (α : F)
    (i j : Fin (Module.finrank ℝ F)) (y : F) :
    chartGramOnE (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) α i j y
      = @inner ℝ F _ ((Module.finBasis ℝ F) i) ((Module.finBasis ℝ F) j) := by
  rw [chartGramOnE_def, euclidean_chartGramMatrix]

/-- **Math.** Every coordinate derivative of the Euclidean Gram matrix is zero. -/
theorem euclidean_partialDeriv_chartGramOnE (α : F)
    (i j k : Fin (Module.finrank ℝ F)) (y : F) :
    partialDeriv (E := F) k
      (chartGramOnE (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) α i j) y = 0 := by
  unfold partialDeriv
  rw [show chartGramOnE (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) α i j =
      fun _ : F => @inner ℝ F _ ((Module.finBasis ℝ F) i) ((Module.finBasis ℝ F) j) by
    funext z
    exact euclidean_chartGramOnE α i j z]
  simp

/-- **Math.** All Christoffel symbols of the Euclidean metric vanish. -/
theorem euclidean_chartChristoffel (α : F)
    (i j k : Fin (Module.finrank ℝ F)) (y : F) :
    chartChristoffel (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) α i j k y = 0 := by
  rw [chartChristoffel_def]
  simp only [euclidean_partialDeriv_chartGramOnE, zero_add, sub_zero, mul_zero,
    Finset.sum_const_zero]

/-- **Math.** The Euclidean Christoffel contraction is identically zero. -/
theorem euclidean_chartChristoffelContraction (α v w y : F) :
    Geodesic.chartChristoffelContraction (I := 𝓘(ℝ, F))
      (DCEuclideanMetric (F := F)) α v w y = 0 := by
  classical
  unfold Geodesic.chartChristoffelContraction
  refine Finset.sum_eq_zero ?_
  intro k _hk
  have hcoeff :
      (∑ i : Fin (Module.finrank ℝ F), ∑ j : Fin (Module.finrank ℝ F),
        chartChristoffel (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) α i j k y *
          Geodesic.chartCoord (E := F) i v * Geodesic.chartCoord (E := F) j w) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i _hi
    refine Finset.sum_eq_zero ?_
    intro j _hj
    rw [euclidean_chartChristoffel]
    simp
  rw [hcoeff, zero_smul]

/-- **Math.** The affine line through `p` with velocity `v`. -/
def euclideanGeodesic (p v : F) : ℝ → F := fun t => p + t • v

@[simp] theorem euclideanGeodesic_zero (p v : F) : euclideanGeodesic p v 0 = p := by
  simp [euclideanGeodesic]

/-- **Math.** In the canonical vector-space chart, reading an affine line does
not change it. -/
theorem chartLocalCurve_euclideanGeodesic (p v : F) (t : ℝ) :
    Geodesic.chartLocalCurve (I := 𝓘(ℝ, F)) (euclideanGeodesic p v) t =
      fun s => p + s • v := by
  funext s
  simp [Geodesic.chartLocalCurve_def, euclideanGeodesic]

/-- **Math.** Euclidean geodesics are affine lines. -/
theorem isGeodesic_euclideanGeodesic (p v : F) :
    Geodesic.IsGeodesic (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F))
      (euclideanGeodesic p v) := by
  intro t
  refine ⟨v, 0, ?_, ?_, ?_, ?_⟩
  · rw [chartLocalCurve_euclideanGeodesic]
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [chartLocalCurve_euclideanGeodesic]
    have hderiv : deriv (fun r : ℝ => p + r • v) s = v := by
      simpa using (((hasDerivAt_id s).smul_const v).const_add p).deriv
    rw [hderiv]
    simpa using ((hasDerivAt_id s).smul_const v).const_add p
  · have hderiv :
        (fun s => deriv (Geodesic.chartLocalCurve (I := 𝓘(ℝ, F))
          (euclideanGeodesic p v) t) s) = fun _ : ℝ => v := by
      funext s
      rw [chartLocalCurve_euclideanGeodesic]
      simpa using (((hasDerivAt_id s).smul_const v).const_add p).deriv
    rw [hderiv]
    exact hasDerivAt_const t v
  · rw [zero_add, euclidean_chartChristoffelContraction]

/-- **Math.** The Euclidean affine line is continuous. -/
theorem continuous_euclideanGeodesic (p v : F) : Continuous (euclideanGeodesic p v) := by
  exact continuous_const.add (continuous_id.smul continuous_const)

/-- **Math.** Under the canonical identification `T_pF = F`, the intrinsic
Euclidean exponential is `exp_p(v) = p + v`. -/
theorem expMapIntrinsic_euclidean (p v : F) :
    Exponential.expMapIntrinsic (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F)) p
      (show TangentSpace 𝓘(ℝ, F) p from v) = p + v := by
  have hw : Geodesic.IsIntrinsicGeodesicOnWithInitial
      (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F))
      (euclideanGeodesic p v) Set.univ p v := by
    refine ⟨euclideanGeodesic_zero p v, ?_,
      (continuous_euclideanGeodesic p v).continuousOn,
      (isGeodesic_euclideanGeodesic p v).isGeodesicOn Set.univ⟩
    change HasDerivAt (fun t => extChartAt 𝓘(ℝ, F) p (euclideanGeodesic p v t))
      v 0
    simpa [euclideanGeodesic] using
      (((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p)
  have h := Exponential.expMapIntrinsic_eq_of_witness
    (I := 𝓘(ℝ, F)) (DCEuclideanMetric (F := F))
    (p := p) (v := v) (γ := euclideanGeodesic p v) (J := Set.univ)
    isOpen_univ isPreconnected_univ (mem_univ 0) (mem_univ 1) hw
  simpa [euclideanGeodesic] using h

end Riemannian

end

import MorganTianLib.Ch03.RicciFlow.ExactSolutions
import DoCarmoLib.Riemannian.Manifold.EuclideanFlat
import MorganTianLib.Ch01.ExpBallDiffeo

/-!
# Morgan--Tian Ch. 3 -- the Euclidean Einstein example

The flat model is already available in do Carmo's checked Euclidean connection
development.  This file transports that calculation through Levi--Civita
uniqueness into the Ricci-flow tensor used by Chapter 3.  It deliberately does
not claim the sphere or hyperbolic examples: those require their respective
space-form models and curvature computations.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]
  [NeZero (Module.finrank ℝ F)]

private theorem euclideanConnection_eq_leviCivitaConnection :
    euclideanConnection (F := F) =
      (DCEuclideanMetric (F := F)).leviCivitaConnection := by
  apply AffineConnection.leviCivita_unique'
  · exact euclideanConnection_isLeviCivita
  · exact isLeviCivita_leviCivitaConnection (DCEuclideanMetric (F := F))

omit [NeZero (Module.finrank ℝ F)] in
private theorem euclidean_curvatureFormAt_eq_zero
    (p : F) (v w z t : TangentSpace 𝓘(ℝ, F) p) :
    curvatureFormAt (DCEuclideanMetric (F := F))
      (euclideanConnection (F := F)) p v w z t = 0 := by
  rw [curvatureFormAt_eq_affineCurvatureFormAt]
  rw [(euclideanConnection (F := F)).curvatureFormAt_eq
    (DCEuclideanMetric (F := F)) p
    (extendVector_apply p v) (extendVector_apply p w)
    (extendVector_apply p z) (extendVector_apply p t)]
  simp only [Riemannian.AffineConnection.curvatureForm]
  rw [euclideanConnection_curvature (extendVector p v)
    (extendVector p w) (extendVector p z)]
  simp

/-! The Euclidean model is Einstein with constant zero, hence its canonical
Einstein scaling is the steady Ricci flow from the Chapter 3 calculation. -/

/-- **Math.** Euclidean space with its standard metric is Ricci-flat, and hence
is an Einstein metric with Einstein constant `0`. -/
theorem euclideanMetric_isEinsteinTensor :
    IsEinsteinTensor (DCEuclideanMetric (F := F)) 0 := by
  intro p v w
  rw [← ricciAt_leviCivita_eq_ricciTensorAt
    (DCEuclideanMetric (F := F))
    (isLeviCivita_leviCivitaConnection (DCEuclideanMetric (F := F))) p v w]
  letI : Bundle.RiemannianBundle (TangentSpace 𝓘(ℝ, F) : F → Type _) :=
    ⟨(DCEuclideanMetric (F := F)).toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace 𝓘(ℝ, F) p)
  rw [ricciAt, Riemannian.ricciForm_eq_sum _ v w e]
  simp only [zero_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [← euclideanConnection_eq_leviCivitaConnection (F := F)]
  exact euclidean_curvatureFormAt_eq_zero p v (e i) w (e i)

/-- **Math.** The steady Euclidean family is a Ricci-flow equation on every
time set: it is the zero-Einstein scaling from the exact-solution calculation. -/
theorem euclideanMetric_isRicciFlowEquationOn (J : Set ℝ) :
    IsRicciFlowEquationOn
      (einsteinMetricFamilyOn (DCEuclideanMetric (F := F)) J 0
        (by intro t _ht; simp [einsteinScale])) J := by
  apply isRicciFlowEquationOn_einsteinMetricFamilyOn
  exact euclideanMetric_isEinsteinTensor

end MorganTianLib

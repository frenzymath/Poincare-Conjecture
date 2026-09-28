import Topping.ParabolicPDE.VariableSectionNemytskii
import Topping.ParabolicPDE.VectorSmooth

/-!
# Compactly carried vector two-jets

This file lifts a `C^2` vector-valued function on a finite-dimensional model
space to the bounded continuous value, first-jet, and second-jet sections used
by the parabolic section evaluator.  The compact carrier is represented by a
continuous map `chi : T -> E`; no chart or bundle assertion is made here.
-/

namespace Topping
namespace ParabolicPDE

open scoped BoundedContinuousFunction BigOperators

noncomputable section

variable {E T V : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace T] [CompactSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [CompactSpace T] in
private theorem continuous_vector_jet_first
    (u : E → V) (hu : ContDiff ℝ 2 u) (chi : T → E)
    (hchi : Continuous chi) (i : Fin (Module.finrank ℝ E)) :
    Continuous (fun t : T =>
      fderiv ℝ u (chi t) ((Module.finBasis ℝ E) i)) := by
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hi : ContDiff ℝ 1 (fun x : E =>
      fderiv ℝ u x ((Module.finBasis ℝ E) i)) := by
    exact hdu.clm_apply contDiff_const
  exact hi.continuous.comp hchi

omit [CompactSpace T] in
private theorem continuous_vector_jet_second
    (u : E → V) (hu : ContDiff ℝ 2 u) (chi : T → E)
    (hchi : Continuous chi) (i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun t : T =>
      fderiv ℝ (fun z : E =>
        fderiv ℝ u z ((Module.finBasis ℝ E) j)) (chi t)
          ((Module.finBasis ℝ E) i)) := by
  have hdu : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hj : ContDiff ℝ 1 (fun x : E =>
      fderiv ℝ u x ((Module.finBasis ℝ E) j)) := by
    exact hdu.clm_apply contDiff_const
  have hdj : ContDiff ℝ 0 (fderiv ℝ (fun x : E =>
      fderiv ℝ u x ((Module.finBasis ℝ E) j))) :=
    hj.fderiv_right (by norm_num)
  have hij : ContDiff ℝ 0 (fun x : E =>
      fderiv ℝ (fun z : E =>
        fderiv ℝ u z ((Module.finBasis ℝ E) j)) x
          ((Module.finBasis ℝ E) i)) := by
    exact hdj.clm_apply contDiff_const
  exact hij.continuous.comp hchi

/-- The bounded value/first/second jet sections obtained by sampling a `C^2`
vector-valued function along a continuous compact carrier. -/
def vectorJetSectionsOf
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi) :
    VectorSecondOrderCoefficients.VariableJetSections
      (T := T) (ι := Fin (Module.finrank ℝ E)) (V := V) :=
  ( BoundedContinuousFunction.mkOfCompact
      { toFun := fun t : T => u (chi t)
        continuous_toFun := hu.continuous.comp hchi }
  , ( fun i => BoundedContinuousFunction.mkOfCompact
      { toFun := fun t : T =>
          fderiv ℝ u (chi t) ((Module.finBasis ℝ E) i)
        continuous_toFun := continuous_vector_jet_first u hu chi hchi i }
    , fun i j => BoundedContinuousFunction.mkOfCompact
      { toFun := fun t : T =>
          fderiv ℝ (fun z : E =>
            fderiv ℝ u z ((Module.finBasis ℝ E) j)) (chi t)
              ((Module.finBasis ℝ E) i)
        continuous_toFun := continuous_vector_jet_second u hu chi hchi i j } )
  )

/-- The basis-coordinate second jet of a vector-valued function on `E`. -/
def vectorBasisJetAt
    (u : E → V) (x : E) :
    VectorSecondOrderJet (Fin (Module.finrank ℝ E)) V where
  value := u x
  first := fun i => fderiv ℝ u x ((Module.finBasis ℝ E) i)
  second := fun i j =>
    fderiv ℝ (fun z : E =>
      fderiv ℝ u z ((Module.finBasis ℝ E) j)) x
        ((Module.finBasis ℝ E) i)

@[simp] theorem vectorBasisJetAt_value
    (u : E → V) (x : E) :
    (vectorBasisJetAt u x).value = u x := rfl

@[simp] theorem vectorBasisJetAt_first
    (u : E → V) (x : E) (i : Fin (Module.finrank ℝ E)) :
    (vectorBasisJetAt u x).first i =
      fderiv ℝ u x ((Module.finBasis ℝ E) i) := rfl

@[simp] theorem vectorBasisJetAt_second
    (u : E → V) (x : E)
    (i j : Fin (Module.finrank ℝ E)) :
    (vectorBasisJetAt u x).second i j =
      fderiv ℝ (fun z : E =>
        fderiv ℝ u z ((Module.finBasis ℝ E) j)) x
          ((Module.finBasis ℝ E) i) := rfl

@[simp] theorem vectorJetSectionsOf_value_apply
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi) (t : T) :
    (vectorJetSectionsOf (T := T) u hu chi hchi).1 t = u (chi t) := rfl

@[simp] theorem vectorJetSectionsOf_first_apply
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi)
    (i : Fin (Module.finrank ℝ E)) (t : T) :
    (vectorJetSectionsOf (T := T) u hu chi hchi).2.1 i t =
      fderiv ℝ u (chi t) ((Module.finBasis ℝ E) i) := rfl

@[simp] theorem vectorJetSectionsOf_second_apply
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi)
    (i j : Fin (Module.finrank ℝ E)) (t : T) :
    (vectorJetSectionsOf (T := T) u hu chi hchi).2.2 i j t =
      fderiv ℝ (fun z : E =>
        fderiv ℝ u z ((Module.finBasis ℝ E) j)) (chi t)
          ((Module.finBasis ℝ E) i) := rfl

def vectorJetSectionsOf_jet
    (u : E → V) (_hu : ContDiff ℝ 2 u)
    (chi : T → E) (_hchi : Continuous chi) (t : T) :
    VectorSecondOrderJet (Fin (Module.finrank ℝ E)) V :=
  vectorBasisJetAt u (chi t)

@[simp] theorem vectorJetSectionsOf_jet_value
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi) (t : T) :
    (vectorJetSectionsOf_jet (T := T) u hu chi hchi t).value =
      (vectorJetSectionsOf (T := T) u hu chi hchi).1 t := by
  simp [vectorJetSectionsOf_jet, vectorBasisJetAt, vectorJetSectionsOf]

@[simp] theorem vectorJetSectionsOf_jet_first
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi) (t : T)
    (i : Fin (Module.finrank ℝ E)) :
    (vectorJetSectionsOf_jet (T := T) u hu chi hchi t).first i =
    (vectorJetSectionsOf (T := T) u hu chi hchi).2.1 i t := by
  simp [vectorJetSectionsOf_jet, vectorBasisJetAt, vectorJetSectionsOf]

@[simp] theorem vectorJetSectionsOf_jet_second
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi) (t : T)
    (i j : Fin (Module.finrank ℝ E)) :
    (vectorJetSectionsOf_jet (T := T) u hu chi hchi t).second i j =
    (vectorJetSectionsOf (T := T) u hu chi hchi).2.2 i j t := by
  simp [vectorJetSectionsOf_jet, vectorBasisJetAt, vectorJetSectionsOf]

@[simp] theorem vectorJetSectionsOf_applyJet
    (C : VectorSecondOrderCoefficients.VariableCoefficientSections
      (T := T) (ι := Fin (Module.finrank ℝ E)) (V := V))
    (u : E → V) (hu : ContDiff ℝ 2 u)
    (chi : T → E) (hchi : Continuous chi) (t : T) :
    VectorSecondOrderCoefficients.variableCoefficientSectionsApplyJetArgs C
      (vectorJetSectionsOf (T := T) u hu chi hchi) t =
      (∑ i, ∑ j, (C.1 i j t)
        ((vectorJetSectionsOf_jet (T := T) u hu chi hchi t).second i j)) +
      (∑ i, (C.2.1 i t)
        ((vectorJetSectionsOf_jet (T := T) u hu chi hchi t).first i)) +
      (C.2.2 t) (vectorJetSectionsOf_jet (T := T) u hu chi hchi t).value := by
  simp [VectorSecondOrderCoefficients.variableCoefficientSectionsApplyJetArgs_apply]

end
end ParabolicPDE
end Topping

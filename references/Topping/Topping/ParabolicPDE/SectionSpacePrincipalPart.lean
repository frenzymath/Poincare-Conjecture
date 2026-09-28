import Topping.ParabolicPDE.SectionSpaceSmooth
import Topping.ParabolicPDE.SectionSpaceDerivative

/-!
# Section-space principal-part extraction

The bounded coefficient/jet evaluator is already known to be a smooth
bilinear map.  This module records the concrete directional consequence used
when identifying the principal part of a section-space linearisation: if a
parameter direction has no first-order coefficient variation and a pure
second-jet variation, its Frechet derivative is exactly the coefficient
evaluator on that second jet.  A rank-one specialization rewrites the result
as the packaged vector principal symbol.

The statements are deliberately about the existing bounded section model.  No
manifold atlas, bundle trivialization, or PDE solver is asserted here.
-/

namespace Topping
namespace ParabolicPDE

open scoped BoundedContinuousFunction
open VectorSecondOrderCoefficients

noncomputable section

variable {T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [CompactSpace T] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-!
The aliases for the coefficient and jet products do not carry the normed
space instances needed by `HasFDerivAt` through an import boundary.  Keep the
same explicit product instances used by `SectionSpaceSmooth`, under local
names so this file remains independent of declaration-name order.
-/

local instance sectionPrincipalPartCoefficientModule :
    Module ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance sectionPrincipalPartJetModule :
    Module ℝ (VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance sectionPrincipalPartCoefficientNormedSpace :
    NormedSpace ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance sectionPrincipalPartJetNormedSpace :
    NormedSpace ℝ (VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance sectionPrincipalPartPairModule :
    Module ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance sectionPrincipalPartPairNormedSpace :
    NormedSpace ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance sectionPrincipalPartOutputNormedAddCommGroup :
    NormedAddCommGroup (T →ᵇ V) :=
  BoundedContinuousFunction.instNormedAddCommGroup

/-! ## Pure second-jet directions -/

/-- The section evaluator's Frechet derivative in a direction whose coefficient
component vanishes and whose jet component is a pure second jet. -/
theorem fderiv_variableCoefficientSectionsApplyJetArgs_pureSecond
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {C : P → VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z : P → VariableJetSections (T := T) (ι := ι) (V := V)}
    {C' : P →L[ℝ] VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z' : P →L[ℝ] VariableJetSections (T := T) (ι := ι) (V := V)}
    {p q : P} {Q : ι → ι → T →ᵇ V}
    (hC : HasFDerivAt C C' p)
    (hZ : HasFDerivAt Z Z' p)
    (hCq : C' q = 0)
    (hZq : Z' q =
      pureSecondJetInjection (T := T) (ι := ι) (V := V) Q) :
    fderiv ℝ
        (fun r => variableCoefficientSectionsApplyJetArgs (C r) (Z r)) p q =
      variableCoefficientSectionsApplyJetArgs (C p)
        (pureSecondJetInjection (T := T) (ι := ι) (V := V) Q) := by
  have hcomp :=
    (hasFDerivAt_variableCoefficientSectionsApplyJetArgs_comp hC hZ).fderiv
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply]
  rw [variableCoefficientSectionsApplyJetArgs_deriv_apply]
  change
    variableCoefficientSectionsApplyJetArgs (C p) (C' q, Z' q).2 +
        variableCoefficientSectionsApplyJetArgs (C' q, Z' q).1 (Z p) = _
  simp [hCq, hZq]
  ext t
  simp [variableCoefficientSectionsApplyJetArgs,
    variableCoefficientSectionsToCoefficients,
    variableSectionApplyJetArgs_apply]

@[simp] theorem fderiv_variableCoefficientSectionsApplyJetArgs_pureSecond_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {C : P → VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z : P → VariableJetSections (T := T) (ι := ι) (V := V)}
    {C' : P →L[ℝ] VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z' : P →L[ℝ] VariableJetSections (T := T) (ι := ι) (V := V)}
    {p q : P} {Q : ι → ι → T →ᵇ V} (t : T)
    (hC : HasFDerivAt C C' p)
    (hZ : HasFDerivAt Z Z' p)
    (hCq : C' q = 0)
    (hZq : Z' q =
      pureSecondJetInjection (T := T) (ι := ι) (V := V) Q) :
    (fderiv ℝ
        (fun r => variableCoefficientSectionsApplyJetArgs (C r) (Z r)) p q) t =
      ∑ i, ∑ k, (C p).1 i k t (Q i k t) := by
  rw [fderiv_variableCoefficientSectionsApplyJetArgs_pureSecond
    hC hZ hCq hZq]
  exact variableCoefficientSectionsApplyJetArgs_pureSecond_apply (C p) Q t

/-! ## Rank-one second jets and the vector symbol -/

/-- A rank-one second-jet section built from a coordinate covector and a
bounded fibre section. -/
def rankOneSecondJetSection
    (xi : ι → ℝ) (h : T →ᵇ V) : ι → ι → T →ᵇ V :=
  fun i k => (xi i * xi k) • h

omit [Fintype ι] [CompactSpace T] in
@[simp] theorem rankOneSecondJetSection_apply
    (xi : ι → ℝ) (h : T →ᵇ V) (i k : ι) (t : T) :
    rankOneSecondJetSection (T := T) xi h i k t =
      (xi i * xi k) • h t := by
  rfl

theorem variableCoefficientSectionsApplyJetArgs_rankOneSecond_apply
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (xi : ι → ℝ) (h : T →ᵇ V) (t : T) :
    variableCoefficientSectionsApplyJetArgs C
        (pureSecondJetInjection (T := T) (ι := ι) (V := V)
          (rankOneSecondJetSection (T := T) xi h)) t =
      (variableCoefficientSectionsToCoefficients C).principalSymbol t xi (h t) := by
  simp [rankOneSecondJetSection, variableCoefficientSectionsToCoefficients,
    VectorSecondOrderCoefficients.principalSymbol_apply]

/-- The section-space Frechet derivative on a rank-one pure second-jet
direction is the packaged vector principal symbol, pointwise on the base. -/
theorem fderiv_variableCoefficientSectionsApplyJetArgs_rankOneSecond_apply
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {C : P → VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z : P → VariableJetSections (T := T) (ι := ι) (V := V)}
    {C' : P →L[ℝ] VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z' : P →L[ℝ] VariableJetSections (T := T) (ι := ι) (V := V)}
    {p q : P} (xi : ι → ℝ) (h : T →ᵇ V) (t : T)
    (hC : HasFDerivAt C C' p)
    (hZ : HasFDerivAt Z Z' p)
    (hCq : C' q = 0)
    (hZq : Z' q = pureSecondJetInjection (T := T) (ι := ι) (V := V)
      (rankOneSecondJetSection (T := T) xi h)) :
    (fderiv ℝ
        (fun r => variableCoefficientSectionsApplyJetArgs (C r) (Z r)) p q) t =
      (variableCoefficientSectionsToCoefficients (C p)).principalSymbol t xi (h t) := by
  rw [fderiv_variableCoefficientSectionsApplyJetArgs_pureSecond_apply
    t hC hZ hCq hZq]
  simp [rankOneSecondJetSection, variableCoefficientSectionsToCoefficients,
    VectorSecondOrderCoefficients.principalSymbol_apply]

#print axioms fderiv_variableCoefficientSectionsApplyJetArgs_pureSecond
#print axioms fderiv_variableCoefficientSectionsApplyJetArgs_pureSecond_apply
#print axioms rankOneSecondJetSection
#print axioms variableCoefficientSectionsApplyJetArgs_rankOneSecond_apply
#print axioms fderiv_variableCoefficientSectionsApplyJetArgs_rankOneSecond_apply

end
end ParabolicPDE
end Topping

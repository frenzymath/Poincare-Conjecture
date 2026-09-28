import Topping.ParabolicPDE.VariableSectionNemytskii

/-!
# Smoothness of the variable section evaluator

The coefficient/jet evaluator is a bounded bilinear map on the product of
bounded continuous coefficient and jet sections.  This module exposes the
resulting `C^∞` producer without adding any manifold or PDE existence claim.
-/

namespace Topping
namespace ParabolicPDE

open scoped ContDiff BoundedContinuousFunction

noncomputable section

open VectorSecondOrderCoefficients

variable {T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [CompactSpace T] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! The bundled evaluator is smooth jointly in its coefficient and jet
arguments. -/

theorem contDiff_variableCoefficientSectionsApplyJetArgs :
    ContDiff ℝ ∞
      (fun p : VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
          VariableJetSections (T := T) (ι := ι) (V := V) ↦
        variableCoefficientSectionsApplyJetArgs p.1 p.2) := by
  exact isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs.contDiff

theorem differentiable_variableCoefficientSectionsApplyJetArgs :
    Differentiable ℝ
      (fun p : VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
          VariableJetSections (T := T) (ι := ι) (V := V) ↦
        variableCoefficientSectionsApplyJetArgs p.1 p.2) := by
  exact (contDiff_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)).differentiable (by norm_num)

/-! Smooth parameter families can be fed into the same evaluator.  This is
the interface used by a later section-space construction when both the
coefficient field and the jet data vary with an external parameter. -/

theorem contDiff_variableCoefficientSectionsApplyJetArgs_comp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {n : ℕ∞ω}
    {C : P → VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z : P → VariableJetSections (T := T) (ι := ι) (V := V)}
    (hC : ContDiff ℝ n C) (hZ : ContDiff ℝ n Z) :
    ContDiff ℝ n
      (fun p => variableCoefficientSectionsApplyJetArgs (C p) (Z p)) := by
  exact isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs.contDiff.comp₂
    hC hZ

/-! The aliases above are reducible products, but Lean does not always unfold
the aliases while elaborating `HasFDerivAt` binders.  Keep the calculus
instances explicit and local to this first-order bridge. -/

local instance variableCoefficientSectionsModule :
    Module ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance variableJetSectionsModule :
    Module ℝ (VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance variableCoefficientSectionsNormedSpace :
    NormedSpace ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance variableJetSectionsNormedSpace :
    NormedSpace ℝ (VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance variableCoefficientJetPairModule :
    Module ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.instModule

local instance variableCoefficientJetPairNormedSpace :
    NormedSpace ℝ (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) :=
  Prod.normedSpace

local instance variableSectionOutputNormedAddCommGroup :
    NormedAddCommGroup (T →ᵇ V) :=
  BoundedContinuousFunction.instNormedAddCommGroup

/-! The same parameter-composition interface at the first Frechet level. -/

theorem hasFDerivAt_variableCoefficientSectionsApplyJetArgs_comp
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {C : P → VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z : P → VariableJetSections (T := T) (ι := ι) (V := V)}
    {C' : P →L[ℝ] VariableCoefficientSections (T := T) (ι := ι) (V := V)}
    {Z' : P →L[ℝ] VariableJetSections (T := T) (ι := ι) (V := V)}
    {p : P}
    (hC : HasFDerivAt C C' p)
    (hZ : HasFDerivAt Z Z' p) :
    HasFDerivAt
      (fun q => variableCoefficientSectionsApplyJetArgs (C q) (Z q))
      (((isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
        (T := T) (ι := ι) (V := V)).deriv (C p, Z p)).comp
        (C'.prod Z')) p := by
  have hpair : HasFDerivAt (fun q => (C q, Z q)) (C'.prod Z') p :=
    HasFDerivAt.prodMk (f₁ := C) (f₁' := C') (f₂ := Z) (f₂' := Z') hC hZ
  let g : (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) → T →ᵇ V :=
    fun q => variableCoefficientSectionsApplyJetArgs q.1 q.2
  let g' : (VariableCoefficientSections (T := T) (ι := ι) (V := V) ×
      VariableJetSections (T := T) (ι := ι) (V := V)) →L[ℝ] T →ᵇ V :=
    (isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
      (T := T) (ι := ι) (V := V)).deriv (C p, Z p)
  have hg : HasFDerivAt g g' ((C p, Z p)) := by
    simpa [g, g'] using
      (hasFDerivAt_variableCoefficientSectionsApplyJetArgs
        (T := T) (ι := ι) (V := V) (C p) (Z p))
  have hcomp := HasFDerivAt.comp (f := fun q => (C q, Z q))
    (f' := C'.prod Z') p hg hpair
  simpa [g, Function.comp_def] using hcomp

end
end ParabolicPDE
end Topping

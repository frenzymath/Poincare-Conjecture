import Topping.ParabolicPDE.VariableSectionNemytskii

/-!
# Section-space derivative bridge

The variable-coefficient section evaluator is bounded bilinear.  This file
records its Frechet derivative with the coefficient held fixed, together with
the canonical pure-second-jet slice.
-/

namespace Topping
namespace ParabolicPDE

open scoped BoundedContinuousFunction
open VectorSecondOrderCoefficients

noncomputable section

variable {T ι V : Type*} [Fintype ι] [TopologicalSpace T]
  [CompactSpace T] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-! The coefficient is held fixed, so the derivative is the evaluator itself
viewed as a continuous linear map in the jet variable. -/
theorem hasFDerivAt_variableCoefficientSectionsApplyJetArgs_right
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V)) :
    HasFDerivAt
      (fun w : VariableJetSections (T := T) (ι := ι) (V := V) =>
        variableCoefficientSectionsApplyJetArgs C w)
      (variableCoefficientSectionsApplyJetArgsCLM C) z := by
  have h := (variableCoefficientSectionsApplyJetArgsCLM C).hasFDerivAt (x := z)
  convert h using 1
  funext w
  exact (variableCoefficientSectionsApplyJetArgsCLM_apply C w).symm

/-! Canonical injection of a pure second-jet section. -/
def pureSecondJetInjection :
    (ι → ι → T →ᵇ V) →L[ℝ] VariableJetSections (T := T) (ι := ι) (V := V) :=
  (0 : (ι → ι → T →ᵇ V) →L[ℝ] (T →ᵇ V)).prod
    ((0 : (ι → ι → T →ᵇ V) →L[ℝ] (ι → T →ᵇ V)).prod
      (ContinuousLinearMap.id ℝ _))

@[simp] theorem pureSecondJetInjection_apply
    (Q : ι → ι → T →ᵇ V) :
    pureSecondJetInjection (T := T) (ι := ι) (V := V) Q = (0, 0, Q) := rfl

theorem hasFDerivAt_variableCoefficientSectionsApplyJetArgs_pureSecond
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V))
    (Q : ι → ι → T →ᵇ V) :
    HasFDerivAt
      (fun s : ι → ι → T →ᵇ V =>
        variableCoefficientSectionsApplyJetArgs C
          (z + pureSecondJetInjection (T := T) (ι := ι) (V := V) s))
      ((variableCoefficientSectionsApplyJetArgsCLM C).comp
        (pureSecondJetInjection (T := T) (ι := ι) (V := V))) Q := by
  have hright := hasFDerivAt_variableCoefficientSectionsApplyJetArgs_right
    (T := T) (ι := ι) (V := V) C
    (z + pureSecondJetInjection (T := T) (ι := ι) (V := V) Q)
  let f : (ι → ι → T →ᵇ V) → VariableJetSections (T := T) (ι := ι) (V := V) :=
    fun s => z + pureSecondJetInjection (T := T) (ι := ι) (V := V) s
  have hf : HasFDerivAt f
      (pureSecondJetInjection (T := T) (ι := ι) (V := V)) Q := by
    change HasFDerivAt
      (fun s : ι → ι → T →ᵇ V =>
        z + pureSecondJetInjection (T := T) (ι := ι) (V := V) s)
      (pureSecondJetInjection (T := T) (ι := ι) (V := V)) Q
    exact (pureSecondJetInjection (T := T) (ι := ι) (V := V)).hasFDerivAt.const_add z
  have hcomp := HasFDerivAt.comp (f := f)
    (f' := pureSecondJetInjection (T := T) (ι := ι) (V := V)) Q hright hf
  simpa [f, Function.comp_def] using hcomp

@[simp] theorem variableCoefficientSectionsApplyJetArgs_pureSecond_apply
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (Q : ι → ι → T →ᵇ V) (t : T) :
    variableCoefficientSectionsApplyJetArgs C
      (pureSecondJetInjection (T := T) (ι := ι) (V := V) Q) t =
      ∑ i, ∑ k, (C.1 i k t) (Q i k t) := by
  simp [pureSecondJetInjection, variableCoefficientSectionsApplyJetArgs_apply]

@[simp] theorem variableCoefficientSectionsApplyJetArgs_pureSecond_deriv_apply
    (C : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (Q : ι → ι → T →ᵇ V) (t : T) :
    ((variableCoefficientSectionsApplyJetArgsCLM C).comp
      (pureSecondJetInjection (T := T) (ι := ι) (V := V)) Q) t =
      ∑ i, ∑ k, (C.1 i k t) (Q i k t) := by
  simp [ContinuousLinearMap.comp_apply,
    pureSecondJetInjection,
    variableCoefficientSectionsApplyJetArgs_apply]

/-! A coefficient perturbation is affine after the jet section is fixed. -/
theorem hasFDerivAt_variableCoefficientSectionsApplyJetArgs_left_affine
    (C H : VariableCoefficientSections (T := T) (ι := ι) (V := V))
    (z : VariableJetSections (T := T) (ι := ι) (V := V))
    (s₀ : ℝ) :
    HasFDerivAt
      (fun s : ℝ =>
        variableCoefficientSectionsApplyJetArgs (C + s • H) z)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight
        (variableCoefficientSectionsApplyJetArgs H z)) s₀ := by
  let B := isBoundedBilinearMap_variableCoefficientSectionsApplyJetArgs
    (T := T) (ι := ι) (V := V)
  have hline :
      (fun s : ℝ =>
        variableCoefficientSectionsApplyJetArgs (C + s • H) z) =
        (fun s : ℝ =>
          variableCoefficientSectionsApplyJetArgs C z +
            s • variableCoefficientSectionsApplyJetArgs H z) := by
    funext s
    rw [B.add_left, B.smul_left]
  rw [hline]
  exact (hasFDerivAt_id (𝕜 := ℝ) s₀).smul_const
      (variableCoefficientSectionsApplyJetArgs H z) |>.const_add
    (variableCoefficientSectionsApplyJetArgs C z)

end
end ParabolicPDE
end Topping

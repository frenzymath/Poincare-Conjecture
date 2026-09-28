import Topping.ParabolicPDE.GlobalBundleSymbol
import Topping.ParabolicPDE.GlobalSymbol

/-!
# Scalar identity symbols on a combined chart/fibre quotient

An identity-multiple principal symbol has no genuinely new frame algebra:
the scalar cocycle supplies the covector transition law, while an arbitrary
inverse pair of fibre frames supplies the bundle transport.  This module
packages that observation as a constructor for `CombinedPrincipalSymbol`.
The geometric chart and bundle data remain explicit inputs.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

variable {X C ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace CombinedPrincipalSymbol

/-! ## The constructor -/

/-- Combine a scalar principal-symbol cocycle with fibre frame transitions.

The resulting local symbol is a scalar multiple of the identity on the fibre.
All transition and cocycle hypotheses are retained as fields rather than
encoded through a target-shaped existence predicate.
-/
def ofScalar
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (frame : C → C → X → BundleFrameTransition V)
    (frame_self : ∀ c x, (frame c c x).forward = ContinuousLinearMap.id ℝ V)
    (frame_cocycle : ∀ c d e x,
      (frame c e x).forward =
        (frame d e x).forward.comp (frame c d x).forward) :
    CombinedPrincipalSymbol X C ι V where
  localSymbol := fun c x ξ =>
    A.localSymbol c x ξ • ContinuousLinearMap.id ℝ V
  covectorTransition := A.transition
  frame := frame
  covector_self := A.transition_self
  covector_cocycle := A.transition_cocycle
  frame_self := frame_self
  frame_cocycle := frame_cocycle
  glue := by
    intro c d x ξ
    rw [A.glue c d x ξ]
    ext v
    simp [ContinuousLinearMap.comp_apply]

@[simp] theorem ofScalar_localSymbol_apply
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (frame : C → C → X → BundleFrameTransition V)
    (frame_self : ∀ c x,
      (frame c c x).forward = ContinuousLinearMap.id ℝ V)
    (frame_cocycle : ∀ c d e x,
      (frame c e x).forward =
        (frame d e x).forward.comp (frame c d x).forward)
    (c : C) (x : X) (ξ : ι → ℝ) (v : V) :
    (ofScalar A frame frame_self frame_cocycle).localSymbol c x ξ v =
      A.localSymbol c x ξ • v := by
  simp [ofScalar]

@[simp] theorem ofScalar_covectorTransition
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (frame : C → C → X → BundleFrameTransition V)
    (frame_self : ∀ c x,
      (frame c c x).forward = ContinuousLinearMap.id ℝ V)
    (frame_cocycle : ∀ c d e x,
      (frame c e x).forward =
        (frame d e x).forward.comp (frame c d x).forward)
    (c d : C) (x : X) :
    (ofScalar A frame frame_self frame_cocycle).covectorTransition c d x =
      A.transition c d x := by
  rfl

@[simp] theorem ofScalar_frame
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (frame : C → C → X → BundleFrameTransition V)
    (frame_self : ∀ c x,
      (frame c c x).forward = ContinuousLinearMap.id ℝ V)
    (frame_cocycle : ∀ c d e x,
      (frame c e x).forward =
        (frame d e x).forward.comp (frame c d x).forward)
    (c d : C) (x : X) :
    (ofScalar A frame frame_self frame_cocycle).frame c d x =
      frame c d x := by
  rfl

/-! ## Representative-level evaluation -/

theorem evaluator_ofScalar_mk
    (A : ScalarPrincipalSymbolCocycle X C ι)
    (frame : C → C → X → BundleFrameTransition V)
    (frame_self : ∀ c x,
      (frame c c x).forward = ContinuousLinearMap.id ℝ V)
    (frame_cocycle : ∀ c d e x,
      (frame c e x).forward =
        (frame d e x).forward.comp (frame c d x).forward)
    (p : CombinedPrincipalSymbol.Representative X C ι V) :
    (ofScalar A frame frame_self frame_cocycle).evaluator ⟦p⟧ =
      (⟦⟨p.base, p.chart,
        A.localSymbol p.chart p.base p.covector • p.vector⟩⟧ :
        GlobalCombinedFiber (ofScalar A frame frame_self frame_cocycle)) := by
  rfl

end CombinedPrincipalSymbol

end
end ParabolicPDE
end Topping


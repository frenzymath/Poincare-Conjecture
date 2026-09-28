import Topping.ParabolicPDE.Operators

/-! An abstract combined covector/fibre principal-symbol cocycle. -/

namespace Topping
namespace ParabolicPDE

noncomputable section

variable {X C ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

structure CombinedPrincipalSymbol (X C ι V : Type*) [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  localSymbol : C → X → (ι → ℝ) → V →L[ℝ] V
  covectorTransition : C → C → X → (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ)
  frame : C → C → X → BundleFrameTransition V
  covector_self : ∀ c x, covectorTransition c c x = LinearEquiv.refl ℝ (ι → ℝ)
  covector_cocycle : ∀ c d e x,
    (covectorTransition c d x).trans (covectorTransition d e x) =
      covectorTransition c e x
  frame_self : ∀ c x, (frame c c x).forward = ContinuousLinearMap.id ℝ V
  frame_cocycle : ∀ c d e x,
    (frame c e x).forward = (frame d e x).forward.comp (frame c d x).forward
  glue : ∀ c d x ξ,
    localSymbol d x (covectorTransition c d x ξ) =
      (frame c d x).forward.comp
        ((localSymbol c x ξ).comp (frame c d x).backward)

namespace CombinedPrincipalSymbol

variable (G : CombinedPrincipalSymbol X C ι V)

@[simp] theorem covector_self_apply (c : C) (x : X) (ξ : ι → ℝ) :
    G.covectorTransition c c x ξ = ξ := by
  rw [G.covector_self c x]
  exact LinearEquiv.refl_apply ξ

theorem covector_inverse_apply (c d : C) (x : X) (ξ : ι → ℝ) :
    G.covectorTransition d c x (G.covectorTransition c d x ξ) = ξ := by
  have h := congrArg (fun e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) => e ξ)
    (G.covector_cocycle c d c x)
  simpa [LinearEquiv.trans_apply, G.covector_self c x] using h

theorem frame_self_apply (c : C) (x : X) (v : V) :
    (G.frame c c x).forward v = v := by
  rw [G.frame_self c x]
  rfl

theorem frame_inverse_apply (c d : C) (x : X) (v : V) :
    (G.frame d c x).forward ((G.frame c d x).forward v) = v := by
  have h := congrArg (fun f : V →L[ℝ] V => f v) (G.frame_cocycle c d c x)
  simpa [ContinuousLinearMap.comp_apply, G.frame_self c x] using h.symm

theorem frame_forward_injective (c d : C) (x : X) :
    Function.Injective (G.frame c d x).forward := by
  intro u v huv
  have h := congrArg (fun z => (G.frame c d x).backward z) huv
  simpa only [BundleFrameTransition.backward_forward_apply] using h

structure Representative (X C ι V : Type*) where
  base : X
  chart : C
  covector : ι → ℝ
  vector : V

def Equivalent (p q : Representative X C ι V) : Prop :=
  p.base = q.base ∧
    q.covector = G.covectorTransition p.chart q.chart p.base p.covector ∧
    q.vector = (G.frame p.chart q.chart p.base).forward p.vector

theorem equivalent_refl (p : Representative X C ι V) : Equivalent G p p := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (G.covector_self_apply p.chart p.base p.covector).symm
  · exact (G.frame_self_apply p.chart p.base p.vector).symm

theorem equivalent_symm {p q : Representative X C ι V}
    (hpq : Equivalent G p q) : Equivalent G q p := by
  rcases hpq with ⟨hb, hc, hv⟩
  refine ⟨hb.symm, ?_, ?_⟩
  · rw [← hb, hc]
    exact (G.covector_inverse_apply p.chart q.chart p.base p.covector).symm
  · rw [hv, ← hb]
    exact (G.frame_inverse_apply p.chart q.chart p.base p.vector).symm

theorem equivalent_trans {p q r : Representative X C ι V}
    (hpq : Equivalent G p q) (hqr : Equivalent G q r) :
    Equivalent G p r := by
  rcases hpq with ⟨hb₁, hc₁, hv₁⟩
  rcases hqr with ⟨hb₂, hc₂, hv₂⟩
  refine ⟨hb₁.trans hb₂, ?_, ?_⟩
  · rw [← hb₁] at hc₂
    rw [hc₂, hc₁, ← LinearEquiv.trans_apply,
      G.covector_cocycle p.chart q.chart r.chart p.base]
  · rw [← hb₁] at hv₂
    rw [hv₂, hv₁, ← ContinuousLinearMap.comp_apply,
      G.frame_cocycle p.chart q.chart r.chart p.base]

end CombinedPrincipalSymbol

def combinedRepresentativeSetoid
    (G : CombinedPrincipalSymbol X C ι V) :
    Setoid (CombinedPrincipalSymbol.Representative X C ι V) where
  r := CombinedPrincipalSymbol.Equivalent G
  iseqv := ⟨CombinedPrincipalSymbol.equivalent_refl G,
    CombinedPrincipalSymbol.equivalent_symm G,
    CombinedPrincipalSymbol.equivalent_trans G⟩

abbrev GlobalCombinedSymbol (G : CombinedPrincipalSymbol X C ι V) :=
  Quotient (combinedRepresentativeSetoid G)

structure FiberRepresentative (X C V : Type*) where
  base : X
  chart : C
  vector : V

namespace FiberRepresentative
variable (G : CombinedPrincipalSymbol X C ι V)

def Equivalent (p q : FiberRepresentative X C V) : Prop :=
  p.base = q.base ∧ q.vector = (G.frame p.chart q.chart p.base).forward p.vector

theorem refl (p : FiberRepresentative X C V) : Equivalent G p p :=
  ⟨rfl, (G.frame_self_apply p.chart p.base p.vector).symm⟩

theorem symm {p q : FiberRepresentative X C V}
    (h : Equivalent G p q) : Equivalent G q p := by
  rcases h with ⟨hb, hv⟩
  exact ⟨hb.symm, by
    rw [hv, ← hb]
    exact (G.frame_inverse_apply p.chart q.chart p.base p.vector).symm⟩

theorem trans {p q r : FiberRepresentative X C V}
    (hpq : Equivalent G p q) (hqr : Equivalent G q r) : Equivalent G p r := by
  rcases hpq with ⟨hb₁, hv₁⟩
  rcases hqr with ⟨hb₂, hv₂⟩
  refine ⟨hb₁.trans hb₂, ?_⟩
  rw [← hb₁] at hv₂
  rw [hv₂, hv₁, ← ContinuousLinearMap.comp_apply,
    G.frame_cocycle p.chart q.chart r.chart p.base]

end FiberRepresentative

def fiberRepresentativeSetoid
    (G : CombinedPrincipalSymbol X C ι V) : Setoid (FiberRepresentative X C V) where
  r := FiberRepresentative.Equivalent G
  iseqv := ⟨FiberRepresentative.refl G, FiberRepresentative.symm G,
    FiberRepresentative.trans G⟩

abbrev GlobalCombinedFiber (G : CombinedPrincipalSymbol X C ι V) :=
  Quotient (fiberRepresentativeSetoid G)

namespace CombinedPrincipalSymbol
variable (G : CombinedPrincipalSymbol X C ι V)

def evaluator : GlobalCombinedSymbol G → GlobalCombinedFiber G :=
  Quotient.lift
    (fun p : Representative X C ι V =>
      ⟦⟨p.base, p.chart, G.localSymbol p.chart p.base p.covector p.vector⟩⟧)
    (by
      intro p q hpq
      rcases hpq with ⟨hb, hc, hv⟩
      rw [← hb, hc, hv]
      apply Quotient.sound
      refine ⟨rfl, ?_⟩
      rw [G.glue]
      simp [BundleFrameTransition.backward_forward_apply])

@[simp] theorem evaluator_mk (p : Representative X C ι V) :
    G.evaluator ⟦p⟧ =
      (⟦⟨p.base, p.chart,
        G.localSymbol p.chart p.base p.covector p.vector⟩⟧ : GlobalCombinedFiber G) := rfl

theorem evaluator_eq_of_equivalent {p q : Representative X C ι V}
    (h : CombinedPrincipalSymbol.Equivalent G p q) :
    G.evaluator ⟦p⟧ = G.evaluator ⟦q⟧ := by
  rw [Quotient.sound h]

end CombinedPrincipalSymbol

end
end ParabolicPDE
end Topping

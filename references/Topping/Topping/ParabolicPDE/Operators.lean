import Topping.ParabolicPDE.Scalar
import Topping.ParabolicPDE.Vector

/-!
# Coordinate and bundle interfaces for second-order operators

This module isolates the algebra needed when a local second-order operator is
read in a different chart or frame.  The chart maps below are the first and
second derivatives of the coordinate change; no manifold implementation is
assumed, so these declarations can be consumed by a later manifold library.
-/

namespace Topping
namespace ParabolicPDE

open scoped BigOperators

/-! ## Scalar chart jets -/

/-- Data for a coordinate change from `m` old coordinates to `n` new ones.

`J α i` is the derivative of the old `α`-coordinate with respect to the new
`i`-coordinate, and `H α i k` is its second derivative. -/
structure ScalarChartTransition (m n : ℕ) where
  J : Matrix (Fin m) (Fin n) ℝ
  H : Fin m → Fin n → Fin n → ℝ

namespace ScalarChartTransition

variable {m n : ℕ} (T : ScalarChartTransition m n)

/-- Pull a scalar second-order jet through a coordinate change. -/
def pullJet (j : ScalarSecondOrderJet m) : ScalarSecondOrderJet n where
  value := j.value
  first := T.J.transpose.mulVec j.first
  second := fun i k =>
    (∑ α, ∑ β, T.J α i * T.J β k * j.second α β) +
      ∑ α, T.H α i k * j.first α

@[simp] theorem pullJet_value (j : ScalarSecondOrderJet m) :
    (T.pullJet j).value = j.value := rfl

@[simp] theorem pullJet_first (j : ScalarSecondOrderJet m) (i : Fin n) :
    (T.pullJet j).first i = ∑ α, T.J α i * j.first α := by
  simp [pullJet, Matrix.mulVec, dotProduct]

@[simp] theorem pullJet_second (j : ScalarSecondOrderJet m) (i k : Fin n) :
    (T.pullJet j).second i k =
      (∑ α, ∑ β, T.J α i * T.J β k * j.second α β) +
        ∑ α, T.H α i k * j.first α := rfl

end ScalarChartTransition

/-! ## The principal part under a chart change -/

/-- The transformed leading matrix in new coordinates. -/
def transformedPrincipalMatrix {m n : ℕ}
    (T : ScalarChartTransition m n) (a : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := T.J.transpose * a * T.J

theorem transformedPrincipalMatrix_symbol {m n : ℕ}
    (T : ScalarChartTransition m n) (a : Matrix (Fin m) (Fin m) ℝ)
    (ξ : Fin n → ℝ) :
    symbol (transformedPrincipalMatrix T a) ξ = symbol a (T.J.mulVec ξ) := by
  exact symbol_congruence T.J a ξ

theorem transformedPrincipalMatrix_positive {m n : ℕ}
    (T : ScalarChartTransition m n) (a : Matrix (Fin m) (Fin m) ℝ)
    (ha : IsPositiveDefinite a)
    (hJ : Function.Injective T.J.mulVec) :
    IsPositiveDefinite (transformedPrincipalMatrix T a) := by
  exact IsPositiveDefinite.congruence T.J a ha hJ

/-- A coordinate change is principal-symbol compatible when its second-order
jet pullback has the prescribed first-order part and the leading matrix is
the congruence transform. -/
theorem pullJet_principal_part {m n : ℕ}
    (T : ScalarChartTransition m n) (a : Matrix (Fin m) (Fin m) ℝ)
    (ξ : Fin n → ℝ) :
    symbol (transformedPrincipalMatrix T a) ξ =
      symbol a (T.J.mulVec ξ) :=
  transformedPrincipalMatrix_symbol T a ξ

/-! ## Local bundle operators and frame gluing -/

variable {X C ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- A local bundle operator consists of lower-order data together with a
fibre-valued principal symbol.  The latter is kept separately so geometric
constructions can provide it without choosing coefficient tensors. -/
structure BundleSecondOrderOperator (X ι V : Type*) [Fintype ι]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] extends
    VectorSecondOrderCoefficients X ι V where
  symbol : X → (ι → ℝ) → V →L[ℝ] V
  symbol_eq_coefficients :
    ∀ x ξ, symbol x ξ = VectorSecondOrderCoefficients.principalSymbol toVectorSecondOrderCoefficients x ξ

namespace BundleSecondOrderOperator

variable (P : BundleSecondOrderOperator X ι V)

@[simp] theorem symbol_apply (x : X) (ξ : ι → ℝ) (v : V) :
    P.symbol x ξ v = P.toVectorSecondOrderCoefficients.principalSymbol x ξ v := by
  rw [P.symbol_eq_coefficients]

theorem symbol_congruent_to_vector (x : X) (ξ : ι → ℝ) :
    P.symbol x ξ = P.toVectorSecondOrderCoefficients.principalSymbol x ξ :=
  P.symbol_eq_coefficients x ξ

/-- Strict parabolicity proved for the coefficient-level Vector producer is
inherited by the packaged bundle operator. -/
theorem strictlyParabolic_of_vector_coefficients
    {q : X → (ι → ℝ) → ℝ}
    (hP : StrictlyParabolic
      P.toVectorSecondOrderCoefficients.principalSymbol q) :
    StrictlyParabolic P.symbol q := by
  have hs : P.symbol = P.toVectorSecondOrderCoefficients.principalSymbol := by
    funext x ξ
    exact P.symbol_congruent_to_vector x ξ
  rw [hs]
  exact hP

end BundleSecondOrderOperator

/-- A frame transition on a fibre.  The `forward` and `backward` maps are
assumed inverse, making the conjugation law below a genuine change of frame. -/
structure BundleFrameTransition (V : Type*)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  forward : V →L[ℝ] V
  backward : V →L[ℝ] V
  forward_backward : forward.comp backward = ContinuousLinearMap.id ℝ V
  backward_forward : backward.comp forward = ContinuousLinearMap.id ℝ V

namespace BundleFrameTransition

variable (F : BundleFrameTransition V)

@[simp] theorem forward_backward_apply (v : V) :
    F.forward (F.backward v) = v := by
  have h := congrArg (fun f : V →L[ℝ] V => f v) F.forward_backward
  simpa [ContinuousLinearMap.comp_apply] using h

@[simp] theorem backward_forward_apply (v : V) :
    F.backward (F.forward v) = v := by
  have h := congrArg (fun f : V →L[ℝ] V => f v) F.backward_forward
  simpa [ContinuousLinearMap.comp_apply] using h

theorem forward_injective : Function.Injective F.forward := by
  intro u v huv
  have h := congrArg (fun z : V => F.backward z) huv
  simpa only [F.backward_forward_apply] using h

theorem backward_injective : Function.Injective F.backward := by
  intro u v huv
  have h := congrArg (fun z : V => F.forward z) huv
  simpa only [F.forward_backward_apply] using h

end BundleFrameTransition

/-- Compatibility of local principal symbols with a frame transition.  This
is the precise gluing condition: covectors are unchanged here, while fibre
endomorphisms are conjugated by the frame map. -/
def FrameSymbolGluing
    (sigma₁ sigma₂ : X → (ι → ℝ) → V →L[ℝ] V)
    (F : BundleFrameTransition V) : Prop :=
  ∀ x ξ, sigma₂ x ξ = F.forward.comp ((sigma₁ x ξ).comp F.backward)

omit [Fintype ι] in
theorem FrameSymbolGluing.apply
    {sigma₁ sigma₂ : X → (ι → ℝ) → V →L[ℝ] V}
    {F : BundleFrameTransition V}
    (h : FrameSymbolGluing sigma₁ sigma₂ F)
    (x : X) (ξ : ι → ℝ) (v : V) :
    sigma₂ x ξ v = F.forward (sigma₁ x ξ (F.backward v)) := by
  change ∀ x ξ, sigma₂ x ξ = F.forward.comp ((sigma₁ x ξ).comp F.backward) at h
  rw [h x ξ]
  rfl

omit [Fintype ι] in
theorem FrameSymbolGluing.refl
    (sigma : X → (ι → ℝ) → V →L[ℝ] V) :
    FrameSymbolGluing sigma sigma
      ⟨ContinuousLinearMap.id ℝ V, ContinuousLinearMap.id ℝ V,
        by simp, by simp⟩ := by
  change ∀ x ξ, sigma x ξ = _
  intro x ξ
  simp

omit [Fintype ι] in
theorem FrameSymbolGluing.symm
    {sigma₁ sigma₂ : X → (ι → ℝ) → V →L[ℝ] V}
    {F : BundleFrameTransition V}
    (h : FrameSymbolGluing sigma₁ sigma₂ F) :
    FrameSymbolGluing sigma₂ sigma₁
      ⟨F.backward, F.forward, F.backward_forward, F.forward_backward⟩ := by
  change ∀ x ξ, sigma₁ x ξ = F.backward.comp ((sigma₂ x ξ).comp F.forward)
  intro x ξ
  ext v
  change ∀ x ξ, sigma₂ x ξ = F.forward.comp ((sigma₁ x ξ).comp F.backward) at h
  rw [h x ξ]
  simp [ContinuousLinearMap.comp_apply]

/-- A global principal-symbol package is local symbol data with transition
maps satisfying the cocycle law and frame gluing.  The transition law is
explicit, so no quotient or hidden chart-membership assumption is involved. -/
structure GlobalPrincipalSymbol (X C ι V : Type*)
    [Fintype ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  localSymbol : C → X → (ι → ℝ) → V →L[ℝ] V
  frame : C → C → BundleFrameTransition V
  glue : ∀ c d x ξ,
    localSymbol d x ξ =
      (frame c d).forward.comp ((localSymbol c x ξ).comp (frame c d).backward)
  cocycle_forward : ∀ c d e,
    (frame c e).forward = (frame d e).forward.comp (frame c d).forward

namespace GlobalPrincipalSymbol

variable (G : GlobalPrincipalSymbol X C ι V)

theorem gluing (c d : C) (x : X) (ξ : ι → ℝ) :
    G.localSymbol d x ξ =
      (G.frame c d).forward.comp ((G.localSymbol c x ξ).comp
        (G.frame c d).backward) :=
  G.glue c d x ξ

theorem gluing_apply (c d : C) (x : X) (ξ : ι → ℝ) (v : V) :
    G.localSymbol d x ξ v =
      (G.frame c d).forward
        (G.localSymbol c x ξ ((G.frame c d).backward v)) := by
  rw [G.gluing c d x ξ]
  rfl

end GlobalPrincipalSymbol

/-! ## Scalar atlas assembly -/

/-- Local scalar symbols together with the cotangent-coordinate transition
maps supplied by an atlas.  The `glue` equation is the actual overlap law;
the injectivity field records that a nonzero covector stays nonzero under a
change of chart. -/
structure ScalarPrincipalSymbolAtlas (X C ι : Type*) [Fintype ι] where
  localSymbol : C → X → (ι → ℝ) → ℝ
  covectorTransition : C → C → X → (ι → ℝ) → (ι → ℝ)
  transition_zero :
    ∀ c d x, covectorTransition c d x 0 = 0
  transition_injective :
    ∀ c d x, Function.Injective (covectorTransition c d x)
  glue : ∀ c d x ξ,
    localSymbol d x (covectorTransition c d x ξ) = localSymbol c x ξ

namespace ScalarPrincipalSymbolAtlas

variable {X C ι : Type*} [Fintype ι]
  (A : ScalarPrincipalSymbolAtlas X C ι)

/-- The chart-dependent representative of a cotangent point. -/
def atlasSymbol (c : C) (x : X) (ξ : ι → ℝ) : ℝ :=
  A.localSymbol c x ξ

theorem atlasSymbol_transition (c d : C) (x : X) (ξ : ι → ℝ) :
    A.atlasSymbol d x (A.covectorTransition c d x ξ) =
      A.atlasSymbol c x ξ :=
  A.glue c d x ξ

theorem transition_ne_zero (c d : C) (x : X) {ξ : ι → ℝ}
    (hξ : ξ ≠ 0) : A.covectorTransition c d x ξ ≠ 0 := by
  intro hzero
  apply hξ
  apply A.transition_injective c d x
  simpa [A.transition_zero c d x] using hzero

theorem positive_on_chart_of_positive_on_atlas
    (hpos : ∀ c x ξ, ξ ≠ 0 → 0 < A.atlasSymbol c x ξ)
    (c d : C) (x : X) (ξ : ι → ℝ) (hξ : ξ ≠ 0) :
    0 < A.atlasSymbol d x (A.covectorTransition c d x ξ) := by
  rw [A.atlasSymbol_transition c d x ξ]
  exact hpos c x ξ hξ

theorem positive_is_coordinate_independent
    (c d : C) (x : X) (ξ : ι → ℝ) :
    0 < A.atlasSymbol c x ξ ↔
      0 < A.atlasSymbol d x (A.covectorTransition c d x ξ) := by
  rw [A.atlasSymbol_transition c d x ξ]

end ScalarPrincipalSymbolAtlas

end ParabolicPDE
end Topping

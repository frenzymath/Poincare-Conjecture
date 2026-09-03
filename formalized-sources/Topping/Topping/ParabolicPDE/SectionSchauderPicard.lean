import Topping.ParabolicPDE.HolderBallConsumers
import Topping.ParabolicPDE.SectionSpacePicard

/-!
# Quantitative Schauder-to-Picard composition

The section-space Holder ball is useful only when a source map and a solution
operator can be composed while preserving both the Holder cone and a uniform
ball.  This module supplies the elementary quantitative part of that
composition.  The source and solver estimates remain explicit hypotheses; no
closed-manifold Schauder theorem is asserted here.
-/

namespace Topping
namespace ParabolicPDE

open Function Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

/-! ## Metric composition estimates -/

/-- A Lipschitz map sends one closed ball into another when the image of the
center has a controlled residual. -/
theorem mapsTo_closedBall_of_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : X → Y} {K : ℝ≥0} {c : X} {d : Y}
    {r R ε : ℝ}
    (hf : LipschitzWith K f)
    (hcenter : dist (f c) d ≤ ε)
    (hresidual : (K : ℝ) * r + ε ≤ R) :
    MapsTo f (Metric.closedBall c r) (Metric.closedBall d R) := by
  intro x hx
  rw [Metric.mem_closedBall] at hx ⊢
  calc
    dist (f x) d ≤ dist (f x) (f c) + dist (f c) d :=
      dist_triangle _ _ _
    _ ≤ (K : ℝ) * dist x c + ε := by
      exact add_le_add (hf.dist_le_mul x c) hcenter
    _ ≤ (K : ℝ) * r + ε := by
      simpa only [add_comm] using
        add_le_add_right
          (mul_le_mul_of_nonneg_left hx (NNReal.coe_nonneg K)) ε
    _ ≤ R := hresidual

/-- Lipschitz constants multiply under composition. -/
theorem lipschitzWith_comp
    {X Y Z : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    [PseudoMetricSpace Z]
    {f : Y → Z} {g : X → Y} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g) :
    LipschitzWith (K * L) (f ∘ g) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist ((f ∘ g) x) ((f ∘ g) y) ≤
        (K : ℝ) * dist (g x) (g y) := by
      simpa only [Function.comp_apply] using hf.dist_le_mul (g x) (g y)
    _ ≤ (K : ℝ) * ((L : ℝ) * dist x y) := by
      exact mul_le_mul_of_nonneg_left (hg.dist_le_mul x y)
        (NNReal.coe_nonneg K)
    _ = ((K * L : ℝ≥0) : ℝ) * dist x y := by
      rw [NNReal.coe_mul]
      ring

/-- Two Lipschitz maps whose constants multiply to less than one give a
contracting composition. -/
theorem contractingWith_comp_of_lipschitz
    {X Y : Type*} [MetricSpace X] [PseudoMetricSpace Y]
    {f : Y → X} {g : X → Y} {K L : ℝ≥0}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hKL : K * L < 1) :
    ContractingWith (K * L) (f ∘ g) :=
  ⟨hKL, lipschitzWith_comp hf hg⟩

/-! ## Holder-ball composition -/

/-- Explicit source-map and solver estimates compose to an invariant
parabolic Holder ball.  The `hcenter`/`hresidual` pair is the quantitative
center-error condition; it is the only ball estimate needed in addition to
the two Lipschitz bounds. -/
theorem mapsTo_parabolicHolderSectionBallSet_of_lipschitz_comp
    {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [MetricSpace V]
    {S : Set X} {J : Set T} {Cs α Ct β K L : NNReal}
    (center : (S × J) →ᵇ V) (radius ε : ℝ)
    {f g : BoundedSectionSpace (S × J) V →
      BoundedSectionSpace (S × J) V}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hcenter : dist (f (g center)) center ≤ ε)
    (hresidual : ((K * L : NNReal) : ℝ) * radius + ε ≤ radius)
    (hg_holder : ∀ u ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β,
      g u ∈ ParabolicHolderSectionSet
        (X := X) (T := T) (V := V) S J Cs α Ct β)
    (hf_holder : ∀ u ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β,
      f u ∈ ParabolicHolderSectionSet
        (X := X) (T := T) (V := V) S J Cs α Ct β) :
    MapsTo (f ∘ g)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius) := by
  have hcomp_holder : ∀ u ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β,
      (f ∘ g) u ∈ ParabolicHolderSectionSet
        (X := X) (T := T) (V := V) S J Cs α Ct β := by
    intro u hu
    exact hf_holder (g u) (hg_holder u hu)
  have hcomp_lip : LipschitzWith (K * L) (f ∘ g) :=
    lipschitzWith_comp hf hg
  have hcomp_ball : MapsTo (f ∘ g)
      (Metric.closedBall center radius)
      (Metric.closedBall center radius) := by
    simpa only [Function.comp_apply] using
      (mapsTo_closedBall_of_lipschitz hcomp_lip hcenter hresidual)
  intro u hu
  exact ⟨hcomp_holder u hu.1, hcomp_ball hu.2⟩

/-- The preceding composition package immediately supplies a Holder-ball
fixed point once the center itself is Holder and the product constant is
strictly contracting. -/
theorem exists_parabolicHolderSectionBall_fixedPoint_of_lipschitz_comp
    {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [MetricSpace V] [CompleteSpace V]
    {S : Set X} {J : Set T} {Cs α Ct β K L : NNReal}
    (center : (S × J) →ᵇ V) (radius ε : ℝ)
    {f g : BoundedSectionSpace (S × J) V →
      BoundedSectionSpace (S × J) V}
    (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hKL : K * L < 1)
    (hcenter : dist (f (g center)) center ≤ ε)
    (hradius : 0 ≤ radius)
    (hresidual : ((K * L : NNReal) : ℝ) * radius + ε ≤ radius)
    (hcenter_holder : center ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β)
    (hg_holder : ∀ u ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β,
      g u ∈ ParabolicHolderSectionSet
        (X := X) (T := T) (V := V) S J Cs α Ct β)
    (hf_holder : ∀ u ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β,
      f u ∈ ParabolicHolderSectionSet
        (X := X) (T := T) (V := V) S J Cs α Ct β) :
    ∃ u : ParabolicHolderSectionBall
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius,
      IsFixedPt (f ∘ g) u.1 := by
  have hmap := mapsTo_parabolicHolderSectionBallSet_of_lipschitz_comp
    center radius ε hf hg hcenter hresidual hg_holder hf_holder
  exact exists_parabolicHolderSectionBall_fixedPoint center hcenter_holder
    hradius hmap (contractingWith_comp_of_lipschitz hf hg hKL)

#print axioms mapsTo_closedBall_of_lipschitz
#print axioms lipschitzWith_comp
#print axioms contractingWith_comp_of_lipschitz
#print axioms mapsTo_parabolicHolderSectionBallSet_of_lipschitz_comp
#print axioms exists_parabolicHolderSectionBall_fixedPoint_of_lipschitz_comp

end
end ParabolicPDE
end Topping

import Topping.ParabolicPDE.Vector

/-!
# Pointwise Nemytskii laws for second-order jet operators

The geometric DeTurck section map is assembled from local coefficient maps and
second-order jets.  This file records the unconditional local analytic
boundary needed by that assembly: evaluation on jet data is a
continuous linear (hence differentiable) map.  No manifold chart or section
regularity is assumed here.
-/

namespace Topping

noncomputable section

open scoped BigOperators

variable {X ι V : Type*} [Fintype ι]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace VectorSecondOrderCoefficients

variable (A : VectorSecondOrderCoefficients X ι V) (x : X)

/-- Evaluation of a vector second-order operator on separate jet slots. -/
def applyJetArgs (value : V) (first : ι → V) (second : ι → ι → V) : V :=
  (∑ i, ∑ k, A.a x i k (second i k)) +
    (∑ i, A.b x i (first i)) + A.c x value

@[simp] theorem applyJetArgs_eq_applyJet (j : VectorSecondOrderJet ι V) :
    A.applyJet x j = A.applyJetArgs x j.value j.first j.second := rfl

theorem continuous_applyJetArgs :
    Continuous (fun z : V × (ι → V) × (ι → ι → V) =>
      A.applyJetArgs x z.1 z.2.1 z.2.2) := by
  simp only [applyJetArgs]
  fun_prop

theorem differentiable_applyJetArgs :
    Differentiable ℝ (fun z : V × (ι → V) × (ι → ι → V) =>
      A.applyJetArgs x z.1 z.2.1 z.2.2) := by
  simp only [applyJetArgs]
  fun_prop

@[simp] theorem applyJetArgs_add
    (value₁ value₂ : V) (first₁ first₂ : ι → V)
    (second₁ second₂ : ι → ι → V) :
    A.applyJetArgs x (value₁ + value₂) (first₁ + first₂) (second₁ + second₂) =
      A.applyJetArgs x value₁ first₁ second₁ +
        A.applyJetArgs x value₂ first₂ second₂ := by
  simp only [applyJetArgs, Pi.add_apply, map_add, Finset.sum_add_distrib,
    add_add_add_comm]

@[simp] theorem applyJetArgs_smul
    (c : ℝ) (value : V) (first : ι → V) (second : ι → ι → V) :
    A.applyJetArgs x (c • value) (c • first) (c • second) =
      c • A.applyJetArgs x value first second := by
  simp only [applyJetArgs, Pi.smul_apply, map_smul, Finset.smul_sum,
    smul_add]

end VectorSecondOrderCoefficients
end
end Topping

import Topping.ParabolicPDE.MetricChartHolderExponent
import Topping.ParabolicPDE.VectorJetCoefficientBridge

/-!
# A concrete metric-chart Holder-section consumer

The universal metric-chart estimate accepts an explicitly supplied bounded
jet section.  This module supplies that section from a `C^3` vector map and
then downgrades the resulting Lipschitz control to the exponents used by a
parabolic Holder scale.  The chart carrier, path, and time set stay explicit;
no atlas gluing, global bundle identification, or Schauder solution operator
is introduced.
-/

namespace Topping
namespace ParabolicPDE

open Set Riemannian
open scoped BigOperators BoundedContinuousFunction ContDiff Manifold Topology
  Bundle NNReal ENNReal
open Topping.VectorSecondOrderCoefficients

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : Set T}

namespace ChartCoefficientSections

variable [CompactSpace X] [CompactSpace T]

/-- **Math.** A `C^3` vector map sampled along a compact chart path produces an
actual element of the parabolic Holder section set after the metric-chart
operator is evaluated.  The constants and the exponent downgrade are
existential, while the chart carrier, path, and time subset are explicit.

This is a chart-local producer for later Schauder work.  In particular, the
statement does not identify these sections across an atlas or assert a global
parabolic solution. -/
theorem exists_metricChartOperator_holderSectionSet_of_smooth_vector_map
    {S : Set X} [CompactSpace S] (hS : IsCompact S) (hJ : IsCompact J)
    (g : RiemannianMetric I M) (alpha : M)
    {K : Set E} (hKtarget : K ⊆ (extChartAt I alpha).target)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (chi : S × T → ChartTarget I alpha) (hchi : Continuous chi)
    (hchiK : ∀ z, (chi z).1 ∈ K)
    {LchiS LchiT : ℝ≥0}
    (hchiS : ∀ t ∈ J,
      LipschitzWith LchiS (fun x : S => (chi (x, t)).1))
    (hchiT : ∀ x : S,
      LipschitzOnWith LchiT (fun t : T => (chi (x, t)).1) J)
    {α β : ℝ≥0} (hα : α ≤ 1) (hβ : β ≤ 1)
    (u : E → V) (hu : ContDiff ℝ 3 u) :
    ∃ (Cs Ct : ℝ≥0),
      restrictTimeSubtype (S := S) (J := J)
        (variableCoefficientSectionsApplyJetArgs
          (metricChartCoefficientSections (V := V) g alpha chi hchi)
          (vectorJetSectionsOf (T := S × T) u (hu.of_le (by norm_num))
            (fun z => (chi z).1) (continuous_subtype_val.comp hchi))) ∈
        ParabolicHolderSectionSet (X := X) (T := T) (V := V)
          S J Cs α Ct β := by
  classical
  let chiE : S × T → E := fun z => (chi z).1
  have hchiE : Continuous chiE := continuous_subtype_val.comp hchi
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  let Z : VariableJetSections (T := S × T)
      (ι := Fin (Module.finrank ℝ E)) (V := V) :=
    vectorJetSectionsOf (T := S × T) u hu2 chiE hchiE
  let C : VariableCoefficientSections (T := S × T)
      (ι := Fin (Module.finrank ℝ E)) (V := V) :=
    metricChartCoefficientSections (V := V) g alpha chi hchi
  let f : (S × T) →ᵇ V :=
    variableCoefficientSectionsApplyJetArgs C Z

  obtain ⟨Cs₁, Ct₁, hoperator⟩ :=
    exists_metricChartOperator_vectorBasisJet_parabolicHolderControl
      (X := S) (T := T) (J := J) (V := V) g alpha hKtarget hKconv
      hKcompact chi hchi hchiK hchiS hchiT u hu

  have hoperator_eq :
      (fun z : S × T => f z) =
        (fun z =>
          ((_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
            (I := I) g alpha V).toVectorSecondOrderCoefficients).applyJet
            (chi z) (vectorBasisJetAt u (chi z).1)) := by
    funext z
    change variableCoefficientSectionsApplyJetArgs C Z z = _
    simpa only [C, Z, f, chiE, hchiE] using
      metricChartCoefficientSections_apply_vectorJetSections
        (I := I) g alpha chi hchi u hu2 z

  have hf₁ : ParabolicHolderControl (fun z : S × T => f z) J
      Cs₁ 1 Ct₁ 1 := by
    rw [hoperator_eq]
    exact hoperator

  obtain ⟨DX, hDX⟩ :=
    exists_edist_bound_of_isCompact_local (Y := X) (A := S) hS
  obtain ⟨DT, hDT⟩ :=
    exists_edist_bound_of_isCompact_local (Y := T) (A := J) hJ
  have hX : ∀ x y : S, edist x y ≤ DX := by
    intro x y
    exact hDX x x.2 y y.2
  have hT : ∀ s ∈ J, ∀ t ∈ J, edist s t ≤ DT := by
    intro s hs t ht
    exact hDT s hs t ht

  refine ⟨Cs₁ * DX ^ ((1 : ℝ) - (α : ℝ)),
    Ct₁ * DT ^ ((1 : ℝ) - (β : ℝ)), ?_⟩
  apply mem_parabolicHolderSectionSet_of_parabolicHolderControl f
  exact ParabolicHolderControl.of_le_exponents hf₁ hX hT hα hβ

end ChartCoefficientSections

end
end ParabolicPDE
end Topping

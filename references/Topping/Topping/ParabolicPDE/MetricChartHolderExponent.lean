import Topping.ParabolicPDE.MetricChartHolderConsumer
import Topping.ParabolicPDE.ParabolicHolderExponent

/-!
# Mixed-exponent metric-chart Holder control

The chart coefficient producer is naturally Lipschitz.  On bounded space and
time carriers this gives the lower exponents used by a Schauder scale, with
the diameter loss made explicit.  This module performs that downgrade before
the universal jet evaluator is assembled.
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

/-- **Math.** A compact-carrier metric-chart evaluator preserves arbitrary
lower Holder exponents.  Its coefficient constants are obtained at exponent
one and downgraded using the explicit spatial and temporal diameter bounds;
the value and jet fields are controlled directly at `α, β`. -/
theorem exists_metricChartOperator_parabolicHolderControl_of_jetSections_of_le_exponents
    (g : RiemannianMetric I M) (alpha : M)
    {K : Set E} (hKtarget : K ⊆ (extChartAt I alpha).target)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (chi : X × T → ChartTarget I alpha) (hchi : Continuous chi)
    (hchiK : ∀ z, (chi z).1 ∈ K)
    {LchiS LchiT : ℝ≥0}
    (hchiS : ∀ t ∈ J,
      LipschitzWith LchiS (fun x : X => (chi (x, t)).1))
    (hchiT : ∀ x : X,
      LipschitzOnWith LchiT (fun t : T => (chi (x, t)).1) J)
    {α β DX DT : ℝ≥0} (hα : α ≤ 1) (hβ : β ≤ 1)
    (hX : ∀ x y : X, edist x y ≤ DX)
    (hT : ∀ s ∈ J, ∀ t ∈ J, edist s t ≤ DT)
    (Z : VariableJetSections (T := X × T)
      (ι := Fin (Module.finrank ℝ E)) (V := V))
    (valueCs valueCt valueB : ℝ≥0)
    (hvalue : ParabolicHolderControl (fun z => Z.1 z) J
      valueCs α valueCt β)
    (hvalue_bound : ∀ z, ‖Z.1 z‖ ≤ valueB)
    (firstCs firstCt : Fin (Module.finrank ℝ E) → ℝ≥0)
    (firstB : Fin (Module.finrank ℝ E) → ℝ≥0)
    (hfirst : ∀ i, ParabolicHolderControl (fun z => Z.2.1 i z) J
      (firstCs i) α (firstCt i) β)
    (hfirst_bound : ∀ i z, ‖Z.2.1 i z‖ ≤ firstB i)
    (secondCs secondCt : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (secondB : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (hsecond : ∀ i k, ParabolicHolderControl
      (fun z => Z.2.2 i k z) J (secondCs i k) α
        (secondCt i k) β)
    (hsecond_bound : ∀ i k z, ‖Z.2.2 i k z‖ ≤ secondB i k) :
    ∃ (Cs Ct : ℝ≥0), ParabolicHolderControl
      (fun z => variableCoefficientSectionsApplyJetArgs
        (metricChartCoefficientSections (V := V) g alpha chi hchi) Z z)
      J Cs α Ct β := by
  classical
  let chiE : X × T → E := fun z => (chi z).1
  have hchiE : Continuous chiE := continuous_subtype_val.comp hchi
  let C := metricChartCoefficientSections (V := V) g alpha chi hchi
  let A := variableCoefficientSectionsToCoefficients C
  have haOne : ∀ i k, ∃ (aCs aCt : ℝ≥0),
      ParabolicHolderControl (fun z : X × T => A.a z i k) J
        aCs 1 aCt 1 := by
    intro i k
    simpa only [A, C, variableCoefficientSectionsToCoefficients,
      metricChartCoefficientSections_apply] using
      exists_metricChartCoefficient_parabolicHolderControl
        (I := I) (V := V) (J := J) g alpha hKtarget hKconv hKcompact
          chiE (fun z => hchiK z) hchiS hchiT i k
  choose aCs aCt haOne using haOne
  have ha : ∀ i k, ∃ (aCs' aCt' : ℝ≥0),
      ParabolicHolderControl (fun z : X × T => A.a z i k) J
        aCs' α aCt' β := by
    intro i k
    exact ⟨aCs i k * DX ^ ((1 : ℝ) - (α : ℝ)),
      aCt i k * DT ^ ((1 : ℝ) - (β : ℝ)),
      ParabolicHolderControl.of_le_exponents (haOne i k) hX hT hα hβ⟩
  choose aCs' aCt' ha using ha
  have hzero : ParabolicHolderControl
      (fun _ : X × T => (0 : V →L[ℝ] V)) J 0 α 0 β := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp [SpatialHolderWith]
    · intro x s hs t ht
      simp
  let d : VectorSecondOrderCoefficients.SectionHolderJetData A J α β := {
    value := fun z => Z.1 z
    first := fun i z => Z.2.1 i z
    second := fun i k z => Z.2.2 i k z
    valueCs := valueCs
    valueCt := valueCt
    valueB := valueB
    firstCs := firstCs
    firstCt := firstCt
    firstB := firstB
    secondCs := secondCs
    secondCt := secondCt
    secondB := secondB
    aCs := aCs'
    aCt := aCt'
    aB := fun i k => ‖C.1 i k‖₊
    bCs := fun _ => 0
    bCt := fun _ => 0
    bB := fun i => ‖C.2.1 i‖₊
    cCs := 0
    cCt := 0
    cB := ‖C.2.2‖₊
    value_control := hvalue
    first_control := hfirst
    second_control := hsecond
    a_control := by
      intro i k
      exact ha i k
    b_control := by
      intro i
      exact hzero
    c_control := hzero
    a_bound := by
      intro i k z
      change ‖C.1 i k z‖ ≤ (‖C.1 i k‖₊ : ℝ)
      exact (C.1 i k).norm_coe_le_norm z
    b_bound := by
      intro i z
      change ‖C.2.1 i z‖ ≤ (‖C.2.1 i‖₊ : ℝ)
      exact (C.2.1 i).norm_coe_le_norm z
    c_bound := by
      intro z
      change ‖C.2.2 z‖ ≤ (‖C.2.2‖₊ : ℝ)
      exact C.2.2.norm_coe_le_norm z
    value_bound := hvalue_bound
    first_bound := hfirst_bound
    second_bound := hsecond_bound
  }
  have hd := d.applyJetArgs_control
  have heval :
      (fun z => A.applyJetArgs z (d.value z)
        (fun i => d.first i z) (fun i k => d.second i k z)) =
      (fun z => variableCoefficientSectionsApplyJetArgs C Z z) := by
    funext z
    change A.applyJetArgs z (Z.1 z)
      (fun i => Z.2.1 i z) (fun i k => Z.2.2 i k z) = _
    rfl
  rw [heval] at hd
  let Cs : ℝ≥0 :=
    (∑ i, ∑ k, (d.aB i k * d.secondCs i k +
      d.aCs i k * d.secondB i k)) +
      (∑ i, (d.bB i * d.firstCs i + d.bCs i * d.firstB i)) +
        (d.cB * d.valueCs + d.cCs * d.valueB)
  let Ct : ℝ≥0 :=
    (∑ i, ∑ k, (d.aB i k * d.secondCt i k +
      d.aCt i k * d.secondB i k)) +
      (∑ i, (d.bB i * d.firstCt i + d.bCt i * d.firstB i)) +
        (d.cB * d.valueCt + d.cCt * d.valueB)
  exact ⟨Cs, Ct, by simpa only [Cs, Ct] using hd⟩

/-! ## Direct section-space packaging -/

theorem exists_edist_bound_of_isCompact_local {Y : Type*}
    [PseudoMetricSpace Y] {A : Set Y} (hA : IsCompact A) :
    ∃ D : ℝ≥0, ∀ x ∈ A, ∀ y ∈ A, edist x y ≤ D := by
  have hb : Bornology.IsBounded A := hA.isBounded
  obtain ⟨D, hD⟩ := (Metric.isBounded_iff_nndist).mp hb
  refine ⟨D, ?_⟩
  intro x hx y hy
  simpa only [edist_nndist, ENNReal.coe_le_coe] using hD hx hy

/-- **Math.** On compact spatial and time carriers, the mixed-exponent metric
chart estimate is directly an element of the Holder section set used by the
Picard interface.  The jet controls and chart path are explicit inputs; this
does not construct the universal DeTurck map or a Schauder solution operator. -/
theorem exists_metricChartOperator_holderSectionSet_of_jetSections_of_le_exponents
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
    (Z : VariableJetSections (T := S × T)
      (ι := Fin (Module.finrank ℝ E)) (V := V))
    (valueCs valueCt valueB : ℝ≥0)
    (hvalue : ParabolicHolderControl (fun z => Z.1 z) J
      valueCs α valueCt β)
    (hvalue_bound : ∀ z, ‖Z.1 z‖ ≤ valueB)
    (firstCs firstCt : Fin (Module.finrank ℝ E) → ℝ≥0)
    (firstB : Fin (Module.finrank ℝ E) → ℝ≥0)
    (hfirst : ∀ i, ParabolicHolderControl (fun z => Z.2.1 i z) J
      (firstCs i) α (firstCt i) β)
    (hfirst_bound : ∀ i z, ‖Z.2.1 i z‖ ≤ firstB i)
    (secondCs secondCt : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (secondB : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (hsecond : ∀ i k, ParabolicHolderControl
      (fun z => Z.2.2 i k z) J (secondCs i k) α
        (secondCt i k) β)
    (hsecond_bound : ∀ i k z, ‖Z.2.2 i k z‖ ≤ secondB i k) :
    ∃ (Cs Ct : ℝ≥0),
      restrictTimeSubtype (S := S) (J := J)
        (variableCoefficientSectionsApplyJetArgs
          (metricChartCoefficientSections (V := V) g alpha chi hchi) Z) ∈
        ParabolicHolderSectionSet (X := X) (T := T) (V := V)
          S J Cs α Ct β := by
  obtain ⟨DX, hDX⟩ := exists_edist_bound_of_isCompact_local hS
  obtain ⟨DT, hDT⟩ := exists_edist_bound_of_isCompact_local hJ
  have hX : ∀ x y : S, edist x y ≤ DX := by
    intro x y
    exact hDX x x.2 y y.2
  have hT : ∀ s ∈ J, ∀ t ∈ J, edist s t ≤ DT := by
    intro s hs t ht
    exact hDT s hs t ht
  obtain ⟨Cs, Ct, hC⟩ :=
    exists_metricChartOperator_parabolicHolderControl_of_jetSections_of_le_exponents
      (X := S) (T := T) (J := J) g alpha hKtarget hKconv hKcompact
      chi hchi hchiK hchiS hchiT hα hβ hX hT Z valueCs valueCt valueB
      hvalue hvalue_bound firstCs firstCt firstB hfirst hfirst_bound
      secondCs secondCt secondB hsecond hsecond_bound
  refine ⟨Cs, Ct, ?_⟩
  apply mem_parabolicHolderSectionSet_of_parabolicHolderControl
  simpa only [restrictTimeSubtype_apply] using hC

end ChartCoefficientSections

end
end ParabolicPDE
end Topping

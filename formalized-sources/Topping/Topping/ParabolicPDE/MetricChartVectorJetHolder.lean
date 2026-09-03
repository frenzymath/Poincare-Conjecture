import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import Topping.ParabolicPDE.SectionSchauder
import Topping.ParabolicPDE.VectorJetCoefficientBridge
import Topping.ParabolicPDE.VectorJetHolder

/-!
# Holder control for metric-chart operators on sampled vector jets

This module joins the local metric coefficient and vector-jet producers at the
regularity level consumed by the section-space Schauder API.  On a compact
convex subset of a chart target, smoothness of the inverse Gram entries gives
Holder control of the principal endomorphism coefficients.  Combining those
controls with the sampled `C^3` vector jets yields an unconditional Holder
control for the actual metric chart operator.

The result remains chart-local: the carrier, chart-target path, and its
separate spatial and temporal Lipschitz bounds are explicit.  No global bundle
identification or parabolic solution operator is asserted here.
-/

namespace Topping
namespace ParabolicPDE

open Set Riemannian
open scoped BoundedContinuousFunction ContDiff Manifold Topology Bundle
open scoped BigOperators NNReal ENNReal
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

/-! ## Principal-coefficient control -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** An inverse-Gram entry, viewed as a scalar multiple of the fibre
identity, has exponent-one parabolic Holder control along a compactly carried
chart path.  The constants are produced from smoothness on the chart target;
they are not hypotheses. -/
theorem exists_metricChartCoefficient_parabolicHolderControl
    (g : RiemannianMetric I M) (alpha : M)
    {K : Set E} (hKtarget : K ⊆ (extChartAt I alpha).target)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (chi : X × T → E) (hchiK : ∀ z, chi z ∈ K)
    {LchiS LchiT : ℝ≥0}
    (hchiS : ∀ t ∈ J, LipschitzWith LchiS (fun x : X => chi (x, t)))
    (hchiT : ∀ x : X,
      LipschitzOnWith LchiT (fun t : T => chi (x, t)) J)
    (i k : Fin (Module.finrank ℝ E)) :
    ∃ (Cs Ct : ℝ≥0), ParabolicHolderControl
      (fun z => chartInvGramOnE (I := I) g alpha i k (chi z) •
        ContinuousLinearMap.id ℝ V) J Cs 1 Ct 1 := by
  have hsmooth : ContDiffOn ℝ 1
      (fun y : E => chartInvGramOnE (I := I) g alpha i k y •
        ContinuousLinearMap.id ℝ V) K := by
    have hscalar : ContDiffOn ℝ 1
        (chartInvGramOnE (I := I) g alpha i k)
        (extChartAt I alpha).target :=
      (chartInvGramOnE_contDiffOn (I := I) g alpha i k).of_le (by norm_num)
    exact (hscalar.smul contDiffOn_const).mono hKtarget
  obtain ⟨L, hL⟩ := exists_parabolicHolderControl_comp_of_contDiffOn
    (J := J) (f := fun y : E =>
      chartInvGramOnE (I := I) g alpha i k y •
        ContinuousLinearMap.id ℝ V)
    (chi := chi) hsmooth hKconv hKcompact hchiK hchiS hchiT
  exact ⟨L * LchiS, L * LchiT, by simpa using hL⟩

/-! ## The metric-chart evaluator -/

/-- **Math.** A metric chart operator applied to the basis two-jet of a `C^3`
vector map is parabolically Holder along a compactly carried chart-target
path.  This assembles the inverse-Gram coefficient controls with value, first,
and second sampled-jet controls through `SectionHolderJetData`.

This is a local analytic producer for a later chartwise Schauder argument.  It
does not construct a solution of a parabolic equation. -/
theorem exists_metricChartOperator_vectorBasisJet_parabolicHolderControl
    [CompactSpace X] [CompactSpace T]
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
    (u : E → V) (hu : ContDiff ℝ 3 u) :
    ∃ (Cs Ct : ℝ≥0), ParabolicHolderControl
      (fun z =>
        ((_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
          (I := I) g alpha V).toVectorSecondOrderCoefficients).applyJet
          (chi z) (vectorBasisJetAt u (chi z).1)) J Cs 1 Ct 1 := by
  classical
  let chiE : X × T → E := fun z => (chi z).1
  have hchiE : Continuous chiE := continuous_subtype_val.comp hchi
  have hu2 : ContDiff ℝ 2 u := hu.of_le (by norm_num)
  let C := metricChartCoefficientSections (V := V) g alpha chi hchi
  let A := variableCoefficientSectionsToCoefficients C
  let Z := vectorJetSectionsOf (T := X × T) u hu2 chiE hchiE

  obtain ⟨valueCs, valueCt, hvalue, hfirstExists, hsecondExists⟩ :=
    exists_vectorJet_parabolicHolderControl (J := J) u hu hKconv hKcompact
      chiE hchiK hchiS hchiT
  choose firstCs firstCt hfirst using hfirstExists
  choose secondCs secondCt hsecond using hsecondExists

  have haExists : ∀ i k, ∃ (aCs aCt : ℝ≥0),
      ParabolicHolderControl (fun z => C.1 i k z) J aCs 1 aCt 1 := by
    intro i k
    simpa only [C, metricChartCoefficientSections_apply] using
      exists_metricChartCoefficient_parabolicHolderControl
        (I := I) (V := V) (J := J) g alpha hKtarget hKconv hKcompact
          chiE hchiK hchiS hchiT i k
  choose aCs aCt ha using haExists

  have hzero : ParabolicHolderControl
      (fun _ : X × T => (0 : V →L[ℝ] V)) J 0 1 0 1 := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp [SpatialHolderWith]
    · intro x
      simp [TemporalHolderOnWith]

  let d : ParabolicPDE.VectorSecondOrderCoefficients.SectionHolderJetData
      A J 1 1 := {
    value := fun z => Z.1 z
    first := fun i z => Z.2.1 i z
    second := fun i k z => Z.2.2 i k z
    valueCs := valueCs
    valueCt := valueCt
    valueB := ‖Z.1‖₊
    firstCs := firstCs
    firstCt := firstCt
    firstB := fun i => ‖Z.2.1 i‖₊
    secondCs := secondCs
    secondCt := secondCt
    secondB := fun i k => ‖Z.2.2 i k‖₊
    aCs := aCs
    aCt := aCt
    aB := fun i k => ‖C.1 i k‖₊
    bCs := fun _ => 0
    bCt := fun _ => 0
    bB := fun i => ‖C.2.1 i‖₊
    cCs := 0
    cCt := 0
    cB := ‖C.2.2‖₊
    value_control := by
      simpa only [Z, vectorJetSectionsOf_value_apply] using hvalue
    first_control := by
      intro i
      simpa only [Z, vectorJetSectionsOf_first_apply] using hfirst i
    second_control := by
      intro i k
      simpa only [Z, vectorJetSectionsOf_second_apply] using hsecond i k
    a_control := by
      intro i k
      change ParabolicHolderControl (fun z => C.1 i k z) J
        (aCs i k) 1 (aCt i k) 1
      exact ha i k
    b_control := by
      intro i
      change ParabolicHolderControl
        (fun _ : X × T => (0 : V →L[ℝ] V)) J 0 1 0 1
      exact hzero
    c_control := by
      change ParabolicHolderControl
        (fun _ : X × T => (0 : V →L[ℝ] V)) J 0 1 0 1
      exact hzero
    a_bound := by
      intro i k z
      change ‖C.1 i k z‖ ≤ (‖C.1 i k‖₊ : ℝ)
      simpa using (C.1 i k).norm_coe_le_norm z
    b_bound := by
      intro i z
      change ‖C.2.1 i z‖ ≤ (‖C.2.1 i‖₊ : ℝ)
      simpa using (C.2.1 i).norm_coe_le_norm z
    c_bound := by
      intro z
      change ‖C.2.2 z‖ ≤ (‖C.2.2‖₊ : ℝ)
      simpa using C.2.2.norm_coe_le_norm z
    value_bound := by
      intro z
      simpa using Z.1.norm_coe_le_norm z
    first_bound := by
      intro i z
      simpa using (Z.2.1 i).norm_coe_le_norm z
    second_bound := by
      intro i k z
      simpa using (Z.2.2 i k).norm_coe_le_norm z
  }

  have hd := d.applyJetArgs_control
  have heval :
      (fun z => A.applyJetArgs z (d.value z)
        (fun i => d.first i z) (fun i k => d.second i k z)) =
      (fun z =>
        ((_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
          (I := I) g alpha V).toVectorSecondOrderCoefficients).applyJet
          (chi z) (vectorBasisJetAt u (chi z).1)) := by
    funext z
    change A.applyJetArgs z (Z.1 z) (fun i => Z.2.1 i z)
      (fun i k => Z.2.2 i k z) = _
    calc
      A.applyJetArgs z (Z.1 z) (fun i => Z.2.1 i z)
          (fun i k => Z.2.2 i k z) =
          variableCoefficientSectionsApplyJetArgs C Z z := by
            simp only [A, variableCoefficientSectionsToCoefficients,
              variableCoefficientSectionsApplyJetArgs_apply,
              VectorSecondOrderCoefficients.applyJetArgs]
      _ = _ := by
        simpa only [C, Z, chiE, hchiE] using
          metricChartCoefficientSections_apply_vectorJetSections
            (I := I) g alpha chi hchi u hu2 z
  rw [heval] at hd
  let Cs : ℝ≥0 :=
    ((∑ i, ∑ k, (d.aB i k * d.secondCs i k +
        d.aCs i k * d.secondB i k)) +
      (∑ i, (d.bB i * d.firstCs i + d.bCs i * d.firstB i)) +
        (d.cB * d.valueCs + d.cCs * d.valueB))
  let Ct : ℝ≥0 :=
    ((∑ i, ∑ k, (d.aB i k * d.secondCt i k +
        d.aCt i k * d.secondB i k)) +
      (∑ i, (d.bB i * d.firstCt i + d.bCt i * d.firstB i)) +
        (d.cB * d.valueCt + d.cCt * d.valueB))
  exact ⟨Cs, Ct, by simpa only [Cs, Ct] using hd⟩

end ChartCoefficientSections

end
end ParabolicPDE
end Topping

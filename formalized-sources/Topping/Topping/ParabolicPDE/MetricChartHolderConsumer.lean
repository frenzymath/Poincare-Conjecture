import Topping.ParabolicPDE.MetricChartVectorJetHolder
import Topping.ParabolicPDE.HolderSpace

/-!
# A universal local metric-chart Holder consumer

The sampled-vector-jet theorem controls one explicitly supplied coordinate
map.  A section-space Schauder argument instead needs a statement quantified
over arbitrary bounded value, first-jet, and second-jet fields.  This module
supplies that missing local interface: compact-carrier smoothness produces
Holder controls for the metric coefficients, and `SectionHolderJetData`
propagates those controls through the actual metric-chart evaluator.

The chart target and carrier remain explicit.  In particular, this is not an
atlas gluing theorem, a global bundle identification, or a parabolic solver.
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

/-! ## Restriction to the section-space time subtype -/

variable {S : Set X}

/-- **Math.** The canonical continuous map which replaces a time point in `T` by a
`J`-subtype point.  It is kept explicit because Holder-section spaces use
`S × J`, while the coefficient evaluator is defined on `S × T`. -/
def timeSubtypeMap : C(S × J, S × T) :=
  { toFun := fun z => (z.1, z.2.1)
    continuous_toFun := continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd) }

/-- **Math.** Restriction of a bounded continuous space-time field to `S × J`. -/
def restrictTimeSubtype (f : (S × T) →ᵇ V) : (S × J) →ᵇ V :=
  f.compContinuous (timeSubtypeMap (S := S) (J := J))

@[simp] theorem restrictTimeSubtype_apply
    (f : (S × T) →ᵇ V) (z : S × J) :
    restrictTimeSubtype (J := J) f z = f (z.1, z.2.1) := rfl

/-- **Math.** A parabolic Holder estimate on `S × T` restricts to a member of
the closed parabolic Holder section set on `S × J`.  This is the concrete
domain bridge needed by the section-space Picard consumers. -/
theorem mem_parabolicHolderSectionSet_of_parabolicHolderControl
    {S : Set X} {J : Set T} {Cs α Ct β : ℝ≥0}
    (f : (S × T) →ᵇ V)
    (hf : ParabolicHolderControl (fun z : S × T => f z) J Cs α Ct β) :
    restrictTimeSubtype (J := J) f ∈
      ParabolicHolderSectionSet (X := X) (T := T) (V := V)
        S J Cs α Ct β := by
  change ParabolicHolderControl
    (fun z : S × J => restrictTimeSubtype (J := J) f z)
    (Set.univ : Set J) Cs α Ct β
  refine ⟨?_, ?_⟩
  · intro t ht x y
    change edist (f (x, t.1)) (f (y, t.1)) ≤
      (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ)
    exact hf.spatial t.1 t.2 x y
  · intro x s hs t ht
    change edist (f (x, s.1)) (f (x, t.1)) ≤
      (Ct : ℝ≥0∞) * edist s t ^ (β : ℝ)
    simpa only [Subtype.edist_eq] using
      hf.temporal x s.1 s.2 t.1 t.2

/-- **Math.** The restriction bridge can be materialized as an element of the
complete parabolic Holder section subtype.  Thus a chartwise evaluator
control can be passed directly to the closed-ball/Picard interfaces. -/
theorem exists_parabolicHolderSection_of_parabolicHolderControl
    {S : Set X} {J : Set T} {Cs α Ct β : ℝ≥0}
    (f : (S × T) →ᵇ V)
    (hf : ParabolicHolderControl (fun z : S × T => f z) J Cs α Ct β) :
    ∃ u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs α Ct β,
      u.1 = restrictTimeSubtype (J := J) f := by
  refine ⟨⟨restrictTimeSubtype (J := J) f, ?_⟩, rfl⟩
  exact mem_parabolicHolderSectionSet_of_parabolicHolderControl f hf

/-! ## The universal jet-field estimate -/

/-- **Math.** On a compact chart carrier, the metric-chart evaluator sends
any Holder-controlled bounded value/first/second jet fields to a Holder field.
The coefficient constants are generated from the smooth inverse Gram entries;
the jet controls are uniform inputs, so this theorem is suitable for a later
section-space map rather than only for one fixed coordinate function. -/
theorem exists_metricChartOperator_parabolicHolderControl_of_jetSections
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
    (Z : VariableJetSections (T := X × T)
      (ι := Fin (Module.finrank ℝ E)) (V := V))
    (valueCs valueCt valueB : ℝ≥0)
    (hvalue : ParabolicHolderControl (fun z => Z.1 z) J
      valueCs 1 valueCt 1)
    (hvalue_bound : ∀ z, ‖Z.1 z‖ ≤ valueB)
    (firstCs firstCt : Fin (Module.finrank ℝ E) → ℝ≥0)
    (firstB : Fin (Module.finrank ℝ E) → ℝ≥0)
    (hfirst : ∀ i, ParabolicHolderControl (fun z => Z.2.1 i z) J
      (firstCs i) 1 (firstCt i) 1)
    (hfirst_bound : ∀ i z, ‖Z.2.1 i z‖ ≤ firstB i)
    (secondCs secondCt : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (secondB : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (hsecond : ∀ i k, ParabolicHolderControl
      (fun z => Z.2.2 i k z) J (secondCs i k) 1 (secondCt i k) 1)
    (hsecond_bound : ∀ i k z, ‖Z.2.2 i k z‖ ≤ secondB i k) :
    ∃ (Cs Ct : ℝ≥0), ParabolicHolderControl
      (fun z => variableCoefficientSectionsApplyJetArgs
        (metricChartCoefficientSections (V := V) g alpha chi hchi) Z z)
      J Cs 1 Ct 1 := by
  classical
  let chiE : X × T → E := fun z => (chi z).1
  have hchiE : Continuous chiE := continuous_subtype_val.comp hchi
  let C := metricChartCoefficientSections (V := V) g alpha chi hchi
  let A := variableCoefficientSectionsToCoefficients C
  have haExists : ∀ i k, ∃ (aCs aCt : ℝ≥0),
      ParabolicHolderControl (fun z : X × T => A.a z i k) J
        aCs 1 aCt 1 := by
    intro i k
    simpa only [A, C, variableCoefficientSectionsToCoefficients,
      metricChartCoefficientSections_apply] using
      exists_metricChartCoefficient_parabolicHolderControl
        (I := I) (V := V) (J := J) g alpha hKtarget hKconv hKcompact
          chiE (fun z => hchiK z) hchiS hchiT i k
  choose aCs aCt ha using haExists
  have hzero : ParabolicHolderControl
      (fun _ : X × T => (0 : V →L[ℝ] V)) J 0 1 0 1 := by
    refine ⟨?_, ?_⟩
    · intro t ht
      simp [SpatialHolderWith]
    · intro x s hs t ht
      simp
  let d : VectorSecondOrderCoefficients.SectionHolderJetData A J 1 1 := {
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
    aCs := aCs
    aCt := aCt
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
    a_control := ha
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

/-! ## Operator-facing form -/

/-- **Math.** The preceding estimate is an estimate for the actual chart operator, not
just for an opaque coefficient package. -/
theorem exists_metricChartOperator_applyJetArgs_parabolicHolderControl
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
    (Z : VariableJetSections (T := X × T)
      (ι := Fin (Module.finrank ℝ E)) (V := V))
    (valueCs valueCt valueB : ℝ≥0)
    (hvalue : ParabolicHolderControl (fun z => Z.1 z) J
      valueCs 1 valueCt 1)
    (hvalue_bound : ∀ z, ‖Z.1 z‖ ≤ valueB)
    (firstCs firstCt : Fin (Module.finrank ℝ E) → ℝ≥0)
    (firstB : Fin (Module.finrank ℝ E) → ℝ≥0)
    (hfirst : ∀ i, ParabolicHolderControl (fun z => Z.2.1 i z) J
      (firstCs i) 1 (firstCt i) 1)
    (hfirst_bound : ∀ i z, ‖Z.2.1 i z‖ ≤ firstB i)
    (secondCs secondCt : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (secondB : Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ≥0)
    (hsecond : ∀ i k, ParabolicHolderControl
      (fun z => Z.2.2 i k z) J (secondCs i k) 1 (secondCt i k) 1)
    (hsecond_bound : ∀ i k z, ‖Z.2.2 i k z‖ ≤ secondB i k) :
    ∃ (Cs Ct : ℝ≥0), ParabolicHolderControl
      (fun z =>
        ((_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
          (I := I) g alpha V).toVectorSecondOrderCoefficients).applyJetArgs
          (chi z) (Z.1 z) (fun i => Z.2.1 i z)
            (fun i k => Z.2.2 i k z)) J Cs 1 Ct 1 := by
  obtain ⟨Cs, Ct, hC⟩ :=
    exists_metricChartOperator_parabolicHolderControl_of_jetSections
      (I := I) (J := J) g alpha hKtarget hKconv hKcompact chi hchi hchiK
      hchiS hchiT Z valueCs valueCt valueB hvalue hvalue_bound
      firstCs firstCt firstB hfirst hfirst_bound secondCs secondCt secondB
      hsecond hsecond_bound
  refine ⟨Cs, Ct, ?_⟩
  have heq :
      (fun z : X × T =>
        variableCoefficientSectionsApplyJetArgs
          (metricChartCoefficientSections (V := V) g alpha chi hchi) Z z) =
      (fun z : X × T =>
        ((_root_.Topping.IntrinsicSymbolBridge.metricChartOperator
          (I := I) g alpha V).toVectorSecondOrderCoefficients).applyJetArgs
          (chi z) (Z.1 z) (fun i => Z.2.1 i z)
            (fun i k => Z.2.2 i k z)) := by
    funext z
    exact metricChartCoefficientSections_applyJetArgs_eq_metricChartOperator
      (I := I) (V := V) g alpha chi hchi Z z
  rw [← heq]
  exact hC

end ChartCoefficientSections

end
end ParabolicPDE
end Topping

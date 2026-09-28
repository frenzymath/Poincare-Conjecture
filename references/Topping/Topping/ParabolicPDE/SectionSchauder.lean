import Topping.ParabolicPDE.VariableParabolicHolder

/-!
# Section-space Holder/Schauder producers

This file packages the variable-coefficient parabolic Holder estimate into a
single section-data structure.  The resulting API is deliberately local and
unconditional: it does not assert existence of solutions to a manifold PDE.
The `SchauderEstimateContract` records the additional estimate supplied by a
future chartwise solver, while `SectionHolderJetData` produces the Holder
control that such a solver consumes.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BigOperators NNReal ENNReal Topology

noncomputable section

namespace VectorSecondOrderCoefficients

variable {X T V : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {ι : Type*} [Fintype ι]

/-! ## Bundled Holder data -/

/-- Holder and uniform bounds for a variable second-order evaluator and its
value/first/second jet sections.  All fields are explicit so this structure
can be instantiated by a chartwise argument without hiding hypotheses. -/
structure SectionHolderJetData
    (A : VectorSecondOrderCoefficients (X × T) ι V)
    (J : Set T) (α β : ℝ≥0) where
  value : X × T → V
  first : ι → X × T → V
  second : ι → ι → X × T → V
  valueCs : ℝ≥0
  valueCt : ℝ≥0
  valueB : ℝ≥0
  firstCs : ι → ℝ≥0
  firstCt : ι → ℝ≥0
  firstB : ι → ℝ≥0
  secondCs : ι → ι → ℝ≥0
  secondCt : ι → ι → ℝ≥0
  secondB : ι → ι → ℝ≥0
  aCs : ι → ι → ℝ≥0
  aCt : ι → ι → ℝ≥0
  aB : ι → ι → ℝ≥0
  bCs : ι → ℝ≥0
  bCt : ι → ℝ≥0
  bB : ι → ℝ≥0
  cCs : ℝ≥0
  cCt : ℝ≥0
  cB : ℝ≥0
  value_control : ParabolicHolderControl value J valueCs α valueCt β
  first_control : ∀ i, ParabolicHolderControl (first i) J
    (firstCs i) α (firstCt i) β
  second_control : ∀ i k, ParabolicHolderControl (second i k) J
    (secondCs i k) α (secondCt i k) β
  a_control : ∀ i k, ParabolicHolderControl (fun z => A.a z i k) J
    (aCs i k) α (aCt i k) β
  b_control : ∀ i, ParabolicHolderControl (fun z => A.b z i) J
    (bCs i) α (bCt i) β
  c_control : ParabolicHolderControl (fun z => A.c z) J cCs α cCt β
  a_bound : ∀ i k z, ‖A.a z i k‖ ≤ aB i k
  b_bound : ∀ i z, ‖A.b z i‖ ≤ bB i
  c_bound : ∀ z, ‖A.c z‖ ≤ cB
  value_bound : ∀ z, ‖value z‖ ≤ valueB
  first_bound : ∀ i z, ‖first i z‖ ≤ firstB i
  second_bound : ∀ i k z, ‖second i k z‖ ≤ secondB i k

/-! ## Holder and two-point producers -/

/-- Applying the variable evaluator to bundled Holder jet data produces a
parabolic Holder section with the explicit finite-sum product constants. -/
theorem SectionHolderJetData.applyJetArgs_control
    {J : Set T} {α β : ℝ≥0}
    {A : VectorSecondOrderCoefficients (X × T) ι V}
    (d : SectionHolderJetData A J α β) :
    ParabolicHolderControl
      (fun z => A.applyJetArgs z (d.value z)
        (fun i => d.first i z) (fun i k => d.second i k z)) J
      ((∑ i, ∑ k, (d.aB i k * d.secondCs i k +
          d.aCs i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCs i + d.bCs i * d.firstB i)) +
          (d.cB * d.valueCs + d.cCs * d.valueB)) α
      ((∑ i, ∑ k, (d.aB i k * d.secondCt i k +
          d.aCt i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCt i + d.bCt i * d.firstB i)) +
          (d.cB * d.valueCt + d.cCt * d.valueB)) β := by
  exact parabolicHolderControl_applyJetArgs A d.value d.first d.second
    d.valueCs d.valueCt d.valueB d.firstCs d.firstCt d.firstB
    d.secondCs d.secondCt d.secondB d.aCs d.aCt d.aB d.bCs d.bCt d.bB
    d.cCs d.cCt d.cB d.value_control d.first_control d.second_control
    d.a_control d.b_control d.c_control d.a_bound d.b_bound d.c_bound
    d.value_bound d.first_bound d.second_bound

/-- Adding an independently controlled forcing field to the variable
second-order jet evaluation preserves parabolic Holder control.  This is the
section-space source assembly used before applying a Schauder solver. -/
theorem SectionHolderJetData.applyJetArgs_add_control
    {J : Set T} {α β : ℝ≥0}
    {A : VectorSecondOrderCoefficients (X × T) ι V}
    (d : SectionHolderJetData A J α β)
    {f : X × T → V} {fCs fCt : ℝ≥0}
    (hf : ParabolicHolderControl f J fCs α fCt β) :
    ParabolicHolderControl
      (fun z => A.applyJetArgs z (d.value z)
        (fun i => d.first i z) (fun i k => d.second i k z) + f z) J
      (((∑ i, ∑ k, (d.aB i k * d.secondCs i k +
          d.aCs i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCs i + d.bCs i * d.firstB i)) +
          (d.cB * d.valueCs + d.cCs * d.valueB)) + fCs) α
      (((∑ i, ∑ k, (d.aB i k * d.secondCt i k +
          d.aCt i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCt i + d.bCt i * d.firstB i)) +
          (d.cB * d.valueCt + d.cCt * d.valueB)) + fCt) β := by
  exact (d.applyJetArgs_control).add hf

/-- The produced section satisfies the explicit split spatial/temporal
two-point estimate on the prescribed time set. -/
theorem SectionHolderJetData.applyJetArgs_edist_le_split
    {J : Set T} {α β : ℝ≥0}
    {A : VectorSecondOrderCoefficients (X × T) ι V}
    (d : SectionHolderJetData A J α β)
    {x y : X} {s t : T} (hs : s ∈ J) (ht : t ∈ J) :
    edist (A.applyJetArgs (x, s) (d.value (x, s))
        (fun i => d.first i (x, s)) (fun i k => d.second i k (x, s)))
      (A.applyJetArgs (y, t) (d.value (y, t))
        (fun i => d.first i (y, t)) (fun i k => d.second i k (y, t))) ≤
      (↑((∑ i, ∑ k, (d.aB i k * d.secondCs i k +
          d.aCs i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCs i + d.bCs i * d.firstB i)) +
          (d.cB * d.valueCs + d.cCs * d.valueB)) : ℝ≥0∞) *
          edist x y ^ (α : ℝ) +
        (↑((∑ i, ∑ k, (d.aB i k * d.secondCt i k +
          d.aCt i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCt i + d.bCt i * d.firstB i)) +
          (d.cB * d.valueCt + d.cCt * d.valueB)) : ℝ≥0∞) *
          edist s t ^ (β : ℝ) := by
  exact (d.applyJetArgs_control).edist_le_split hs ht

/-! The same two-point estimate is exposed for the source assembly with an
independently controlled forcing term. -/

/-- **Math.** Adding a Holder-controlled forcing field to the section evaluator
preserves the explicit split spatial/temporal estimate. -/
theorem SectionHolderJetData.applyJetArgs_add_control_edist_le_split
    {J : Set T} {α β : ℝ≥0}
    {A : VectorSecondOrderCoefficients (X × T) ι V}
    (d : SectionHolderJetData A J α β)
    {f : X × T → V} {fCs fCt : ℝ≥0}
    (hf : ParabolicHolderControl f J fCs α fCt β)
    {x y : X} {s t : T} (hs : s ∈ J) (ht : t ∈ J) :
    edist (A.applyJetArgs (x, s) (d.value (x, s))
        (fun i => d.first i (x, s)) (fun i k => d.second i k (x, s)) + f (x, s))
      (A.applyJetArgs (y, t) (d.value (y, t))
        (fun i => d.first i (y, t)) (fun i k => d.second i k (y, t)) + f (y, t)) ≤
      (↑(((∑ i, ∑ k, (d.aB i k * d.secondCs i k +
          d.aCs i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCs i + d.bCs i * d.firstB i)) +
          (d.cB * d.valueCs + d.cCs * d.valueB)) + fCs) : ℝ≥0∞) *
          edist x y ^ (α : ℝ) +
        (↑(((∑ i, ∑ k, (d.aB i k * d.secondCt i k +
          d.aCt i k * d.secondB i k)) +
        (∑ i, (d.bB i * d.firstCt i + d.bCt i * d.firstB i)) +
          (d.cB * d.valueCt + d.cCt * d.valueB)) + fCt) : ℝ≥0∞) *
          edist s t ^ (β : ℝ) := by
  exact (d.applyJetArgs_add_control hf).edist_le_split hs ht

end VectorSecondOrderCoefficients

/-! ## Explicit Schauder contracts -/

/-- A chart-free contract for a future section-space Schauder solver.  The
Holder control and the estimate are inputs; this structure makes clear exactly
which analytic statement a solver must provide, without asserting existence
or regularity on its own. -/
structure SchauderEstimateContract
    {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
    [NormedAddCommGroup V]
    (J : Set T) (α β : ℝ≥0) where
  solution : X × T → V
  source : X × T → V
  solutionCs : ℝ≥0
  solutionCt : ℝ≥0
  sourceCs : ℝ≥0
  sourceCt : ℝ≥0
  solution_control : ParabolicHolderControl solution J solutionCs α solutionCt β
  source_control : ParabolicHolderControl source J sourceCs α sourceCt β
  spatial_estimate : solutionCs ≤ sourceCs
  temporal_estimate : solutionCt ≤ sourceCt

namespace SchauderEstimateContract

variable {X T V : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup V] {J : Set T} {α β : ℝ≥0}

/-- A contract immediately yields a Holder control with any enlarged constants.
This is the monotonicity interface used when local estimates are assembled. -/
theorem control_mono
    (C : SchauderEstimateContract (X := X) (T := T) (V := V) J α β)
    {Ds Dt : ℝ≥0} (hCs : C.solutionCs ≤ Ds) (hCt : C.solutionCt ≤ Dt) :
    ParabolicHolderControl C.solution J Ds α Dt β := by
  exact C.solution_control.mono hCs hCt

/-- The contract's solution obeys the canonical split two-point estimate. -/
theorem edist_le_split
    (C : SchauderEstimateContract (X := X) (T := T) (V := V) J α β)
    {x y : X} {s t : T} (hs : s ∈ J) (ht : t ∈ J) :
    edist (C.solution (x, s)) (C.solution (y, t)) ≤
      (C.solutionCs : ℝ≥0∞) * edist x y ^ (α : ℝ) +
        (C.solutionCt : ℝ≥0∞) * edist s t ^ (β : ℝ) := by
  exact C.solution_control.edist_le_split hs ht

end SchauderEstimateContract

end
end ParabolicPDE
end Topping

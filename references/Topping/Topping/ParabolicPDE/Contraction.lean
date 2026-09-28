import Mathlib.Topology.MetricSpace.Contracting

/-!
# Contraction producers for nonlinear parabolic equations

This module isolates the Banach--Picard part of a quasilinear existence
argument.  A section space (or a closed subspace of one) is supplied as a
complete metric space, together with a forward-invariant complete set on which
the iteration map contracts.  The resulting fixed point, convergence, error
bound, and uniqueness are genuine consequences of the contraction hypotheses;
no equation-shaped existence predicate is introduced.

The second half packages a uniform family of contractions.  A common
contraction factor and a uniform parameter Lipschitz estimate give an explicit
stability bound for the fixed points.  This is the estimate used when a
Picard solution is compared as the initial metric or lower-order data vary.
-/

namespace Topping
namespace ParabolicPDE

open Filter Function Set
open scoped Topology NNReal ENNReal

noncomputable section

/-! ## A contraction on a complete invariant subset -/

/-- A self-map that contracts on a complete forward-invariant subset.

The ambient type is allowed to be larger than the subset: this is useful for
section spaces where a closed ball carries the a priori norm bound. -/
structure CompleteInvariantContraction (X : Type*) [MetricSpace X] where
  carrier : Set X
  complete : IsComplete carrier
  map : X → X
  invariant : MapsTo map carrier carrier
  K : ℝ≥0
  contract : ContractingWith K (invariant.restrict map carrier carrier)

namespace CompleteInvariantContraction

variable {X : Type*} [MetricSpace X]
  (C : CompleteInvariantContraction X)

/-- The Picard fixed point obtained from an initial point in the invariant set. -/
noncomputable def fixedPoint (x : X) (hx : x ∈ C.carrier) : X :=
  ContractingWith.efixedPoint' C.map C.complete C.invariant C.contract x hx
    (edist_ne_top x (C.map x))

theorem fixedPoint_mem (x : X) (hx : x ∈ C.carrier) :
    C.fixedPoint x hx ∈ C.carrier := by
  exact ContractingWith.efixedPoint_mem' C.complete C.invariant C.contract hx
    (edist_ne_top x (C.map x))

theorem fixedPoint_isFixedPt (x : X) (hx : x ∈ C.carrier) :
    IsFixedPt C.map (C.fixedPoint x hx) := by
  exact ContractingWith.efixedPoint_isFixedPt' C.complete C.invariant C.contract hx
    (edist_ne_top x (C.map x))

theorem fixedPoint_tendsto_iterate (x : X) (hx : x ∈ C.carrier) :
    Tendsto (fun n : ℕ => C.map^[n] x) atTop
      (𝓝 (C.fixedPoint x hx)) := by
  exact ContractingWith.tendsto_iterate_efixedPoint' C.complete C.invariant C.contract hx
    (edist_ne_top x (C.map x))

theorem fixedPoint_apriori_edist (x : X) (hx : x ∈ C.carrier) (n : ℕ) :
    edist (C.map^[n] x) (C.fixedPoint x hx) ≤
      edist x (C.map x) * (C.K : ℝ≥0∞) ^ n / (1 - C.K) := by
  exact ContractingWith.apriori_edist_iterate_efixedPoint_le' C.complete C.invariant C.contract hx
    (edist_ne_top x (C.map x)) n

/-- Existence, membership, convergence, and the geometric Picard error bound in
one theorem.  This is the direct producer consumed by a nonlinear solver. -/
theorem exists_fixedPoint (x : X) (hx : x ∈ C.carrier) :
    ∃ y ∈ C.carrier, IsFixedPt C.map y ∧
      Tendsto (fun n : ℕ => C.map^[n] x) atTop (𝓝 y) ∧
      ∀ n : ℕ,
        edist (C.map^[n] x) y ≤
          edist x (C.map x) * (C.K : ℝ≥0∞) ^ n / (1 - C.K) := by
  exact ContractingWith.exists_fixedPoint' C.complete C.invariant C.contract hx
    (edist_ne_top x (C.map x))

/-- Any two fixed points lying in the invariant set agree. -/
theorem fixedPoint_unique {y z : X}
    (hy : y ∈ C.carrier) (hz : z ∈ C.carrier)
    (hyfix : IsFixedPt C.map y) (hzfix : IsFixedPt C.map z) :
    y = z := by
  have hy' : IsFixedPt
      (C.invariant.restrict C.map C.carrier C.carrier) ⟨y, hy⟩ := by
    apply Subtype.ext
    exact hyfix
  have hz' : IsFixedPt
      (C.invariant.restrict C.map C.carrier C.carrier) ⟨z, hz⟩ := by
    apply Subtype.ext
    exact hzfix
  have hsub : (⟨y, hy⟩ : C.carrier) = ⟨z, hz⟩ :=
    C.contract.fixedPoint_unique' hy' hz'
  exact congrArg Subtype.val hsub

end CompleteInvariantContraction

/-! ## Uniformly contracting parameter families -/

/-- A family of self-maps with one contraction factor on a complete metric
space.  The parameter type can encode initial metrics, coefficients, or other
lower-order data. -/
structure UniformContractionFamily
    (P X : Type*) [MetricSpace P] [MetricSpace X]
    [Nonempty X] [CompleteSpace X] where
  K : ℝ≥0
  map : P → X → X
  contract : ∀ p, ContractingWith K (map p)

namespace UniformContractionFamily

variable {P X : Type*} [MetricSpace P] [MetricSpace X]
  [Nonempty X] [CompleteSpace X]
  (F : UniformContractionFamily P X)

noncomputable def contractionDenominator [Nonempty P] : ℝ≥0 :=
  1 - F.K

theorem contractionDenominator_pos [Nonempty P] :
    0 < F.contractionDenominator := by
  obtain ⟨p⟩ := ‹Nonempty P›
  exact tsub_pos_iff_lt.mpr (F.contract p).1

theorem contractionDenominator_coe [Nonempty P] :
    (F.contractionDenominator : ℝ) = 1 - (F.K : ℝ) := by
  apply NNReal.coe_sub
  obtain ⟨p⟩ := ‹Nonempty P›
  exact (F.contract p).1.le

/-- The unique fixed point selected by the Banach theorem for each parameter. -/
noncomputable def fixedPointAt (p : P) : X :=
  ContractingWith.fixedPoint (F.map p) (F.contract p)

theorem fixedPointAt_isFixedPt (p : P) :
    IsFixedPt (F.map p) (F.fixedPointAt p) := by
  exact (F.contract p).fixedPoint_isFixedPt

theorem fixedPointAt_unique (p : P) {x : X}
    (hx : IsFixedPt (F.map p) x) : x = F.fixedPointAt p := by
  exact (F.contract p).fixedPoint_unique hx

theorem fixedPointAt_tendsto_iterate (p : P) (x : X) :
    Tendsto (fun n : ℕ => (F.map p)^[n] x) atTop
      (𝓝 (F.fixedPointAt p)) := by
  exact (F.contract p).tendsto_iterate_fixedPoint x

/-- Uniform parameter control of the map yields an explicit stability estimate
for the selected fixed points. -/
theorem dist_fixedPointAt_le
    {L : ℝ≥0}
    (hmap : ∀ (p q : P) (z : X),
      dist (F.map p z) (F.map q z) ≤ (L : ℝ) * dist p q)
    (p q : P) :
    dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
      (L : ℝ) * dist p q / (1 - (F.K : ℝ)) := by
  exact (F.contract p).fixedPoint_lipschitz_in_map (F.contract q)
    (C := (L : ℝ) * dist p q) (fun z => hmap p q z)

/-- Convenient form of parameter control when each map is Lipschitz in the
parameter with the same `NNReal` constant. -/
theorem dist_fixedPointAt_le_of_lipschitz
    {L : ℝ≥0}
    (hmap : ∀ (z : X), LipschitzWith L (fun p : P => F.map p z))
    (p q : P) :
    dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
      (L : ℝ) * dist p q / (1 - (F.K : ℝ)) := by
  apply F.dist_fixedPointAt_le (L := L) ?_ p q
  intro p' q' z
  exact (hmap z).dist_le_mul p' q'

theorem lipschitz_fixedPointAt_of_lipschitz
    [Nonempty P] {L : ℝ≥0}
    (hmap : ∀ (z : X), LipschitzWith L (fun p : P => F.map p z)) :
    LipschitzWith
      ⟨(L : ℝ) / (1 - (F.K : ℝ)), by
        have hK : (F.K : ℝ) < 1 := by
          obtain ⟨p⟩ := ‹Nonempty P›
          exact (NNReal.coe_lt_one).2 (F.contract p).1
        exact div_nonneg (NNReal.coe_nonneg L)
          (le_of_lt (sub_pos.mpr hK))⟩
      F.fixedPointAt := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := F.dist_fixedPointAt_le_of_lipschitz hmap p q
  change dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
    ((L : ℝ) / (1 - (F.K : ℝ))) * dist p q
  calc
    dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
        (L : ℝ) * dist p q / (1 - (F.K : ℝ)) := h
    _ = ((L : ℝ) / (1 - (F.K : ℝ))) * dist p q := by ring

theorem continuous_fixedPointAt_of_lipschitz
    [Nonempty P] {L : ℝ≥0}
    (hmap : ∀ (z : X), LipschitzWith L (fun p : P => F.map p z)) :
    Continuous F.fixedPointAt := by
  exact (F.lipschitz_fixedPointAt_of_lipschitz hmap).continuous

theorem lipschitz_fixedPointAt_of_lipschitz'
    [Nonempty P] {L : ℝ≥0}
    (hmap : ∀ (z : X), LipschitzWith L (fun p : P => F.map p z)) :
    LipschitzWith (L / F.contractionDenominator) F.fixedPointAt := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := F.dist_fixedPointAt_le_of_lipschitz hmap p q
  change dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
    ((L / F.contractionDenominator : ℝ≥0) : ℝ) * dist p q
  rw [NNReal.coe_div, F.contractionDenominator_coe]
  calc
    dist (F.fixedPointAt p) (F.fixedPointAt q) ≤
        (L : ℝ) * dist p q / (1 - (F.K : ℝ)) := h
    _ = ((L : ℝ) / (1 - (F.K : ℝ))) * dist p q := by ring

theorem continuous_fixedPointAt_of_lipschitz'
    [Nonempty P] {L : ℝ≥0}
    (hmap : ∀ (z : X), LipschitzWith L (fun p : P => F.map p z)) :
    Continuous F.fixedPointAt := by
  exact (F.lipschitz_fixedPointAt_of_lipschitz' hmap).continuous

/-- The fixed points of two members of a uniformly contracting family are
controlled by the parameter-map discrepancy evaluated at the first fixed
point.  This estimate needs no regularity hypothesis on the parameter map. -/
theorem dist_fixedPointAt_le_of_map_dist (p q : P) :
    dist (F.fixedPointAt q) (F.fixedPointAt p) ≤
      dist (F.map p (F.fixedPointAt p)) (F.map q (F.fixedPointAt p)) /
        (1 - (F.K : ℝ)) := by
  have h := (F.contract q).dist_inequality
    (F.fixedPointAt q) (F.fixedPointAt p)
  rw [F.fixedPointAt_isFixedPt q, dist_self, zero_add] at h
  calc
    dist (F.fixedPointAt q) (F.fixedPointAt p) ≤
        dist (F.fixedPointAt p) (F.map q (F.fixedPointAt p)) /
          (1 - (F.K : ℝ)) := h
    _ = dist (F.map p (F.fixedPointAt p)) (F.map q (F.fixedPointAt p)) /
          (1 - (F.K : ℝ)) := by
      rw [F.fixedPointAt_isFixedPt p]

/-- Pointwise parameter continuity of a uniformly contracting family is enough
to make its selected fixed point continuous.  The contraction estimate is
used to transfer continuity of the map at the fixed point back to the fixed
point itself; no uniform parameter Lipschitz constant is required. -/
theorem continuous_fixedPointAt_of_continuous
    (hmap : ∀ (z : X), Continuous (fun p : P => F.map p z)) :
    Continuous F.fixedPointAt := by
  rw [Metric.continuous_iff]
  intro p ε hε
  have hden : 0 < 1 - (F.K : ℝ) := by
    exact sub_pos.mpr ((NNReal.coe_lt_one).2 (F.contract p).1)
  obtain ⟨δ, hδ, hnear⟩ :=
    (Metric.continuousAt_iff.mp (hmap (F.fixedPointAt p)).continuousAt)
      (ε * (1 - (F.K : ℝ))) (mul_pos hε hden)
  refine ⟨δ, hδ, ?_⟩
  intro q hq
  have hvar :
      dist (F.map q (F.fixedPointAt p)) (F.map p (F.fixedPointAt p)) <
        ε * (1 - (F.K : ℝ)) := hnear hq
  have hbound := F.dist_fixedPointAt_le_of_map_dist p q
  have hvar' :
      dist (F.map p (F.fixedPointAt p)) (F.map q (F.fixedPointAt p)) <
        ε * (1 - (F.K : ℝ)) := by
    simpa only [dist_comm] using hvar
  have hdiv :
      dist (F.map p (F.fixedPointAt p)) (F.map q (F.fixedPointAt p)) /
          (1 - (F.K : ℝ)) < ε :=
    (div_lt_iff₀ hden).2 hvar'
  exact hbound.trans_lt hdiv

end UniformContractionFamily

/-! ## Decoding a fixed point into geometric data -/

/-- A contraction family together with an explicit decoding map into a second
metric space.  The two decode bounds separate dependence on the Picard state
from dependence on the parameter; this is the form needed when a fixed point
is converted into a metric, tensor, or section. -/
structure DecodedUniformContractionFamily
    (P X Y : Type*) [MetricSpace P] [MetricSpace X] [MetricSpace Y]
    [Nonempty X] [CompleteSpace X] where
  family : UniformContractionFamily P X
  mapLipschitz : ℝ≥0
  map_parameter_lipschitz :
    ∀ (z : X), LipschitzWith mapLipschitz
      (fun p : P => family.map p z)
  decode : P → X → Y
  stateLipschitz : ℝ≥0
  parameterLipschitz : ℝ≥0
  decode_state_lipschitz :
    ∀ (p : P), LipschitzWith stateLipschitz (decode p)
  decode_parameter_lipschitz :
    ∀ (x : X), LipschitzWith parameterLipschitz
      (fun p : P => decode p x)

namespace DecodedUniformContractionFamily

variable {P X Y : Type*} [MetricSpace P] [MetricSpace X] [MetricSpace Y]
  [Nonempty X] [CompleteSpace X]
  (D : DecodedUniformContractionFamily P X Y)

noncomputable def lipschitzConstant [Nonempty P] : ℝ≥0 :=
  D.stateLipschitz * (D.mapLipschitz / D.family.contractionDenominator) +
    D.parameterLipschitz

noncomputable def fixedPointAt (p : P) : X :=
  D.family.fixedPointAt p

noncomputable def decodedFixedPoint (p : P) : Y :=
  D.decode p (D.fixedPointAt p)

theorem fixedPointAt_isFixedPt (p : P) :
    IsFixedPt (D.family.map p) (D.fixedPointAt p) := by
  exact D.family.fixedPointAt_isFixedPt p

theorem dist_fixedPointAt_le (p q : P) :
    dist (D.fixedPointAt p) (D.fixedPointAt q) ≤
      (D.mapLipschitz : ℝ) * dist p q /
        (1 - (D.family.K : ℝ)) := by
  exact D.family.dist_fixedPointAt_le_of_lipschitz
    D.map_parameter_lipschitz p q

theorem dist_decodedFixedPoint_le (p q : P) :
    dist (D.decodedFixedPoint p) (D.decodedFixedPoint q) ≤
      ((D.stateLipschitz : ℝ) *
          ((D.mapLipschitz : ℝ) * dist p q /
            (1 - (D.family.K : ℝ))) +
        (D.parameterLipschitz : ℝ) * dist p q) := by
  calc
    dist (D.decode p (D.fixedPointAt p))
        (D.decode q (D.fixedPointAt q)) ≤
        dist (D.decode p (D.fixedPointAt p))
            (D.decode p (D.fixedPointAt q)) +
          dist (D.decode p (D.fixedPointAt q))
            (D.decode q (D.fixedPointAt q)) := dist_triangle _ _ _
    _ ≤ (D.stateLipschitz : ℝ) *
          dist (D.fixedPointAt p) (D.fixedPointAt q) +
        (D.parameterLipschitz : ℝ) * dist p q := by
      exact add_le_add
        ((D.decode_state_lipschitz p).dist_le_mul _ _)
        ((D.decode_parameter_lipschitz (D.fixedPointAt q)).dist_le_mul _ _)
    _ ≤ (D.stateLipschitz : ℝ) *
          ((D.mapLipschitz : ℝ) * dist p q /
            (1 - (D.family.K : ℝ))) +
        (D.parameterLipschitz : ℝ) * dist p q := by
      gcongr
      exact D.dist_fixedPointAt_le p q

theorem lipschitz_decodedFixedPoint [Nonempty P] :
    LipschitzWith D.lipschitzConstant D.decodedFixedPoint := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  have h := D.dist_decodedFixedPoint_le p q
  change dist (D.decodedFixedPoint p) (D.decodedFixedPoint q) ≤
    (D.lipschitzConstant : ℝ) * dist p q
  rw [lipschitzConstant, NNReal.coe_add, NNReal.coe_mul,
    NNReal.coe_div, D.family.contractionDenominator_coe]
  calc
    dist (D.decodedFixedPoint p) (D.decodedFixedPoint q) ≤
        (D.stateLipschitz : ℝ) *
            ((D.mapLipschitz : ℝ) * dist p q /
              (1 - (D.family.K : ℝ))) +
          (D.parameterLipschitz : ℝ) * dist p q := h
    _ = ((D.stateLipschitz : ℝ) *
          ((D.mapLipschitz : ℝ) /
            (1 - (D.family.K : ℝ))) +
        (D.parameterLipschitz : ℝ)) * dist p q := by ring

theorem continuous_decodedFixedPoint [Nonempty P] :
    Continuous D.decodedFixedPoint := by
  exact D.lipschitz_decodedFixedPoint.continuous

end DecodedUniformContractionFamily

end
end ParabolicPDE
end Topping

import Topping.ParabolicPDE.SectionSpacePicard

/-!
# Parameter dependence for invariant bounded-section Picard maps

This module fills the parameter-dependence boundary for Picard maps whose
contraction is available only on one complete invariant carrier.  The core
comparison is a direct Banach estimate for two maps on a common carrier.  It
is then specialized to bounded continuous section balls and to a parameter
family with a common centre, radius, and contraction factor.

No PDE solver or geometric identification is built into these structures:
the map, invariance, and contraction estimates remain explicit hypotheses.
-/

namespace Topping
namespace ParabolicPDE

open Filter Function Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction

noncomputable section

/-! ## Two maps on one complete carrier -/

/-- Two self-maps which contract with the same factor on one complete carrier.

The common carrier is useful when comparing Picard maps at two parameters: the
maps need not be contractions on the whole ambient space. -/
structure CommonCarrierContractionPair (X : Type*) [MetricSpace X] where
  carrier : Set X
  complete : IsComplete carrier
  map1 : X → X
  map2 : X → X
  invariant1 : MapsTo map1 carrier carrier
  invariant2 : MapsTo map2 carrier carrier
  K : ℝ≥0
  contract1 : ContractingWith K
    (invariant1.restrict map1 carrier carrier)
  contract2 : ContractingWith K
    (invariant2.restrict map2 carrier carrier)

namespace CommonCarrierContractionPair

variable {X : Type*} [MetricSpace X]
  (C : CommonCarrierContractionPair X)

/-- Uniform map perturbations give the geometric fixed-point stability bound. -/
theorem dist_fixedPoints_le
    {u v : X}
    (hu : u ∈ C.carrier) (hv : v ∈ C.carrier)
    (hufix : IsFixedPt C.map1 u)
    (hvfix : IsFixedPt C.map2 v)
    {ε : ℝ}
    (hmap : ∀ z ∈ C.carrier,
      dist (C.map1 z) (C.map2 z) ≤ ε) :
    dist u v ≤ ε / (1 - (C.K : ℝ)) := by
  let f : C.carrier → C.carrier :=
    C.invariant1.restrict C.map1 C.carrier C.carrier
  let g : C.carrier → C.carrier :=
    C.invariant2.restrict C.map2 C.carrier C.carrier
  have hf : ContractingWith C.K f := by
    simpa [f] using C.contract1
  have hg : ContractingWith C.K g := by
    simpa [g] using C.contract2
  have hu' : IsFixedPt f ⟨u, hu⟩ := by
    apply Subtype.ext
    exact hufix
  have hv' : IsFixedPt g ⟨v, hv⟩ := by
    apply Subtype.ext
    exact hvfix
  have hmap' : ∀ z : C.carrier, dist (f z) (g z) ≤ ε := by
    intro z
    change dist (C.map1 z) (C.map2 z) ≤ ε
    exact hmap z z.property
  have hsub := hf.dist_fixedPoint_fixedPoint_of_dist_le' g hu' hv' hmap'
  simpa only [Subtype.dist_eq] using hsub

/-- The discrepancy at the first fixed point already controls the second one.

This is the local form used to prove continuity from pointwise continuity of a
parameterized map; no uniform perturbation bound over the whole carrier is
needed. -/
theorem dist_fixedPoints_le_of_map_at
    {u v : X}
    (hu : u ∈ C.carrier) (hv : v ∈ C.carrier)
    (hufix : IsFixedPt C.map1 u)
    (hvfix : IsFixedPt C.map2 v) :
    dist u v ≤
      dist (C.map1 u) (C.map2 u) / (1 - (C.K : ℝ)) := by
  let g : C.carrier → C.carrier :=
    C.invariant2.restrict C.map2 C.carrier C.carrier
  have hg : ContractingWith C.K g := by
    simpa [g] using C.contract2
  have hv' : IsFixedPt g ⟨v, hv⟩ := by
    apply Subtype.ext
    exact hvfix
  have h := hg.dist_le_of_fixedPoint (⟨u, hu⟩ : C.carrier) hv'
  have h' : dist u v ≤
      dist u (C.map2 u) / (1 - (C.K : ℝ)) := by
    change dist u v ≤ dist u (C.map2 u) / (1 - (C.K : ℝ)) at h
    exact h
  rw [hufix]
  exact h'

end CommonCarrierContractionPair

/-! ## A common-carrier bounded-section family -/

/-- A parameter family of bounded-section Picard maps with common ball data. -/
structure BoundedSectionPicardFamily
    (A T V : Type*) [MetricSpace A] [TopologicalSpace T]
    [MetricSpace V] [CompleteSpace V] where
  center : BoundedSectionSpace T V
  radius : ℝ
  radius_nonneg : 0 ≤ radius
  map : A → BoundedSectionSpace T V → BoundedSectionSpace T V
  invariant : ∀ a, MapsTo (map a) (Metric.closedBall center radius)
    (Metric.closedBall center radius)
  K : ℝ≥0
  contract : ∀ a, ContractingWith K
    ((invariant a).restrict (map a) (Metric.closedBall center radius)
      (Metric.closedBall center radius))

namespace BoundedSectionPicardFamily

variable {A T V : Type*} [MetricSpace A] [TopologicalSpace T]
  [MetricSpace V] [CompleteSpace V]
  (F : BoundedSectionPicardFamily A T V)

/-- The common invariant closed ball. -/
def carrier : Set (BoundedSectionSpace T V) :=
  Metric.closedBall F.center F.radius

/-- The complete invariant contraction associated with one parameter. -/
def contractionAt (a : A) : CompleteInvariantContraction
    (BoundedSectionSpace T V) where
  carrier := Metric.closedBall F.center F.radius
  complete := by
    exact Metric.isClosed_closedBall.isComplete
  map := F.map a
  invariant := F.invariant a
  K := F.K
  contract := F.contract a

theorem center_mem : F.center ∈ F.carrier := by
  dsimp [carrier]
  exact Metric.mem_closedBall_self F.radius_nonneg

/-- The Banach fixed point selected in the common invariant ball. -/
noncomputable def fixedPointAt (a : A) : BoundedSectionSpace T V :=
  F.contractionAt a |>.fixedPoint F.center F.center_mem

theorem fixedPointAt_mem (a : A) : F.fixedPointAt a ∈ F.carrier := by
  exact F.contractionAt a |>.fixedPoint_mem F.center F.center_mem

theorem fixedPointAt_isFixedPt (a : A) :
    IsFixedPt (F.map a) (F.fixedPointAt a) := by
  exact F.contractionAt a |>.fixedPoint_isFixedPt F.center F.center_mem

/-- Uniform perturbation of two parameter maps gives fixed-point stability. -/
theorem dist_fixedPointAt_le_of_map_perturbation
    (a b : A) {ε : ℝ}
    (hmap : ∀ z ∈ F.carrier,
      dist (F.map a z) (F.map b z) ≤ ε) :
    dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
      ε / (1 - (F.K : ℝ)) := by
  let C : CommonCarrierContractionPair (BoundedSectionSpace T V) :=
    { carrier := Metric.closedBall F.center F.radius
      complete := by
        exact Metric.isClosed_closedBall.isComplete
      map1 := F.map a
      map2 := F.map b
      invariant1 := F.invariant a
      invariant2 := F.invariant b
      K := F.K
      contract1 := F.contract a
      contract2 := F.contract b }
  have h := C.dist_fixedPoints_le (F.fixedPointAt_mem a)
    (F.fixedPointAt_mem b) (F.fixedPointAt_isFixedPt a)
    (F.fixedPointAt_isFixedPt b) hmap
  simpa [C] using h

/-- Pointwise map continuity only needs the discrepancy at the first fixed point. -/
theorem dist_fixedPointAt_le_of_map_at
    (a b : A) :
    dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
      dist (F.map a (F.fixedPointAt a))
          (F.map b (F.fixedPointAt a)) /
        (1 - (F.K : ℝ)) := by
  let C : CommonCarrierContractionPair (BoundedSectionSpace T V) :=
    { carrier := Metric.closedBall F.center F.radius
      complete := by
        exact Metric.isClosed_closedBall.isComplete
      map1 := F.map a
      map2 := F.map b
      invariant1 := F.invariant a
      invariant2 := F.invariant b
      K := F.K
      contract1 := F.contract a
      contract2 := F.contract b }
  have h := C.dist_fixedPoints_le_of_map_at
    (F.fixedPointAt_mem a) (F.fixedPointAt_mem b)
    (F.fixedPointAt_isFixedPt a) (F.fixedPointAt_isFixedPt b)
  simpa [C] using h

/-- A restricted-state parameter Lipschitz estimate yields fixed-point control. -/
theorem dist_fixedPointAt_le_of_lipschitz
    {L : ℝ≥0}
    (hmap : ∀ z ∈ F.carrier,
      LipschitzWith L (fun a : A => F.map a z))
    (a b : A) :
    dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
      (L : ℝ) * dist a b / (1 - (F.K : ℝ)) := by
  apply F.dist_fixedPointAt_le_of_map_perturbation a b
  intro z hz
  exact (hmap z hz).dist_le_mul a b

/-- Global Lipschitz dependence of the selected fixed point. -/
theorem lipschitz_fixedPointAt_of_lipschitz
    [Nonempty A] {L : ℝ≥0}
    (hmap : ∀ z ∈ F.carrier,
      LipschitzWith L (fun a : A => F.map a z)) :
    LipschitzWith
      ⟨(L : ℝ) / (1 - (F.K : ℝ)), by
        have hK : (F.K : ℝ) < 1 := by
          obtain ⟨a⟩ := ‹Nonempty A›
          exact (NNReal.coe_lt_one).2 (F.contract a).1
        exact div_nonneg (NNReal.coe_nonneg L)
          (le_of_lt (sub_pos.mpr hK))⟩
      F.fixedPointAt := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h := F.dist_fixedPointAt_le_of_lipschitz hmap a b
  change dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
    ((L : ℝ) / (1 - (F.K : ℝ))) * dist a b
  calc
    dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
        (L : ℝ) * dist a b / (1 - (F.K : ℝ)) := h
    _ = ((L : ℝ) / (1 - (F.K : ℝ))) * dist a b := by ring

/-- Joint state/parameter Lipschitz control gives a sharper denominator. -/
theorem dist_fixedPointAt_le_of_joint_lipschitz
    {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ a b : A,
      ∀ z w : BoundedSectionSpace T V,
      z ∈ F.carrier → w ∈ F.carrier →
      dist (F.map a z) (F.map b w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist a b)
    (a b : A) :
    dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
      (Lparam : ℝ) * dist a b / (1 - (Lstate : ℝ)) := by
  let x := F.fixedPointAt a
  let y := F.fixedPointAt b
  have hx : x ∈ F.carrier := F.fixedPointAt_mem a
  have hy : y ∈ F.carrier := F.fixedPointAt_mem b
  have hxa : F.map a x = x := F.fixedPointAt_isFixedPt a
  have hyb : F.map b y = y := F.fixedPointAt_isFixedPt b
  have hineq : dist x y ≤
      (Lstate : ℝ) * dist x y + (Lparam : ℝ) * dist a b := by
    calc
      dist x y = dist (F.map a x) (F.map b y) := by rw [hxa, hyb]
      _ ≤ (Lstate : ℝ) * dist x y + (Lparam : ℝ) * dist a b :=
        hmap a b x y hx hy
  have hden : 0 < 1 - (Lstate : ℝ) := sub_pos.mpr hstate
  apply (le_div_iff₀ hden).2
  nlinarith

/-- Joint Lipschitz control packages as a global Lipschitz fixed-point map. -/
theorem lipschitz_fixedPointAt_of_joint_lipschitz
    [Nonempty A] {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ a b : A,
      ∀ z w : BoundedSectionSpace T V,
      z ∈ F.carrier → w ∈ F.carrier →
      dist (F.map a z) (F.map b w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist a b) :
    LipschitzWith
      ⟨(Lparam : ℝ) / (1 - (Lstate : ℝ)), by
        exact div_nonneg (NNReal.coe_nonneg Lparam)
          (le_of_lt (sub_pos.mpr hstate))⟩
      F.fixedPointAt := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  have h := F.dist_fixedPointAt_le_of_joint_lipschitz hstate hmap a b
  change dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
    ((Lparam : ℝ) / (1 - (Lstate : ℝ))) * dist a b
  calc
    dist (F.fixedPointAt a) (F.fixedPointAt b) ≤
        (Lparam : ℝ) * dist a b / (1 - (Lstate : ℝ)) := h
    _ = ((Lparam : ℝ) / (1 - (Lstate : ℝ))) * dist a b := by ring

/-- Lipschitz fixed-point dependence implies continuity. -/
theorem continuous_fixedPointAt_of_joint_lipschitz
    [Nonempty A] {Lstate Lparam : ℝ≥0}
    (hstate : (Lstate : ℝ) < 1)
    (hmap : ∀ a b : A,
      ∀ z w : BoundedSectionSpace T V,
      z ∈ F.carrier → w ∈ F.carrier →
      dist (F.map a z) (F.map b w) ≤
        (Lstate : ℝ) * dist z w + (Lparam : ℝ) * dist a b) :
    Continuous F.fixedPointAt :=
  (F.lipschitz_fixedPointAt_of_joint_lipschitz hstate hmap).continuous

end BoundedSectionPicardFamily

/-! ## A competing map for one bounded-section problem -/

namespace BoundedSectionPicardProblem

variable {T V : Type*} [TopologicalSpace T] [MetricSpace V] [CompleteSpace V]
  (P : BoundedSectionPicardProblem T V)

/-- A competing invariant contraction on the same ball is quantitatively close
to the selected Picard fixed point whenever its map is uniformly perturbed. -/
theorem dist_fixedPoint_le_of_map_perturbation
    {map2 : BoundedSectionSpace T V → BoundedSectionSpace T V}
    (invariant2 : MapsTo map2 (Metric.closedBall P.center P.radius)
      (Metric.closedBall P.center P.radius))
    (contract2 : ContractingWith P.K
      (invariant2.restrict map2 (Metric.closedBall P.center P.radius)
        (Metric.closedBall P.center P.radius)))
    {v : BoundedSectionSpace T V}
    (hv : v ∈ Metric.closedBall P.center P.radius)
    (hvfix : IsFixedPt map2 v)
    {ε : ℝ}
    (hmap : ∀ z ∈ Metric.closedBall P.center P.radius,
      dist (P.map z) (map2 z) ≤ ε) :
    dist P.fixedPoint v ≤ ε / (1 - (P.K : ℝ)) := by
  let C : CommonCarrierContractionPair (BoundedSectionSpace T V) :=
    { carrier := Metric.closedBall P.center P.radius
      complete := Metric.isClosed_closedBall.isComplete
      map1 := P.map
      map2 := map2
      invariant1 := P.invariant
      invariant2 := invariant2
      K := P.K
      contract1 := P.contract
      contract2 := contract2 }
  have h := C.dist_fixedPoints_le P.fixedPoint_mem hv
    P.fixedPoint_isFixedPt hvfix hmap
  simpa [C] using h

end BoundedSectionPicardProblem

/-! The headline estimates use only the standard contraction-library axioms. -/
#print axioms CommonCarrierContractionPair.dist_fixedPoints_le
#print axioms BoundedSectionPicardFamily.dist_fixedPointAt_le_of_joint_lipschitz
#print axioms BoundedSectionPicardFamily.lipschitz_fixedPointAt_of_joint_lipschitz

end
end ParabolicPDE
end Topping

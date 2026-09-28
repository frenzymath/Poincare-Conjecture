import Topping.ParabolicPDE.Contraction
import Topping.ParabolicPDE.HolderSpace

/-!
# Consumers for parabolic Holder balls

These adapters connect the closed parabolic Holder ball to the ambient
bounded-section contraction API.  They deliberately take Holder preservation,
ball invariance, and contraction as hypotheses: no PDE solver or existence
claim is hidden in the definitions below.
-/

namespace Topping
namespace ParabolicPDE

open Function Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

variable {X T V : Type*}
  [TopologicalSpace X] [PseudoMetricSpace X]
  [TopologicalSpace T] [PseudoMetricSpace T]
  [MetricSpace V]

/-! ## Invariance and restriction -/

/-- Separate Holder preservation and ordinary closed-ball invariance combine to
forward invariance of the parabolic Holder ball. -/
theorem mapsTo_parabolicHolderSectionBallSet
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (center : (S × J) →ᵇ V) (radius : ℝ)
    {f : ((S × J) →ᵇ V) → ((S × J) →ᵇ V)}
    (hholder : ∀ u ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β,
      f u ∈ ParabolicHolderSectionSet
        (X := X) (T := T) (V := V) S J Cs α Ct β)
    (hball : MapsTo f (Metric.closedBall center radius)
      (Metric.closedBall center radius)) :
    MapsTo f
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius) := by
  intro u hu
  exact ⟨hholder u hu.1, hball hu.2⟩

/-- The invariant Holder ball induces the corresponding self-map on its
subtype. -/
def parabolicHolderSectionBallMap
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (center : (S × J) →ᵇ V) (radius : ℝ)
    {f : ((S × J) →ᵇ V) → ((S × J) →ᵇ V)}
    (hmap : MapsTo f
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)) :
    ParabolicHolderSectionBall
      (X := X) (T := T) (V := V) S J Cs α Ct β center radius →
      ParabolicHolderSectionBall
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius :=
  hmap.restrict f
    (ParabolicHolderSectionBallSet
      (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
    (ParabolicHolderSectionBallSet
      (X := X) (T := T) (V := V) S J Cs α Ct β center radius)

/-! ## Contraction and fixed-point adapters -/

/-- An ambient contraction remains a contraction after restriction to the
invariant Holder ball. -/
theorem parabolicHolderSectionBallMap_contracting
    {S : Set X} {J : Set T} {Cs α Ct β K : NNReal}
    (center : (S × J) →ᵇ V) (radius : ℝ)
    {f : ((S × J) →ᵇ V) → ((S × J) →ᵇ V)}
    (hmap : MapsTo f
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius))
    (hcontract : ContractingWith K f) :
    ContractingWith K
      (parabolicHolderSectionBallMap center radius hmap) := by
  simpa only [parabolicHolderSectionBallMap] using hcontract.restrict hmap

/-- Package an invariant ambient contraction as a complete contraction on the
closed Holder ball. -/
def parabolicHolderSectionBallContraction
    {S : Set X} {J : Set T} {Cs α Ct β K : NNReal}
    [CompleteSpace V]
    (center : (S × J) →ᵇ V) (radius : ℝ)
    {f : ((S × J) →ᵇ V) → ((S × J) →ᵇ V)}
    (hmap : MapsTo f
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius))
    (hcontract : ContractingWith K f) :
    CompleteInvariantContraction
      ((S × J) →ᵇ V) :=
  { carrier := ParabolicHolderSectionBallSet
      (X := X) (T := T) (V := V) S J Cs α Ct β center radius
    complete := (isClosed_parabolicHolderSectionBallSet
      S J Cs α Ct β center radius).isComplete
    map := f
    invariant := hmap
    K := K
    contract := hcontract.restrict hmap }

/-- If the Holder center is admissible, Banach's theorem supplies a fixed
point inside the Holder ball. -/
theorem exists_parabolicHolderSectionBall_fixedPoint
    {S : Set X} {J : Set T} {Cs α Ct β K : NNReal}
    [CompleteSpace V]
    (center : (S × J) →ᵇ V) {radius : ℝ}
    (hcenter : center ∈ ParabolicHolderSectionSet
      (X := X) (T := T) (V := V) S J Cs α Ct β)
    (hradius : 0 ≤ radius)
    {f : ((S × J) →ᵇ V) → ((S × J) →ᵇ V)}
    (hmap : MapsTo f
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius))
    (hcontract : ContractingWith K f) :
    ∃ u : ParabolicHolderSectionBall
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius,
      IsFixedPt f u.1 := by
  let C := parabolicHolderSectionBallContraction center radius hmap hcontract
  have hmem : center ∈ C.carrier :=
    parabolicHolderSectionBall_center_mem S J Cs α Ct β center radius
      hcenter hradius
  let u : (S × J) →ᵇ V := C.fixedPoint center hmem
  have humem : u ∈ C.carrier := C.fixedPoint_mem center hmem
  have hufix : IsFixedPt f u := C.fixedPoint_isFixedPt center hmem
  exact ⟨⟨u, humem⟩, hufix⟩

/-! ## Uniqueness in the Holder ball -/

/-- Any two fixed points of an invariant contracting map which lie in the
parabolic Holder ball agree.  This is the subtype-level uniqueness consumer
for `exists_parabolicHolderSectionBall_fixedPoint`. -/
theorem parabolicHolderSectionBall_fixedPoint_unique
    {S : Set X} {J : Set T} {Cs α Ct β K : NNReal}
    [CompleteSpace V]
    (center : (S × J) →ᵇ V) (radius : ℝ)
    {f : ((S × J) →ᵇ V) → ((S × J) →ᵇ V)}
    (hmap : MapsTo f
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius)
      (ParabolicHolderSectionBallSet
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius))
    (hcontract : ContractingWith K f)
    {u v : ParabolicHolderSectionBall
        (X := X) (T := T) (V := V) S J Cs α Ct β center radius}
    (hu : IsFixedPt f u.1) (hv : IsFixedPt f v.1) :
    u = v := by
  let C := parabolicHolderSectionBallContraction center radius hmap hcontract
  have hu' : u.1 ∈ C.carrier := u.2
  have hv' : v.1 ∈ C.carrier := v.2
  have huv : u.1 = v.1 := C.fixedPoint_unique hu' hv' hu hv
  exact Subtype.ext huv

end
end ParabolicPDE
end Topping

import Topping.ParabolicPDE.HolderSpace
import Topping.ParabolicPDE.ProductHolder

/-!
# Product Holder estimate for parabolic sections

This module exposes the ordinary product-space Holder estimate carried by a
parabolic section when its spatial and temporal exponents agree.  The target
is stated on the existing product-of-subtypes carrier `S × J`; it deliberately
does not identify that carrier with the different subtype of `X × T`.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

/-- A common-exponent parabolic section is Holder on its product carrier. -/
theorem parabolicHolderSectionSpace_holderWith_commonExponent
    {X T V : Type*} [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T] [PseudoMetricSpace V]
    {S : Set X} {J : Set T} {Cs Ct α : NNReal}
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs α Ct α) :
    HolderWith (Cs + Ct) α (fun z : S × J => u.1 z) := by
  have hp := ParabolicHolderControl.holderOnWith_prod_of_common_exponent
    (u := fun z : S × J => u.1 z)
    (J := (Set.univ : Set J)) (S := (Set.univ : Set S))
    (parabolicHolderSectionSpace_mem S J Cs α Ct α u)
  simpa only [Set.univ_prod_univ, holderOnWith_univ] using hp

/- An explicit pair of slice-wise Lipschitz estimates can be packaged directly
   into the bounded-continuous parabolic section subtype. -/
def parabolicHolderSectionSpace_of_lipschitz
    {X T V : Type*} [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    {S : Set X} {J : Set T} {Cs Ct : NNReal}
    (u : (S × J) →ᵇ V)
    (hsp : ∀ t : J, LipschitzWith Cs (fun x : S => u (x, t)))
    (htm : ∀ x : S,
      LipschitzOnWith Ct (fun t : J => u (x, t)) (Set.univ : Set J)) :
    ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs 1 Ct 1 := by
  refine ⟨u, ?_⟩
  change ParabolicHolderControl (fun z : S × J => u z)
    (Set.univ : Set J) Cs 1 Ct 1
  apply ParabolicHolderControl.of_lipschitz
  · intro t ht
    simpa using hsp t
  · intro x
    simpa using htm x

end
end ParabolicPDE
end Topping

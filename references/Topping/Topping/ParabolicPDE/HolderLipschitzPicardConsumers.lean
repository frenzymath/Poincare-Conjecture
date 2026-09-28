import Topping.ParabolicPDE.HolderSectionProduct
import Topping.ParabolicPDE.HolderSectionPicard

/-!
# Lipschitz-center consumer for Holder Picard iteration

This file supplies the small bridge from explicit slice-wise Lipschitz bounds
to the Holder-ball fixed-point consumer.  The iteration map's Holder
preservation remains an explicit hypothesis; no PDE solver is constructed.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

variable {X T V : Type*}
  [TopologicalSpace X] [PseudoMetricSpace X]
  [TopologicalSpace T] [PseudoMetricSpace T]
  [MetricSpace V] [CompleteSpace V]

/- A center with explicit slice-wise Lipschitz estimates supplies the Holder
   premise needed by the Picard fixed-point ball consumer. -/
theorem BoundedSectionPicardProblem.fixedPoint_mem_parabolicHolderSectionBall_of_lipschitz_center
    {S : Set X} {J : Set T} {Cs Ct : NNReal}
    (P : BoundedSectionPicardProblem (S × J) V)
    (hsp : ∀ t : J,
      LipschitzWith Cs (fun x : S => P.center (x, t)))
    (htm : ∀ x : S,
      LipschitzOnWith Ct (fun t : J => P.center (x, t))
        (Set.univ : Set J))
    (hmap : ∀ (u : BoundedSectionSpace (S × J) V),
      ParabolicHolderControl (fun z : S × J => u z)
        (Set.univ : Set J) Cs 1 Ct 1 ->
      ParabolicHolderControl (fun z : S × J => P.map u z)
        (Set.univ : Set J) Cs 1 Ct 1) :
    P.fixedPoint ∈ ParabolicHolderSectionBallSet
      (X := X) (T := T) (V := V) S J Cs 1 Ct 1 P.center P.radius := by
  let hcenter :
      ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
        S J Cs 1 Ct 1 :=
    parabolicHolderSectionSpace_of_lipschitz P.center hsp htm
  have hcenterControl :
    ParabolicHolderControl (fun z : S × J => P.center z)
        (Set.univ : Set J) Cs 1 Ct 1 :=
    by
      simpa [hcenter, parabolicHolderSectionSpace_of_lipschitz] using
        (parabolicHolderSectionSpace_mem S J Cs 1 Ct 1 hcenter)
  exact P.fixedPoint_mem_parabolicHolderSectionBall hcenterControl hmap

#print axioms
  BoundedSectionPicardProblem.fixedPoint_mem_parabolicHolderSectionBall_of_lipschitz_center

end
end ParabolicPDE
end Topping

import Topping.ParabolicPDE.HolderSpace

/-!
# Algebraic closure of parabolic Holder section spaces

The raw `ParabolicHolderControl` API is closed under subtraction.  This file
exposes the corresponding operation on bounded continuous section subtypes,
which is the form needed by difference estimates for linearized equations.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

/-- Subtracting two controlled bounded sections preserves Holder control, with
the spatial and temporal constants added componentwise. -/
def parabolicHolderSectionSpace_sub {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [NormedAddCommGroup V]
    (S : Set X) (J : Set T)
    (Cu alpha Cv beta Du Dv : NNReal)
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cu alpha Cv beta)
    (v : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Du alpha Dv beta) :
    ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J (Cu + Du) alpha (Cv + Dv) beta := by
  refine ⟨u.1 - v.1, ?_⟩
  change ParabolicHolderControl (fun z : S × J => u.1 z - v.1 z)
    (Set.univ : Set J) (Cu + Du) alpha (Cv + Dv) beta
  simpa only [BoundedContinuousFunction.sub_apply] using
    (ParabolicHolderControl.sub
      (parabolicHolderSectionSpace_mem S J Cu alpha Cv beta u)
      (parabolicHolderSectionSpace_mem S J Du alpha Dv beta v))

end
end ParabolicPDE
end Topping

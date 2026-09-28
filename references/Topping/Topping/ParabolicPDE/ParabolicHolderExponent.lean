import Topping.ParabolicPDE.ParabolicHolder

/-!
# Exponent downgrade for parabolic Holder controls

On bounded carriers, a Holder estimate at a larger exponent implies the
corresponding estimate at every smaller exponent.  The explicit diameter
factors are important for the section-space Schauder scale: they prevent a
Lipschitz coefficient estimate from being silently identified with an
arbitrary Holder estimate.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped ENNReal NNReal Topology

noncomputable section

namespace ParabolicHolderControl

variable {X T V : Type*}
  [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]

/-- **Math.** Downgrade the spatial and temporal exponents of a parabolic
Holder control on bounded carriers, with the sharp elementary diameter
factors. -/
theorem of_le_exponents
    {u : X × T → V} {J : Set T}
    {Cs α Ct β r s D_X D_T : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β)
    (hX : ∀ x y : X, edist x y ≤ D_X)
    (hT : ∀ x ∈ J, ∀ y ∈ J, edist x y ≤ D_T)
    (hrα : r ≤ α) (hsβ : s ≤ β) :
    ParabolicHolderControl u J
      (Cs * D_X ^ ((α : ℝ) - (r : ℝ))) r
      (Ct * D_T ^ ((β : ℝ) - (s : ℝ))) s := by
  refine ⟨?_, ?_⟩
  · intro t ht
    change HolderWith
      (Cs * D_X ^ ((α : ℝ) - (r : ℝ))) r
      (fun x : X => u (x, t))
    exact HolderWith.of_le hX (h.spatial t ht) hrα
  · intro x
    change HolderOnWith
      (Ct * D_T ^ ((β : ℝ) - (s : ℝ))) s
      (fun t : T => u (x, t)) J
    exact HolderOnWith.of_le hT (h.temporal x) hsβ

end ParabolicHolderControl

end
end ParabolicPDE
end Topping

import Topping.ParabolicPDE.SectionSolverConsumers
import Topping.ParabolicPDE.ParabolicHolderRestrictedContinuity
import Topping.ParabolicPDE.HolderSpace

/-!
# Compact-base consumers for Schauder/Holder data

On a compact base and a compact time subtype, positive split Holder exponents
make the solution carried by a `SchauderEstimateContract` continuous on the
restricted space-time domain.  Compactness then packages that restriction as a
bounded continuous section, and the contract's estimate supplies its Holder
membership.  This is a consumer of supplied Schauder data; it does not assert
a PDE solver or construct one.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

namespace SchauderEstimateContract

variable {X T V : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup V]
  {S : Set X} {J : Set T} {α β : ℝ≥0}

/-! ## Restriction to a compact time subtype -/

/-- The solution of a contract is continuous after restricting its time
coordinate to a compact time subtype, provided both Holder exponents are
positive. -/
theorem continuousOn_restrict_time_of_positive
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) :
    Continuous (fun z : S × J => C.solution (z.1, z.2.1)) := by
  have hcont : ContinuousOn C.solution (Set.univ ×ˢ J) :=
    C.solution_control.continuousOn_prod_of_positive hα hβ
  have hpre : Continuous (fun z : S × J => (z.1, z.2.1)) := by
    exact continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hmaps : ∀ z : S × J, (z.1, z.2.1) ∈ (Set.univ ×ˢ J) := by
    intro z
    exact ⟨Set.mem_univ z.1, z.2.2⟩
  have hcomp : Continuous (C.solution ∘ fun z : S × J => (z.1, z.2.1)) :=
    hcont.comp_continuous hpre hmaps
  change Continuous (C.solution ∘ fun z : S × J => (z.1, z.2.1))
  exact hcomp

/-! ## Bounded section produced by compactness -/

/-- Compactness packages the restricted contract solution as a bounded
continuous section on `X × J`. -/
noncomputable def boundedSection
    [CompactSpace S] [CompactSpace J]
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) :
    BoundedSectionSpace (S × J) V :=
  BoundedContinuousFunction.mkOfCompact
    (ContinuousMap.mk
      (fun z : S × J => C.solution (z.1, z.2.1))
      (C.continuousOn_restrict_time_of_positive hα hβ))

@[simp] theorem boundedSection_apply
    [CompactSpace S] [CompactSpace J]
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) (z : S × J) :
    C.boundedSection hα hβ z = C.solution (z.1, z.2.1) := rfl

/-- The compactly packaged solution retains the contract's source-scale Holder
estimate on `X × J`. -/
theorem boundedSection_control
    [CompactSpace S] [CompactSpace J]
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) :
    ParabolicHolderControl (fun z : S × J => C.boundedSection hα hβ z)
      (Set.univ : Set J) C.sourceCs α C.sourceCt β := by
  have hC := C.solution_control_mono_source
  refine ⟨?_, ?_⟩
  · intro t ht x y
    change edist (C.solution (x, t.1)) (C.solution (y, t.1)) ≤
      (C.sourceCs : ℝ≥0∞) * edist x y ^ (α : ℝ)
    simpa only [C.boundedSection_apply hα hβ] using
      hC.spatial t.1 t.2 x y
  · intro x s hs t ht
    change edist (C.solution (x, s.1)) (C.solution (x, t.1)) ≤
      (C.sourceCt : ℝ≥0∞) * edist s t ^ (β : ℝ)
    simpa only [C.boundedSection_apply hα hβ, Subtype.edist_eq] using
      hC.temporal x s.1 s.2 t.1 t.2

/-- The compact-base solution is an element of the complete parabolic Holder
section space at the contract's source scale. -/
noncomputable def holderSection
    [CompactSpace S] [CompactSpace J]
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) :
    ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J C.sourceCs α C.sourceCt β :=
  ⟨C.boundedSection hα hβ, C.boundedSection_control hα hβ⟩

@[simp] theorem holderSection_coe
    [CompactSpace S] [CompactSpace J]
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) :
    (C.holderSection hα hβ).1 = C.boundedSection hα hβ := rfl

/-! A version with ordinary compactness hypotheses installs the subtype
compact-space instances needed by the preceding construction. -/
theorem exists_holderSection_of_isCompact
    (hS : IsCompact S) (hJ : IsCompact J)
    (C : SchauderEstimateContract (X := S) (T := T) (V := V) J α β)
    (hα : 0 < α) (hβ : 0 < β) :
    ∃ u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
        S J C.sourceCs α C.sourceCt β,
      ∀ z : S × J, u.1 z = C.solution (z.1, z.2.1) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  letI : CompactSpace J := isCompact_iff_compactSpace.mp hJ
  refine ⟨C.holderSection hα hβ, ?_⟩
  intro z
  rfl

end SchauderEstimateContract

end
end ParabolicPDE
end Topping

#print axioms Topping.ParabolicPDE.SchauderEstimateContract.continuousOn_restrict_time_of_positive
#print axioms Topping.ParabolicPDE.SchauderEstimateContract.boundedSection_control
#print axioms Topping.ParabolicPDE.SchauderEstimateContract.holderSection

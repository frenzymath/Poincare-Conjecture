import Topping.ParabolicPDE.SectionSpacePicard
import Topping.ParabolicPDE.HolderSpace

/-!
# Holder regularity of a compact-section Picard fixed point

The Banach contraction package works in the ambient sup-metric space of bounded
continuous sections.  This file records the separate regularity consumer: if
the center and the iteration map preserve one parabolic Holder estimate, the
selected fixed point has that estimate as well.  The argument uses pointwise
continuity of bounded-section evaluation and the closedness of the Holder
inequalities; it does not assert a Schauder estimate or a PDE solver.
-/

namespace Topping
namespace ParabolicPDE

open Filter Function Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

variable {X T V : Type*}
  [TopologicalSpace X] [PseudoMetricSpace X]
  [TopologicalSpace T] [PseudoMetricSpace T]
  [MetricSpace V] [CompleteSpace V]

/-! The iteration preserves the Holder control carried by its center. -/

theorem BoundedSectionPicardProblem.iterate_parabolicHolderControl
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (P : BoundedSectionPicardProblem (S × J) V)
    (hcenter : ParabolicHolderControl
      (fun z : S × J => P.center z) (Set.univ : Set J) Cs α Ct β)
    (hmap : ∀ (u : BoundedSectionSpace (S × J) V),
      ParabolicHolderControl (fun z : S × J => u z)
        (Set.univ : Set J) Cs α Ct β →
      ParabolicHolderControl (fun z : S × J => P.map u z)
        (Set.univ : Set J) Cs α Ct β) :
    ∀ n : ℕ, ParabolicHolderControl
      (fun z : S × J => (P.map^[n] P.center) z)
      (Set.univ : Set J) Cs α Ct β := by
  intro n
  induction n with
  | zero =>
      simpa only [Function.iterate_zero, id_eq] using hcenter
  | succ n ih =>
      simpa only [Function.iterate_succ_apply'] using
        hmap (P.map^[n] P.center) ih

/-!
The ambient Picard limit inherits the same Holder control.  The pointwise
limit is obtained by composing the sup-metric convergence with evaluation at a
fixed section-domain point.
-/

theorem BoundedSectionPicardProblem.fixedPoint_parabolicHolderControl
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (P : BoundedSectionPicardProblem (S × J) V)
    (hcenter : ParabolicHolderControl
      (fun z : S × J => P.center z) (Set.univ : Set J) Cs α Ct β)
    (hmap : ∀ (u : BoundedSectionSpace (S × J) V),
      ParabolicHolderControl (fun z : S × J => u z)
        (Set.univ : Set J) Cs α Ct β →
      ParabolicHolderControl (fun z : S × J => P.map u z)
        (Set.univ : Set J) Cs α Ct β) :
    ParabolicHolderControl
      (fun z : S × J => P.fixedPoint z)
      (Set.univ : Set J) Cs α Ct β := by
  apply ParabolicHolderControl.of_tendsto
    (l := atTop)
    (f := fun n : ℕ => fun z : S × J => (P.map^[n] P.center) z)
    (g := fun z : S × J => P.fixedPoint z)
  · intro z
    have hev : Continuous
        (fun u : BoundedSectionSpace (S × J) V => u z) :=
      continuous_eval_const z
    change Tendsto
      (fun n : ℕ => ((P.map^[n] P.center) : (S × J) →ᵇ V) z)
      atTop (𝓝 (P.fixedPoint z))
    exact hev.continuousAt.tendsto.comp P.tendsto_iterate_fixedPoint
  · exact Eventually.of_forall
      (P.iterate_parabolicHolderControl hcenter hmap)

/-! The same result packaged as membership in the closed Holder ball used by
the section-space iteration. -/

theorem BoundedSectionPicardProblem.fixedPoint_mem_parabolicHolderSectionBall
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (P : BoundedSectionPicardProblem (S × J) V)
    (hcenter : ParabolicHolderControl
      (fun z : S × J => P.center z) (Set.univ : Set J) Cs α Ct β)
    (hmap : ∀ (u : BoundedSectionSpace (S × J) V),
      ParabolicHolderControl (fun z : S × J => u z)
        (Set.univ : Set J) Cs α Ct β →
      ParabolicHolderControl (fun z : S × J => P.map u z)
        (Set.univ : Set J) Cs α Ct β) :
    P.fixedPoint ∈ ParabolicHolderSectionBallSet
      (X := X) (T := T) (V := V) S J Cs α Ct β P.center P.radius := by
  refine ⟨?_, P.fixedPoint_mem⟩
  exact P.fixedPoint_parabolicHolderControl hcenter hmap

/-! The fixed point can be viewed directly as an element of the Holder ball. -/

noncomputable def BoundedSectionPicardProblem.holderFixedPoint
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (P : BoundedSectionPicardProblem (S × J) V)
    (hcenter : ParabolicHolderControl
      (fun z : S × J => P.center z) (Set.univ : Set J) Cs α Ct β)
    (hmap : ∀ (u : BoundedSectionSpace (S × J) V),
      ParabolicHolderControl (fun z : S × J => u z)
        (Set.univ : Set J) Cs α Ct β →
      ParabolicHolderControl (fun z : S × J => P.map u z)
        (Set.univ : Set J) Cs α Ct β) :
    ParabolicHolderSectionBall (X := X) (T := T) (V := V)
      S J Cs α Ct β P.center P.radius :=
  ⟨P.fixedPoint, P.fixedPoint_mem_parabolicHolderSectionBall hcenter hmap⟩

@[simp] theorem BoundedSectionPicardProblem.holderFixedPoint_coe
    {S : Set X} {J : Set T} {Cs α Ct β : NNReal}
    (P : BoundedSectionPicardProblem (S × J) V)
    (hcenter : ParabolicHolderControl
      (fun z : S × J => P.center z) (Set.univ : Set J) Cs α Ct β)
    (hmap : ∀ (u : BoundedSectionSpace (S × J) V),
      ParabolicHolderControl (fun z : S × J => u z)
        (Set.univ : Set J) Cs α Ct β →
      ParabolicHolderControl (fun z : S × J => P.map u z)
        (Set.univ : Set J) Cs α Ct β) :
    (P.holderFixedPoint hcenter hmap : (S × J) →ᵇ V) = P.fixedPoint := rfl

#print axioms BoundedSectionPicardProblem.fixedPoint_parabolicHolderControl
#print axioms BoundedSectionPicardProblem.fixedPoint_mem_parabolicHolderSectionBall

end
end ParabolicPDE
end Topping

import PoincareConjecture.Topology.MappingTorus
import Mathlib.Topology.Homeomorph.Quotient
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# The identity mapping torus is a product with the circle

This identifies the actual orbit quotient, rather than using the product
description only in prose. Together with the sphere-fibre calculation it
gives the fundamental group of the ordinary product `S² × S¹`.
-/

open Function Set Topology
open scoped ContinuousMap

namespace PoincareConjecture

variable (X : Type*) [TopologicalSpace X]

/-- The identity mapping-torus quotient is homeomorphic to the actual product
with `ℝ/ℤ`. The quotient relation is proved equal to the kernel relation of
the product projection, and the latter is an open quotient map. -/
noncomputable def identityMappingTorusHomeomorph :
    MappingTorus (Homeomorph.refl X) ≃ₜ X × UnitAddCircle := by
  let f : MappingTorusCover (Homeomorph.refl X) → X × UnitAddCircle :=
    fun z => (z.1, (z.2 : UnitAddCircle))
  have hf : IsOpenQuotientMap f :=
    IsOpenQuotientMap.id.prodMap
      (QuotientAddGroup.isOpenQuotientMap_mk (N := AddSubgroup.zmultiples (1 : ℝ)))
  have hrel : ∀ z w : MappingTorusCover (Homeomorph.refl X),
      MulAction.orbitRel (Multiplicative ℤ) _ z w ↔ Setoid.ker f z w := by
    intro z w
    change (∃ g : Multiplicative ℤ, g • w = z) ↔ f z = f w
    have hact (g : Multiplicative ℤ) :
        g • w = (w.1, w.2 + (g.toAdd : ℝ)) := by
      change (((Homeomorph.refl X) ^ g.toAdd) w.1, w.2 + (g.toAdd : ℝ)) = _
      change (((1 : X ≃ₜ X) ^ g.toAdd) w.1, w.2 + (g.toAdd : ℝ)) = _
      simp only [one_zpow, Homeomorph.one_apply]
    constructor
    · rintro ⟨g, hg⟩
      rw [hact] at hg
      have hfst := congrArg Prod.fst hg
      have hsnd := congrArg Prod.snd hg
      change (z.1, (z.2 : UnitAddCircle)) = (w.1, (w.2 : UnitAddCircle))
      refine Prod.ext ?_ ?_
      · exact hfst.symm
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change z.2 - w.2 ∈ AddSubgroup.zmultiples (1 : ℝ)
      rw [AddSubgroup.mem_zmultiples_iff]
      refine ⟨g.toAdd, ?_⟩
      simp only [zsmul_eq_mul, mul_one]
      change w.2 + (g.toAdd : ℝ) = z.2 at hsnd
      linarith
    · intro h
      have hfst : z.1 = w.1 := congrArg (Prod.fst : X × UnitAddCircle → X) h
      have hsnd : (z.2 : UnitAddCircle) = (w.2 : UnitAddCircle) :=
        congrArg (Prod.snd : X × UnitAddCircle → UnitAddCircle) h
      have hmem := QuotientAddGroup.eq_iff_sub_mem.mp hsnd
      rw [AddSubgroup.mem_zmultiples_iff] at hmem
      obtain ⟨n, hn⟩ := hmem
      simp only [zsmul_eq_mul, mul_one] at hn
      refine ⟨Multiplicative.ofAdd n, ?_⟩
      rw [hact]
      refine Prod.ext ?_ ?_
      · exact hfst.symm
      change w.2 + (n : ℝ) = z.2
      linarith
  let fc : C(MappingTorusCover (Homeomorph.refl X), X × UnitAddCircle) := ⟨f, hf.continuous⟩
  exact (Homeomorph.Quotient.congrRight hrel).trans
    (Topology.IsQuotientMap.homeomorph (f := fc) hf.isQuotientMap)

end PoincareConjecture

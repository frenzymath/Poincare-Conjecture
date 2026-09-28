import PoincareConjecture.Topology.FiniteQuotient
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Int
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Algebra.Group.Equiv.Opposite

/-!
# Nontrivial fundamental groups of mapping tori

The mapping torus of a homeomorphism `φ : X ≃ₜ X` is represented by the actual
orbit quotient of `X × ℝ` by `(x,t) ↦ (φ^n x,t+n)`, for `n : ℤ`.
The action is free and properly discontinuous because its real coordinate is
an integer translation. These properties are proved, not assumed.

Monodromy then surjects from the fundamental group of the quotient onto the
infinite cyclic acting group. This supplies the nontriviality obstruction
needed to exclude sphere-bundle factors in the simply connected endgame.
It does not assert the stronger full calculation `π₁ = ℤ` for arbitrary `X`.
-/

open Function Set Filter
open scoped Topology ContinuousMap

namespace PoincareConjecture

variable {X : Type*} [TopologicalSpace X] (φ : X ≃ₜ X)

/-- The product covering space, tagged by its monodromy so that different
actions on the same product do not compete as typeclass instances. -/
def MappingTorusCover (_φ : X ≃ₜ X) := X × ℝ

instance : TopologicalSpace (MappingTorusCover φ) :=
  inferInstanceAs (TopologicalSpace (X × ℝ))

instance [T2Space X] : T2Space (MappingTorusCover φ) :=
  inferInstanceAs (T2Space (X × ℝ))

instance [LocallyCompactSpace X] : LocallyCompactSpace (MappingTorusCover φ) :=
  inferInstanceAs (LocallyCompactSpace (X × ℝ))

instance [PathConnectedSpace X] : PathConnectedSpace (MappingTorusCover φ) :=
  inferInstanceAs (PathConnectedSpace (X × ℝ))

instance [SimplyConnectedSpace X] : SimplyConnectedSpace (MappingTorusCover φ) := by
  let e : X × ℝ ≃ₕ X :=
    ((ContinuousMap.HomotopyEquiv.refl X).prodCongr
      (ContractibleSpace.hequiv ℝ Unit).some).trans
        (Homeomorph.prodUnique X Unit).toHomotopyEquiv
  exact e.simplyConnectedSpace

/-- The mapping-torus action on the product cover. -/
noncomputable instance mappingTorusAction : MulAction (Multiplicative ℤ) (MappingTorusCover φ) where
  smul g z := ((φ ^ g.toAdd) z.1, z.2 + (g.toAdd : ℝ))
  one_smul z := by
    change ((φ ^ (0 : ℤ)) z.1, z.2 + ((0 : ℤ) : ℝ)) = z
    simp
  mul_smul g h z := by
    change ((φ ^ (g.toAdd + h.toAdd)) z.1, z.2 + ((g.toAdd + h.toAdd : ℤ) : ℝ)) =
      ((φ ^ g.toAdd) ((φ ^ h.toAdd) z.1), (z.2 + (h.toAdd : ℝ)) + (g.toAdd : ℝ))
    rw [zpow_add]
    simp only [Homeomorph.mul_apply, Int.cast_add]
    congr 1
    ring

/-- The actual mapping-torus quotient, with no fundamental-group properties
included in its definition. -/
abbrev MappingTorus := MulAction.orbitRel.Quotient (Multiplicative ℤ) (MappingTorusCover φ)

local instance action_continuous : ContinuousConstSMul (Multiplicative ℤ) (MappingTorusCover φ) where
  continuous_const_smul g := by
    change Continuous (fun z : MappingTorusCover φ => ((φ ^ g.toAdd) z.1, z.2 + (g.toAdd : ℝ)))
    exact ((φ ^ g.toAdd).continuous.comp continuous_fst).prodMk
      (continuous_snd.add continuous_const)

local instance action_free : IsCancelSMul (Multiplicative ℤ) (MappingTorusCover φ) := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g z h
  have hs := congrArg Prod.snd h
  change z.2 + (g.toAdd : ℝ) = z.2 at hs
  have hg : (g.toAdd : ℝ) = 0 := by linarith
  apply Multiplicative.toAdd.injective
  exact_mod_cast hg

/-- Proper discontinuity follows from bounding the integer translation
between the real-coordinate images of two arbitrary compact sets. -/
local instance action_proper : ProperlyDiscontinuousSMul (Multiplicative ℤ) (MappingTorusCover φ) := by
  constructor
  intro K L hK hL
  have hK' := hK.image continuous_snd
  have hL' := hL.image continuous_snd
  obtain ⟨a, ha⟩ := hK'.bddBelow
  obtain ⟨b, hb⟩ := hK'.bddAbove
  obtain ⟨c, hc⟩ := hL'.bddBelow
  obtain ⟨d, hd⟩ := hL'.bddAbove
  have hfinite : (Multiplicative.toAdd ⁻¹' Icc (⌈c - b⌉ : ℤ) ⌊d - a⌋).Finite :=
    (finite_Icc _ _).preimage Multiplicative.toAdd.injective.injOn
  apply hfinite.subset
  intro g hg
  obtain ⟨_, ⟨z, hz, rfl⟩, hgz⟩ := hg
  have haz : a ≤ z.2 := ha (mem_image_of_mem Prod.snd hz)
  have hzb : z.2 ≤ b := hb (mem_image_of_mem Prod.snd hz)
  have hcz : c ≤ z.2 + (g.toAdd : ℝ) := hc (mem_image_of_mem Prod.snd hgz)
  have hzd : z.2 + (g.toAdd : ℝ) ≤ d := hd (mem_image_of_mem Prod.snd hgz)
  exact ⟨Int.ceil_le.mpr (by linarith), Int.le_floor.mpr (by linarith)⟩

/-- The product cover of a mapping torus is a genuine quotient covering. -/
theorem mappingTorus_isQuotientCoveringMap [LocallyCompactSpace X] [T2Space X] :
    IsQuotientCoveringMap
      (Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (MappingTorusCover φ))) (Multiplicative ℤ) :=
  isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

/-- A mapping torus of a path-connected locally compact Hausdorff space is
not simply connected. In particular this applies to both sphere-bundle
monodromies, identity and antipodal, without assuming their fundamental groups. -/
theorem mappingTorus_not_simplyConnected [LocallyCompactSpace X] [T2Space X]
    [PathConnectedSpace X] : ¬ SimplyConnectedSpace (MappingTorus φ) := by
  intro h
  letI := h
  have hG := quotientCovering_group_subsingleton (mappingTorus_isQuotientCoveringMap φ)
  exact (zero_ne_one : (0 : ℤ) ≠ 1)
    (congrArg Multiplicative.toAdd
      (hG.elim (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 1)))

/-- The obstruction is basepoint independent: every fundamental group of
the actual mapping-torus quotient is nontrivial. -/
theorem mappingTorus_fundamentalGroup_not_subsingleton
    [LocallyCompactSpace X] [T2Space X] [PathConnectedSpace X] (q : MappingTorus φ) :
    ¬ Subsingleton (FundamentalGroup (MappingTorus φ) q) := by
  intro h
  letI := h
  let p := Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (MappingTorusCover φ))
  have hp := mappingTorus_isQuotientCoveringMap φ
  obtain ⟨e, he⟩ := hp.surjective q
  have hop : Subsingleton (Multiplicative ℤ)ᵐᵒᵖ :=
    (hp.fundamentalGroupToMulOpposite_surjective ⟨e, he⟩).subsingleton
  have hg : (Multiplicative.ofAdd (0 : ℤ)) = Multiplicative.ofAdd 1 :=
    MulOpposite.op_injective (hop.elim _ _)
  exact (zero_ne_one : (0 : ℤ) ≠ 1) (congrArg Multiplicative.toAdd hg)

/-- For a simply connected fibre, the full fundamental group of the actual
mapping torus is the infinite cyclic group. The covering's monodromy is
proved both injective and surjective by the imported path-lifting theorems. -/
noncomputable def mappingTorusFundamentalGroupEquiv
    [LocallyCompactSpace X] [T2Space X] [SimplyConnectedSpace X] (q : MappingTorus φ) :
    FundamentalGroup (MappingTorus φ) q ≃* Multiplicative ℤ := by
  let hp := mappingTorus_isQuotientCoveringMap φ
  let e : (Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) (MappingTorusCover φ))) ⁻¹' {q} :=
    ⟨(hp.surjective q).choose, (hp.surjective q).choose_spec⟩
  exact (hp.fundamentalGroupEquiv e).trans MulOpposite.opMulEquiv.symm

end PoincareConjecture

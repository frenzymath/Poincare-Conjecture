import HatcherLib.Ch1.CoveringSpaces
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Chapter 1: sheets of a covering

A sheet over `U` is an open part of the total space that maps
homeomorphically onto `U`.  We use a predicate rather than choosing a
trivialization, so the definition is independent of any particular indexing
of the sheets.
-/

namespace HatcherLib

noncomputable section

universe u v

variable {E : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace X]

/-- `V` is a sheet of `p` over `U` when it is open and `p|V` is a homeomorphism onto `U`. -/
def IsSheet (p : E → X) (U : Set X) (V : Set E) : Prop :=
  IsOpen V ∧ ∃ h : V ≃ₜ U, ∀ v : V, (h v : X) = p v

namespace IsSheet

theorem mapsTo {p : E → X} {U : Set X} {V : Set E} (hV : IsSheet p U V) :
    Set.MapsTo p V U := by
  rcases hV.2 with ⟨e, he⟩
  intro x hx
  rw [← he ⟨x, hx⟩]
  exact (e ⟨x, hx⟩).property

/-- The chosen homeomorphism supplied by a sheet witness. -/
noncomputable def homeomorph {p : E → X} {U : Set X} {V : Set E}
    (hV : IsSheet p U V) : V ≃ₜ U :=
  hV.2.choose

theorem isOpen {p : E → X} {U : Set X} {V : Set E} (hV : IsSheet p U V) : IsOpen V :=
  hV.1

end IsSheet

/-- The number of sheets at a point, defined as the cardinality of its fiber. -/
def coveringSheetNumber (p : E → X) (x : X) : Cardinal :=
  Cardinal.mk (p ⁻¹' {x})

/-- The number of sheets of a covering map is locally constant on the base. -/
theorem coveringSheetNumber_isLocallyConstant {p : E → X}
    (cov : CoveringMap p) :
    IsLocallyConstant (coveringSheetNumber p) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  rcases cov x with ⟨_, U, hxU, hU, _, H, hH⟩
  refine ⟨U, hU, hxU, ?_⟩
  intro y hy
  let liftToU (z : p ⁻¹' {y}) : p ⁻¹' U :=
    ⟨z.1, by
      change p z.1 ∈ U
      rw [show p z.1 = y from z.2]
      exact hy⟩
  let e : (p ⁻¹' {y}) ≃ (p ⁻¹' {x}) :=
    { toFun := fun z => (H (liftToU z)).2
      invFun := fun i =>
        ⟨(H.symm (⟨y, hy⟩, i)).1, by
          change p (H.symm (⟨y, hy⟩, i)).1 = y
          exact (hH _).symm.trans
            (congrArg (fun z : U × (p ⁻¹' {x}) => (z.1 : X))
              (H.apply_symm_apply (⟨y, hy⟩, i)))⟩
      left_inv := by
        intro z
        apply Subtype.ext
        have hfirst : (H (liftToU z)).1 = ⟨y, hy⟩ := by
          apply Subtype.ext
          exact (hH _).trans z.2
        have hpair :
            (⟨y, hy⟩, (H (liftToU z)).2) = H (liftToU z) := by
          apply Prod.ext
          · exact hfirst.symm
          · rfl
        change (H.symm (⟨y, hy⟩, (H (liftToU z)).2)).1 = z.1
        rw [hpair, H.symm_apply_apply]
      right_inv := by
        intro i
        change (H (H.symm (⟨y, hy⟩, i))).2 = i
        rw [H.apply_symm_apply] }
  exact Cardinal.mk_congr e

/-- On a preconnected base, a covering map has the same number of sheets over
every point. -/
theorem coveringSheetNumber_eq [PreconnectedSpace X] {p : E → X}
    (cov : CoveringMap p) (x y : X) :
    coveringSheetNumber p x = coveringSheetNumber p y :=
  (coveringSheetNumber_isLocallyConstant cov).apply_eq_of_preconnectedSpace x y

end
end HatcherLib

import HatcherLib.Ch0.MappingCylinder
import HatcherLib.Ch0.HomotopyExtensionRel
import HatcherLib.Ch0.MappingCylinderHEP

/-!
# Chapter 0 — Homotopy equivalences and the mapping cylinder (Hatcher Cor. 0.21)

Hatcher's Corollary 0.21: *a map `f : X → Y` is a homotopy equivalence iff `X` is a
deformation retract of the mapping cylinder `M_f`*. Its proof factors `f = r ∘ i`
through the mapping cylinder, where `i : X → M_f` is the inclusion of the domain and
`r : M_f → Y` is the canonical (homotopy-equivalence) retraction, and observes that
`f` is a homotopy equivalence iff `i` is, then applies Corollary 0.20
(`hep_inclusion_deformation_retract`) to the pair `(M_f, X)`, whose homotopy
extension property is `hasHEPMap_mcylInclX`.

This file proves:

* `IsHmtpyEquiv` — the unbundled predicate "`φ` is a homotopy equivalence";
* `isHmtpyEquiv_mcylInclX_iff` — **the heart of Cor. 0.21**: `f` is a homotopy
  equivalence iff the inclusion `i : X → M_f` is (unconditional, no HEP needed);
* `isHmtpyEquiv_of_mcylDeformationRetract` — the *if* half of Cor. 0.21 (a
  deformation retract of `M_f` onto `X` makes `f` a homotopy equivalence);
* `isHmtpyEquiv_iff_isMcylDeformationRetract` — **Hatcher's Corollary 0.21**:
  `f` is a homotopy equivalence iff `X` is a deformation retract of `M_f`;
* `homotopyEquiv_iff_common_deformationRetract` — the closing remark of Cor. 0.21:
  two spaces are homotopy equivalent iff both are deformation retracts of a common
  space (namely the mapping cylinder).
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- The canonical retraction `r : M_f → Y` is a homotopy equivalence. -/
theorem mcylProj_isHmtpyEquiv (f : C(X, Y)) : IsHmtpyEquiv (mcylProj f) :=
  ⟨mcylInclY f, (mcylHomotopyEquiv f).left_inv, (mcylHomotopyEquiv f).right_inv⟩

/-- `r ∘ i = f`: the retraction of `M_f` onto `Y` composed with the inclusion of `X`
recovers `f`. -/
theorem mcylProj_comp_inclX (f : C(X, Y)) : (mcylProj f).comp (mcylInclX f) = f := by
  ext x; exact mcylProj_inclX f x

/-- **Heart of Hatcher's Corollary 0.21.** A map `f : X → Y` is a homotopy
equivalence iff the inclusion `i : X → M_f` of the domain into the mapping cylinder
is a homotopy equivalence. Indeed `f = r ∘ i` with `r : M_f → Y` a homotopy
equivalence, so composing (resp. cancelling) `r` transfers the property between `f`
and `i`. No homotopy extension property is needed for this equivalence. -/
theorem isHmtpyEquiv_mcylInclX_iff (f : C(X, Y)) :
    IsHmtpyEquiv (mcylInclX f) ↔ IsHmtpyEquiv f := by
  constructor
  · intro hi
    have h := hi.comp (mcylProj_isHmtpyEquiv f)
    rwa [mcylProj_comp_inclX] at h
  · intro hf
    have hj : IsHmtpyEquiv (mcylInclY f) :=
      ⟨mcylProj f, (mcylHomotopyEquiv f).right_inv, (mcylHomotopyEquiv f).left_inv⟩
    have hjf : IsHmtpyEquiv ((mcylInclY f).comp f) := hf.comp hj
    have hi_htpc : (mcylInclX f).Homotopic ((mcylInclY f).comp f) := by
      have step : (mcylInclX f).Homotopic
          (((mcylInclY f).comp (mcylProj f)).comp (mcylInclX f)) := by
        have h := ContinuousMap.Homotopic.comp
          (mcylHomotopyEquiv f).left_inv.symm
          (ContinuousMap.Homotopic.refl (mcylInclX f))
        rwa [ContinuousMap.id_comp] at h
      rwa [ContinuousMap.comp_assoc, mcylProj_comp_inclX] at step
    exact IsHmtpyEquiv.of_homotopic hi_htpc.symm hjf

/-- `X` is a **deformation retract of the mapping cylinder** `M_f` (map form):
a retraction `ρ : M_f → X` with `ρ ∘ i = 𝟙_X` and `i ∘ ρ ≃ 𝟙_{M_f}` rel the copy
of `X` inside `M_f`. -/
def IsMcylDeformationRetract (f : C(X, Y)) : Prop :=
  IsDeformationRetractIncl (mcylInclX f)

/-- **The "if" half of Hatcher's Corollary 0.21.** If `X` is a deformation retract of
`M_f`, then `f` is a homotopy equivalence. The deformation retraction makes the
inclusion `i : X → M_f` a homotopy equivalence, and then `f` is one by
`isHmtpyEquiv_mcylInclX_iff`. -/
theorem isHmtpyEquiv_of_mcylDeformationRetract (f : C(X, Y))
    (h : IsMcylDeformationRetract f) : IsHmtpyEquiv f := by
  obtain ⟨ρ, hρ, ⟨H⟩⟩ := h
  have hi : IsHmtpyEquiv (mcylInclX f) := by
    refine ⟨ρ, ?_, ⟨H.toHomotopy⟩⟩
    rw [hρ]
  exact (isHmtpyEquiv_mcylInclX_iff f).mp hi

/-- **The "only if" half of Hatcher's Corollary 0.21**, taking the homotopy extension
property of `(M_f, X)` as a hypothesis. If `f` is a homotopy equivalence then so is
`i : X → M_f` (`isHmtpyEquiv_mcylInclX_iff`); applying Corollary 0.20
(`hep_inclusion_deformation_retract`) to the pair `(M_f, X)` upgrades the homotopy
inverse of `i` to a deformation retraction of `M_f` onto `X`. -/
theorem mcylDeformationRetract_of_isHmtpyEquiv (f : C(X, Y))
    (hHEP : HasHEPMap (mcylInclX f)) (hf : IsHmtpyEquiv f) :
    IsMcylDeformationRetract f := by
  have hi : IsHmtpyEquiv (mcylInclX f) := (isHmtpyEquiv_mcylInclX_iff f).mpr hf
  obtain ⟨g, hgi, hig⟩ := hi
  obtain ⟨ρ, hρA, hrel⟩ := hep_inclusion_deformation_retract (mcylInclX f) hHEP g hgi hig
  exact ⟨ρ, ContinuousMap.ext hρA, hrel⟩

/-- **Hatcher's Corollary 0.21** (conditional form). A map `f : X → Y` is a homotopy
equivalence iff `X` is a deformation retract of the mapping cylinder `M_f`, given the
homotopy extension property of `(M_f, X)` (which enters only in the forward
direction). -/
theorem homotopy_equiv_iff_mcylDeformationRetract (f : C(X, Y))
    (hHEP : HasHEPMap (mcylInclX f)) :
    IsHmtpyEquiv f ↔ IsMcylDeformationRetract f :=
  ⟨mcylDeformationRetract_of_isHmtpyEquiv f hHEP,
    isHmtpyEquiv_of_mcylDeformationRetract f⟩

/-- **Hatcher's Corollary 0.21.** A map `f : X → Y` is a homotopy equivalence iff
`X` is a deformation retract of the mapping cylinder `M_f`. The homotopy extension
property of `(M_f, X)` — Hatcher's mapping-cylinder neighborhood `X × [0, 1/2]` —
is supplied by `hasHEPMap_mcylInclX`. -/
theorem isHmtpyEquiv_iff_isMcylDeformationRetract (f : C(X, Y)) :
    IsHmtpyEquiv f ↔ IsMcylDeformationRetract f :=
  homotopy_equiv_iff_mcylDeformationRetract f (hasHEPMap_mcylInclX f)

/-- `Y` is a deformation retract of the mapping cylinder `M_f` (map form): the
sliding deformation retraction `mcylDeformationRetract`, packaged as
`IsDeformationRetractIncl`. -/
theorem isDeformationRetractIncl_mcylInclY (f : C(X, Y)) :
    IsDeformationRetractIncl (mcylInclY f) :=
  ⟨mcylProj f, mcylProj_comp_inclY f, ⟨(mcylDeformationRetract f).symm⟩⟩

/-- **The closing remark of Hatcher's Corollary 0.21.** Two spaces `X` and `Y` are
homotopy equivalent iff there is a third space containing both as deformation
retracts. Forward: the mapping cylinder of a homotopy equivalence deformation
retracts onto its domain (Cor. 0.21) and onto its codomain (the sliding
retraction). Backward: each deformation-retract inclusion is a homotopy
equivalence; compose one with the homotopy inverse of the other. -/
theorem homotopyEquiv_iff_common_deformationRetract
    (X Y : Type u) [TopologicalSpace X] [TopologicalSpace Y] :
    Nonempty (ContinuousMap.HomotopyEquiv X Y) ↔
      ∃ (Z : Type u) (_ : TopologicalSpace Z) (iX : C(X, Z)) (iY : C(Y, Z)),
        IsDeformationRetractIncl iX ∧ IsDeformationRetractIncl iY := by
  constructor
  · rintro ⟨e⟩
    have hf : IsHmtpyEquiv e.toFun := ⟨e.invFun, e.left_inv, e.right_inv⟩
    exact ⟨MappingCylinder e.toFun, inferInstance,
      mcylInclX e.toFun, mcylInclY e.toFun,
      (isHmtpyEquiv_iff_isMcylDeformationRetract e.toFun).mp hf,
      isDeformationRetractIncl_mcylInclY e.toFun⟩
  · rintro ⟨Z, _, iX, iY, hX, hY⟩
    obtain ⟨ρX, hρX1, hρX2⟩ := hX.isHmtpyEquiv
    obtain ⟨ρY, hρY1, hρY2⟩ := hY.isHmtpyEquiv
    exact ⟨ContinuousMap.HomotopyEquiv.trans
      { toFun := iX, invFun := ρX, left_inv := hρX1, right_inv := hρX2 }
      ({ toFun := iY, invFun := ρY, left_inv := hρY1, right_inv := hρY2 } :
          ContinuousMap.HomotopyEquiv Y Z).symm⟩

end HatcherLib

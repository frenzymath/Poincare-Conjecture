import HatcherLib.Ch0.MappingCylinder
import HatcherLib.Ch0.HomotopyExtensionRel

/-!
# Chapter 0 — Homotopy equivalences and the mapping cylinder (Hatcher Cor. 0.21)

Hatcher's Corollary 0.21: *a map `f : X → Y` is a homotopy equivalence iff `X` is a
deformation retract of the mapping cylinder `M_f`*. Its proof factors `f = r ∘ i`
through the mapping cylinder, where `i : X → M_f` is the inclusion of the domain and
`r : M_f → Y` is the canonical (homotopy-equivalence) retraction, and observes that
`f` is a homotopy equivalence iff `i` is, then applies Corollary 0.20
(`hep_inclusion_deformation_retract`) to the pair `(M_f, X)`.

This file proves:

* `IsHmtpyEquiv` — the unbundled predicate "`φ` is a homotopy equivalence";
* `isHmtpyEquiv_mcylInclX_iff` — **the heart of Cor. 0.21**: `f` is a homotopy
  equivalence iff the inclusion `i : X → M_f` is (unconditional, no HEP needed);
* `isHmtpyEquiv_of_mcylDeformationRetract` — the *if* half of Cor. 0.21 (a
  deformation retract of `M_f` onto `X` makes `f` a homotopy equivalence);
* `homotopy_equiv_iff_mcylDeformationRetract` — the full biconditional of Cor. 0.21,
  taking the homotopy extension property of `(M_f, X)` as an explicit hypothesis.

The one input still to be supplied to make Cor. 0.21 unconditional is
`HasHEPMap (mcylInclX f)` — the HEP of `(M_f, X)`, which Hatcher gets from the
mapping-cylinder neighborhood `X × [0, 1/2]` (blueprint
`ex:mapping-cylinder-neighborhood-hep`). See the note at the end of the file.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- A map `φ` is a **homotopy equivalence** when it has a two-sided homotopy inverse
(Hatcher's "`f` is a homotopy equivalence"). This is the unbundled form of
`ContinuousMap.HomotopyEquiv`. -/
def IsHmtpyEquiv {A B : Type u} [TopologicalSpace A] [TopologicalSpace B] (φ : C(A, B)) : Prop :=
  ∃ ψ : C(B, A), (ψ.comp φ).Homotopic (ContinuousMap.id A) ∧
    (φ.comp ψ).Homotopic (ContinuousMap.id B)

namespace IsHmtpyEquiv

variable {A B C : Type u} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- The composite of two homotopy equivalences is a homotopy equivalence. -/
theorem comp {φ : C(A, B)} {χ : C(B, C)} (hφ : IsHmtpyEquiv φ) (hχ : IsHmtpyEquiv χ) :
    IsHmtpyEquiv (χ.comp φ) := by
  obtain ⟨ψ, hψ1, hψ2⟩ := hφ
  obtain ⟨ω, hω1, hω2⟩ := hχ
  let E : ContinuousMap.HomotopyEquiv A C :=
    ({ toFun := φ, invFun := ψ, left_inv := hψ1, right_inv := hψ2 } :
        ContinuousMap.HomotopyEquiv A B).trans
      { toFun := χ, invFun := ω, left_inv := hω1, right_inv := hω2 }
  exact ⟨ψ.comp ω, E.left_inv, E.right_inv⟩

/-- A map homotopic to a homotopy equivalence is a homotopy equivalence. -/
theorem of_homotopic {φ φ' : C(A, B)} (h : φ.Homotopic φ') (hφ : IsHmtpyEquiv φ) :
    IsHmtpyEquiv φ' := by
  obtain ⟨ψ, hψ1, hψ2⟩ := hφ
  refine ⟨ψ, ?_, ?_⟩
  · exact (ContinuousMap.Homotopic.comp (ContinuousMap.Homotopic.refl ψ) h.symm).trans hψ1
  · exact (ContinuousMap.Homotopic.comp h.symm (ContinuousMap.Homotopic.refl ψ)).trans hψ2

end IsHmtpyEquiv

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
  ∃ ρ : C(MappingCylinder f, X), ρ.comp (mcylInclX f) = ContinuousMap.id X ∧
    Nonempty (((mcylInclX f).comp ρ).HomotopyRel (ContinuousMap.id (MappingCylinder f))
      (Set.range (mcylInclX f)))

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

/-- **Hatcher's Corollary 0.21** (conditional on the HEP of `(M_f, X)`). A map
`f : X → Y` is a homotopy equivalence iff `X` is a deformation retract of the mapping
cylinder `M_f`. The homotopy extension property of `(M_f, X)` — Hatcher's mapping
cylinder neighborhood `X × [0, 1/2]`, blueprint `ex:mapping-cylinder-neighborhood-hep`
— enters only in the forward direction. -/
theorem homotopy_equiv_iff_mcylDeformationRetract (f : C(X, Y))
    (hHEP : HasHEPMap (mcylInclX f)) :
    IsHmtpyEquiv f ↔ IsMcylDeformationRetract f :=
  ⟨mcylDeformationRetract_of_isHmtpyEquiv f hHEP,
    isHmtpyEquiv_of_mcylDeformationRetract f⟩

end HatcherLib

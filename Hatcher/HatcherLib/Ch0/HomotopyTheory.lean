import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible

/-!
# Chapter 0 — Homotopy and homotopy type

This file records the correspondence between the geometric notions of Hatcher's
Chapter 0, *Some Underlying Geometric Notions* (§ "Homotopy and Homotopy Type"),
and mathlib's `ContinuousMap` homotopy library. Most of Hatcher's definitions are
already present in mathlib, so we expose them as thin aliases (pure reuse — no
re-formalization) so that the blueprint's `\lean{…}` markers resolve to
Hatcher-namespaced names.

Two notions that Hatcher constructs by hand and mathlib does not package are
added here directly:

* `HatcherLib.IsRetraction` — a retraction `r`, characterised by `r ∘ r = r`;
* `HatcherLib.DeformationRetract` — a deformation retraction of `X` onto a
  subspace `A`,

together with the basic fact `DeformationRetract.homotopyEquiv`: a deformation
retraction of `X` onto `A` exhibits `A` and `X` as homotopy equivalent (Hatcher's
`r i = 𝟙`, `i r ≃ 𝟙`).
-/

namespace HatcherLib

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A **homotopy** between `f₀, f₁ : C(X, Y)` (Hatcher, Def. of a homotopy): the
associated map `F : X × I → Y` is continuous. This is mathlib's
`ContinuousMap.Homotopy`. -/
abbrev Homotopy (f₀ f₁ : C(X, Y)) := ContinuousMap.Homotopy f₀ f₁

/-- Two maps `f₀, f₁ : C(X, Y)` are **homotopic** when a homotopy connects them,
written `f₀ ≃ f₁`. This is mathlib's `ContinuousMap.Homotopic`. -/
abbrev Homotopic (f₀ f₁ : C(X, Y)) : Prop := ContinuousMap.Homotopic f₀ f₁

/-- A **homotopy rel `S`**: a homotopy `fₜ : X → Y` whose restriction to the
subspace `S ⊆ X` is independent of `t`. This is mathlib's
`ContinuousMap.HomotopyRel`. -/
abbrev HomotopyRel (f₀ f₁ : C(X, Y)) (S : Set X) := ContinuousMap.HomotopyRel f₀ f₁ S

/-- A **homotopy equivalence** `X ≃ₕ Y`: a map `f : X → Y` admitting `g : Y → X`
with `f g ≃ 𝟙` and `g f ≃ 𝟙`. `X` and `Y` then have the same **homotopy type**.
This is mathlib's `ContinuousMap.HomotopyEquiv`. -/
abbrev HomotopyEquiv (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] :=
  ContinuousMap.HomotopyEquiv X Y

/-- A map is **nullhomotopic** when it is homotopic to a constant map. This is
mathlib's `ContinuousMap.Nullhomotopic`. -/
abbrev Nullhomotopic (f : C(X, Y)) : Prop := ContinuousMap.Nullhomotopic f

/-- A space is **contractible** when it has the homotopy type of a point,
equivalently its identity map is nullhomotopic. This is mathlib's
`ContractibleSpace`. -/
abbrev IsContractible (X : Type u) [TopologicalSpace X] : Prop := ContractibleSpace X

/-- A **retraction** of `X` onto its image is a self-map `r : X → X` with
`r ∘ r = r`; the equation says exactly that `r` is the identity on its image
(Hatcher, Def. of a retraction). -/
def IsRetraction (r : C(X, X)) : Prop := ∀ x, r (r x) = r x

/-- A **deformation retraction** of `X` onto a subspace `A` (Hatcher, Def. of a
deformation retraction): a homotopy `fₜ : X → X` rel `A` from the identity `f₀ = 𝟙`
to a retraction `f₁ = r` of `X` onto `A`, i.e. with `f₁(X) ⊆ A` and `f₁|_A = 𝟙`. -/
structure DeformationRetract (A : Set X) where
  /-- the terminal retraction `r = f₁`. -/
  retraction : C(X, X)
  /-- `f₁(X) ⊆ A`. -/
  mapsInto : ∀ x, retraction x ∈ A
  /-- `f₁|_A = 𝟙`: `r` is the identity on `A`. -/
  fixes : ∀ x ∈ A, retraction x = x
  /-- the homotopy `𝟙 ≃ r`, rel `A`. -/
  homotopy : ContinuousMap.HomotopyRel (ContinuousMap.id X) retraction A

namespace DeformationRetract

variable {A : Set X}

/-- The retraction of a deformation retraction is idempotent, i.e. a retraction
in the sense of `IsRetraction`. -/
theorem isRetraction (d : DeformationRetract A) : IsRetraction d.retraction :=
  fun x => d.fixes (d.retraction x) (d.mapsInto x)

/-- The inclusion `A ↪ X` of the retract. -/
def incl (A : Set X) : C(↥A, X) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The retraction, corestricted to a map `X → A`. -/
def coretr (d : DeformationRetract A) : C(X, ↥A) :=
  ⟨fun x => ⟨d.retraction x, d.mapsInto x⟩, d.retraction.continuous.subtype_mk d.mapsInto⟩

theorem coretr_comp_incl (d : DeformationRetract A) :
    (coretr d).comp (incl A) = ContinuousMap.id ↥A := by
  ext a; exact d.fixes a.1 a.2

theorem incl_comp_coretr (d : DeformationRetract A) :
    (incl A).comp (coretr d) = d.retraction := by
  ext x; rfl

/-- **A deformation retraction of `X` onto `A` is a homotopy equivalence**
between `A` and `X`. The inclusion `i : A ↪ X` and the corestricted retraction
`r : X → A` satisfy `r i = 𝟙` on the nose and `i r = r ≃ 𝟙` via the deformation
homotopy. -/
def homotopyEquiv (d : DeformationRetract A) : ContinuousMap.HomotopyEquiv ↥A X where
  toFun := incl A
  invFun := coretr d
  left_inv := by
    rw [coretr_comp_incl d]
  right_inv := by
    rw [incl_comp_coretr d]
    exact ContinuousMap.Homotopic.symm
      (⟨d.homotopy.toHomotopy⟩ : ContinuousMap.Homotopic (ContinuousMap.id X) d.retraction)

end DeformationRetract

end HatcherLib

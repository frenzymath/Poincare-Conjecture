import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Constructions.SumProd
import HatcherLib.Ch0.HomotopyExtension

/-!
# Chapter 0 — Attaching one space to another

Hatcher's Chapter 0 § "Two Criteria for Homotopy Equivalence" introduces the
**attaching space** (adjunction space) `X₀ ⊔_f X₁`: given a subspace `A ⊆ X₁` and
an attaching map `f : A → X₀`, the quotient of the disjoint union `X₀ ⊔ X₁`
identifying each `a ∈ A` with its image `f a ∈ X₀`. mathlib has no topological
adjunction space (only category-theoretic pushouts in `TopCat`), so we build it
here as project-local infrastructure, mirroring `HatcherLib.MappingCylinder`.

Main constructions:

* `HatcherLib.AttachingSpace A f` — the attaching space `X₀ ⊔_f X₁`, the quotient
  of `X₀ ⊕ X₁` by the identification `a ∼ f a` for `a ∈ A`;
* `attachInclBase`, `attachInclTop` — the canonical maps `X₀ → X₀ ⊔_f X₁`
  (injective, `attachInclBase_injective`) and `X₁ → X₀ ⊔_f X₁`;
* `attachIncl_glue` — the defining identification `[a] = [f a]` for `a ∈ A`;
* `attachDesc` — descent: maps `g₀ : X₀ → Z` and `g₁ : X₁ → Z` with
  `g₁|_A = g₀ ∘ f` combine to a map `X₀ ⊔_f X₁ → Z`.
-/

namespace HatcherLib

open ContinuousMap

universe u

variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]

/-- The normalisation function on `X₀ ⊕ X₁` sending each point `a` of the subspace
`A ⊆ X₁` to its image `f a ∈ X₀` and fixing everything else. The attaching-space
identification is exactly its kernel. -/
noncomputable def attachNorm (A : Set X₁) (f : C(↥A, X₀)) (p : X₀ ⊕ X₁) : X₀ ⊕ X₁ :=
  open Classical in
  p.elim Sum.inl fun x₁ => if h : x₁ ∈ A then Sum.inl (f ⟨x₁, h⟩) else Sum.inr x₁

@[simp] theorem attachNorm_inl (A : Set X₁) (f : C(↥A, X₀)) (x₀ : X₀) :
    attachNorm A f (Sum.inl x₀) = Sum.inl x₀ := rfl

theorem attachNorm_inr_of_mem (A : Set X₁) (f : C(↥A, X₀)) {x₁ : X₁} (h : x₁ ∈ A) :
    attachNorm A f (Sum.inr x₁) = Sum.inl (f ⟨x₁, h⟩) := by
  simp only [attachNorm, Sum.elim_inr, dif_pos h]

theorem attachNorm_inr_of_not_mem (A : Set X₁) (f : C(↥A, X₀)) {x₁ : X₁} (h : x₁ ∉ A) :
    attachNorm A f (Sum.inr x₁) = Sum.inr x₁ := by
  simp only [attachNorm, Sum.elim_inr, dif_neg h]

/-- The setoid identifying `a ∈ A` with `f a ∈ X₀`: two points are equivalent when
`attachNorm` sends them to the same point. (In particular two points `a, a' ∈ A` are
identified iff `f a = f a'`, as they should be in the quotient.) -/
noncomputable def attachSetoid (A : Set X₁) (f : C(↥A, X₀)) : Setoid (X₀ ⊕ X₁) :=
  Setoid.ker (attachNorm A f)

/-- The **attaching space** (adjunction space) `X₀ ⊔_f X₁` of an attaching map
`f : A → X₀` defined on a subspace `A ⊆ X₁`: the quotient of `X₀ ⊕ X₁` by the
identification `a ∼ f a` for `a ∈ A`, carrying the quotient topology (Hatcher,
"attaching one space to another"). -/
abbrev AttachingSpace (A : Set X₁) (f : C(↥A, X₀)) : Type u := Quotient (attachSetoid A f)

/-- The quotient map `X₀ ⊕ X₁ → X₀ ⊔_f X₁`. -/
noncomputable def attachMk (A : Set X₁) (f : C(↥A, X₀)) : C(X₀ ⊕ X₁, AttachingSpace A f) :=
  ⟨Quotient.mk (attachSetoid A f), continuous_quotient_mk'⟩

theorem attachMk_eq {A : Set X₁} {f : C(↥A, X₀)} {a b : X₀ ⊕ X₁}
    (h : attachNorm A f a = attachNorm A f b) : attachMk A f a = attachMk A f b :=
  Quotient.sound h

/-- The canonical map `X₀ → X₀ ⊔_f X₁`. -/
noncomputable def attachInclBase (A : Set X₁) (f : C(↥A, X₀)) : C(X₀, AttachingSpace A f) :=
  (attachMk A f).comp ⟨Sum.inl, continuous_inl⟩

/-- The canonical map `X₁ → X₀ ⊔_f X₁`. -/
noncomputable def attachInclTop (A : Set X₁) (f : C(↥A, X₀)) : C(X₁, AttachingSpace A f) :=
  (attachMk A f).comp ⟨Sum.inr, continuous_inr⟩

@[simp] theorem attachInclBase_apply (A : Set X₁) (f : C(↥A, X₀)) (x₀ : X₀) :
    attachInclBase A f x₀ = attachMk A f (Sum.inl x₀) := rfl

@[simp] theorem attachInclTop_apply (A : Set X₁) (f : C(↥A, X₀)) (x₁ : X₁) :
    attachInclTop A f x₁ = attachMk A f (Sum.inr x₁) := rfl

/-- The defining identification of the attaching space: for `a ∈ A`, the point
`a ∈ X₁` is glued to `f a ∈ X₀`. -/
theorem attachIncl_glue (A : Set X₁) (f : C(↥A, X₀)) (a : ↥A) :
    attachInclTop A f (a : X₁) = attachInclBase A f (f a) := by
  refine attachMk_eq ?_
  show attachNorm A f (Sum.inr (a : X₁)) = attachNorm A f (Sum.inl (f a))
  rw [attachNorm_inr_of_mem A f a.2, attachNorm_inl]

/-- The canonical map `X₀ → X₀ ⊔_f X₁` is injective: `X₀` sits inside the attaching
space. -/
theorem attachInclBase_injective (A : Set X₁) (f : C(↥A, X₀)) :
    Function.Injective (attachInclBase A f) := by
  intro x y hxy
  have h : attachNorm A f (Sum.inl x) = attachNorm A f (Sum.inl y) :=
    Quotient.exact hxy
  rwa [attachNorm_inl, attachNorm_inl, Sum.inl.injEq] at h

/-- Points of `X₁ \ A` are not identified with points of `X₀`. -/
theorem attachInclTop_ne_base (A : Set X₁) (f : C(↥A, X₀)) {x₁ : X₁} (h : x₁ ∉ A)
    (x₀ : X₀) : attachInclTop A f x₁ ≠ attachInclBase A f x₀ := by
  intro hcontra
  have hk : attachNorm A f (Sum.inr x₁) = attachNorm A f (Sum.inl x₀) :=
    Quotient.exact hcontra
  rw [attachNorm_inr_of_not_mem A f h, attachNorm_inl] at hk
  exact Sum.inr_ne_inl hk

section Desc

variable {A : Set X₁} {f : C(↥A, X₀)} {Z : Type u} [TopologicalSpace Z]

/-- The underlying elimination map of `attachDesc`. -/
def attachDescFun (g₀ : C(X₀, Z)) (g₁ : C(X₁, Z)) : C(X₀ ⊕ X₁, Z) :=
  ⟨Sum.elim g₀ g₁, (map_continuous g₀).sumElim (map_continuous g₁)⟩

theorem attachDescFun_norm (g₀ : C(X₀, Z)) (g₁ : C(X₁, Z))
    (hcompat : ∀ a : ↥A, g₁ (a : X₁) = g₀ (f a)) (p : X₀ ⊕ X₁) :
    attachDescFun g₀ g₁ (attachNorm A f p) = attachDescFun g₀ g₁ p := by
  cases p with
  | inl x₀ => rfl
  | inr x₁ =>
    by_cases h : x₁ ∈ A
    · rw [attachNorm_inr_of_mem A f h]
      exact (hcompat ⟨x₁, h⟩).symm
    · rw [attachNorm_inr_of_not_mem A f h]

/-- **Descent for attaching spaces.** Maps `g₀ : X₀ → Z` and `g₁ : X₁ → Z` with
`g₁ a = g₀ (f a)` for all `a ∈ A` combine to a map `X₀ ⊔_f X₁ → Z`. -/
noncomputable def attachDesc (g₀ : C(X₀, Z)) (g₁ : C(X₁, Z))
    (hcompat : ∀ a : ↥A, g₁ (a : X₁) = g₀ (f a)) : C(AttachingSpace A f, Z) where
  toFun := Quotient.lift (attachDescFun g₀ g₁) fun a b hab => by
    rw [← attachDescFun_norm g₀ g₁ hcompat a, ← attachDescFun_norm g₀ g₁ hcompat b]
    exact congrArg _ hab
  continuous_toFun := (map_continuous (attachDescFun g₀ g₁)).quotient_lift _

@[simp] theorem attachDesc_inclBase (g₀ : C(X₀, Z)) (g₁ : C(X₁, Z))
    (hcompat : ∀ a : ↥A, g₁ (a : X₁) = g₀ (f a)) (x₀ : X₀) :
    attachDesc g₀ g₁ hcompat (attachInclBase A f x₀) = g₀ x₀ := rfl

@[simp] theorem attachDesc_inclTop (g₀ : C(X₀, Z)) (g₁ : C(X₁, Z))
    (hcompat : ∀ a : ↥A, g₁ (a : X₁) = g₀ (f a)) (x₁ : X₁) :
    attachDesc g₀ g₁ hcompat (attachInclTop A f x₁) = g₁ x₁ := rfl

/-- Two maps out of an attaching space agreeing on both canonical inclusions are
equal. -/
theorem attach_hom_ext {φ ψ : C(AttachingSpace A f, Z)}
    (h₀ : ∀ x₀, φ (attachInclBase A f x₀) = ψ (attachInclBase A f x₀))
    (h₁ : ∀ x₁, φ (attachInclTop A f x₁) = ψ (attachInclTop A f x₁)) : φ = ψ := by
  ext z
  induction z using Quotient.ind with
  | _ p =>
    cases p with
    | inl x₀ => exact h₀ x₀
    | inr x₁ => exact h₁ x₁

end Desc

end HatcherLib

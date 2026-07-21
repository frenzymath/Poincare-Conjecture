import Mathlib.Topology.Homotopy.Equiv
import HatcherLib.Ch0.AttachingSpace
import HatcherLib.Ch0.HomotopyExtensionRel

/-!
# Chapter 0 — Homotopic attaching maps give homotopy equivalent spaces (Hatcher Prop. 0.18)

Hatcher's Proposition 0.18: if `(X₁, A)` is a CW pair and the attaching maps
`f, g : A → X₀` are homotopic, then `X₀ ⊔_f X₁ ≃ X₀ ⊔_g X₁ rel X₀`. Following
Hatcher's remark (and his exercise), we prove it for any pair `(X₁, A)` with `A`
closed satisfying the **homotopy extension property** — CW pairs are the special
case once `prop:cw-pairs-have-hep` is formalized.

The proof is Hatcher's: given a homotopy `F : A × I → X₀` from `f` to `g`, form the
**attaching cylinder** `W = X₀ ⊔_F (X₁ × I)`. The deformation retraction of
`X₁ × I` onto `X₁ × {0} ∪ A × I` (`HasHEP.hepBase_deformationRetract`, from the
HEP) fixes `A × I` pointwise, hence descends to a deformation retraction of `W`
onto the image of `X₀ ⊔ (X₁ × {0})` — which receives a copy of `X₀ ⊔_f X₁`.
Symmetrically (flipping time), `W` deformation retracts onto a copy of
`X₀ ⊔_g X₁`. Two spaces that are deformation retracts (rel `X₀`) of a common
space are homotopy equivalent rel `X₀`.

Main results:

* `attachLevel` — the canonical map `X₀ ⊔_{F_{t₀}} X₁ → W` at level `t₀`;
* `attachLevel_isDeformationRetractIncl` — given a deformation retraction of
  `X₁ × I` onto `X₁ × {t₀} ∪ A × I`, the level-`t₀` map is a deformation-retract
  inclusion;
* `hepBaseTopDeformationRetract` — time-flip transport of the `hepBase`
  deformation retraction from level `0` to level `1`;
* `attachingSpace_homotopyEquiv_rel` — **Proposition 0.18** (HEP form).
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

variable {X₀ X₁ : Type u} [TopologicalSpace X₀] [TopologicalSpace X₁]

/-! ## Endpoint evaluation and the attaching cylinder -/

section Defs

variable {A : Set X₁}

/-- The attaching map at time `t₀` of a homotopy `F : A × I → X₀` of attaching
maps. -/
def attachEval (F : C(↥A × I, X₀)) (t₀ : I) : C(↥A, X₀) :=
  ⟨fun a => F (a, t₀), (map_continuous F).comp (continuous_id.prodMk continuous_const)⟩

@[simp] theorem attachEval_apply (F : C(↥A × I, X₀)) (t₀ : I) (a : ↥A) :
    attachEval F t₀ a = F (a, t₀) := rfl

/-- The thickened subspace `A × I ⊆ X₁ × I`. -/
def attachCylSet (A : Set X₁) : Set (X₁ × I) := {p | p.1 ∈ A}

omit [TopologicalSpace X₁] in
theorem mem_attachCylSet {A : Set X₁} {p : X₁ × I} : p ∈ attachCylSet A ↔ p.1 ∈ A :=
  Iff.rfl

/-- A homotopy `F : A × I → X₀` of attaching maps, viewed as a single attaching map
on the thickened subspace `A × I ⊆ X₁ × I`. -/
def attachCylMap (F : C(↥A × I, X₀)) : C(↥(attachCylSet A), X₀) :=
  ⟨fun q => F (⟨q.1.1, q.2⟩, q.1.2),
    (map_continuous F).comp
      (((continuous_fst.comp continuous_subtype_val).subtype_mk fun q => q.2).prodMk
        (continuous_snd.comp continuous_subtype_val))⟩

@[simp] theorem attachCylMap_apply (F : C(↥A × I, X₀)) (q : ↥(attachCylSet A)) :
    attachCylMap F q = F (⟨q.1.1, q.2⟩, q.1.2) := rfl

/-- The **attaching cylinder** `W = X₀ ⊔_F (X₁ × I)` of a homotopy `F` of attaching
maps: the cylinder `X₁ × I` attached to `X₀` along `A × I` via `F`. -/
abbrev AttachingCylinder (F : C(↥A × I, X₀)) : Type u :=
  AttachingSpace (attachCylSet A) (attachCylMap F)

/-- The gluing relation of the attaching cylinder: for `a ∈ A`,
`[(a, t)] = [F (a, t)]` in `W`. -/
theorem attachCyl_glue (F : C(↥A × I, X₀)) {x₁ : X₁} (hx : x₁ ∈ A) (t : I) :
    attachInclTop (attachCylSet A) (attachCylMap F) (x₁, t)
      = attachInclBase (attachCylSet A) (attachCylMap F) (F (⟨x₁, hx⟩, t)) :=
  attachIncl_glue (attachCylSet A) (attachCylMap F) ⟨(x₁, t), hx⟩

/-- The canonical map `X₀ ⊔_{F_{t₀}} X₁ → W` including the attaching space of the
time-`t₀` attaching map at level `t₀` of the cylinder. It is the identity on `X₀`. -/
noncomputable def attachLevel (F : C(↥A × I, X₀)) (t₀ : I) :
    C(AttachingSpace A (attachEval F t₀), AttachingCylinder F) :=
  attachDesc (attachInclBase (attachCylSet A) (attachCylMap F))
    ((attachInclTop (attachCylSet A) (attachCylMap F)).comp
      ⟨fun x₁ => (x₁, t₀), continuous_id.prodMk continuous_const⟩)
    (fun a => attachCyl_glue F a.2 t₀)

@[simp] theorem attachLevel_base (F : C(↥A × I, X₀)) (t₀ : I) (x₀ : X₀) :
    attachLevel F t₀ (attachInclBase A (attachEval F t₀) x₀)
      = attachInclBase (attachCylSet A) (attachCylMap F) x₀ := rfl

@[simp] theorem attachLevel_top (F : C(↥A × I, X₀)) (t₀ : I) (x₁ : X₁) :
    attachLevel F t₀ (attachInclTop A (attachEval F t₀) x₁)
      = attachInclTop (attachCylSet A) (attachCylMap F) (x₁, t₀) := rfl

/-- The level-`t₀` slice-plus-collar `X₁ × {t₀} ∪ A × I` of the cylinder
`X₁ × I`. For `t₀ = 0` this is `hepBase A`. -/
def attachLevelSet (A : Set X₁) (t₀ : I) : Set (X₁ × I) := {p | p.1 ∈ A ∨ p.2 = t₀}

omit [TopologicalSpace X₁] in
theorem hepBase_eq_attachLevelSet (A : Set X₁) : hepBase A = attachLevelSet A 0 := rfl

end Defs

/-! ## Time-flip transport of the `hepBase` deformation retraction -/

/-- The time flip `(x, t) ↦ (x, 1 - t)` of a cylinder. -/
def cylFlip (X : Type u) [TopologicalSpace X] : C(X × I, X × I) :=
  ⟨fun p => (p.1, σ p.2), continuous_fst.prodMk (unitInterval.continuous_symm.comp
    continuous_snd)⟩

@[simp] theorem cylFlip_apply (X : Type u) [TopologicalSpace X] (p : X × I) :
    cylFlip X p = (p.1, σ p.2) := rfl

theorem cylFlip_flip (X : Type u) [TopologicalSpace X] (p : X × I) :
    cylFlip X (cylFlip X p) = p := Prod.ext rfl (unitInterval.symm_symm p.2)

/-- **Time-flip transport**: a deformation retraction of `X₁ × I` onto
`X₁ × {0} ∪ A × I` conjugates, along `(x, t) ↦ (x, 1 - t)`, to a deformation
retraction onto `X₁ × {1} ∪ A × I`. -/
noncomputable def hepBaseTopDeformationRetract {A : Set X₁}
    (d : DeformationRetract (hepBase A)) :
    DeformationRetract (attachLevelSet A 1) where
  retraction := (cylFlip X₁).comp (d.retraction.comp (cylFlip X₁))
  mapsInto := by
    intro p
    rcases d.mapsInto (cylFlip X₁ p) with h | h
    · exact Or.inl h
    · refine Or.inr ?_
      show σ (d.retraction (cylFlip X₁ p)).2 = 1
      rw [h]
      exact unitInterval.symm_zero
  fixes := by
    intro p hp
    have hmem : cylFlip X₁ p ∈ hepBase A := by
      rcases hp with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        show σ p.2 = 0
        rw [h]
        exact unitInterval.symm_one
    show cylFlip X₁ (d.retraction (cylFlip X₁ p)) = p
    rw [d.fixes _ hmem, cylFlip_flip]
  homotopy :=
    { toContinuousMap :=
        { toFun := fun q => cylFlip X₁ (d.homotopy (q.1, cylFlip X₁ q.2))
          continuous_toFun := (map_continuous (cylFlip X₁)).comp <|
            (map_continuous d.homotopy).comp <|
              continuous_fst.prodMk ((map_continuous (cylFlip X₁)).comp continuous_snd) }
      map_zero_left := by
        intro p
        show cylFlip X₁ (d.homotopy (0, cylFlip X₁ p)) = p
        exact (congrArg (cylFlip X₁) (d.homotopy.map_zero_left (cylFlip X₁ p))).trans
          (cylFlip_flip X₁ p)
      map_one_left := by
        intro p
        show cylFlip X₁ (d.homotopy (1, cylFlip X₁ p)) = _
        exact congrArg (cylFlip X₁) (d.homotopy.map_one_left (cylFlip X₁ p))
      prop' := by
        intro u p hp
        have hmem : cylFlip X₁ p ∈ hepBase A := by
          rcases hp with h | h
          · exact Or.inl h
          · refine Or.inr ?_
            show σ p.2 = 0
            rw [h]
            exact unitInterval.symm_one
        show cylFlip X₁ (d.homotopy (u, cylFlip X₁ p)) = p
        exact (congrArg (cylFlip X₁) (d.homotopy.eq_fst u hmem)).trans
          (cylFlip_flip X₁ p) }

/-! ## The level-`t₀` inclusion is a deformation-retract inclusion -/

/-- **Core of Proposition 0.18.** Suppose `A ⊆ X₁` is closed and `X₁ × I`
deformation retracts onto `X₁ × {t₀} ∪ A × I`. Then the level-`t₀` map
`X₀ ⊔_{F_{t₀}} X₁ → W = X₀ ⊔_F (X₁ × I)` is a deformation-retract inclusion: the
deformation retraction upstairs fixes `A × I` pointwise, hence descends to `W`,
and its end map collapses `W` onto the copy of `X₀ ⊔_{F_{t₀}} X₁`. -/
theorem attachLevel_isDeformationRetractIncl {A : Set X₁} (hA : IsClosed A)
    (F : C(↥A × I, X₀)) (t₀ : I) (d : DeformationRetract (attachLevelSet A t₀)) :
    IsDeformationRetractIncl (attachLevel F t₀) := by
  classical
  -- The collapse `γ` of the slice-plus-collar onto the attaching space of `F_{t₀}`:
  -- `(x₁, t) ↦ [F (x₁, t)]` for `x₁ ∈ A`, and `(x₁, t₀) ↦ [x₁]` otherwise.
  set γ : X₁ × I → AttachingSpace A (attachEval F t₀) :=
    hepGlue (attachInclTop A (attachEval F t₀))
      ((attachInclBase A (attachEval F t₀)).comp F)
  have hagree : ∀ a : ↥A, ((attachInclBase A (attachEval F t₀)).comp F) (a, t₀)
      = attachInclTop A (attachEval F t₀) (a : X₁) := fun a =>
    (attachIncl_glue A (attachEval F t₀) a).symm
  have hγ_cont : ContinuousOn γ (attachLevelSet A t₀) :=
    continuousOn_hepGlue_at hA _ _ t₀ hagree
  have hγ_mem : ∀ (q : X₁ × I) (hq : q.1 ∈ A),
      γ q = attachInclBase A (attachEval F t₀) (F (⟨q.1, hq⟩, q.2)) := fun q hq =>
    hepGlue_of_mem _ _ hq
  have hγ_not_mem : ∀ (q : X₁ × I), q.1 ∉ A →
      γ q = attachInclTop A (attachEval F t₀) q.1 := fun q hq =>
    hepGlue_of_not_mem _ _ hq
  -- The retraction `β : W → X₀ ⊔_{F_{t₀}} X₁`, collapsing along the deformation
  -- retraction upstairs.
  set β : C(AttachingCylinder F, AttachingSpace A (attachEval F t₀)) :=
    attachDesc (attachInclBase A (attachEval F t₀))
      ⟨fun p => γ (d.retraction p),
        hγ_cont.comp_continuous (map_continuous d.retraction) d.mapsInto⟩
      (fun q => by
        show γ (d.retraction (q : X₁ × I))
          = attachInclBase A (attachEval F t₀) (attachCylMap F q)
        rw [d.fixes (q : X₁ × I) (Or.inl q.2), hγ_mem (q : X₁ × I) q.2]
        rfl)
  have hβ_top : ∀ p : X₁ × I,
      β (attachInclTop (attachCylSet A) (attachCylMap F) p) = γ (d.retraction p) :=
    fun _ => rfl
  -- `β ∘ α = 𝟙` on the nose.
  have hβα : β.comp (attachLevel F t₀)
      = ContinuousMap.id (AttachingSpace A (attachEval F t₀)) := by
    refine attach_hom_ext (fun x₀ => rfl) (fun x₁ => ?_)
    show β ((attachLevel F t₀) (attachInclTop A (attachEval F t₀) x₁))
      = attachInclTop A (attachEval F t₀) x₁
    rw [attachLevel_top, hβ_top, d.fixes (x₁, t₀) (Or.inr rfl)]
    by_cases hx : x₁ ∈ A
    · rw [hγ_mem (x₁, t₀) hx]
      exact (attachIncl_glue A (attachEval F t₀) ⟨x₁, hx⟩).symm
    · rw [hγ_not_mem (x₁, t₀) hx]
  -- The deformation retraction upstairs descends to `W`: it fixes `A × I`, on which
  -- the attaching identification takes place.
  let Ktil : C(I × (X₀ ⊕ (X₁ × I)), AttachingCylinder F) :=
    ⟨fun q => q.2.elim (fun x₀ => attachInclBase (attachCylSet A) (attachCylMap F) x₀)
        (fun p => attachInclTop (attachCylSet A) (attachCylMap F) (d.homotopy (q.1, p))), by
      have key : Continuous fun w : (X₀ ⊕ (X₁ × I)) × I =>
          (w.1.elim (fun x₀ => attachInclBase (attachCylSet A) (attachCylMap F) x₀)
            (fun p => attachInclTop (attachCylSet A) (attachCylMap F)
              (d.homotopy (w.2, p))) : AttachingCylinder F) := by
        refine continuous_sumProd ?_ ?_
        · exact (map_continuous (attachInclBase (attachCylSet A) (attachCylMap F))).comp
            continuous_fst
        · exact (map_continuous (attachInclTop (attachCylSet A) (attachCylMap F))).comp <|
            (map_continuous d.homotopy).comp (continuous_snd.prodMk continuous_fst)
      exact key.comp ((continuous_snd.prodMk continuous_fst) :
        Continuous fun q : I × (X₀ ⊕ (X₁ × I)) => (q.2, q.1))⟩
  have hKtil_inl : ∀ (u : I) (x₀ : X₀),
      Ktil (u, Sum.inl x₀) = attachInclBase (attachCylSet A) (attachCylMap F) x₀ :=
    fun _ _ => rfl
  have hKtil_inr : ∀ (u : I) (p : X₁ × I),
      Ktil (u, Sum.inr p)
        = attachInclTop (attachCylSet A) (attachCylMap F) (d.homotopy (u, p)) :=
    fun _ _ => rfl
  have hnorm : ∀ (u : I) (p : X₀ ⊕ (X₁ × I)),
      Ktil (u, attachNorm (attachCylSet A) (attachCylMap F) p) = Ktil (u, p) := by
    intro u p
    cases p with
    | inl x₀ => rfl
    | inr pp =>
      by_cases hpp : pp ∈ attachCylSet A
      · rw [attachNorm_inr_of_mem _ _ hpp, hKtil_inl, hKtil_inr,
          d.homotopy.eq_fst u (Or.inl hpp)]
        show attachInclBase (attachCylSet A) (attachCylMap F) (attachCylMap F ⟨pp, hpp⟩)
          = attachInclTop (attachCylSet A) (attachCylMap F) pp
        exact (attachIncl_glue (attachCylSet A) (attachCylMap F) ⟨pp, hpp⟩).symm
      · rw [attachNorm_inr_of_not_mem _ _ hpp]
  have hdesc : ∀ (u : I) (a b : X₀ ⊕ (X₁ × I)),
      attachNorm (attachCylSet A) (attachCylMap F) a
        = attachNorm (attachCylSet A) (attachCylMap F) b →
      Ktil (u, a) = Ktil (u, b) := by
    intro u a b hab
    rw [← hnorm u a, ← hnorm u b, hab]
  let K : C(I × AttachingCylinder F, AttachingCylinder F) :=
    ⟨fun q => Quotient.liftOn q.2 (fun p => Ktil (q.1, p)) fun a b hab => hdesc q.1 a b hab, by
      apply (isQuotientMap_quotient_mk').continuous_lift_prod_right
      exact map_continuous Ktil⟩
  -- `K` is a homotopy rel the image of `X₀ ⊔_{F_{t₀}} X₁` from the identity to `α ∘ β`.
  have hK0 : ∀ w, K (0, w) = w := by
    intro w
    induction w using Quotient.ind with
    | _ p =>
      cases p with
      | inl x₀ => rfl
      | inr pp =>
        show attachInclTop (attachCylSet A) (attachCylMap F) (d.homotopy (0, pp))
          = attachMk (attachCylSet A) (attachCylMap F) (Sum.inr pp)
        exact congrArg (attachInclTop (attachCylSet A) (attachCylMap F))
          (d.homotopy.map_zero_left pp)
  have hK1 : ∀ w, K (1, w) = (attachLevel F t₀) (β w) := by
    intro w
    induction w using Quotient.ind with
    | _ p =>
      cases p with
      | inl x₀ => rfl
      | inr pp =>
        show attachInclTop (attachCylSet A) (attachCylMap F) (d.homotopy (1, pp))
          = (attachLevel F t₀) (β (attachInclTop (attachCylSet A) (attachCylMap F) pp))
        refine (congrArg (attachInclTop (attachCylSet A) (attachCylMap F))
          (d.homotopy.map_one_left pp)).trans ?_
        rw [hβ_top]
        have hq := d.mapsInto pp
        by_cases hq1 : (d.retraction pp).1 ∈ A
        · rw [hγ_mem (d.retraction pp) hq1, attachLevel_base]
          exact attachCyl_glue F hq1 (d.retraction pp).2
        · have hq2 : (d.retraction pp).2 = t₀ := hq.resolve_left hq1
          rw [hγ_not_mem (d.retraction pp) hq1, attachLevel_top]
          exact congrArg (attachInclTop (attachCylSet A) (attachCylMap F))
            (Prod.ext rfl hq2)
  have hrelK : ∀ (u : I) (w : AttachingCylinder F),
      w ∈ Set.range (attachLevel F t₀) → K (u, w) = w := by
    rintro u w ⟨z, rfl⟩
    induction z using Quotient.ind with
    | _ p =>
      cases p with
      | inl x₀ => rfl
      | inr x₁ =>
        show attachInclTop (attachCylSet A) (attachCylMap F) (d.homotopy (u, (x₁, t₀)))
          = (attachLevel F t₀) (attachMk A (attachEval F t₀) (Sum.inr x₁))
        exact congrArg (attachInclTop (attachCylSet A) (attachCylMap F))
          (d.homotopy.eq_fst u (Or.inr rfl))
  -- Assemble.
  refine ⟨β, hβα, ⟨?_⟩⟩
  have Hrel : (ContinuousMap.id (AttachingCylinder F)).HomotopyRel
      ((attachLevel F t₀).comp β) (Set.range (attachLevel F t₀)) :=
    { toContinuousMap := K
      map_zero_left := hK0
      map_one_left := hK1
      prop' := hrelK }
  exact Hrel.symm

/-! ## Proposition 0.18 -/

/-- **Proposition 0.18 (Hatcher, HEP form).** Let `A ⊆ X₁` be closed with `(X₁, A)`
satisfying the homotopy extension property, and let `F : A × I → X₀` be a homotopy
of attaching maps from `f = F(·, 0)` to `g = F(·, 1)`. Then the attaching spaces
`X₀ ⊔_f X₁` and `X₀ ⊔_g X₁` are homotopy equivalent **rel `X₀`**: there are maps
`φ, ψ` between them restricting to the identity on the copies of `X₀`, with
`ψ ∘ φ ≃ 𝟙` and `φ ∘ ψ ≃ 𝟙` rel `X₀`.

For CW pairs `(X₁, A)` this is Hatcher's statement verbatim, given that CW pairs
have the homotopy extension property (`prop:cw-pairs-have-hep`). -/
theorem attachingSpace_homotopyEquiv_rel {A : Set X₁} (hA : IsClosed A)
    (hHEP : HasHEP.{u, u} A) (F : C(↥A × I, X₀)) :
    ∃ (φ : C(AttachingSpace A (attachEval F 0), AttachingSpace A (attachEval F 1)))
      (ψ : C(AttachingSpace A (attachEval F 1), AttachingSpace A (attachEval F 0))),
      (∀ x₀ : X₀, φ (attachInclBase A (attachEval F 0) x₀)
        = attachInclBase A (attachEval F 1) x₀) ∧
      (∀ x₀ : X₀, ψ (attachInclBase A (attachEval F 1) x₀)
        = attachInclBase A (attachEval F 0) x₀) ∧
      Nonempty ((ψ.comp φ).HomotopyRel (ContinuousMap.id _)
        (Set.range (attachInclBase A (attachEval F 0)))) ∧
      Nonempty ((φ.comp ψ).HomotopyRel (ContinuousMap.id _)
        (Set.range (attachInclBase A (attachEval F 1)))) := by
  obtain ⟨d0⟩ := hHEP.hepBase_deformationRetract
  obtain ⟨β₀, hβα₀, ⟨H₀⟩⟩ :=
    attachLevel_isDeformationRetractIncl hA F 0 (hepBase_eq_attachLevelSet A ▸ d0)
  obtain ⟨β₁, hβα₁, ⟨H₁⟩⟩ :=
    attachLevel_isDeformationRetractIncl hA F 1 (hepBaseTopDeformationRetract d0)
  refine ⟨β₁.comp (attachLevel F 0), β₀.comp (attachLevel F 1), ?_, ?_, ⟨?_⟩, ⟨?_⟩⟩
  · -- `φ` restricts to the identity on `X₀`.
    intro x₀
    show β₁ ((attachLevel F 0) (attachInclBase A (attachEval F 0) x₀))
      = attachInclBase A (attachEval F 1) x₀
    rw [show (attachLevel F 0) (attachInclBase A (attachEval F 0) x₀)
        = (attachLevel F 1) (attachInclBase A (attachEval F 1) x₀) from rfl]
    exact ContinuousMap.congr_fun hβα₁ (attachInclBase A (attachEval F 1) x₀)
  · -- `ψ` restricts to the identity on `X₀`.
    intro x₀
    show β₀ ((attachLevel F 1) (attachInclBase A (attachEval F 1) x₀))
      = attachInclBase A (attachEval F 0) x₀
    rw [show (attachLevel F 1) (attachInclBase A (attachEval F 1) x₀)
        = (attachLevel F 0) (attachInclBase A (attachEval F 0) x₀) from rfl]
    exact ContinuousMap.congr_fun hβα₀ (attachInclBase A (attachEval F 0) x₀)
  · -- `ψ ∘ φ ≃ 𝟙 rel X₀`.
    have hm : ∀ z ∈ Set.range (attachInclBase A (attachEval F 0)),
        (attachLevel F 0) z ∈ Set.range (attachLevel F 1) := by
      rintro z ⟨x₀, rfl⟩
      exact ⟨attachInclBase A (attachEval F 1) x₀, rfl⟩
    have step := (homotopyRelPrecomp H₁ (attachLevel F 0) hm).compContinuousMap β₀
    refine step.cast ?_ ?_
    · ext z; rfl
    · show β₀.comp ((ContinuousMap.id _).comp (attachLevel F 0)) = ContinuousMap.id _
      rw [ContinuousMap.id_comp]
      exact hβα₀
  · -- `φ ∘ ψ ≃ 𝟙 rel X₀`.
    have hm : ∀ z ∈ Set.range (attachInclBase A (attachEval F 1)),
        (attachLevel F 1) z ∈ Set.range (attachLevel F 0) := by
      rintro z ⟨x₀, rfl⟩
      exact ⟨attachInclBase A (attachEval F 0) x₀, rfl⟩
    have step := (homotopyRelPrecomp H₀ (attachLevel F 1) hm).compContinuousMap β₁
    refine step.cast ?_ ?_
    · ext z; rfl
    · show β₁.comp ((ContinuousMap.id _).comp (attachLevel F 1)) = ContinuousMap.id _
      rw [ContinuousMap.id_comp]
      exact hβα₁

/-- **Homotopic attaching maps yield homotopy equivalent spaces** (Hatcher's
preview of Prop. 0.18, HEP form): forgetting the rel-`X₀` refinement of
`attachingSpace_homotopyEquiv_rel`, the attaching spaces of the two ends of a
homotopy of attaching maps are homotopy equivalent. -/
theorem attachingSpace_homotopyEquiv {A : Set X₁} (hA : IsClosed A)
    (hHEP : HasHEP.{u, u} A) (F : C(↥A × I, X₀)) :
    Nonempty (ContinuousMap.HomotopyEquiv (AttachingSpace A (attachEval F 0))
      (AttachingSpace A (attachEval F 1))) := by
  obtain ⟨φ, ψ, -, -, ⟨Hψφ⟩, ⟨Hφψ⟩⟩ := attachingSpace_homotopyEquiv_rel hA hHEP F
  exact ⟨{ toFun := φ
           invFun := ψ
           left_inv := ⟨Hψφ.toHomotopy⟩
           right_inv := ⟨Hφψ.toHomotopy⟩ }⟩

end HatcherLib

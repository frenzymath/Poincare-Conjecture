import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.CompactOpen
import HatcherLib.Ch0.HomotopyExtension

/-!
# Chapter 0 — Collapsing a contractible subspace with the HEP

Hatcher's Proposition 0.17: if a pair `(X, A)` has the homotopy extension property
and `A` is contractible, then the quotient map `q : X → X/A` is a homotopy
equivalence.

We build the collapse quotient `X/A` (which crushes `A` to a single point) as
`HatcherLib.collapseQuotient A`, the quotient of `X` by the setoid identifying all
of `A`, and prove `collapseMk_homotopyEquiv`: the quotient map `q = collapseMk A`
admits a homotopy inverse (which is exactly what it means for `q` to be a homotopy
equivalence).

The proof follows Hatcher exactly. A contraction of `A` (from `ContractibleSpace ↥A`)
is a homotopy of the inclusion `A ↪ X`; the HEP extends it to a homotopy
`fₜ : X → X` with `f₀ = 𝟙`, `fₜ(A) ⊆ A`, and `f₁(A)` a single point. Then:

* `q ∘ fₜ` sends `A` to a point, so it descends to `f̄ₜ : X/A → X/A` with
  `q ∘ fₜ = f̄ₜ ∘ q`. Joint continuity of `f̄` uses that `𝟙_I × q` is a quotient
  map (mathlib's `IsQuotientMap.continuous_lift_prod_right`, valid because `I` is
  locally compact — Whitehead's theorem);
* `f₁` is constant on `A`, so it descends to `g : X/A → X` with `g ∘ q = f₁`;
* `g` and `q` are inverse homotopy equivalences: `g ∘ q = f₁ ≃ f₀ = 𝟙` via `f`, and
  `q ∘ g = f̄₁ ≃ f̄₀ = 𝟙` via `f̄`.
-/

namespace HatcherLib

open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The setoid on `X` that identifies all points of a subset `A` with one another
(and distinguishes everything else): `x ≈ y` iff `x = y` or both `x, y ∈ A`.
Quotienting by it collapses `A` to a single point. -/
def collapseSetoid (A : Set X) : Setoid X where
  r x y := x = y ∨ (x ∈ A ∧ y ∈ A)
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun h => h.imp Eq.symm (fun p => ⟨p.2, p.1⟩)
      trans := fun hxy hyz => by
        rcases hxy with rfl | ⟨hx, hy⟩
        · exact hyz
        · rcases hyz with rfl | ⟨_, hz⟩
          · exact Or.inr ⟨hx, hy⟩
          · exact Or.inr ⟨hx, hz⟩ }

/-- The **collapse quotient** `X/A`: the quotient of `X` that crushes `A` to a point,
carrying the quotient topology. -/
abbrev collapseQuotient (A : Set X) : Type u := Quotient (collapseSetoid A)

/-- The quotient map `q : X → X/A`. -/
def collapseMk (A : Set X) : C(X, collapseQuotient A) :=
  ⟨Quotient.mk (collapseSetoid A), continuous_quotient_mk'⟩

/-- Any two points of `A` are identified in `X/A`. -/
theorem collapseMk_eq_of_mem {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    collapseMk A x = collapseMk A y :=
  Quotient.sound (Or.inr ⟨hx, hy⟩)

/-- **Proposition 0.17 (Hatcher).** If the pair `(X, A)` has the homotopy extension
property and `A` is contractible, then the quotient map `q = collapseMk A : X → X/A`
is a homotopy equivalence: it admits a map `g : X/A → X` with `g ∘ q ≃ 𝟙_X` and
`q ∘ g ≃ 𝟙_{X/A}`. -/
theorem collapseMk_homotopyEquiv {A : Set X} (hHEP : HasHEP.{u, u} A)
    [ContractibleSpace ↥A] :
    ∃ g : C(collapseQuotient A, X),
      (g.comp (collapseMk A)).Homotopic (ContinuousMap.id X) ∧
        ((collapseMk A).comp g).Homotopic (ContinuousMap.id (collapseQuotient A)) := by
  -- A contraction of `A`: a homotopy `H` of `𝟙 : A → A` to the constant map `a₀`.
  obtain ⟨a₀, hcon⟩ := id_nullhomotopic ↥A
  obtain ⟨H⟩ := hcon
  -- View the contraction as a homotopy of the inclusion `A ↪ X` (time is the first
  -- coordinate of `H`, so we swap it to the HEP's `A × I` convention).
  have hmap_cont : Continuous (fun p : ↥A × I => (H (p.2, p.1) : X)) :=
    continuous_subtype_val.comp
      ((map_continuous H).comp (continuous_snd.prodMk continuous_fst))
  let hmap : C(↥A × I, X) := ⟨_, hmap_cont⟩
  -- Extend it by the HEP to a homotopy `F = fₜ : X → X` of `𝟙`.
  obtain ⟨F, hF0, hFA⟩ :=
    hHEP (ContinuousMap.id X) hmap (fun a => congrArg Subtype.val (H.map_zero_left a))
  have hF0' : ∀ x : X, F (x, 0) = x := hF0
  -- `fₜ(A) ⊆ A`, and `f₁` collapses `A` to the single point `a₀`.
  have hFmem : ∀ (a : ↥A) (t : I), F ((a : X), t) ∈ A := by
    intro a t; rw [hFA a t]; exact (H (t, a)).2
  have hF1 : ∀ (a : ↥A), F ((a : X), 1) = (a₀ : X) := by
    intro a; rw [hFA a 1]; exact congrArg Subtype.val (H.map_one_left a)
  let q := collapseMk A
  -- The map `g : X/A → X` induced by `f₁`, using `f₁|_A ≡ a₀`.
  have hg_wd : ∀ (x y : X), (collapseSetoid A).r x y → F (x, 1) = F (y, 1) := by
    rintro x y (rfl | ⟨hx, hy⟩)
    · rfl
    · rw [hF1 ⟨x, hx⟩, hF1 ⟨y, hy⟩]
  let g : C(collapseQuotient A, X) :=
    ⟨Quotient.lift (fun x => F (x, 1)) hg_wd,
      ((map_continuous F).comp (continuous_id.prodMk continuous_const)).quotient_lift hg_wd⟩
  -- The descended homotopy `f̄ : X/A → X/A`, `f̄ₜ ∘ q = q ∘ fₜ`.
  have hFbar_wd : ∀ (t : I) (x y : X), (collapseSetoid A).r x y →
      q (F (x, t)) = q (F (y, t)) := by
    rintro t x y (rfl | ⟨hx, hy⟩)
    · rfl
    · exact collapseMk_eq_of_mem (hFmem ⟨x, hx⟩ t) (hFmem ⟨y, hy⟩ t)
  let Fbarfun : I × collapseQuotient A → collapseQuotient A :=
    fun p => Quotient.lift (fun x => q (F (x, p.1))) (hFbar_wd p.1) p.2
  have hFbar_cont : Continuous Fbarfun := by
    refine (isQuotientMap_quotient_mk').continuous_lift_prod_right ?_
    exact (map_continuous q).comp ((map_continuous F).comp
      (continuous_snd.prodMk continuous_fst))
  -- Package `f̄` as a homotopy `𝟙_{X/A} ≃ q ∘ g`.
  let Fbar : ContinuousMap.Homotopy (ContinuousMap.id (collapseQuotient A)) (q.comp g) :=
    { toContinuousMap := ⟨Fbarfun, hFbar_cont⟩
      map_zero_left := by
        intro z
        induction z using Quotient.ind
        rename_i x
        show q (F (x, 0)) = q x
        rw [hF0' x]
      map_one_left := by
        intro z
        induction z using Quotient.ind
        rename_i x
        show q (F (x, 1)) = q (g (collapseMk A x))
        rfl }
  -- Package `f` as a homotopy `𝟙_X ≃ g ∘ q`.
  let Fhom : ContinuousMap.Homotopy (ContinuousMap.id X) (g.comp q) :=
    { toContinuousMap := ⟨fun p : I × X => F (p.2, p.1),
        (map_continuous F).comp (continuous_snd.prodMk continuous_fst)⟩
      map_zero_left := hF0
      map_one_left := fun _ => rfl }
  exact ⟨g,
    ContinuousMap.Homotopic.symm ⟨Fhom⟩,
    ContinuousMap.Homotopic.symm ⟨Fbar⟩⟩

end HatcherLib

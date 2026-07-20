import Mathlib.Topology.Homotopy.Basic
import Mathlib.Topology.Constructions.SumProd
import HatcherLib.Ch0.HomotopyTheory

/-!
# Chapter 0 — The homotopy extension property

Hatcher's Chapter 0 closes with the **homotopy extension property** (HEP) for a
pair `(X, A)`, and proves several homotopy-equivalence criteria from it. mathlib
does not package the HEP, so we introduce it here as project-local
infrastructure.

The propositions of Hatcher's final section — `(X, A)` has the HEP iff
`X × {0} ∪ A × I` is a retract of `X × I`; CW pairs have the HEP; the quotient by
a contractible subspace with the HEP is a homotopy equivalence; a homotopy
equivalence restricting to `𝟙` on `A` is one rel `A` — are future work built on
this definition.
-/

namespace HatcherLib

open scoped unitInterval

universe u v

/-! ## Topological preliminary: maps out of `(A ⊕ B) × C` -/

/-- A map out of `(A ⊕ B) × C` is continuous as soon as its restrictions to the
two summands are: transport along the homeomorphism
`(A ⊕ B) × C ≃ₜ (A × C) ⊕ (B × C)`. Used to check continuity of maps defined on
products of quotients of sum types (mapping cylinders, attaching spaces). -/
theorem continuous_sumProd {A B C Z : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace Z] {g : (A ⊕ B) × C → Z}
    (hl : Continuous fun p : A × C => g (Sum.inl p.1, p.2))
    (hr : Continuous fun p : B × C => g (Sum.inr p.1, p.2)) :
    Continuous g := by
  rw [← Homeomorph.comp_continuous_iff'
    (Homeomorph.sumProdDistrib (X := A) (Y := B) (Z := C)).symm]
  refine continuous_sum_dom.mpr ⟨?_, ?_⟩
  · have h : ((g ∘ ⇑(Homeomorph.sumProdDistrib (X := A) (Y := B) (Z := C)).symm) ∘ Sum.inl) =
        fun p : A × C => g (Sum.inl p.1, p.2) := by
      funext p; simp [Homeomorph.sumProdDistrib]
    rw [h]; exact hl
  · have h : ((g ∘ ⇑(Homeomorph.sumProdDistrib (X := A) (Y := B) (Z := C)).symm) ∘ Sum.inr) =
        fun p : B × C => g (Sum.inr p.1, p.2) := by
      funext p; simp [Homeomorph.sumProdDistrib]
    rw [h]; exact hr

variable {X : Type u} [TopologicalSpace X]

/-- The pair `(X, A)` with `A ⊆ X` has the **homotopy extension property** if for
every space `Y`, every map `f : X → Y` and every homotopy `h : A × I → Y` of the
restriction `f|_A` (that is, `h(a, 0) = f(a)` for all `a ∈ A`) extend to a
homotopy `F : X × I → Y` of `f` (that is, `F(x, 0) = f(x)`) whose restriction to
`A × I` is `h`. -/
def HasHEP (A : Set X) : Prop :=
  ∀ {Y : Type v} [TopologicalSpace Y] (f : C(X, Y)) (h : C(↥A × I, Y)),
    (∀ a : ↥A, h (a, 0) = f (a : X)) →
      ∃ F : C(X × I, Y),
        (∀ x : X, F (x, 0) = f x) ∧ ∀ (a : ↥A) (t : I), F ((a : X), t) = h (a, t)

/-!
## The retract characterisation of the homotopy extension property

Hatcher's first proposition of the section (Prop. 0.??, "HEP is equivalent to a
retraction property") states that `(X, A)` has the HEP iff the subspace
`X × {0} ∪ A × I` is a retract of the cylinder `X × I`. We prove:

* `HasHEP.isRetract` — the forward direction, needing **no** hypothesis on `A`;
* `hasHEP_of_isRetract` — the converse **when `A` is closed** (Hatcher's proof
  glues two maps on the closed sets `X × {0}` and `A × I`);
* `isClosed_of_isRetract` — Hatcher's final observation: if `X` is Hausdorff and
  the retract exists, then `A` is automatically closed;
* `hasHEP_iff_isRetract` — the equivalence, for a closed `A`.

The construction of the extension from a retraction goes through the glued map
`hepGlue`, which is reusable for the later CW-pair and rel-`A` propositions.
-/

/-- The subspace `X × {0} ∪ A × I` of the cylinder `X × I` (the domain on which a
homotopy of `f` and a homotopy along `A` are simultaneously prescribed by the
HEP). -/
def hepBase (A : Set X) : Set (X × I) := {p | p.1 ∈ A ∨ p.2 = 0}

omit [TopologicalSpace X] in
theorem mem_hepBase_left {A : Set X} {p : X × I} (hp : p.1 ∈ A) : p ∈ hepBase A :=
  Or.inl hp

omit [TopologicalSpace X] in
theorem mem_hepBase_right {A : Set X} {p : X × I} (hp : p.2 = 0) : p ∈ hepBase A :=
  Or.inr hp

/-- A subset `M` of a space is a **retract** of it: there is a continuous self-map
landing in `M` and fixing `M` pointwise (Hatcher's "`M` is a retract of `X × I`").
Such an `r` is automatically idempotent, so this matches the projection-operator
picture of `HatcherLib.IsRetraction`. -/
def IsRetract {P : Type*} [TopologicalSpace P] (M : Set P) : Prop :=
  ∃ r : C(P, P), (∀ p, r p ∈ M) ∧ ∀ p ∈ M, r p = p

/-- The map `X × {0} ∪ A × I → Y` obtained by combining a map `f : X → Y` on
`X × {0}` with a homotopy `h : A × I → Y` along `A`. Extended to all of `X × I` by
the value `f p.1` off `A`; on the overlap `A × {0}` the two prescriptions agree
exactly when `h(a, 0) = f a`. -/
noncomputable def hepGlue {A : Set X} {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (h : C(↥A × I, Y)) : X × I → Y :=
  open Classical in
  fun p => if hp : p.1 ∈ A then h (⟨p.1, hp⟩, p.2) else f p.1

theorem hepGlue_of_mem {A : Set X} {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (h : C(↥A × I, Y)) {p : X × I} (hp : p.1 ∈ A) :
    hepGlue f h p = h (⟨p.1, hp⟩, p.2) := by
  simp only [hepGlue, dif_pos hp]

theorem hepGlue_of_not_mem {A : Set X} {Y : Type v} [TopologicalSpace Y]
    (f : C(X, Y)) (h : C(↥A × I, Y)) {p : X × I} (hp : p.1 ∉ A) :
    hepGlue f h p = f p.1 := by
  simp only [hepGlue, dif_neg hp]

/-- When `A` is closed, `hepGlue f h` is continuous on `X × {0} ∪ A × I`: it agrees
with the continuous map `h` on the closed set `A × I` and with `f ∘ pr₁` on the
closed set `X × {0}`, and these agree on the overlap, so the pasting lemma applies. -/
theorem continuousOn_hepGlue {A : Set X} (hA : IsClosed A) {Y : Type v}
    [TopologicalSpace Y] (f : C(X, Y)) (h : C(↥A × I, Y))
    (hagree : ∀ a : ↥A, h (a, 0) = f (a : X)) :
    ContinuousOn (hepGlue f h) (hepBase A) := by
  have hMA : IsClosed {p : X × I | p.1 ∈ A} := hA.preimage continuous_fst
  have hM0 : IsClosed {p : X × I | p.2 = (0 : I)} :=
    isClosed_singleton.preimage continuous_snd
  have contA : ContinuousOn (hepGlue f h) {p : X × I | p.1 ∈ A} := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous
        (fun q : {p : X × I | p.1 ∈ A} => h (⟨q.1.1, q.2⟩, q.1.2)) :=
      map_continuous h |>.comp <|
        ((continuous_fst.comp continuous_subtype_val).subtype_mk fun q => q.2).prodMk
          (continuous_snd.comp continuous_subtype_val)
    exact hc.congr fun q => (hepGlue_of_mem f h q.2).symm
  have contB : ContinuousOn (hepGlue f h) {p : X × I | p.2 = (0 : I)} := by
    refine ContinuousOn.congr (f := fun p => f p.1)
      ((map_continuous f).comp continuous_fst).continuousOn ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_cases hpa : p.1 ∈ A
    · rw [hepGlue_of_mem f h hpa, hp]; exact hagree ⟨p.1, hpa⟩
    · rw [hepGlue_of_not_mem f h hpa]
  have hunion : hepBase A = {p : X × I | p.1 ∈ A} ∪ {p : X × I | p.2 = (0 : I)} := rfl
  rw [hunion]
  exact contA.union_of_isClosed contB hMA hM0

/-- Level-`t₀` generalisation of `continuousOn_hepGlue`: when `A` is closed and the
prescriptions agree on `A × {t₀}`, the glued map `hepGlue f h` is continuous on
`X × {t₀} ∪ A × I`. (The `hepBase` version is the case `t₀ = 0`.) -/
theorem continuousOn_hepGlue_at {A : Set X} (hA : IsClosed A) {Y : Type v}
    [TopologicalSpace Y] (f : C(X, Y)) (h : C(↥A × I, Y)) (t₀ : I)
    (hagree : ∀ a : ↥A, h (a, t₀) = f (a : X)) :
    ContinuousOn (hepGlue f h) {p : X × I | p.1 ∈ A ∨ p.2 = t₀} := by
  have hMA : IsClosed {p : X × I | p.1 ∈ A} := hA.preimage continuous_fst
  have hM0 : IsClosed {p : X × I | p.2 = t₀} :=
    isClosed_singleton.preimage continuous_snd
  have contA : ContinuousOn (hepGlue f h) {p : X × I | p.1 ∈ A} := by
    rw [continuousOn_iff_continuous_restrict]
    have hc : Continuous
        (fun q : {p : X × I | p.1 ∈ A} => h (⟨q.1.1, q.2⟩, q.1.2)) :=
      map_continuous h |>.comp <|
        ((continuous_fst.comp continuous_subtype_val).subtype_mk fun q => q.2).prodMk
          (continuous_snd.comp continuous_subtype_val)
    exact hc.congr fun q => (hepGlue_of_mem f h q.2).symm
  have contB : ContinuousOn (hepGlue f h) {p : X × I | p.2 = t₀} := by
    refine ContinuousOn.congr (f := fun p => f p.1)
      ((map_continuous f).comp continuous_fst).continuousOn ?_
    intro p hp
    simp only [Set.mem_setOf_eq] at hp
    by_cases hpa : p.1 ∈ A
    · rw [hepGlue_of_mem f h hpa, hp]; exact hagree ⟨p.1, hpa⟩
    · rw [hepGlue_of_not_mem f h hpa]
  have hunion : {p : X × I | p.1 ∈ A ∨ p.2 = t₀}
      = {p : X × I | p.1 ∈ A} ∪ {p : X × I | p.2 = t₀} := rfl
  rw [hunion]
  exact contA.union_of_isClosed contB hMA hM0

/-- **Forward direction of the HEP characterisation.** If `(X, A)` has the homotopy
extension property, then `X × {0} ∪ A × I` is a retract of `X × I`. Apply the HEP to
the target `↥(hepBase A)` itself, with `f = (·, 0)` and `h` the inclusion of
`A × I`; the resulting extension, followed by the inclusion into `X × I`, is the
retraction. No hypothesis on `A` is needed. -/
theorem HasHEP.isRetract {A : Set X} (hHEP : HasHEP.{u, u} A) :
    IsRetract (hepBase A) := by
  let f : C(X, ↥(hepBase A)) :=
    ⟨fun x => ⟨(x, 0), Or.inr rfl⟩,
      (continuous_id.prodMk continuous_const).subtype_mk fun _ => Or.inr rfl⟩
  let h : C(↥A × I, ↥(hepBase A)) :=
    ⟨fun p => ⟨((p.1 : X), p.2), Or.inl p.1.2⟩,
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk
        fun p => Or.inl p.1.2⟩
  obtain ⟨F, hF0, hFA⟩ := hHEP f h fun a => Subtype.ext rfl
  refine ⟨(⟨Subtype.val, continuous_subtype_val⟩ : C(↥(hepBase A), X × I)).comp F,
    fun p => (F p).2, ?_⟩
  intro p hp
  show (F p).val = p
  rcases hp with hpA | hp0
  · have e : F p = h (⟨p.1, hpA⟩, p.2) := hFA ⟨p.1, hpA⟩ p.2
    rw [e]; exact Prod.ext rfl rfl
  · have e : F p = f p.1 := by
      have h1 : F p = F (p.1, 0) := by rw [← hp0]
      rw [h1]; exact hF0 p.1
    rw [e]; exact Prod.ext rfl hp0.symm

/-- **Converse of the HEP characterisation, for a closed subspace.** If `A` is closed
in `X` and `X × {0} ∪ A × I` is a retract of `X × I`, then `(X, A)` has the homotopy
extension property: glue the prescribed data with `hepGlue` and precompose with the
retraction. -/
theorem hasHEP_of_isRetract {A : Set X} (hA : IsClosed A)
    (hR : IsRetract (hepBase A)) : HasHEP A := by
  obtain ⟨r, hr_mem, hr_fix⟩ := hR
  intro Y _ f h hagree
  refine ⟨⟨fun p => hepGlue f h (r p),
      (continuousOn_hepGlue hA f h hagree).comp_continuous (map_continuous r) hr_mem⟩,
    ?_, ?_⟩
  · intro x
    show hepGlue f h (r (x, 0)) = f x
    rw [hr_fix (x, 0) (mem_hepBase_right rfl)]
    by_cases hxa : x ∈ A
    · rw [hepGlue_of_mem f h (p := (x, 0)) hxa]; exact hagree ⟨x, hxa⟩
    · rw [hepGlue_of_not_mem f h (p := (x, 0)) hxa]
  · intro a t
    show hepGlue f h (r ((a : X), t)) = h (a, t)
    rw [hr_fix ((a : X), t) (mem_hepBase_left a.2), hepGlue_of_mem f h (p := ((a : X), t)) a.2]

/-- **Hatcher's closedness observation.** If `X` is Hausdorff and `X × {0} ∪ A × I`
is a retract of `X × I`, then `A` is closed in `X`. The retraction's fixed-point set
is closed (an equalizer into a Hausdorff space) and equals `hepBase A`; slicing at
`t = 1` recovers `A`. -/
theorem isClosed_of_isRetract [T2Space X] {A : Set X}
    (hR : IsRetract (hepBase A)) : IsClosed A := by
  obtain ⟨r, hr_mem, hr_fix⟩ := hR
  have hfix : IsClosed {p : X × I | r p = p} :=
    isClosed_eq (map_continuous r) continuous_id
  have hEq : hepBase A = {p : X × I | r p = p} := by
    ext p
    refine ⟨fun hp => hr_fix p hp, fun (hp : r p = p) => ?_⟩
    have hmem := hr_mem p
    rwa [hp] at hmem
  have hbase : IsClosed (hepBase A) := hEq ▸ hfix
  have hpre : A = (fun x : X => (x, (1 : I))) ⁻¹' hepBase A := by
    have h10 : (1 : I) ≠ 0 := by
      intro hh; simpa using congrArg Subtype.val hh
    ext x
    simp only [Set.mem_preimage, hepBase, Set.mem_setOf_eq]
    tauto
  rw [hpre]
  exact hbase.preimage (by fun_prop)

/-- **HEP characterisation (Hatcher).** For a closed subspace `A ⊆ X`, the pair
`(X, A)` has the homotopy extension property iff `X × {0} ∪ A × I` is a retract of
`X × I`. -/
theorem hasHEP_iff_isRetract {A : Set X} (hA : IsClosed A) :
    HasHEP.{u, u} A ↔ IsRetract (hepBase A) :=
  ⟨HasHEP.isRetract, hasHEP_of_isRetract hA⟩

/-!
## The retract of the cylinder onto `X × {0} ∪ A × I` is a deformation retract

Hatcher observes (as an exercise, via Corollary 0.20) that when `(X, A)` has the
homotopy extension property, `X × I` *deformation* retracts onto
`X × {0} ∪ A × I`. There is a direct classical formula: any retraction
`r = (r₁, r₂)` of `X × I` onto `X × {0} ∪ A × I` is homotopic to the identity rel
`X × {0} ∪ A × I` via

`H_u(x, s) = ( r₁(x, u·s), (1-u)·s + u·r₂(x, s) )`.

At `u = 0` this is `(r₁(x, 0), s) = (x, s)`; at `u = 1` it is `r(x, s)`; and both
prescriptions on `X × {0} ∪ A × I` are fixed throughout, since `r` fixes
`(x, 0)` and `(a, s)`. This fact is the engine of Hatcher's Proposition 0.18
(homotopic attaching maps): the induced deformation retraction of an adjunction
cylinder onto its bottom-plus-attached part descends to adjunction spaces.
-/

/-- The convex combination `(1-u)·s + u·t` stays in the unit interval. -/
theorem convexCombo_mem (u s t : I) :
    (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * (t : ℝ) ∈ unitInterval := by
  have hu0 := unitInterval.nonneg u
  have hu1 := unitInterval.le_one u
  have hs0 := unitInterval.nonneg s
  have hs1 := unitInterval.le_one s
  have ht0 := unitInterval.nonneg t
  have ht1 := unitInterval.le_one t
  constructor
  · positivity
  · nlinarith

/-- **A retraction of the cylinder onto `X × {0} ∪ A × I` is automatically a
deformation retraction.** Writing `r = (r₁, r₂)`, the deformation is
`H_u(x, s) = (r₁(x, u·s), (1-u)·s + u·r₂(x, s))`: the identity at `u = 0`
(as `r` fixes `X × {0}`), the retraction `r` at `u = 1`, and constant in `u` on
`X × {0} ∪ A × I`. -/
noncomputable def hepBaseDeformationRetract {A : Set X} (r : C(X × I, X × I))
    (hmem : ∀ p, r p ∈ hepBase A) (hfix : ∀ p ∈ hepBase A, r p = p) :
    DeformationRetract (hepBase A) where
  retraction := r
  mapsInto := hmem
  fixes := hfix
  homotopy :=
    { toContinuousMap :=
        { toFun := fun p =>
            ((r (p.2.1, ⟨(p.1 : ℝ) * (p.2.2 : ℝ),
                unitInterval.mul_mem p.1.2 p.2.2.2⟩)).1,
              ⟨(1 - (p.1 : ℝ)) * (p.2.2 : ℝ) + (p.1 : ℝ) * ((r p.2).2 : ℝ),
                convexCombo_mem p.1 p.2.2 (r p.2).2⟩)
          continuous_toFun := by
            refine Continuous.prodMk ?_ ?_
            · exact continuous_fst.comp <| (map_continuous r).comp <|
                (continuous_fst.comp continuous_snd).prodMk <|
                  Continuous.subtype_mk (by fun_prop) _
            · exact Continuous.subtype_mk (by fun_prop) _ }
      map_zero_left := by
        intro p
        obtain ⟨x, s⟩ := p
        have hz : (x, (⟨((0 : I) : ℝ) * (s : ℝ), unitInterval.mul_mem (0 : I).2 s.2⟩ : I))
            = ((x, 0) : X × I) := by
          refine Prod.ext rfl (Subtype.ext ?_)
          show (0 : ℝ) * (s : ℝ) = (0 : ℝ)
          ring
        refine Prod.ext ?_ (Subtype.ext ?_)
        · show (r (x, ⟨((0 : I) : ℝ) * (s : ℝ), unitInterval.mul_mem (0 : I).2 s.2⟩)).1 = x
          rw [hz, hfix (x, 0) (mem_hepBase_right rfl)]
        · show (1 - (0 : ℝ)) * (s : ℝ) + (0 : ℝ) * ((r (x, s)).2 : ℝ) = (s : ℝ)
          ring
      map_one_left := by
        intro p
        obtain ⟨x, s⟩ := p
        have ho : (x, (⟨((1 : I) : ℝ) * (s : ℝ), unitInterval.mul_mem (1 : I).2 s.2⟩ : I))
            = ((x, s) : X × I) := by
          refine Prod.ext rfl (Subtype.ext ?_)
          show (1 : ℝ) * (s : ℝ) = (s : ℝ)
          ring
        refine Prod.ext ?_ (Subtype.ext ?_)
        · show (r (x, ⟨((1 : I) : ℝ) * (s : ℝ), unitInterval.mul_mem (1 : I).2 s.2⟩)).1
            = (r (x, s)).1
          rw [ho]
        · show (1 - (1 : ℝ)) * (s : ℝ) + (1 : ℝ) * ((r (x, s)).2 : ℝ) = ((r (x, s)).2 : ℝ)
          ring
      prop' := by
        intro u p hp
        obtain ⟨x, s⟩ := p
        rcases hp with hpA | hp0
        · -- `p = (a, s)` with `a ∈ A`: `r` fixes both `(a, u·s)` and `(a, s)`.
          have h1 : r (x, ⟨(u : ℝ) * (s : ℝ), unitInterval.mul_mem u.2 s.2⟩)
              = (x, ⟨(u : ℝ) * (s : ℝ), unitInterval.mul_mem u.2 s.2⟩) :=
            hfix _ (mem_hepBase_left hpA)
          have h2 : r (x, s) = (x, s) := hfix (x, s) (mem_hepBase_left hpA)
          refine Prod.ext ?_ (Subtype.ext ?_)
          · show (r (x, ⟨(u : ℝ) * (s : ℝ), unitInterval.mul_mem u.2 s.2⟩)).1 = x
            rw [h1]
          · show (1 - (u : ℝ)) * (s : ℝ) + (u : ℝ) * ((r (x, s)).2 : ℝ) = (s : ℝ)
            rw [h2]
            ring
        · -- `p = (x, 0)`: `u·0 = 0` and `r` fixes `(x, 0)`.
          have hs0 : s = 0 := hp0
          subst hs0
          have h2 : r (x, (0 : I)) = (x, 0) := hfix (x, 0) (mem_hepBase_right rfl)
          have hz : (x, (⟨(u : ℝ) * ((0 : I) : ℝ),
                unitInterval.mul_mem u.2 (0 : I).2⟩ : I)) = ((x, 0) : X × I) := by
            refine Prod.ext rfl (Subtype.ext ?_)
            show (u : ℝ) * (0 : ℝ) = (0 : ℝ)
            ring
          refine Prod.ext ?_ (Subtype.ext ?_)
          · show (r (x, ⟨(u : ℝ) * ((0 : I) : ℝ), unitInterval.mul_mem u.2 (0 : I).2⟩)).1 = x
            rw [hz, h2]
          · show (1 - (u : ℝ)) * ((0 : I) : ℝ) + (u : ℝ) * ((r (x, (0 : I))).2 : ℝ)
              = ((0 : I) : ℝ)
            rw [h2]
            show (1 - (u : ℝ)) * (0 : ℝ) + (u : ℝ) * (0 : ℝ) = (0 : ℝ)
            ring }

/-- **If `(X, A)` has the homotopy extension property, then `X × I` deformation
retracts onto `X × {0} ∪ A × I`** (Hatcher's exercise following Corollary 0.20,
by the direct formula of `hepBaseDeformationRetract` applied to the retraction
produced by the HEP). -/
theorem HasHEP.hepBase_deformationRetract {A : Set X} (hHEP : HasHEP.{u, u} A) :
    Nonempty (DeformationRetract (hepBase A)) := by
  obtain ⟨r, hmem, hfix⟩ := hHEP.isRetract
  exact ⟨hepBaseDeformationRetract r hmem hfix⟩

end HatcherLib

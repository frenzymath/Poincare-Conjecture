import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.CompactOpen
import HatcherLib.Ch0.HomotopyExtension

/-!
# Chapter 0 — The homotopy extension property, map form, and the rel-`A` refinement

This file develops the last technical results of Hatcher's Chapter 0 built on the
homotopy extension property (HEP). The `HatcherLib.Ch0.HomotopyExtension` file
states the HEP for a *subspace* `A ⊆ X` (`HatcherLib.HasHEP`); here we work with
the equivalent **map form** `HatcherLib.HasHEPMap i` for an inclusion `i : A → X`,
which is what Hatcher's Proposition 0.19 needs, since there the same subspace `A`
sits inside two different spaces `X` and `Y`.

The map form coincides with the subspace form for the subtype inclusion
`(Subtype.val : ↥A → X)` (`hasHEP_iff_hasHEPMap`), so it is faithful to the
blueprint's HEP.

Main results:

* `HasHEPMap` — the homotopy extension property for a map `i : A → X`;
* `hasHEP_iff_hasHEPMap` — the map form for the subtype inclusion is the subspace
  form of `HatcherLib.HasHEP`;
* `HasHEPMap.prodMap_id` — **if `(X, A)` has the HEP then so does `(X × I, A × I)`**
  (Hatcher's inline lemma in the proof of Prop. 0.19). The proof is the "exponential
  law": a homotopy over the extra `I`-factor is a homotopy into the mapping space
  `C(I, Z)`, so ordinary HEP with target `C(I, Z)` does the job. No closedness of
  `A` is needed.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

/-- The pair `(X, i)` — a space `X` with a map `i : A → X`, thought of as the
inclusion of a subspace — has the **homotopy extension property** if for every
space `Z`, every map `φ : X → Z` and every homotopy `h : A × I → Z` of `φ ∘ i`
(that is, `h(a, 0) = φ(i a)`) extend to a homotopy `F : X × I → Z` of `φ` whose
restriction along `i` is `h`.

This is the map (cofibration) form of `HatcherLib.HasHEP`; for the subtype
inclusion of a subset it reduces to it (`hasHEP_iff_hasHEPMap`). -/
def HasHEPMap {A X : Type u} [TopologicalSpace A] [TopologicalSpace X] (i : C(A, X)) :
    Prop :=
  ∀ {Z : Type u} [TopologicalSpace Z] (φ : C(X, Z)) (h : C(A × I, Z)),
    (∀ a : A, h (a, 0) = φ (i a)) →
      ∃ F : C(X × I, Z),
        (∀ x : X, F (x, 0) = φ x) ∧ ∀ (a : A) (t : I), F (i a, t) = h (a, t)

variable {X : Type u} [TopologicalSpace X]

/-- The subtype inclusion `↥A → X` of a subset. -/
def subtypeIncl (A : Set X) : C(↥A, X) := ⟨Subtype.val, continuous_subtype_val⟩

@[simp] theorem subtypeIncl_apply (A : Set X) (a : ↥A) : subtypeIncl A a = (a : X) := rfl

/-- **The map form of the HEP for a subtype inclusion is the subspace form.** For a
subset `A ⊆ X`, `HasHEPMap (subtypeIncl A)` is definitionally Hatcher's
`HasHEP A`. -/
theorem hasHEP_iff_hasHEPMap (A : Set X) : HasHEP.{u, u} A ↔ HasHEPMap (subtypeIncl A) :=
  Iff.rfl

/-- **HEP is preserved by taking the product with `I`.** If `(X, A)` has the homotopy
extension property (map form), then so does `(X × I, A × I)`, where `A × I ⊆ X × I`
is included via `i × 𝟙_I`.

Hatcher uses this inline in the proof of Proposition 0.19 ("Since `(X, A)` has the
homotopy extension property, so does `(X × I, A × I)`"). The proof is the exponential
law: a homotopy of a map on `X × I`, in a fresh parameter `u`, is the same as a
homotopy of a map on `X` valued in the mapping space `C(I, Z)`; apply the ordinary
HEP with target `C(I, Z)`. -/
theorem HasHEPMap.prodMap_id {A : Type u} [TopologicalSpace A] {i : C(A, X)}
    (hi : HasHEPMap i) : HasHEPMap (i.prodMap (ContinuousMap.id I)) := by
  intro Z _ φ h hcompat
  -- Reassociate the source coordinates: `e1 : ((a, u), s) ↦ ((a, s), u)` and
  -- `e2 : ((x, s), u) ↦ ((x, u), s)`.
  let e1 : C((A × I) × I, (A × I) × I) :=
    ⟨fun p => ((p.1.1, p.2), p.1.2), by fun_prop⟩
  let e2 : C((X × I) × I, (X × I) × I) :=
    ⟨fun p => ((p.1.1, p.2), p.1.2), by fun_prop⟩
  -- `φ' : X → C(I, Z)`, `x ↦ (s ↦ φ (x, s))`.
  let φ' : C(X, C(I, Z)) := φ.curry
  -- `h' : A × I → C(I, Z)`, `(a, u) ↦ (s ↦ h ((a, s), u))`.
  let h' : C(A × I, C(I, Z)) := (h.comp e1).curry
  -- Compatibility at the parameter value `u = 0`.
  have hcompat' : ∀ a : A, h' (a, 0) = φ' (i a) := by
    intro a
    ext s
    show h ((a, s), 0) = φ (i a, s)
    have := hcompat (a, s)
    simpa [ContinuousMap.prodMap_apply] using this
  -- Apply the HEP for `(X, A)` with target the mapping space `C(I, Z)`.
  obtain ⟨F', hF'0, hF'A⟩ := hi φ' h' hcompat'
  -- Reassemble the extension on `(X × I) × I`.
  refine ⟨F'.uncurry.comp e2, ?_, ?_⟩
  · intro q
    obtain ⟨x, s⟩ := q
    show F'.uncurry ((x, 0), s) = φ (x, s)
    rw [ContinuousMap.uncurry_apply]
    show (F' (x, 0)) s = φ (x, s)
    rw [hF'0 x]
    rfl
  · intro a t
    obtain ⟨a, s⟩ := a
    show F'.uncurry ((i a, t), s) = h ((a, s), t)
    rw [ContinuousMap.uncurry_apply]
    show (F' (i a, t)) s = h ((a, s), t)
    rw [hF'A a t]
    rfl

section Step2

variable {A : Type u} [TopologicalSpace A]

/-- **Step-2 core of Prop 0.19 (abstract form).** Suppose `k` is a homotopy from `p`
to `𝟙_X` whose restriction along `iX` is *palindromic*: `k(s, iX a) = k(σ s, iX a)`
(the homotopy retraces itself on `A`). If `(X, A)` has the HEP, then `p ≃ 𝟙_X` rel
`A`. The palindromic loop on `A` is nullhomotoped by the standard "V-shaped" homotopy
of homotopies, extended over `X` by the HEP for `(X × I, A × I)`. -/
theorem step2_core (iX : C(A, X)) (p : C(X, X))
    (k : ContinuousMap.Homotopy p (ContinuousMap.id X))
    (hpal : ∀ (a : A) (s : I), k (s, iX a) = k (σ s, iX a))
    (hHEP : HasHEPMap iX) :
    Nonempty (p.HomotopyRel (ContinuousMap.id X) (Set.range iX)) := by
  classical
  have c0 : ((0 : I) : ℝ) = 0 := rfl
  have c1 : ((1 : I) : ℝ) = 1 := rfl
  have sz : σ (0 : I) = 1 := by simp
  have so : σ (1 : I) = 0 := by simp
  -- `p` is the identity on `A`: `k(0, iX a) = k(σ 0, iX a) = k(1, iX a) = iX a`.
  have hp : ∀ a : A, p (iX a) = iX a := by
    intro a
    have h0 : k ((0 : I), iX a) = p (iX a) := k.map_zero_left (iX a)
    have h1 : k ((1 : I), iX a) = iX a := k.map_one_left (iX a)
    have h := hpal a 0
    rw [sz] at h
    rw [h0, h1] at h
    exact h
  -- The reparametrisation `ρ(t, u) = ½ - max(|t - ½|, u/2) ∈ [0, ½]`. Thanks to the
  -- palindromic identity, the single formula `k(ρ(t, u), iX a)` realises the "V-shaped"
  -- homotopy of homotopies on `A`: `k_t|_A` on the bottom, `iX a` on the other edges.
  have hrr_mem : ∀ tu : I × I,
      (1/2 - max (|(tu.1 : ℝ) - 1/2|) ((tu.2 : ℝ)/2)) ∈ Set.Icc (0 : ℝ) 1 := by
    intro tu
    have h1 : |(tu.1 : ℝ) - 1/2| ≤ 1/2 := by
      rw [abs_le]
      exact ⟨by linarith [unitInterval.nonneg tu.1], by linarith [unitInterval.le_one tu.1]⟩
    have h2 : (tu.2 : ℝ)/2 ≤ 1/2 := by linarith [unitInterval.le_one tu.2]
    have h4 : (0 : ℝ) ≤ |(tu.1 : ℝ) - 1/2| := abs_nonneg _
    rw [Set.mem_Icc]
    exact ⟨by linarith [max_le h1 h2],
      by linarith [h4, le_max_left (|(tu.1 : ℝ) - 1/2|) ((tu.2 : ℝ)/2)]⟩
  let ρ : C(I × I, I) :=
    ⟨fun tu => Set.projIcc 0 1 zero_le_one (1/2 - max (|(tu.1 : ℝ) - 1/2|) ((tu.2 : ℝ)/2)),
      continuous_projIcc.comp (by fun_prop)⟩
  have hρ_coe : ∀ tu : I × I,
      (ρ tu : ℝ) = 1/2 - max (|(tu.1 : ℝ) - 1/2|) ((tu.2 : ℝ)/2) := by
    intro tu
    show (Set.projIcc (0 : ℝ) 1 zero_le_one
        (1/2 - max (|(tu.1 : ℝ) - 1/2|) ((tu.2 : ℝ)/2)) : ℝ) = _
    rw [Set.projIcc_of_mem _ (hrr_mem tu)]
  let K : C(A × (I × I), X) := ⟨fun q => k (ρ q.2, iX q.1),
    (map_continuous k).comp ((ρ.continuous.comp continuous_snd).prodMk
      ((map_continuous iX).comp continuous_fst))⟩
  have hKapp : ∀ (a : A) (tu : I × I), K (a, tu) = k (ρ tu, iX a) := fun _ _ => rfl
  -- Bottom edge `u = 0`: `K(a, (t, 0)) = k_t(iX a)` (palindrome for `t ≥ ½`).
  have hbot : ∀ (a : A) (t : I), K (a, (t, 0)) = k (t, iX a) := by
    intro a t
    rw [hKapp]
    rcases le_total ((t : ℝ)) (1/2) with ht | ht
    · have hρ0 : ρ (t, 0) = t := by
        apply Subtype.ext
        rw [hρ_coe]
        show 1/2 - max (|(t : ℝ) - 1/2|) (((0 : I) : ℝ)/2) = (t : ℝ)
        rw [c0, zero_div, abs_of_nonpos (by linarith : (t : ℝ) - 1/2 ≤ 0),
          max_eq_left (by linarith)]
        ring
      rw [hρ0]
    · have hρ0 : ρ (t, 0) = σ t := by
        apply Subtype.ext
        rw [hρ_coe, unitInterval.coe_symm_eq]
        show 1/2 - max (|(t : ℝ) - 1/2|) (((0 : I) : ℝ)/2) = 1 - (t : ℝ)
        rw [c0, zero_div, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (t : ℝ) - 1/2),
          max_eq_left (by linarith)]
        ring
      rw [hρ0]; exact (hpal a t).symm
  -- The three other edges collapse to `iX a` (there `ρ = 0`).
  have hedge0 : ∀ tu : I × I, (tu.1 = 0 ∨ tu.1 = 1 ∨ tu.2 = 1) → ρ tu = 0 := by
    rintro ⟨t, u⟩ hcase
    apply Subtype.ext
    rw [hρ_coe]
    show 1/2 - max (|(t : ℝ) - 1/2|) ((u : ℝ)/2) = ((0 : I) : ℝ)
    rw [c0]
    have habs : |(t : ℝ) - 1/2| ≤ 1/2 := by
      rw [abs_le]
      exact ⟨by linarith [unitInterval.nonneg t], by linarith [unitInterval.le_one t]⟩
    have hu2 : (u : ℝ)/2 ≤ 1/2 := by linarith [unitInterval.le_one u]
    have hmax : max (|(t : ℝ) - 1/2|) ((u : ℝ)/2) = 1/2 := by
      apply le_antisymm (max_le habs hu2)
      rcases hcase with h | h | h
      · rw [show t = (0 : I) from h]; refine le_max_of_le_left ?_
        rw [c0, abs_of_nonpos (by norm_num : (0 : ℝ) - 1/2 ≤ 0)]; norm_num
      · rw [show t = (1 : I) from h]; refine le_max_of_le_left ?_
        rw [c1, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ) - 1/2)]; norm_num
      · rw [show u = (1 : I) from h]; refine le_max_of_le_right ?_
        rw [c1]
    rw [hmax]; norm_num
  have hedgeval : ∀ (a : A) (tu : I × I), (tu.1 = 0 ∨ tu.1 = 1 ∨ tu.2 = 1) →
      K (a, tu) = iX a := by
    intro a tu hcase
    rw [hKapp, hedge0 tu hcase]
    exact (k.map_zero_left (iX a)).trans (hp a)
  -- Extend `K` over `X` by the HEP for `(X × I, A × I)`.
  let φhep : C(X × I, X) := ⟨fun xt => k (xt.2, xt.1),
    (map_continuous k).comp (continuous_snd.prodMk continuous_fst)⟩
  let hh : C((A × I) × I, X) := ⟨fun q => K (q.1.1, (q.1.2, q.2)),
    (map_continuous K).comp (by fun_prop)⟩
  have hcompat : ∀ q : A × I, hh (q, 0) = φhep ((iX.prodMap (ContinuousMap.id I)) q) := by
    intro q
    obtain ⟨a, t⟩ := q
    show K (a, (t, 0)) = k (t, iX a)
    exact hbot a t
  obtain ⟨F, hF0, hFA⟩ := hHEP.prodMap_id φhep hh hcompat
  -- `F ((x, t), u)` with the bottom row `k_t` and the `A`-fibres given by `K`.
  have hFbot : ∀ (x : X) (t : I), F ((x, t), 0) = k (t, x) := fun x t => hF0 (x, t)
  have hFside : ∀ (a : A) (t u : I), F ((iX a, t), u) = K (a, (t, u)) :=
    fun a t u => hFA (a, t) u
  -- The three edge homotopies of maps `X → X`, each rel `A`.
  let q1 : C(X, X) := ⟨fun x => F ((x, 0), 1), by fun_prop⟩
  let q2 : C(X, X) := ⟨fun x => F ((x, 1), 1), by fun_prop⟩
  -- Left edge: `p ≃ q1` rel `A`.
  let HL : ContinuousMap.HomotopyRel p q1 (Set.range iX) :=
    { toContinuousMap := ⟨fun sx => F ((sx.2, 0), sx.1), by fun_prop⟩
      map_zero_left := fun x => by
        show F ((x, 0), 0) = p x
        rw [hFbot x 0]; exact k.map_zero_left x
      map_one_left := fun _ => rfl
      prop' := by
        rintro s x ⟨a, rfl⟩
        show F ((iX a, 0), s) = p (iX a)
        rw [hFside a 0 s, hedgeval a (0, s) (Or.inl rfl)]
        exact (hp a).symm }
  -- Top edge: `q1 ≃ q2` rel `A`.
  let HT : ContinuousMap.HomotopyRel q1 q2 (Set.range iX) :=
    { toContinuousMap := ⟨fun sx => F ((sx.2, sx.1), 1), by fun_prop⟩
      map_zero_left := fun _ => rfl
      map_one_left := fun _ => rfl
      prop' := by
        rintro s x ⟨a, rfl⟩
        show F ((iX a, s), 1) = q1 (iX a)
        rw [hFside a s 1, hedgeval a (s, 1) (Or.inr (Or.inr rfl))]
        show iX a = F ((iX a, 0), 1)
        rw [hFside a 0 1, hedgeval a (0, 1) (Or.inl rfl)] }
  -- Right edge (reversed): `q2 ≃ 𝟙_X` rel `A`.
  let HR : ContinuousMap.HomotopyRel q2 (ContinuousMap.id X) (Set.range iX) :=
    { toContinuousMap := ⟨fun sx => F ((sx.2, 1), σ sx.1), by fun_prop⟩
      map_zero_left := fun x => by
        show F ((x, 1), σ (0 : I)) = F ((x, 1), (1 : I))
        rw [sz]
      map_one_left := fun x => by
        show F ((x, 1), σ (1 : I)) = x
        rw [so, hFbot x 1]; exact k.map_one_left x
      prop' := by
        rintro s x ⟨a, rfl⟩
        show F ((iX a, 1), σ s) = q2 (iX a)
        rw [hFside a 1 (σ s), hedgeval a (1, σ s) (Or.inr (Or.inl rfl))]
        show iX a = F ((iX a, 1), 1)
        rw [hFside a 1 1, hedgeval a (1, 1) (Or.inr (Or.inl rfl))] }
  exact ⟨(HL.trans HT).trans HR⟩

end Step2

section Main

variable {A X Y : Type u} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]

/-- Precompose a rel-`S` homotopy `f₀ ≃ f₁` (of maps `B → C`) with a fixed map
`m : A → B` carrying `T` into `S`, giving `f₀ ∘ m ≃ f₁ ∘ m` rel `T`. (mathlib has the
post-composition version `HomotopyRel.compContinuousMap` but not this one.) -/
def homotopyRelPrecomp {B C : Type u} [TopologicalSpace B] [TopologicalSpace C]
    {f₀ f₁ : C(B, C)} {S : Set B} (F : f₀.HomotopyRel f₁ S) (m : C(A, B)) {T : Set A}
    (hm : ∀ a ∈ T, m a ∈ S) : (f₀.comp m).HomotopyRel (f₁.comp m) T where
  toContinuousMap := ⟨fun sa => F (sa.1, m sa.2),
    (map_continuous F).comp (continuous_fst.prodMk ((map_continuous m).comp continuous_snd))⟩
  map_zero_left a := F.map_zero_left (m a)
  map_one_left a := F.map_one_left (m a)
  prop' s a ha := F.eq_fst s (hm a ha)

/-- **Steps 1–2 of Prop 0.19.** Suppose `(X, A)` and `(Y, A)` have the HEP,
`f : X → Y` restricts to the identity on `A` (`f ∘ iX = iY`), and `g : Y → X` is a
homotopy inverse from the left (`g ∘ f ≃ 𝟙_X` via `h`). Then there is `g₁ : Y → X`
homotopic to `g`, restricting to the identity on `A`, with `g₁ ∘ f ≃ 𝟙_X` rel `A`. -/
theorem hep_step12 (iX : C(A, X)) (iY : C(A, Y)) (hX : HasHEPMap iX) (hY : HasHEPMap iY)
    (f : C(X, Y)) (hf : ∀ a, f (iX a) = iY a) (g : C(Y, X))
    (h : (g.comp f).Homotopy (ContinuousMap.id X)) :
    ∃ g₁ : C(Y, X), (∀ a, g₁ (iY a) = iX a) ∧
      Nonempty ((g₁.comp f).HomotopyRel (ContinuousMap.id X) (Set.range iX)) ∧
      g.Homotopic g₁ := by
  have sz : σ (0 : I) = 1 := by simp
  have so : σ (1 : I) = 0 := by simp
  -- Step 1: extend `h|_A` (a homotopy of `g|_A`) over `Y` by the HEP for `(Y, A)`.
  let hh : C(A × I, X) := ⟨fun p => h (p.2, iX p.1),
    (map_continuous h).comp (continuous_snd.prodMk ((map_continuous iX).comp continuous_fst))⟩
  have hcompat0 : ∀ a : A, hh (a, 0) = g (iY a) := fun a => by
    show h ((0 : I), iX a) = g (iY a)
    rw [show h ((0 : I), iX a) = g (f (iX a)) from h.map_zero_left (iX a), hf]
  obtain ⟨G, hG0, hGiY⟩ := hY g hh hcompat0
  have hGiY' : ∀ (a : A) (t : I), G (iY a, t) = h (t, iX a) := fun a t => hGiY a t
  let g₁ : C(Y, X) := ⟨fun y => G (y, 1),
    (map_continuous G).comp (continuous_id.prodMk continuous_const)⟩
  have hg1A : ∀ a, g₁ (iY a) = iX a := fun a => by
    show G (iY a, 1) = iX a
    rw [hGiY' a 1]; exact h.map_one_left (iX a)
  have hgg1 : g.Homotopic g₁ :=
    ⟨{ toContinuousMap := ⟨fun sy => G (sy.2, sy.1),
        (map_continuous G).comp (continuous_snd.prodMk continuous_fst)⟩
       map_zero_left := fun y => hG0 y
       map_one_left := fun _ => rfl }⟩
  -- Step 2: the palindromic homotopy `k : g₁ ∘ f ≃ 𝟙_X`.
  let P : (g₁.comp f).Homotopy (g.comp f) :=
    { toContinuousMap := ⟨fun τx => G (f τx.2, σ τx.1),
        (map_continuous G).comp (((map_continuous f).comp continuous_snd).prodMk
          (unitInterval.continuous_symm.comp continuous_fst))⟩
      map_zero_left := fun x => by
        show G (f x, σ (0 : I)) = G (f x, (1 : I)); rw [sz]
      map_one_left := fun x => by
        show G (f x, σ (1 : I)) = g (f x); rw [so]; exact hG0 (f x) }
  let k : (g₁.comp f).Homotopy (ContinuousMap.id X) := P.trans h
  have hPA : ∀ (a : A) (τ : I), P (τ, iX a) = h (σ τ, iX a) := fun a τ => by
    show G (f (iX a), σ τ) = h (σ τ, iX a)
    rw [hf]; exact hGiY' a (σ τ)
  -- On `A`, `k` retraces itself: `k(s, iX a) = h(⟨|2s - 1|, _⟩, iX a)` (tent parameter).
  have habs : ∀ s : I, |2*(s : ℝ) - 1| ∈ Set.Icc (0 : ℝ) 1 := by
    intro s
    rw [Set.mem_Icc]
    refine ⟨abs_nonneg _, ?_⟩
    rw [abs_le]
    exact ⟨by linarith [unitInterval.nonneg s], by linarith [unitInterval.le_one s]⟩
  have kA : ∀ (a : A) (s : I), k (s, iX a) = h (⟨|2*(s : ℝ) - 1|, habs s⟩, iX a) := by
    intro a s
    show (P.trans h) (s, iX a) = h (⟨|2*(s : ℝ) - 1|, habs s⟩, iX a)
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs with hs
    · rw [hPA]
      refine congrArg (fun p => h (p, iX a)) (Subtype.ext ?_)
      rw [unitInterval.coe_symm_eq]
      show 1 - 2*(s : ℝ) = |2*(s : ℝ) - 1|
      rw [abs_of_nonpos (by linarith : 2*(s : ℝ) - 1 ≤ 0)]; ring
    · refine congrArg (fun p => h (p, iX a)) (Subtype.ext ?_)
      show 2*(s : ℝ) - 1 = |2*(s : ℝ) - 1|
      rw [abs_of_nonneg (by linarith [not_le.mp hs] : (0 : ℝ) ≤ 2*(s : ℝ) - 1)]
  have hpal : ∀ (a : A) (s : I), k (s, iX a) = k (σ s, iX a) := by
    intro a s
    rw [kA a s, kA a (σ s)]
    have harg : |2*((σ s : I) : ℝ) - 1| = |2*(s : ℝ) - 1| := by
      rw [unitInterval.coe_symm_eq, show 2*(1 - (s : ℝ)) - 1 = -(2*(s : ℝ) - 1) by ring, abs_neg]
    exact congrArg (fun p => h (p, iX a)) (Subtype.ext harg.symm)
  obtain ⟨Hrel⟩ := step2_core iX (g₁.comp f) k hpal hX
  exact ⟨g₁, hg1A, ⟨Hrel⟩, hgg1⟩

/-- **Proposition 0.19 (Hatcher).** Suppose `(X, A)` and `(Y, A)` have the homotopy
extension property (via inclusions `iX : A → X`, `iY : A → Y`), and `f : X → Y` is a
homotopy equivalence restricting to the identity on `A` (`f ∘ iX = iY`). Then `f` is a
homotopy equivalence **rel `A`**: there is a homotopy inverse `g' : Y → X` with
`g' ∘ iY = iX`, and homotopies `g' ∘ f ≃ 𝟙_X` and `f ∘ g' ≃ 𝟙_Y` that are constant on
`A` at all times.

The proof runs Hatcher's three steps: `hep_step12` produces `g₁` with `g₁ f ≃ 𝟙 rel A`
and `g₁|_A = 𝟙`; applying it again with the roles of `f` and `g₁` swapped yields `f₁`
with `f₁ g₁ ≃ 𝟙 rel A`; then `f ≃ f₁ rel A` (`f₁ ≃ f₁(g₁ f) = (f₁ g₁)f ≃ f`), whence
`f g₁ ≃ f₁ g₁ ≃ 𝟙 rel A`. -/
theorem hep_homotopy_equiv_rel (iX : C(A, X)) (iY : C(A, Y))
    (hX : HasHEPMap iX) (hY : HasHEPMap iY)
    (f : C(X, Y)) (hf : ∀ a, f (iX a) = iY a) (g : C(Y, X))
    (hgf : (g.comp f).Homotopic (ContinuousMap.id X))
    (hfg : (f.comp g).Homotopic (ContinuousMap.id Y)) :
    ∃ g' : C(Y, X), (∀ a, g' (iY a) = iX a) ∧
      Nonempty ((g'.comp f).HomotopyRel (ContinuousMap.id X) (Set.range iX)) ∧
      Nonempty ((f.comp g').HomotopyRel (ContinuousMap.id Y) (Set.range iY)) := by
  obtain ⟨h⟩ := hgf
  -- First application: `g₁` with `g₁|_A = 𝟙`, `g₁ f ≃ 𝟙_X rel A`, `g ≃ g₁`.
  obtain ⟨g₁, hg1A, ⟨hrel1⟩, hgg1⟩ := hep_step12 iX iY hX hY f hf g h
  -- `f g₁ ≃ 𝟙_Y` (plain), a left homotopy inverse for the swapped application.
  have hfg1 : (f.comp g₁).Homotopic (ContinuousMap.id Y) :=
    ((Homotopic.refl f).comp hgg1).symm.trans hfg
  obtain ⟨h'⟩ := hfg1
  -- Second application, roles of `f` and `g₁` swapped: `f₁` with `f₁ g₁ ≃ 𝟙_Y rel A`.
  obtain ⟨f₁, hf1A, ⟨hrel2⟩, -⟩ := hep_step12 iY iX hY hX g₁ hg1A f h'
  have hmXY : ∀ x ∈ Set.range iX, f x ∈ Set.range iY := by
    rintro x ⟨a, rfl⟩; exact ⟨a, (hf a).symm⟩
  have hmYX : ∀ y ∈ Set.range iY, g₁ y ∈ Set.range iX := by
    rintro y ⟨a, rfl⟩; exact ⟨a, (hg1A a).symm⟩
  -- `f₁ (g₁ f) ≃ f₁ rel A` and `(f₁ g₁) f ≃ f rel A`.
  let A1 : (f₁.comp (g₁.comp f)).HomotopyRel f₁ (Set.range iX) :=
    (hrel1.compContinuousMap f₁).cast rfl (ContinuousMap.comp_id f₁)
  let B1 : (f₁.comp (g₁.comp f)).HomotopyRel f (Set.range iX) :=
    (homotopyRelPrecomp hrel2 f hmXY).cast
      (ContinuousMap.comp_assoc f₁ g₁ f) (ContinuousMap.id_comp f)
  -- `f ≃ f₁ rel A`, hence `f g₁ ≃ f₁ g₁ ≃ 𝟙_Y rel A`.
  have hffrel : f.HomotopyRel f₁ (Set.range iX) := B1.symm.trans A1
  exact ⟨g₁, hg1A, ⟨hrel1⟩,
    ⟨(homotopyRelPrecomp hffrel g₁ hmYX).trans hrel2⟩⟩

/-- The identity map always has the homotopy extension property (extend by the given
homotopy itself). -/
theorem hasHEPMap_id : HasHEPMap (ContinuousMap.id A) := by
  intro Z _ φ h hcompat
  exact ⟨h, hcompat, fun _ _ => rfl⟩

/-- **Corollary 0.20 (Hatcher).** If `(X, A)` has the homotopy extension property and
the inclusion `iX : A → X` is a homotopy equivalence, then `A` is a deformation retract
of `X`: there is a retraction `r : X → A` (`r ∘ iX = 𝟙_A`) with `iX ∘ r ≃ 𝟙_X` rel `A`.

This is `hep_homotopy_equiv_rel` applied to the inclusion `iX : A → X`, viewed as a
map of the pair `(A, A)` to `(X, A)` (the `A`-side inclusion being `𝟙_A`). -/
theorem hep_inclusion_deformation_retract (iX : C(A, X)) (hX : HasHEPMap iX)
    (g : C(X, A)) (hgi : (g.comp iX).Homotopic (ContinuousMap.id A))
    (hig : (iX.comp g).Homotopic (ContinuousMap.id X)) :
    ∃ r : C(X, A), (∀ a, r (iX a) = a) ∧
      Nonempty ((iX.comp r).HomotopyRel (ContinuousMap.id X) (Set.range iX)) := by
  obtain ⟨r, hrA, -, hrelX⟩ := hep_homotopy_equiv_rel (ContinuousMap.id A) iX
    hasHEPMap_id hX iX (fun _ => rfl) g hgi hig
  exact ⟨r, hrA, hrelX⟩

end Main

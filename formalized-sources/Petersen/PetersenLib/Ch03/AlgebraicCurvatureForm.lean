import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Algebraic curvature forms — pure linear-algebra core (Petersen §3.1)

Petersen §3.1.3 (Prop. 3.1.3, do Carmo Ch. 4 §3) observes that the sectional
curvature `sec(v,w) = g(R(w,v)v,w) / g(v∧w,v∧w)` determines the whole curvature
tensor `R`, and that this is "a purely algebraic fact". This file formalises
that algebraic layer over an arbitrary real vector space `V` — **not** an
inner-product space: Petersen's `TangentSpace I p` carries no inner-product
instance, so wherever do Carmo's algebraic core uses `⟨x,y⟩` we instead take an
abstract symmetric bilinear pairing `G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` (standing in for the
metric `g`) as an explicit argument.

* `IsAlgCurvatureForm` — a quadrilinear form `B : V⁴ → ℝ` with the four
  symmetries of do Carmo Prop. 2.5 / Petersen's curvature-symmetry properties
  (antisymmetry in each pair, and the first Bianchi identity); the pair-swap
  symmetry is *derived* (`IsAlgCurvatureForm.pairSwap`).
* `IsAlgCurvatureForm.ext` — the algebraic core of do Carmo Ch. 4, Lemma 3.3 /
  Petersen Prop. 3.1.3 (1)⇒(2): two algebraic curvature forms with the same
  diagonal values `B(x,y,x,y)` are equal (the polarization argument).
* `bivectorPairing` — Petersen's bivector inner product
  `g(x∧y,v∧w) = g(x,v)g(y,w) − g(x,w)g(y,v)` (`def:pet-ch3-bivector-inner-product`),
  taken here with respect to an abstract symmetric bilinear form `G` in place
  of `g`; `wedgeGramSq` is its diagonal, the squared area `|x∧y|²`.
* `isAlgCurvatureForm_bivectorPairing` — the model curvature form
  `R_G(x,y,z,t) = G(x,z)G(y,t) − G(x,t)G(y,z) = g(x∧y,z∧t)` (Petersen's `R_k`
  with `k = 1`, do Carmo's `stdCurvForm`) is an algebraic curvature form.
* `IsAlgCurvatureForm.eq_smul_bivectorPairing_of_const` — do Carmo Ch. 4,
  Lemma 3.4 / Petersen Prop. 3.1.3 (1)⇒(2): constant "curvature" `k` (i.e.
  `B(x,y,x,y) = k·g(x∧y,x∧y)` for all `x,y`) forces `B = k·R_G`.
* `IsAlgCurvatureForm.bilin_det_12`, `bilin_det_34`, `diag_changeBasis` — the
  determinant-reduction identities behind do Carmo Prop. 3.1 / the basis
  independence of sectional curvature, pure consequences of the
  `IsAlgCurvatureForm` axioms (no pairing needed).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.2–§3.1.3;
do Carmo, *Riemannian Geometry*, Ch. 4 §3.
-/

noncomputable section

namespace PetersenLib

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen §3.1.3 / do Carmo Ch. 4, Prop. 2.5 abstracted: an
**algebraic curvature form** on a real vector space `V` is a map
`B : V⁴ → ℝ` that is additive and `ℝ`-homogeneous in its first slot and
satisfies the three defining symmetries — antisymmetry in the first pair
`(X,Y,Z,T) = −(Y,X,Z,T)` (b), antisymmetry in the second pair
`(X,Y,Z,T) = −(X,Y,T,Z)` (c), and the first Bianchi identity
`(X,Y,Z,T)+(Y,Z,X,T)+(Z,X,Y,T)=0` (a). The full multilinearity and the
pair-swap symmetry (d) are consequences (see below). -/
structure IsAlgCurvatureForm (B : V → V → V → V → ℝ) : Prop where
  /-- additivity in the first slot -/
  add_left : ∀ x₁ x₂ y z t, B (x₁ + x₂) y z t = B x₁ y z t + B x₂ y z t
  /-- `ℝ`-homogeneity in the first slot -/
  smul_left : ∀ (a : ℝ) x y z t, B (a • x) y z t = a * B x y z t
  /-- antisymmetry in the first pair (do Carmo Prop. 2.5(b)) -/
  antisymm₁₂ : ∀ x y z t, B x y z t = - B y x z t
  /-- antisymmetry in the second pair (do Carmo Prop. 2.5(c)) -/
  antisymm₃₄ : ∀ x y z t, B x y z t = - B x y t z
  /-- first Bianchi identity (do Carmo Prop. 2.5(a)) -/
  bianchi : ∀ x y z t, B x y z t + B y z x t + B z x y t = 0

namespace IsAlgCurvatureForm

variable {B B' : V → V → V → V → ℝ}

/-- **Math.** do Carmo Ch. 4, Prop. 2.5(d) — **pair-swap symmetry**
`(X,Y,Z,T) = (Z,T,X,Y)`, derived from (a), (b), (c): sum the four cyclic
Bianchi identities and cancel using (b) and (c). -/
theorem pairSwap (hB : IsAlgCurvatureForm B) (x y z t : V) :
    B x y z t = B z t x y := by
  have Eq1 := hB.bianchi y z x t
  have Eq2 := hB.bianchi z x t y
  have Eq3 := hB.bianchi x t y z
  have Eq4 := hB.bianchi t y z x
  have ar1 := hB.antisymm₃₄ y z x t
  have ar2 := hB.antisymm₃₄ z x y t
  have ar3 := hB.antisymm₃₄ x t z y
  have ar4 := hB.antisymm₃₄ t y z x
  have ar5 := hB.antisymm₃₄ x y z t
  have ar6 := hB.antisymm₃₄ t z x y
  have al5 := hB.antisymm₁₂ y x t z
  have al6 := hB.antisymm₁₂ z t y x
  have al7 := hB.antisymm₁₂ t z x y
  linarith [Eq1, Eq2, Eq3, Eq4, ar1, ar2, ar3, ar4, ar5, ar6, al5, al6, al7]

/-- Additivity in the second slot. -/
theorem add_two (hB : IsAlgCurvatureForm B) (x y₁ y₂ z t : V) :
    B x (y₁ + y₂) z t = B x y₁ z t + B x y₂ z t := by
  rw [hB.antisymm₁₂ x (y₁ + y₂), hB.add_left, hB.antisymm₁₂ y₁ x, hB.antisymm₁₂ y₂ x]
  ring

/-- Additivity in the third slot. -/
theorem add_three (hB : IsAlgCurvatureForm B) (x y z₁ z₂ t : V) :
    B x y (z₁ + z₂) t = B x y z₁ t + B x y z₂ t := by
  rw [hB.pairSwap x y (z₁ + z₂) t, hB.add_left, hB.pairSwap z₁ t x y, hB.pairSwap z₂ t x y]

/-- Additivity in the fourth slot. -/
theorem add_four (hB : IsAlgCurvatureForm B) (x y z t₁ t₂ : V) :
    B x y z (t₁ + t₂) = B x y z t₁ + B x y z t₂ := by
  rw [hB.antisymm₃₄ x y z (t₁ + t₂), hB.add_three, hB.antisymm₃₄ x y t₁ z,
    hB.antisymm₃₄ x y t₂ z]
  ring

/-- Homogeneity in the second slot. -/
theorem smul_two (hB : IsAlgCurvatureForm B) (a : ℝ) (x y z t : V) :
    B x (a • y) z t = a * B x y z t := by
  rw [hB.antisymm₁₂ x (a • y), hB.smul_left, hB.antisymm₁₂ y x]; ring

/-- Homogeneity in the third slot. -/
theorem smul_three (hB : IsAlgCurvatureForm B) (a : ℝ) (x y z t : V) :
    B x y (a • z) t = a * B x y z t := by
  rw [hB.pairSwap x y (a • z) t, hB.smul_left, hB.pairSwap z t x y]

/-- Homogeneity in the fourth slot. -/
theorem smul_four (hB : IsAlgCurvatureForm B) (a : ℝ) (x y z t : V) :
    B x y z (a • t) = a * B x y z t := by
  rw [hB.antisymm₃₄ x y z (a • t), hB.smul_three, hB.antisymm₃₄ x y t z]; ring

/-- `B` vanishes when its first pair is repeated. -/
theorem self_left (hB : IsAlgCurvatureForm B) (x z t : V) : B x x z t = 0 := by
  have h := hB.antisymm₁₂ x x z t; linarith

/-- `B` vanishes when its second pair is repeated. -/
theorem self_right (hB : IsAlgCurvatureForm B) (x y z : V) : B x y z z = 0 := by
  have h := hB.antisymm₃₄ x y z z; linarith

/-- The difference of two algebraic curvature forms is again one. -/
theorem sub (hB : IsAlgCurvatureForm B) (hB' : IsAlgCurvatureForm B') :
    IsAlgCurvatureForm (fun a b c e => B a b c e - B' a b c e) where
  add_left x₁ x₂ y z t := by simp only [hB.add_left, hB'.add_left]; ring
  smul_left a x y z t := by simp only [hB.smul_left, hB'.smul_left]; ring
  antisymm₁₂ x y z t := by simp only [hB.antisymm₁₂ x y, hB'.antisymm₁₂ x y]; ring
  antisymm₃₄ x y z t := by simp only [hB.antisymm₃₄ x y z, hB'.antisymm₃₄ x y z]; ring
  bianchi x y z t := by
    have hb := hB.bianchi x y z t
    have hb' := hB'.bianchi x y z t
    show B x y z t - B' x y z t + (B y z x t - B' y z x t) + (B z x y t - B' z x y t) = 0
    linarith

/-- A scalar multiple of an algebraic curvature form is again one. -/
theorem smul (hB : IsAlgCurvatureForm B) (c : ℝ) :
    IsAlgCurvatureForm (fun x y z t => c * B x y z t) where
  add_left x₁ x₂ y z t := by simp only [hB.add_left]; ring
  smul_left a x y z t := by simp only [hB.smul_left]; ring
  antisymm₁₂ x y z t := by simp only [hB.antisymm₁₂ x y]; ring
  antisymm₃₄ x y z t := by simp only [hB.antisymm₃₄ x y z]; ring
  bianchi x y z t := by
    have hb := hB.bianchi x y z t
    show c * B x y z t + c * B y z x t + c * B z x y t = 0
    linear_combination c * hb

/-! ### Multilinearity in `Finset` sums, and basis determination -/

/-- `B` vanishes when its first slot is zero. -/
theorem zero_left (hB : IsAlgCurvatureForm B) (y z t : V) : B 0 y z t = 0 := by
  have h := hB.smul_left 0 y y z t; rw [zero_smul, zero_mul] at h; exact h

/-- `B` vanishes when its second slot is zero. -/
theorem zero_two (hB : IsAlgCurvatureForm B) (x z t : V) : B x 0 z t = 0 := by
  have h := hB.smul_two 0 x x z t; rw [zero_smul, zero_mul] at h; exact h

/-- `B` vanishes when its third slot is zero. -/
theorem zero_three (hB : IsAlgCurvatureForm B) (x y t : V) : B x y 0 t = 0 := by
  have h := hB.smul_three 0 x y y t; rw [zero_smul, zero_mul] at h; exact h

/-- `B` vanishes when its fourth slot is zero. -/
theorem zero_four (hB : IsAlgCurvatureForm B) (x y z : V) : B x y z 0 = 0 := by
  have h := hB.smul_four 0 x y z z; rw [zero_smul, zero_mul] at h; exact h

/-- Multilinear expansion of a `Finset`-sum in the first slot. -/
theorem sum_left (hB : IsAlgCurvatureForm B) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (g : ι → V) (y z t : V) :
    B (∑ i ∈ s, f i • g i) y z t = ∑ i ∈ s, f i * B (g i) y z t := by
  classical
  refine Finset.induction_on s (by simp [hB.zero_left]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hB.add_left, hB.smul_left, ih]

/-- Multilinear expansion of a `Finset`-sum in the second slot. -/
theorem sum_two (hB : IsAlgCurvatureForm B) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (g : ι → V) (x z t : V) :
    B x (∑ i ∈ s, f i • g i) z t = ∑ i ∈ s, f i * B x (g i) z t := by
  classical
  refine Finset.induction_on s (by simp [hB.zero_two]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hB.add_two, hB.smul_two, ih]

/-- Multilinear expansion of a `Finset`-sum in the third slot. -/
theorem sum_three (hB : IsAlgCurvatureForm B) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (g : ι → V) (x y t : V) :
    B x y (∑ i ∈ s, f i • g i) t = ∑ i ∈ s, f i * B x y (g i) t := by
  classical
  refine Finset.induction_on s (by simp [hB.zero_three]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hB.add_three, hB.smul_three, ih]

/-- Multilinear expansion of a `Finset`-sum in the fourth slot. -/
theorem sum_four (hB : IsAlgCurvatureForm B) {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (g : ι → V) (x y z : V) :
    B x y z (∑ i ∈ s, f i • g i) = ∑ i ∈ s, f i * B x y z (g i) := by
  classical
  refine Finset.induction_on s (by simp [hB.zero_four]) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha, Finset.sum_insert ha, hB.add_four, hB.smul_four, ih]

/-- **Math.** An algebraic curvature form is determined by its values on a basis:
if `B` vanishes on all basis 4-tuples `(b i, b j, b k, b l)`, it vanishes
identically. Expand each argument in the basis and use full multilinearity. -/
theorem eq_zero_of_basis (hB : IsAlgCurvatureForm B) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ V)
    (h0 : ∀ i j k l, B (b i) (b j) (b k) (b l) = 0) : ∀ x y z t, B x y z t = 0 := by
  intro x y z t
  conv_lhs => rw [← b.sum_repr x, ← b.sum_repr y, ← b.sum_repr z, ← b.sum_repr t]
  simp only [hB.sum_left, hB.sum_two, hB.sum_three, hB.sum_four, h0, mul_zero,
    Finset.sum_const_zero]

/-- **Math.** Two algebraic curvature forms agreeing on all basis 4-tuples are
equal — the finite-dimensional basis-determination lemma behind Petersen's
basis expansion of the curvature operator (`def:pet-ch3-curvature-operator`). -/
theorem ext_basis (hB : IsAlgCurvatureForm B) (hB' : IsAlgCurvatureForm B')
    {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ V)
    (h : ∀ i j k l, B (b i) (b j) (b k) (b l) = B' (b i) (b j) (b k) (b l)) :
    ∀ x y z t, B x y z t = B' x y z t := by
  have hd := hB.sub hB'
  have h0 : ∀ i j k l, (fun a e c d => B a e c d - B' a e c d) (b i) (b j) (b k) (b l) = 0 := by
    intro i j k l; simp only [h i j k l, sub_self]
  intro x y z t
  have := hd.eq_zero_of_basis b h0 x y z t
  simp only at this; linarith

/-- **Math.** Key step of do Carmo Ch. 4, Lemma 3.3: an algebraic curvature form
whose diagonal `B(x,y,x,y)` vanishes for all `x,y` is identically zero.
Polarize `B(x+z,y,x+z,y)=0` to get `B(x,y,z,y)=0`, then polarize
`B(x,y+t,z,y+t)=0` to obtain cyclic invariance in the first three arguments,
which with the Bianchi identity forces `3·B=0`. -/
theorem eq_zero_of_diag (hB : IsAlgCurvatureForm B)
    (h0 : ∀ x y, B x y x y = 0) : ∀ x y z t, B x y z t = 0 := by
  -- Step 1: `B x y z y = 0`.
  have step1 : ∀ x y z, B x y z y = 0 := by
    intro x y z
    have key := h0 (x + z) y
    rw [hB.add_left, hB.add_three, hB.add_three, h0 x y, h0 z y,
      hB.pairSwap z y x y] at key
    linarith
  -- Step 2: cyclic invariance `B x y z t = B y z x t`.
  have cyc : ∀ x y z t, B x y z t = B y z x t := by
    intro x y z t
    have key := step1 x (y + t) z
    rw [hB.add_two, hB.add_four, hB.add_four, step1 x y z, step1 x t z] at key
    have htr : B x t z y = - B y z x t := by
      rw [hB.pairSwap x t z y, hB.antisymm₁₂ z y x t]
    linarith [key, htr]
  intro x y z t
  have b := hB.bianchi x y z t
  have c1 := cyc x y z t
  have c2 := cyc y z x t
  linarith

/-- **Math.** do Carmo Ch. 4, **Lemma 3.3** / Petersen Prop. 3.1.3's algebraic
core: if two algebraic curvature forms `B`, `B'` agree on the diagonal —
i.e. `B(x,y,x,y) = B'(x,y,x,y)` for all `x,y` — then `B = B'`. Proved by
polarization (`eq_zero_of_diag` applied to the difference `B − B'`). -/
theorem ext (hB : IsAlgCurvatureForm B) (hB' : IsAlgCurvatureForm B')
    (hdiag : ∀ x y, B x y x y = B' x y x y) :
    ∀ x y z t, B x y z t = B' x y z t := by
  have hd := hB.sub hB'
  have h0 : ∀ x y, (fun a b c e => B a b c e - B' a b c e) x y x y = 0 := by
    intro x y; simp only [hdiag x y, sub_self]
  intro x y z t
  have := hd.eq_zero_of_diag h0 x y z t
  simp only at this; linarith

end IsAlgCurvatureForm

/-! ### The Petersen model form `g(x∧y,v∧w)` -/

/-- **Math.** Petersen §3.1.2, `def:pet-ch3-bivector-inner-product`: the
**inner product on bivectors**, `g(x∧y,v∧w) = g(x,v)g(y,w) − g(x,w)g(y,v)`, the
Gram determinant of `x,y` against `v,w`. Here `G : V →ₗ[ℝ] V →ₗ[ℝ] ℝ` stands in
for the (a priori unavailable) metric `g` on the plain module `V`. -/
def bivectorPairing (G : LinearMap.BilinForm ℝ V) (x y v w : V) : ℝ :=
  G x v * G y w - G x w * G y v

/-- **Math.** Petersen §3.1.3, `def:pet-ch3-sectional-curvature`: the squared
area `|x ∧ y|² = g(x∧y,x∧y)` of the parallelogram spanned by `x, y`, the
diagonal of `bivectorPairing`. -/
def wedgeGramSq (G : LinearMap.BilinForm ℝ V) (x y : V) : ℝ :=
  bivectorPairing G x y x y

/-- **Math.** Petersen Prop. 3.1.3, model form `R_k` with `k = 1` (do Carmo Ch. 4,
Lemma 3.4's `stdCurvForm`): the map `(x,y,z,t) ↦ g(x∧y,z∧t)` is an algebraic
curvature form, for any symmetric bilinear `G` standing in for `g`. Antisymmetry
in each pair holds for *any* `G` (it is the antisymmetry of a `2×2`
determinant); only the Bianchi identity uses symmetry of `G`. -/
theorem isAlgCurvatureForm_bivectorPairing (G : LinearMap.BilinForm ℝ V)
    (hG : ∀ a b, G a b = G b a) :
    IsAlgCurvatureForm (fun x y z t => bivectorPairing G x y z t) where
  add_left x₁ x₂ y z t := by
    simp only [bivectorPairing, map_add, LinearMap.add_apply]; ring
  smul_left a x y z t := by
    simp only [bivectorPairing, map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  antisymm₁₂ x y z t := by simp only [bivectorPairing]; ring
  antisymm₃₄ x y z t := by simp only [bivectorPairing]; ring
  bianchi x y z t := by
    simp only [bivectorPairing]
    rw [hG y x, hG z x, hG z y]
    ring

namespace IsAlgCurvatureForm

variable {B : V → V → V → V → ℝ}

/-- **Math.** do Carmo Ch. 4, **Lemma 3.4** / Petersen Prop. 3.1.3 (1)⇒(2): if
`B` has constant "curvature" `k` — meaning `B(x,y,x,y) = k·g(x∧y,x∧y)` for all
`x,y` — then `B = k·g(·∧·,·∧·)` everywhere. Both sides are algebraic curvature
forms agreeing on the diagonal, so `IsAlgCurvatureForm.ext` (Lemma 3.3) forces
equality. -/
theorem eq_smul_bivectorPairing_of_const (hB : IsAlgCurvatureForm B)
    (G : LinearMap.BilinForm ℝ V) (hG : ∀ a b, G a b = G b a) (k : ℝ)
    (hconst : ∀ x y, B x y x y = k * bivectorPairing G x y x y) :
    ∀ x y z t, B x y z t = k * bivectorPairing G x y z t := by
  have hB' := (isAlgCurvatureForm_bivectorPairing G hG).smul k
  exact hB.ext hB' hconst

/-- **Math.** do Carmo Ch. 4, Lemma 3.4 (`⇒`) / Petersen Prop. 3.1.3 (2)⇒(1):
`B = k·g(·∧·,·∧·)` gives the constant-diagonal identity `B(x,y,x,y) =
k·g(x∧y,x∧y)`, trivially by evaluating the hypothesis at `(x,y,x,y)`. -/
theorem const_of_eq_smul_bivectorPairing (G : LinearMap.BilinForm ℝ V) (k : ℝ)
    (h : ∀ x y z t, B x y z t = k * bivectorPairing G x y z t) (x y : V) :
    B x y x y = k * bivectorPairing G x y x y :=
  h x y x y

/-! ### Determinant reduction (basis independence of the sectional numerator) -/

/-- Determinant reduction in the first pair: `B(a·x+b·y, c·x+d·y, z, t) =
(ad−bc)·B(x,y,z,t)`, from antisymmetry in the first pair. -/
theorem bilin_det_12 (hB : IsAlgCurvatureForm B) (a b c d : ℝ) (x y z t : V) :
    B (a • x + b • y) (c • x + d • y) z t = (a * d - b * c) * B x y z t := by
  simp only [hB.add_left, hB.add_two, hB.smul_left, hB.smul_two, hB.self_left,
    hB.antisymm₁₂ y x z t]
  ring

/-- Determinant reduction in the second pair: `B(x, y, a·z+b·t, c·z+d·t) =
(ad−bc)·B(x,y,z,t)`, from antisymmetry in the second pair. -/
theorem bilin_det_34 (hB : IsAlgCurvatureForm B) (a b c d : ℝ) (x y z t : V) :
    B x y (a • z + b • t) (c • z + d • t) = (a * d - b * c) * B x y z t := by
  simp only [hB.add_three, hB.add_four, hB.smul_three, hB.smul_four, hB.self_right,
    hB.antisymm₃₄ x y t z]
  ring

/-- **Math.** The diagonal `B(x,y,x,y)` scales by the square of the determinant
under a linear change of the spanning pair: with `x' = a·x+b·y`, `y' = c·x+d·y`,
`B(x',y',x',y') = (ad−bc)²·B(x,y,x,y)`. This is the antisymmetry (determinant)
identity behind the basis independence of Petersen's sectional curvature
(Prop. 3.1.3, `def:pet-ch3-sectional-curvature`). -/
theorem diag_changeBasis (hB : IsAlgCurvatureForm B) (a b c d : ℝ) (x y : V) :
    B (a • x + b • y) (c • x + d • y) (a • x + b • y) (c • x + d • y)
      = (a * d - b * c) ^ 2 * B x y x y := by
  rw [hB.bilin_det_12, hB.bilin_det_34]; ring

end IsAlgCurvatureForm

end PetersenLib

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# do Carmo Chapter 4 §3 — sectional curvature (algebraic core)

do Carmo introduces the **sectional curvature**
`K(x,y) = ⟨R(x,y)x,y⟩ / |x ∧ y|²` and observes that the fact that `K`
determines the whole curvature tensor `R` is "a purely algebraic fact"
(`lem:dc-ch4-3-3`). This file formalises exactly that algebraic layer, over an
arbitrary real inner product space `V`:

* `IsAlgCurvatureForm` — a quadrilinear form `B : V⁴ → ℝ` with do Carmo's four
  symmetries of `prop:dc-ch4-2-5` (antisymmetry in each pair, and the first
  Bianchi identity); the pair-swap symmetry is *derived*
  (`IsAlgCurvatureForm.pairSwap`).
* `IsAlgCurvatureForm.ext` — do Carmo Ch. 4, Lemma 3.3: two algebraic curvature
  forms with the same sectional curvature are equal (the polarization argument).
* `wedgeSq`, `sectionalCurvature` — the area `|x ∧ y|²` and `K` (`def:dc-ch4-3-2`),
  with `wedgeSq_nonneg` and `wedgeSq_pos_iff_linearIndependent` (strict
  Cauchy–Schwarz).
* `stdCurvForm` — the constant-curvature model `R'` of `lem:dc-ch4-3-4`,
  `⟨x,z⟩⟨y,t⟩ − ⟨y,z⟩⟨x,t⟩`, shown to be an `IsAlgCurvatureForm`.
* `IsAlgCurvatureForm.eq_smul_stdCurvForm_of_const` — do Carmo Ch. 4, Lemma 3.4:
  constant sectional curvature `K₀` iff `R = K₀ R'`.
* `sectionalCurvature_changeBasis` — do Carmo Ch. 4, Prop. 3.1: `K` is unchanged
  under an invertible linear change of the spanning pair (basis independence).

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §3.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Math.** do Carmo Ch. 4, Prop. 2.5 abstracted: an **algebraic curvature
form** on a real inner product space `V` is a map `B : V⁴ → ℝ` that is additive
and `ℝ`-homogeneous in its first slot and satisfies the three defining
symmetries — antisymmetry in the first pair `(X,Y,Z,T) = −(Y,X,Z,T)` (b),
antisymmetry in the second pair `(X,Y,Z,T) = −(X,Y,T,Z)` (c), and the first
Bianchi identity `(X,Y,Z,T)+(Y,Z,X,T)+(Z,X,Y,T)=0` (a). The full multilinearity
and the pair-swap symmetry (d) are consequences (see below). -/
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
`(X,Y,Z,T) = (Z,T,X,Y)`, derived from (a), (b), (c) exactly as in the manifold
proof `curvatureForm_pairSwap`: sum the four cyclic Bianchi identities and cancel
using (b) and (c). -/
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
equal — the finite-dimensional basis-determination lemma behind
`cor:dc-ch4-3-5`. -/
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
whose sectional numerator `B(x,y,x,y)` vanishes for all `x,y` is identically
zero. Polarize `B(x+z,y,x+z,y)=0` to get `B(x,y,z,y)=0`, then polarize
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

/-- **Math.** do Carmo Ch. 4, **Lemma 3.3**: if two algebraic curvature forms `B`,
`B'` induce the same sectional curvature — i.e. `B(x,y,x,y) = B'(x,y,x,y)` for all
`x,y` — then `B = B'`. This is do Carmo's "purely algebraic fact", proved by
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

/-! ### The area form `|x ∧ y|²` and the sectional curvature -/

/-- **Math.** do Carmo Ch. 4 §3: the squared area `|x ∧ y|²` of the parallelogram
spanned by `x, y`, namely `⟨x,x⟩⟨y,y⟩ − ⟨x,y⟩²` (the Gram determinant). -/
def wedgeSq (x y : V) : ℝ :=
  (inner ℝ x x) * (inner ℝ y y) - (inner ℝ x y) * (inner ℝ x y)

/-- `|x ∧ y|² ≥ 0` (Cauchy–Schwarz). -/
theorem wedgeSq_nonneg (x y : V) : 0 ≤ wedgeSq x y := by
  have h := real_inner_mul_inner_self_le x y
  unfold wedgeSq; linarith

/-- **Math.** do Carmo Ch. 4 §3: `|x ∧ y|² > 0` iff `x, y` are linearly
independent (the strict Cauchy–Schwarz inequality). -/
theorem wedgeSq_pos_iff_linearIndependent (x y : V) :
    0 < wedgeSq x y ↔ LinearIndependent ℝ ![x, y] := by
  have hposdef : ∀ v : V, v ≠ 0 → 0 < (innerₗ V) v v := by
    intro v hv
    rw [innerₗ_apply_apply]
    exact real_inner_self_pos.mpr hv
  have h := LinearMap.BilinForm.apply_sq_lt_iff_linearIndependent_of_symm
    (innerₗ V) hposdef isSymm_inner x y
  rw [innerₗ_apply_apply, innerₗ_apply_apply, innerₗ_apply_apply] at h
  rw [← h]
  unfold wedgeSq
  constructor <;> intro hh <;> nlinarith [hh]

/-- **Math.** do Carmo Ch. 4, Def. 3.2: the **sectional curvature**
`K(x,y) = ⟨R(x,y)x,y⟩ / |x ∧ y|²` of the plane spanned by `x, y`, for an
algebraic curvature form `B` playing the role of `⟨R·,·⟩`. -/
def sectionalCurvature (B : V → V → V → V → ℝ) (x y : V) : ℝ :=
  B x y x y / wedgeSq x y

/-! ### The constant-curvature model `R'` (do Carmo Lemma 3.4) -/

/-- **Math.** do Carmo Ch. 4, Lemma 3.4: the model curvature form
`R'(x,y,z,t) = ⟨x,z⟩⟨y,t⟩ − ⟨y,z⟩⟨x,t⟩`, whose sectional curvature is constant
`1`. It is the algebraic curvature form of a space of constant curvature. -/
def stdCurvForm (x y z t : V) : ℝ :=
  (inner ℝ x z) * (inner ℝ y t) - (inner ℝ y z) * (inner ℝ x t)

/-- `R'(x,y,x,y) = |x ∧ y|²`. -/
theorem stdCurvForm_diag (x y : V) : stdCurvForm x y x y = wedgeSq x y := by
  unfold stdCurvForm wedgeSq
  rw [real_inner_comm y x]

/-- **Math.** do Carmo Ch. 4, Cor. 3.5 kernel: on an **orthonormal** family
`e`, the model form `R'` takes the Kronecker-delta values
`R'(eᵢ,eⱼ,eₖ,eₗ) = δᵢₖδⱼₗ − δᵢₗδⱼₖ`. -/
theorem stdCurvForm_orthonormal {ι : Type*} [DecidableEq ι] {e : ι → V}
    (he : Orthonormal ℝ e) (i j k l : ι) :
    stdCurvForm (e i) (e j) (e k) (e l)
      = (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0) := by
  have hite := orthonormal_iff_ite.mp he
  unfold stdCurvForm
  rw [hite i k, hite j l, hite j k, hite i l]; ring

/-- **Math.** The model form `R'` is an algebraic curvature form. -/
theorem isAlgCurvatureForm_stdCurvForm :
    IsAlgCurvatureForm (stdCurvForm (V := V)) where
  add_left x₁ x₂ y z t := by simp only [stdCurvForm, inner_add_left]; ring
  smul_left a x y z t := by simp only [stdCurvForm, real_inner_smul_left]; ring
  antisymm₁₂ x y z t := by simp only [stdCurvForm]; ring
  antisymm₃₄ x y z t := by simp only [stdCurvForm]; ring
  bianchi x y z t := by
    simp only [stdCurvForm]
    rw [real_inner_comm y x, real_inner_comm z x, real_inner_comm z y]
    ring

namespace IsAlgCurvatureForm

variable {B : V → V → V → V → ℝ}

/-- **Math.** do Carmo Ch. 4, **Lemma 3.4** (`⇐` of the algebraic content): if `B`
has constant sectional curvature `K₀` — meaning `B(x,y,x,y) = K₀·|x∧y|²` for all
`x,y` — then `B = K₀·R'`. Both sides are algebraic curvature forms agreeing on
the diagonal `(x,y,x,y)`, so `IsAlgCurvatureForm.ext` (Lemma 3.3) forces
equality. -/
theorem eq_smul_stdCurvForm_of_const (hB : IsAlgCurvatureForm B) (K₀ : ℝ)
    (hconst : ∀ x y, B x y x y = K₀ * wedgeSq x y) :
    ∀ x y z t, B x y z t = K₀ * stdCurvForm x y z t := by
  have hB' := (isAlgCurvatureForm_stdCurvForm (V := V)).smul K₀
  refine hB.ext hB' ?_
  intro x y
  rw [hconst x y, stdCurvForm_diag]

/-- **Math.** do Carmo Ch. 4, Lemma 3.4 (`⇒`): `B = K₀·R'` gives constant
sectional curvature. Conversely the diagonal identity `B(x,y,x,y) = K₀·|x∧y|²`
follows by `stdCurvForm_diag`. -/
theorem const_of_eq_smul_stdCurvForm (K₀ : ℝ)
    (h : ∀ x y z t, B x y z t = K₀ * stdCurvForm x y z t) (x y : V) :
    B x y x y = K₀ * wedgeSq x y := by
  rw [h x y x y, stdCurvForm_diag]

end IsAlgCurvatureForm

/-! ### Basis independence of the sectional curvature (do Carmo Prop. 3.1) -/

namespace IsAlgCurvatureForm

variable {B : V → V → V → V → ℝ}

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

/-- **Math.** The numerator `B(x,y,x,y)` scales by the square of the determinant
under a linear change of the spanning pair: with `x' = a·x+b·y`, `y' = c·x+d·y`,
`B(x',y',x',y') = (ad−bc)²·B(x,y,x,y)`. This is the antisymmetry (determinant)
identity behind do Carmo Prop. 3.1. -/
theorem diag_changeBasis (hB : IsAlgCurvatureForm B) (a b c d : ℝ) (x y : V) :
    B (a • x + b • y) (c • x + d • y) (a • x + b • y) (c • x + d • y)
      = (a * d - b * c) ^ 2 * B x y x y := by
  rw [hB.bilin_det_12, hB.bilin_det_34]; ring

/-- **Math.** do Carmo Ch. 4, **Prop. 3.1** — the sectional curvature depends only
on the plane, not on the chosen basis: for an invertible linear change of the
spanning pair `x' = a·x+b·y`, `y' = c·x+d·y` (with `ad−bc ≠ 0`) of a linearly
independent pair `x,y`, `K(x',y') = K(x,y)`. Both numerator and denominator scale
by `(ad−bc)²` (the latter because `|·∧·|²` is the diagonal of the algebraic
curvature form `R'`), so the ratio is unchanged. -/
theorem sectionalCurvature_changeBasis (hB : IsAlgCurvatureForm B)
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) (x y : V)
    (hxy : LinearIndependent ℝ ![x, y]) :
    sectionalCurvature B (a • x + b • y) (c • x + d • y) = sectionalCurvature B x y := by
  have hw : wedgeSq (a • x + b • y) (c • x + d • y) = (a * d - b * c) ^ 2 * wedgeSq x y := by
    rw [← stdCurvForm_diag, isAlgCurvatureForm_stdCurvForm.diag_changeBasis, stdCurvForm_diag]
  have hnum := hB.diag_changeBasis a b c d x y
  have hpos : 0 < wedgeSq x y := (wedgeSq_pos_iff_linearIndependent x y).mpr hxy
  have hdet2 : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  unfold sectionalCurvature
  rw [hnum, hw, mul_div_mul_left _ _ hdet2]

/-! ### Constant curvature in an orthonormal basis (do Carmo Cor. 3.5) -/

/-- **Math.** do Carmo Ch. 4, **Cor. 3.5**: for an orthonormal basis
`{e₁,…,eₙ}` of `T_pM`, the algebraic curvature form `B` has constant sectional
curvature `K₀` (i.e. `B(x,y,x,y) = K₀·|x∧y|²` for all `x,y`, equivalently
`K(p,σ) = K₀` for every plane `σ`) **iff** its components in the basis have the
Kronecker form `R_{ijkℓ} = K₀(δ_{ik}δ_{jℓ} − δ_{iℓ}δ_{jk})`. The forward
direction is `eq_smul_stdCurvForm_of_const` (Lemma 3.4) read on the orthonormal
basis via `stdCurvForm_orthonormal`; the converse uses the basis-determination
lemma `ext_basis` (a curvature form is fixed by its basis components), so the
Kronecker relations force `B = K₀·R'` and hence constant curvature. -/
theorem eq_kronecker_iff_const (hB : IsAlgCurvatureForm B) (K₀ : ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : OrthonormalBasis ι ℝ V) :
    (∀ x y, B x y x y = K₀ * wedgeSq x y) ↔
      (∀ i j k l, B (e i) (e j) (e k) (e l) =
        K₀ * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
            - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0))) := by
  constructor
  · intro hconst i j k l
    rw [hB.eq_smul_stdCurvForm_of_const K₀ hconst (e i) (e j) (e k) (e l),
      stdCurvForm_orthonormal e.orthonormal i j k l]
  · intro hkron x y
    have key : ∀ a c d f, B a c d f = K₀ * stdCurvForm a c d f := by
      apply hB.ext_basis ((isAlgCurvatureForm_stdCurvForm (V := V)).smul K₀) e.toBasis
      intro i j k l
      simp only [OrthonormalBasis.coe_toBasis]
      rw [hkron i j k l, stdCurvForm_orthonormal e.orthonormal i j k l]
    rw [key x y x y, stdCurvForm_diag]

end IsAlgCurvatureForm

end Riemannian

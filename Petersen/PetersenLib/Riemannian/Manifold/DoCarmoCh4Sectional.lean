/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Manifold/DoCarmoCh4Sectional.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import PetersenLib.Ch03.AlgebraicCurvatureForm

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
* `wedgeSq`, `algSectionalCurvature` — the area `|x ∧ y|²` and `K` (`def:dc-ch4-3-2`),
  with `wedgeSq_nonneg` and `wedgeSq_pos_iff_linearIndependent` (strict
  Cauchy–Schwarz).
* `stdCurvForm` — the constant-curvature model `R'` of `lem:dc-ch4-3-4`,
  `⟨x,z⟩⟨y,t⟩ − ⟨y,z⟩⟨x,t⟩`, shown to be an `IsAlgCurvatureForm`.
* `IsAlgCurvatureForm.eq_smul_stdCurvForm_of_const` — do Carmo Ch. 4, Lemma 3.4:
  constant sectional curvature `K₀` iff `R = K₀ R'`.
* `algSectionalCurvature_changeBasis` — do Carmo Ch. 4, Prop. 3.1: `K` is unchanged
  under an invertible linear change of the spanning pair (basis independence).

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §3.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace PetersenLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

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
def algSectionalCurvature (B : V → V → V → V → ℝ) (x y : V) : ℝ :=
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

/-- **Math.** do Carmo Ch. 4, **Prop. 3.1** — the sectional curvature depends only
on the plane, not on the chosen basis: for an invertible linear change of the
spanning pair `x' = a·x+b·y`, `y' = c·x+d·y` (with `ad−bc ≠ 0`) of a linearly
independent pair `x,y`, `K(x',y') = K(x,y)`. Both numerator and denominator scale
by `(ad−bc)²` (the latter because `|·∧·|²` is the diagonal of the algebraic
curvature form `R'`), so the ratio is unchanged. -/
theorem algSectionalCurvature_changeBasis (hB : IsAlgCurvatureForm B)
    {a b c d : ℝ} (hdet : a * d - b * c ≠ 0) (x y : V)
    (hxy : LinearIndependent ℝ ![x, y]) :
    algSectionalCurvature B (a • x + b • y) (c • x + d • y) = algSectionalCurvature B x y := by
  have hw : wedgeSq (a • x + b • y) (c • x + d • y) = (a * d - b * c) ^ 2 * wedgeSq x y := by
    rw [← stdCurvForm_diag, isAlgCurvatureForm_stdCurvForm.diag_changeBasis, stdCurvForm_diag]
  have hnum := hB.diag_changeBasis a b c d x y
  have hpos : 0 < wedgeSq x y := (wedgeSq_pos_iff_linearIndependent x y).mpr hxy
  have hdet2 : (a * d - b * c) ^ 2 ≠ 0 := pow_ne_zero 2 hdet
  unfold algSectionalCurvature
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

end PetersenLib

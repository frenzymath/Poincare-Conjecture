import Mathlib.Algebra.BigOperators.Fin
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci

/-!
# Morgan–Tian Ch. 1, §1.2 — Ricci curvature, scalar curvature, and Einstein manifolds

Formalizes, at the algebraic fiber level (an algebraic curvature form `B` on a
finite-dimensional real inner product space `V` playing the role of the curvature
`(0,4)`-tensor on `T_pM`):

* the **Ricci curvature tensor** `Ric(x,y) = ∑ᵢ R(x,eᵢ,y,eᵢ)` and the
  **scalar curvature** `R = tr_g Ric` (Morgan–Tian `def:ricci-curvature`),
  re-exported from DoCarmoLib's basis-free `Riemannian.ricciForm` /
  `Riemannian.scalarCurvature`;
* the **Einstein condition** `Ric = λ·g` (`def:einstein-manifold`), as
  `IsEinsteinForm`;
* Morgan–Tian **Example `ex:einstein-dimension-2-3`** (the constant-sectional-
  curvature half): in dimensions `2` and `3`, an Einstein form with Einstein
  constant `λ` has constant sectional curvature `λ/(n−1)`
  (`IsEinsteinForm.sectional_const` for orthonormal pairs,
  `IsEinsteinForm.diag_eq_wedgeSq` for arbitrary pairs).

## Convention check

Morgan–Tian's curvature operator is minus do Carmo's, and Morgan–Tian's
`(0,4)`-tensor `R(X,Y,Z,W) = g(R(X,Y)W, Z)` swaps the last two slots relative to
DoCarmoLib's `curvatureForm X Y Z W = ⟨R(X,Y)Z, W⟩`; the two sign flips cancel, so
Morgan–Tian's 4-tensor at `(X,Y,Z,W)` *equals* DoCarmoLib's `curvatureForm X Y Z W`
and `Riemannian.ricciForm` (with `ricciForm_eq_sum : Ric(x,y) = ∑ᵢ B x eᵢ y eᵢ`)
is exactly Morgan–Tian's Ricci tensor. Sanity check: for the unit-sphere model
`B = stdCurvForm`, `ricciForm = (n−1)·⟨·,·⟩`.

## Fidelity caveat

Everything here is at the algebraic fiber level (a single tangent space), not the
manifold level. The second half of `ex:einstein-dimension-2-3` ("complete Einstein
implies space form") depends on `thm:uniformization` and is **not** formalized here.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2
(blueprint `def:ricci-curvature`, `def:einstein-manifold`,
`ex:einstein-dimension-2-3`).
-/

open scoped RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Math.** The **Ricci curvature tensor** at a point, as a function of an
algebraic curvature form `B` on the tangent space: Morgan–Tian's
`Ric(X,Y) = ∑ᵢ R(X,eᵢ,Y,eᵢ)` over any orthonormal basis `{eᵢ}` of `T_pM`
(`Riemannian.ricciForm_eq_sum`), packaged basis-free as a trace so that it is
well defined; it is symmetric (`Riemannian.ricciForm_symm`) and bilinear.
Blueprint: def:ricci-curvature. -/
abbrev ricciForm {B : V → V → V → V → ℝ} (hB : Riemannian.IsAlgCurvatureForm B)
    (x y : V) : ℝ :=
  Riemannian.ricciForm hB x y

/-- **Math.** The **scalar curvature** `R = tr_g Ric = gⁱʲ Ricᵢⱼ`, the metric trace
of the Ricci tensor; over any orthonormal basis it is `∑ⱼ Ric(eⱼ,eⱼ)`
(`Riemannian.scalarCurvature_eq_sum_ricci`). Blueprint: def:ricci-curvature. -/
abbrev scalarCurvature {B : V → V → V → V → ℝ}
    (hB : Riemannian.IsAlgCurvatureForm B) : ℝ :=
  Riemannian.scalarCurvature hB

/-- **Math.** The **Einstein condition** with Einstein constant `λ`, at the
algebraic fiber level: the Ricci tensor of the curvature form `B` satisfies
`Ric = λ·g`, i.e. `Ric(x,y) = λ·⟨x,y⟩` for all tangent vectors `x, y`.
Blueprint: def:einstein-manifold. -/
def IsEinsteinForm {B : V → V → V → V → ℝ} (hB : Riemannian.IsAlgCurvatureForm B)
    (lam : ℝ) : Prop :=
  ∀ x y : V, ricciForm hB x y = lam * (inner ℝ x y : ℝ)

/-- **Math.** Any orthonormal pair `x, y` in a finite-dimensional real inner
product space of dimension `n` extends to an orthonormal basis indexed by `Fin n`
placing `x, y` at any two prescribed distinct indices. (The orthonormal-extension
step of the proof of `ex:einstein-dimension-2-3`: "choose an orthonormal basis of
`T_pM` whose first two vectors span `P`".) -/
theorem exists_orthonormalBasis_pair {n : ℕ} (hdim : Module.finrank ℝ V = n)
    (i₀ i₁ : Fin n) (hne : i₀ ≠ i₁) {x y : V}
    (hx : inner ℝ x x = (1 : ℝ)) (hy : inner ℝ y y = (1 : ℝ))
    (hxy : inner ℝ x y = (0 : ℝ)) :
    ∃ e : OrthonormalBasis (Fin n) ℝ V, e i₀ = x ∧ e i₁ = y := by
  classical
  have hx' : ‖x‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hx, Real.sqrt_one]
  have hy' : ‖y‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hy, Real.sqrt_one]
  have hyx : inner ℝ y x = (0 : ℝ) := by rw [real_inner_comm]; exact hxy
  have hON : Orthonormal ℝ
      (Set.restrict {i₀, i₁} (fun i : Fin n => if i = i₀ then x else y)) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, hi⟩ ⟨j, hj⟩
    have hi' : i = i₀ ∨ i = i₁ := by simpa using hi
    have hj' : j = i₀ ∨ j = i₁ := by simpa using hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;>
      simp [Set.restrict_apply, hne, hne.symm, hx', hy', hxy, hyx]
  obtain ⟨e, he⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (by simp [hdim]) hON
  refine ⟨e, ?_, ?_⟩
  · have h := he i₀ (by simp)
    rwa [if_pos rfl] at h
  · have h := he i₁ (by simp)
    rwa [if_neg hne.symm] at h

/-- **Math.** Morgan–Tian Example `ex:einstein-dimension-2-3`, constant-sectional-
curvature half, on orthonormal pairs: if `(V, B)` is Einstein with Einstein
constant `λ` and `dim V = n ∈ {2, 3}`, then for every orthonormal pair `x, y` the
sectional curvature of the plane they span is `B(x,y,x,y) = λ/(n−1)`.

Proof (following the blueprint): extend `{x,y}` to an orthonormal basis
`{e₁,…,eₙ}` with `e₁ = x`, `e₂ = y`; write `Kᵢⱼ = B(eᵢ,eⱼ,eᵢ,eⱼ)`. The
orthonormal-basis formula for `Ric` and the antisymmetries of `B` give
`Ric(eᵢ,eᵢ) = ∑_{j≠i} Kᵢⱼ` and `Kⱼᵢ = Kᵢⱼ`. For `n = 2` the Einstein condition
reads `K₁₂ = λ`; for `n = 3` it gives the three equations `K₁₂+K₁₃ = λ`,
`K₁₂+K₂₃ = λ`, `K₁₃+K₂₃ = λ`, whence `K₁₂ = λ/2`.

The "complete implies space-form" half of the blueprint node needs
`thm:uniformization` and is not formalized here.
Blueprint: ex:einstein-dimension-2-3. -/
theorem IsEinsteinForm.sectional_const {B : V → V → V → V → ℝ}
    (hB : Riemannian.IsAlgCurvatureForm B) (lam : ℝ) (hE : IsEinsteinForm hB lam)
    (hdim : Module.finrank ℝ V = 2 ∨ Module.finrank ℝ V = 3) :
    ∀ x y : V, inner ℝ x x = (1 : ℝ) → inner ℝ y y = (1 : ℝ) →
      inner ℝ x y = (0 : ℝ) →
      B x y x y = lam / (Module.finrank ℝ V - 1) := by
  intro x y hx hy hxy
  rcases hdim with hdim | hdim
  · -- `n = 2`: `Ric(x,x) = K₁₂ = λ`.
    obtain ⟨e, he0, he1⟩ :=
      exists_orthonormalBasis_pair hdim (0 : Fin 2) 1 (by decide) hx hy hxy
    have h : Riemannian.ricciForm hB x x = lam * inner ℝ x x := hE x x
    rw [hx, mul_one, Riemannian.ricciForm_eq_sum hB x x e, Fin.sum_univ_two,
      he0, he1, hB.self_left, zero_add] at h
    rw [hdim]
    norm_num
    exact h
  · -- `n = 3`: the three diagonal Einstein equations.
    obtain ⟨e, he0, he1⟩ :=
      exists_orthonormalBasis_pair hdim (0 : Fin 3) 1 (by decide) hx hy hxy
    have hzz : inner ℝ (e 2) (e 2) = (1 : ℝ) := by
      have h := orthonormal_iff_ite.mp e.orthonormal 2 2
      rwa [if_pos rfl] at h
    -- `K ⱼᵢ = K ᵢⱼ` from the two pair antisymmetries.
    have hKcomm : ∀ a b : V, B b a b a = B a b a b := by
      intro a b
      rw [hB.antisymm₁₂ b a b a, hB.antisymm₃₄ a b b a, neg_neg]
    have h1 : B x y x y + B x (e 2) x (e 2) = lam := by
      have h : Riemannian.ricciForm hB x x = lam * inner ℝ x x := hE x x
      rw [hx, mul_one, Riemannian.ricciForm_eq_sum hB x x e, Fin.sum_univ_three,
        he0, he1, hB.self_left, zero_add] at h
      exact h
    have h2 : B x y x y + B y (e 2) y (e 2) = lam := by
      have h : Riemannian.ricciForm hB y y = lam * inner ℝ y y := hE y y
      rw [hy, mul_one, Riemannian.ricciForm_eq_sum hB y y e, Fin.sum_univ_three,
        he0, he1, hB.self_left, add_zero, hKcomm x y] at h
      exact h
    have h3 : B x (e 2) x (e 2) + B y (e 2) y (e 2) = lam := by
      have h : Riemannian.ricciForm hB (e 2) (e 2) = lam * inner ℝ (e 2) (e 2) :=
        hE (e 2) (e 2)
      rw [hzz, mul_one, Riemannian.ricciForm_eq_sum hB (e 2) (e 2) e,
        Fin.sum_univ_three, he0, he1, hB.self_left, add_zero, hKcomm x (e 2),
        hKcomm y (e 2)] at h
      exact h
    rw [hdim]
    norm_num
    linarith

/-- **Math.** Morgan–Tian Example `ex:einstein-dimension-2-3`, constant-sectional-
curvature half, for **arbitrary** pairs: if `(V, B)` is Einstein with Einstein
constant `λ` and `dim V = n ∈ {2, 3}`, then
`B(x,y,x,y) = (λ/(n−1))·|x∧y|²` for all `x, y` — i.e. `B` has constant sectional
curvature `λ/(n−1)` in do Carmo's sense (`K(x,y) = B(x,y,x,y)/|x∧y|²` on every
plane). Reduces to the orthonormal case `IsEinsteinForm.sectional_const` by
Gram–Schmidt on the pair and the determinant scaling `diag_changeBasis` of both
sides; degenerate pairs contribute `0 = 0`.
Blueprint: ex:einstein-dimension-2-3. -/
theorem IsEinsteinForm.diag_eq_wedgeSq {B : V → V → V → V → ℝ}
    (hB : Riemannian.IsAlgCurvatureForm B) (lam : ℝ) (hE : IsEinsteinForm hB lam)
    (hdim : Module.finrank ℝ V = 2 ∨ Module.finrank ℝ V = 3) (x y : V) :
    B x y x y = (lam / (Module.finrank ℝ V - 1)) * Riemannian.wedgeSq x y := by
  by_cases hx0 : x = 0
  · subst hx0
    simp [Riemannian.wedgeSq, hB.zero_left]
  by_cases hLI : LinearIndependent ℝ ![x, y]
  case neg =>
    -- Degenerate plane: both sides vanish.
    rw [LinearIndependent.pair_iff' hx0] at hLI
    obtain ⟨a, ha⟩ := not_forall.mp hLI
    rw [not_ne_iff] at ha
    have hwedge : Riemannian.wedgeSq x (a • x) = 0 := by
      simp only [Riemannian.wedgeSq, real_inner_smul_left, real_inner_smul_right]
      ring
    rw [← ha, hB.smul_two, hB.self_left, mul_zero, hwedge, mul_zero]
  case pos =>
    -- Gram–Schmidt: replace `x, y` by an orthonormal pair `u, v` spanning the
    -- same plane, with `x = ‖x‖·u`, `y = c·u + ‖w‖·v`.
    have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    set u : V := ‖x‖⁻¹ • x with hu
    set c : ℝ := inner ℝ u y with hc
    set w : V := y - c • u with hw
    have huu : inner ℝ u u = (1 : ℝ) := by
      rw [hu, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_mul_norm]
      field_simp
    have hw0 : w ≠ 0 := by
      intro h0
      rw [hw, sub_eq_zero] at h0
      refine (LinearIndependent.pair_iff' hx0).mp hLI (c * ‖x‖⁻¹) ?_
      rw [mul_smul, ← hu, ← h0]
    have hwn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    set v : V := ‖w‖⁻¹ • w with hv
    have hvv : inner ℝ v v = (1 : ℝ) := by
      rw [hv, real_inner_smul_left, real_inner_smul_right,
        real_inner_self_eq_norm_mul_norm]
      field_simp
    have huw : inner ℝ u w = (0 : ℝ) := by
      rw [hw, inner_sub_right, real_inner_smul_right, huu, mul_one, ← hc, sub_self]
    have huv : inner ℝ u v = (0 : ℝ) := by
      rw [hv, real_inner_smul_right, huw, mul_zero]
    have hxdec : x = ‖x‖ • u + (0 : ℝ) • v := by
      rw [zero_smul, add_zero, hu, smul_smul, mul_inv_cancel₀ hxn, one_smul]
    have hydec : y = c • u + ‖w‖ • v := by
      rw [hv, smul_smul ‖w‖ ‖w‖⁻¹ w, mul_inv_cancel₀ hwn, one_smul, hw]
      abel
    have hBuv : B u v u v = lam / (Module.finrank ℝ V - 1) :=
      IsEinsteinForm.sectional_const hB lam hE hdim u v huu hvv huv
    -- Both `B(x,y,x,y)` and `|x∧y|²` scale by `(‖x‖·‖w‖)²` under the change of pair.
    have hnum := hB.diag_changeBasis ‖x‖ 0 c ‖w‖ u v
    have hden := (Riemannian.isAlgCurvatureForm_stdCurvForm (V := V)).diag_changeBasis
      ‖x‖ 0 c ‖w‖ u v
    rw [← hxdec, ← hydec] at hnum hden
    rw [Riemannian.stdCurvForm_diag, Riemannian.stdCurvForm_diag] at hden
    have hwuv : Riemannian.wedgeSq u v = 1 := by
      simp only [Riemannian.wedgeSq]
      rw [huu, hvv, huv]
      norm_num
    rw [hnum, hBuv, hden, hwuv]
    ring

end MorganTianLib

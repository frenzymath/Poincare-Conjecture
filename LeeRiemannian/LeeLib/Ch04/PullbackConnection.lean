/-
Chapter 4, "Connections", §"Pullback Connections": Lee's Lemma 4.37 and the
abstract naturality lemma at the heart of Proposition 4.38.

Connections in the tangent bundle cannot be pushed forward or pulled back by
arbitrary smooth maps, but a **diffeomorphism** `φ : M → M̃` lets us pull back a
connection `∇̃` in `TM̃` to a connection `φ*∇̃` in `TM`, defined by Lee's equation
(4.26):

  `(φ*∇̃)_X Y = (φ⁻¹)_* (∇̃_{φ_* X} (φ_* Y))`,

where `φ_*` denotes the pushforward of vector fields (`VectorField.mpullback` by
`φ.symm`).

On mathlib's representation a connection sends a raw section `σ ↦ ∇σ`, with
`∇σ x : TₓM →L V x`.  Under the fibre identifications `e x := dφ_x : TₓM ≃L T_{φx}M̃`
(mathlib's `Diffeomorph.mfderivToContinuousLinearEquiv`), the pullback connection
is the term

  `(φ*∇̃) σ x = (e x).symm ∘L (∇̃ (φ_* σ) (φ x)) ∘L (e x) : TₓM →L TₓM`.

This file builds:

* `TangentConnection.pullback` — the pullback connection `φ*∇̃`, a genuine
  `Connection I E (TangentSpace I : M → _)`, verifying additivity and the Leibniz
  rule (Lee's Lemma 4.37).  `ℝ`-linearity in `Y` and `C^∞`-linearity in `X` come
  for free from the generic `covariantDeriv_*` API of `Connection.lean`.
* `pullback_covariantDeriv_apply` — the covariant derivative read off the term:
  `∇_X σ x = (e x).symm (∇̃ (φ_* σ) (φ x) (e x (X x)))`.
* `covariantDeriv_pullback_naturality` — the abstract heart of Proposition 4.38
  (Properties of Pullback Connections): `dφ` intertwines the pullback covariant
  derivative with `∇̃`,
  `dφ_x (∇_X σ x) = ∇̃_{φ_* X} (φ_* σ) (φ x)`.
  Proposition 4.38 (a),(b),(c) — covariant differentiation along curves, geodesics,
  parallel transport — are instances of this naturality, but their global forms
  (`D_t`, geodesics, parallel transport) live only chart-locally in LeeLib, so we
  record only the abstract naturality that captures their mathematical content.

The one nontrivial smoothness input is that the pushforward of a differentiable
section is differentiable (`MDifferentiableAt.mpullback_vectorField`), needed to
invoke `∇̃`'s additivity/Leibniz on the pushed-forward sections.
-/
import LeeLib.Ch04.Connection
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.Geometry.Manifold.LocalDiffeomorph

namespace LeeLib.Ch04

open Bundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

/-- `n ≠ 0` from `2 ≤ n`, used to form the fibre equivalences. -/
private theorem ne_zero_of_two_le {n : ℕ∞ω} (hn : 2 ≤ n) : n ≠ 0 := by
  rintro rfl; simp at hn

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : ℕ∞ω}

section

variable [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E']
  (φ : M ≃ₘ^n⟮I, I'⟯ M') (hn : 2 ≤ n)

/-- The fibre identification `e x = dφ_x : TₓM ≃L T_{φx}M̃`, mathlib's
`Diffeomorph.mfderivToContinuousLinearEquiv`. -/
local notation3 "e% " x => Diffeomorph.mfderivToContinuousLinearEquiv φ (ne_zero_of_two_le hn) x

omit [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E'] in
include hn in
/-- Key inverse identity: the junk-inverse of `dφ⁻¹` at `φ x` is `dφ_x`.  Both sides
are honest maps `E →L E'` because `TangentSpace` collapses to the model fibre. -/
theorem inverse_mfderiv_symm (x : M) :
    (mfderiv% φ.symm (φ x)).inverse = mfderiv% φ x := by
  have A : mfderiv% ((⇑φ.symm) ∘ (⇑φ)) x = ContinuousLinearMap.id _ _ := by
    have h : (⇑φ.symm) ∘ (⇑φ) = id := by ext y; exact φ.symm_apply_apply y
    rw [h, id_eq, mfderiv_id]
  rw [mfderiv_comp x (φ.symm.mdifferentiable (ne_zero_of_two_le hn) _)
    (φ.mdifferentiable (ne_zero_of_two_le hn) _)] at A
  have A' : mfderiv% ((⇑φ) ∘ (⇑φ.symm)) (φ x) = ContinuousLinearMap.id _ _ := by
    have h : (⇑φ) ∘ (⇑φ.symm) = id := by ext y; exact φ.apply_symm_apply y
    rw [h, id_eq, mfderiv_id]
  rw [mfderiv_comp (φ x) (φ.mdifferentiable (ne_zero_of_two_le hn) _)
    (φ.symm.mdifferentiable (ne_zero_of_two_le hn) _), φ.symm_apply_apply] at A'
  exact ContinuousLinearMap.inverse_eq A A'

omit [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E'] in
include hn in
/-- Value of the pushforward `φ_* σ` at `φ x`: `(φ_* σ)(φ x) = dφ_x (σ x)`. -/
theorem pushforward_apply_phi (σ : Π x : M, TangentSpace I x) (x : M) :
    mpullback I' I φ.symm σ (φ x) = mfderiv% φ x (σ x) := by
  rw [mpullback_apply, inverse_mfderiv_symm φ hn, φ.symm_apply_apply]

omit [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E'] in
include hn in
/-- The junk-inverse `dφ⁻¹` at `φ x` is genuinely invertible: it is the forward
direction of the fibre equivalence `dφ⁻¹` (mathlib's `mfderivToContinuousLinearEquiv`
for `φ.symm`).  Needed to invoke `MDifferentiableAt.mpullback_vectorField`. -/
private theorem isInvertible_mfderiv_symm (x : M) :
    (mfderiv% φ.symm (φ x)).IsInvertible :=
  ⟨Diffeomorph.mfderivToContinuousLinearEquiv φ.symm (ne_zero_of_two_le hn) (φ x),
    Diffeomorph.mfderivToContinuousLinearEquiv_coe φ.symm (ne_zero_of_two_le hn)⟩

include hn in
/-- The pushforward `φ_* σ` of a section differentiable at `x` is differentiable at
`φ x` (Lee's smoothness input for Lemma 4.37): a special case of mathlib's
`MDifferentiableAt.mpullback_vectorField`, using that `φ.symm` is `C^n` with
invertible differential. -/
private theorem mdiffAt_pushforward {σ : Π x : M, TangentSpace I x} {x : M}
    (hσ : MDiffAt (T% σ) x) :
    MDiffAt (T% (mpullback I' I φ.symm σ)) (φ x) := by
  refine MDifferentiableAt.mpullback_vectorField ?_ φ.symm.contMDiffAt
    (isInvertible_mfderiv_symm φ hn x) hn
  rw [φ.symm_apply_apply]; exact hσ

omit [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E'] in
include hn in
/-- The chain rule underlying the Leibniz identity of the pullback connection
(Lee's eq. (A.7), `(φ_* X)(f̃) = (Xf) ∘ φ⁻¹`): for `f̃ = f ∘ φ⁻¹`, the differential
`d f̃` at `φ x` composed with `dφ_x` recovers `d f` at `x`,
`d f̃_{φx}(dφ_x v) = d f_x(v)`. -/
private theorem mvfderiv_pushforward_apply {g : M → ℝ} {x : M} (hg : MDiffAt g x)
    (v : TangentSpace I x) :
    d% (g ∘ ⇑φ.symm) (φ x) ((e% x) v) = d% g x v := by
  have hφ : MDiffAt φ x := φ.mdifferentiable (ne_zero_of_two_le hn) x
  have hg' : MDiffAt (g ∘ ⇑φ.symm) (φ x) :=
    MDifferentiableAt.comp_of_eq (φ x) hg
      (φ.symm.mdifferentiable (ne_zero_of_two_le hn) (φ x)) (φ.symm_apply_apply x)
  have hchain := mfderiv_comp (x := x) (f := ⇑φ) (g := g ∘ ⇑φ.symm) hg' hφ
  have hcomp : (g ∘ ⇑φ.symm) ∘ ⇑φ = g := by
    funext y; simp [Function.comp_apply, φ.symm_apply_apply]
  rw [hcomp] at hchain
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [← ContinuousLinearEquiv.coe_coe (e% x),
    Diffeomorph.mfderivToContinuousLinearEquiv_coe φ (ne_zero_of_two_le hn), hchain]
  rfl

omit [IsManifold I 2 M] [IsManifold I' 2 M'] [CompleteSpace E'] in
include hn in
/-- `(φ⁻¹)_*` undoes `φ_*` fibrewise: `(dφ_x)⁻¹ ((φ_* σ)(φ x)) = σ x`. -/
private theorem symm_pushforward_apply (σ : Π x : M, TangentSpace I x) (x : M) :
    (e% x).symm (mpullback I' I φ.symm σ (φ x)) = σ x := by
  rw [pushforward_apply_phi φ hn σ x,
    ← Diffeomorph.mfderivToContinuousLinearEquiv_coe φ (ne_zero_of_two_le hn),
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

/-- **Pullback connection** (Lee, Lemma 4.37, eq. 4.26).  Given a diffeomorphism
`φ : M ≃ₘ M'` and a connection `∇̃` in `TM'`, the pullback `φ*∇̃` in `TM`,
`(φ*∇̃)_X Y = (φ⁻¹)_* (∇̃_{φ_* X} (φ_* Y))`.  On the raw-section representation,
`(φ*∇̃) σ x = (dφ_x)⁻¹ ∘L (∇̃ (φ_* σ) (φ x)) ∘L dφ_x`.  Additivity and the Leibniz
rule (Lee's Lemma 4.37) are verified; `ℝ`-linearity in `Y` and `C^∞`-linearity in
`X` come for free from the `covariantDeriv_*` API of `Connection.lean`. -/
noncomputable def TangentConnection.pullback
    (cov' : Connection I' E' (TangentSpace I' : M' → Type _)) :
    Connection I E (TangentSpace I : M → Type _) where
  toFun σ x := (e% x).symm.toContinuousLinearMap ∘L
    (cov'.toFun (mpullback I' I φ.symm σ) (φ x) ∘L (e% x).toContinuousLinearMap)
  isCovariantDerivativeOnUniv := {
    add := by
      intro σ σ' x hσ hσ' _
      rw [mpullback_add, cov'.isCovariantDerivativeOnUniv.add
        (mdiffAt_pushforward φ hn hσ) (mdiffAt_pushforward φ hn hσ'),
        ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    leibniz := by
      intro σ g x hσ hg _
      have hτ : MDiffAt (T% (mpullback I' I φ.symm σ)) (φ x) := mdiffAt_pushforward φ hn hσ
      have hgt : MDiffAt (g ∘ ⇑φ.symm) (φ x) :=
        MDifferentiableAt.comp_of_eq (φ x) hg
          (φ.symm.mdifferentiable (ne_zero_of_two_le hn) (φ x)) (φ.symm_apply_apply x)
      ext v
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply]
      rw [mpullback_smul, cov'.isCovariantDerivativeOnUniv.leibniz hτ hgt]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, map_add, map_smul]
      rw [Function.comp_apply, φ.symm_apply_apply, mvfderiv_pushforward_apply φ hn hg v,
        symm_pushforward_apply φ hn σ x] }

/-- Read-off of the pullback covariant derivative on the section representation:
`(φ*∇̃)_X σ x = (dφ_x)⁻¹ (∇̃ (φ_* σ) (φ x) (dφ_x (X x)))`. -/
theorem pullback_covariantDeriv_apply
    (cov' : Connection I' E' (TangentSpace I' : M' → Type _))
    (X σ : Π x : M, TangentSpace I x) (x : M) :
    covariantDeriv (TangentConnection.pullback φ hn cov') X σ x
      = (e% x).symm (cov'.toFun (mpullback I' I φ.symm σ) (φ x) ((e% x) (X x))) := by
  simp only [covariantDeriv_apply, TangentConnection.pullback,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- **Naturality** (the abstract heart of Prop 4.38): `dφ` intertwines the pullback
covariant derivative `φ*∇̃` with `∇̃`,
`dφ_x ((φ*∇̃)_X σ x) = ∇̃ (φ_* σ) (φ x) (dφ_x (X x))`.  Proposition 4.38(a),(b),(c)
— covariant differentiation along curves, geodesics, parallel transport — are
instances of this, but their global forms are not available in LeeLib, so only the
naturality that captures their content is recorded. -/
theorem covariantDeriv_pullback_naturality
    (cov' : Connection I' E' (TangentSpace I' : M' → Type _))
    (X σ : Π x : M, TangentSpace I x) (x : M) :
    (e% x) (covariantDeriv (TangentConnection.pullback φ hn cov') X σ x)
      = cov'.toFun (mpullback I' I φ.symm σ) (φ x) ((e% x) (X x)) := by
  rw [pullback_covariantDeriv_apply, ContinuousLinearEquiv.apply_symm_apply]

end

end LeeLib.Ch04

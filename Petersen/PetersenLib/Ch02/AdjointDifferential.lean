import PetersenLib.Ch01.BiinvariantExistence
import PetersenLib.Ch01.AdjointRepresentation
import PetersenLib.Ch02.OneParameterSubgroup
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# The differential of the adjoint representation (Petersen §2.1.4, Lemma 2.1.7)

This file supplies the **abstract** `Ad`/`ad` correspondence needed to close
Petersen Exercise 1.6.24 (3) — the skew-symmetry of `ad_U` for a bi-invariant
metric — reducing the whole exercise to a single, clean differential-geometric
identity of §2.1.4.

The reduction proved here is that **no flow / one-parameter-subgroup *law* is
needed**: the only analytic ingredient is that the adjoint map
`Ad : G → 𝔤 →L 𝔤` (`adMap`) is `C^∞` as an *operator-valued* map, so that for any
smooth curve `φ` realising `U ∈ 𝔤` (`φ 0 = 1`, `φ'(0) = U`) the operator curve
`t ↦ Ad_{φ t}` is differentiable at `0` with derivative the fixed operator
`ad_U = D(Ad)_e(U) = mfderiv Ad 1 U`.  A convenient such curve is Mathlib's
one-parameter subgroup (`PetersenLib.exists_oneParameterSubgroup`), whose initial
velocity is `U` (`PetersenLib.oneParameterSubgroup_hasMFDerivAt_zero`).

## Main results

* `PetersenLib.contMDiffAt_adMap` — the adjoint representation
  `Ad : G → 𝔤 →L 𝔤` is `C^∞` (upgrading `PetersenLib.adMap_continuous`).  This is
  the joint-smoothness step, discharged through Mathlib's family derivative lemma
  `ContMDiffAt.mfderiv` exactly as in `adMap_continuous`.
* `PetersenLib.hasDerivAt_adMap_comp` — for any curve `φ` with `φ 0 = 1` and
  manifold velocity `U` at `0`, the operator curve `t ↦ Ad_{φ t}` has derivative
  `ad_U := mfderiv Ad 1 U` at `0`.
* `PetersenLib.mfderiv_adMap_apply_eq_groupBracket` — **Lemma 2.1.7** (abstract):
  `ad_U(X) = ⁅U, X⁆`, i.e. `(mfderiv Ad 1 U) X = ⁅U, X⁆`, the Lie-algebra bracket
  of `GroupLieAlgebra I G`.  This is the sole remaining §2.1.4 gap; it is a
  chart-level second-derivative computation (the mixed second derivative of group
  multiplication antisymmetrises to the bracket).  The model case `G = Rˣ` is
  `PetersenLib.ad_eq_differential_of_Ad`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.4, Lemma 2.1.7.
-/

open Bundle Set Function VectorField TopologicalSpace
open scoped Manifold ContDiff Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-! ## Smoothness of the adjoint representation `Ad : G → 𝔤 →L 𝔤` -/

/-- **Math.** `Ad : G → 𝔤 →L 𝔤` is `C^∞`.  Conjugation `(h, y) ↦ h y h⁻¹` is
jointly smooth and fixes the identity `conj_h(e) = e`, so the family lemma
`ContMDiffAt.mfderiv` reads its `y`-differential at `e` through the tangent-space
trivialization *at the fixed point `e`*; because both source and target base
points are the constant `e`, that trivialization is a single fixed continuous
linear isomorphism, so `inTangentCoordinates` collapses to conjugating `Ad_h` by
the fixed maps `C₁, C₂`.  Undoing that fixed conjugation (`C₁ ∘ C₂ = id`) recovers
`Ad` as a smooth function.  (Smooth strengthening of `PetersenLib.adMap_continuous`.) -/
theorem contMDiffAt_adMap (h₀ : G) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ (adMap (I := I) (G := G)) h₀ := by
  set T := trivializationAt E (TangentSpace I) (1 : G) with hT
  have h1mem : (1 : G) ∈ T.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (1 : G)
  set C₁ : E →L[ℝ] E := (T.symmL ℝ (1 : G) : E →L[ℝ] E) with hC₁
  set C₂ : E →L[ℝ] E := (T.continuousLinearMapAt ℝ (1 : G) : E →L[ℝ] E) with hC₂
  have hC₁C₂ : ∀ y : E, C₁ (C₂ y) = y := fun y =>
    T.symmL_continuousLinearMapAt h1mem y
  have hf : ContMDiffAt (I.prod I) I ∞
      (Function.uncurry (fun h y : G => h * y * h⁻¹)) (h₀, (fun _ : G => (1 : G)) h₀) :=
    (contMDiffAt_fst.mul contMDiffAt_snd).mul contMDiffAt_fst.inv
  have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
  have h0 := ContMDiffAt.mfderiv (fun h y : G => h * y * h⁻¹) (fun _ : G => (1 : G))
    hf contMDiffAt_const hmn
  have hbase : (fun x : G => (fun h y : G => h * y * h⁻¹) x ((fun _ : G => (1 : G)) x))
      = (fun _ : G => (1 : G)) := by funext x; simp
  rw [hbase] at h0
  set Ψ := inTangentCoordinates I I (fun _ : G => (1 : G)) (fun _ : G => (1 : G))
    (fun h => adMap (I := I) h) h₀ with hΨ
  have hΨcont : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ Ψ h₀ := h0
  have hΨval : ∀ h : G, Ψ h = C₂.comp ((adMap (I := I) h).comp C₁) := fun _ => rfl
  have hEq : ∀ h : G, adMap (I := I) h = C₁.comp ((Ψ h).comp C₂) := by
    intro h
    ext u
    rw [hΨval h]
    simp only [ContinuousLinearMap.comp_apply, hC₁C₂]
  rw [show (adMap (I := I) (G := G)) = fun h => C₁.comp ((Ψ h).comp C₂) from funext hEq]
  exact contMDiffAt_const.clm_comp (hΨcont.clm_comp contMDiffAt_const)

/-- The adjoint representation is manifold-differentiable at every point. -/
theorem mdifferentiableAt_adMap (h₀ : G) :
    MDifferentiableAt I 𝓘(ℝ, E →L[ℝ] E) (adMap (I := I) (G := G)) h₀ :=
  (contMDiffAt_adMap h₀).mdifferentiableAt (by norm_num)

/-! ## The adjoint orbit of a curve has derivative `ad_U = D(Ad)_e(U)` -/

/-- **Math.** (Petersen §2.1.4, the analytic reduction.)  *No flow law is needed.*
For **any** smooth curve `φ` with `φ 0 = 1` and manifold velocity `U` at `0`
(`Dφ|₀ = t ↦ t·U`), the operator curve `t ↦ Ad_{φ t}` is differentiable at `0`
with derivative the fixed operator `ad_U := D(Ad)_e(U) = mfderiv Ad 1 U`.  This is
just the chain rule for the composition of the smooth operator-valued map `Ad`
(`contMDiffAt_adMap`) with the curve `φ`. -/
theorem hasDerivAt_adMap_comp {φ : ℝ → G} {U : TangentSpace I (1 : G)}
    (hφ0 : φ 0 = 1)
    (hφ : HasMFDerivAt 𝓘(ℝ, ℝ) I φ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight U)) :
    HasDerivAt (fun t => adMap (I := I) (φ t))
      (mfderiv I 𝓘(ℝ, E →L[ℝ] E) (adMap (I := I) (G := G)) 1 U) 0 := by
  have hAd : HasMFDerivAt I 𝓘(ℝ, E →L[ℝ] E) (adMap (I := I) (G := G)) (φ 0)
      (mfderiv I 𝓘(ℝ, E →L[ℝ] E) (adMap (I := I) (G := G)) (φ 0)) :=
    (mdifferentiableAt_adMap (φ 0)).hasMFDerivAt
  have hcomp := hAd.comp 0 hφ
  rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
  have hd := hcomp.hasDerivAt
  rw [hφ0] at hd
  have hval : ((mfderiv I 𝓘(ℝ, E →L[ℝ] E) (adMap (I := I) (G := G)) 1).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight U)) 1
      = mfderiv I 𝓘(ℝ, E →L[ℝ] E) (adMap (I := I) (G := G)) 1 U := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul]
  rw [← hval]
  exact hd

/-! ## Lemma 2.1.7 (abstract): `ad_U = ⁅U, ·⁆`

The identity `D(Ad)_e(U)(X) = ⁅U, X⁆`
(`PetersenLib.mfderiv_adMap_apply_eq_groupBracket`) is proved in
`PetersenLib.Ch02.AdjointBracketMain`, by reducing both sides to second
derivatives of the chart multiplication `μ(a, b) = φ(φ⁻¹a · φ⁻¹b)` (see
`PetersenLib.ChartMul.adChart_eq_bracketChart` and the manifold ↔ chart bridges
`PetersenLib.AdjointBracket.mfderiv_adMap_eq_adChart` /
`PetersenLib.AdjointBracket.groupBracket_eq_bracketChart`).  It is stated there,
not here, only to avoid an import cycle: those bridge files import this one for
the smoothness of `adMap`.  The model case `G = Rˣ` is
`PetersenLib.ad_eq_differential_of_Ad`. -/

/-- **Math.** *The `Z`-component of the adjoint orbit is differentiable.*  For any
curve `φ` with `φ 0 = 1` and velocity `U` at `0`, and any `Z ∈ E`, the vector
curve `t ↦ Ad_{φ t}(Z)` is differentiable at `0` with derivative
`D(h ↦ Ad_h Z)_e(U)`.  This is the chain rule for `(h ↦ Ad_h Z) ∘ φ` (using
`contMDiffAt_adMap` and `MDifferentiableAt.clm_apply`).  Composed with **Lemma
2.1.7** (`mfderiv_adMap_apply_eq_groupBracket`) this derivative is `⁅U, Z⁆`; the
form is kept as an `mfderiv` to stay inside the model space `E`. -/
theorem hasDerivAt_adMap_apply {φ : ℝ → G} {U : TangentSpace I (1 : G)} (Z : E)
    (hφ0 : φ 0 = 1)
    (hφ : HasMFDerivAt 𝓘(ℝ, ℝ) I φ 0 ((1 : ℝ →L[ℝ] ℝ).smulRight U)) :
    HasDerivAt (fun t => adMap (I := I) (φ t) Z)
      (mfderiv I 𝓘(ℝ, E) (fun h => adMap (I := I) h Z) 1 U) 0 := by
  have hg : HasMFDerivAt I 𝓘(ℝ, E) (fun h => adMap (I := I) h Z) (φ 0)
      (mfderiv I 𝓘(ℝ, E) (fun h => adMap (I := I) h Z) (φ 0)) :=
    ((mdifferentiableAt_adMap (φ 0)).clm_apply mdifferentiableAt_const).hasMFDerivAt
  have hcomp := hg.comp 0 hφ
  rw [hasMFDerivAt_iff_hasFDerivAt] at hcomp
  have hd := hcomp.hasDerivAt
  rw [hφ0] at hd
  have hval : ((mfderiv I 𝓘(ℝ, E) (fun h => adMap (I := I) h Z) 1).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight U)) 1
      = mfderiv I 𝓘(ℝ, E) (fun h => adMap (I := I) h Z) 1 U := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.one_apply, one_smul]
  rw [← hval]
  exact hd

end PetersenLib

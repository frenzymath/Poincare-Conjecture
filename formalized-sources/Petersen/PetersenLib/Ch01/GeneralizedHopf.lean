import PetersenLib.Ch01.SnocIsometry
import PetersenLib.Ch01.HopfVertical

/-!
# The generalized Hopf fibration `S^{2n+3} → ℂP^{n+1}` (Petersen Example 1.4.14)

Example 1.4.12 (`hopfFibrationHigherDimSphere`) exhibits the circle quotient of a doubly warped
product `I × S^{2n+1} × S¹` with metric `dt² + ρ²(t) ds²_{2n+1} + φ²(t) dθ²`.  Example 1.4.14 is
the special case `ρ = sin`, `φ = cos`, where the source is the *round* sphere `S^{2n+3}` and the
quotient is *complex projective space* `ℂP^{n+1}` with its Fubini–Study metric, presented as

  `dt² + sin²(t) (g + cos²(t) h)`,  `t ∈ [0, π/2]`,

where `h = (θ)²` is the square of the Hopf 1-form of `S^{2n+1}` and `g` is the (degenerate)
horizontal part of the round metric of `S^{2n+1}`.

This file closes the identification of the *quotient* with `ℂP^{n+1}`, which
`PetersenLib.Ch01.HopfSphereSubmersion` deliberately left as an abstract quotient form:

* `pullbackForm_genHopfSphere` — the parametrization `(t, ζ, w) ↦ (sin(t)·ζ, cos(t)·w)` of
  `S^{2n+3} ⊆ ℂ^{n+2}` pulls the round metric back to the doubly warped product metric.
* `projSphere_genHopfSphere` — **the commuting square**: the Hopf projection
  `π : S^{2n+3} → ℂP^{n+1}` composed with the parametrization equals the base map
  `ψ(t, ζ) = [sin(t)·ζ : cos(t)]` composed with the quotient map
  `(t, ζ, w) ↦ (t, w⁻¹·ζ)` of Example 1.4.12.  This is what says that the quotient *is*
  `ℂP^{n+1}`.
* `surjective_genHopfBase` — `ψ` is onto `ℂP^{n+1}`.
* `pullbackForm_genHopfBase` — **the payoff**: `ψ` pulls the Fubini–Study metric back to
  `dt² + sin²(t) g + sin²(t)cos²(t) h`, i.e. exactly the quotient form of Example 1.4.12 with
  `ρ = sin`, `φ = cos` (there `(ρφ)²/(ρ² + φ²) = sin²cos²`).
* `generalizedHopfFibrationComplexProjective` — Example 1.4.14, assembled.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.4.14.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Metric Module
open scoped ContDiff Manifold RealInnerProductSpace

namespace PetersenLib

section GeneralizedHopf

/-! ## Generic smoothness helpers

The ambient space of the generalized Hopf fibration is `EuclideanSpace ℂ (Fin (n+2))`, whose real
scalar action goes through the complex one.  Elaborating `ContMDiff.smul` / `HasFDerivAt.smul`
*directly* at such a space gets stuck on `IsScalarTower ℝ ?m ℂ`; the standard escape used
throughout this chapter is to prove the smoothness statement over an *abstract* real inner-product
space and then instantiate it.  These are those abstract statements. -/

section Generic

variable {E₁ : Type*} [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {n₁ n₂ : ℕ} [Fact (finrank ℝ E₁ = n₁ + 1)] [Fact (finrank ℝ E₂ = n₂ + 1)]

/-- **Eng.** The doubly warped sphere map `(t, x, y) ↦ (sin(t)·x, cos(t)·y)` into the `ℓ²`-product
is smooth. -/
theorem contMDiff_doublyWarpedSphereAmbient :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, WithLp 2 (E₁ × E₂)) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
        (WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))
          : WithLp 2 (E₁ × E₂))) := by
  have hfst : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, ℝ) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => q.1) := contMDiff_fst
  have h21 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₁) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.1 : E₁)) :=
    contMDiff_coe_sphere.comp ((contMDiff_fst (I := 𝓡 n₁) (J := 𝓡 n₂)).comp contMDiff_snd)
  have h22 : ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 n₁).prod (𝓡 n₂))) 𝓘(ℝ, E₂) ∞
      (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 => (q.2.2 : E₂)) :=
    contMDiff_coe_sphere.comp ((contMDiff_snd (I := 𝓡 n₁) (J := 𝓡 n₂)).comp contMDiff_snd)
  have hfun : (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
        (WithLp.toLp 2 (Real.sin q.1 • (q.2.1 : E₁), Real.cos q.1 • (q.2.2 : E₂))
          : WithLp 2 (E₁ × E₂)))
      = (fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          (lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)) (Real.sin q.1 • (q.2.1 : E₁)))
        + fun q : ℝ × sphere (0 : E₁) 1 × sphere (0 : E₂) 1 =>
          (lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)) (Real.cos q.1 • (q.2.2 : E₂)) := by
    funext q; exact toLp_eq_lpInl_add_lpInr _ _
  rw [hfun]
  exact ((lpInl : E₁ →L[ℝ] WithLp 2 (E₁ × E₂)).contMDiff.comp
        ((Real.contDiff_sin.contMDiff.comp hfst).smul h21)).add
      ((lpInr : E₂ →L[ℝ] WithLp 2 (E₁ × E₂)).contMDiff.comp
        ((Real.contDiff_cos.contMDiff.comp hfst).smul h22))

/-- **Eng.** The single warped component `(t, x) ↦ sin(t)·x` is smooth. -/
theorem contMDiff_sinSmulSphere :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, E₁) ∞
      (fun p : ℝ × sphere (0 : E₁) 1 => Real.sin p.1 • (p.2 : E₁)) :=
  (Real.contDiff_sin.contMDiff.comp contMDiff_fst).smul (contMDiff_coe_sphere.comp contMDiff_snd)

/-- **Eng.** The first projection of `ℝ × S^{n₁}` is smooth. -/
theorem mdifferentiableAt_fstSphere (p : ℝ × sphere (0 : E₁) 1) :
    MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, ℝ)
      (Prod.fst : ℝ × sphere (0 : E₁) 1 → ℝ) p :=
  (contMDiffAt_fst : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, ℝ) ∞ Prod.fst p).mdifferentiableAt
    (by simp)

/-- **Eng.** The ambient sphere coordinate of `ℝ × S^{n₁}` is smooth. -/
theorem mdifferentiableAt_coeSndSphere (p : ℝ × sphere (0 : E₁) 1) :
    MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, E₁)
      (fun q : ℝ × sphere (0 : E₁) 1 => (q.2 : E₁)) p :=
  ((contMDiff_coe_sphere.comp contMDiff_snd :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, E₁) ∞
      fun q : ℝ × sphere (0 : E₁) 1 => (q.2 : E₁)) p).mdifferentiableAt (by simp)

/-- **Eng.** The differential of `q ↦ (q.2 : E₁)` is the differential of the sphere inclusion
applied to the second component of the tangent vector. -/
theorem mfderiv_coeSndSphere_apply (p : ℝ × sphere (0 : E₁) 1)
    (x : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n₁)) p) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, E₁)
        (fun q : ℝ × sphere (0 : E₁) 1 => (q.2 : E₁)) p x
      = mfderiv (𝓡 n₁) 𝓘(ℝ, E₁) ((↑) : sphere (0 : E₁) 1 → E₁) p.2 x.2 := by
  have hcomp : (fun q : ℝ × sphere (0 : E₁) 1 => (q.2 : E₁))
      = ((↑) : sphere (0 : E₁) 1 → E₁) ∘ Prod.snd := rfl
  have hsndM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 n₁)) (𝓡 n₁)
      (Prod.snd : ℝ × sphere (0 : E₁) 1 → sphere (0 : E₁) 1) p :=
    (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n₁)) (𝓡 n₁) ∞ Prod.snd p).mdifferentiableAt
      (by simp)
  have hιM : MDifferentiableAt (𝓡 n₁) 𝓘(ℝ, E₁) ((↑) : sphere (0 : E₁) 1 → E₁) p.2 :=
    (contMDiff_coe_sphere (m := 1) p.2).mdifferentiableAt one_ne_zero
  have hsndD : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n₁)) (𝓡 n₁) Prod.snd p x = x.2 := by
    rw [mfderiv_snd]; rfl
  rw [hcomp, mfderiv_comp p hιM hsndM, ContinuousLinearMap.comp_apply, hsndD]

/-- **Eng.** The differential of the first projection is the first component of the tangent
vector. -/
theorem mfderiv_fstSphere_apply (p : ℝ × sphere (0 : E₁) 1)
    (x : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 n₁)) p) :
    mfderiv (𝓘(ℝ, ℝ).prod (𝓡 n₁)) 𝓘(ℝ, ℝ) (Prod.fst : ℝ × sphere (0 : E₁) 1 → ℝ) p x = x.1 := by
  rw [mfderiv_fst]; rfl

end Generic

/-! ## Real scalars on `ℂ^m` -/

section RealScalars

variable {m : ℕ}

/-- **Eng.** A real scalar acts on `ℂ^m` through its complex image.  Rewriting real scalar
multiplications into complex ones is the escape hatch from the `ℝ`-module diamond of
`EuclideanSpace ℂ (Fin m)`, on which `real_inner_smul_left/right` do not elaborate. -/
theorem real_smul_eq_ofReal_smul (s : ℝ) (v : EuclideanSpace ℂ (Fin m)) :
    s • v = ((s : ℂ)) • v := by
  refine PiLp.ext fun k => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, Complex.real_smul, smul_eq_mul]

/-- **Eng.** The norm of a real multiple on `ℂ^m` (`norm_smul` itself does not elaborate for the
restricted real action). -/
theorem norm_real_smul_euclidean (s : ℝ) (v : EuclideanSpace ℂ (Fin m)) :
    ‖s • v‖ = |s| * ‖v‖ := by
  rw [real_smul_eq_ofReal_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs]

/-- **Eng.** The real inner product of `ℂ^m` is `ℝ`-linear in the right slot, phrased with a
complex scalar of real type. -/
theorem real_inner_ofReal_smul_right (s : ℝ) (a b : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ a (((s : ℂ)) • b) : ℝ) = s * inner ℝ a b := by
  rw [real_inner_eq_re_inner_euclideanSpace, real_inner_eq_re_inner_euclideanSpace,
    inner_smul_right, Complex.re_ofReal_mul]

/-- **Eng.** The real inner product of `ℂ^m` is `ℝ`-linear in the left slot, phrased with a
complex scalar of real type. -/
theorem real_inner_ofReal_smul_left (s : ℝ) (a b : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ (((s : ℂ)) • a) b : ℝ) = s * inner ℝ a b := by
  rw [real_inner_eq_re_inner_euclideanSpace, real_inner_eq_re_inner_euclideanSpace,
    inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul]

/-- **Eng.** Multiplication by `i` commutes with real scalars on `ℂ^m`. -/
theorem complexI_smul_real_smul (s : ℝ) (v : EuclideanSpace ℂ (Fin m)) :
    Complex.I • (s • v) = s • (Complex.I • v) := by
  rw [real_smul_I_smul, real_smul_eq_ofReal_smul s v, smul_smul, mul_comm]

end RealScalars

variable {n : ℕ}

/-- Local shorthand for the ambient space `ℂ^{n+1}` of `S^{2n+1}`. -/
local notation "𝔼₁" => EuclideanSpace ℂ (Fin (n + 1))

/-- Local shorthand for the ambient space `ℂ^{n+2}` of `S^{2n+3}` and `ℂP^{n+1}`. -/
local notation "𝔼₂" => EuclideanSpace ℂ (Fin (n + 2))

/-! ## The parametrization of `S^{2n+3}` and the base map into `ℂP^{n+1}` -/

/-- **Math.** Petersen Example 1.4.14: the doubly warped parametrization
`(t, ζ, w) ↦ (sin(t)·ζ, cos(t)·w)` of the round sphere `S^{2n+3} ⊆ ℂ^{n+2}`. -/
def genHopfSphere (q : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1) : sphere (0 : 𝔼₂) 1 :=
  ⟨genHopfAmbient q, mem_sphere_zero_iff_norm.mpr (norm_genHopfAmbient q)⟩

@[simp] theorem coe_genHopfSphere (q : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1) :
    (genHopfSphere q : 𝔼₂) = genHopfAmbient q := rfl

/-- **Math.** The ambient base map `(t, ζ) ↦ (sin(t)·ζ, cos(t)) ∈ ℂ^{n+2}`: the `w = 1` slice of
the parametrization `genHopfAmbient`. -/
def genHopfBaseAmbient (p : ℝ × sphere (0 : 𝔼₁) 1) : 𝔼₂ :=
  snocLpEquiv (WithLp.toLp 2 (Real.sin p.1 • (p.2 : 𝔼₁), ((Real.cos p.1 : ℝ) : ℂ)))

/-- **Math.** The base map lands in the unit sphere: `|sin(t)·ζ|² + |cos(t)|² = 1`. -/
theorem norm_genHopfBaseAmbient (p : ℝ × sphere (0 : 𝔼₁) 1) : ‖genHopfBaseAmbient p‖ = 1 := by
  rw [genHopfBaseAmbient, snocLpEquiv.norm_map, WithLp.prod_norm_eq_of_L2]
  simp only [WithLp.toLp_fst, WithLp.toLp_snd, norm_real_smul_euclidean, norm_eq_of_mem_sphere,
    mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Real.sin_sq_add_cos_sq, Real.sqrt_one]

/-- **Math.** The base map into the unit sphere `S^{2n+3} ⊆ ℂ^{n+2}`. -/
def genHopfBaseSphere (p : ℝ × sphere (0 : 𝔼₁) 1) : sphere (0 : 𝔼₂) 1 :=
  ⟨genHopfBaseAmbient p, mem_sphere_zero_iff_norm.mpr (norm_genHopfBaseAmbient p)⟩

@[simp] theorem coe_genHopfBaseSphere (p : ℝ × sphere (0 : 𝔼₁) 1) :
    (genHopfBaseSphere p : 𝔼₂) = genHopfBaseAmbient p := rfl

/-- **Math.** Petersen Example 1.4.14: the base map
`ψ : I × S^{2n+1} → ℂP^{n+1}`, `ψ(t, ζ) = [sin(t)·ζ : cos(t)]`,
of the generalized Hopf fibration. -/
def genHopfBase (p : ℝ × sphere (0 : 𝔼₁) 1) : ComplexProjectiveSpace (n + 1) :=
  projSphere (genHopfBaseSphere p)

/-! ## Smoothness -/

/-- **Eng.** The `Fin.snoc` isometry `ℂ^{n+1} ⊕₂ ℂ ≅ ℂ^{n+2}` as a continuous `ℝ`-linear map. -/
def snocCLM : WithLp 2 (𝔼₁ × ℂ) →L[ℝ] 𝔼₂ :=
  (snocLpEquiv (n := n)).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem snocCLM_apply (x : WithLp 2 (𝔼₁ × ℂ)) : snocCLM x = snocLpEquiv x := rfl

/-- **Eng.** The parametrization of `S^{2n+3}` is smooth: it is the smooth doubly warped map into
the `ℓ²`-product, followed by the linear isometry `snocLpEquiv`. -/
theorem contMDiff_genHopfAmbient :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) 𝓘(ℝ, 𝔼₂) ∞
      (genHopfAmbient : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1 → 𝔼₂) := by
  have hfun : (genHopfAmbient : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1 → 𝔼₂)
      = fun q => snocCLM (WithLp.toLp 2
          (Real.sin q.1 • (q.2.1 : 𝔼₁), Real.cos q.1 • (q.2.2 : ℂ))) := by
    funext q; exact genHopfAmbient_eq q
  rw [hfun]
  exact snocCLM.contMDiff.comp contMDiff_doublyWarpedSphereAmbient

/-- **Eng.** The parametrization of `S^{2n+3}`, as a map into the sphere, is smooth. -/
theorem contMDiff_genHopfSphere :
    ContMDiff (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) (𝓡 (2 * (n + 1) + 1)) ∞
      (genHopfSphere : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1 → sphere (0 : 𝔼₂) 1) :=
  ContMDiff.codRestrict_sphere contMDiff_genHopfAmbient
    fun q => mem_sphere_zero_iff_norm.mpr (norm_genHopfAmbient q)

/-- **Eng.** The differential of the parametrization, read in the ambient space: the differential
of `genHopfSphere` followed by the differential of the inclusion is the differential of
`genHopfAmbient`. -/
theorem mfderiv_coe_genHopfSphere (p : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1)
    (u : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) p) :
    mfderiv (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, 𝔼₂) ((↑) : sphere (0 : 𝔼₂) 1 → 𝔼₂) (genHopfSphere p)
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) (𝓡 (2 * (n + 1) + 1))
          genHopfSphere p u)
      = mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) 𝓘(ℝ, 𝔼₂) genHopfAmbient p u := by
  have hGS : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1)))
      (𝓡 (2 * (n + 1) + 1)) genHopfSphere p :=
    (contMDiff_genHopfSphere p).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, 𝔼₂)
      ((↑) : sphere (0 : 𝔼₂) 1 → 𝔼₂) (genHopfSphere p) :=
    (contMDiff_coe_sphere (m := 1) (genHopfSphere p)).mdifferentiableAt one_ne_zero
  have hEq : (genHopfAmbient : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1 → 𝔼₂)
      = ((↑) : sphere (0 : 𝔼₂) 1 → 𝔼₂) ∘ genHopfSphere := rfl
  rw [hEq, mfderiv_comp p hι hGS]
  rfl

/-! ## (I) The source is the round sphere `S^{2n+3}` -/

/-- **Math.** Petersen Example 1.4.14, source clause: the doubly warped product
`I × S^{2n+1} × S¹` with `dt² + sin²(t) ds²_{2n+1} + cos²(t) dθ²` is the *round* sphere
`S^{2n+3} ⊆ ℂ^{n+2}`: the parametrization `(t, ζ, w) ↦ (sin(t)·ζ, cos(t)·w)` pulls the round
metric back to the doubly warped metric.  Restated from `pullbackForm_genHopfAmbient` by the chain
rule, since the round metric of the sphere is the pullback of the ambient inner product. -/
theorem pullbackForm_genHopfSphere (p : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1)
    (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1)))
        (sphereMetricUnit (n := 2 * (n + 1) + 1) 𝔼₂) genHopfSphere p u v
      = doublyWarpedProductForm (sphereMetricUnit (n := 2 * n + 1) 𝔼₁)
          (sphereMetricUnit (n := 1) ℂ) Real.sin Real.cos p u v := by
  have hpb := pullbackForm_genHopfAmbient p u v
  rw [pullbackForm_apply, innerProductSpaceMetric_apply] at hpb
  rw [pullbackForm_apply, sphereMetricUnit_apply, mfderiv_coe_genHopfSphere p u,
    mfderiv_coe_genHopfSphere p v]
  exact hpb

/-! ## (II) The commuting square: the quotient is `ℂP^{n+1}` -/

/-- **Math.** The parametrization `(t, ζ, w) ↦ (sin(t)·ζ, cos(t)·w)` of `S^{2n+3}` and the base
map `(t, ζ) ↦ (sin(t)·ζ, cos(t))` differ, along the quotient map `(t, ζ, w) ↦ (t, w⁻¹·ζ)` of
Example 1.4.12, exactly by the unit complex scalar `w`:

  `w · ψ(t, w⁻¹·ζ) = (w·sin(t)·w⁻¹·ζ, w·cos(t)) = (sin(t)·ζ, cos(t)·w) = Φ(t, ζ, w)`.

This is the whole content of Example 1.4.14's identification of the quotient with `ℂP^{n+1}`:
the two ambient points lie on the same complex line. -/
theorem smul_genHopfBaseAmbient (q : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1) :
    ((q.2.2 : ℂ)) • genHopfBaseAmbient (hopfSphereQuotientMap q) = genHopfAmbient q := by
  have hne : (q.2.2 : ℂ) ≠ 0 := by
    intro h
    have h1 : ‖(q.2.2 : ℂ)‖ = 1 := norm_eq_of_mem_sphere q.2.2
    rw [h, norm_zero] at h1
    exact zero_ne_one h1
  have hcoe : (((q.2.2⁻¹ • q.2.1 : sphere (0 : 𝔼₁) 1)) : 𝔼₁)
      = ((q.2.2 : ℂ))⁻¹ • (q.2.1 : 𝔼₁) := rfl
  have hfst : ((q.2.2 : ℂ)) • (Real.sin q.1 • (((q.2.2⁻¹ • q.2.1 : sphere (0 : 𝔼₁) 1)) : 𝔼₁))
      = Real.sin q.1 • (q.2.1 : 𝔼₁) := by
    rw [hcoe, real_smul_eq_ofReal_smul, real_smul_eq_ofReal_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  have hsnd : ((q.2.2 : ℂ)) • ((Real.cos q.1 : ℝ) : ℂ) = Real.cos q.1 • (q.2.2 : ℂ) := by
    rw [smul_eq_mul, Complex.real_smul, mul_comm]
  rw [genHopfAmbient_eq, genHopfBaseAmbient, ← snocLpEquiv_complex_smul]
  congr 1
  have hsmul : ((q.2.2 : ℂ)) • (WithLp.toLp 2
        (Real.sin (hopfSphereQuotientMap q).1 • ((hopfSphereQuotientMap q).2 : 𝔼₁),
          ((Real.cos (hopfSphereQuotientMap q).1 : ℝ) : ℂ)) : WithLp 2 (𝔼₁ × ℂ))
      = WithLp.toLp 2
        (((q.2.2 : ℂ)) • (Real.sin q.1 • (((q.2.2⁻¹ • q.2.1 : sphere (0 : 𝔼₁) 1)) : 𝔼₁)),
          ((q.2.2 : ℂ)) • ((Real.cos q.1 : ℝ) : ℂ)) := rfl
  rw [hsmul, hfst, hsnd]

/-- **Math.** Petersen Example 1.4.14, **the commuting square**: the Hopf projection
`π : S^{2n+3} → ℂP^{n+1}` intertwines the parametrization `Φ` of `S^{2n+3}` with the base map
`ψ(t, ζ) = [sin(t)·ζ : cos(t)]` and the circle quotient map `(t, ζ, w) ↦ (t, w⁻¹·ζ)` of Example
1.4.12.  Hence the quotient of Example 1.4.12 *is* `ℂP^{n+1}` and its quotient metric *is* the
Fubini–Study metric. -/
theorem projSphere_genHopfSphere (q : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1) :
    projSphere (genHopfSphere q) = genHopfBase (hopfSphereQuotientMap q) := by
  have h : projSphere (genHopfBaseSphere (hopfSphereQuotientMap q))
      = projSphere (genHopfSphere q) := by
    refine (projSphere_eq_iff _ _).mpr ⟨⟨(q.2.2 : ℂ), q.2.2.2⟩, ?_⟩
    apply Subtype.ext
    exact smul_genHopfBaseAmbient q
  exact h.symm

/-! ## The two blocks of `ℂ^{n+2} = ℂ^{n+1} ⊕₂ ℂ` -/

/-- **Eng.** The inclusion of the first block `ℂ^{n+1} ↪ ℂ^{n+2}`, `a ↦ (a, 0)`. -/
def snocInl : 𝔼₁ →L[ℝ] 𝔼₂ := snocCLM.comp (lpInl : 𝔼₁ →L[ℝ] WithLp 2 (𝔼₁ × ℂ))

/-- **Eng.** The inclusion of the last block `ℂ ↪ ℂ^{n+2}`, `c ↦ (0, c)`. -/
def snocInr : ℂ →L[ℝ] 𝔼₂ := snocCLM.comp (lpInr : ℂ →L[ℝ] WithLp 2 (𝔼₁ × ℂ))

theorem snocInl_apply (a : 𝔼₁) : snocInl a = snocLpEquiv (WithLp.toLp 2 (a, 0)) := rfl

theorem snocInr_apply (c : ℂ) :
    snocInr (n := n) c = snocLpEquiv (WithLp.toLp 2 ((0 : 𝔼₁), c)) := rfl

/-- **Math.** The two blocks are orthogonal and the first is isometric: `⟪(a,0), (b,0)⟫ = ⟪a,b⟫`. -/
theorem real_inner_snocInl_snocInl (a b : 𝔼₁) :
    (inner ℝ (snocInl a) (snocInl b) : ℝ) = inner ℝ a b := by
  rw [snocInl_apply, snocInl_apply, snocLpEquiv.inner_map_map]
  simp [WithLp.prod_inner_apply]

/-- **Math.** The last block is isometric: `⟪(0,c), (0,d)⟫ = ⟪c,d⟫`. -/
theorem real_inner_snocInr_snocInr (c d : ℂ) :
    (inner ℝ (snocInr (n := n) c) (snocInr (n := n) d) : ℝ) = inner ℝ c d := by
  rw [snocInr_apply, snocInr_apply, snocLpEquiv.inner_map_map]
  simp [WithLp.prod_inner_apply]

/-- **Math.** The two blocks are orthogonal: `⟪(a,0), (0,c)⟫ = 0`. -/
theorem real_inner_snocInl_snocInr (a : 𝔼₁) (c : ℂ) :
    (inner ℝ (snocInl a) (snocInr c) : ℝ) = 0 := by
  rw [snocInl_apply, snocInr_apply, snocLpEquiv.inner_map_map]
  simp [WithLp.prod_inner_apply]

/-- **Math.** The two blocks are orthogonal: `⟪(0,c), (a,0)⟫ = 0`. -/
theorem real_inner_snocInr_snocInl (c : ℂ) (a : 𝔼₁) :
    (inner ℝ (snocInr c) (snocInl a) : ℝ) = 0 := by
  rw [snocInl_apply, snocInr_apply, snocLpEquiv.inner_map_map]
  simp [WithLp.prod_inner_apply]

/-- **Eng.** The base map in block form: `ψ(t, ζ) = (sin(t)·ζ, cos(t))`. -/
theorem genHopfBaseAmbient_eq_add (p : ℝ × sphere (0 : 𝔼₁) 1) :
    genHopfBaseAmbient p
      = snocInl (Real.sin p.1 • (p.2 : 𝔼₁)) + snocInr (((Real.cos p.1 : ℝ) : ℂ)) := by
  have h : (WithLp.toLp 2 (Real.sin p.1 • (p.2 : 𝔼₁), ((Real.cos p.1 : ℝ) : ℂ))
        : WithLp 2 (𝔼₁ × ℂ))
      = (lpInl : 𝔼₁ →L[ℝ] WithLp 2 (𝔼₁ × ℂ)) (Real.sin p.1 • (p.2 : 𝔼₁))
        + (lpInr : ℂ →L[ℝ] WithLp 2 (𝔼₁ × ℂ)) (((Real.cos p.1 : ℝ) : ℂ)) :=
    toLp_eq_lpInl_add_lpInr _ _
  rw [genHopfBaseAmbient, h, map_add]
  rfl

/-- **Eng.** The base map is smooth. -/
theorem contMDiff_genHopfBaseAmbient :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) ∞
      (genHopfBaseAmbient : ℝ × sphere (0 : 𝔼₁) 1 → 𝔼₂) := by
  have hfun : (genHopfBaseAmbient : ℝ × sphere (0 : 𝔼₁) 1 → 𝔼₂)
      = (fun p : ℝ × sphere (0 : 𝔼₁) 1 => snocInl (Real.sin p.1 • (p.2 : 𝔼₁)))
        + fun p : ℝ × sphere (0 : 𝔼₁) 1 => snocInr (((Real.cos p.1 : ℝ) : ℂ)) :=
    funext genHopfBaseAmbient_eq_add
  rw [hfun]
  exact (snocInl.contMDiff.comp contMDiff_sinSmulSphere).add
    (snocInr.contMDiff.comp ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).contMDiff.comp
      (Real.contDiff_cos.contMDiff.comp contMDiff_fst)))

/-- **Eng.** The base map into the sphere is smooth. -/
theorem contMDiff_genHopfBaseSphere :
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) (𝓡 (2 * (n + 1) + 1)) ∞
      (genHopfBaseSphere : ℝ × sphere (0 : 𝔼₁) 1 → sphere (0 : 𝔼₂) 1) :=
  ContMDiff.codRestrict_sphere contMDiff_genHopfBaseAmbient
    fun p => mem_sphere_zero_iff_norm.mpr (norm_genHopfBaseAmbient p)

/-- **Eng.** The differential of the base map, in block form:
`Dψ(x) = ((cos(t)·x₁)·ζ + sin(t)·ζ̇, -sin(t)·x₁)`. -/
theorem mfderiv_genHopfBaseAmbient_apply (p : ℝ × sphere (0 : 𝔼₁) 1)
    (x : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p) :
    (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x : 𝔼₂)
      = snocInl ((Real.cos p.1 * x.1) • (p.2 : 𝔼₁) + Real.sin p.1 • sphereAmbient p.2 x.2)
        + snocInr (((-Real.sin p.1 * x.1 : ℝ) : ℂ)) := by
  have hfstM := mdifferentiableAt_fstSphere (E₁ := 𝔼₁) (n₁ := 2 * n + 1) p
  have hwM := mdifferentiableAt_coeSndSphere (E₁ := 𝔼₁) (n₁ := 2 * n + 1) p
  have hf₁ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₁)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.sin q.1 • (q.2 : 𝔼₁)) p :=
    (contMDiff_sinSmulSphere (E₁ := 𝔼₁) (n₁ := 2 * n + 1) p).mdifferentiableAt (by simp)
  have hcosM : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℝ)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.cos q.1) p :=
    (Real.hasDerivAt_cos p.1).differentiableAt.comp_mdifferentiableAt hfstM
  have hf₂ : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p :=
    (HasMFDerivAt.comp p ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasFDerivAt.hasMFDerivAt)
      hcosM.hasMFDerivAt).mdifferentiableAt
  have hD₁ : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => snocInl (Real.sin q.1 • (q.2 : 𝔼₁))) p
      (snocInl.comp (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₁)
        (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.sin q.1 • (q.2 : 𝔼₁)) p)) :=
    HasMFDerivAt.comp p snocInl.hasFDerivAt.hasMFDerivAt hf₁.hasMFDerivAt
  have hD₂ : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => snocInr (((Real.cos q.1 : ℝ) : ℂ))) p
      (snocInr.comp (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
        (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p)) :=
    HasMFDerivAt.comp p snocInr.hasFDerivAt.hasMFDerivAt hf₂.hasMFDerivAt
  have hD : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p
      (snocInl.comp (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₁)
          (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.sin q.1 • (q.2 : 𝔼₁)) p)
        + snocInr.comp (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
          (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p)) := by
    have hfun : (genHopfBaseAmbient : ℝ × sphere (0 : 𝔼₁) 1 → 𝔼₂)
        = (fun q : ℝ × sphere (0 : 𝔼₁) 1 => snocInl (Real.sin q.1 • (q.2 : 𝔼₁)))
          + fun q : ℝ × sphere (0 : 𝔼₁) 1 => snocInr (((Real.cos q.1 : ℝ) : ℂ)) :=
      funext genHopfBaseAmbient_eq_add
    rw [hfun]
    exact hD₁.add hD₂
  have hDf₁ : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₁)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.sin q.1 • (q.2 : 𝔼₁)) p x
      = (Real.cos p.1 * x.1) • (p.2 : 𝔼₁) + Real.sin p.1 • sphereAmbient p.2 x.2 := by
    have h := mfderiv_warpSmul_apply (J := 𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) (c := Prod.fst)
      (w := fun q : ℝ × sphere (0 : 𝔼₁) 1 => (q.2 : 𝔼₁)) (f := Real.sin) (f' := Real.cos p.1)
      hfstM hwM (Real.hasDerivAt_sin p.1) x
    simpa only [fromTangentSpace_apply, mfderiv_fstSphere_apply, mfderiv_coeSndSphere_apply]
      using h
  have hDf₂ : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
      (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p x
      = ((-Real.sin p.1 * x.1 : ℝ) : ℂ) := by
    have hD' : HasMFDerivAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
        (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p
        ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp
          (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℝ)
            (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.cos q.1) p)) :=
      HasMFDerivAt.comp p ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).hasFDerivAt.hasMFDerivAt)
        hcosM.hasMFDerivAt
    have h2 : mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
        (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p x
        = (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℝ)
            (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.cos q.1) p x) := by
      rw [hD'.mfderiv]; rfl
    rw [h2, mfderiv_comp_fst_apply (Real.hasDerivAt_cos p.1) x]
    rfl
  have hsplit : (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x : 𝔼₂)
      = snocInl (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₁)
          (fun q : ℝ × sphere (0 : 𝔼₁) 1 => Real.sin q.1 • (q.2 : 𝔼₁)) p x)
        + snocInr (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, ℂ)
          (fun q : ℝ × sphere (0 : 𝔼₁) 1 => ((Real.cos q.1 : ℝ) : ℂ)) p x) := by
    rw [hD.mfderiv]; rfl
  rw [hsplit, hDf₁, hDf₂]

/-! ## (IV) The Fubini–Study representation -/

/-- **Math.** The ambient inner product of two velocities of the base map:
`⟪Dψ(x), Dψ(y)⟫ = x₁y₁ + sin²(t) ⟪ζ̇, ζ̇'⟫`.

The `cos²(t)·x₁y₁` coming from the `ℂ^{n+1}` block and the `sin²(t)·x₁y₁` coming from the last
block add up to `x₁y₁`; the cross terms vanish because `⟪ζ, ζ̇⟫ = 0` on the sphere. -/
theorem real_inner_mfderiv_genHopfBaseAmbient (p : ℝ × sphere (0 : 𝔼₁) 1)
    (x y : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p) :
    (@inner ℝ 𝔼₂ _ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p y) : ℝ)
      = x.1 * y.1
        + Real.sin p.1 ^ 2 * (inner ℝ (sphereAmbient p.2 x.2) (sphereAmbient p.2 y.2) : ℝ) := by
  have hζζ : (inner ℝ (p.2 : 𝔼₁) (p.2 : 𝔼₁) : ℝ) = 1 := real_inner_coe_self_sphere p.2
  have hζd : ∀ u : TangentSpace (𝓡 (2 * n + 1)) p.2,
      (inner ℝ (p.2 : 𝔼₁) (sphereAmbient p.2 u) : ℝ) = 0 :=
    fun u => inner_coe_mfderiv_coe_unitSphere p.2 u
  have hdζ : ∀ u : TangentSpace (𝓡 (2 * n + 1)) p.2,
      (inner ℝ (sphereAmbient p.2 u) (p.2 : 𝔼₁) : ℝ) = 0 :=
    fun u => inner_mfderiv_coe_sphere_coe p.2 u
  have hx : @Eq 𝔼₂ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x)
      (snocInl ((Real.cos p.1 * x.1) • (p.2 : 𝔼₁) + Real.sin p.1 • sphereAmbient p.2 x.2)
        + snocInr (((-Real.sin p.1 * x.1 : ℝ) : ℂ))) :=
    mfderiv_genHopfBaseAmbient_apply p x
  have hy : @Eq 𝔼₂ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p y)
      (snocInl ((Real.cos p.1 * y.1) • (p.2 : 𝔼₁) + Real.sin p.1 • sphereAmbient p.2 y.2)
        + snocInr (((-Real.sin p.1 * y.1 : ℝ) : ℂ))) :=
    mfderiv_genHopfBaseAmbient_apply p y
  rw [hx, hy]
  simp only [map_add, map_smul, inner_add_left, inner_add_right]
  simp only [real_smul_eq_ofReal_smul, real_inner_ofReal_smul_left, real_inner_ofReal_smul_right,
    real_inner_snocInl_snocInl, real_inner_snocInr_snocInr, real_inner_snocInl_snocInr,
    real_inner_snocInr_snocInl, real_inner_complex, Complex.ofReal_re, Complex.ofReal_im,
    hζζ, hζd, hdζ]
  linear_combination (x.1 * y.1) * Real.sin_sq_add_cos_sq p.1

/-- **Math.** The Hopf direction at `ψ(t, ζ)`, in block form:
`i·ψ(t, ζ) = (sin(t)·(i·ζ), i·cos(t))`. -/
theorem I_smul_genHopfBaseAmbient (p : ℝ × sphere (0 : 𝔼₁) 1) :
    Complex.I • genHopfBaseAmbient p
      = snocInl (Real.sin p.1 • (Complex.I • (p.2 : 𝔼₁)))
        + snocInr (Complex.I * ((Real.cos p.1 : ℝ) : ℂ)) := by
  have hsmul : (Complex.I • (WithLp.toLp 2
        (Real.sin p.1 • (p.2 : 𝔼₁), ((Real.cos p.1 : ℝ) : ℂ)) : WithLp 2 (𝔼₁ × ℂ)))
      = WithLp.toLp 2 (Real.sin p.1 • (Complex.I • (p.2 : 𝔼₁)),
          Complex.I * ((Real.cos p.1 : ℝ) : ℂ)) := by
    show (WithLp.toLp 2 (Complex.I • (Real.sin p.1 • (p.2 : 𝔼₁)),
        Complex.I • ((Real.cos p.1 : ℝ) : ℂ)) : WithLp 2 (𝔼₁ × ℂ)) = _
    rw [complexI_smul_real_smul, smul_eq_mul]
  have hadd : (WithLp.toLp 2 (Real.sin p.1 • (Complex.I • (p.2 : 𝔼₁)),
        Complex.I * ((Real.cos p.1 : ℝ) : ℂ)) : WithLp 2 (𝔼₁ × ℂ))
      = (lpInl : 𝔼₁ →L[ℝ] WithLp 2 (𝔼₁ × ℂ)) (Real.sin p.1 • (Complex.I • (p.2 : 𝔼₁)))
        + (lpInr : ℂ →L[ℝ] WithLp 2 (𝔼₁ × ℂ)) (Complex.I * ((Real.cos p.1 : ℝ) : ℂ)) :=
    toLp_eq_lpInl_add_lpInr _ _
  rw [genHopfBaseAmbient, ← snocLpEquiv_complex_smul, hsmul, hadd, map_add]
  rfl

/-- **Math.** The Hopf 1-form of `S^{2n+3}` pulled back by the base map is `sin²(t)` times the
Hopf 1-form of `S^{2n+1}`:
`⟪i·ψ(t, ζ), Dψ(x)⟫ = sin²(t)·θ_ζ(x₂)`.
The last block contributes `⟪i·cos(t), -sin(t)x₁⟫ = 0` (purely imaginary against purely real), and
in the first block `⟪i·ζ, ζ⟫ = 0` kills the radial term. -/
theorem real_inner_I_smul_mfderiv_genHopfBaseAmbient (p : ℝ × sphere (0 : 𝔼₁) 1)
    (x : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p) :
    (@inner ℝ 𝔼₂ _ (Complex.I • genHopfBaseAmbient p)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x) : ℝ)
      = Real.sin p.1 ^ 2 * hopfAngleForm p.2 x.2 := by
  have hIζ : (inner ℝ (Complex.I • (p.2 : 𝔼₁)) (p.2 : 𝔼₁) : ℝ) = 0 := by
    rw [real_inner_comm]
    exact real_inner_I_smul_coe_sphere p.2
  have hx : @Eq 𝔼₂ (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x)
      (snocInl ((Real.cos p.1 * x.1) • (p.2 : 𝔼₁) + Real.sin p.1 • sphereAmbient p.2 x.2)
        + snocInr (((-Real.sin p.1 * x.1 : ℝ) : ℂ))) :=
    mfderiv_genHopfBaseAmbient_apply p x
  rw [I_smul_genHopfBaseAmbient, hx, hopfAngleForm_apply]
  simp only [map_add, map_smul, inner_add_left, inner_add_right]
  simp only [real_smul_eq_ofReal_smul, real_inner_ofReal_smul_left, real_inner_ofReal_smul_right,
    real_inner_snocInl_snocInl, real_inner_snocInr_snocInr, real_inner_snocInl_snocInr,
    real_inner_snocInr_snocInl, real_inner_complex, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, hIζ]
  ring

/-- **Eng.** The differential of the base map into the sphere, read in the ambient space. -/
theorem mfderiv_coe_genHopfBaseSphere (p : ℝ × sphere (0 : 𝔼₁) 1)
    (x : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p) :
    sphereAmbient (genHopfBaseSphere p)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) (𝓡 (2 * (n + 1) + 1)) genHopfBaseSphere p x)
      = mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, 𝔼₂) genHopfBaseAmbient p x := by
  have hGBS : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1)))
      (𝓡 (2 * (n + 1) + 1)) genHopfBaseSphere p :=
    (contMDiff_genHopfBaseSphere p).mdifferentiableAt (by simp)
  have hι : MDifferentiableAt (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, 𝔼₂)
      ((↑) : sphere (0 : 𝔼₂) 1 → 𝔼₂) (genHopfBaseSphere p) :=
    (contMDiff_coe_sphere (m := 1) (genHopfBaseSphere p)).mdifferentiableAt one_ne_zero
  have hEq : (genHopfBaseAmbient : ℝ × sphere (0 : 𝔼₁) 1 → 𝔼₂)
      = ((↑) : sphere (0 : 𝔼₂) 1 → 𝔼₂) ∘ genHopfBaseSphere := rfl
  rw [hEq, mfderiv_comp p hι hGBS]
  rfl

/-- **Math.** Petersen Example 1.4.14, **the payoff**: the base map
`ψ(t, ζ) = [sin(t)·ζ : cos(t)]` pulls the Fubini–Study metric of `ℂP^{n+1}` back to

  `dt² + sin²(t)·(g - θ²) + sin²(t)cos²(t)·θ²`,

which is exactly the quotient form of Example 1.4.12 for `ρ = sin`, `φ = cos` (whose warping
coefficient of the fibre direction is `(ρφ)²/(ρ² + φ²) = sin²(t)cos²(t)`).  Equivalently, in
Petersen's notation, `dt² + sin²(t)(g + cos²(t) h)`.

The proof: `Dπ` kills the Hopf direction and is an isometry on its orthogonal complement
(`fubiniStudy_mfderiv_projSphere`), so the Fubini–Study inner product of the velocities is
`⟪Dψ(x), Dψ(y)⟫ - θ(Dψ(x))·θ(Dψ(y))`; the two computations above evaluate the two summands, and
`sin²·cos² - sin² + sin⁴ = -sin²(1 - sin² - cos²) = 0` closes it. -/
theorem pullbackForm_genHopfBase
    (gFS : RiemannianMetric 𝓘(ℝ, Fin (n + 1) → ℂ) (ComplexProjectiveSpace (n + 1)))
    (hFS : IsRiemannianSubmersion (sphereMetricUnit (n := 2 * (n + 1) + 1) 𝔼₂) gFS projSphere)
    (p : ℝ × sphere (0 : 𝔼₁) 1)
    (x y : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p) :
    pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) gFS genHopfBase p x y
      = hopfQuotientForm (fun t => Real.sin t * Real.cos t) Real.sin p x y := by
  have hGBS : MDifferentiableAt (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1)))
      (𝓡 (2 * (n + 1) + 1)) genHopfBaseSphere p :=
    (contMDiff_genHopfBaseSphere p).mdifferentiableAt (by simp)
  have hproj : MDifferentiableAt (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ)
      projSphere (genHopfBaseSphere p) :=
    ((contMDiff_projSphere (n := n + 1)) (genHopfBaseSphere p)).mdifferentiableAt (by simp)
  have hchain : ∀ w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) 𝓘(ℝ, Fin (n + 1) → ℂ) genHopfBase p w
        = mfderiv (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) projSphere (genHopfBaseSphere p)
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) (𝓡 (2 * (n + 1) + 1))
              genHopfBaseSphere p w) := by
    intro w
    have hEq : (genHopfBase : ℝ × sphere (0 : 𝔼₁) 1 → ComplexProjectiveSpace (n + 1))
        = projSphere ∘ genHopfBaseSphere := rfl
    rw [hEq, mfderiv_comp p hproj hGBS]
    rfl
  have hstep : pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) gFS genHopfBase p x y
      = gFS.metricInner (projSphere (genHopfBaseSphere p))
          (mfderiv (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) projSphere (genHopfBaseSphere p)
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) (𝓡 (2 * (n + 1) + 1))
              genHopfBaseSphere p x))
          (mfderiv (𝓡 (2 * (n + 1) + 1)) 𝓘(ℝ, Fin (n + 1) → ℂ) projSphere (genHopfBaseSphere p)
            (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) (𝓡 (2 * (n + 1) + 1))
              genHopfBaseSphere p y)) := by
    rw [pullbackForm_apply, hchain x, hchain y]
    rfl
  rw [hstep, fubiniStudy_mfderiv_projSphere gFS hFS, hopfAngleForm_apply, hopfAngleForm_apply,
    mfderiv_coe_genHopfBaseSphere, mfderiv_coe_genHopfBaseSphere, coe_genHopfBaseSphere,
    real_inner_mfderiv_genHopfBaseAmbient, real_inner_I_smul_mfderiv_genHopfBaseAmbient,
    real_inner_I_smul_mfderiv_genHopfBaseAmbient, hopfQuotientForm_apply]
  linear_combination (-(Real.sin p.1 ^ 2) * hopfAngleForm p.2 x.2 * hopfAngleForm p.2 y.2)
    * Real.sin_sq_add_cos_sq p.1

/-! ## (III) The base map is onto `ℂP^{n+1}` -/

/-- **Math.** Petersen Example 1.4.14: the base map `ψ(t, ζ) = [sin(t)·ζ : cos(t)]` is onto
`ℂP^{n+1}`.  Given a homogeneous coordinate `[a : c]` with `|a|² + |c|² = 1`, take
`t = arccos|c|` (so `cos t = |c|`, `sin t = |a|`), rotate the last coordinate to be real by the
unit `u = c/|c|` (or `u = 1` if `c = 0`) and set `ζ = |a|⁻¹·u⁻¹·a` (any unit vector if `a = 0`):
then `u · ψ(t, ζ) = (a, c)`, so the two points lie on the same complex line. -/
theorem surjective_genHopfBase : Function.Surjective (genHopfBase (n := n)) := by
  intro P
  obtain ⟨x, hx⟩ := surjective_projSphere (n := n + 1) P
  set y : WithLp 2 (𝔼₁ × ℂ) := snocLpEquiv.symm (x : 𝔼₂) with hy
  set a : 𝔼₁ := (WithLp.ofLp y).1 with ha
  set c : ℂ := (WithLp.ofLp y).2 with hc
  have hxy : snocLpEquiv (WithLp.toLp 2 (a, c)) = (x : 𝔼₂) := by
    have h : (WithLp.toLp 2 (a, c) : WithLp 2 (𝔼₁ × ℂ)) = y := rfl
    rw [h, hy, LinearIsometryEquiv.apply_symm_apply]
  have hny : ‖y‖ = 1 := by
    rw [hy, LinearIsometryEquiv.norm_map]
    exact norm_eq_of_mem_sphere x
  have hsum : ‖a‖ ^ 2 + ‖c‖ ^ 2 = 1 := by
    rw [WithLp.prod_norm_eq_of_L2, Real.sqrt_eq_one] at hny
    exact hny
  have hc0 : (0 : ℝ) ≤ ‖c‖ := norm_nonneg c
  have hc1 : ‖c‖ ≤ 1 := by nlinarith [norm_nonneg a, sq_nonneg ‖a‖, sq_nonneg (‖c‖ - 1)]
  set t : ℝ := Real.arccos ‖c‖ with ht
  have hcos : Real.cos t = ‖c‖ := Real.cos_arccos (by linarith) hc1
  have hsin : Real.sin t = ‖a‖ := by
    rw [ht, Real.sin_arccos]
    have h : 1 - ‖c‖ ^ 2 = ‖a‖ ^ 2 := by linarith
    rw [h, Real.sqrt_sq (norm_nonneg a)]
  set u : ℂ := if c = 0 then 1 else c / ((‖c‖ : ℝ) : ℂ) with hu
  have hun : ‖u‖ = 1 := by
    by_cases h : c = 0
    · simp [hu, h]
    · have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr h
      rw [hu, if_neg h, norm_div, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg c), div_self hcn]
  have hune : u ≠ 0 := by
    intro h
    rw [h, norm_zero] at hun
    exact zero_ne_one hun
  have huc : u * ((‖c‖ : ℝ) : ℂ) = c := by
    by_cases h : c = 0
    · simp [hu, h]
    · have hcn' : ((‖c‖ : ℝ) : ℂ) ≠ 0 := by
        simpa using (norm_ne_zero_iff.mpr h)
      rw [hu, if_neg h, div_mul_cancel₀ _ hcn']
  set v : 𝔼₁ := if ‖a‖ = 0 then EuclideanSpace.single 0 (1 : ℂ) else ‖a‖⁻¹ • (u⁻¹ • a) with hv
  have hvn : ‖v‖ = 1 := by
    by_cases h : ‖a‖ = 0
    · rw [hv, if_pos h, PiLp.norm_single]
      exact norm_one
    · rw [hv, if_neg h, norm_real_smul_euclidean, norm_smul, norm_inv, hun, inv_one, one_mul,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg a)), inv_mul_cancel₀ h]
  set ζ : sphere (0 : 𝔼₁) 1 := ⟨v, mem_sphere_zero_iff_norm.mpr hvn⟩ with hζ
  have hkey : ‖a‖ • v = u⁻¹ • a := by
    by_cases h : ‖a‖ = 0
    · have ha0 : a = 0 := norm_eq_zero.mp h
      rw [hv, if_pos h, h, ha0, smul_zero, real_smul_eq_ofReal_smul]
      simp
    · rw [hv, if_neg h, real_smul_eq_ofReal_smul, real_smul_eq_ofReal_smul, smul_smul, smul_smul]
      have hane : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h
      have hcast : ((‖a‖ : ℝ) : ℂ) * ((‖a‖⁻¹ : ℝ) : ℂ) * u⁻¹ = u⁻¹ := by
        push_cast
        field_simp
      rw [hcast]
  have hamb : u • genHopfBaseAmbient (t, ζ) = (x : 𝔼₂) := by
    have h1 : genHopfBaseAmbient (t, ζ)
        = snocLpEquiv (WithLp.toLp 2 (u⁻¹ • a, ((‖c‖ : ℝ) : ℂ))) := by
      rw [genHopfBaseAmbient]
      congr 1
      show (WithLp.toLp 2 (Real.sin t • v, ((Real.cos t : ℝ) : ℂ)) : WithLp 2 (𝔼₁ × ℂ)) = _
      rw [hsin, hcos, hkey]
    rw [h1, ← snocLpEquiv_complex_smul]
    have h2 : (u • (WithLp.toLp 2 (u⁻¹ • a, ((‖c‖ : ℝ) : ℂ)) : WithLp 2 (𝔼₁ × ℂ)))
        = WithLp.toLp 2 (u • (u⁻¹ • a), u * ((‖c‖ : ℝ) : ℂ)) := rfl
    rw [h2, smul_smul, mul_inv_cancel₀ hune, one_smul, huc, hxy]
  have hsph : projSphere (genHopfBaseSphere (t, ζ)) = projSphere x := by
    refine (projSphere_eq_iff _ _).mpr ⟨⟨u, mem_sphere_zero_iff_norm.mpr hun⟩, ?_⟩
    apply Subtype.ext
    exact hamb
  exact ⟨(t, ζ), by rw [genHopfBase, hsph, hx]⟩

/-! ## Example 1.4.14, assembled -/

/-- **Math.** Petersen Example 1.4.14 — the **generalized Hopf fibration**: taking `ρ = sin`,
`φ = cos` in Example 1.4.12 recovers the Hopf fibration `S^{2n+3} → ℂP^{n+1}`.  Concretely, for any
metric `gFS` on `ℂP^{n+1}` making the Hopf projection a Riemannian submersion (i.e. the
Fubini–Study metric):

1. the doubly warped product `I × S^{2n+1} × S¹`,
   `dt² + sin²(t) ds²_{2n+1} + cos²(t) dθ²`, is the round sphere `S^{2n+3}`
   (`pullbackForm_genHopfSphere`);
2. the Hopf projection `π : S^{2n+3} → ℂP^{n+1}` factors through the circle quotient map of
   Example 1.4.12 via the base map `ψ(t, ζ) = [sin(t)·ζ : cos(t)]`
   (`projSphere_genHopfSphere`) — so the quotient of Example 1.4.12 *is* `ℂP^{n+1}`;
3. `ψ` is onto `ℂP^{n+1}` (`surjective_genHopfBase`);
4. `ψ` pulls the Fubini–Study metric back to `dt² + sin²(t)(g + cos²(t) h)`
   (`pullbackForm_genHopfBase`), i.e. exactly the quotient metric of Example 1.4.12 for
   `ρ = sin`, `φ = cos`, whose fibre coefficient is `(ρφ)²/(ρ² + φ²) = sin²(t)cos²(t)`. -/
theorem generalizedHopfFibrationComplexProjective
    (gFS : RiemannianMetric 𝓘(ℝ, Fin (n + 1) → ℂ) (ComplexProjectiveSpace (n + 1)))
    (hFS : IsRiemannianSubmersion (sphereMetricUnit (n := 2 * (n + 1) + 1) 𝔼₂) gFS projSphere) :
    (∀ (p : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1)
        (u v : TangentSpace (𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1))) p),
        pullbackForm (I := 𝓘(ℝ, ℝ).prod ((𝓡 (2 * n + 1)).prod (𝓡 1)))
            (sphereMetricUnit (n := 2 * (n + 1) + 1) 𝔼₂) genHopfSphere p u v
          = doublyWarpedProductForm (sphereMetricUnit (n := 2 * n + 1) 𝔼₁)
              (sphereMetricUnit (n := 1) ℂ) Real.sin Real.cos p u v)
      ∧ (∀ q : ℝ × sphere (0 : 𝔼₁) 1 × sphere (0 : ℂ) 1,
          projSphere (genHopfSphere q) = genHopfBase (hopfSphereQuotientMap q))
      ∧ Function.Surjective (genHopfBase (n := n))
      ∧ (∀ (p : ℝ × sphere (0 : 𝔼₁) 1)
          (x y : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) p),
          pullbackForm (I := 𝓘(ℝ, ℝ).prod (𝓡 (2 * n + 1))) gFS genHopfBase p x y
            = hopfQuotientForm (fun t => Real.sin t * Real.cos t) Real.sin p x y) :=
  ⟨pullbackForm_genHopfSphere, projSphere_genHopfSphere, surjective_genHopfBase,
    pullbackForm_genHopfBase gFS hFS⟩

end GeneralizedHopf

end PetersenLib

import PetersenLib.Ch01.ComplexProjectiveSpace
import PetersenLib.Ch01.HopfSphereSubmersion

/-!
# The vertical distribution of the Hopf projection `S^{2n+1} → ℂPⁿ`

`PetersenLib.Ch01.ComplexProjectiveSpace` builds `ℂPⁿ = S^{2n+1}/S¹` as a smooth manifold and
shows that the Hopf projection `π = projSphere` is a smooth submersion carrying a unique
Riemannian metric — the Fubini–Study metric — for which it is a Riemannian submersion.
`PetersenLib.Ch01.HopfSphereSubmersion` introduces the Hopf 1-form `θ_z(u) = ⟪i·z, u⟫` on the
odd sphere.  This file identifies the **vertical distribution** of `π`, i.e. `ker Dπ`, and reads
off the resulting formula for the Fubini–Study metric.

## Main results

* `hopfVerticalVector z` — the unit vertical tangent vector at `z`, characterized by
  `sphereAmbient z (hopfVerticalVector z) = i·z` (`sphereAmbient_hopfVertical`); it satisfies
  `θ_z(hopfVerticalVector z) = 1` (`hopfAngleForm_hopfVertical`).  (The bare name `hopfVertical`
  is already taken by `PetersenLib.Ch01.HopfFibration`, where it denotes the *ambient* vector
  `i·(z, w) ∈ ℂ²` of the classical Hopf fibration; the name here follows
  `exists_hopfVerticalVector` of `PetersenLib.Ch01.HopfSphereSubmersion`.)
* `mfderiv_projSphere_hopfVertical` — the Hopf direction is vertical, so
  `Dπ (hopfVerticalVector z) = 0`.
  Proved by differentiating the constant curve `θ ↦ π(e^{iθ}·z)` at `θ = 0`.
* `ker_mfderiv_projSphere` — **exactness**: `ker Dπ_z = ℝ·(hopfVerticalVector z)`, nothing more.
  Rank–nullity: `dim T_z S^{2n+1} = 2n + 1`, `dim T_{π(z)} ℂPⁿ = 2n`, and `Dπ_z` is onto, so the
  kernel is a line; it contains the nonzero vector `hopfVerticalVector z`.
* `fubiniStudy_mfderiv_projSphere` — **the payoff**: for *any* metric `gFS` making `π` a
  Riemannian submersion (so, by `fubiniStudyMetricComplexProjectiveSpace`, for the Fubini–Study
  metric),
  `gFS(Dπ X, Dπ Y) = ⟪X, Y⟫ − θ(X) θ(Y)`,
  i.e. the Fubini–Study inner product of two pushforwards is the round inner product of the
  ambient vectors with their Hopf (vertical) components removed.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Examples 1.3.4 and 1.4.14.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Metric Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace PetersenLib

variable {n : ℕ}

local notation "𝔼" => EuclideanSpace ℂ (Fin (n + 1))

/-! ## Real scalars against the Hopf direction of `ℂ^m`

On `EuclideanSpace ℂ (Fin m)` the `ℝ`-action lives in a `Module ℝ` diamond (the `PiLp` action
versus the restriction-of-scalars one), which makes Mathlib's `real_inner_smul_left`, `lsmul`
and `restrictScalars` diverge.  The remedy used throughout `PetersenLib` is to keep every scalar
*complex*: the real multiple `s·(i·v)` is rewritten as the complex multiple `((s : ℂ)·i)·v`,
after which the `ℂ`-inner-product API applies.  These two coordinatewise lemmas are the bridge. -/

/-- **Eng.** Complex scalars act coordinatewise on `ℂ^m`. -/
theorem euclideanC_complex_smul_apply {m : ℕ} (c : ℂ) (v : EuclideanSpace ℂ (Fin m))
    (k : Fin m) : (c • v) k = c * v k := by simp

/-- **Eng.** Real scalars act coordinatewise on `ℂ^m`, through the coercion `ℝ → ℂ`. -/
theorem euclideanC_real_smul_apply {m : ℕ} (r : ℝ) (v : EuclideanSpace ℂ (Fin m)) (k : Fin m) :
    (r • v) k = (r : ℂ) * v k := by
  simp only [WithLp.ofLp_smul, Pi.smul_apply]
  exact Complex.real_smul

/-- **Eng.** The real multiple `s·(i·v)` of the Hopf direction, rewritten with the complex
scalar `(s : ℂ)·i`.  This is the form in which `real_inner_ofReal_I_smul_left/right` and
`real_inner_I_smul_ofReal_I_smul` expect it. -/
theorem real_smul_I_smul {m : ℕ} (s : ℝ) (v : EuclideanSpace ℂ (Fin m)) :
    s • (Complex.I • v) = (((s : ℝ) : ℂ) * Complex.I) • v := by
  refine PiLp.ext fun k => ?_
  rw [euclideanC_real_smul_apply, euclideanC_complex_smul_apply, euclideanC_complex_smul_apply,
    ← mul_assoc]

/-- **Eng.** Complex scalar multiplication on a *fixed* vector of `ℂ^{n+1}`, as a real-linear
continuous map `ℂ → ℂ^{n+1}`, `c ↦ c·v`.  Built by hand from `c·v = re(c)·v + im(c)·(i·v)`:
`ContinuousLinearMap.restrictScalars` would need the `IsScalarTower ℝ ℂ ℂ^{n+1}` instance,
which does not fire here (same diamond as above). -/
def smulRightCL (v : 𝔼) : ℂ →L[ℝ] 𝔼 :=
  Complex.reCLM.smulRight v + Complex.imCLM.smulRight (Complex.I • v)

/-- **Math.** The real/imaginary decomposition of complex scalar multiplication on `ℂ^m`,
checked coordinatewise. -/
theorem smul_eq_re_add_im {m : ℕ} (c : ℂ) (x : EuclideanSpace ℂ (Fin m)) :
    c • x = c.re • x + c.im • (Complex.I • x) := by
  refine PiLp.ext fun k => ?_
  rw [euclideanC_complex_smul_apply]
  show _ = (c.re • x) k + (c.im • (Complex.I • x)) k
  rw [euclideanC_real_smul_apply, euclideanC_real_smul_apply, euclideanC_complex_smul_apply]
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im] <;> ring

@[simp]
theorem smulRightCL_apply (v : 𝔼) (c : ℂ) : (smulRightCL v : ℂ →L[ℝ] 𝔼) c = c • v := by
  rw [smulRightCL]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    Complex.reCLM_apply, Complex.imCLM_apply]
  exact (smul_eq_re_add_im c v).symm

/-! ## The unit vertical vector -/

/-- **Math.** The unit **vertical** (Hopf-fibre) tangent vector at `z ∈ S^{2n+1}`: the tangent
vector whose ambient image is `i·z`.  It exists because `i·z ⊥ z` (`real_inner_I_smul_coe_sphere`)
and Mathlib's `range_mfderiv_coe_sphere` says the range of the differential of the inclusion is
exactly the orthogonal complement of the position vector; it is unique because that differential
is injective. -/
def hopfVerticalVector (z : sphere (0 : 𝔼) 1) : TangentSpace (𝓡 (2 * n + 1)) z :=
  (exists_mfderiv_coe_sphere_eq (E := 𝔼) (n := 2 * n + 1) z
    (real_inner_I_smul_coe_sphere z)).choose

/-- **Math.** The defining property of `hopfVerticalVector`: its ambient image is the Hopf field
`i·z`. -/
@[simp]
theorem sphereAmbient_hopfVertical (z : sphere (0 : 𝔼) 1) :
    sphereAmbient z (hopfVerticalVector z) = Complex.I • (z : 𝔼) :=
  (exists_mfderiv_coe_sphere_eq (E := 𝔼) (n := 2 * n + 1) z
    (real_inner_I_smul_coe_sphere z)).choose_spec

/-- **Math.** The Hopf 1-form is dual to the vertical vector: `θ_z(hopfVerticalVector z) = 1`. -/
@[simp]
theorem hopfAngleForm_hopfVertical (z : sphere (0 : 𝔼) 1) :
    hopfAngleForm z (hopfVerticalVector z) = 1 := by
  rw [hopfAngleForm_apply, sphereAmbient_hopfVertical, real_inner_I_smul_self]

/-- **Eng.** In particular the vertical vector is nonzero. -/
theorem hopfVertical_ne_zero (z : sphere (0 : 𝔼) 1) : hopfVerticalVector z ≠ 0 := by
  intro h
  have h1 : hopfAngleForm z (hopfVerticalVector z) = 0 := by rw [h, map_zero]
  rw [hopfAngleForm_hopfVertical] at h1
  exact one_ne_zero h1

/-! ## The Hopf-fibre curve `θ ↦ e^{iθ}·z` -/

/-- The ambient Hopf-fibre curve through `z ∈ S^{2n+1} ⊆ ℂ^{n+1}`: `θ ↦ e^{iθ}·z`. -/
def hopfCurveAmbient (z : sphere (0 : 𝔼) 1) (θ : ℝ) : 𝔼 :=
  Complex.exp ((θ : ℂ) * Complex.I) • (z : 𝔼)

theorem norm_exp_ofReal_mul_I (θ : ℝ) : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_hopfCurveAmbient (z : sphere (0 : 𝔼) 1) (θ : ℝ) :
    ‖hopfCurveAmbient z θ‖ = 1 := by
  rw [hopfCurveAmbient, norm_smul, norm_exp_ofReal_mul_I, norm_coe_unitSphere, one_mul]

/-- **Math.** The Hopf-fibre curve through `z`: `θ ↦ e^{iθ}·z`, a curve inside `S^{2n+1}` whose
image is the whole Hopf fibre through `z`, and whose velocity at `θ = 0` is the vertical
vector. -/
def hopfCurve (z : sphere (0 : 𝔼) 1) (θ : ℝ) : sphere (0 : 𝔼) 1 :=
  ⟨hopfCurveAmbient z θ, mem_sphere_zero_iff_norm.mpr (norm_hopfCurveAmbient z θ)⟩

@[simp]
theorem coe_hopfCurve (z : sphere (0 : 𝔼) 1) (θ : ℝ) :
    ((hopfCurve z θ : sphere (0 : 𝔼) 1) : 𝔼) = hopfCurveAmbient z θ := rfl

@[simp]
theorem hopfCurve_zero (z : sphere (0 : 𝔼) 1) : hopfCurve z 0 = z := by
  apply Subtype.ext
  show hopfCurveAmbient z 0 = (z : 𝔼)
  rw [hopfCurveAmbient]
  norm_num

/-- **Eng.** The Hopf-fibre curve is the orbit of `z` under `Circle.exp`. -/
theorem hopfCurve_eq_circle_exp_smul (z : sphere (0 : 𝔼) 1) (θ : ℝ) :
    hopfCurve z θ = (Circle.exp θ) • z := Subtype.ext rfl

/-- **Math.** The Hopf projection is constant along the Hopf-fibre curve: `e^{iθ}·z` and `z`
define the same point of `ℂPⁿ`. -/
theorem projSphere_hopfCurve (z : sphere (0 : 𝔼) 1) (θ : ℝ) :
    projSphere (hopfCurve z θ) = projSphere z := by
  rw [hopfCurve_eq_circle_exp_smul, projSphere_circle_smul]

/-- **Eng.** The real-linear map `θ ↦ iθ`, `ℝ →L[ℝ] ℂ`.  Written as a `smulRight` of the
identity rather than as a product, so that no `IsScalarTower` instance is needed. -/
def mulICL : ℝ →L[ℝ] ℂ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.I

@[simp]
theorem mulICL_apply (θ : ℝ) : (mulICL : ℝ →L[ℝ] ℂ) θ = (θ : ℂ) * Complex.I := by
  show θ • Complex.I = _
  rw [Complex.real_smul]

theorem coe_mulICL : ⇑(mulICL : ℝ →L[ℝ] ℂ) = fun θ : ℝ => ((θ : ℂ) * Complex.I) :=
  funext mulICL_apply

theorem contDiff_ofReal_mul_I : ContDiff ℝ ∞ fun θ : ℝ => ((θ : ℂ) * Complex.I) := by
  rw [← coe_mulICL]
  exact (mulICL : ℝ →L[ℝ] ℂ).contDiff

theorem hasDerivAt_ofReal_mul_I : HasDerivAt (fun θ : ℝ => ((θ : ℂ) * Complex.I)) Complex.I 0 := by
  have h := (mulICL : ℝ →L[ℝ] ℂ).hasDerivAt (x := (0 : ℝ))
  rw [coe_mulICL] at h
  simpa using h

theorem hopfCurveAmbient_eq (z : sphere (0 : 𝔼) 1) :
    hopfCurveAmbient z
      = fun θ : ℝ => (smulRightCL (z : 𝔼) : ℂ →L[ℝ] 𝔼) (Complex.exp ((θ : ℂ) * Complex.I)) := by
  funext θ
  rw [smulRightCL_apply]
  rfl

theorem contDiff_hopfCurveAmbient (z : sphere (0 : 𝔼) 1) :
    ContDiff ℝ ∞ (hopfCurveAmbient z) := by
  have hexp : ContDiff ℝ ∞ fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp contDiff_ofReal_mul_I
  rw [hopfCurveAmbient_eq]
  exact (smulRightCL (z : 𝔼)).contDiff.comp hexp

/-- **Math.** The velocity of the Hopf-fibre curve at `θ = 0` is the Hopf field `i·z`. -/
theorem hasDerivAt_hopfCurveAmbient (z : sphere (0 : 𝔼) 1) :
    HasDerivAt (hopfCurveAmbient z) (Complex.I • (z : 𝔼)) 0 := by
  have h2 : HasDerivAt (fun θ : ℝ => Complex.exp ((θ : ℂ) * Complex.I)) Complex.I 0 := by
    simpa using hasDerivAt_ofReal_mul_I.cexp
  have h3 := (smulRightCL (z : 𝔼)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  simpa [Function.comp_def, hopfCurveAmbient] using h3

theorem contMDiff_hopfCurve (z : sphere (0 : 𝔼) 1) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)) ∞ (hopfCurve z) :=
  (contDiff_hopfCurveAmbient z).contMDiff.codRestrict_sphere
    (fun θ => mem_sphere_zero_iff_norm.mpr (norm_hopfCurveAmbient z θ))

/-- **Math.** The intrinsic velocity of the Hopf-fibre curve at `θ = 0`, read through the sphere
inclusion, is `i·z`. -/
theorem sphereAmbient_mfderiv_hopfCurve (z : sphere (0 : 𝔼) 1) :
    sphereAmbient z (mfderiv 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)) (hopfCurve z) 0 (1 : ℝ))
      = Complex.I • (z : 𝔼) := by
  have hz0 : hopfCurve z 0 = z := hopfCurve_zero z
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)) (hopfCurve z) 0 :=
    ((contMDiff_hopfCurve z) 0).mdifferentiableAt (by simp)
  have hcoe : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼)
      (hopfCurve z 0) :=
    (contMDiff_coe_sphere (E := 𝔼) (n := 2 * n + 1) (m := ∞) _).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply (I' := 𝓡 (2 * n + 1)) (I'' := 𝓘(ℝ, 𝔼)) (0 : ℝ) hcoe hd (1 : ℝ)
  have hcomp : ((↑) : sphere (0 : 𝔼) 1 → 𝔼) ∘ (hopfCurve z) = hopfCurveAmbient z := rfl
  rw [hcomp, hz0] at h
  have hmf : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼) (hopfCurveAmbient z) 0
      = ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (Complex.I • (z : 𝔼)) := by
    rw [mfderiv_eq_fderiv]
    exact (hasDerivAt_hopfCurveAmbient z).hasFDerivAt.fderiv
  have hfd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, 𝔼) (hopfCurveAmbient z) 0 (1 : ℝ) = Complex.I • (z : 𝔼) := by
    rw [hmf]
    show (1 : ℝ) • (Complex.I • (z : 𝔼)) = Complex.I • (z : 𝔼)
    exact one_smul ℝ _
  exact h.symm.trans hfd

/-- **Math.** The intrinsic velocity of the Hopf-fibre curve at `θ = 0` *is* the vertical
vector (both have ambient image `i·z`, and the differential of the inclusion is injective). -/
theorem mfderiv_hopfCurve_one (z : sphere (0 : 𝔼) 1) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)) (hopfCurve z) 0 (1 : ℝ) = hopfVerticalVector z := by
  apply mfderiv_coe_sphere_injective (n := 2 * n + 1) z
  show sphereAmbient z (mfderiv 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)) (hopfCurve z) 0 (1 : ℝ))
    = sphereAmbient z (hopfVerticalVector z)
  rw [sphereAmbient_mfderiv_hopfCurve, sphereAmbient_hopfVertical]

/-! ## The vertical direction is in the kernel -/

/-- **Math.** The Hopf direction is **vertical**: the differential of the Hopf projection kills
it.  Indeed `π(e^{iθ}·z) = π(z)` for all `θ`, so the curve `θ ↦ π(hopfCurve z θ)` is constant;
its derivative at `0` is `0`, and by the chain rule that derivative is `Dπ_z` applied to the
velocity of the curve, which is `hopfVerticalVector z`. -/
theorem mfderiv_projSphere_hopfVertical (z : sphere (0 : 𝔼) 1) :
    mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z (hopfVerticalVector z) = 0 := by
  have hz0 : hopfCurve z 0 = z := hopfCurve_zero z
  have hd : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (2 * n + 1)) (hopfCurve z) 0 :=
    ((contMDiff_hopfCurve z) 0).mdifferentiableAt (by simp)
  have hp : MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) (hopfCurve z 0) := by
    rw [hz0]
    exact (contMDiff_projSphere z).mdifferentiableAt (by simp)
  have h := mfderiv_comp_apply (I' := 𝓡 (2 * n + 1)) (I'' := 𝓘(ℝ, Fin n → ℂ)) (0 : ℝ) hp hd
    (1 : ℝ)
  have hconst : (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) ∘ (hopfCurve z)
      = fun _ : ℝ => projSphere z := funext fun θ => projSphere_hopfCurve z θ
  rw [hconst] at h
  simp only [mfderiv_const, ContinuousLinearMap.zero_apply] at h
  rw [hz0] at h
  rw [← mfderiv_hopfCurve_one z]
  exact h.symm

/-! ## Exactness of the kernel -/

theorem finrank_tangentSpace_sphere (z : sphere (0 : 𝔼) 1) :
    finrank ℝ (TangentSpace (𝓡 (2 * n + 1)) z) = 2 * n + 1 :=
  finrank_euclideanSpace_fin

theorem finrank_fin_complex : finrank ℝ (Fin n → ℂ) = 2 * n := by
  simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]

instance instFiniteDimensionalTangentSphere (z : sphere (0 : 𝔼) 1) :
    FiniteDimensional ℝ (TangentSpace (𝓡 (2 * n + 1)) z) :=
  inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin (2 * n + 1))))

instance instFiniteDimensionalTangentCP (p : ComplexProjectiveSpace n) :
    FiniteDimensional ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) p) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin n → ℂ))

/-- **Math.** **Exactness of the vertical distribution.**  The kernel of `Dπ_z` is exactly the
Hopf line `ℝ·(i·z)` — nothing more.  Rank–nullity: `Dπ_z` is onto (`surjective_mfderiv_projSphere`),
`dim_ℝ T_z S^{2n+1} = 2n + 1` and `dim_ℝ T_{π(z)} ℂPⁿ = dim_ℝ ℂⁿ = 2n`, so the kernel is a line;
it contains the nonzero vector `hopfVerticalVector z`, hence equals its span. -/
theorem ker_mfderiv_projSphere (z : sphere (0 : 𝔼) 1) :
    LinearMap.ker (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
        (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z
        : TangentSpace (𝓡 (2 * n + 1)) z →L[ℝ] _).toLinearMap
      = Submodule.span ℝ {hopfVerticalVector z} := by
  set f := (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z
      : TangentSpace (𝓡 (2 * n + 1)) z →L[ℝ] _).toLinearMap with hf
  have hsurj : Function.Surjective f := surjective_mfderiv_projSphere z
  have hrange : LinearMap.range f = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange, finrank_top, finrank_tangentSpace_sphere z] at hrk
  have hcod : finrank ℝ (TangentSpace 𝓘(ℝ, Fin n → ℂ) (projSphere z)) = 2 * n :=
    finrank_fin_complex
  rw [hcod] at hrk
  have hker1 : finrank ℝ (LinearMap.ker f) = 1 := by omega
  have hmem : hopfVerticalVector z ∈ LinearMap.ker f :=
    LinearMap.mem_ker.mpr (mfderiv_projSphere_hopfVertical z)
  have hle : Submodule.span ℝ {hopfVerticalVector z} ≤ LinearMap.ker f := by
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hmem
  have hspan : finrank ℝ (Submodule.span ℝ {hopfVerticalVector z}) = 1 :=
    finrank_span_singleton (hopfVertical_ne_zero z)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hspan, hker1])).symm

/-- **Math.** Membership in the kernel of `Dπ_z` means being a real multiple of the vertical
vector. -/
theorem exists_smul_hopfVertical_of_mfderiv_eq_zero {z : sphere (0 : 𝔼) 1}
    {w : TangentSpace (𝓡 (2 * n + 1)) z}
    (hw : mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z w = 0) :
    ∃ t : ℝ, w = t • hopfVerticalVector z := by
  have hmem : w ∈ Submodule.span ℝ {hopfVerticalVector z} := by
    rw [← ker_mfderiv_projSphere z]
    exact LinearMap.mem_ker.mpr hw
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hmem
  exact ⟨t, ht.symm⟩

/-! ## The horizontal part of a tangent vector -/

/-- **Math.** The **horizontal part** of a tangent vector: `X^h = X − θ(X)·(hopfVerticalVector z)`,
the component of `X` orthogonal to the Hopf fibre. -/
def hopfHorizontalPart (z : sphere (0 : 𝔼) 1) (X : TangentSpace (𝓡 (2 * n + 1)) z) :
    TangentSpace (𝓡 (2 * n + 1)) z :=
  X - hopfAngleForm z X • hopfVerticalVector z

/-- **Math.** The ambient image of the horizontal part: `Dι(X^h) = Dι(X) − θ(X)·(i·z)` (with the
real scalar written complex, per the diamond convention). -/
theorem sphereAmbient_hopfHorizontalPart (z : sphere (0 : 𝔼) 1)
    (X : TangentSpace (𝓡 (2 * n + 1)) z) :
    sphereAmbient z (hopfHorizontalPart z X)
      = sphereAmbient z X - (((hopfAngleForm z X : ℝ) : ℂ) * Complex.I) • (z : 𝔼) := by
  show mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z
      (X - hopfAngleForm z X • hopfVerticalVector z) = _
  rw [map_sub, ContinuousLinearMap.map_smul]
  show sphereAmbient z X - hopfAngleForm z X • sphereAmbient z (hopfVerticalVector z) = _
  rw [sphereAmbient_hopfVertical, real_smul_I_smul]

/-- **Math.** The horizontal part is annihilated by the Hopf 1-form: it is horizontal. -/
@[simp]
theorem hopfAngleForm_hopfHorizontalPart (z : sphere (0 : 𝔼) 1)
    (X : TangentSpace (𝓡 (2 * n + 1)) z) :
    hopfAngleForm z (hopfHorizontalPart z X) = 0 := by
  show hopfAngleForm z (X - hopfAngleForm z X • hopfVerticalVector z) = 0
  rw [map_sub, ContinuousLinearMap.map_smul, hopfAngleForm_hopfVertical, smul_eq_mul, mul_one,
    sub_self]

/-- **Math.** The projection does not see the difference: `Dπ(X^h) = Dπ(X)`, because the
subtracted piece is vertical. -/
@[simp]
theorem mfderiv_projSphere_hopfHorizontalPart (z : sphere (0 : 𝔼) 1)
    (X : TangentSpace (𝓡 (2 * n + 1)) z) :
    mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
        (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z (hopfHorizontalPart z X)
      = mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
        (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z X := by
  show mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z
      (X - hopfAngleForm z X • hopfVerticalVector z) = _
  rw [map_sub, ContinuousLinearMap.map_smul, mfderiv_projSphere_hopfVertical, smul_zero, sub_zero]

/-- **Math.** The horizontal part is `ds²_{2n+1}`-orthogonal to the whole vertical line, i.e.
to `ker Dπ_z`.  This is the hypothesis needed to feed `IsRiemannianSubmersion`. -/
theorem metricInner_hopfHorizontalPart_of_mem_ker (z : sphere (0 : 𝔼) 1)
    (X : TangentSpace (𝓡 (2 * n + 1)) z) (w : TangentSpace (𝓡 (2 * n + 1)) z)
    (hw : mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
      (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z w = 0) :
    (sphereMetricUnit (n := 2 * n + 1) 𝔼).metricInner z (hopfHorizontalPart z X) w = 0 := by
  obtain ⟨t, rfl⟩ := exists_smul_hopfVertical_of_mfderiv_eq_zero hw
  have hamb : sphereAmbient z (t • hopfVerticalVector z) = (((t : ℝ) : ℂ) * Complex.I) • (z : 𝔼) := by
    show mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) z
        (t • hopfVerticalVector z) = _
    rw [ContinuousLinearMap.map_smul]
    show t • sphereAmbient z (hopfVerticalVector z) = _
    rw [sphereAmbient_hopfVertical, real_smul_I_smul]
  rw [sphereMetricUnit_apply]
  show (inner ℝ (sphereAmbient z (hopfHorizontalPart z X))
    (sphereAmbient z (t • hopfVerticalVector z)) : ℝ) = 0
  rw [hamb, real_inner_ofReal_I_smul_right]
  show t * hopfAngleForm z (hopfHorizontalPart z X) = 0
  rw [hopfAngleForm_hopfHorizontalPart, mul_zero]

/-! ## The Fubini–Study metric of two pushforwards -/

/-- **Eng.** The ambient inner product of two horizontal parts: `⟪A − a·(i·z), B − b·(i·z)⟫
= ⟪A, B⟫ − a·b`, when `a = ⟪i·z, A⟫` and `b = ⟪i·z, B⟫`. -/
theorem real_inner_sub_ofReal_I_smul (z : sphere (0 : 𝔼) 1) (A B : 𝔼) (a b : ℝ)
    (ha : (inner ℝ (Complex.I • (z : 𝔼)) A : ℝ) = a)
    (hb : (inner ℝ (Complex.I • (z : 𝔼)) B : ℝ) = b) :
    (inner ℝ (A - (((a : ℝ) : ℂ) * Complex.I) • (z : 𝔼))
        (B - (((b : ℝ) : ℂ) * Complex.I) • (z : 𝔼)) : ℝ)
      = (inner ℝ A B : ℝ) - a * b := by
  have hz1 : ∀ s : ℝ, (inner ℝ (Complex.I • (z : 𝔼))
      ((((s : ℝ) : ℂ) * Complex.I) • (z : 𝔼)) : ℝ) = s := fun s =>
    real_inner_I_smul_ofReal_I_smul s (norm_coe_unitSphere z)
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_ofReal_I_smul_right, real_inner_ofReal_I_smul_left,
    real_inner_ofReal_I_smul_left, hz1, ha, hb]
  ring

/-- **Math.** **The payoff.**  For any Riemannian metric `gFS` on `ℂPⁿ` making the Hopf
projection a Riemannian submersion — by `fubiniStudyMetricComplexProjectiveSpace` there is
exactly one, the **Fubini–Study metric** — the inner product of two pushforwards is the round
inner product of the ambient vectors minus their Hopf components:

  `gFS(Dπ X, Dπ Y) = ⟪Dι X, Dι Y⟫ − θ(X)·θ(Y)`.

Proof: split `X = X^h + θ(X)·(hopfVerticalVector z)`.  The vertical summand is killed by `Dπ`
(`mfderiv_projSphere_hopfVertical`), so `Dπ X = Dπ X^h`; and `X^h` is orthogonal to
`ker Dπ = ℝ·(hopfVerticalVector z)` (`ker_mfderiv_projSphere`), so the submersion identity applies to
`X^h, Y^h` and computes `gFS(Dπ X, Dπ Y) = ⟪Dι X^h, Dι Y^h⟫`, which expands to the stated
formula. -/
theorem fubiniStudy_mfderiv_projSphere
    (gFS : RiemannianMetric 𝓘(ℝ, Fin n → ℂ) (ComplexProjectiveSpace n))
    (hFS : IsRiemannianSubmersion (sphereMetricUnit (n := 2 * n + 1) 𝔼) gFS projSphere)
    (z : sphere (0 : 𝔼) 1) (X Y : TangentSpace (𝓡 (2 * n + 1)) z) :
    gFS.metricInner (projSphere z)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
          (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z X)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ)
          (projSphere : sphere (0 : 𝔼) 1 → ComplexProjectiveSpace n) z Y)
      = (inner ℝ (sphereAmbient z X) (sphereAmbient z Y) : ℝ)
        - hopfAngleForm z X * hopfAngleForm z Y := by
  have hsub := hFS.2.2 z (hopfHorizontalPart z X) (hopfHorizontalPart z Y)
    (metricInner_hopfHorizontalPart_of_mem_ker z X)
    (metricInner_hopfHorizontalPart_of_mem_ker z Y)
  rw [mfderiv_projSphere_hopfHorizontalPart, mfderiv_projSphere_hopfHorizontalPart] at hsub
  rw [← hsub, sphereMetricUnit_apply]
  show (inner ℝ (sphereAmbient z (hopfHorizontalPart z X))
    (sphereAmbient z (hopfHorizontalPart z Y)) : ℝ) = _
  rw [sphereAmbient_hopfHorizontalPart, sphereAmbient_hopfHorizontalPart]
  exact real_inner_sub_ofReal_I_smul z (sphereAmbient z X) (sphereAmbient z Y)
    (hopfAngleForm z X) (hopfAngleForm z Y) (hopfAngleForm_apply z X).symm
    (hopfAngleForm_apply z Y).symm

end PetersenLib

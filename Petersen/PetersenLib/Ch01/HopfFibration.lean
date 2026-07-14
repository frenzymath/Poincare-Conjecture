import PetersenLib.Ch01.Sphere
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Petersen Ch. 1, Example 1.1.5 — the Hopf fibration

The **Hopf fibration** `S³(1) → S²(1/2)`, in F. Wilhelm's coordinates: viewing
`S³(1) ⊆ ℂ²` and `S²(1/2) ⊆ ℝ ⊕ ℂ`, the map is

  `H(z, w) = (½(|w|² − |z|²), z w̄)`,

and it is a Riemannian submersion for the canonical (round) metrics on the two
spheres.

## Implementation

* The ambient spaces are the real inner product spaces `WithLp 2 (ℂ × ℂ)`
  (real dimension `4`, carrying `S³(1)`) and `WithLp 2 (ℝ × ℂ)` (real
  dimension `3`, carrying `S²(1/2)`), with the `L²` product inner products.
* `hopfMapAmbient` is Wilhelm's formula on all of `ℂ²`; it multiplies norms
  quadratically (`norm_hopfMapAmbient`), so it maps the unit sphere to the
  sphere of radius `1/2`, and `hopfMap` is the restriction.
* The total differential of the ambient map is the explicit continuous linear
  map `hopfDeriv z w : (u, v) ↦ (⟪w, v⟫ − ⟪z, u⟫, u w̄ + z v̄)`
  (`hasFDerivAt_hopfMapAmbient`).
* The fibre direction `i(z, w)` is `hopfVertical`, the horizontal plane
  `λ(−w̄, z̄)`, `λ ∈ ℂ`, is `hopfHorizontal`; the differential kills the
  vertical vector (`hopfDeriv_hopfVertical`) and preserves inner products of
  horizontal vectors (`real_inner_hopfDeriv_hopfHorizontal`), which is the
  computational heart of Petersen's Example 1.1.5.
* `hopfMap_isRiemannianSubmersion` assembles these into the statement that
  `hopfMap : (S³(1), g) → (S²(1/2), g)` is a Riemannian submersion, where the
  domain carries `sphereMetricUnit` (the canonical metric of the unit sphere,
  over Mathlib's stereographic charted-space structure) and the target carries
  `sphereMetric _ (1/2)` (the canonical metric of the radius-`1/2` sphere).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Example 1.1.5.
-/

open Metric Module Function ComplexConjugate
open scoped ContDiff Manifold Topology InnerProductSpace

noncomputable section

namespace PetersenLib

/-! ## The ambient spaces `ℂ²` and `ℝ ⊕ ℂ` -/

/-- **Eng.** The domain of the Hopf fibration lives in
`ℂ² = WithLp 2 (ℂ × ℂ)`, of real dimension `4 = 3 + 1`; this `Fact` feeds the
sphere `S³ ⊆ ℂ²` its charted-space structure over `EuclideanSpace ℝ (Fin 3)`. -/
instance fact_finrank_complex_prod : Fact (finrank ℝ (WithLp 2 (ℂ × ℂ)) = 3 + 1) :=
  ⟨by rw [(WithLp.linearEquiv 2 ℝ (ℂ × ℂ)).finrank_eq, Module.finrank_prod,
    Complex.finrank_real_complex]⟩

/-- **Eng.** The target of the Hopf fibration lives in
`ℝ ⊕ ℂ = WithLp 2 (ℝ × ℂ)`, of real dimension `3 = 2 + 1`; this `Fact` feeds
the sphere `S² ⊆ ℝ ⊕ ℂ` its charted-space structure over
`EuclideanSpace ℝ (Fin 2)`. -/
instance fact_finrank_real_complex_prod : Fact (finrank ℝ (WithLp 2 (ℝ × ℂ)) = 2 + 1) :=
  ⟨by rw [(WithLp.linearEquiv 2 ℝ (ℝ × ℂ)).finrank_eq, Module.finrank_prod,
    Complex.finrank_real_complex, Module.finrank_self]⟩

/-- **Eng.** The target sphere of the Hopf fibration has radius `1/2 > 0`;
recorded as a `Fact` so that the charted-space structure of
`PetersenLib.sphereChartedSpace` is found by instance resolution. -/
instance fact_zero_lt_half : Fact ((0 : ℝ) < 1 / 2) := ⟨by norm_num⟩

/-! ## The ambient Hopf map -/

/-- **Math.** Petersen Example 1.1.5 (F. Wilhelm's formula), extended to all
of `ℂ²`: the quadratic polynomial map

  `Ĥ(z, w) = (½(|w|² − |z|²), z w̄) : ℂ² → ℝ ⊕ ℂ`.

Its restriction to the unit sphere is the Hopf fibration `hopfMap`. -/
def hopfMapAmbient (x : WithLp 2 (ℂ × ℂ)) : WithLp 2 (ℝ × ℂ) :=
  WithLp.toLp 2 ((‖x.snd‖ ^ 2 - ‖x.fst‖ ^ 2) / 2, x.fst * conj x.snd)

@[simp]
theorem hopfMapAmbient_fst (x : WithLp 2 (ℂ × ℂ)) :
    (hopfMapAmbient x).fst = (‖x.snd‖ ^ 2 - ‖x.fst‖ ^ 2) / 2 :=
  rfl

@[simp]
theorem hopfMapAmbient_snd (x : WithLp 2 (ℂ × ℂ)) :
    (hopfMapAmbient x).snd = x.fst * conj x.snd :=
  rfl

/-- **Math.** The ambient Hopf map squares norms (up to the factor `1/2`):
`|Ĥ(z, w)| = ½(|z|² + |w|²)²`, because
`|Ĥ(z,w)|² = ¼(|w|² − |z|²)² + |z|²|w|² = ¼(|z|² + |w|²)²`. -/
theorem norm_hopfMapAmbient (x : WithLp 2 (ℂ × ℂ)) :
    ‖hopfMapAmbient x‖ = ‖x‖ ^ 2 / 2 := by
  have h1 : ‖hopfMapAmbient x‖ ^ 2 = (‖x‖ ^ 2 / 2) ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2 x,
      hopfMapAmbient_fst, hopfMapAmbient_snd, norm_mul, RCLike.norm_conj]
    rw [Real.norm_eq_abs, sq_abs, mul_pow]
    ring
  have h2 : (0 : ℝ) ≤ ‖hopfMapAmbient x‖ := norm_nonneg _
  have h3 : (0 : ℝ) ≤ ‖x‖ ^ 2 / 2 := by positivity
  exact (sq_eq_sq₀ h2 h3).mp h1

/-- **Math.** The ambient Hopf map is a quadratic polynomial map, hence
`C^∞`. -/
theorem contDiff_hopfMapAmbient : ContDiff ℝ ∞ hopfMapAmbient := by
  have hfst : ContDiff ℝ ∞ (fun x : WithLp 2 (ℂ × ℂ) => x.fst) :=
    (WithLp.fstL 2 ℝ ℂ ℂ).contDiff
  have hsnd : ContDiff ℝ ∞ (fun x : WithLp 2 (ℂ × ℂ) => x.snd) :=
    (WithLp.sndL 2 ℝ ℂ ℂ).contDiff
  have h₁ : ContDiff ℝ ∞
      (fun x : WithLp 2 (ℂ × ℂ) => (‖x.snd‖ ^ 2 - ‖x.fst‖ ^ 2) / 2) :=
    ((hsnd.norm_sq ℝ).sub (hfst.norm_sq ℝ)).div_const 2
  have h₂ : ContDiff ℝ ∞
      (fun x : WithLp 2 (ℂ × ℂ) => x.fst * conj x.snd) :=
    hfst.mul (Complex.conjCLE.contDiff.comp hsnd)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm.contDiff.comp (h₁.prodMk h₂)

/-! ## The differential of the ambient Hopf map -/

/-- **Math.** The total differential of the ambient Hopf map at `(z, w)`:

  `DĤ|_{(z,w)}(u, v) = (⟪w, v⟫ − ⟪z, u⟫, u w̄ + z v̄)`,

obtained by expanding `Ĥ((z, w) + t(u, v))` to first order in `t` (product
rule for the real-bilinear map `(z, w) ↦ z w̄` and polarization for the
squared norms). -/
def hopfDeriv (z w : ℂ) : WithLp 2 (ℂ × ℂ) →L[ℝ] WithLp 2 (ℝ × ℂ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm :
      ℝ × ℂ →L[ℝ] WithLp 2 (ℝ × ℂ)).comp <|
    ContinuousLinearMap.prod
      ((innerSL ℝ w).comp (WithLp.sndL 2 ℝ ℂ ℂ) -
        (innerSL ℝ z).comp (WithLp.fstL 2 ℝ ℂ ℂ))
      (((ContinuousLinearMap.mul ℝ ℂ).flip (conj w)).comp (WithLp.fstL 2 ℝ ℂ ℂ) +
        (ContinuousLinearMap.mul ℝ ℂ z).comp
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (WithLp.sndL 2 ℝ ℂ ℂ)))

@[simp]
theorem hopfDeriv_fst (z w : ℂ) (v : WithLp 2 (ℂ × ℂ)) :
    (hopfDeriv z w v).fst = ⟪w, v.snd⟫_ℝ - ⟪z, v.fst⟫_ℝ :=
  rfl

@[simp]
theorem hopfDeriv_snd (z w : ℂ) (v : WithLp 2 (ℂ × ℂ)) :
    (hopfDeriv z w v).snd = v.fst * conj w + z * conj v.snd :=
  rfl

/-- **Math.** `hopfDeriv z w` is the derivative of the ambient Hopf map at
`(z, w)`. -/
theorem hasFDerivAt_hopfMapAmbient (x : WithLp 2 (ℂ × ℂ)) :
    HasFDerivAt hopfMapAmbient (hopfDeriv x.fst x.snd) x := by
  have hfst : HasFDerivAt (fun y : WithLp 2 (ℂ × ℂ) => y.fst)
      (WithLp.fstL 2 ℝ ℂ ℂ) x := (WithLp.fstL 2 ℝ ℂ ℂ).hasFDerivAt
  have hsnd : HasFDerivAt (fun y : WithLp 2 (ℂ × ℂ) => y.snd)
      (WithLp.sndL 2 ℝ ℂ ℂ) x := (WithLp.sndL 2 ℝ ℂ ℂ).hasFDerivAt
  -- first component: ½(‖w‖² − ‖z‖²)
  have h₁ : HasFDerivAt
      (fun y : WithLp 2 (ℂ × ℂ) => (‖y.snd‖ ^ 2 - ‖y.fst‖ ^ 2) / 2)
      ((innerSL ℝ x.snd).comp (WithLp.sndL 2 ℝ ℂ ℂ) -
        (innerSL ℝ x.fst).comp (WithLp.fstL 2 ℝ ℂ ℂ)) x := by
    have h := (hsnd.norm_sq.sub hfst.norm_sq).const_smul (2⁻¹ : ℝ)
    have harg : (fun y : WithLp 2 (ℂ × ℂ) => (‖y.snd‖ ^ 2 - ‖y.fst‖ ^ 2) / 2)
        = (2⁻¹ : ℝ) • fun y : WithLp 2 (ℂ × ℂ) => ‖y.snd‖ ^ 2 - ‖y.fst‖ ^ 2 := by
      funext y
      simp [div_eq_inv_mul]
    rw [harg]
    refine h.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.comp_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  -- second component: z w̄
  have h₂ : HasFDerivAt (fun y : WithLp 2 (ℂ × ℂ) => y.fst * conj y.snd)
      (((ContinuousLinearMap.mul ℝ ℂ).flip (conj x.snd)).comp (WithLp.fstL 2 ℝ ℂ ℂ) +
        (ContinuousLinearMap.mul ℝ ℂ x.fst).comp
          ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (WithLp.sndL 2 ℝ ℂ ℂ))) x := by
    have hconj : HasFDerivAt (fun y : WithLp 2 (ℂ × ℂ) => conj y.snd)
        ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (WithLp.sndL 2 ℝ ℂ ℂ)) x :=
      (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x hsnd
    refine (hfst.mul hconj).congr_fderiv ?_
    ext v
    show x.fst • (starRingEnd ℂ) v.snd + (starRingEnd ℂ) x.snd • v.fst
        = v.fst * (starRingEnd ℂ) x.snd + x.fst * (starRingEnd ℂ) v.snd
    simp only [smul_eq_mul]
    ring
  have h := ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ ℂ).symm.hasFDerivAt
    (x := ((‖x.snd‖ ^ 2 - ‖x.fst‖ ^ 2) / 2, x.fst * conj x.snd))).comp x (h₁.prodMk h₂)
  exact h

/-! ## Vertical and horizontal vectors

At `p = (z, w) ∈ S³`, the fibre of the Hopf fibration through `p` is the
circle `θ ↦ (e^{iθ}z, e^{iθ}w)`, so `i(z, w)` spans the vertical direction;
the plane `{λ(−w̄, z̄) : λ ∈ ℂ}` is its orthogonal complement inside the
tangent space `T_pS³ = (z, w)^⊥`. -/

/-- **Math.** The **vertical vector** `i(z, w)` at `(z, w)`: the velocity of
the Hopf circle `θ ↦ (e^{iθ}z, e^{iθ}w)` through the point. -/
def hopfVertical (z w : ℂ) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (Complex.I * z, Complex.I * w)

@[simp]
theorem hopfVertical_fst (z w : ℂ) : (hopfVertical z w).fst = Complex.I * z :=
  rfl

@[simp]
theorem hopfVertical_snd (z w : ℂ) : (hopfVertical z w).snd = Complex.I * w :=
  rfl

/-- **Math.** The **horizontal vector** `λ(−w̄, z̄)` at `(z, w)`: as `λ`
ranges over `ℂ` these fill the orthogonal complement of the Hopf fibre
direction inside `T_{(z,w)}S³`. -/
def hopfHorizontal (z w l : ℂ) : WithLp 2 (ℂ × ℂ) :=
  WithLp.toLp 2 (-(l * conj w), l * conj z)

@[simp]
theorem hopfHorizontal_fst (z w l : ℂ) :
    (hopfHorizontal z w l).fst = -(l * conj w) :=
  rfl

@[simp]
theorem hopfHorizontal_snd (z w l : ℂ) :
    (hopfHorizontal z w l).snd = l * conj z :=
  rfl

/-- **Math.** Expansion of the real inner product against a point `(z, w)`
of `ℂ²`: `⟪(z, w), v⟫_ℝ = Re(v₁ z̄ + v₂ w̄)`. -/
theorem real_inner_toLp_left (z w : ℂ) (v : WithLp 2 (ℂ × ℂ)) :
    ⟪WithLp.toLp 2 (z, w), v⟫_ℝ = (v.fst * conj z + v.snd * conj w).re := by
  simp only [WithLp.prod_inner_apply, Complex.inner, Complex.add_re,
    WithLp.fst, WithLp.snd]

private theorem real_inner_real (a b : ℝ) : ⟪a, b⟫_ℝ = b * a := rfl

/-- **Math.** The vertical vector is tangent to the sphere:
`⟪(z, w), i(z, w)⟫_ℝ = Re(i|z|²) + Re(i|w|²) = 0`. -/
theorem real_inner_toLp_hopfVertical (z w : ℂ) :
    ⟪WithLp.toLp 2 (z, w), hopfVertical z w⟫_ℝ = 0 := by
  rw [real_inner_toLp_left, hopfVertical_fst, hopfVertical_snd]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re,
    Complex.conj_im, Complex.I_re, Complex.I_im]
  ring

/-- **Math.** Horizontal vectors are tangent to the sphere:
`⟪(z, w), λ(−w̄, z̄)⟫_ℝ = Re(−λw̄z̄) + Re(λz̄w̄) = 0`. -/
theorem real_inner_toLp_hopfHorizontal (z w l : ℂ) :
    ⟪WithLp.toLp 2 (z, w), hopfHorizontal z w l⟫_ℝ = 0 := by
  rw [real_inner_toLp_left, hopfHorizontal_fst, hopfHorizontal_snd]
  simp only [Complex.add_re, Complex.neg_re, Complex.neg_im, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Math.** Inner products of horizontal vectors:
`⟪λ(−w̄, z̄), μ(−w̄, z̄)⟫_ℝ = Re(μλ̄)(|z|² + |w|²)`; on the unit sphere the
horizontal parametrization `λ ↦ λ(−w̄, z̄)` is a linear isometry of `ℂ`
onto the horizontal plane. -/
theorem real_inner_hopfHorizontal (z w l m : ℂ) :
    ⟪hopfHorizontal z w l, hopfHorizontal z w m⟫_ℝ
      = (m * conj l).re * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  simp only [hopfHorizontal, WithLp.prod_inner_apply, Complex.inner,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [map_neg, map_mul, Complex.neg_re, Complex.mul_re,
    Complex.mul_im, Complex.neg_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Math.** Petersen Example 1.1.5: the differential of the Hopf map kills
the vertical direction — `DĤ(iz, iw) = (Re(i|w|²) − Re(i|z|²), izw̄ + z(−iw̄)) = 0`.
The fibre `θ ↦ (e^{iθ}z, e^{iθ}w)` is mapped to the single point `H(z, w)`. -/
theorem hopfDeriv_hopfVertical (z w : ℂ) :
    hopfDeriv z w (hopfVertical z w) = 0 := by
  apply WithLp.ofLp_injective
  refine Prod.ext ?_ ?_
  · show ⟪w, (hopfVertical z w).snd⟫_ℝ - ⟪z, (hopfVertical z w).fst⟫_ℝ = 0
    rw [hopfVertical_fst, hopfVertical_snd]
    simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re,
      Complex.conj_im, Complex.I_re, Complex.I_im]
    ring
  · show (hopfVertical z w).fst * conj w + z * conj ((hopfVertical z w).snd) = 0
    rw [hopfVertical_fst, hopfVertical_snd]
    simp only [map_mul, Complex.conj_I]
    ring

/-- **Math.** Petersen Example 1.1.5, the key computation: the differential
of the Hopf map preserves inner products of horizontal vectors. With
`DĤ(λ(−w̄, z̄)) = (2Re(λ̄zw), −λw̄² + λ̄z²)`, one expands

  `⟪DĤ(λ(−w̄, z̄)), DĤ(μ(−w̄, z̄))⟫ = Re(μλ̄)(|z|² + |w|²)²`,

which on the unit sphere equals `⟪λ(−w̄, z̄), μ(−w̄, z̄)⟫ = Re(μλ̄)`. -/
theorem real_inner_hopfDeriv_hopfHorizontal (z w l m : ℂ) :
    ⟪hopfDeriv z w (hopfHorizontal z w l), hopfDeriv z w (hopfHorizontal z w m)⟫_ℝ
      = (m * conj l).re * (‖z‖ ^ 2 + ‖w‖ ^ 2) ^ 2 := by
  have hfst : ∀ a : ℂ, (WithLp.ofLp (hopfDeriv z w (hopfHorizontal z w a))).1
      = ⟪w, (hopfHorizontal z w a).snd⟫_ℝ - ⟪z, (hopfHorizontal z w a).fst⟫_ℝ := fun _ => rfl
  have hsnd : ∀ a : ℂ, (WithLp.ofLp (hopfDeriv z w (hopfHorizontal z w a))).2
      = (hopfHorizontal z w a).fst * conj w + z * conj ((hopfHorizontal z w a).snd) :=
    fun _ => rfl
  rw [WithLp.prod_inner_apply, hfst, hfst, hsnd, hsnd, real_inner_real]
  simp only [hopfHorizontal_fst, hopfHorizontal_snd, Complex.inner,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [map_add, map_mul, map_neg, Complex.add_re, Complex.add_im, Complex.neg_re,
    Complex.neg_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Math.** Petersen Example 1.1.5: inside the tangent space
`T_{(z,w)}S³ = (z, w)^⊥`, the orthogonal complement of the vertical (fibre)
direction `i(z, w)` is exactly the horizontal plane `{λ(−w̄, z̄) : λ ∈ ℂ}`:
a vector `v ⊥ (z, w)` with `v ⊥ i(z, w)` satisfies `v₁z̄ + v₂w̄ = 0`, and
with `|z|² + |w|² = 1` one solves `v = λ(−w̄, z̄)` for `λ = v₂z − v₁w`. -/
theorem exists_hopfHorizontal_eq (z w : ℂ) (h1 : ‖z‖ ^ 2 + ‖w‖ ^ 2 = 1)
    (v : WithLp 2 (ℂ × ℂ)) (hp : ⟪WithLp.toLp 2 (z, w), v⟫_ℝ = 0)
    (hv : ⟪hopfVertical z w, v⟫_ℝ = 0) :
    ∃ l : ℂ, v = hopfHorizontal z w l := by
  set a : ℂ := v.fst with ha
  set b : ℂ := v.snd with hb
  -- the two real orthogonality conditions combine into one complex equation
  have hre : (a * conj z + b * conj w).re = 0 := by
    rw [real_inner_toLp_left] at hp
    exact hp
  have him : (a * conj z + b * conj w).im = 0 := by
    have hv' : (a * conj (Complex.I * z) + b * conj (Complex.I * w)).re = 0 := by
      rw [show hopfVertical z w = WithLp.toLp 2 (Complex.I * z, Complex.I * w) from rfl,
        real_inner_toLp_left] at hv
      exact hv
    rw [show (a * conj z + b * conj w).im
        = (a * conj (Complex.I * z) + b * conj (Complex.I * w)).re by
      simp only [map_mul, Complex.conj_I, Complex.add_re, Complex.add_im, Complex.mul_re,
        Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.conj_re, Complex.conj_im,
        Complex.I_re, Complex.I_im]
      ring]
    exact hv'
  have hab : a * conj z + b * conj w = 0 := Complex.ext hre him
  -- the sphere equation, complexified
  have hzw : z * conj z + w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_add]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, h1, Complex.ofReal_one]
  refine ⟨b * z - a * w, ?_⟩
  have hva : v = WithLp.toLp 2 (a, b) := rfl
  rw [hva, hopfHorizontal]
  refine congrArg (WithLp.toLp 2) (Prod.ext ?_ ?_)
  · show a = -((b * z - a * w) * conj w)
    linear_combination z * hab - a * hzw
  · show b = (b * z - a * w) * conj z
    linear_combination w * hab - b * hzw

/-! ## The Hopf fibration `S³(1) → S²(1/2)` -/

/-- **Math.** The ambient Hopf map takes the unit sphere `S³(1) ⊆ ℂ²` into
the sphere `S²(1/2) ⊆ ℝ ⊕ ℂ` of radius `1/2`:
`|Ĥ(z, w)| = ½(|z|² + |w|²)² = ½` when `|(z, w)| = 1`. -/
theorem hopfMapAmbient_mem_sphere (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) :
    hopfMapAmbient ↑x ∈ sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) := by
  rw [mem_sphere_zero_iff_norm, norm_hopfMapAmbient,
    mem_sphere_zero_iff_norm.mp x.2]
  norm_num

/-- **Math.** Petersen Example 1.1.5: the **Hopf fibration**
`H : S³(1) → S²(1/2)`, in F. Wilhelm's coordinates

  `H(z, w) = (½(|w|² − |z|²), z w̄)`,

viewing `S³(1) ⊆ ℂ²` and `S²(1/2) ⊆ ℝ ⊕ ℂ`. It is a Riemannian submersion
(`hopfMap_isRiemannianSubmersion`); its fibres are the circles
`θ ↦ (e^{iθ}z, e^{iθ}w)`, the orbits of the Hopf `S¹`-action. -/
def hopfMap (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) :
    sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) :=
  ⟨hopfMapAmbient ↑x, hopfMapAmbient_mem_sphere x⟩

@[simp]
theorem coe_hopfMap (x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) :
    (hopfMap x : WithLp 2 (ℝ × ℂ)) = hopfMapAmbient ↑x :=
  rfl

/-- **Math.** The Hopf fibration is smooth: the ambient map is a quadratic
polynomial, and (after scaling `S²(1/2)` to the unit sphere, which is how the
radius-`1/2` sphere carries its charts) restriction to spheres preserves
smoothness. -/
theorem contMDiff_hopfMap : ContMDiff (𝓡 3) (𝓡 2) ∞ hopfMap := by
  haveI : NormSMulClass ℝ (WithLp 2 (ℝ × ℂ)) := NormedSpace.toNormSMulClass
  have hmem : ∀ x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1,
      (2 : ℝ) • hopfMapAmbient ↑x ∈ sphere (0 : WithLp 2 (ℝ × ℂ)) 1 := by
    intro x
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_hopfMapAmbient,
      mem_sphere_zero_iff_norm.mp x.2]
    norm_num
  have key : hopfMap = ⇑(sphereHomeomorphUnitSphere (E := WithLp 2 (ℝ × ℂ)) (1 / 2)).symm
      ∘ Set.codRestrict (fun x : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 =>
          (2 : ℝ) • hopfMapAmbient ↑x) (sphere (0 : WithLp 2 (ℝ × ℂ)) 1) hmem := by
    funext x
    refine Subtype.ext ?_
    show hopfMapAmbient ↑x = (1 / 2 : ℝ) • ((2 : ℝ) • hopfMapAmbient ↑x)
    module
  rw [key]
  refine (contMDiff_sphereHomeomorphUnitSphere_symm (1 / 2)).comp ?_
  exact ContMDiff.codRestrict_sphere
    (((contDiff_const_smul (2 : ℝ)).contMDiff).comp
      (contDiff_hopfMapAmbient.contMDiff.comp contMDiff_coe_sphere)) hmem

/-! ## The Hopf fibration is a Riemannian submersion

The differential-geometric bridge from the ambient computations to the
intrinsic statement: composing with the sphere inclusions `ι : S³(1) ↪ ℂ²`
and `ι' : S²(1/2) ↪ ℝ ⊕ ℂ` identifies the intrinsic differential `DH` of
`hopfMap` with the ambient differential `hopfDeriv`
(`mfderiv_coe_hopfMap_apply`, the chain rule applied to `ι' ∘ H = Ĥ ∘ ι`).
The kernel of `DH` is spanned by the tangent lift of the vertical vector
`i(z, w)` (which exists since `i(z, w) ⊥ (z, w)`, by mathlib's
`range_mfderiv_coe_sphere`), so tangent vectors `g`-orthogonal to the kernel
have horizontal ambient image (`exists_hopfHorizontal_mfderiv_coe`), where
`real_inner_hopfDeriv_hopfHorizontal` shows `DH` preserves inner products. -/

section RiemannianSubmersion

/-- **Math.** Pointwise form of mathlib's `range_mfderiv_coe_sphere`: every
ambient vector orthogonal to the base point `x ∈ Sⁿ ⊆ E` is the image of a
tangent vector under the differential of the inclusion `Sⁿ ↪ E` (whose range
is the tangent hyperplane `x^⊥`). -/
theorem exists_mfderiv_coe_sphere_eq {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]
    (x : sphere (0 : E) 1) {v : E} (hv : ⟪(x : E), v⟫_ℝ = 0) :
    ∃ u : TangentSpace (𝓡 n) x,
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x u = v := by
  have hmem : v ∈ (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :
      TangentSpace (𝓡 n) x →L[ℝ] E).range := by
    rw [range_mfderiv_coe_sphere x]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv
  exact LinearMap.mem_range.mp hmem

/-- **Math.** For `p = (z, w) ∈ S³(1) ⊆ ℂ²`, the sphere equation reads
`‖z‖² + ‖w‖² = 1` (the `L²` product norm). -/
theorem norm_fst_sq_add_norm_snd_sq_coe_unitSphere
    (p : sphere (0 : WithLp 2 (ℂ × ℂ)) 1) :
    ‖(p : WithLp 2 (ℂ × ℂ)).fst‖ ^ 2 + ‖(p : WithLp 2 (ℂ × ℂ)).snd‖ ^ 2 = 1 := by
  rw [← WithLp.prod_norm_sq_eq_of_L2, mem_sphere_zero_iff_norm.mp p.2, one_pow]

/-- **Math.** The chain-rule bridge for the Hopf fibration: reading the
intrinsic differential `DH : T_pS³ → T_{H(p)}S²(1/2)` of `hopfMap` through
the sphere inclusions gives the ambient differential, `Dι' ∘ DH = DĤ ∘ Dι`
— differentiate `ι' ∘ H = Ĥ ∘ ι` at `p`. -/
theorem mfderiv_coe_hopfMap_apply (p : sphere (0 : WithLp 2 (ℂ × ℂ)) 1)
    (u : TangentSpace (𝓡 3) p) :
    mfderiv (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ)) (hopfMap p)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap p u)
      = hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
          (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p u) := by
  have hH : MDifferentiableAt (𝓡 3) (𝓡 2) hopfMap p :=
    (contMDiff_hopfMap p).mdifferentiableAt (by simp)
  have hι' : MDifferentiableAt (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
      ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ)) (hopfMap p) :=
    (contMDiff_coe_sphere_radius (m := 1) (1 / 2) (hopfMap p)).mdifferentiableAt
      one_ne_zero
  have hι : MDifferentiableAt (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
      ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p :=
    (contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero
  have hamb : MDifferentiableAt 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
      hopfMapAmbient (p : WithLp 2 (ℂ × ℂ)) :=
    (hasFDerivAt_hopfMapAmbient (p : WithLp 2 (ℂ × ℂ))).differentiableAt.mdifferentiableAt
  have h1 := mfderiv_comp p hι' hH
  have h2 := mfderiv_comp p hamb hι
  have hfun : (((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ)) ∘ hopfMap)
      = hopfMapAmbient ∘ ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) := rfl
  have h3 : (mfderiv (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ))
        (hopfMap p)).comp (mfderiv (𝓡 3) (𝓡 2) hopfMap p)
      = (mfderiv 𝓘(ℝ, WithLp 2 (ℂ × ℂ)) 𝓘(ℝ, WithLp 2 (ℝ × ℂ)) hopfMapAmbient
          (p : WithLp 2 (ℂ × ℂ))).comp
          (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p) := by
    rw [← h1, hfun]
    exact h2
  have h4 := DFunLike.congr_fun h3 u
  simpa [mfderiv_eq_fderiv, (hasFDerivAt_hopfMapAmbient (p : WithLp 2 (ℂ × ℂ))).fderiv]
    using h4

/-- **Math.** Petersen Example 1.1.5: a tangent vector of `S³` that is
`g`-orthogonal to the kernel of `DH` has horizontal ambient image. The
vertical vector `i(z, w)` lifts to a kernel vector of `DH` (it is tangent to
the sphere and `DĤ` kills it), so the hypothesis gives
`Dι(u) ⊥ i(z, w)`; together with `Dι(u) ⊥ (z, w)` this puts `Dι(u)` in the
horizontal plane, by `exists_hopfHorizontal_eq`. -/
theorem exists_hopfHorizontal_mfderiv_coe (p : sphere (0 : WithLp 2 (ℂ × ℂ)) 1)
    (u : TangentSpace (𝓡 3) p)
    (hu : ∀ t : TangentSpace (𝓡 3) p, mfderiv (𝓡 3) (𝓡 2) hopfMap p t = 0 →
      (sphereMetricUnit (WithLp 2 (ℂ × ℂ))).metricInner p u t = 0) :
    ∃ l : ℂ,
      mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
          ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p u
        = hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd l := by
  -- the vertical vector `i(z, w)` is tangent to `S³`; lift it to `t₀ ∈ T_pS³`
  obtain ⟨t₀, ht₀⟩ := exists_mfderiv_coe_sphere_eq (n := 3) p
    (real_inner_toLp_hopfVertical (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd)
  -- `t₀` lies in the kernel of `DH`, since `DĤ` kills the vertical vector
  have ht₀ker : mfderiv (𝓡 3) (𝓡 2) hopfMap p t₀ = 0 := by
    apply mfderiv_coe_sphere_radius_injective (1 / 2) (hopfMap p)
    rw [map_zero, mfderiv_coe_hopfMap_apply p t₀, ht₀, hopfDeriv_hopfVertical]
    rfl
  -- hence `Dι(u) ⊥ i(z, w)` …
  have h := hu t₀ ht₀ker
  rw [sphereMetricUnit_apply, ht₀] at h
  -- … and `Dι(u) ⊥ (z, w)`, since `Dι` ranges in the tangent hyperplane
  have hup : ⟪(p : WithLp 2 (ℂ × ℂ)),
      mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p u⟫_ℝ = 0 := by
    have hmem : mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p u
        ∈ (mfderiv (𝓡 3) 𝓘(ℝ, WithLp 2 (ℂ × ℂ))
            ((↑) : sphere (0 : WithLp 2 (ℂ × ℂ)) 1 → WithLp 2 (ℂ × ℂ)) p :
          TangentSpace (𝓡 3) p →L[ℝ] WithLp 2 (ℂ × ℂ)).range :=
      LinearMap.mem_range.mpr ⟨u, rfl⟩
    rw [range_mfderiv_coe_sphere p] at hmem
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hmem
  refine exists_hopfHorizontal_eq _ _ (norm_fst_sq_add_norm_snd_sq_coe_unitSphere p) _
    hup ?_
  rw [real_inner_comm]
  exact h

/-- **Math.** Petersen Example 1.1.5: the **Hopf fibration**
`H : (S³(1), g) → (S²(1/2), g)` is a Riemannian submersion for the canonical
(round) metrics of the two spheres — `sphereMetricUnit` on `S³(1) ⊆ ℂ²` and
`sphereMetric _ (1/2)` on `S²(1/2) ⊆ ℝ ⊕ ℂ`.

At `p = (z, w)`: the differential `DH` is surjective because the two
orthonormal horizontal vectors `(−w̄, z̄)` and `i(−w̄, z̄)` lift to tangent
vectors whose images under `DH` are linearly independent, hence span the
`2`-dimensional tangent space of `S²(1/2)`; and vectors orthogonal to
`ker DH` have horizontal ambient image `λ(−w̄, z̄)`, on which
`DĤ` preserves inner products (`real_inner_hopfDeriv_hopfHorizontal`, using
`|z|² + |w|² = 1`). -/
theorem hopfMap_isRiemannianSubmersion :
    IsRiemannianSubmersion (sphereMetricUnit (n := 3) (WithLp 2 (ℂ × ℂ)))
      (sphereMetric (n := 2) (WithLp 2 (ℝ × ℂ)) (1 / 2)) hopfMap := by
  refine ⟨contMDiff_hopfMap, ?_, ?_⟩
  · -- surjectivity of the differential
    intro p
    obtain ⟨t₁, ht₁⟩ := exists_mfderiv_coe_sphere_eq (n := 3) p
      (real_inner_toLp_hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst
        (p : WithLp 2 (ℂ × ℂ)).snd 1)
    obtain ⟨t₂, ht₂⟩ := exists_mfderiv_coe_sphere_eq (n := 3) p
      (real_inner_toLp_hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst
        (p : WithLp 2 (ℂ × ℂ)).snd Complex.I)
    have hy₁ : mfderiv (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ)) (hopfMap p)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap p t₁)
        = hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
            (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd 1) := by
      rw [mfderiv_coe_hopfMap_apply p t₁, ht₁]
    have hy₂ : mfderiv (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
        ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ)) (hopfMap p)
        (mfderiv (𝓡 3) (𝓡 2) hopfMap p t₂)
        = hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
            (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
              Complex.I) := by
      rw [mfderiv_coe_hopfMap_apply p t₂, ht₂]
    -- the two horizontal images are orthonormal in `ℝ ⊕ ℂ`
    have e11 : ⟪hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd 1),
        hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd 1)⟫_ℝ
        = 1 := by
      rw [real_inner_hopfDeriv_hopfHorizontal,
        norm_fst_sq_add_norm_snd_sq_coe_unitSphere p]
      simp
    have e12 : ⟪hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd 1),
        hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
          Complex.I)⟫_ℝ = 0 := by
      rw [real_inner_hopfDeriv_hopfHorizontal]
      simp
    have e21 : ⟪hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
          Complex.I),
        hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd 1)⟫_ℝ
        = 0 := by
      rw [real_inner_hopfDeriv_hopfHorizontal]
      simp [Complex.conj_I]
    have e22 : ⟪hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
          Complex.I),
        hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
        (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
          Complex.I)⟫_ℝ = 1 := by
      rw [real_inner_hopfDeriv_hopfHorizontal,
        norm_fst_sq_add_norm_snd_sq_coe_unitSphere p]
      simp [Complex.conj_I]
    -- hence `DH t₁, DH t₂` are linearly independent (the inclusion is injective)
    have hli : LinearIndependent ℝ ![mfderiv (𝓡 3) (𝓡 2) hopfMap p t₁,
        mfderiv (𝓡 3) (𝓡 2) hopfMap p t₂] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      -- transport the vanishing combination to the ambient space `ℝ ⊕ ℂ`
      have h0 : s • hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
            (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd 1)
          + t • hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
            (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
              Complex.I)
          = (0 : WithLp 2 (ℝ × ℂ)) := by
        have h := congrArg (mfderiv (𝓡 2) 𝓘(ℝ, WithLp 2 (ℝ × ℂ))
          ((↑) : sphere (0 : WithLp 2 (ℝ × ℂ)) (1 / 2) → WithLp 2 (ℝ × ℂ))
          (hopfMap p)) hst
        rw [map_add, map_smul, map_smul, hy₁, hy₂, map_zero] at h
        exact h
      -- `real_inner_smul_right`, restated so that its scalar action is
      -- syntactically the one appearing in `h0` (`simp` cannot see through
      -- the instance defeq on its own)
      have hsmul : ∀ (r : ℝ) (x y : WithLp 2 (ℝ × ℂ)), ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
        fun r x y => real_inner_smul_right x y r
      constructor
      · have hs := congrArg (fun x : WithLp 2 (ℝ × ℂ) =>
          ⟪hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
            (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst
              (p : WithLp 2 (ℂ × ℂ)).snd 1), x⟫_ℝ) h0
        simp only [inner_add_right, hsmul, e11, e12, inner_zero_right,
          mul_one, mul_zero, add_zero] at hs
        exact hs
      · have ht := congrArg (fun x : WithLp 2 (ℝ × ℂ) =>
          ⟪hopfDeriv (p : WithLp 2 (ℂ × ℂ)).fst (p : WithLp 2 (ℂ × ℂ)).snd
            (hopfHorizontal (p : WithLp 2 (ℂ × ℂ)).fst
              (p : WithLp 2 (ℂ × ℂ)).snd Complex.I), x⟫_ℝ) h0
        simp only [inner_add_right, hsmul, e21, e22, inner_zero_right,
          mul_one, mul_zero, zero_add] at ht
        exact ht
    -- two independent vectors span the 2-dimensional tangent space of `S²(1/2)`
    have hspan : Submodule.span ℝ (Set.range ![mfderiv (𝓡 3) (𝓡 2) hopfMap p t₁,
        mfderiv (𝓡 3) (𝓡 2) hopfMap p t₂]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank
        (by rw [Fintype.card_fin]; exact (finrank_euclideanSpace_fin (𝕜 := ℝ)).symm)
    intro y
    have hy : y ∈ Submodule.span ℝ (Set.range ![mfderiv (𝓡 3) (𝓡 2) hopfMap p t₁,
        mfderiv (𝓡 3) (𝓡 2) hopfMap p t₂]) := by
      rw [hspan]; exact Submodule.mem_top
    rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at hy
    obtain ⟨a, b, hab⟩ := hy
    refine ⟨a • t₁ + b • t₂, ?_⟩
    rw [map_add, map_smul, map_smul]
    exact hab
  · -- the isometry property on the orthogonal complement of the kernel
    intro p u v hu hv
    obtain ⟨l, hl⟩ := exists_hopfHorizontal_mfderiv_coe p u hu
    obtain ⟨m, hm⟩ := exists_hopfHorizontal_mfderiv_coe p v hv
    rw [sphereMetricUnit_apply, sphereMetric_apply, mfderiv_coe_hopfMap_apply p u,
      mfderiv_coe_hopfMap_apply p v, hl, hm, real_inner_hopfHorizontal,
      real_inner_hopfDeriv_hopfHorizontal,
      norm_fst_sq_add_norm_snd_sq_coe_unitSphere p]
    norm_num

end RiemannianSubmersion

import PetersenLib.Ch01.PolarCoordinates
import PetersenLib.Ch02.DirectionalDerivative

/-!
# Petersen Ch. 2, §2.1 — the gradient is not coordinate-invariant

Petersen (§2.1, rem:pet-ch2-gradient-not-invariant) warns that the coordinate
recipe `∇f = g^{ij}∂_i(f)∂_j`, which in Cartesian coordinates on `ℝⁿ` reads
`∇f = Σ_i ∂_i(f)∂_i`, is **not** invariantly defined: forming the analogous
expression `∂_r(f)∂_r + ∂_θ(f)∂_θ` in polar coordinates does *not* reproduce the
true (metric) gradient.

We make this concrete on `ℝ²`. For the linear function `f(x) = x_0` at the point
`P(2, π/2) = (0, 2)`, the naive polar expression
`naivePolarGradient f (2, π/2)` evaluates to `(4, 0)`, whereas the true gradient
`gradient (euclideanMetric 2) f (P(2, π/2))` is the constant field `e_0 = (1, 0)`
(`gradient_not_coordinate_invariant`). The two differ, so the bare coordinate
sum `∂_a(f)∂_a` carries no invariant meaning.

Here `∂_r, ∂_θ` are the polar coordinate basis vectors — the columns of the polar
Jacobian `polarJacobian` (Example 1.4.2) — and `∂_r(f), ∂_θ(f)` are the partial
derivatives of `f ∘ P` in the polar chart.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.
-/

noncomputable section

open Real Bundle
open scoped Manifold Topology ContDiff

namespace PetersenLib

/-- **Math.** The naive "polar-coordinate gradient" of a function `f` on `ℝ²`,
`∂_r(f)∂_r + ∂_θ(f)∂_θ`: the polar-coordinate partial derivatives of `f`
weighting the polar coordinate basis vectors (the columns `polarJacobian q (1,0)`,
`polarJacobian q (0,1)`), formed the same way as the Cartesian `∇f = Σ_i ∂_i(f)∂_i`
but read in the polar chart. -/
def naivePolarGradient (f : EuclideanSpace ℝ (Fin 2) → ℝ) (q : ℝ × ℝ) :
    EuclideanSpace ℝ (Fin 2) :=
  (fderiv ℝ (f ∘ polarCoordinatesMap) q (1, 0)) • polarJacobian q (1, 0)
    + (fderiv ℝ (f ∘ polarCoordinatesMap) q (0, 1)) • polarJacobian q (0, 1)

/-- **Math.** **The gradient is not coordinate-invariant** (Petersen §2.1,
rem:pet-ch2-gradient-not-invariant). For `f(x) = x_0` on `ℝ²` at the point
`P(2, π/2) = (0, 2)`, the naive polar-coordinate gradient
`∂_r(f)∂_r + ∂_θ(f)∂_θ` equals `(4, 0)` but the true metric gradient is the
constant field `e_0 = (1, 0)`; the two are different. Thus the coordinate
expression `∂_a(f)∂_a` is not an invariantly defined object (unlike `df` or,
given a metric, `∇f = g^{ij}∂_i(f)∂_j`). -/
theorem gradient_not_coordinate_invariant :
    naivePolarGradient (fun x => x 0) (2, π / 2)
      ≠ gradient (euclideanMetric 2) (fun x => x 0) (polarCoordinatesMap (2, π / 2)) := by
  set f : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => x 0 with hf
  set q₀ : ℝ × ℝ := (2, π / 2) with hq₀
  -- component `0` of the polar Jacobian applied to a direction
  have hjac0 : ∀ v : ℝ × ℝ, (polarJacobian q₀ v) 0
      = Real.cos q₀.2 * v.1 - q₀.1 * Real.sin q₀.2 * v.2 := by
    intro v
    simp only [polarJacobian, ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, PiLp.continuousLinearEquiv_symm_apply,
      ContinuousLinearMap.pi_apply, Matrix.cons_val_zero,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  -- `f ∘ P` is the first Cartesian coordinate `r cos θ`, with computable derivative
  have hcomp : (f ∘ polarCoordinatesMap) = fun q : ℝ × ℝ => q.1 * Real.cos q.2 := by
    funext q; simp [hf, polarCoordinatesMap]
  have hb : HasFDerivAt (fun q : ℝ × ℝ => Real.cos q.2)
      ((-Real.sin q₀.2) • ContinuousLinearMap.snd ℝ ℝ ℝ) q₀ :=
    (Real.hasDerivAt_cos q₀.2).comp_hasFDerivAt q₀ hasFDerivAt_snd
  have hab : HasFDerivAt (fun q : ℝ × ℝ => q.1 * Real.cos q.2)
      (q₀.1 • ((-Real.sin q₀.2) • ContinuousLinearMap.snd ℝ ℝ ℝ)
        + Real.cos q₀.2 • ContinuousLinearMap.fst ℝ ℝ ℝ) q₀ :=
    (hasFDerivAt_fst).mul hb
  have hfd : ∀ v : ℝ × ℝ, fderiv ℝ (f ∘ polarCoordinatesMap) q₀ v
      = Real.cos q₀.2 * v.1 - q₀.1 * Real.sin q₀.2 * v.2 := by
    intro v
    rw [hcomp, hab.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
    ring
  have hcos : Real.cos q₀.2 = 0 := by rw [hq₀]; exact Real.cos_pi_div_two
  have hsin : Real.sin q₀.2 = 1 := by rw [hq₀]; exact Real.sin_pi_div_two
  -- the naive polar gradient has first Cartesian component `4`
  have hnaive0 : (naivePolarGradient f q₀) 0 = 4 := by
    simp only [naivePolarGradient, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      hfd, hjac0, hcos, hsin]
    rw [hq₀]; norm_num
  -- the true gradient of `x ↦ x_0` is the constant field `e_0`
  have hclm : f = fun x => (EuclideanSpace.proj (0 : Fin 2) :
      EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) x := by funext x; rfl
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun a b => rfl
  have hgrad_eq : gradient (euclideanMetric 2) f (polarCoordinatesMap q₀)
      = EuclideanSpace.single 0 1 := by
    symm
    apply gradient_unique
    intro w
    rw [mfderiv_eq_fderiv, hclm, ContinuousLinearMap.fderiv]
    unfold euclideanMetric
    rw [innerProductSpaceMetric_apply]
    simp only [PiLp.inner_apply, Fin.sum_univ_two, PiLp.single_apply, hinner, if_pos, mul_one]
    norm_num
    rfl
  -- conclude: the two disagree already in the first Cartesian component (`4 ≠ 1`)
  intro hEq
  rw [hgrad_eq] at hEq
  have hcomp0 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) hEq
  simp only [hnaive0, PiLp.single_apply] at hcomp0
  norm_num at hcomp0

end PetersenLib

end

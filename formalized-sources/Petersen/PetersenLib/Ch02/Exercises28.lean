import PetersenLib.Ch02.DivergenceProductRules
import PetersenLib.Ch03.EuclideanCurvature
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.28(3): an incompressible unit field on `ℝ³`

Petersen (§2.5, Exercise 2.5.28) calls a vector field `X` (and its flow)
**incompressible** when `div X = 0`.  Part (3) asks for an *incompressible unit*
vector field on `ℝ³` whose covariant derivative does **not** vanish.

**The field.**  Petersen's example (in the coordinate-free form used here) is the
"twisting" field
`X(x) = cos⟨a, x⟩ · u + sin⟨a, x⟩ · v`,
where `a, u, v` is an orthonormal triple (`a = e₃`, `u = e₁`, `v = e₂` in
coordinates).  It is a **unit** field because `‖X‖² = cos² + sin² = 1`, and its
Euclidean differential is the rank-one map
`dX_x(w) = ⟨a, w⟩ · (−sin⟨a, x⟩ · u + cos⟨a, x⟩ · v) = ⟨a, w⟩ · N(x)`,
with `N(x) = −sin⟨a, x⟩ · u + cos⟨a, x⟩ · v` again a unit vector orthogonal to
`a` (as `u, v ⊥ a`).

**Incompressible.**  Against the standard orthonormal frame `bᵢ` the divergence is
the covariant trace (`divergenceLieDerivative_eq_sum_covariant`)
`div X = Σᵢ ⟨∇_{bᵢ}X, bᵢ⟩ = Σᵢ ⟨a, bᵢ⟩⟨N, bᵢ⟩ = ⟨a, N⟩ = 0`,
the last step being Parseval (`OrthonormalBasis.sum_inner_mul_inner`) and
`a ⊥ N`.

**Non-parallel.**  `∇_a X|₀ = dX_0(a) = ‖a‖² · N(0) = v ≠ 0`, so `∇X ≠ 0`.

Parts (1) (incompressible ⇔ volume-preserving flow) and (2) (a unit
incompressible field on `ℝ²` is parallel) are not formalized: (1) needs the flow
of a vector field and the divergence/Stokes theorem, absent from the manifold
API; (2) is a `ℝ²`-specific PDE argument.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.28.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

/-! ## The twisting field on an inner product space -/

section TwistField

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** The **twisting field** `X(x) = cos⟨a, x⟩ · u + sin⟨a, x⟩ · v`. -/
def twistField (a u v : F) : Π x : F, TangentSpace 𝓘(ℝ, F) x :=
  fun x => Real.cos (inner ℝ a x) • u + Real.sin (inner ℝ a x) • v

/-- **Math.** The **twist normal** `N(x) = −sin⟨a, x⟩ · u + cos⟨a, x⟩ · v`, the
value of `dX_x` in the direction `a` up to the factor `‖a‖²`. -/
def twistNormal (a u v : F) (x : F) : F :=
  -(Real.sin (inner ℝ a x)) • u + Real.cos (inner ℝ a x) • v

theorem twistField_apply (a u v : F) (x : F) :
    twistField a u v x = Real.cos (inner ℝ a x) • u + Real.sin (inner ℝ a x) • v := rfl

/-- **Math.** The Euclidean differential of the twisting field:
`HasFDerivAt X ((−sin θ · ⟨a, ·⟩)·u + (cos θ · ⟨a, ·⟩)·v)` with `θ = ⟨a, x⟩`. -/
theorem twistField_hasFDerivAt (a u v : F) (x : F) :
    HasFDerivAt (twistField a u v)
      ((-(Real.sin (inner ℝ a x)) • innerSL ℝ a).smulRight u
        + (Real.cos (inner ℝ a x) • innerSL ℝ a).smulRight v) x := by
  have hθ : HasFDerivAt (fun y : F => inner ℝ a y) (innerSL ℝ a) x := by
    simpa using (innerSL ℝ a).hasFDerivAt
  have hc : HasFDerivAt (fun y : F => Real.cos (inner ℝ a y) • u)
      ((-(Real.sin (inner ℝ a x)) • innerSL ℝ a).smulRight u) x :=
    (HasFDerivAt.cos hθ).smul_const u
  have hs : HasFDerivAt (fun y : F => Real.sin (inner ℝ a y) • v)
      ((Real.cos (inner ℝ a x) • innerSL ℝ a).smulRight v) x :=
    (HasFDerivAt.sin hθ).smul_const v
  exact hc.add hs

/-- **Math.** `dX_x(w) = ⟨a, w⟩ · N(x)`. -/
theorem twistField_fderiv_apply (a u v : F) (x w : F) :
    fderiv ℝ (twistField a u v) x w = inner ℝ a w • twistNormal a u v x := by
  rw [(twistField_hasFDerivAt a u v x).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, twistNormal]
  module

/-- Constant-coefficient smoothness: the twisting field is `C^∞`. -/
theorem twistField_smooth (a u v : F) :
    IsSmoothVectorField (I := 𝓘(ℝ, F)) (twistField a u v) := by
  rw [isSmoothVectorField_iff_contDiff]
  have hθ : ContDiff ℝ ∞ (fun y : F => inner ℝ a y) := (innerSL ℝ a).contDiff
  have hc : ContDiff ℝ ∞ (fun y : F => Real.cos (inner ℝ a y) • u) :=
    (ContDiff.comp Real.contDiff_cos hθ).smul contDiff_const
  have hs : ContDiff ℝ ∞ (fun y : F => Real.sin (inner ℝ a y) • v) :=
    (ContDiff.comp Real.contDiff_sin hθ).smul contDiff_const
  exact hc.add hs

/-- **Math.** `X` is a unit field when `a, u, v` has `u, v` orthonormal:
`‖X(x)‖ = 1`. -/
theorem twistField_norm (a u v : F)
    (huu : inner ℝ u u = (1 : ℝ)) (hvv : inner ℝ v v = (1 : ℝ))
    (huv : inner ℝ u v = (0 : ℝ)) (x : F) :
    ‖twistField a u v x‖ = 1 := by
  have hsq : inner ℝ (twistField a u v x) (twistField a u v x) = (1 : ℝ) := by
    show inner ℝ (Real.cos (inner ℝ a x) • u + Real.sin (inner ℝ a x) • v : F)
      (Real.cos (inner ℝ a x) • u + Real.sin (inner ℝ a x) • v : F) = 1
    rw [real_inner_add_add_self]
    simp only [real_inner_smul_left, real_inner_smul_right, huu, hvv, huv]
    have := Real.sin_sq_add_cos_sq (inner ℝ a x)
    ring_nf
    ring_nf at this
    linarith
  have hnorm : ‖twistField a u v x‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq]; exact hsq
  have hnn : 0 ≤ ‖twistField a u v x‖ := norm_nonneg _
  have hfac : (‖twistField a u v x‖ - 1) * (‖twistField a u v x‖ + 1) = 0 := by
    nlinarith [hnorm]
  rcases mul_eq_zero.mp hfac with h | h <;> linarith

/-- `N(x) ≠ 0` when `u, v` are orthonormal (`‖N(x)‖ = 1`). -/
theorem twistNormal_ne_zero (a u v : F)
    (huu : inner ℝ u u = (1 : ℝ)) (hvv : inner ℝ v v = (1 : ℝ))
    (huv : inner ℝ u v = (0 : ℝ)) (x : F) :
    twistNormal a u v x ≠ 0 := by
  intro hz
  have hsq : inner ℝ (twistNormal a u v x) (twistNormal a u v x) = (1 : ℝ) := by
    rw [twistNormal, real_inner_add_add_self (-(Real.sin (inner ℝ a x)) • u)
      (Real.cos (inner ℝ a x) • v)]
    simp only [real_inner_smul_left, real_inner_smul_right, huu, hvv, huv]
    have := Real.sin_sq_add_cos_sq (inner ℝ a x)
    ring_nf
    ring_nf at this
    linarith
  rw [hz, inner_zero_left] at hsq
  norm_num at hsq

/-- **Math.** The twist normal `N(x)` is orthogonal to the twist axis `a` when
`a ⊥ u` and `a ⊥ v`: `⟨a, N(x)⟩ = 0`.  This is the vanishing of the divergence. -/
theorem inner_axis_twistNormal (a u v : F) (x : F)
    (hau : inner ℝ a u = (0 : ℝ)) (hav : inner ℝ a v = (0 : ℝ)) :
    inner ℝ a (twistNormal a u v x) = 0 := by
  rw [twistNormal, inner_add_right, real_inner_smul_right, real_inner_smul_right, hau, hav]
  ring

end TwistField

/-! ## Exercise 2.5.28(3) on `ℝ³`

The divergence is `div X = Σᵢ g(∇_{Eᵢ}X, Eᵢ)` against a positively oriented
orthonormal frame `Eᵢ` (`divergenceLieDerivative_eq_sum_covariant`).  On `ℝ³`
with the standard orthonormal frame `e₁, e₂, e₃` this covariant trace *is* the
divergence; we express **incompressibility** through it directly (the
volume-form `divergenceLieDerivative` would require installing a `HasMetric`
instance on `ℝ³`, whose induced tangent-bundle inner product diamonds with the
native inner product of `EuclideanSpace`). -/

section Euclidean3

open Module

/-- **Math.** **Exercise 2.5.28(3).** There is an incompressible unit vector
field on `ℝ³` whose covariant derivative does not vanish: the twisting field
`X(x) = cos⟨e₃, x⟩ · e₁ + sin⟨e₃, x⟩ · e₂`.  It is a unit field; its covariant
divergence — the trace `Σᵢ g(∇_{eᵢ}X, eᵢ)` of `∇X` against the standard
orthonormal frame, which is the divergence — is `⟨e₃, N⟩ = 0` (the twist normal
`N` is orthogonal to `e₃`); and `∇_{e₃}X|₀ = e₂ ≠ 0`. -/
theorem exercise2_5_28 :
    ∃ X : Π x : EuclideanSpace ℝ (Fin 3), TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x,
      IsSmoothVectorField X ∧
      (∀ x, ‖X x‖ = 1) ∧
      (∀ x, ∑ i : Fin 3,
        inner ℝ (((innerProductSpaceMetric (EuclideanSpace ℝ (Fin 3))).leviCivita).cov x
            (EuclideanSpace.basisFun (Fin 3) ℝ i) X)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) = 0) ∧
      (∃ (x : EuclideanSpace ℝ (Fin 3))
          (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
        ((innerProductSpaceMetric (EuclideanSpace ℝ (Fin 3))).leviCivita).cov x w X ≠ 0) := by
  classical
  set eb : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3)) :=
    EuclideanSpace.basisFun (Fin 3) ℝ with heb
  set a : EuclideanSpace ℝ (Fin 3) := eb 2 with ha
  set u : EuclideanSpace ℝ (Fin 3) := eb 0 with hu
  set v : EuclideanSpace ℝ (Fin 3) := eb 1 with hv
  have hon : ∀ i j : Fin 3, inner ℝ (eb i) (eb j) = if i = j then (1 : ℝ) else 0 :=
    orthonormal_iff_ite.mp eb.orthonormal
  have huu : inner ℝ u u = (1 : ℝ) := by simp [hu]
  have hvv : inner ℝ v v = (1 : ℝ) := by simp [hv]
  have huv : inner ℝ u v = (0 : ℝ) := by simp [hu, hv, hon]
  have hau : inner ℝ a u = (0 : ℝ) := by simp [ha, hu, hon]
  have hav : inner ℝ a v = (0 : ℝ) := by simp [ha, hv, hon]
  have haa : inner ℝ a a = (1 : ℝ) := by simp [ha]
  refine ⟨twistField a u v, twistField_smooth a u v,
    fun x => twistField_norm a u v huu hvv huv x, ?_, ?_⟩
  · -- incompressible: the covariant divergence vanishes
    intro x
    have hcov : ∀ i : Fin 3,
        ((innerProductSpaceMetric (EuclideanSpace ℝ (Fin 3))).leviCivita).cov x (eb i)
            (twistField a u v)
          = inner ℝ a (eb i) • twistNormal a u v x := by
      intro i
      have h := leviCivita_cov_eq_euclidean (F := EuclideanSpace ℝ (Fin 3))
        (V := fun _ => eb i) (W := twistField a u v) (isSmoothVectorField_const (eb i))
        (twistField_smooth a u v) x
      rw [h]
      simp only [covariantDerivativeEuclidean_apply]
      rw [twistField_fderiv_apply]
    have hterm : ∀ i : Fin 3,
        inner ℝ (((innerProductSpaceMetric (EuclideanSpace ℝ (Fin 3))).leviCivita).cov x (eb i)
            (twistField a u v)) (eb i)
          = inner ℝ a (eb i) * inner ℝ (twistNormal a u v x) (eb i) := by
      intro i
      rw [hcov i]
      show inner ℝ (inner ℝ a (eb i) • twistNormal a u v x : EuclideanSpace ℝ (Fin 3)) (eb i)
        = inner ℝ a (eb i) * inner ℝ (twistNormal a u v x) (eb i)
      rw [real_inner_smul_left]
    have hsum : ∑ i : Fin 3,
          inner ℝ (((innerProductSpaceMetric (EuclideanSpace ℝ (Fin 3))).leviCivita).cov x (eb i)
            (twistField a u v)) (eb i)
        = ∑ i : Fin 3, inner ℝ a (eb i) * inner ℝ (twistNormal a u v x) (eb i) :=
      Finset.sum_congr rfl (fun i _ => hterm i)
    exact hsum.trans ((Finset.sum_congr rfl (fun i _ => by
        rw [real_inner_comm (twistNormal a u v x) (eb i)])).trans
      ((eb.sum_inner_mul_inner a (twistNormal a u v x)).trans
        (inner_axis_twistNormal a u v x hau hav)))
  · -- the covariant derivative does not vanish: ∇_{e₃}X|₀ = e₂ ≠ 0
    refine ⟨0, a, ?_⟩
    have h := leviCivita_cov_eq_euclidean (F := EuclideanSpace ℝ (Fin 3))
      (V := fun _ => a) (W := twistField a u v) (isSmoothVectorField_const a)
      (twistField_smooth a u v) 0
    rw [h]
    simp only [covariantDerivativeEuclidean_apply]
    rw [twistField_fderiv_apply, haa, one_smul]
    have hN0 : twistNormal a u v 0 = v := by
      simp [twistNormal, inner_zero_right]
    rw [hN0, hv]
    simpa using eb.toBasis.ne_zero 1

end Euclidean3

end PetersenLib

end

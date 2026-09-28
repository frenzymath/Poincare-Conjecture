import Topping.ParabolicPDE.Scalar

/-!
# Smooth producers for the scalar principal-symbol formula

This file connects the formal scalar jets in `Scalar.lean` to actual twice
continuously differentiable functions on a finite-dimensional coordinate
space.  Coordinate derivatives are evaluations of the Frechet derivative on
the standard coordinate vectors.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

/-- The coordinate domain used by a scalar operator with `n` spatial
coordinates. -/
abbrev ScalarCoordinateSpace (n : ℕ) := Fin n → ℝ

/-- The `i`th standard coordinate vector. -/
def scalarCoordinateVector {n : ℕ} (i : Fin n) : ScalarCoordinateSpace n :=
  Pi.single i 1

/-- The coordinate evaluation of the Frechet derivative of `g` at `x`. -/
def coordinateFDeriv {n : ℕ} (g : ScalarCoordinateSpace n → ℝ)
    (x : ScalarCoordinateSpace n) (i : Fin n) : ℝ :=
  fderiv ℝ g x (scalarCoordinateVector i)

/-- The iterated coordinate derivative `D_i (D_k g)` obtained from actual
Frechet derivatives. -/
def coordinateSecondFDeriv {n : ℕ} (g : ScalarCoordinateSpace n → ℝ)
    (x : ScalarCoordinateSpace n) (i k : Fin n) : ℝ :=
  coordinateFDeriv (fun y => coordinateFDeriv g y k) x i

/-- The formal second-order jet produced by actual Frechet derivatives. -/
def frechetScalarJetAt {n : ℕ} (g : ScalarCoordinateSpace n → ℝ)
    (x : ScalarCoordinateSpace n) : ScalarSecondOrderJet n where
  value := g x
  first := coordinateFDeriv g x
  second := coordinateSecondFDeriv g x

/-- The exponential phase appearing in the principal-symbol test. -/
def exponentialPhase {n : ℕ} (s : ℝ)
    (phi : ScalarCoordinateSpace n → ℝ) : ScalarCoordinateSpace n → ℝ :=
  fun y => Real.exp (s * phi y)

/-- The actual function `exp (s phi) f`. -/
def exponentialProduct {n : ℕ} (s : ℝ)
    (phi f : ScalarCoordinateSpace n → ℝ) : ScalarCoordinateSpace n → ℝ :=
  fun y => exponentialPhase s phi y * f y

namespace ScalarSecondOrderJet

/-- Two scalar second-order jets are equal when their three components are
equal. -/
theorem ext_fields {n : ℕ} {j₁ j₂ : ScalarSecondOrderJet n}
    (hvalue : j₁.value = j₂.value)
    (hfirst : j₁.first = j₂.first)
    (hsecond : j₁.second = j₂.second) :
    j₁ = j₂ := by
  cases j₁
  cases j₂
  simp_all

/-- Scale every component of a scalar second-order jet. -/
def scale {n : ℕ} (c : ℝ) (j : ScalarSecondOrderJet n) :
    ScalarSecondOrderJet n where
  value := c * j.value
  first := fun i => c * j.first i
  second := fun i k => c * j.second i k

@[simp] theorem scale_value {n : ℕ} (c : ℝ) (j : ScalarSecondOrderJet n) :
    (j.scale c).value = c * j.value := rfl

@[simp] theorem scale_first {n : ℕ} (c : ℝ) (j : ScalarSecondOrderJet n)
    (i : Fin n) :
    (j.scale c).first i = c * j.first i := rfl

@[simp] theorem scale_second {n : ℕ} (c : ℝ) (j : ScalarSecondOrderJet n)
    (i k : Fin n) :
    (j.scale c).second i k = c * j.second i k := rfl

end ScalarSecondOrderJet

/-- The actual jet of `exp (s phi) f`, with the common factor
`exp (s phi x)` removed. -/
def normalizedExponentialJetAt {n : ℕ} (s : ℝ)
    (phi f : ScalarCoordinateSpace n → ℝ) (x : ScalarCoordinateSpace n) :
    ScalarSecondOrderJet n :=
  (frechetScalarJetAt (exponentialProduct s phi f) x).scale
    (Real.exp (-(s * phi x)))

/-! ## Coordinate Frechet calculus -/

theorem coordinateFDeriv_const_mul {n : ℕ}
    {g : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (i : Fin n) (c : ℝ) (hg : DifferentiableAt ℝ g x) :
    coordinateFDeriv (fun y => c * g y) x i =
      c * coordinateFDeriv g x i := by
  rw [coordinateFDeriv, fderiv_const_mul hg c]
  simp [coordinateFDeriv]

theorem coordinateFDeriv_add {n : ℕ}
    {g h : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (i : Fin n) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    coordinateFDeriv (fun y => g y + h y) x i =
      coordinateFDeriv g x i + coordinateFDeriv h x i := by
  rw [coordinateFDeriv, fderiv_fun_add hg hh]
  simp [coordinateFDeriv]

theorem coordinateFDeriv_mul {n : ℕ}
    {g h : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (i : Fin n) (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) :
    coordinateFDeriv (fun y => g y * h y) x i =
      g x * coordinateFDeriv h x i + h x * coordinateFDeriv g x i := by
  rw [coordinateFDeriv, fderiv_fun_mul hg hh]
  simp [coordinateFDeriv]

theorem coordinateFDeriv_exp {n : ℕ}
    {g : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (i : Fin n) (hg : DifferentiableAt ℝ g x) :
    coordinateFDeriv (fun y => Real.exp (g y)) x i =
      Real.exp (g x) * coordinateFDeriv g x i := by
  rw [coordinateFDeriv, fderiv_exp hg]
  simp [coordinateFDeriv]

theorem coordinateFDeriv_differentiable_of_contDiff_two {n : ℕ}
    {g : ScalarCoordinateSpace n → ℝ} (hg : ContDiff ℝ 2 g) (k : Fin n) :
    Differentiable ℝ (fun y => coordinateFDeriv g y k) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ g) :=
    hg.fderiv_right (by norm_num)
  have he : ContDiff ℝ 1
      (fun _ : ScalarCoordinateSpace n => scalarCoordinateVector k) :=
    contDiff_const
  exact (hfd.clm_apply he).differentiable (by norm_num)

/-- The second-order product rule for genuine iterated coordinate Frechet
derivatives. -/
theorem coordinateSecondFDeriv_mul {n : ℕ}
    {g h : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (i k : Fin n) (hg : Differentiable ℝ g) (hh : Differentiable ℝ h)
    (hg2 : DifferentiableAt ℝ (fun y => coordinateFDeriv g y k) x)
    (hh2 : DifferentiableAt ℝ (fun y => coordinateFDeriv h y k) x) :
    coordinateSecondFDeriv (fun y => g y * h y) x i k =
      g x * coordinateSecondFDeriv h x i k +
        coordinateFDeriv g x i * coordinateFDeriv h x k +
        coordinateFDeriv h x i * coordinateFDeriv g x k +
        h x * coordinateSecondFDeriv g x i k := by
  unfold coordinateSecondFDeriv
  rw [show (fun y => coordinateFDeriv (fun z => g z * h z) y k) =
      fun y => g y * coordinateFDeriv h y k +
        h y * coordinateFDeriv g y k by
    funext y
    exact coordinateFDeriv_mul k (hg y) (hh y)]
  calc
    coordinateFDeriv
        (fun y => g y * coordinateFDeriv h y k +
          h y * coordinateFDeriv g y k) x i =
      coordinateFDeriv (fun y => g y * coordinateFDeriv h y k) x i +
        coordinateFDeriv (fun y => h y * coordinateFDeriv g y k) x i := by
          exact coordinateFDeriv_add i ((hg x).mul hh2) ((hh x).mul hg2)
    _ = _ := by
      rw [coordinateFDeriv_mul i (hg x) hh2]
      rw [coordinateFDeriv_mul i (hh x) hg2]
      ring

theorem coordinateFDeriv_exponentialPhase {n : ℕ}
    {phi : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (s : ℝ) (i : Fin n) (hphi : DifferentiableAt ℝ phi x) :
    coordinateFDeriv (exponentialPhase s phi) x i =
      Real.exp (s * phi x) * (s * coordinateFDeriv phi x i) := by
  change coordinateFDeriv (fun y => Real.exp (s * phi y)) x i = _
  rw [coordinateFDeriv_exp i (hphi.const_mul s)]
  rw [coordinateFDeriv_const_mul i s hphi]

theorem coordinateSecondFDeriv_exponentialPhase {n : ℕ}
    {phi : ScalarCoordinateSpace n → ℝ} {x : ScalarCoordinateSpace n}
    (s : ℝ) (i k : Fin n) (hphi : ContDiff ℝ 2 phi) :
    coordinateSecondFDeriv (exponentialPhase s phi) x i k =
      Real.exp (s * phi x) *
        (s ^ 2 * coordinateFDeriv phi x i * coordinateFDeriv phi x k +
          s * coordinateSecondFDeriv phi x i k) := by
  have hphiDiff : Differentiable ℝ phi := hphi.differentiable (by norm_num)
  have hphiPartial :
      Differentiable ℝ (fun y => coordinateFDeriv phi y k) :=
    coordinateFDeriv_differentiable_of_contDiff_two hphi k
  unfold coordinateSecondFDeriv
  rw [show (fun y => coordinateFDeriv (exponentialPhase s phi) y k) =
      fun y => Real.exp (s * phi y) *
        (s * coordinateFDeriv phi y k) by
    funext y
    exact coordinateFDeriv_exponentialPhase s k (hphiDiff y)]
  rw [coordinateFDeriv_mul i
    (((hphiDiff x).const_mul s).exp) ((hphiPartial x).const_mul s)]
  rw [coordinateFDeriv_exp i ((hphiDiff x).const_mul s)]
  rw [coordinateFDeriv_const_mul i s (hphiDiff x)]
  rw [coordinateFDeriv_const_mul i s (hphiPartial x)]
  ring

namespace ScalarSecondOrderCoefficients

/-- Evaluation of a linear scalar operator commutes with scaling a formal
jet. -/
theorem applyJet_scale {Omega : Type*} {n : ℕ}
    (A : ScalarSecondOrderCoefficients Omega n) (x : Omega)
    (c : ℝ) (j : ScalarSecondOrderJet n) :
    A.applyJet x (j.scale c) = c * A.applyJet x j := by
  simp only [applyJet, ScalarSecondOrderJet.scale]
  have hmul (a z : ℝ) : a * (c * z) = c * (a * z) := by ring
  simp_rw [hmul, ← Finset.mul_sum]
  ring

end ScalarSecondOrderCoefficients

/-- The actual twice-differentiated exponential product has exactly the
formal normalized jet used in `Scalar.lean`. -/
theorem normalizedExponentialJetAt_eq_normalizedConjugatedJet {n : ℕ}
    (s : ℝ) (phi f : ScalarCoordinateSpace n → ℝ)
    (x : ScalarCoordinateSpace n) (hphi : ContDiff ℝ 2 phi)
    (hf : ContDiff ℝ 2 f) :
    normalizedExponentialJetAt s phi f x =
      normalizedConjugatedJet s (frechetScalarJetAt phi x)
        (frechetScalarJetAt f x) := by
  have hphiDiff : Differentiable ℝ phi := hphi.differentiable (by norm_num)
  have hfDiff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hscaled : ContDiff ℝ 2 (fun y => s * phi y) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using hphi.const_smul s
  have hphase : ContDiff ℝ 2 (exponentialPhase s phi) := by
    exact hscaled.exp
  have hphaseDiff : Differentiable ℝ (exponentialPhase s phi) :=
    hphase.differentiable (by norm_num)
  have hcancel :
      Real.exp (-(s * phi x)) * Real.exp (s * phi x) = 1 := by
    rw [Real.exp_neg]
    exact inv_mul_cancel₀ (Real.exp_ne_zero _)
  apply ScalarSecondOrderJet.ext_fields
  · change Real.exp (-(s * phi x)) *
        (Real.exp (s * phi x) * f x) = f x
    calc
      Real.exp (-(s * phi x)) * (Real.exp (s * phi x) * f x) =
          (Real.exp (-(s * phi x)) * Real.exp (s * phi x)) * f x := by ring
      _ = f x := by rw [hcancel]; ring
  · funext i
    change Real.exp (-(s * phi x)) *
        coordinateFDeriv (fun y => exponentialPhase s phi y * f y) x i =
      s * coordinateFDeriv phi x i * f x + coordinateFDeriv f x i
    rw [coordinateFDeriv_mul i (hphaseDiff x) (hfDiff x)]
    rw [coordinateFDeriv_exponentialPhase s i (hphiDiff x)]
    calc
      Real.exp (-(s * phi x)) *
          (Real.exp (s * phi x) * coordinateFDeriv f x i +
            f x * (Real.exp (s * phi x) *
              (s * coordinateFDeriv phi x i))) =
        (Real.exp (-(s * phi x)) * Real.exp (s * phi x)) *
          (s * coordinateFDeriv phi x i * f x +
            coordinateFDeriv f x i) := by ring
      _ = s * coordinateFDeriv phi x i * f x +
          coordinateFDeriv f x i := by rw [hcancel]; ring
  · funext i k
    have hphasePartial :
        DifferentiableAt ℝ
          (fun y => coordinateFDeriv (exponentialPhase s phi) y k) x :=
      (coordinateFDeriv_differentiable_of_contDiff_two hphase k) x
    have hfPartial :
        DifferentiableAt ℝ (fun y => coordinateFDeriv f y k) x :=
      (coordinateFDeriv_differentiable_of_contDiff_two hf k) x
    change Real.exp (-(s * phi x)) *
        coordinateSecondFDeriv
          (fun y => exponentialPhase s phi y * f y) x i k =
      s ^ 2 * coordinateFDeriv phi x i * coordinateFDeriv phi x k * f x +
        s * (coordinateSecondFDeriv phi x i k * f x +
          coordinateFDeriv phi x i * coordinateFDeriv f x k +
          coordinateFDeriv phi x k * coordinateFDeriv f x i) +
        coordinateSecondFDeriv f x i k
    rw [coordinateSecondFDeriv_mul i k hphaseDiff hfDiff
      hphasePartial hfPartial]
    rw [coordinateFDeriv_exponentialPhase s i (hphiDiff x)]
    rw [coordinateFDeriv_exponentialPhase s k (hphiDiff x)]
    rw [coordinateSecondFDeriv_exponentialPhase s i k hphi]
    calc
      Real.exp (-(s * phi x)) *
          (Real.exp (s * phi x) * coordinateSecondFDeriv f x i k +
              Real.exp (s * phi x) * (s * coordinateFDeriv phi x i) *
                coordinateFDeriv f x k +
            coordinateFDeriv f x i *
              (Real.exp (s * phi x) * (s * coordinateFDeriv phi x k)) +
          f x *
            (Real.exp (s * phi x) *
              (s ^ 2 * coordinateFDeriv phi x i * coordinateFDeriv phi x k +
                s * coordinateSecondFDeriv phi x i k))) =
        (Real.exp (-(s * phi x)) * Real.exp (s * phi x)) *
          (s ^ 2 * coordinateFDeriv phi x i * coordinateFDeriv phi x k * f x +
            s * (coordinateSecondFDeriv phi x i k * f x +
              coordinateFDeriv phi x i * coordinateFDeriv f x k +
              coordinateFDeriv phi x k * coordinateFDeriv f x i) +
            coordinateSecondFDeriv f x i k) := by ring
      _ = s ^ 2 * coordinateFDeriv phi x i * coordinateFDeriv phi x k * f x +
          s * (coordinateSecondFDeriv phi x i k * f x +
            coordinateFDeriv phi x i * coordinateFDeriv f x k +
            coordinateFDeriv phi x k * coordinateFDeriv f x i) +
          coordinateSecondFDeriv f x i k := by rw [hcancel]; ring

/-- Applying the coordinate operator to the actual exponential product and
removing its common exponential factor gives the formal conjugated operator
exactly. -/
theorem normalizedExponentialOperator_eq_conjugated {n : ℕ}
    (A : ScalarSecondOrderCoefficients (ScalarCoordinateSpace n) n)
    (x : ScalarCoordinateSpace n) (s : ℝ)
    (phi f : ScalarCoordinateSpace n → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hf : ContDiff ℝ 2 f) :
    Real.exp (-(s * phi x)) *
        A.applyJet x (frechetScalarJetAt (exponentialProduct s phi f) x) =
      A.conjugatedScalarOperator x s (frechetScalarJetAt phi x)
        (frechetScalarJetAt f x) := by
  calc
    Real.exp (-(s * phi x)) *
        A.applyJet x (frechetScalarJetAt (exponentialProduct s phi f) x) =
      A.applyJet x
        ((frechetScalarJetAt (exponentialProduct s phi f) x).scale
          (Real.exp (-(s * phi x)))) := by
            symm
            exact A.applyJet_scale x _ _
    _ = A.applyJet x (normalizedExponentialJetAt s phi f x) := rfl
    _ = A.applyJet x
        (normalizedConjugatedJet s (frechetScalarJetAt phi x)
          (frechetScalarJetAt f x)) := by
            rw [normalizedExponentialJetAt_eq_normalizedConjugatedJet
              s phi f x hphi hf]
    _ = A.conjugatedScalarOperator x s (frechetScalarJetAt phi x)
        (frechetScalarJetAt f x) := rfl

/-- The scalar principal-symbol limit for actual `C²` functions on the
coordinate space.  Every derivative in the operator expression is produced by
`fderiv`; no formal jet is assumed. -/
theorem scalarPrincipalSymbol_limit_of_contDiff_two {n : ℕ}
    (A : ScalarSecondOrderCoefficients (ScalarCoordinateSpace n) n)
    (x : ScalarCoordinateSpace n) (phi f : ScalarCoordinateSpace n → ℝ)
    (hphi : ContDiff ℝ 2 phi) (hf : ContDiff ℝ 2 f) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 *
        (Real.exp (-(s * phi x)) *
          A.applyJet x (frechetScalarJetAt (exponentialProduct s phi f) x)))
      Filter.atTop
      (nhds (f x * A.principalSymbol x (coordinateFDeriv phi x))) := by
  have hformal := scalarPrincipalSymbol_limit A x
    (frechetScalarJetAt phi x) (frechetScalarJetAt f x)
  have heq :
      (fun s : ℝ => s⁻¹ ^ 2 *
        A.conjugatedScalarOperator x s (frechetScalarJetAt phi x)
          (frechetScalarJetAt f x)) =ᶠ[Filter.atTop]
      (fun s : ℝ => s⁻¹ ^ 2 *
        (Real.exp (-(s * phi x)) *
          A.applyJet x (frechetScalarJetAt (exponentialProduct s phi f) x))) :=
    Filter.Eventually.of_forall fun s => by
      exact congrArg (fun z : ℝ => s⁻¹ ^ 2 * z)
        (normalizedExponentialOperator_eq_conjugated
          A x s phi f hphi hf).symm
  simpa only [frechetScalarJetAt] using hformal.congr' heq

/-- The source form of the actual-function limit: if the coordinate
differential of `phi` at `x` is the covector `xi`, then the limit is
`f(x) * sigma(A)(x, xi)`. -/
theorem scalarPrincipalSymbol_limit_of_contDiff_two_of_differential_eq {n : ℕ}
    (A : ScalarSecondOrderCoefficients (ScalarCoordinateSpace n) n)
    (x : ScalarCoordinateSpace n) (phi f : ScalarCoordinateSpace n → ℝ)
    (xi : Fin n → ℝ) (hphi : ContDiff ℝ 2 phi) (hf : ContDiff ℝ 2 f)
    (hxi : ∀ i, coordinateFDeriv phi x i = xi i) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 *
        (Real.exp (-(s * phi x)) *
          A.applyJet x (frechetScalarJetAt (exponentialProduct s phi f) x)))
      Filter.atTop (nhds (f x * A.principalSymbol x xi)) := by
  have hdiff : coordinateFDeriv phi x = xi := funext hxi
  simpa only [hdiff] using
    scalarPrincipalSymbol_limit_of_contDiff_two A x phi f hphi hf

end

end ParabolicPDE
end Topping

import Topping.ParabolicPDE.ScalarSmooth
import Topping.ParabolicPDE.Vector

/-!
# Smooth local-frame vector jets

This module turns the formal vector second-order jet in `Vector.lean` into
actual coordinate-space data.  The base is a finite-dimensional coordinate
space and the fibre is an arbitrary normed inner-product space; no manifold
atlas or global section space is assumed.
-/

namespace Topping
namespace ParabolicPDE

noncomputable section

open scoped BigOperators

variable {n : ℕ} {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The coordinate evaluation of the Frechet derivative of a vector-valued
section. -/
def vectorCoordinateFDeriv
    (u : ScalarCoordinateSpace n → V)
    (x : ScalarCoordinateSpace n) (i : Fin n) : V :=
  fderiv ℝ u x (scalarCoordinateVector i)

/-- The iterated coordinate derivative of a vector-valued section. -/
def vectorCoordinateSecondFDeriv
    (u : ScalarCoordinateSpace n → V)
    (x : ScalarCoordinateSpace n) (i k : Fin n) : V :=
  vectorCoordinateFDeriv (fun y => vectorCoordinateFDeriv u y k) x i

/-- The actual local-frame second-order jet of a coordinate-space section. -/
def frechetVectorJetAt
    (u : ScalarCoordinateSpace n → V)
    (x : ScalarCoordinateSpace n) :
    VectorSecondOrderJet (Fin n) V where
  value := u x
  first := vectorCoordinateFDeriv u x
  second := vectorCoordinateSecondFDeriv u x

namespace VectorSecondOrderJet

theorem ext_fields
    {j₁ j₂ : VectorSecondOrderJet (Fin n) V}
    (hvalue : j₁.value = j₂.value)
    (hfirst : j₁.first = j₂.first)
    (hsecond : j₁.second = j₂.second) : j₁ = j₂ := by
  cases j₁ with
  | mk v₁ f₁ s₁ =>
    cases j₂ with
    | mk v₂ f₂ s₂ =>
      simp_all

end VectorSecondOrderJet

/-- Multiplication by an exponential scalar phase, as used for a local-frame
test section. -/
def vectorExponentialProduct (s : ℝ)
    (phi : ScalarCoordinateSpace n → ℝ)
    (u : ScalarCoordinateSpace n → V) :
    ScalarCoordinateSpace n → V :=
  fun y => Real.exp (s * phi y) • u y

theorem vectorCoordinateFDeriv_smul
    {c : ScalarCoordinateSpace n → ℝ}
    {u : ScalarCoordinateSpace n → V}
    {x : ScalarCoordinateSpace n} (i : Fin n)
    (hc : DifferentiableAt ℝ c x)
    (hu : DifferentiableAt ℝ u x) :
    vectorCoordinateFDeriv (fun y => c y • u y) x i =
      c x • vectorCoordinateFDeriv u x i +
        vectorCoordinateFDeriv c x i • u x := by
  change (fderiv ℝ (c • u) x) (scalarCoordinateVector i) = _
  have h := congrArg
    (fun L : (ScalarCoordinateSpace n) →L[ℝ] V =>
      L (scalarCoordinateVector i)) (fderiv_smul hc hu)
  simpa only [vectorCoordinateFDeriv, Pi.smul_apply,
    add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul] using h

theorem vectorCoordinateFDeriv_add
    {u v : ScalarCoordinateSpace n → V}
    {x : ScalarCoordinateSpace n} (i : Fin n)
    (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x) :
    vectorCoordinateFDeriv (fun y => u y + v y) x i =
      vectorCoordinateFDeriv u x i + vectorCoordinateFDeriv v x i := by
  unfold vectorCoordinateFDeriv
  have h := congrArg
    (fun L : (ScalarCoordinateSpace n) →L[ℝ] V =>
      L (scalarCoordinateVector i)) (fderiv_fun_add hu hv)
  simpa only [add_apply] using h

theorem vectorCoordinateFDeriv_differentiable_of_contDiff_two
    {u : ScalarCoordinateSpace n → V}
    (hu : ContDiff ℝ 2 u) (k : Fin n) :
    Differentiable ℝ (fun y => vectorCoordinateFDeriv u y k) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have he : ContDiff ℝ 1
      (fun _ : ScalarCoordinateSpace n => scalarCoordinateVector k) :=
    contDiff_const
  exact (hfd.clm_apply he).differentiable (by norm_num)

theorem vectorCoordinateSecondFDeriv_smul
    {c : ScalarCoordinateSpace n → ℝ}
    {u : ScalarCoordinateSpace n → V}
    {x : ScalarCoordinateSpace n} (i k : Fin n)
    (hc : Differentiable ℝ c) (hu : Differentiable ℝ u)
    (hc2 : DifferentiableAt ℝ
      (fun y => vectorCoordinateFDeriv c y k) x)
    (hu2 : DifferentiableAt ℝ
      (fun y => vectorCoordinateFDeriv u y k) x) :
    vectorCoordinateSecondFDeriv (fun y => c y • u y) x i k =
      c x • vectorCoordinateSecondFDeriv u x i k +
        vectorCoordinateFDeriv c x i • vectorCoordinateFDeriv u x k +
        vectorCoordinateFDeriv c x k • vectorCoordinateFDeriv u x i +
        vectorCoordinateSecondFDeriv c x i k • u x := by
  unfold vectorCoordinateSecondFDeriv
  rw [show (fun y => vectorCoordinateFDeriv
      (fun z => c z • u z) y k) =
      (fun y => c y • vectorCoordinateFDeriv u y k +
        vectorCoordinateFDeriv c y k • u y) by
    funext y
    exact vectorCoordinateFDeriv_smul k (hc y) (hu y)]
  have h₁ : DifferentiableAt ℝ
      (fun y => c y • vectorCoordinateFDeriv u y k) x :=
    (hc x).smul hu2
  have h₂ : DifferentiableAt ℝ
      (fun y => vectorCoordinateFDeriv c y k • u y) x :=
    hc2.smul (hu x)
  rw [vectorCoordinateFDeriv_add i h₁ h₂]
  have h₁' := vectorCoordinateFDeriv_smul (n := n) (V := V) i
    (hc x) hu2
  have h₂' := vectorCoordinateFDeriv_smul (n := n) (V := V) i
    hc2 (hu x)
  rw [h₁', h₂']
  abel

theorem frechetVectorJetAt_smul
    {c : ScalarCoordinateSpace n → ℝ}
    {u : ScalarCoordinateSpace n → V}
    {x : ScalarCoordinateSpace n}
    (hc : Differentiable ℝ c) (hu : Differentiable ℝ u)
    (hc2 : ∀ k, DifferentiableAt ℝ
      (fun y => vectorCoordinateFDeriv c y k) x)
    (hu2 : ∀ k, DifferentiableAt ℝ
      (fun y => vectorCoordinateFDeriv u y k) x) :
    frechetVectorJetAt (fun y => c y • u y) x =
      { value := c x • u x
        first := fun i =>
          c x • vectorCoordinateFDeriv u x i +
            vectorCoordinateFDeriv c x i • u x
        second := fun i k =>
          c x • vectorCoordinateSecondFDeriv u x i k +
            vectorCoordinateFDeriv c x i • vectorCoordinateFDeriv u x k +
            vectorCoordinateFDeriv c x k • vectorCoordinateFDeriv u x i +
            vectorCoordinateSecondFDeriv c x i k • u x } := by
  apply VectorSecondOrderJet.ext_fields
  · rfl
  · funext i
    exact vectorCoordinateFDeriv_smul i (hc x) (hu x)
  · funext i k
    exact vectorCoordinateSecondFDeriv_smul i k hc hu (hc2 k) (hu2 k)

end
end ParabolicPDE
end Topping

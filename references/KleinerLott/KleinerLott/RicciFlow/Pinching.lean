import Mathlib

/-!
# Curvature pinching

This file records the pinching functions and curvature-operator lower bounds
used in the Hamilton-Ivey estimate.
-/

namespace KleinerLott

/-- A smooth positive pinching function whose relative growth tends to zero. -/
def IsPinchingFunction (Phi : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ Phi ∧
    (∀ s, 0 < Phi s) ∧
    Monotone Phi ∧
    AntitoneOn (fun s => Phi s / s) (Set.Ioi 0) ∧
    Filter.Tendsto (fun s => Phi s / s) Filter.atTop (nhds 0)

/-- The curvature-operator inequality defining pinching by `Phi`. -/
def IsCurvaturePinchedBy {P : Type*} (CurvatureFiber : P → Type*)
    [∀ p, NormedAddCommGroup (CurvatureFiber p)]
    [∀ p, InnerProductSpace ℝ (CurvatureFiber p)]
    (Phi : ℝ → ℝ) (scalarCurvature : P → ℝ)
    (curvatureOperator : (p : P) → QuadraticForm ℝ (CurvatureFiber p)) : Prop :=
  IsPinchingFunction Phi ∧
    ∀ p v, -(Phi (scalarCurvature p)) * ‖v‖ ^ 2 ≤ curvatureOperator p v

/-- The time-`t` Hamilton-Ivey pinching condition in dimension three. -/
def IsHamiltonIveyPinched {P : Type*} (t : ℝ) (scalarCurvature : P → ℝ)
    (curvatureEigenvalues : P → Fin 3 → ℝ) : Prop :=
  0 ≤ t ∧
    ∀ p,
      let lambda1 := curvatureEigenvalues p 0
      let lambda2 := curvatureEigenvalues p 1
      let lambda3 := curvatureEigenvalues p 2
      let X := -lambda1
      lambda1 ≤ lambda2 ∧
        lambda2 ≤ lambda3 ∧
        (0 ≤ lambda1 ∨
          (lambda1 < 0 ∧
            t * scalarCurvature p ≥
              t * X * (Real.log (t * X) + Real.log ((1 + t) / t) - 3)))

end KleinerLott

import MorganTianLib.Ch03.RicciFlow.ShiGeometricLevels
import MorganTianLib.Ch03.RicciFlow.ShiEstimates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Morgan--Tian Ch. 3 - the zeroth Shi evolution interface

The analytic Shi tower stores the squared norms of the iterated covariant
derivatives of the all-lowered Riemann tensor.  At its first two levels these
are exactly the usual curvature norm square and the norm square of one
covariant derivative.  This file records those definitional bridges and the
resulting `k = 0` tower adapter.

The adapter deliberately keeps the curvature evolution inequality as an
explicit input.  It supplies the missing interface between a curvature-norm
evolution producer and the finite Shi cancellation, without asserting the
geometric evolution calculation itself.
-/

open Set
open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Canonical curvature norms -/

/-- **Math.** The squared norm of the all-lowered Riemann tensor, represented
by the zeroth level of the intrinsic Shi tower. -/
def riemannNormSqAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  riemannCovDerivNormSqAt g 0 p

/-- **Math.** The norm of the all-lowered Riemann tensor, represented by the
zeroth level of the intrinsic Shi tower. -/
def riemannNormAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  riemannCovDerivNormAt g 0 p

/-- **Math.** The squared norm of one covariant derivative of the Riemann
tensor, represented by the first level of the intrinsic Shi tower. -/
def gradRiemannNormSqAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  riemannCovDerivNormSqAt g 1 p

@[simp] theorem riemannNormSqAt_eq_level_zero
    (g : RiemannianMetric I M) (p : M) :
    riemannNormSqAt g p = riemannCovDerivNormSqAt g 0 p := rfl

@[simp] theorem riemannNormAt_eq_level_zero
    (g : RiemannianMetric I M) (p : M) :
    riemannNormAt g p = riemannCovDerivNormAt g 0 p := rfl

@[simp] theorem gradRiemannNormSqAt_eq_level_one
    (g : RiemannianMetric I M) (p : M) :
    gradRiemannNormSqAt g p = riemannCovDerivNormSqAt g 1 p := rfl

/-- **Math.** The zeroth-level squared norm is the pointwise finite tensor
energy of `riemannTensorField`. -/
theorem riemannNormSqAt_eq_covTensorNormSqAt
    (g : RiemannianMetric I M) (p : M) :
    riemannNormSqAt g p = covTensorNormSqAt g (riemannTensorField g) p := by
  rfl

/-- **Math.** The zeroth-level norm is the pointwise finite tensor norm of
`riemannTensorField`. -/
theorem riemannNormAt_eq_covTensorNormAt
    (g : RiemannianMetric I M) (p : M) :
    riemannNormAt g p = covTensorNormAt g (riemannTensorField g) p := by
  rfl

/-- **Math.** The first Shi level is the pointwise finite tensor energy of one
covariant derivative of `riemannTensorField`. -/
theorem gradRiemannNormSqAt_eq_covTensorNormSqAt
    (g : RiemannianMetric I M) (p : M) :
    gradRiemannNormSqAt g p =
      covTensorNormSqAt g
        (covTensorDeriv g.leviCivitaConnection (riemannTensorField g)) p := by
  rfl

/-! ## Elementary norm facts -/

/-- **Math.** The zeroth-level curvature norm is nonnegative. -/
theorem riemannNormAt_nonneg (g : RiemannianMetric I M) (p : M) :
    0 ≤ riemannNormAt g p := by
  exact riemannCovDerivNormAt_nonneg g 0 p

/-- **Math.** Squaring the zeroth-level norm recovers its stored Shi energy. -/
theorem riemannNormAt_sq (g : RiemannianMetric I M) (p : M) :
    riemannNormAt g p ^ 2 = riemannNormSqAt g p := by
  simpa [riemannNormAt, riemannNormSqAt] using
    (riemannCovDerivNormAt_sq g 0 p)

/-! ## The level-zero tower adapter -/

/-- **Math.** A curvature-norm-square evolution inequality is precisely the
zeroth member of the intrinsic Shi tower, after the first level is identified
with `gradRiemannNormSqAt`.  The other tower levels are absent because the
order parameter is `0`. -/
theorem shiTowerInequalitiesOn_zero_of_riemannNormSqEvolution
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    {lap0 : M → ℝ → ℝ} {kappa rho : ℝ}
    (h : ∀ t ∈ J, ∀ p : M,
      derivWithin (fun s => riemannNormSqAt (g s) p) J t ≤
        lap0 p t - 2 * gradRiemannNormSqAt (g t) p
          + kappa * riemannNormSqAt (g t) p + rho) :
    ShiTowerInequalitiesOn
      (fun j p t => riemannCovDerivNormSqAt (g t) j p)
      (fun j p t => if j = 0 then lap0 p t else 0) kappa rho 0 J := by
  intro j hj t ht p
  have hj' : j < 1 := by simpa using hj
  have hj0 : j = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hj')
  subst j
  simpa [riemannNormSqAt, gradRiemannNormSqAt] using h t ht p

/-- **Math.** The same `k = 0` adapter accepts the usual notation in which
the evolving quantity is written as `|Rm| ^ 2`. -/
theorem shiTowerInequalitiesOn_zero_of_riemannNormEvolution
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    {lap0 : M → ℝ → ℝ} {kappa rho : ℝ}
    (h : ∀ t ∈ J, ∀ p : M,
      derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
        lap0 p t - 2 * gradRiemannNormSqAt (g t) p
          + kappa * riemannNormSqAt (g t) p + rho) :
    ShiTowerInequalitiesOn
      (fun j p t => riemannCovDerivNormSqAt (g t) j p)
      (fun j p t => if j = 0 then lap0 p t else 0) kappa rho 0 J := by
  apply shiTowerInequalitiesOn_zero_of_riemannNormSqEvolution
  intro t ht p
  simpa only [riemannNormAt_sq] using h t ht p

/-! ## Replacing the cubic reaction by a uniform constant -/

/-- **Math.** A nonnegative zeroth-level norm bounded by `m` has cubic power
bounded by `m ^ 3`. -/
theorem riemannNormAt_cube_le_of_le
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {m : ℝ}
    (hm : 0 ≤ m)
    (hbound : ∀ t ∈ J, ∀ p : M, riemannNormAt (g t) p ≤ m) :
    ∀ t ∈ J, ∀ p : M, riemannNormAt (g t) p ^ 3 ≤ m ^ 3 := by
  intro t ht p
  have ha := hbound t ht p
  have ha0 : 0 ≤ riemannNormAt (g t) p := riemannNormAt_nonneg (g t) p
  have hsq : riemannNormAt (g t) p ^ 2 ≤ m ^ 2 := by
    nlinarith
  calc
    riemannNormAt (g t) p ^ 3 =
        riemannNormAt (g t) p ^ 2 * riemannNormAt (g t) p := by ring
    _ ≤ m ^ 2 * riemannNormAt (g t) p :=
      mul_le_mul_of_nonneg_right hsq ha0
    _ ≤ m ^ 2 * m :=
      mul_le_mul_of_nonneg_left ha (sq_nonneg m)
    _ = m ^ 3 := by ring

/-- **Math.** A cubic curvature-norm evolution inequality with a uniform
zeroth-level bound supplies the constant-reaction zeroth Shi inequality.  The
only estimate added here is the monotonicity of the cubic reaction; the
geometric evolution inequality remains the explicit input `h`. -/
theorem shiTowerInequalitiesOn_zero_of_cubic_riemannNormEvolution
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    {lap0 : M → ℝ → ℝ} {kappa c m : ℝ}
    (hc : 0 ≤ c) (hm : 0 ≤ m)
    (hbound : ∀ t ∈ J, ∀ p : M, riemannNormAt (g t) p ≤ m)
    (h : ∀ t ∈ J, ∀ p : M,
      derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
        lap0 p t - 2 * gradRiemannNormSqAt (g t) p
          + kappa * riemannNormSqAt (g t) p
          + c * riemannNormAt (g t) p ^ 3) :
    ShiTowerInequalitiesOn
      (fun j p t => riemannCovDerivNormSqAt (g t) j p)
      (fun j p t => if j = 0 then lap0 p t else 0) kappa (c * m ^ 3) 0 J := by
  apply shiTowerInequalitiesOn_zero_of_riemannNormSqEvolution
  intro t ht p
  have hcube := riemannNormAt_cube_le_of_le hm hbound t ht p
  have hcm := mul_le_mul_of_nonneg_left hcube hc
  have hbase := h t ht p
  have hsq : derivWithin (fun s => riemannNormSqAt (g s) p) J t ≤
      lap0 p t - 2 * gradRiemannNormSqAt (g t) p
        + kappa * riemannNormSqAt (g t) p
        + c * riemannNormAt (g t) p ^ 3 := by
    simpa only [riemannNormAt_sq] using hbase
  calc
    derivWithin (fun s => riemannNormSqAt (g s) p) J t ≤
        lap0 p t - 2 * gradRiemannNormSqAt (g t) p
          + kappa * riemannNormSqAt (g t) p
          + c * riemannNormAt (g t) p ^ 3 := hsq
    _ ≤ lap0 p t - 2 * gradRiemannNormSqAt (g t) p
          + kappa * riemannNormSqAt (g t) p + c * m ^ 3 := by
      linarith

end MorganTianLib

end

#print axioms MorganTianLib.riemannNormSqAt
#print axioms MorganTianLib.riemannNormAt
#print axioms MorganTianLib.gradRiemannNormSqAt
#print axioms MorganTianLib.shiTowerInequalitiesOn_zero_of_riemannNormSqEvolution
#print axioms MorganTianLib.shiTowerInequalitiesOn_zero_of_riemannNormEvolution
#print axioms MorganTianLib.riemannNormAt_cube_le_of_le
#print axioms MorganTianLib.shiTowerInequalitiesOn_zero_of_cubic_riemannNormEvolution

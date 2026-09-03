import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian

/-!
# Morgan--Tian Ch. 3 - geometric derivative levels

This file packages the iterated covariant derivatives used in Shi estimates.
The tower is defined for an arbitrary covariant tensor field, so the curvature
case is a specialization rather than a separate formal surrogate.  Pointwise
energies are finite sums of component squares in the standard orthonormal
basis of the tangent fibre.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-! ## The covariant-derivative tower -/

/-- **Math.** The `n`-fold covariant derivative of a covariant tensor field.
The derivative direction is inserted in the first slot at every step, matching
`covTensorDeriv`. -/
def iteratedCovTensorDeriv (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) : (n : ℕ) → CovTensorField I M (k + n)
  | 0 => A
  | n + 1 => covTensorDeriv nabla (iteratedCovTensorDeriv nabla A n)

@[simp] theorem iteratedCovTensorDeriv_zero (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) :
    iteratedCovTensorDeriv nabla A 0 = A := rfl

@[simp] theorem iteratedCovTensorDeriv_succ (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) (n : ℕ) :
    iteratedCovTensorDeriv nabla A (n + 1) =
      covTensorDeriv nabla (iteratedCovTensorDeriv nabla A n) := rfl

/-- **Math.** The component formula for one step of the tower. -/
theorem iteratedCovTensorDeriv_succ_apply
    (nabla : AffineConnection I M) {k n : ℕ}
    (A : CovTensorField I M k) (Y : Fin (k + (n + 1)) → SmoothVectorField I M)
    (p : M) :
    iteratedCovTensorDeriv nabla A (n + 1) Y p =
      covTensorDeriv nabla (iteratedCovTensorDeriv nabla A n) Y p := by
  rfl

/-- **Math.** Evaluating a new derivative level on a cons-list of smooth
vector fields exposes `covTensorDerivAlong` directly. -/
theorem iteratedCovTensorDeriv_succ_cons
    (nabla : AffineConnection I M) {k n : ℕ}
    (A : CovTensorField I M k) (X : SmoothVectorField I M)
    (Y : Fin (k + n) → SmoothVectorField I M) (p : M) :
      iteratedCovTensorDeriv nabla A (n + 1) (Fin.cons X Y) p =
      covTensorDerivAlong nabla X (iteratedCovTensorDeriv nabla A n) Y p := by
  rfl

/-! ## Pointwise components and square energies -/

section Pointwise

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The component of a covariant tensor obtained by inserting the
standard orthonormal basis at `p` in every slot. -/
def covTensorComponentAt (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M)
    (s : Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  A (fun i => extendVector p
    (stdOrthonormalBasis ℝ (TangentSpace I p) (s i))) p

/-- **Math.** The pointwise squared norm of a covariant tensor field, computed
as the finite sum of squares of its components in the standard orthonormal
basis of the tangent fibre. -/
def covTensorNormSqAt (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ s : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
    (covTensorComponentAt g A p s) ^ 2

/-- **Math.** The pointwise norm associated with `covTensorNormSqAt`. -/
def covTensorNormAt (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) : ℝ :=
  Real.sqrt (covTensorNormSqAt g A p)

theorem covTensorNormSqAt_nonneg (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    0 ≤ covTensorNormSqAt g A p := by
  classical
  unfold covTensorNormSqAt
  exact Finset.sum_nonneg (fun s _ => sq_nonneg _)

theorem covTensorNormAt_sq (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    (covTensorNormAt g A p) ^ 2 = covTensorNormSqAt g A p := by
  unfold covTensorNormAt
  exact Real.sq_sqrt (covTensorNormSqAt_nonneg g A p)

theorem covTensorNormAt_nonneg (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    0 ≤ covTensorNormAt g A p := by
  unfold covTensorNormAt
  exact Real.sqrt_nonneg _

theorem covTensorNormSqAt_eq_zero_iff (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    covTensorNormSqAt g A p = 0 ↔
      ∀ s : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorComponentAt g A p s = 0 := by
  classical
  unfold covTensorNormSqAt
  constructor
  · intro h s
    have hs := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s _ => sq_nonneg (covTensorComponentAt g A p s))).1 h s
      (Finset.mem_univ s)
    exact (sq_eq_zero_iff).1 hs
  · intro h
    apply Finset.sum_eq_zero
    intro s hs
    exact (sq_eq_zero_iff).2 (h s)

theorem covTensorNormAt_eq_zero_iff (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    covTensorNormAt g A p = 0 ↔
      ∀ s : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
        covTensorComponentAt g A p s = 0 := by
  classical
  change Real.sqrt (covTensorNormSqAt g A p) = 0 ↔ _
  rw [Real.sqrt_eq_zero (covTensorNormSqAt_nonneg g A p)]
  exact covTensorNormSqAt_eq_zero_iff g A p

/-! ## Bridges for the zero level and for curvature -/

theorem covTensorNormSqAt_iterated_zero (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    covTensorNormSqAt g (iteratedCovTensorDeriv nabla A 0) p =
      covTensorNormSqAt g A p := by
  rfl

theorem covTensorNormAt_iterated_zero (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    covTensorNormAt g (iteratedCovTensorDeriv nabla A 0) p =
      covTensorNormAt g A p := by
  rfl

/-! ## Curvature levels -/

section Curvature

variable [CompleteSpace E] [NeZero (Module.finrank ℝ E)]

/-- **Math.** The curvature derivative tower, starting with the Riemann tensor. -/
def riemannCovDerivTower (g : RiemannianMetric I M) (n : ℕ) :
    CovTensorField I M (4 + n) :=
  iteratedCovTensorDeriv g.leviCivitaConnection (riemannTensorField g) n

@[simp] theorem riemannCovDerivTower_zero (g : RiemannianMetric I M) :
    riemannCovDerivTower g 0 = riemannTensorField g := rfl

/-- **Math.** The squared pointwise size of the `n`-th Riemann tensor level. -/
def riemannCovDerivNormSqAt (g : RiemannianMetric I M) (n : ℕ) (p : M) : ℝ :=
  covTensorNormSqAt g (riemannCovDerivTower g n) p

/-- **Math.** The pointwise size of the `n`-th Riemann tensor level. -/
def riemannCovDerivNormAt (g : RiemannianMetric I M) (n : ℕ) (p : M) : ℝ :=
  covTensorNormAt g (riemannCovDerivTower g n) p

theorem riemannCovDerivNormSqAt_nonneg (g : RiemannianMetric I M)
    (n : ℕ) (p : M) : 0 ≤ riemannCovDerivNormSqAt g n p := by
  exact covTensorNormSqAt_nonneg g (riemannCovDerivTower g n) p

theorem riemannCovDerivNormAt_sq (g : RiemannianMetric I M)
    (n : ℕ) (p : M) : (riemannCovDerivNormAt g n p) ^ 2 =
      riemannCovDerivNormSqAt g n p := by
  exact covTensorNormAt_sq g (riemannCovDerivTower g n) p

theorem riemannCovDerivNormAt_nonneg (g : RiemannianMetric I M)
    (n : ℕ) (p : M) : 0 ≤ riemannCovDerivNormAt g n p := by
  exact covTensorNormAt_nonneg g (riemannCovDerivTower g n) p

@[simp] theorem riemannCovDerivNormSqAt_zero (g : RiemannianMetric I M) (p : M) :
    riemannCovDerivNormSqAt g 0 p =
      covTensorNormSqAt g (riemannTensorField g) p := rfl

@[simp] theorem riemannCovDerivNormAt_zero (g : RiemannianMetric I M) (p : M) :
    riemannCovDerivNormAt g 0 p =
      covTensorNormAt g (riemannTensorField g) p := rfl

end Curvature

end Pointwise

end MorganTianLib

end

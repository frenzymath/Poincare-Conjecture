import MorganTianLib.Ch02.Laplacian
import Topping.Riemannian.Curvature

/-!
# Covariant tensor fields and the operators of Topping's notation section

Topping's Chapter 2 states every variation and evolution formula in a fixed
vocabulary of operators acting on covariant tensor fields: the second covariant
derivative `∇²_{X,Y} = ∇_X∇_Y - ∇_{∇_XY}`, the connection (rough) Laplacian
`Δ A = tr₁₂ ∇²A`, and the divergence `δ(T) = -tr₁₂ ∇T`. This module fixes the
representation of a covariant tensor field and builds those operators.

A covariant `k`-tensor field is represented by its action on `k`-tuples of
smooth vector fields, `CovTensorField I M k = (Fin k → SmoothVectorField I M) →
M → ℝ`. This is the level at which the Leibniz corrections defining `∇` make
sense. Traces are taken against the pointwise metric: the first two slots are
fed a `g`-orthonormal basis of `T_pM`, extended to global fields by
`MorganTianLib.extendVector`.

Following Topping's convention, the derivative slot of `∇A` comes **first**:
`∇_X A = ∇A(X, …)`, which is what makes `tr₁₂` in `Δ` and `δ` trace the
derivative slot against the first tensor slot.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A covariant `k`-tensor field, represented by its action on
`k`-tuples of smooth vector fields. -/
def CovTensorField (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] (k : ℕ) : Type _ :=
  (Fin k → SmoothVectorField I M) → M → ℝ

/-! ### Covariant differentiation -/

/-- **Math.** The covariant derivative `∇_X A` of a covariant `k`-tensor field
along a vector field `X`: the tensor product rule
`∇_X(A ⊗ B) = (∇_XA) ⊗ B + A ⊗ (∇_XB)` forces the Leibniz corrections
`(∇_XA)(Y₁,…,Y_k) = X(A(Y₁,…,Y_k)) - Σᵢ A(…, ∇_XYᵢ, …)`. -/
def covDerivAlong (nabla : AffineConnection I M) (X : SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k) : CovTensorField I M k :=
  fun Y p =>
    X.dir (A Y) p - ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p

/-- **Math.** The full covariant derivative `∇A` of a covariant `k`-tensor
field, a covariant `(k+1)`-tensor field whose **first** slot is the direction of
differentiation: `∇A(X, …) = ∇_XA(…)`, Topping's displayed-slot convention. -/
def covDeriv (nabla : AffineConnection I M) {k : ℕ} (A : CovTensorField I M k) :
    CovTensorField I M (k + 1) :=
  fun Y p => covDerivAlong nabla (Y 0) A (fun i => Y i.succ) p

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The defining property of the displayed-slot convention:
`∇A(X, Y₁,…,Y_k) = (∇_XA)(Y₁,…,Y_k)`. -/
theorem covDeriv_cons (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (X : SmoothVectorField I M)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    covDeriv nabla A (Fin.cons X Y) p = covDerivAlong nabla X A Y p := by
  simp only [covDeriv, Fin.cons_zero, Fin.cons_succ]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Component form of the covariant derivative. -/
theorem covDerivAlong_apply (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    covDerivAlong nabla X A Y p =
      X.dir (A Y) p - ∑ i, A (Function.update Y i (nabla.cov X (Y i))) p :=
  rfl

/-! ### The second covariant derivative -/

/-- **Math.** Topping's second covariant derivative
`∇²_{X,Y} := ∇_X∇_Y - ∇_{∇_XY}`, applied to a covariant `k`-tensor field. The
correction term is what makes it tensorial in `X` and `Y`. -/
def secondCovDerivAlong (nabla : AffineConnection I M)
    (X Y : SmoothVectorField I M) {k : ℕ} (A : CovTensorField I M k) :
    CovTensorField I M k :=
  fun Z p =>
    covDerivAlong nabla X (covDerivAlong nabla Y A) Z p
      - covDerivAlong nabla (nabla.cov X Y) A Z p

/-- **Math.** The full second covariant derivative `∇²A`, a covariant
`(k+2)`-tensor field with the two differentiation directions in the first two
slots. -/
def secondCovDeriv (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) : CovTensorField I M (k + 2) :=
  covDeriv nabla (covDeriv nabla A)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** `∇²A` is the iterated covariant derivative: unfolding its first
two slots gives Topping's `∇²_{X,Y} = ∇_X∇_Y - ∇_{∇_XY}`. -/
theorem secondCovDeriv_cons (nabla : AffineConnection I M) {k : ℕ}
    (A : CovTensorField I M k) (X Y : SmoothVectorField I M)
    (Z : Fin k → SmoothVectorField I M) (p : M) :
    secondCovDeriv nabla A (Fin.cons X (Fin.cons Y Z)) p =
      secondCovDerivAlong nabla X Y A Z p := by
  rw [secondCovDeriv, covDeriv_cons, covDerivAlong_apply, secondCovDerivAlong,
    covDerivAlong_apply, covDerivAlong_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have hupd : ∀ i : Fin k,
      Function.update (Fin.cons Y Z : Fin (k + 1) → SmoothVectorField I M)
          i.succ (nabla.cov X (Z i))
        = Fin.cons Y (Function.update Z i (nabla.cov X (Z i))) := by
    intro i
    funext j
    refine Fin.cases ?_ ?_ j
    · rw [Function.update_of_ne (Fin.succ_ne_zero i).symm]
      simp
    · intro j
      by_cases hij : j = i
      · subst hij; simp
      · rw [Function.update_of_ne (fun h => hij (Fin.succ_injective _ h)),
          Fin.cons_succ, Fin.cons_succ, Function.update_of_ne hij]
  have hzero : Function.update (Fin.cons Y Z : Fin (k + 1) → SmoothVectorField I M)
      0 (nabla.cov X Y) = Fin.cons (nabla.cov X Y) Z := by
    funext j
    refine Fin.cases ?_ ?_ j
    · simp
    · intro j
      rw [Function.update_of_ne (Fin.succ_ne_zero j), Fin.cons_succ, Fin.cons_succ]
  have hfun : covDeriv nabla A (Fin.cons Y Z) = covDerivAlong nabla Y A Z :=
    funext fun q => covDeriv_cons nabla A Y Z q
  rw [hzero]
  simp only [hupd, covDeriv_cons, hfun, covDerivAlong_apply]
  ring

/-! ### Metric traces of the first two slots

Both `Δ = tr₁₂∇²` and `δ = -tr₁₂∇` contract the first two slots of a covariant
tensor field against the metric. The trace is computed by feeding a `g`-orthonormal
basis of `T_pM` into those two slots, using `MorganTianLib.extendVector` to turn
tangent vectors into global fields. -/

/-- **Math.** The metric trace `tr₁₂ B` of the first two slots of a covariant
`(k+2)`-tensor field, as a covariant `k`-tensor field:
`(tr₁₂B)(Y₁,…,Y_k)(p) = Σᵢ B(eᵢ, eᵢ, Y₁,…,Y_k)(p)` for a `g_p`-orthonormal basis
`{eᵢ}` of `T_pM`. -/
def traceFirstTwo (g : RiemannianMetric I M) {k : ℕ}
    (B : CovTensorField I M (k + 2)) : CovTensorField I M k :=
  fun Y p =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, B (Fin.cons (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (Fin.cons (MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y)) p

/-- **Math.** Topping's connection (rough) Laplacian of a covariant tensor
field, `Δ A := tr₁₂ ∇²A`. -/
def roughLaplacian (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (A : CovTensorField I M k) : CovTensorField I M k :=
  traceFirstTwo g (secondCovDeriv nabla A)

omit [CompleteSpace E] in
/-- **Math.** The rough Laplacian is the `g`-trace of `∇²` over an orthonormal
basis: `ΔA(Y) = Σᵢ ∇²_{eᵢ,eᵢ}A(Y)`. -/
theorem roughLaplacian_apply (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {k : ℕ} (A : CovTensorField I M k)
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    roughLaplacian g nabla A Y p =
      ∑ i, secondCovDerivAlong nabla
        (MorganTianLib.extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        (MorganTianLib.extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        A Y p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [roughLaplacian, traceFirstTwo, secondCovDeriv_cons]

/-- **Math.** Topping's divergence of a covariant tensor field of rank at least
one, `δ(T) := -tr₁₂ ∇T`. -/
def divergence (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    {k : ℕ} (T : CovTensorField I M (k + 1)) : CovTensorField I M k :=
  fun Y p => -traceFirstTwo g (covDeriv nabla T) Y p

omit [CompleteSpace E] in
/-- **Math.** The divergence is minus the `g`-trace of `∇T` over the derivative
slot and the first tensor slot: `δT(Y) = -Σᵢ (∇_{eᵢ}T)(eᵢ, Y)`. -/
theorem divergence_apply (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {k : ℕ} (T : CovTensorField I M (k + 1))
    (Y : Fin k → SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    divergence g nabla T Y p =
      -∑ i, covDerivAlong nabla
        (MorganTianLib.extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
        T (Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [divergence, traceFirstTwo, covDeriv_cons]

/-! ### The gravitation tensor -/

/-- **Math.** The metric, viewed as a covariant `2`-tensor field. -/
def metricTensorField (g : RiemannianMetric I M) : CovTensorField I M 2 :=
  fun Y p => g.metricInner p (Y 0 p) (Y 1 p)

/-- **Math.** The metric trace `tr T` of a covariant `2`-tensor field, a scalar
function on `M`. -/
def trace₂ (g : RiemannianMetric I M) (T : CovTensorField I M 2) : M → ℝ :=
  fun p => traceFirstTwo g (k := 0) T (fun i => i.elim0) p

/-- **Math.** Topping's gravitation tensor `G(T) := T - ½(tr T)g` of a
symmetric `2`-tensor field. -/
def gravitationTensor (g : RiemannianMetric I M) (T : CovTensorField I M 2) :
    CovTensorField I M 2 :=
  fun Y p => T Y p - (1 / 2 : ℝ) * trace₂ g T p * metricTensorField g Y p

omit [CompleteSpace E] in
/-- **Math.** Component form of the gravitation tensor. -/
theorem gravitationTensor_apply (g : RiemannianMetric I M)
    (T : CovTensorField I M 2) (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    gravitationTensor g T Y p =
      T Y p - (1 / 2 : ℝ) * trace₂ g T p * g.metricInner p (Y 0 p) (Y 1 p) :=
  rfl

omit [CompleteSpace E] in
/-- **Math.** The gravitation tensor of the metric itself is
`(1 - n/2)g`, where `n = dim M`. -/
theorem gravitationTensor_metricTensorField (g : RiemannianMetric I M)
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    gravitationTensor g (metricTensorField g) Y p =
      (1 - (Module.finrank ℝ E : ℝ) / 2) * g.metricInner p (Y 0 p) (Y 1 p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have htr : trace₂ g (metricTensorField g) p = (Module.finrank ℝ E : ℝ) := by
    have hone : ∀ i, g.metricInner p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) = 1 := by
      intro i
      have h : inner ℝ (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) = 1 := by
        have := orthonormal_iff_ite.mp
          (stdOrthonormalBasis ℝ (TangentSpace I p)).orthonormal i i
        rwa [if_pos rfl] at this
      exact h
    simp only [trace₂, traceFirstTwo, metricTensorField, Fin.cons_zero,
      Fin.cons_one, MorganTianLib.extendVector_apply]
    rw [Finset.sum_congr rfl fun i _ => hone i, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    simp only [nsmul_eq_mul, mul_one, Nat.cast_inj]
    rfl
  rw [gravitationTensor_apply, htr, metricTensorField]
  ring

end Topping

end

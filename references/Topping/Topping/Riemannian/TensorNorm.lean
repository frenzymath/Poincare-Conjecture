import Topping.Riemannian.CovariantTensor

/-!
# The pointwise norm of a covariant tensor field

The full metric contraction of a covariant `k`-tensor field with itself,
`|A|^2 = g^{i_1j_1}\cdots g^{i_kj_k}A_{i_1\ldots i_k}A_{j_1\ldots j_k}`, which in
an orthonormal basis is the plain sum of squares of the components. This is the
`|\Rm|^2` and `|\Ric|^2` appearing throughout the Ricci-flow estimates.

The definition sums over `k`-tuples of basis indices, `Fin k → ι`, which is what
makes it uniform in the rank: for `k = 4` it is
`Σ_{ijkl} \Rm(e_i,e_j,e_k,e_l)^2`.
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

/-- **Math.** The square norm `|A|^2` of a covariant `k`-tensor field at `p`: the
full metric contraction of `A` with itself, computed as the sum of squares of its
components in a `g_p`-orthonormal basis. -/
def normSqAt (g : RiemannianMetric I M) {k : ℕ} (A : CovTensorField I M k)
    (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
    (A (fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p) ^ 2

omit [CompleteSpace E] in
/-- **Math.** The square norm is a sum of squares, hence nonnegative. -/
theorem normSqAt_nonneg (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) : 0 ≤ normSqAt g A p :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [CompleteSpace E] in
/-- **Math.** The square norm vanishes exactly when every component in an
orthonormal basis vanishes. -/
theorem normSqAt_eq_zero_iff (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    normSqAt g A p = 0 ↔
      ∀ v : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
        A (fun i => MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) (v i))) p = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [normSqAt, Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _]
  constructor
  · intro h v
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (h v (Finset.mem_univ v))
  · intro h v _
    rw [h v]
    norm_num

/-- **Math.** The pointwise norm `|A|`, the square root of the square norm. -/
def normAt (g : RiemannianMetric I M) {k : ℕ} (A : CovTensorField I M k)
    (p : M) : ℝ :=
  Real.sqrt (normSqAt g A p)

omit [CompleteSpace E] in
/-- **Math.** The pointwise norm is nonnegative. -/
theorem normAt_nonneg (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) : 0 ≤ normAt g A p :=
  Real.sqrt_nonneg _

omit [CompleteSpace E] in
/-- **Math.** `|A|^2` recovers the square norm, the point of `normAt`. -/
theorem normAt_sq (g : RiemannianMetric I M) {k : ℕ}
    (A : CovTensorField I M k) (p : M) :
    normAt g A p ^ 2 = normSqAt g A p :=
  Real.sq_sqrt (normSqAt_nonneg g A p)

end Topping

end

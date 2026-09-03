import Topping.MaximumPrinciple.CurvatureStarBound
import Topping.MaximumPrinciple.TensorNormAlgebra
import Topping.RicciFlow.Existence.FlowIntervals
import Topping.RicciFlow.Existence.NormAtBridge

/-!
# Ricci norm control from a Riemann curvature bound

The finite-time extension argument first bounds the full Riemann tensor and
then needs the source hypothesis `|Ric| <= M` used by metric equivalence.  This
file supplies that contraction step.  Ricci is one metric trace of a slot
permutation of the covariant Riemann tensor, so the existing trace estimate
costs exactly `sqrt (dim M)`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! The first two slots of the permuted tensor are the traced second and fourth
Riemann slots; the remaining two slots are Ricci's arguments. -/

def ricciTracePerm : Equiv.Perm (Fin 4) where
  toFun := ![2, 0, 3, 1]
  invFun := ![1, 3, 0, 2]
  left_inv := by decide
  right_inv := by decide

@[simp] theorem ricciTracePerm_zero : ricciTracePerm 0 = 2 := by decide
@[simp] theorem ricciTracePerm_one : ricciTracePerm 1 = 0 := by decide
@[simp] theorem ricciTracePerm_two : ricciTracePerm 2 = 3 := by decide
@[simp] theorem ricciTracePerm_three : ricciTracePerm 3 = 1 := by decide

/-- **Math.** The covariant Ricci tensor is the metric trace of the second and
fourth slots of the Riemann tensor. -/
theorem traceFirstTwo_perm_riemannTensorField_eq_ricciTensorField
    (g : RiemannianMetric I M) :
    traceFirstTwo g (permSlots ricciTracePerm (riemannTensorField g)) =
      ricciTensorField g := by
  funext Y p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [traceFirstTwo, permSlots, riemannTensorField, ricciTensorField]
  rw [ricciTracePerm_zero, ricciTracePerm_one,
    ricciTracePerm_two, ricciTracePerm_three]
  simp only [Fin.cons_zero, MorganTianLib.extendVector_apply]
  have h1 (x : Fin (Module.finrank ℝ (TangentSpace I p))) :
      ((Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x))
        (Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x)) Y) :
          Fin 4 → SmoothVectorField I M) (1 : Fin 4)) p =
        (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x)) p := by
    rfl
  have h2 (x : Fin (Module.finrank ℝ (TangentSpace I p))) :
      ((Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x))
        (Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x)) Y) :
          Fin 4 → SmoothVectorField I M) (2 : Fin 4)) p =
        (Y 0) p := by
    rfl
  have h3 (x : Fin (Module.finrank ℝ (TangentSpace I p))) :
      ((Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x))
        (Fin.cons (MorganTianLib.extendVector p
          (stdOrthonormalBasis ℝ (TangentSpace I p) x)) Y) :
          Fin 4 → SmoothVectorField I M) (3 : Fin 4)) p =
        (Y 1) p := by
    rfl
  simp_rw [h1, h2, h3]
  simp only [MorganTianLib.extendVector_apply]
  change (∑ x, riemannCurvatureAt g p
      ((Y 0) p)
      (stdOrthonormalBasis ℝ (TangentSpace I p) x)
      (Y 1 p)
      (stdOrthonormalBasis ℝ (TangentSpace I p) x)) = _
  exact (ricciTensorAt_eq_sum g p (Y 0 p) (Y 1 p)
    (stdOrthonormalBasis ℝ (TangentSpace I p))).symm

/-- **Math.** One curvature contraction costs at most `sqrt (dim M)` in the
Hilbert--Schmidt pointwise norm: `|Ric| <= sqrt(n) |Rm|`. -/
theorem normAt_ricciCovTensorField_le_sqrt_finrank_mul_riemannNormAt
    (g : RiemannianMetric I M) (p : M) :
    normAt g (ricciCovTensorField g) p ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) * riemannNormAt g p := by
  calc
    normAt g (ricciCovTensorField g) p =
        normAt g (traceFirstTwo g
          (permSlots ricciTracePerm (riemannTensorField g))) p := by
      rw [traceFirstTwo_perm_riemannTensorField_eq_ricciTensorField]
      rfl
    _ ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
        normAt g (permSlots ricciTracePerm (riemannTensorField g)) p :=
      normAt_traceFirstTwo_le g _ p
    _ = Real.sqrt (Module.finrank ℝ E : ℝ) * riemannNormAt g p := by
      rw [normAt_permSlots, riemannNormAt_eq_normAt_riemannTensorField]

/-- **Math.** A pointwise Riemann norm bound on a time set produces the Ricci
norm bound consumed by the metric-equivalence theorem. -/
theorem hasRicciNormBoundOn_of_riemannNormBoundOn
    (g : ℝ → RiemannianMetric I M) (C : ℝ) (J : Set ℝ)
    (hRm : ∀ t ∈ J, ∀ p : M, riemannNormAt (g t) p ≤ C) :
    HasRicciNormBoundOn g
      (Real.sqrt (Module.finrank ℝ E : ℝ) * C) J := by
  intro t ht p
  exact (normAt_ricciCovTensorField_le_sqrt_finrank_mul_riemannNormAt
      (g t) p).trans
    (mul_le_mul_of_nonneg_left (hRm t ht p) (Real.sqrt_nonneg _))

/-- **Math.** Topping's uniform curvature-bound contract therefore supplies a
single nonnegative Ricci bound on the whole half-open flow interval. -/
theorem exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hRm : HasUniformCurvatureBoundBefore g T) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧ HasRicciNormBoundOn g M0 (Ico 0 T) := by
  obtain ⟨C, hC, hRm⟩ := hRm
  refine ⟨Real.sqrt (Module.finrank ℝ E : ℝ) * C,
    mul_nonneg (Real.sqrt_nonneg _) hC, ?_⟩
  exact hasRicciNormBoundOn_of_riemannNormBoundOn g C (Ico 0 T) hRm

#print axioms traceFirstTwo_perm_riemannTensorField_eq_ricciTensorField
#print axioms normAt_ricciCovTensorField_le_sqrt_finrank_mul_riemannNormAt
#print axioms hasRicciNormBoundOn_of_riemannNormBoundOn
#print axioms exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore

end Topping

end

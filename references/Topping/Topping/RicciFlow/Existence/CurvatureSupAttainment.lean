import Topping.RicciFlow.Existence.CurvatureSupBounds
import Topping.MaximumPrinciple.TensorLeibniz

/-!
# Continuity and attainment of the curvature supremum

The definition of `curvatureSup` is deliberately an extended-domain `sSup`
bridge.  On a compact manifold the curvature norm is continuous, so this file
supplies the missing finiteness and maximum-point consumers without changing
that definition or silently assuming boundedness elsewhere.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [Nonempty M]

/-! ## Fixed-time continuity -/

omit [Nonempty M] in
/-- **Math.** The pointwise curvature norm is continuous on a compact manifold. -/
theorem continuous_riemannNormAt [CompactSpace M]
    (g : RiemannianMetric I M) :
    Continuous (fun p : M => riemannNormAt g p) := by
  have hsq : Continuous (fun p : M => riemannNormAt g p ^ 2) :=
    (riemannNormAt_sq_contMDiff g).continuous
  have hsqrt : Continuous (fun p : M =>
      Real.sqrt (riemannNormAt g p ^ 2)) :=
    Real.continuous_sqrt.comp hsq
  convert hsqrt using 1
  funext p
  exact (Real.sqrt_sq (riemannNormAt_nonneg g p)).symm

/-! ## Supremum finiteness and attainment -/

omit [Nonempty M] in
/-- **Math.** The curvature-norm range is bounded above on a compact manifold. -/
theorem bddAbove_range_riemannNormAt [CompactSpace M]
    (g : RiemannianMetric I M) :
    BddAbove (Set.range (fun p : M => riemannNormAt g p)) := by
  simpa only [Set.image_univ] using
    (isCompact_univ.image (continuous_riemannNormAt g)).bddAbove

/-- **Math.** The spatial curvature supremum is attained at a point of a compact
    manifold. -/
theorem exists_curvatureSup_eq_riemannNormAt [CompactSpace M]
    (g : ℝ → RiemannianMetric I M) (t : ℝ) :
    ∃ p : M, curvatureSup g t = riemannNormAt (g t) p := by
  let f : M → ℝ := fun p => riemannNormAt (g t) p
  have hf : Continuous f := continuous_riemannNormAt (g t)
  obtain ⟨p, hp, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set M)).exists_isMaxOn
      (Set.univ_nonempty) hf.continuousOn
  have hgreat : IsGreatest (Set.range f) (f p) := by
    refine ⟨⟨p, rfl⟩, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hmax (Set.mem_univ q)
  refine ⟨p, ?_⟩
  change sSup (Set.range f) = f p
  exact hgreat.csSup_eq

/-- **Math.** The spatial curvature supremum is nonnegative on a compact manifold. -/
theorem curvatureSup_nonneg [CompactSpace M]
    (g : ℝ → RiemannianMetric I M) (t : ℝ) :
    0 ≤ curvatureSup g t := by
  obtain ⟨p, hp⟩ := exists_curvatureSup_eq_riemannNormAt g t
  rw [hp]
  exact riemannNormAt_nonneg (g t) p

#print axioms continuous_riemannNormAt
#print axioms bddAbove_range_riemannNormAt
#print axioms exists_curvatureSup_eq_riemannNormAt
#print axioms curvatureSup_nonneg

end Topping

end

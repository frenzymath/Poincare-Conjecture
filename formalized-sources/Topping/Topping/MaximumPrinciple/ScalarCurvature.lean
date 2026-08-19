import Topping.MaximumPrinciple.Riemannian
import Topping.RicciFlow.Basic
import Topping.Riemannian.RicciNorm

/-!
# Scalar curvature barriers

This module packages the quadratic ODE comparison used for scalar curvature
under Ricci flow.  The geometric input is stated as the scalar parabolic
inequality, so the result can be connected to the metric evolution once that
interface is available.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

/-- **Math.** Scalar curvature obeys its Ricci-flow evolution equation on `J`. -/
def HasScalarCurvatureEvolutionOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p,
    HasDerivWithinAt (fun s => scalarCurvatureAt (g s) p)
      (metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
        2 * ricciNormSqAt (g t) p) J t

/-- **Math.** Scalar-curvature evolution and trace decomposition imply the
quadratic scalar parabolic inequality used by the weak minimum principle. -/
theorem scalarCurvature_parabolic_inequality_of_evolution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T) (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T)) :
    ∀ t ∈ Icc 0 T, ∀ p,
      metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          (2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureAt (g t) p ^ 2 ≤
        derivWithin (fun s => scalarCurvatureAt (g s) p) (Icc 0 T) t := by
  intro t ht p
  have hderiv :=
    (hevolution t ht p).derivWithin (uniqueDiffOn_Icc hT t ht)
  rw [hderiv]
  have htrace :=
    scalarCurvatureAt_sq_div_finrank_le_ricciNormSqAt (g t) p
  have hscaled := mul_le_mul_of_nonneg_left htrace (by norm_num : (0 : ℝ) ≤ 2)
  calc
    metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          (2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureAt (g t) p ^ 2 =
        metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          2 * (scalarCurvatureAt (g t) p ^ 2 / (Module.finrank ℝ E : ℝ)) := by
      ring
    _ ≤ metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          2 * ricciNormSqAt (g t) p := add_le_add_right hscaled _

/-- **Math.** The scalar-curvature evolution equation on Ioc 0 T gives the
same parabolic inequality on the closed consumer interval at every strictly
positive time. The two within-sets agree in a neighbourhood of such a time. -/
theorem scalarCurvature_parabolic_inequality_of_evolution_on_Ioc
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T) (hevolution : HasScalarCurvatureEvolutionOn g (Ioc 0 T)) :
    ∀ t ∈ Icc 0 T, 0 < t → ∀ p,
      metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          (2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureAt (g t) p ^ 2 ≤
        derivWithin (fun s => scalarCurvatureAt (g s) p) (Icc 0 T) t := by
  intro t ht htpos p
  have hsets : Ioc (0 : ℝ) T =ᶠ[𝓝 t] Icc 0 T := by
    filter_upwards [Ioi_mem_nhds htpos] with s hs
    apply propext
    constructor
    · intro h
      exact ⟨h.1.le, h.2⟩
    · intro h
      exact ⟨hs, h.2⟩
  have hderiv :=
    (hevolution t ⟨htpos, ht.2⟩ p).congr_set hsets
  have hderiv' :=
    hderiv.derivWithin (uniqueDiffOn_Icc hT t ht)
  rw [hderiv']
  have htrace :=
    scalarCurvatureAt_sq_div_finrank_le_ricciNormSqAt (g t) p
  have hscaled := mul_le_mul_of_nonneg_left htrace (by norm_num : (0 : ℝ) ≤ 2)
  calc
    metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          (2 / (Module.finrank ℝ E : ℝ)) * scalarCurvatureAt (g t) p ^ 2 =
        metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          2 * (scalarCurvatureAt (g t) p ^ 2 / (Module.finrank ℝ E : ℝ)) := by
      ring
    _ ≤ metricLaplacianAt (g t) (fun q => scalarCurvatureAt (g t) q) p +
          2 * ricciNormSqAt (g t) p := add_le_add_right hscaled _

/-- **Math.** The solution of `phi' = c * phi ^ 2` with initial value `alpha`. -/
def quadraticBarrier (c alpha t : ℝ) : ℝ :=
  alpha / (1 - c * alpha * t)

/-- **Math.** The quadratic barrier solves its ODE wherever its denominator is
positive. -/
theorem quadraticBarrier_hasDerivWithinAt {c alpha T t : ℝ}
    (hdenom : 0 < 1 - c * alpha * t) :
    HasDerivWithinAt (quadraticBarrier c alpha)
      (c * quadraticBarrier c alpha t ^ 2) (Icc 0 T) t := by
  have hnum : HasDerivAt (fun _ : ℝ => alpha) 0 t :=
    hasDerivAt_const t alpha
  have hden : HasDerivAt (fun s : ℝ => 1 - c * alpha * s) (-c * alpha) t := by
    have h := (hasDerivAt_const t (1 : ℝ)).sub
      ((hasDerivAt_id t).const_mul (c * alpha))
    convert h using 1 <;>
      first | apply Subsingleton.elim | rfl | ring
  have hquot := hnum.div hden (ne_of_gt hdenom)
  rw [quadraticBarrier]
  convert hquot.hasDerivWithinAt using 1 <;>
    first
    | apply Subsingleton.elim
    | rfl
    | (field_simp [ne_of_gt hdenom]; ring)

/-- **Math.** The scalar-curvature comparison profile in dimension `n`. -/
def scalarLowerBarrier (n : ℕ) (alpha t : ℝ) : ℝ :=
  quadraticBarrier (2 / (n : ℝ)) alpha t

/-- **Math.** A scalar parabolic inequality with reaction `(2 / n) R^2` preserves the
explicit lower barrier while its denominator stays positive.  This is the
maximum-principle part of the scalar-curvature lower bound; a Ricci-flow
specialization supplies the scalar evolution inequality. -/
theorem scalarLowerBarrier_le_of_parabolic_inequality
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M}
    {R : M → ℝ → ℝ} {n : ℕ} {T alpha : ℝ}
    (_hn : 0 < n) (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => R z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : ∀ t ∈ Icc 0 T, ∀ x,
      metricLaplacianAt (g t) (fun y => R y t) x
          + (2 / (n : ℝ)) * R x t ^ 2 ≤
        derivWithin (R x) (Icc 0 T) t)
    (hdenom : ∀ t ∈ Icc 0 T,
      0 < 1 - (2 / (n : ℝ)) * alpha * t)
    (hzero : ∀ x, alpha ≤ R x 0) :
    ∀ x t, t ∈ Icc 0 T → scalarLowerBarrier n alpha t ≤ R x t := by
  apply weak_minimum_principle
    (g := g) (X := fun _ => 0) (u := R)
    (φ := scalarLowerBarrier n alpha)
    (F := fun r _ => (2 / (n : ℝ)) * r ^ 2)
    (T := T) (α := alpha) hT
  · fun_prop
  · exact hR
  · intro t ht x
    have hzero :
        (0 : SmoothVectorField I M).dir (fun y => R y t) x = 0 := by
      rw [SmoothVectorField.dir, SmoothVectorField.zero_apply]
      exact map_zero _
    rw [hzero]
    simpa only [add_zero] using hevolution t ht x
  · intro t ht
    exact quadraticBarrier_hasDerivWithinAt (hdenom t ht)
  · simp [scalarLowerBarrier, quadraticBarrier]
  · exact hzero

/-- **Math.** The quadratic scalar barrier remains valid when the parabolic
inequality is supplied only at strictly positive times. -/
theorem scalarLowerBarrier_le_of_parabolic_inequality_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [FiniteDimensional ℝ E]
    [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M}
    {R : M → ℝ → ℝ} {n : ℕ} {T alpha : ℝ}
    (_hn : 0 < n) (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => R z.1 z.2)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : ∀ t ∈ Icc 0 T, 0 < t → ∀ x,
      metricLaplacianAt (g t) (fun y => R y t) x
          + (2 / (n : ℝ)) * R x t ^ 2 ≤
        derivWithin (R x) (Icc 0 T) t)
    (hdenom : ∀ t ∈ Icc 0 T,
      0 < 1 - (2 / (n : ℝ)) * alpha * t)
    (hzero : ∀ x, alpha ≤ R x 0) :
    ∀ x t, t ∈ Icc 0 T → scalarLowerBarrier n alpha t ≤ R x t := by
  apply weak_minimum_principle_of_pos
    (g := g) (X := fun _ => 0) (u := R)
    (φ := scalarLowerBarrier n alpha)
    (F := fun r _ => (2 / (n : ℝ)) * r ^ 2)
    (T := T) (α := alpha) hT
  · fun_prop
  · exact hR
  · intro t ht htpos x
    have hzero :
        (0 : SmoothVectorField I M).dir (fun y => R y t) x = 0 := by
      rw [SmoothVectorField.dir, SmoothVectorField.zero_apply]
      exact map_zero _
    rw [hzero]
    simpa only [add_zero] using hevolution t ht htpos x
  · intro t ht
    exact quadraticBarrier_hasDerivWithinAt (hdenom t ht)
  · simp [scalarLowerBarrier, quadraticBarrier]
  · exact hzero

/-- **Math.** Scalar-curvature evolution on a closed Ricci flow supplies the
explicit quadratic lower barrier. -/
theorem scalarLowerBarrier_le_of_scalarCurvatureEvolution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [CompactSpace M]
    {g : ℝ → RiemannianMetric I M} {T alpha : ℝ}
    (hT : 0 < T)
    (hR : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
      (fun z : M × ℝ => scalarCurvatureAt (g z.2) z.1)
      ((Set.univ : Set M) ×ˢ Icc 0 T))
    (hevolution : HasScalarCurvatureEvolutionOn g (Icc 0 T))
    (hdenom : ∀ t ∈ Icc 0 T,
      0 < 1 - (2 / (Module.finrank ℝ E : ℝ)) * alpha * t)
    (hzero : ∀ p, alpha ≤ scalarCurvatureAt (g 0) p) :
    ∀ p t, t ∈ Icc 0 T →
      scalarLowerBarrier (Module.finrank ℝ E) alpha t ≤
        scalarCurvatureAt (g t) p := by
  have hn : 0 < Module.finrank ℝ E :=
    Nat.pos_of_ne_zero (NeZero.ne _)
  apply scalarLowerBarrier_le_of_parabolic_inequality
    (g := g) (R := fun p t => scalarCurvatureAt (g t) p)
    (n := Module.finrank ℝ E) hn hT hR
  · exact scalarCurvature_parabolic_inequality_of_evolution hT hevolution
  · exact hdenom
  · exact hzero

end Topping

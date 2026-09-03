import MorganTianLib.Ch03.RicciFlow.CurvatureEvolution

/-!
# Morgan--Tian Ch. 3 - multilinearity of the quadratic curvature contraction

The quadratic contraction `curvatureB` is defined by an orthonormal-frame
contraction of two curvature forms.  This module exposes its genuine
four-slot multilinearity at a tangent space.  These are structural producers,
not certificate wrappers: each identity is proved by expanding the defining
finite sums and using the curvature-form slot laws.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private theorem sum₂_mul_left {α β : Type*} [Fintype α] [Fintype β]
    (a : ℝ) (f : α → β → ℝ) :
    (∑ i, ∑ j, a * f i j) = a * ∑ i, ∑ j, f i j := by
  symm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]

private theorem sum₂_mul_right {α β : Type*} [Fintype α] [Fintype β]
    (a : ℝ) (f : α → β → ℝ) :
    (∑ i, ∑ j, f i j * a) = a * ∑ i, ∑ j, f i j := by
  calc
    (∑ i, ∑ j, f i j * a) = (∑ i, ∑ j, f i j) * a := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
    _ = a * ∑ i, ∑ j, f i j := by ring

theorem curvatureB_add_left (g : RiemannianMetric I M) (p : M)
    (x₁ x₂ y w z : TangentSpace I p) :
    curvatureB g p (x₁ + x₂) y w z =
      curvatureB g p x₁ y w z + curvatureB g p x₂ y w z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_add_left,
    g.metricInner_add_left, add_mul, Finset.sum_add_distrib]

theorem curvatureB_add_snd (g : RiemannianMetric I M) (p : M)
    (x y₁ y₂ w z : TangentSpace I p) :
    curvatureB g p x (y₁ + y₂) w z =
      curvatureB g p x y₁ w z + curvatureB g p x y₂ w z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_add_right,
    g.metricInner_add_left, add_mul, Finset.sum_add_distrib]

theorem curvatureB_add_third (g : RiemannianMetric I M) (p : M)
    (x y w₁ w₂ z : TangentSpace I p) :
    curvatureB g p x y (w₁ + w₂) z =
      curvatureB g p x y w₁ z + curvatureB g p x y w₂ z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_add_left,
    g.metricInner_add_left, mul_add, Finset.sum_add_distrib]

theorem curvatureB_add_fourth (g : RiemannianMetric I M) (p : M)
    (x y w z₁ z₂ : TangentSpace I p) :
    curvatureB g p x y w (z₁ + z₂) =
      curvatureB g p x y w z₁ + curvatureB g p x y w z₂ := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_add_right,
    g.metricInner_add_left, mul_add, Finset.sum_add_distrib]

theorem curvatureB_smul_left (g : RiemannianMetric I M) (p : M)
    (a : ℝ) (x y w z : TangentSpace I p) :
    curvatureB g p (a • x) y w z = a * curvatureB g p x y w z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_smul_left,
    g.metricInner_smul_left]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (sum₂_mul_left (α := Fin (Module.finrank ℝ (TangentSpace I p)))
      (β := Fin (Module.finrank ℝ (TangentSpace I p))) a
      (fun i j =>
        g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p x
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) y)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
          g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p w
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) z)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j)))

theorem curvatureB_smul_snd (g : RiemannianMetric I M) (p : M)
    (a : ℝ) (x y w z : TangentSpace I p) :
    curvatureB g p x (a • y) w z = a * curvatureB g p x y w z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_smul_right,
    g.metricInner_smul_left]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (sum₂_mul_left (α := Fin (Module.finrank ℝ (TangentSpace I p)))
      (β := Fin (Module.finrank ℝ (TangentSpace I p))) a
      (fun i j =>
        g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p x
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) y)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
          g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p w
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) z)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j)))

theorem curvatureB_smul_third (g : RiemannianMetric I M) (p : M)
    (a : ℝ) (x y w z : TangentSpace I p) :
    curvatureB g p x y (a • w) z = a * curvatureB g p x y w z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_smul_left,
    g.metricInner_smul_left]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (sum₂_mul_right (α := Fin (Module.finrank ℝ (TangentSpace I p)))
      (β := Fin (Module.finrank ℝ (TangentSpace I p))) a
      (fun i j =>
        g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p x
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) y)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
          g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p w
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) z)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j)))

theorem curvatureB_smul_fourth (g : RiemannianMetric I M) (p : M)
    (a : ℝ) (x y w z : TangentSpace I p) :
    curvatureB g p x y w (a • z) = a * curvatureB g p x y w z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  simp only [curvatureB]
  simp only [Riemannian.AffineConnection.curvatureFormAt,
    g.leviCivitaConnection.curvatureOperatorAt_smul_right,
    g.metricInner_smul_left]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using
    (sum₂_mul_right (α := Fin (Module.finrank ℝ (TangentSpace I p)))
      (β := Fin (Module.finrank ℝ (TangentSpace I p))) a
      (fun i j =>
        g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p x
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) y)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
          g.metricInner p
            (g.leviCivitaConnection.curvatureOperatorAt p w
              (stdOrthonormalBasis ℝ (TangentSpace I p) i) z)
            (stdOrthonormalBasis ℝ (TangentSpace I p) j)))

end MorganTianLib

end

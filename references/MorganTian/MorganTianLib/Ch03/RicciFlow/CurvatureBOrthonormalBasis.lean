import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian
import DoCarmoLib.Riemannian.Connection.ChartCurvatureMovingPoint
import Shared.Algebraic.Auxiliary.OrthonormalBasisDiagonal

/-!
# Morgan--Tian Ch. 3 - basis invariance of the quadratic curvature contraction

The tensor `curvatureB` is defined using the standard orthonormal basis of a
tangent fibre.  This file records the corresponding coordinate-free producer:
the same double contraction is obtained from every finite orthonormal basis.
The algebraic step is separated into a generic Frobenius pairing lemma so that
later curvature estimates can change frames without unfolding the geometric
definition again.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

section BilinearPairing

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/- The Hilbert--Schmidt pairing of two bilinear maps is independent of the
   orthonormal basis used in both slots. -/
theorem sum_mul_bilinear_invariant
    (b : OrthonormalBasis ι ℝ V) (b' : OrthonormalBasis κ ℝ V)
    (A C : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    (∑ i, ∑ j, A (b i) (b j) * C (b i) (b j)) =
      ∑ i, ∑ j, A (b' i) (b' j) * C (b' i) (b' j) := by
  classical
  -- First change the outer basis, keeping the inner basis `b` fixed.
  let Q : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v v' => ∑ j, A v (b j) * C v' (b j))
      (fun v₁ v₂ v' => by
        have h : ∀ j, A (v₁ + v₂) (b j) * C v' (b j) =
            A v₁ (b j) * C v' (b j) + A v₂ (b j) * C v' (b j) := fun j => by
          rw [map_add, LinearMap.add_apply]
          ring
        simp only [h, Finset.sum_add_distrib])
      (fun a v v' => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smul_apply]
        simp only [smul_eq_mul]
        ring)
      (fun v w₁ w₂ => by
        have h : ∀ j, A v (b j) * C (w₁ + w₂) (b j) =
            A v (b j) * C w₁ (b j) + A v (b j) * C w₂ (b j) := fun j => by
          rw [map_add, LinearMap.add_apply]
          ring
        simp only [h, Finset.sum_add_distrib])
      (fun a v w => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, LinearMap.smul_apply]
        simp only [smul_eq_mul]
        ring)
  have hQ : ∀ v v', Q v v' = ∑ j, A v (b j) * C v' (b j) := fun _ _ => rfl
  have step1 :
      (∑ i, ∑ j, A (b i) (b j) * C (b i) (b j)) =
        ∑ i, ∑ j, A (b' i) (b j) * C (b' i) (b j) := by
    have h := OrthonormalBasis.sum_apply_diagonal_invariant b b' Q
    simp only [hQ] at h
    exact h
  -- Then change the inner basis, keeping the outer basis `b'` fixed.
  let R : V →ₗ[ℝ] V →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun w w' => ∑ i, A (b' i) w * C (b' i) w')
      (fun w₁ w₂ w' => by
        have h : ∀ i, A (b' i) (w₁ + w₂) * C (b' i) w' =
            A (b' i) w₁ * C (b' i) w' + A (b' i) w₂ * C (b' i) w' := fun i => by
          rw [map_add]
          ring
        simp only [h, Finset.sum_add_distrib])
      (fun a w w' => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        simp only [smul_eq_mul]
        ring)
      (fun w u₁ u₂ => by
        have h : ∀ i, A (b' i) w * C (b' i) (u₁ + u₂) =
            A (b' i) w * C (b' i) u₁ + A (b' i) w * C (b' i) u₂ := fun i => by
          rw [map_add]
          ring
        simp only [h, Finset.sum_add_distrib])
      (fun a w u => by
        simp only [smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul]
        simp only [smul_eq_mul]
        ring)
  have hR : ∀ w w', R w w' = ∑ i, A (b' i) w * C (b' i) w' := fun _ _ => rfl
  have step2 :
      (∑ i, ∑ j, A (b' i) (b j) * C (b' i) (b j)) =
        ∑ i, ∑ j, A (b' i) (b' j) * C (b' i) (b' j) := by
    have h := OrthonormalBasis.sum_apply_diagonal_invariant b b' R
    simp only [hR] at h
    calc
      (∑ i, ∑ j, A (b' i) (b j) * C (b' i) (b j)) =
          ∑ j, ∑ i, A (b' i) (b j) * C (b' i) (b j) := by
            exact Finset.sum_comm
      _ = ∑ j, ∑ i, A (b' i) (b' j) * C (b' i) (b' j) := h
      _ = ∑ i, ∑ j, A (b' i) (b' j) * C (b' i) (b' j) := by
            exact Finset.sum_comm
  rw [step1, step2]

end BilinearPairing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Morgan--Tian quadratic curvature contraction is independent
of the orthonormal basis used for its two contracted slots.  Thus the standard
basis in `curvatureB` may be replaced by any finite orthonormal basis `e` of
the metric tangent fibre. -/
theorem curvatureB_eq_sum_orthonormalBasis
    (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    curvatureB g p x y w z =
      ∑ i, ∑ j,
        g.leviCivitaConnection.curvatureFormAt g p x (e i) y (e j) *
          g.leviCivitaConnection.curvatureFormAt g p w (e i) z (e j) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  let A : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v v' => g.leviCivitaConnection.curvatureFormAt g p x v y v')
      (fun v₁ v₂ v' => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.leviCivitaConnection.curvatureOperatorAt_add_middle,
          g.metricInner_add_left])
      (fun a v v' => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.leviCivitaConnection.curvatureOperatorAt_smul_middle,
          g.metricInner_smul_left, smul_eq_mul])
      (fun v v'₁ v'₂ => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.metricInner_add_right])
      (fun a v v' => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.metricInner_smul_right, smul_eq_mul])
  let C : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ
      (fun v v' => g.leviCivitaConnection.curvatureFormAt g p w v z v')
      (fun v₁ v₂ v' => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.leviCivitaConnection.curvatureOperatorAt_add_middle,
          g.metricInner_add_left])
      (fun a v v' => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.leviCivitaConnection.curvatureOperatorAt_smul_middle,
          g.metricInner_smul_left, smul_eq_mul])
      (fun v v'₁ v'₂ => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.metricInner_add_right])
      (fun a v v' => by
        simp only [Riemannian.AffineConnection.curvatureFormAt,
          g.metricInner_smul_right, smul_eq_mul])
  have h := sum_mul_bilinear_invariant b e A C
  rw [curvatureB]
  change
    (∑ i, ∑ j, A (b i) (b j) * C (b i) (b j)) =
      ∑ i, ∑ j, A (e i) (e j) * C (e i) (e j)
  exact h

#print axioms MorganTianLib.sum_mul_bilinear_invariant
#print axioms MorganTianLib.curvatureB_eq_sum_orthonormalBasis

end MorganTianLib

end

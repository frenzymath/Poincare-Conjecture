import MorganTianLib.Ch03.RicciFlow.GeneralizedScaling
import MorganTianLib.Ch03.RicciFlow.GeneralizedScalingClosure

/-!
# Morgan--Tian Ch. 3 - transport laws for affine scaling

This module records the exact composition laws for the positive affine time
changes used by generalized space-time embeddings.  They are useful when a
rescaling is followed by a second rescaling or translation.
-/

open scoped ContDiff
open Set

noncomputable section

namespace MorganTianLib

variable {X : Type*}

@[simp]
theorem parabolicTimeOrderIso_comp (Q R : ℝ) (hQ : 0 < Q) (hR : 0 < R)
    (a b t : ℝ) :
    parabolicTimeOrderIso R hR b (parabolicTimeOrderIso Q hQ a t) =
      parabolicTimeOrderIso (R * Q) (mul_pos hR hQ) (R * a + b) t := by
  simp only [parabolicTimeOrderIso_apply]
  ring

/-! The component fields of the generalized affine constructor obey the same
composition law.  These identities are the algebraic core needed when a
parabolic blow-up is followed by a second rescaling. -/

@[simp]
theorem GeneralizedSpaceTime.affineTimeChange_affineTimeChange_time
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n.succ) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]
    (S : GeneralizedSpaceTime n (N := N))
    (Q R : ℝ) (hQ : 0 < Q) (hR : 0 < R) (a b : ℝ) (x : N) :
    ((S.affineTimeChange n Q hQ a).affineTimeChange n R hR b).time x =
      (S.affineTimeChange n (R * Q) (mul_pos hR hQ) (R * a + b)).time x := by
  simp only [GeneralizedSpaceTime.affineTimeChange_time]
  ring

@[simp]
theorem GeneralizedSpaceTime.affineTimeChange_affineTimeChange_timeVector
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n.succ) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]
    (S : GeneralizedSpaceTime n (N := N))
    (Q R : ℝ) (hQ : 0 < Q) (hR : 0 < R) (a b : ℝ) (x : N) :
    ((S.affineTimeChange n Q hQ a).affineTimeChange n R hR b).timeVector x =
      (S.affineTimeChange n (R * Q) (mul_pos hR hQ) (R * a + b)).timeVector x := by
  simp only [GeneralizedSpaceTime.affineTimeChange_timeVector, smul_smul, mul_inv]

theorem parabolicTimeOrderIso_image_image (Q R : ℝ) (hQ : 0 < Q) (hR : 0 < R)
    (a b : ℝ) (J : Set ℝ) :
    parabolicTimeOrderIso R hR b ''
        (parabolicTimeOrderIso Q hQ a '' J) =
      parabolicTimeOrderIso (R * Q) (mul_pos hR hQ) (R * a + b) '' J := by
  rw [Set.image_image]
  ext t
  simp only [parabolicTimeOrderIso_comp]

/-! The affine reparameterization is a right inverse to the corresponding
time change on every spatial parameter.  This pointwise identity is the
compatibility step used when transporting an embedding (and avoids repeating
the field cancellation at each image argument). -/

theorem GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam_parabolicTimeOrderIso
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n.succ) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {J : Set ℝ}
    (e : S.CompatibleEmbedding n C J) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x : N) (t : ℝ) :
    e.affineTimeReparam n Q hQ a
        (x, parabolicTimeOrderIso Q hQ a t) = e.toFun (x, t) := by
  simp only [GeneralizedSpaceTime.CompatibleEmbedding.affineTimeReparam,
    parabolicTimeOrderIso_apply, parabolicTimeOrderIso_symm_apply]
  have hcancel : (Q * t + a - a) / Q = t := by
    field_simp [hQ.ne']
    ring
  rw [hcancel]

theorem parabolicTimeOrderIso_preimage_image (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (J : Set ℝ) :
    (parabolicTimeOrderIso Q hQ a) ⁻¹' (parabolicTimeOrderIso Q hQ a '' J) = J := by
  exact (parabolicTimeOrderIso Q hQ a).injective.preimage_image J

theorem parabolicTimeOrderIso_image_preimage (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (J : Set ℝ) :
    parabolicTimeOrderIso Q hQ a ''
        ((parabolicTimeOrderIso Q hQ a) ⁻¹' J) = J := by
  exact (parabolicTimeOrderIso Q hQ a).surjective.image_preimage J

theorem parabolicTimeOrderIso_product_image_image
    (C : Set X) (Q R : ℝ) (hQ : 0 < Q) (hR : 0 < R) (a b : ℝ)
    (J : Set ℝ) :
    C ×ˢ (parabolicTimeOrderIso R hR b ''
      (parabolicTimeOrderIso Q hQ a '' J)) =
      C ×ˢ (parabolicTimeOrderIso (R * Q) (mul_pos hR hQ)
        (R * a + b) '' J) := by
  rw [parabolicTimeOrderIso_image_image]

/-! The affine space-time constructor in `GeneralizedScalingClosure` packages
the scaled time and inverse-scaled vector.  The following differential laws
make that package explicit at the manifold level. -/

theorem GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n.succ) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x : N) :
    (S.affineTimeChange n Q hQ a).timeDifferential (n := n) x =
      Q • S.timeDifferential (n := n) x := by
  change
    (mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) (Q • S.time + fun _ : N => a) x :
      TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ] ℝ) =
      Q • (mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
        (modelWithCornersSelf ℝ ℝ) S.time x :
        TangentSpace (modelWithCornersEuclideanHalfSpace n.succ) x →L[ℝ] ℝ)
  have htime : MDifferentiableAt (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) S.time x :=
    S.time_contMDiff.mdifferentiableAt (by simp)
  have hconst : MDifferentiableAt (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) (fun _ : N => a) x :=
    mdifferentiableAt_const
  have hscaled := htime.hasMFDerivAt.const_smul Q
  have hderiv := hscaled.add hconst.hasMFDerivAt
  have hEq := hderiv.mfderiv
  rw [mfderiv_const] at hEq
  convert hEq using 1
  · ext v
    change Q • ((mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
      (modelWithCornersSelf ℝ ℝ) S.time x) v) =
      Q • ((mfderiv (modelWithCornersEuclideanHalfSpace n.succ)
        (modelWithCornersSelf ℝ ℝ) S.time x) v) + 0
    rw [add_zero]

theorem GeneralizedSpaceTime.affineTimeChange_timeDifferential_timeVector
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n.succ) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x : N) :
    (S.affineTimeChange n Q hQ a).timeDifferential (n := n) x
        ((S.affineTimeChange n Q hQ a).timeVector x) = 1 := by
  rw [GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq]
  simp only [GeneralizedSpaceTime.affineTimeChange_timeVector,
    smul_apply, map_smul, S.timeDifferential_timeVector (n := n) x,
    smul_eq_mul]
  field_simp [hQ.ne']

@[simp]
theorem GeneralizedSpaceTime.affineTimeChange_affineTimeChange_timeDifferential
    {n : ℕ} {N : Type*} [TopologicalSpace N]
    [ChartedSpace (EuclideanHalfSpace n.succ) N]
    [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]
    (S : GeneralizedSpaceTime n (N := N))
    (Q R : ℝ) (hQ : 0 < Q) (hR : 0 < R) (a b : ℝ) (x : N) :
    ((S.affineTimeChange n Q hQ a).affineTimeChange n R hR b).timeDifferential
        (n := n) x =
      (S.affineTimeChange n (R * Q) (mul_pos hR hQ) (R * a + b)).timeDifferential
        (n := n) x := by
  rw [GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq,
    GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq,
    GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq]
  simp only [smul_smul]

end MorganTianLib

end

#print axioms MorganTianLib.GeneralizedSpaceTime.affineTimeChange_timeDifferential_eq
#print axioms MorganTianLib.GeneralizedSpaceTime.affineTimeChange_timeDifferential_timeVector

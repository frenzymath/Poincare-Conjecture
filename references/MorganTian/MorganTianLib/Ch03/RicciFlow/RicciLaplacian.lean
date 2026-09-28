import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian
import MorganTianLib.Ch03.RicciFlow.ScalarEvolution

/-!
# Morgan--Tian Ch. 3 - the Ricci curvature reaction terms

This module expands the Lichnerowicz Laplacian of the Ricci tensor into the
rough Laplacian and the two quadratic contractions appearing in the Ricci-flow
evolution equation.  Both contractions are stated pointwise in an orthonormal
basis:

`Delta_L Ric(X,W) = Delta Ric(X,W)
  + 2 sum_ij Rm(X,e_i,W,e_j) Ric(e_i,e_j)
  - 2 sum_i Ric(X,e_i) Ric(e_i,W)`.
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

/-! ### Curvature operator and the Lichnerowicz Laplacian -/

/-- **Math.** The curvature operator of the canonical Levi--Civita connection, evaluated
on smooth vector fields. -/
noncomputable def curvatureOperatorField (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) : SmoothVectorField I M :=
  g.leviCivitaConnection.curvature X Y Z

/-- **Math.** The Lichnerowicz Laplacian of a covariant `2`-tensor, in
Morgan--Tian's curvature convention.  Its curvature trace uses `R(X,e_i)W`.
The displayed `R_{pjkr}` in Morgan--Tian is a source erratum; the tensorial
Ricci evolution has the corrected contraction `R_{jpkr}`. -/
def lichnerowiczLaplacian (g : RiemannianMetric I M)
    (h : CovTensorField I M 2) : CovTensorField I M 2 :=
  fun Y p =>
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    roughLaplacian g g.leviCivitaConnection h Y p
      - h (fun i => if i = 0 then Y 0 else
            extendVector p (ricciEndomorphismAt g p (Y 1 p))) p
      - h (fun i => if i = 0 then Y 1 else
            extendVector p (ricciEndomorphismAt g p (Y 0 p))) p
      + 2 * ∑ i, h (fun j => if j = 0 then
            extendVector p
              (curvatureOperatorField g
                (Y 0) (extendVector p
                  (stdOrthonormalBasis ℝ (TangentSpace I p) i)) (Y 1) p)
          else extendVector p
            (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p

/-! ### Orthonormal expansions -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Orthonormal expansion `v = sum_j <e_j,v> e_j`. -/
theorem sum_inner_smul_stdOrthonormalBasis (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ j, (inner ℝ (stdOrthonormalBasis ℝ (TangentSpace I p) j) v) •
        (stdOrthonormalBasis ℝ (TangentSpace I p) j : TangentSpace I p) = v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  have hcoef : ∀ j, (inner ℝ (e j) v) • (e j : TangentSpace I p)
      = (e.repr v).ofLp j • e j := by
    intro j
    rw [e.repr_apply_apply v j]
  rw [Finset.sum_congr rfl fun j _ => hcoef j]
  exact e.sum_repr v

/-- **Math.** Expanding the first argument of the Ricci tensor in the standard
orthonormal basis. -/
theorem ricciTensorAt_expand_left (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p v w =
      ∑ j, (inner ℝ (stdOrthonormalBasis ℝ (TangentSpace I p) j) v) *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) j) w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  conv_lhs => rw [← sum_inner_smul_stdOrthonormalBasis g p v]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]

/-! ### The quadratic Ricci contraction -/

/-- **Math.** Feeding the Ricci endomorphism into the Ricci tensor gives the inner
product of the two endomorphism images. -/
theorem ricciTensorAt_ricciEndomorphismAt (g : RiemannianMetric I M) (p : M)
    (x w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p x (ricciEndomorphismAt g p w) =
      inner ℝ (ricciEndomorphismAt g p x) (ricciEndomorphismAt g p w) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← inner_ricciEndomorphismAt g p x (ricciEndomorphismAt g p w)]

/-- **Math.** The two Ricci-endomorphism insertions agree by symmetry. -/
theorem ricciTensorAt_ricciEndomorphismAt_comm (g : RiemannianMetric I M) (p : M)
    (x w : TangentSpace I p) :
    ricciTensorAt g p x (ricciEndomorphismAt g p w) =
      ricciTensorAt g p w (ricciEndomorphismAt g p x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [ricciTensorAt_ricciEndomorphismAt, ricciTensorAt_ricciEndomorphismAt,
    real_inner_comm]

/-- **Math.** The quadratic Ricci term in orthonormal-basis form. -/
theorem inner_ricciEndomorphismAt_eq_sum (g : RiemannianMetric I M) (p : M)
    (x w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ (ricciEndomorphismAt g p x) (ricciEndomorphismAt g p w) =
      ∑ i, ricciTensorAt g p x
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) *
        ricciTensorAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) w := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← ricciTensorAt_ricciEndomorphismAt g p x w,
    ricciTensorAt_symm g p x (ricciEndomorphismAt g p w),
    ricciTensorAt_expand_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_comm, inner_ricciEndomorphismAt,
    ricciTensorAt_symm g p w _, ricciTensorAt_symm g p _ x]
  ring

/-! ### The curvature--Ricci contraction -/

omit [I.Boundaryless] in
/-- **Math.** The component of the curvature vector in a tangent direction is the
corresponding all-lowered curvature component. -/
theorem inner_curvatureOperatorAt_eq_curvatureFormAt (g : RiemannianMetric I M)
    (p : M) (x y z v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    inner ℝ v (g.leviCivitaConnection.curvatureOperatorAt p x y z) =
      g.leviCivitaConnection.curvatureFormAt g p x y z v := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [AffineConnection.curvatureFormAt]
  exact real_inner_comm _ _

/-- **Math.** Expanding a curvature vector in the first Ricci slot yields the pointwise
curvature--Ricci contraction. -/
theorem ricciTensorAt_curvatureOperatorAt_expand (g : RiemannianMetric I M)
    (p : M) (x y z u : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ricciTensorAt g p (g.leviCivitaConnection.curvatureOperatorAt p x y z) u =
      ∑ j, g.leviCivitaConnection.curvatureFormAt g p x y z
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) j) u := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [ricciTensorAt_expand_left g p _ u]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_curvatureOperatorAt_eq_curvatureFormAt]

/-- **Math.** The field-level curvature operator evaluates to the pointwise curvature
operator. -/
theorem curvatureOperatorField_apply_eq_curvatureOperatorAt (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    curvatureOperatorField g X Y Z p =
      g.leviCivitaConnection.curvatureOperatorAt p (X p) (Y p) (Z p) :=
  (g.leviCivitaConnection.curvatureOperatorAt_eq p rfl rfl rfl).symm

/-! ### Expansion of the Lichnerowicz Laplacian -/

/-- **Math.** The Lichnerowicz Laplacian of the Ricci tensor, with the quadratic Ricci
term retained as an inner product and the curvature contraction ordered as
`sum_ij Rm(X,e_i,W,e_j) Ric(e_i,e_j)`. -/
theorem lichnerowiczLaplacian_ricciTensorField_apply
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    lichnerowiczLaplacian g (ricciTensorField g)
        (fun i => if i = 0 then X else W) p =
      roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
          (fun i => if i = 0 then X else W) p
        - 2 * inner ℝ (ricciEndomorphismAt g p (X p))
            (ricciEndomorphismAt g p (W p))
        + 2 * ∑ i, ∑ j,
            g.leviCivitaConnection.curvatureFormAt g p
                (X p) (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
              ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  have hR1 : ricciTensorField g
      (fun i : Fin 2 => if i = 0 then X else
        extendVector p (ricciEndomorphismAt g p (W p))) p
      = inner ℝ (ricciEndomorphismAt g p (X p))
          (ricciEndomorphismAt g p (W p)) := by
    rw [ricciTensorField]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte,
      extendVector_apply]
    exact ricciTensorAt_ricciEndomorphismAt g p (X p) (W p)
  have hR2 : ricciTensorField g
      (fun i : Fin 2 => if i = 0 then W else
        extendVector p (ricciEndomorphismAt g p (X p))) p
      = inner ℝ (ricciEndomorphismAt g p (X p))
          (ricciEndomorphismAt g p (W p)) := by
    rw [ricciTensorField]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte,
      extendVector_apply]
    rw [← ricciTensorAt_ricciEndomorphismAt_comm,
      ricciTensorAt_ricciEndomorphismAt]
  have hcurv : ∀ i, ricciTensorField g
      (fun j : Fin 2 => if j = 0 then
          extendVector p
            (curvatureOperatorField g X (extendVector p (e i)) W p)
        else extendVector p (e i)) p
      = ∑ j, g.leviCivitaConnection.curvatureFormAt g p
          (X p) (e i) (W p) (e j) * ricciTensorAt g p (e i) (e j) := by
    intro i
    rw [ricciTensorField]
    simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte,
      extendVector_apply]
    rw [curvatureOperatorField_apply_eq_curvatureOperatorAt]
    simp only [extendVector_apply]
    rw [ricciTensorAt_curvatureOperatorAt_expand]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ricciTensorAt_symm g p (e j) (e i)]
  rw [lichnerowiczLaplacian]
  simp only [show (1 : Fin 2) ≠ 0 by decide, if_false, reduceIte]
  rw [hR1, hR2, Finset.sum_congr rfl fun i _ => hcurv i]
  ring

/-- **Math.** **Morgan--Tian, Ricci reaction terms.** Pointwise, the
Lichnerowicz Laplacian of Ricci is its rough Laplacian plus
`2 sum_ij Rm(X,e_i,W,e_j) Ric(e_i,e_j)` and minus
`2 sum_i Ric(X,e_i) Ric(e_i,W)`.  The first sum is the orthonormal-frame form
of the corrected term `2 g^{pq} g^{rs} R_{jpkr} Ric_{qs}`; the displayed
`R_{pjkr}` in Morgan--Tian is a source erratum. -/
theorem lichnerowiczLaplacian_ricciTensorField_apply_explicit
    (g : RiemannianMetric I M) (X W : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    lichnerowiczLaplacian g (ricciTensorField g)
        (fun i => if i = 0 then X else W) p =
      roughLaplacian g g.leviCivitaConnection (ricciTensorField g)
          (fun i => if i = 0 then X else W) p
        + 2 * ∑ i, ∑ j,
            g.leviCivitaConnection.curvatureFormAt g p
                (X p) (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
              ricciTensorAt g p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
                (stdOrthonormalBasis ℝ (TangentSpace I p) j)
        - 2 * ∑ i,
            ricciTensorAt g p (X p)
                (stdOrthonormalBasis ℝ (TangentSpace I p) i) *
              ricciTensorAt g p
                (stdOrthonormalBasis ℝ (TangentSpace I p) i) (W p) := by
  rw [lichnerowiczLaplacian_ricciTensorField_apply,
    inner_ricciEndomorphismAt_eq_sum]
  ring

#print axioms MorganTianLib.inner_ricciEndomorphismAt_eq_sum
#print axioms MorganTianLib.lichnerowiczLaplacian_ricciTensorField_apply_explicit

end MorganTianLib

end

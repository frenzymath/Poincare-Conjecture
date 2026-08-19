import Topping.Riemannian.CurvatureContractedBianchi
import Topping.Riemannian.RicciEvolution

/-!
# The curvature Laplacian formula

This module assembles the differentiated Bianchi identity, its Ricci trace,
and the rank-four Ricci commutator into Topping's formula for the rough
Laplacian of the Riemann tensor.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The corrected second covariant derivative preserves the symmetry
of the Ricci tensor in its two tensor slots. -/
theorem secondCovDerivAlong_ricciTensorField_symm
    (g : RiemannianMetric I M) (U V X Y : SmoothVectorField I M) (p : M) :
    secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![X, Y] p =
      secondCovDerivAlong g.leviCivitaConnection U V (ricciTensorField g)
        ![Y, X] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum,
    secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact secondCovDerivAlong_riemannTensorField_pairSwap g U V X
    (MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y
    (MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p

/-- **Math.** A field-level curvature action evaluated at a point is the
pointwise Riemann tensor applied to the pointwise curvature operator. -/
theorem curvatureForm_curvature_eq_riemannCurvatureAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g
        (g.leviCivitaConnection.curvature A B C) D F G p =
      riemannCurvatureAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p))
        (D p) (F p) (G p) := by
  rw [← curvatureOperator_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [riemannCurvature, curvatureOperator] using
    (riemannCurvatureAt_eq g p rfl rfl rfl rfl).symm

/-- **Math.** The same pointwise bridge with the curvature vector in the second
Riemann slot. -/
theorem curvatureForm_curvature_second_eq_riemannCurvatureAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g D
        (g.leviCivitaConnection.curvature A B C) F G p =
      riemannCurvatureAt g p (D p)
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p))
        (F p) (G p) := by
  rw [← curvatureOperator_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [riemannCurvature, curvatureOperator] using
    (riemannCurvatureAt_eq g p rfl rfl rfl rfl).symm

/-- **Math.** The same pointwise bridge with the curvature vector in the third
Riemann slot. -/
theorem curvatureForm_curvature_third_eq_riemannCurvatureAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g D F
        (g.leviCivitaConnection.curvature A B C) G p =
      riemannCurvatureAt g p (D p) (F p)
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p))
        (G p) := by
  rw [← curvatureOperator_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [riemannCurvature, curvatureOperator] using
    (riemannCurvatureAt_eq g p rfl rfl rfl rfl).symm

/-- **Math.** The same pointwise bridge with the curvature vector in the fourth
Riemann slot. -/
theorem curvatureForm_curvature_fourth_eq_riemannCurvatureAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g D F G
        (g.leviCivitaConnection.curvature A B C) p =
      riemannCurvatureAt g p (D p) (F p) (G p)
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p)) := by
  rw [← curvatureOperator_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [riemannCurvature, curvatureOperator] using
    (riemannCurvatureAt_eq g p rfl rfl rfl rfl).symm

/-- **Math.** Expanding a curvature vector in the first slot of the Riemann tensor over
the standard orthonormal basis. -/
theorem riemannCurvatureAt_curvatureOperatorAt_expand_first
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCurvatureAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) x y z =
      ∑ j, riemannCurvatureAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        riemannCurvatureAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) x y z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := riemannCurvatureAt_isAlg g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_left Finset.univ
    (fun j => inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j => e j) x y z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_curvatureOperatorAt_eq_riemannCurvatureAt]

/-- **Math.** Expanding a curvature vector in the second slot of the Riemann tensor over
the standard orthonormal basis. -/
theorem riemannCurvatureAt_curvatureOperatorAt_expand_second
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCurvatureAt g p x
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) y z =
      ∑ j, riemannCurvatureAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        riemannCurvatureAt g p x
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) y z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := riemannCurvatureAt_isAlg g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_two Finset.univ
    (fun j => inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j => e j) x y z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_curvatureOperatorAt_eq_riemannCurvatureAt]

/-- **Math.** Expanding a curvature vector in the third slot of the Riemann tensor over
the standard orthonormal basis. -/
theorem riemannCurvatureAt_curvatureOperatorAt_expand_third
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCurvatureAt g p x y
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) z =
      ∑ j, riemannCurvatureAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        riemannCurvatureAt g p x y
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := riemannCurvatureAt_isAlg g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_three Finset.univ
    (fun j => inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j => e j) x y z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_curvatureOperatorAt_eq_riemannCurvatureAt]

/-- **Math.** Expanding a curvature vector in the fourth slot of the Riemann tensor over
the standard orthonormal basis. -/
theorem riemannCurvatureAt_curvatureOperatorAt_expand_fourth
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    riemannCurvatureAt g p x y z
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) =
      ∑ j, riemannCurvatureAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        riemannCurvatureAt g p x y z
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := riemannCurvatureAt_isAlg g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_four Finset.univ
    (fun j => inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j => e j) x y z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_curvatureOperatorAt_eq_riemannCurvatureAt]

/-- **Math.** The trace of the curvature action in the first Riemann slot is
the difference of the two `B` contractions obtained by exchanging the last
free pair. -/
theorem sum_riemannCurvatureAt_curvatureOperatorAt_first
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, riemannCurvatureAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a b)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) c d =
      curvatureB g p a b c d - curvatureB g p a b d c := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := riemannCurvatureAt_isAlg g p
  change (∑ i, riemannCurvatureAt g p
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a b)
    (e i) c d) = _
  rw [Finset.sum_congr rfl fun i _ =>
    riemannCurvatureAt_curvatureOperatorAt_expand_first
      g p (e i) a b (e i) c d]
  let S := ∑ i, ∑ j, riemannCurvatureAt g p a (e i) b (e j) *
    riemannCurvatureAt g p c (e j) (e i) d
  have hsplit :
      (∑ i, ∑ j, riemannCurvatureAt g p (e i) a b (e j) *
        riemannCurvatureAt g p (e j) (e i) c d) =
      curvatureB g p a b c d + S := by
    simp only [curvatureB]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hb := halg.bianchi (e j) (e i) c d
    have hanti := halg.antisymm₁₂ (e i) c (e j) d
    have hq : riemannCurvatureAt g p (e j) (e i) c d =
        riemannCurvatureAt g p c (e i) (e j) d -
          riemannCurvatureAt g p c (e j) (e i) d := by
      linear_combination hb - hanti
    rw [halg.antisymm₁₂ (e i) a b (e j), hq,
      halg.antisymm₃₄ c (e i) (e j) d]
    ring
  have hcross : S = -curvatureB g p a b d c := by
    rw [← curvatureB_swap_within g p b a c d]
    dsimp [S]
    rw [Finset.sum_comm]
    simp only [curvatureB]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [halg.pairSwap a (e j) b (e i),
      halg.antisymm₃₄ c (e i) (e j) d]
    ring
  rw [hsplit, hcross]
  ring

/-- **Math.** Tracing the curvature action in the second Riemann slot gives
the Ricci tensor applied to the curvature vector in the two remaining slots. -/
theorem sum_riemannCurvatureAt_curvatureOperatorAt_second
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, riemannCurvatureAt g p b
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) c d =
      ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p c d b) a := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := riemannCurvatureAt_isAlg g p
  change (∑ i, riemannCurvatureAt g p b
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a (e i)) c d) =
    ricciTensorAt g p
      (g.leviCivitaConnection.curvatureOperatorAt p c d b) a
  rw [Finset.sum_congr rfl fun i _ =>
    riemannCurvatureAt_curvatureOperatorAt_expand_second
      g p (e i) a (e i) b c d]
  rw [ricciTensorAt_curvatureOperatorAt_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  have htrace : (∑ i, riemannCurvatureAt g p (e i) a (e i) (e j)) =
      ricciTensorAt g p (e j) a := by
    rw [ricciTensorAt_eq_sum g p (e j) a e]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [halg.antisymm₃₄ (e i) a (e i) (e j),
      halg.antisymm₁₂ (e i) a (e j) (e i),
      halg.pairSwap a (e i) (e j) (e i)]
    ring
  rw [htrace]
  rw [halg.pairSwap b (e j) c d]
  ring

/-- **Math.** The trace of the curvature action in the third Riemann slot is
the corresponding `B` contraction. -/
theorem sum_riemannCurvatureAt_curvatureOperatorAt_third
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, riemannCurvatureAt g p b
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a c) d =
      curvatureB g p a c b d := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := riemannCurvatureAt_isAlg g p
  change (∑ i, riemannCurvatureAt g p b (e i)
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a c) d) =
    curvatureB g p a c b d
  rw [Finset.sum_congr rfl fun i _ =>
    riemannCurvatureAt_curvatureOperatorAt_expand_third
      g p (e i) a c b (e i) d]
  simp only [curvatureB]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [halg.antisymm₁₂ (e i) a c (e j),
    halg.antisymm₃₄ b (e i) (e j) d]
  ring

/-- **Math.** The trace of the curvature action in the fourth Riemann slot is
the negative of the corresponding `B` contraction. -/
theorem sum_riemannCurvatureAt_curvatureOperatorAt_fourth
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, riemannCurvatureAt g p b
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) c
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a d) =
      -curvatureB g p a d b c := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := riemannCurvatureAt_isAlg g p
  change (∑ i, riemannCurvatureAt g p b (e i) c
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a d)) =
    -curvatureB g p a d b c
  rw [Finset.sum_congr rfl fun i _ =>
    riemannCurvatureAt_curvatureOperatorAt_expand_fourth
      g p (e i) a d b (e i) c]
  simp only [curvatureB]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [halg.antisymm₁₂ (e i) a d (e j)]
  ring

/-- **Math.** The four curvature actions arising when the derivative directions
`e_i` and `x` are commuted on `Rm(y,e_i,w,z)` trace to one Ricci term and the
four-term `B` combination in Topping's formula. -/
theorem sum_riemannCurvatureAt_curvatureActions_y_e
    (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x y)
          (e i) w z
        + riemannCurvatureAt g p y
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x (e i)) w z
        + riemannCurvatureAt g p y (e i)
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x w) z
        + riemannCurvatureAt g p y (e i) w
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x z)) =
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p w z y) x
        + (curvatureB g p x y w z - curvatureB g p x y z w
            + curvatureB g p x w y z - curvatureB g p x z y w) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  simp only [Finset.sum_add_distrib]
  rw [sum_riemannCurvatureAt_curvatureOperatorAt_first g p x y w z,
    sum_riemannCurvatureAt_curvatureOperatorAt_second g p x y w z,
    sum_riemannCurvatureAt_curvatureOperatorAt_third g p x y w z,
    sum_riemannCurvatureAt_curvatureOperatorAt_fourth g p x y w z]
  ring

/-- **Math.** The four curvature actions arising when the derivative directions
`e_i` and `y` are commuted on `Rm(e_i,x,w,z)` give the other Ricci term and the
same four-term `B` combination. -/
theorem sum_riemannCurvatureAt_curvatureActions_e_x
    (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i))
          x w z
        + riemannCurvatureAt g p (e i)
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z
        + riemannCurvatureAt g p (e i) x
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z
        + riemannCurvatureAt g p (e i) x w
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z)) =
      -ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p w z x) y
        + (curvatureB g p x y w z - curvatureB g p x y z w
            + curvatureB g p x w y z - curvatureB g p x z y w) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := riemannCurvatureAt_isAlg g p
  dsimp only
  change (∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i))
          x w z
        + riemannCurvatureAt g p (e i)
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z
        + riemannCurvatureAt g p (e i) x
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z
        + riemannCurvatureAt g p (e i) x w
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z))) = _
  have h₁ : (∑ i, riemannCurvatureAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i)) x w z) =
      -ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p w z x) y := by
    rw [Finset.sum_congr rfl fun i _ => halg.antisymm₁₂
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i)) x w z,
      Finset.sum_neg_distrib,
      sum_riemannCurvatureAt_curvatureOperatorAt_second g p y x w z]
  have h₂ : (∑ i, riemannCurvatureAt g p (e i)
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z) =
      curvatureB g p x y w z - curvatureB g p x y z w := by
    rw [Finset.sum_congr rfl fun i _ => halg.antisymm₁₂ (e i)
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z,
      Finset.sum_neg_distrib,
      sum_riemannCurvatureAt_curvatureOperatorAt_first g p y x w z,
      curvatureB_swap_within g p y x w z,
      curvatureB_swap_within g p y x z w]
    ring
  have h₃ : (∑ i, riemannCurvatureAt g p (e i) x
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z) =
      -curvatureB g p x z y w := by
    rw [Finset.sum_congr rfl fun i _ => halg.antisymm₁₂ (e i) x
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z,
      Finset.sum_neg_distrib,
      sum_riemannCurvatureAt_curvatureOperatorAt_third g p y x w z,
      curvatureB_swap_pairs g p y w x z]
  have h₄ : (∑ i, riemannCurvatureAt g p (e i) x w
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z)) =
      curvatureB g p x w y z := by
    rw [Finset.sum_congr rfl fun i _ => halg.antisymm₁₂ (e i) x w
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z),
      Finset.sum_neg_distrib,
      sum_riemannCurvatureAt_curvatureOperatorAt_fourth g p y x w z,
      curvatureB_swap_pairs g p y z x w]
    ring
  simp only [Finset.sum_add_distrib]
  rw [h₁, h₂, h₃, h₄]
  ring

/-- **Math.** Commuting the two derivative directions in the first traced
cross term produces the four curvature actions. -/
theorem sum_secondCovDerivAlong_riemannTensorField_commute_y_e
    (g : RiemannianMetric I M)
    (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    ∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) X
        (riemannTensorField g) ![Y, e i, W, Z] p =
      ∑ i, (secondCovDerivAlong g.leviCivitaConnection X (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p
        + g.leviCivitaConnection.curvatureForm g
            (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
        + g.leviCivitaConnection.curvatureForm g Y
            (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i)
            (g.leviCivitaConnection.curvature (e i) X W) Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i) W
            (g.leviCivitaConnection.curvature (e i) X Z) p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) X
        (riemannTensorField g) ![Y, e i, W, Z] p) = _
  apply Finset.sum_congr rfl
  intro i hi
  have h := secondCovDerivAlong_riemannTensorField_sub_swap
    g (e i) X ![Y, e i, W, Z] p
  change secondCovDerivAlong g.leviCivitaConnection (e i) X
      (riemannTensorField g) ![Y, e i, W, Z] p -
      secondCovDerivAlong g.leviCivitaConnection X (e i)
        (riemannTensorField g) ![Y, e i, W, Z] p =
    g.leviCivitaConnection.curvatureForm g
        (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
      + g.leviCivitaConnection.curvatureForm g Y
          (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
      + g.leviCivitaConnection.curvatureForm g Y (e i)
          (g.leviCivitaConnection.curvature (e i) X W) Z p
      + g.leviCivitaConnection.curvatureForm g Y (e i) W
          (g.leviCivitaConnection.curvature (e i) X Z) p at h
  linear_combination h

/-- **Math.** Commuting the two derivative directions in the second traced
cross term produces its four curvature actions. -/
theorem sum_secondCovDerivAlong_riemannTensorField_commute_e_x
    (g : RiemannianMetric I M)
    (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    ∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) Y
        (riemannTensorField g) ![e i, X, W, Z] p =
      ∑ i, (secondCovDerivAlong g.leviCivitaConnection Y (e i)
          (riemannTensorField g) ![e i, X, W, Z] p
        + g.leviCivitaConnection.curvatureForm g
            (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
        + g.leviCivitaConnection.curvatureForm g (e i)
            (g.leviCivitaConnection.curvature (e i) Y X) W Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X
            (g.leviCivitaConnection.curvature (e i) Y W) Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X W
            (g.leviCivitaConnection.curvature (e i) Y Z) p) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) Y
        (riemannTensorField g) ![e i, X, W, Z] p) = _
  apply Finset.sum_congr rfl
  intro i hi
  have h := secondCovDerivAlong_riemannTensorField_sub_swap
    g (e i) Y ![e i, X, W, Z] p
  change secondCovDerivAlong g.leviCivitaConnection (e i) Y
      (riemannTensorField g) ![e i, X, W, Z] p -
      secondCovDerivAlong g.leviCivitaConnection Y (e i)
        (riemannTensorField g) ![e i, X, W, Z] p =
    g.leviCivitaConnection.curvatureForm g
        (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
      + g.leviCivitaConnection.curvatureForm g (e i)
          (g.leviCivitaConnection.curvature (e i) Y X) W Z p
      + g.leviCivitaConnection.curvatureForm g (e i) X
          (g.leviCivitaConnection.curvature (e i) Y W) Z p
      + g.leviCivitaConnection.curvatureForm g (e i) X W
          (g.leviCivitaConnection.curvature (e i) Y Z) p at h
  linear_combination h

/-- **Math.** Field-level form of
`sum_riemannCurvatureAt_curvatureActions_y_e`, in the standard frame used by
the rough Laplacian. -/
theorem sum_curvatureForm_curvatureActions_y_e
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    ∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
        + g.leviCivitaConnection.curvatureForm g Y
          (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i)
          (g.leviCivitaConnection.curvature (e i) X W) Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i) W
          (g.leviCivitaConnection.curvature (e i) X Z) p) =
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (Y p))
          (X p)
        + (curvatureB g p (X p) (Y p) (W p) (Z p)
            - curvatureB g p (X p) (Y p) (Z p) (W p)
            + curvatureB g p (X p) (W p) (Y p) (Z p)
            - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  change (∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
        + g.leviCivitaConnection.curvatureForm g Y
          (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i)
          (g.leviCivitaConnection.curvature (e i) X W) Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i) W
          (g.leviCivitaConnection.curvature (e i) X Z) p)) = _
  have hsum :
      (∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) (Y p))
          ((e i) p) (W p) (Z p)
        + riemannCurvatureAt g p (Y p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) ((e i) p))
          (W p) (Z p)
        + riemannCurvatureAt g p (Y p) ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) (W p))
          (Z p)
        + riemannCurvatureAt g p (Y p) ((e i) p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) (Z p)))) =
        ricciTensorAt g p
            (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (Y p))
            (X p)
          + (curvatureB g p (X p) (Y p) (W p) (Z p)
              - curvatureB g p (X p) (Y p) (Z p) (W p)
              + curvatureB g p (X p) (W p) (Y p) (Z p)
              - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
    simpa only [e, MorganTianLib.extendVector_apply] using
      sum_riemannCurvatureAt_curvatureActions_y_e g p
        (X p) (Y p) (W p) (Z p)
  calc
    (∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
        + g.leviCivitaConnection.curvatureForm g Y
          (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i)
          (g.leviCivitaConnection.curvature (e i) X W) Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i) W
          (g.leviCivitaConnection.curvature (e i) X Z) p)) =
        ∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) (Y p))
          ((e i) p) (W p) (Z p)
        + riemannCurvatureAt g p (Y p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) ((e i) p))
          (W p) (Z p)
        + riemannCurvatureAt g p (Y p) ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) (W p))
          (Z p)
        + riemannCurvatureAt g p (Y p) ((e i) p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (X p) (Z p))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [curvatureForm_curvature_eq_riemannCurvatureAt_curvatureOperatorAt,
        curvatureForm_curvature_second_eq_riemannCurvatureAt_curvatureOperatorAt,
        curvatureForm_curvature_third_eq_riemannCurvatureAt_curvatureOperatorAt,
        curvatureForm_curvature_fourth_eq_riemannCurvatureAt_curvatureOperatorAt]
    _ = _ := hsum

/-- **Math.** Field-level form of
`sum_riemannCurvatureAt_curvatureActions_e_x`, in the standard frame used by
the rough Laplacian. -/
theorem sum_curvatureForm_curvatureActions_e_x
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i => MorganTianLib.extendVector p
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    ∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
        + g.leviCivitaConnection.curvatureForm g (e i)
          (g.leviCivitaConnection.curvature (e i) Y X) W Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X
          (g.leviCivitaConnection.curvature (e i) Y W) Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X W
          (g.leviCivitaConnection.curvature (e i) Y Z) p) =
      -ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (X p))
          (Y p)
        + (curvatureB g p (X p) (Y p) (W p) (Z p)
            - curvatureB g p (X p) (Y p) (Z p) (W p)
            + curvatureB g p (X p) (W p) (Y p) (Z p)
            - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  change (∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
        + g.leviCivitaConnection.curvatureForm g (e i)
          (g.leviCivitaConnection.curvature (e i) Y X) W Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X
          (g.leviCivitaConnection.curvature (e i) Y W) Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X W
          (g.leviCivitaConnection.curvature (e i) Y Z) p)) = _
  have hsum :
      (∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) ((e i) p))
          (X p) (W p) (Z p)
        + riemannCurvatureAt g p ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) (X p))
          (W p) (Z p)
        + riemannCurvatureAt g p ((e i) p) (X p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) (W p))
          (Z p)
        + riemannCurvatureAt g p ((e i) p) (X p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) (Z p)))) =
        -ricciTensorAt g p
            (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (X p))
            (Y p)
          + (curvatureB g p (X p) (Y p) (W p) (Z p)
              - curvatureB g p (X p) (Y p) (Z p) (W p)
              + curvatureB g p (X p) (W p) (Y p) (Z p)
              - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
    simpa only [e, MorganTianLib.extendVector_apply] using
      sum_riemannCurvatureAt_curvatureActions_e_x g p
        (X p) (Y p) (W p) (Z p)
  calc
    (∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
        + g.leviCivitaConnection.curvatureForm g (e i)
          (g.leviCivitaConnection.curvature (e i) Y X) W Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X
          (g.leviCivitaConnection.curvature (e i) Y W) Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X W
          (g.leviCivitaConnection.curvature (e i) Y Z) p)) =
        ∑ i, (riemannCurvatureAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) ((e i) p))
          (X p) (W p) (Z p)
        + riemannCurvatureAt g p ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) (X p))
          (W p) (Z p)
        + riemannCurvatureAt g p ((e i) p) (X p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) (W p))
          (Z p)
        + riemannCurvatureAt g p ((e i) p) (X p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p ((e i) p) (Y p) (Z p))) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [curvatureForm_curvature_eq_riemannCurvatureAt_curvatureOperatorAt,
        curvatureForm_curvature_second_eq_riemannCurvatureAt_curvatureOperatorAt,
        curvatureForm_curvature_third_eq_riemannCurvatureAt_curvatureOperatorAt,
        curvatureForm_curvature_fourth_eq_riemannCurvatureAt_curvatureOperatorAt]
    _ = _ := hsum

/-- **Math.** The curvature Laplacian identity (Topping (2.4.1)), with its
tensor slots written as explicit tuples. -/
theorem curvatureLaplacianFormula_explicit
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
        ![X, Y, W, Z] p =
      -secondCovDerivAlong g.leviCivitaConnection Y W (ricciTensorField g)
          ![X, Z] p
        + secondCovDerivAlong g.leviCivitaConnection X W (ricciTensorField g)
            ![Y, Z] p
        - secondCovDerivAlong g.leviCivitaConnection X Z (ricciTensorField g)
            ![Y, W] p
        + secondCovDerivAlong g.leviCivitaConnection Y Z (ricciTensorField g)
            ![X, W] p
        - ricciTensorAt g p
            (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (Y p))
            (X p)
        + ricciTensorAt g p
            (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (X p))
            (Y p)
        - 2 * (curvatureB g p (X p) (Y p) (W p) (Z p)
            - curvatureB g p (X p) (Y p) (Z p) (W p)
            + curvatureB g p (X p) (W p) (Y p) (Z p)
            - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  have hrough :=
    roughLaplacian_riemannTensorField_eq_neg_cyclic_cross_sum g X Y W Z p
  dsimp only at hrough
  change roughLaplacian g g.leviCivitaConnection (riemannTensorField g)
      ![X, Y, W, Z] p =
    -∑ i, (secondCovDerivAlong g.leviCivitaConnection (e i) X
        (riemannTensorField g) ![Y, e i, W, Z] p
      + secondCovDerivAlong g.leviCivitaConnection (e i) Y
        (riemannTensorField g) ![e i, X, W, Z] p) at hrough
  have hcommX :=
    sum_secondCovDerivAlong_riemannTensorField_commute_y_e g X Y W Z p
  dsimp only at hcommX
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) X
        (riemannTensorField g) ![Y, e i, W, Z] p) =
      ∑ i, (secondCovDerivAlong g.leviCivitaConnection X (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p
        + g.leviCivitaConnection.curvatureForm g
            (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
        + g.leviCivitaConnection.curvatureForm g Y
            (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i)
            (g.leviCivitaConnection.curvature (e i) X W) Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i) W
            (g.leviCivitaConnection.curvature (e i) X Z) p) at hcommX
  have hcommY :=
    sum_secondCovDerivAlong_riemannTensorField_commute_e_x g X Y W Z p
  dsimp only at hcommY
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) Y
        (riemannTensorField g) ![e i, X, W, Z] p) =
      ∑ i, (secondCovDerivAlong g.leviCivitaConnection Y (e i)
          (riemannTensorField g) ![e i, X, W, Z] p
        + g.leviCivitaConnection.curvatureForm g
            (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
        + g.leviCivitaConnection.curvatureForm g (e i)
            (g.leviCivitaConnection.curvature (e i) Y X) W Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X
            (g.leviCivitaConnection.curvature (e i) Y W) Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X W
            (g.leviCivitaConnection.curvature (e i) Y Z) p) at hcommY
  have htraceX :=
    secondCovDerivAlong_riemannTensorField_contracted_first_pair g X Y W Z p
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection X (e i)
        (riemannTensorField g) ![Y, e i, W, Z] p) =
      secondCovDerivAlong g.leviCivitaConnection X Z (ricciTensorField g)
        ![W, Y] p -
      secondCovDerivAlong g.leviCivitaConnection X W (ricciTensorField g)
        ![Z, Y] p at htraceX
  have htraceY :=
    secondCovDerivAlong_riemannTensorField_contracted_first_pair g Y X W Z p
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection Y (e i)
        (riemannTensorField g) ![X, e i, W, Z] p) =
      secondCovDerivAlong g.leviCivitaConnection Y Z (ricciTensorField g)
        ![W, X] p -
      secondCovDerivAlong g.leviCivitaConnection Y W (ricciTensorField g)
        ![Z, X] p at htraceY
  have hanti :
      (∑ i, secondCovDerivAlong g.leviCivitaConnection Y (e i)
        (riemannTensorField g) ![e i, X, W, Z] p) =
      -∑ i, secondCovDerivAlong g.leviCivitaConnection Y (e i)
        (riemannTensorField g) ![X, e i, W, Z] p := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact secondCovDerivAlong_riemannTensorField_antisymm_firstPair
      g Y (e i) (e i) X W Z p
  have hquadX := sum_curvatureForm_curvatureActions_y_e g X Y W Z p
  dsimp only at hquadX
  change (∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) X Y) (e i) W Z p
        + g.leviCivitaConnection.curvatureForm g Y
          (g.leviCivitaConnection.curvature (e i) X (e i)) W Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i)
          (g.leviCivitaConnection.curvature (e i) X W) Z p
        + g.leviCivitaConnection.curvatureForm g Y (e i) W
          (g.leviCivitaConnection.curvature (e i) X Z) p)) =
      ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (Y p))
          (X p) +
        (curvatureB g p (X p) (Y p) (W p) (Z p)
          - curvatureB g p (X p) (Y p) (Z p) (W p)
          + curvatureB g p (X p) (W p) (Y p) (Z p)
          - curvatureB g p (X p) (Z p) (Y p) (W p)) at hquadX
  have hquadY := sum_curvatureForm_curvatureActions_e_x g X Y W Z p
  dsimp only at hquadY
  change (∑ i, (g.leviCivitaConnection.curvatureForm g
          (g.leviCivitaConnection.curvature (e i) Y (e i)) X W Z p
        + g.leviCivitaConnection.curvatureForm g (e i)
          (g.leviCivitaConnection.curvature (e i) Y X) W Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X
          (g.leviCivitaConnection.curvature (e i) Y W) Z p
        + g.leviCivitaConnection.curvatureForm g (e i) X W
          (g.leviCivitaConnection.curvature (e i) Y Z) p)) =
      -ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (X p))
          (Y p) +
        (curvatureB g p (X p) (Y p) (W p) (Z p)
          - curvatureB g p (X p) (Y p) (Z p) (W p)
          + curvatureB g p (X p) (W p) (Y p) (Z p)
          - curvatureB g p (X p) (Z p) (Y p) (W p)) at hquadY
  have hsymXZ := secondCovDerivAlong_ricciTensorField_symm g X Z W Y p
  have hsymXW := secondCovDerivAlong_ricciTensorField_symm g X W Z Y p
  have hsymYZ := secondCovDerivAlong_ricciTensorField_symm g Y Z W X p
  have hsymYW := secondCovDerivAlong_ricciTensorField_symm g Y W Z X p
  simp only [Finset.sum_add_distrib] at hrough hcommX hcommY hquadX hquadY
  linarith only [hrough, hcommX, hcommY, htraceX, htraceY, hanti,
    hquadX, hquadY, hsymXZ, hsymXW, hsymYZ, hsymYW]

/-- **Math.** The curvature Laplacian identity (Topping (2.4.1)) holds for every
Riemannian metric. -/
theorem hasCurvatureLaplacianFormula
    (g : RiemannianMetric I M) : HasCurvatureLaplacianFormula g := by
  intro X Y W Z p
  have hfour :
      (fun i : Fin 4 => if i = 0 then X else if i = 1 then Y else
        if i = 2 then W else Z) = ![X, Y, W, Z] := by
    funext i
    fin_cases i <;> rfl
  have hXZ : (fun i : Fin 2 => if i = 0 then X else Z) = ![X, Z] := by
    funext i
    fin_cases i <;> rfl
  have hYZ : (fun i : Fin 2 => if i = 0 then Y else Z) = ![Y, Z] := by
    funext i
    fin_cases i <;> rfl
  have hYW : (fun i : Fin 2 => if i = 0 then Y else W) = ![Y, W] := by
    funext i
    fin_cases i <;> rfl
  have hXW : (fun i : Fin 2 => if i = 0 then X else W) = ![X, W] := by
    funext i
    fin_cases i <;> rfl
  rw [hfour, hXZ, hYZ, hYW, hXW,
    curvatureOperator_apply_eq_curvatureOperatorAt,
    curvatureOperator_apply_eq_curvatureOperatorAt]
  exact curvatureLaplacianFormula_explicit g X Y W Z p

#print axioms Topping.curvatureLaplacianFormula_explicit
#print axioms Topping.hasCurvatureLaplacianFormula

end Topping

end

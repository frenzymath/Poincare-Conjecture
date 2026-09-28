import MorganTianLib.Ch03.RicciFlow.CurvatureRicciTrace
import MorganTianLib.Ch03.RicciFlow.RicciLaplacian

/-!
# Morgan--Tian Ch. 3 - the curvature Laplacian formula

This module assembles the differentiated Bianchi identity, its Ricci trace,
and the rank-four Ricci commutator into the pointwise formula for the rough
Laplacian of the Riemann tensor.  All curvature contractions are written in
Morgan--Tian's local `curvatureFormAt` and `curvatureB` convention.
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

/-! ### The differentiated Ricci trace -/

/-- **Math.** The corrected second covariant derivative preserves symmetry in
the two Ricci slots. -/
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
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact secondCovDerivAlong_riemannTensorField_pairSwap g U V X
    (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) Y
    (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) p

/-- **Math.** Contracting the differentiated second Bianchi identity gives
`sum_i nabla²(U,e_i)Rm(Y,e_i,W,Z)
  = nabla²(U,Z)Ric(W,Y) - nabla²(U,W)Ric(Z,Y)`. -/
theorem secondCovDerivAlong_riemannTensorField_contracted_first_pair
    (g : RiemannianMetric I M) (U Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, secondCovDerivAlong g.leviCivitaConnection U
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i))
      (riemannTensorField g)
      ![Y, extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i), W, Z] p =
      secondCovDerivAlong g.leviCivitaConnection U Z (ricciTensorField g)
        ![W, Y] p -
      secondCovDerivAlong g.leviCivitaConnection U W (ricciTensorField g)
        ![Z, Y] p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
    fun i ↦ extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  have hcyc (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![W, Z, Y, e i] p
        + secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p
        + secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![e i, W, Y, e i] p = 0 := by
    exact secondCovDerivAlong_riemannTensorField_cyclic_first_pair
      g U (e i) W Z Y (e i) p
  have hpair (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![W, Z, Y, e i] p =
        secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p := by
    exact secondCovDerivAlong_riemannTensorField_pairSwap
      g U (e i) W Z Y (e i) p
  have hanti (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![e i, W, Y, e i] p =
        -secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p := by
    exact secondCovDerivAlong_riemannTensorField_antisymm_firstPair
      g U Z (e i) W Y (e i) p
  have hterm (i : Fin (Module.finrank ℝ E)) :
      secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p
        + secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p
        - secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p = 0 := by
    have h := hcyc i
    rw [hpair i, hanti i] at h
    simpa [sub_eq_add_neg] using h
  change
    (∑ i, secondCovDerivAlong g.leviCivitaConnection U (e i)
      (riemannTensorField g) ![Y, e i, W, Z] p) =
      secondCovDerivAlong g.leviCivitaConnection U Z (ricciTensorField g)
        ![W, Y] p -
      secondCovDerivAlong g.leviCivitaConnection U W (ricciTensorField g)
        ![Z, Y] p
  have hsum :
      ∑ i, (secondCovDerivAlong g.leviCivitaConnection U (e i)
          (riemannTensorField g) ![Y, e i, W, Z] p
        + secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p
        - secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hterm i
  have hsum' := hsum
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib] at hsum'
  have htraceZ :
      secondCovDerivAlong g.leviCivitaConnection U Z (ricciTensorField g)
          ![W, Y] p =
        ∑ i, secondCovDerivAlong g.leviCivitaConnection U Z
          (riemannTensorField g) ![W, e i, Y, e i] p := by
    dsimp [e]
    exact secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
      g U Z W Y p
  have htraceW :
      secondCovDerivAlong g.leviCivitaConnection U W (ricciTensorField g)
          ![Z, Y] p =
        ∑ i, secondCovDerivAlong g.leviCivitaConnection U W
          (riemannTensorField g) ![Z, e i, Y, e i] p := by
    dsimp [e]
    exact secondCovDerivAlong_ricciTensorField_eq_stdOrthonormalBasis_sum
      g U W Z Y p
  rw [htraceZ, htraceW]
  linear_combination hsum'

/-! ### Pointwise curvature-action contractions -/

private theorem curvatureFormAt_isAlg_local
    (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    IsAlgCurvatureForm (g.leviCivitaConnection.curvatureFormAt g p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g
    (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q ↦ g.koszulDualSection_dual X Y W q)) p

private theorem ricciTensorAt_eq_curvatureFormAt_sum
    (g : RiemannianMetric I M) (p : M) (x y : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I p)),
      ricciTensorAt g p x y =
        ∑ i, g.leviCivitaConnection.curvatureFormAt g p x (e i) y (e i) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro ι _ e
  simpa [ricciTensorAt, Riemannian.ricciBilin_apply] using
    Riemannian.ricciForm_eq_sum (curvatureFormAt_isAlg_local g p) x y e

private theorem curvatureForm_curvature_eq_curvatureFormAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g
        (g.leviCivitaConnection.curvature A B C) D F G p =
      g.leviCivitaConnection.curvatureFormAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p))
        (D p) (F p) (G p) := by
  rw [← curvatureOperatorField_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [curvatureOperatorField] using
    (g.leviCivitaConnection.curvatureFormAt_eq g p rfl rfl rfl rfl).symm

private theorem curvatureForm_curvature_second_eq_curvatureFormAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g D
        (g.leviCivitaConnection.curvature A B C) F G p =
      g.leviCivitaConnection.curvatureFormAt g p (D p)
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p))
        (F p) (G p) := by
  rw [← curvatureOperatorField_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [curvatureOperatorField] using
    (g.leviCivitaConnection.curvatureFormAt_eq g p rfl rfl rfl rfl).symm

private theorem curvatureForm_curvature_third_eq_curvatureFormAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g D F
        (g.leviCivitaConnection.curvature A B C) G p =
      g.leviCivitaConnection.curvatureFormAt g p (D p) (F p)
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p))
        (G p) := by
  rw [← curvatureOperatorField_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [curvatureOperatorField] using
    (g.leviCivitaConnection.curvatureFormAt_eq g p rfl rfl rfl rfl).symm

private theorem curvatureForm_curvature_fourth_eq_curvatureFormAt_curvatureOperatorAt
    (g : RiemannianMetric I M)
    (A B C D F G : SmoothVectorField I M) (p : M) :
    g.leviCivitaConnection.curvatureForm g D F G
        (g.leviCivitaConnection.curvature A B C) p =
      g.leviCivitaConnection.curvatureFormAt g p (D p) (F p) (G p)
        (g.leviCivitaConnection.curvatureOperatorAt p (A p) (B p) (C p)) := by
  rw [← curvatureOperatorField_apply_eq_curvatureOperatorAt g A B C p]
  simpa only [curvatureOperatorField] using
    (g.leviCivitaConnection.curvatureFormAt_eq g p rfl rfl rfl rfl).symm

private theorem curvatureFormAt_curvatureOperatorAt_expand_first
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    g.leviCivitaConnection.curvatureFormAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) x y z =
      ∑ j, g.leviCivitaConnection.curvatureFormAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        g.leviCivitaConnection.curvatureFormAt g p
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) x y z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := curvatureFormAt_isAlg_local g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_left Finset.univ
    (fun j ↦ inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j ↦ e j) x y z]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_curvatureOperatorAt_eq_curvatureFormAt]

private theorem curvatureFormAt_curvatureOperatorAt_expand_second
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    g.leviCivitaConnection.curvatureFormAt g p x
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) y z =
      ∑ j, g.leviCivitaConnection.curvatureFormAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        g.leviCivitaConnection.curvatureFormAt g p x
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) y z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := curvatureFormAt_isAlg_local g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_two Finset.univ
    (fun j ↦ inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j ↦ e j) x y z]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_curvatureOperatorAt_eq_curvatureFormAt]

private theorem curvatureFormAt_curvatureOperatorAt_expand_third
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    g.leviCivitaConnection.curvatureFormAt g p x y
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) z =
      ∑ j, g.leviCivitaConnection.curvatureFormAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        g.leviCivitaConnection.curvatureFormAt g p x y
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) z := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := curvatureFormAt_isAlg_local g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_three Finset.univ
    (fun j ↦ inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j ↦ e j) x y z]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_curvatureOperatorAt_eq_curvatureFormAt]

private theorem curvatureFormAt_curvatureOperatorAt_expand_fourth
    (g : RiemannianMetric I M) (p : M)
    (a b c x y z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    g.leviCivitaConnection.curvatureFormAt g p x y z
        (g.leviCivitaConnection.curvatureOperatorAt p a b c) =
      ∑ j, g.leviCivitaConnection.curvatureFormAt g p a b c
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) *
        g.leviCivitaConnection.curvatureFormAt g p x y z
          (stdOrthonormalBasis ℝ (TangentSpace I p) j) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hexp := sum_inner_smul_stdOrthonormalBasis g p
    (g.leviCivitaConnection.curvatureOperatorAt p a b c)
  have halg := curvatureFormAt_isAlg_local g p
  conv_lhs => rw [← hexp]
  rw [halg.sum_four Finset.univ
    (fun j ↦ inner ℝ (e j)
      (g.leviCivitaConnection.curvatureOperatorAt p a b c))
    (fun j ↦ e j) x y z]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [inner_curvatureOperatorAt_eq_curvatureFormAt]

private theorem sum_curvatureFormAt_curvatureOperatorAt_first
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.leviCivitaConnection.curvatureFormAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a b)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) c d =
      curvatureB g p a b c d - curvatureB g p a b d c := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_local g p
  change (∑ i, g.leviCivitaConnection.curvatureFormAt g p
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a b)
    (e i) c d) = _
  rw [Finset.sum_congr rfl fun i _ ↦
    curvatureFormAt_curvatureOperatorAt_expand_first
      g p (e i) a b (e i) c d]
  let S := ∑ i, ∑ j,
    g.leviCivitaConnection.curvatureFormAt g p a (e i) b (e j) *
      g.leviCivitaConnection.curvatureFormAt g p c (e j) (e i) d
  have hsplit :
      (∑ i, ∑ j,
        g.leviCivitaConnection.curvatureFormAt g p (e i) a b (e j) *
          g.leviCivitaConnection.curvatureFormAt g p (e j) (e i) c d) =
      curvatureB g p a b c d + S := by
    simp only [curvatureB]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hb := halg.bianchi (e j) (e i) c d
    have hanti := halg.antisymm₁₂ (e i) c (e j) d
    have hq : g.leviCivitaConnection.curvatureFormAt g p (e j) (e i) c d =
        g.leviCivitaConnection.curvatureFormAt g p c (e i) (e j) d -
          g.leviCivitaConnection.curvatureFormAt g p c (e j) (e i) d := by
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
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [halg.pairSwap a (e j) b (e i),
      halg.antisymm₃₄ c (e i) (e j) d]
    ring
  rw [hsplit, hcross]
  ring

private theorem sum_curvatureFormAt_curvatureOperatorAt_second
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.leviCivitaConnection.curvatureFormAt g p b
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a
          (stdOrthonormalBasis ℝ (TangentSpace I p) i)) c d =
      ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p c d b) a := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_local g p
  change (∑ i, g.leviCivitaConnection.curvatureFormAt g p b
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a (e i)) c d) =
    ricciTensorAt g p
      (g.leviCivitaConnection.curvatureOperatorAt p c d b) a
  rw [Finset.sum_congr rfl fun i _ ↦
    curvatureFormAt_curvatureOperatorAt_expand_second
      g p (e i) a (e i) b c d]
  rw [ricciTensorAt_curvatureOperatorAt_expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← Finset.sum_mul]
  have htrace :
      (∑ i, g.leviCivitaConnection.curvatureFormAt g p
        (e i) a (e i) (e j)) = ricciTensorAt g p (e j) a := by
    rw [ricciTensorAt_eq_curvatureFormAt_sum g p (e j) a e]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [halg.antisymm₃₄ (e i) a (e i) (e j),
      halg.antisymm₁₂ (e i) a (e j) (e i),
      halg.pairSwap a (e i) (e j) (e i)]
    ring
  rw [htrace]
  rw [halg.pairSwap b (e j) c d]
  ring

private theorem sum_curvatureFormAt_curvatureOperatorAt_third
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.leviCivitaConnection.curvatureFormAt g p b
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a c) d =
      curvatureB g p a c b d := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_local g p
  change (∑ i, g.leviCivitaConnection.curvatureFormAt g p b (e i)
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a c) d) =
    curvatureB g p a c b d
  rw [Finset.sum_congr rfl fun i _ ↦
    curvatureFormAt_curvatureOperatorAt_expand_third
      g p (e i) a c b (e i) d]
  simp only [curvatureB]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [halg.antisymm₁₂ (e i) a c (e j),
    halg.antisymm₃₄ b (e i) (e j) d]
  ring

private theorem sum_curvatureFormAt_curvatureOperatorAt_fourth
    (g : RiemannianMetric I M) (p : M)
    (a b c d : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.leviCivitaConnection.curvatureFormAt g p b
        (stdOrthonormalBasis ℝ (TangentSpace I p) i) c
        (g.leviCivitaConnection.curvatureOperatorAt p
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) a d) =
      -curvatureB g p a d b c := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_local g p
  change (∑ i, g.leviCivitaConnection.curvatureFormAt g p b (e i) c
    (g.leviCivitaConnection.curvatureOperatorAt p (e i) a d)) =
    -curvatureB g p a d b c
  rw [Finset.sum_congr rfl fun i _ ↦
    curvatureFormAt_curvatureOperatorAt_expand_fourth
      g p (e i) a d b (e i) c]
  simp only [curvatureB]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [halg.antisymm₁₂ (e i) a d (e j)]
  ring

/-- **Math.** The four curvature actions produced by commuting `e_i` and `x`
on `Rm(y,e_i,w,z)` trace to one Ricci term and Morgan--Tian's four-term
`B` combination. -/
theorem sum_curvatureFormAt_curvatureActions_y_e
    (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x y)
          (e i) w z
        + g.leviCivitaConnection.curvatureFormAt g p y
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x (e i)) w z
        + g.leviCivitaConnection.curvatureFormAt g p y (e i)
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) x w) z
        + g.leviCivitaConnection.curvatureFormAt g p y (e i) w
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
  rw [sum_curvatureFormAt_curvatureOperatorAt_first g p x y w z,
    sum_curvatureFormAt_curvatureOperatorAt_second g p x y w z,
    sum_curvatureFormAt_curvatureOperatorAt_third g p x y w z,
    sum_curvatureFormAt_curvatureOperatorAt_fourth g p x y w z]
  ring

/-- **Math.** The four curvature actions produced by commuting `e_i` and `y`
on `Rm(e_i,x,w,z)` give the other Ricci term and the same four-term
`B` combination. -/
theorem sum_curvatureFormAt_curvatureActions_e_x
    (g : RiemannianMetric I M) (p : M)
    (x y w z : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i))
          x w z
        + g.leviCivitaConnection.curvatureFormAt g p (e i)
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z
        + g.leviCivitaConnection.curvatureFormAt g p (e i) x
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z
        + g.leviCivitaConnection.curvatureFormAt g p (e i) x w
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z)) =
      -ricciTensorAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p w z x) y
        + (curvatureB g p x y w z - curvatureB g p x y z w
            + curvatureB g p x w y z - curvatureB g p x z y w) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have halg := curvatureFormAt_isAlg_local g p
  dsimp only
  change (∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i))
          x w z
        + g.leviCivitaConnection.curvatureFormAt g p (e i)
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z
        + g.leviCivitaConnection.curvatureFormAt g p (e i) x
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z
        + g.leviCivitaConnection.curvatureFormAt g p (e i) x w
          (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z))) = _
  have h₁ : (∑ i, g.leviCivitaConnection.curvatureFormAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i)) x w z) =
      -ricciTensorAt g p
        (g.leviCivitaConnection.curvatureOperatorAt p w z x) y := by
    rw [Finset.sum_congr rfl fun i _ ↦ halg.antisymm₁₂
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y (e i)) x w z,
      Finset.sum_neg_distrib,
      sum_curvatureFormAt_curvatureOperatorAt_second g p y x w z]
  have h₂ : (∑ i, g.leviCivitaConnection.curvatureFormAt g p (e i)
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z) =
      curvatureB g p x y w z - curvatureB g p x y z w := by
    rw [Finset.sum_congr rfl fun i _ ↦ halg.antisymm₁₂ (e i)
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y x) w z,
      Finset.sum_neg_distrib,
      sum_curvatureFormAt_curvatureOperatorAt_first g p y x w z,
      curvatureB_swap_within g p y x w z,
      curvatureB_swap_within g p y x z w]
    ring
  have h₃ : (∑ i, g.leviCivitaConnection.curvatureFormAt g p (e i) x
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z) =
      -curvatureB g p x z y w := by
    rw [Finset.sum_congr rfl fun i _ ↦ halg.antisymm₁₂ (e i) x
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y w) z,
      Finset.sum_neg_distrib,
      sum_curvatureFormAt_curvatureOperatorAt_third g p y x w z,
      curvatureB_swap_pairs g p y w x z]
  have h₄ : (∑ i, g.leviCivitaConnection.curvatureFormAt g p (e i) x w
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z)) =
      curvatureB g p x w y z := by
    rw [Finset.sum_congr rfl fun i _ ↦ halg.antisymm₁₂ (e i) x w
        (g.leviCivitaConnection.curvatureOperatorAt p (e i) y z),
      Finset.sum_neg_distrib,
      sum_curvatureFormAt_curvatureOperatorAt_fourth g p y x w z,
      curvatureB_swap_pairs g p y z x w]
    ring
  simp only [Finset.sum_add_distrib]
  rw [h₁, h₂, h₃, h₄]
  ring

/-! ### Commuted derivative traces -/

private theorem sum_secondCovDerivAlong_riemannTensorField_commute_y_e
    (g : RiemannianMetric I M)
    (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i ↦ extendVector p
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
    fun i ↦ extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) X
        (riemannTensorField g) ![Y, e i, W, Z] p) = _
  apply Finset.sum_congr rfl
  intro i _
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

private theorem sum_secondCovDerivAlong_riemannTensorField_commute_e_x
    (g : RiemannianMetric I M)
    (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i ↦ extendVector p
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
    fun i ↦ extendVector p
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)
  change (∑ i, secondCovDerivAlong g.leviCivitaConnection (e i) Y
        (riemannTensorField g) ![e i, X, W, Z] p) = _
  apply Finset.sum_congr rfl
  intro i _
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

private theorem sum_curvatureForm_curvatureActions_y_e
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i ↦ extendVector p
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
    fun i ↦ extendVector p
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
      (∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) (Y p))
          ((e i) p) (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p (Y p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) ((e i) p))
          (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p (Y p) ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) (W p))
          (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p (Y p) ((e i) p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) (Z p)))) =
        ricciTensorAt g p
            (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (Y p))
            (X p)
          + (curvatureB g p (X p) (Y p) (W p) (Z p)
              - curvatureB g p (X p) (Y p) (Z p) (W p)
              + curvatureB g p (X p) (W p) (Y p) (Z p)
              - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
    simpa only [e, extendVector_apply] using
      sum_curvatureFormAt_curvatureActions_y_e g p
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
        ∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) (Y p))
          ((e i) p) (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p (Y p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) ((e i) p))
          (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p (Y p) ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) (W p))
          (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p (Y p) ((e i) p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (X p) (Z p))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [curvatureForm_curvature_eq_curvatureFormAt_curvatureOperatorAt,
        curvatureForm_curvature_second_eq_curvatureFormAt_curvatureOperatorAt,
        curvatureForm_curvature_third_eq_curvatureFormAt_curvatureOperatorAt,
        curvatureForm_curvature_fourth_eq_curvatureFormAt_curvatureOperatorAt]
    _ = _ := hsum

private theorem sum_curvatureForm_curvatureActions_e_x
    (g : RiemannianMetric I M) (X Y W Z : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let e : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M :=
      fun i ↦ extendVector p
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
    fun i ↦ extendVector p
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
      (∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) ((e i) p))
          (X p) (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) (X p))
          (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p ((e i) p) (X p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) (W p))
          (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p ((e i) p) (X p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) (Z p)))) =
        -ricciTensorAt g p
            (g.leviCivitaConnection.curvatureOperatorAt p (W p) (Z p) (X p))
            (Y p)
          + (curvatureB g p (X p) (Y p) (W p) (Z p)
              - curvatureB g p (X p) (Y p) (Z p) (W p)
              + curvatureB g p (X p) (W p) (Y p) (Z p)
              - curvatureB g p (X p) (Z p) (Y p) (W p)) := by
    simpa only [e, extendVector_apply] using
      sum_curvatureFormAt_curvatureActions_e_x g p
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
        ∑ i, (g.leviCivitaConnection.curvatureFormAt g p
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) ((e i) p))
          (X p) (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p ((e i) p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) (X p))
          (W p) (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p ((e i) p) (X p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) (W p))
          (Z p)
        + g.leviCivitaConnection.curvatureFormAt g p ((e i) p) (X p) (W p)
          (g.leviCivitaConnection.curvatureOperatorAt p
            ((e i) p) (Y p) (Z p))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [curvatureForm_curvature_eq_curvatureFormAt_curvatureOperatorAt,
        curvatureForm_curvature_second_eq_curvatureFormAt_curvatureOperatorAt,
        curvatureForm_curvature_third_eq_curvatureFormAt_curvatureOperatorAt,
        curvatureForm_curvature_fourth_eq_curvatureFormAt_curvatureOperatorAt]
    _ = _ := hsum

/-! ### The curvature Laplacian formula -/

/-- **Math.** The unconditional curvature Laplacian identity, with the Hessian
slots and quadratic contractions in Morgan--Tian's convention. -/
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
    fun i ↦ extendVector p
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
    intro i _
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

#print axioms MorganTianLib.sum_curvatureFormAt_curvatureActions_y_e
#print axioms MorganTianLib.curvatureLaplacianFormula_explicit

end MorganTianLib

end

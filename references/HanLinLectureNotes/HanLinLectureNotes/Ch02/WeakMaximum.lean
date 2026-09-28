import HanLinLectureNotes.Ch02.HopfBarrierAnnulus
import HanLinLectureNotes.Ch02.MaximumPrinciple
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Han--Lin Chapter 2: weak maximum principle

The compact Hopf barrier supplies the strict perturbation used to pass from
the strict interior maximum test to the weak maximum principle.
-/

open Filter InnerProductSpace Metric Set Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

lemma exists_not_mem_closure_of_bounded
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    (hbounded : Bornology.IsBounded Omega) :
    exists x, x ∉ closure Omega := by
  obtain ⟨r, hr⟩ :=
    (Metric.isBounded_iff_subset_closedBall (0 : Euclidean n)).mp hbounded.closure
  let R : Real := |r| + 1
  have hR : 0 <= R := by dsimp [R]; positivity
  obtain ⟨x, hx⟩ : (Metric.sphere (0 : Euclidean n) R).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hR
  refine ⟨x, ?_⟩
  intro hxcl
  have hxball := hr hxcl
  rw [Metric.mem_closedBall] at hxball
  have hxsphere : dist x 0 = R := Metric.mem_sphere.mp hx
  rw [hxsphere] at hxball
  dsimp [R] at hxball
  linarith [le_abs_self r]

lemma nondivergenceOperator_eq_coordinate
    {n : Nat} {u : Euclidean n -> Real} {p : Euclidean n}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (hu : ContDiffAt Real 2 u p) :
    nondivergenceOperator a b c u p =
      (∑ i, ∑ j, a p i j *
        fderiv Real (fun y => fderiv Real u y
          (EuclideanSpace.basisFun (Fin n) Real j)) p
          (EuclideanSpace.basisFun (Fin n) Real i)) +
      ∑ i, b p i * fderiv Real u p (EuclideanSpace.basisFun (Fin n) Real i) +
      c p * u p := by
  unfold nondivergenceOperator
  congr 2
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, hessianMatrix,
    LinearMap.BilinForm.toMatrix_apply, secondDerivativeBilin]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  rw [fderiv_apply_eq_fderiv_fderiv hu]
  simpa using (hu.isSymmSndFDerivAt (by norm_num)
    (EuclideanSpace.basisFun (Fin n) Real i)
    (EuclideanSpace.basisFun (Fin n) Real j)).symm

private lemma continuousOn_matrix_apply
    {n : Nat} {S : Set (Euclidean n)}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    (ha : ContinuousOn a S) (i j : Fin n) :
    ContinuousOn (fun x => a x i j) S :=
  (continuous_apply j).comp_continuousOn ((continuous_apply i).comp_continuousOn ha)

private lemma continuousOn_vector_apply
    {n : Nat} {S : Set (Euclidean n)}
    {b : Euclidean n -> Fin n -> Real}
    (hb : ContinuousOn b S) (i : Fin n) :
    ContinuousOn (fun x => b x i) S :=
  (continuous_apply i).comp_continuousOn hb

lemma exists_hopfBarrier_operator_pos_on_closure
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    {lambda : Real} (hbounded : Bornology.IsBounded Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc : ContinuousOn c (closure Omega))
    (hlambda : 0 < lambda)
    (helliptic : forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda) :
    exists (xbar : Euclidean n) (alpha : Real),
      xbar ∉ closure Omega ∧ 0 < alpha ∧
      forall x, x ∈ closure Omega ->
        0 < nondivergenceOperator a b c
          (HanLinLectureNotes.hopfBarrier alpha xbar) x := by
  have hcompact : IsCompact (closure Omega) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hbounded.closure⟩
  obtain ⟨xbar, hxbar⟩ := exists_not_mem_closure_of_bounded hbounded
  let e : Fin n -> Euclidean n := fun i => EuclideanSpace.basisFun (Fin n) Real i
  have hspan : forall v : Euclidean n, (forall i, inner Real v (e i) = 0) -> v = 0 := by
    intro v hv
    ext i
    rw [← EuclideanSpace.inner_basisFun_real (Fin n) v i]
    simpa [e] using hv i
  have ha' : forall i j, ContinuousOn (fun x => a x i j) (closure Omega) :=
    fun i j => continuousOn_matrix_apply ha i j
  have hb' : forall i, ContinuousOn (fun x => b x i) (closure Omega) :=
    fun i => continuousOn_vector_apply hb i
  have hpos : forall x, x ∈ closure Omega -> forall xi : Fin n -> Real, xi ≠ 0 ->
      0 < ∑ i, ∑ j, a x i j * xi i * xi j := by
    intro x hx xi hxi
    have hqcont : ContinuousOn
        (fun y => ∑ i, ∑ j, a y i j * xi i * xi j) (closure Omega) := by
      refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
      exact ((ha' i j).mul continuousOn_const).mul continuousOn_const
    have hinterior : forall y, y ∈ Omega ->
        lambda * (∑ i, (xi i) ^ 2) <= ∑ i, ∑ j, a y i j * xi i * xi j := by
      intro y hy
      have h := helliptic y hy xi
      simpa [UniformlyElliptic, dotProduct, Matrix.mulVec, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm] using h
    have hlower : lambda * (∑ i, (xi i) ^ 2) <=
        ∑ i, ∑ j, a x i j * xi i * xi j :=
      le_on_closure hinterior continuousOn_const hqcont hx
    obtain ⟨i, hi⟩ : exists i, xi i ≠ 0 := by
      by_contra h
      push Not at h
      exact hxi (funext h)
    have hsumsq : 0 < ∑ i, (xi i) ^ 2 := by
      apply Finset.sum_pos'
      · exact fun j _ => sq_nonneg (xi j)
      · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    exact lt_of_lt_of_le (mul_pos hlambda hsumsq) hlower
  obtain ⟨alpha, halpha, hbarrier⟩ :=
    HanLinLectureNotes.exists_pos_forall_hopfBarrier_operator_pos_with_zeroOrder
      e hspan (A := fun x i j => a x i j) (b := b) (c := c)
      hcompact ha' hb' hc hpos hxbar
  refine ⟨xbar, alpha, hxbar, halpha, ?_⟩
  intro x hx
  have hsmooth : ContDiffAt Real 2 (HanLinLectureNotes.hopfBarrier alpha xbar) x :=
    ((HanLinLectureNotes.hopfBarrier_contDiff alpha xbar).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  rw [nondivergenceOperator_eq_coordinate hsmooth]
  exact hbarrier x hx

/-- Han--Lin Lemma 2.3, the weak maximum principle. A nonnegative maximum of
a subsolution on the closure of a bounded connected domain is attained on the
frontier. -/
theorem weak_maximum_principle
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u : Euclidean n -> Real}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (hOmega_open : IsOpen Omega) (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    (helliptic : exists lambda : Real, 0 < lambda /\
      forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda)
    (hLu : forall x, x ∈ Omega -> 0 <= nondivergenceOperator a b c u x)
    (hc : forall x, x ∈ Omega -> c x <= 0)
    {x0 : Euclidean n} (hx0 : x0 ∈ closure Omega)
    (hmax : IsMaxOn u (closure Omega) x0) (hu_nonneg : 0 <= u x0) :
    exists z, z ∈ frontier Omega ∧ IsMaxOn u (closure Omega) z := by
  obtain ⟨lambda, hlambda, helliptic⟩ := helliptic
  obtain ⟨xbar, alpha, hxbar, halpha, hbarrier⟩ :=
    exists_hopfBarrier_operator_pos_on_closure hOmega_bounded ha hb hc_cont
      hlambda helliptic
  have hcompact : IsCompact (closure Omega) :=
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure, hOmega_bounded.closure⟩
  have hOmega_ne_univ : Omega ≠ univ := by
    intro h
    apply hxbar
    simp [h]
  have hfrontier_ne : (frontier Omega).Nonempty :=
    nonempty_frontier_iff.mpr ⟨hOmega_connected.nonempty, hOmega_ne_univ⟩
  have hfrontier_compact : IsCompact (frontier Omega) :=
    hcompact.of_isClosed_subset isClosed_frontier frontier_subset_closure
  obtain ⟨z, hz, hzmax⟩ := hfrontier_compact.exists_isMaxOn hfrontier_ne
    (hu_cont.mono frontier_subset_closure)
  have huz_le : u z <= u x0 :=
    (isMaxOn_iff.mp hmax) z (frontier_subset_closure hz)
  have hux_le : u x0 <= u z := by
    by_contra hcontra
    rw [not_le] at hcontra
    let eps : Real := (u x0 - u z) / 2
    have heps : 0 < eps := by dsimp [eps]; linarith
    let phi : Euclidean n -> Real := HanLinLectureNotes.hopfBarrier alpha xbar
    let w : Euclidean n -> Real := u + eps • phi
    have hphiC2 : ContDiff Real 2 phi :=
      (HanLinLectureNotes.hopfBarrier_contDiff alpha xbar).of_le
        (WithTop.coe_le_coe.mpr le_top)
    have hwC2 : ContDiffOn Real 2 w Omega :=
      huC2.add (hphiC2.const_smul eps).contDiffOn
    have hw_cont : ContinuousOn w (closure Omega) :=
      hu_cont.add (hphiC2.continuous.const_smul eps).continuousOn
    have hLw : forall x, x ∈ Omega ->
        0 < nondivergenceOperator a b c w x := by
      intro x hx
      have huAt : ContDiffAt Real 2 u x :=
        (huC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
      have hphiAt : ContDiffAt Real 2 phi x := hphiC2.contDiffAt
      rw [show w = u + eps • phi by rfl,
        nondivergenceOperator_add_const_smul eps huAt hphiAt]
      nlinarith [hLu x hx, hbarrier x (subset_closure hx)]
    have hclosure_ne : (closure Omega).Nonempty :=
      hOmega_connected.nonempty.mono subset_closure
    obtain ⟨y, hy, hymax⟩ := hcompact.exists_isMaxOn hclosure_ne hw_cont
    have hw_x0_nonneg : 0 <= w x0 := by
      change 0 <= u x0 + eps * HanLinLectureNotes.hopfBarrier alpha xbar x0
      exact add_nonneg hu_nonneg
        (mul_nonneg heps.le (HanLinLectureNotes.hopfBarrier_pos alpha xbar x0).le)
    have hw_y_nonneg : 0 <= w y :=
      hw_x0_nonneg.trans ((isMaxOn_iff.mp hymax) x0 hx0)
    have hy_not : y ∉ Omega :=
      positive_operator_nonnegative_maximum_not_mem hOmega_open hOmega_bounded
        hOmega_connected ha hb hc_cont hwC2 hw_cont
        ⟨lambda, hlambda, helliptic⟩ hLw hc hymax hw_y_nonneg
    have hyfrontier : y ∈ frontier Omega := by
      rw [frontier, hOmega_open.interior_eq]
      exact ⟨hy, hy_not⟩
    have hchain : u x0 <= u z + eps := by
      calc
        u x0 <= w x0 := by
          change u x0 <= u x0 + eps * HanLinLectureNotes.hopfBarrier alpha xbar x0
          exact le_add_of_nonneg_right
            (mul_nonneg heps.le (HanLinLectureNotes.hopfBarrier_pos alpha xbar x0).le)
        _ <= w y := (isMaxOn_iff.mp hymax) x0 hx0
        _ = u y + eps * HanLinLectureNotes.hopfBarrier alpha xbar y := rfl
        _ <= u z + eps * 1 := add_le_add (isMaxOn_iff.mp hzmax y hyfrontier)
          (mul_le_mul_of_nonneg_left
            (HanLinLectureNotes.hopfBarrier_le_one halpha.le xbar y) heps.le)
        _ = u z + eps := by ring
    dsimp [eps] at hchain
    linarith
  refine ⟨z, hz, ?_⟩
  intro x hx
  calc
    u x <= u x0 := (isMaxOn_iff.mp hmax) x hx
    _ = u z := le_antisymm hux_le huz_le

end HanLinLectureNotes.Ch02

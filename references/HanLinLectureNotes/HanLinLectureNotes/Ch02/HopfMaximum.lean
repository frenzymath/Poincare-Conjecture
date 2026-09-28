import HanLinLectureNotes.Ch02.WeakMaximum
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Han--Lin Chapter 2: Hopf and strong maximum principles

The compact annulus barrier is localized to an interior tangent ball.  This
file develops the boundary-point comparison and the resulting strong maximum
principle for a general nondivergence-form elliptic operator.
-/

open Filter InnerProductSpace Metric Set Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The ball with midpoint center and half the radius is internally tangent to
the original Euclidean ball only at the prescribed boundary point. -/
lemma closedBall_midpoint_subset_ball_insert
    {n : Nat} {center x0 : Euclidean n} {R : Real}
    (hR : 0 < R) (hx0 : x0 ∈ sphere center R) :
    closedBall (center + (1 / 2 : Real) • (x0 - center)) (R / 2) ⊆
      ball center R ∪ {x0} := by
  intro z hz
  rw [mem_closedBall] at hz
  by_cases hzin : dist z center < R
  · exact Or.inl (mem_ball.mpr hzin)
  · right
    have hxnorm : ‖x0 - center‖ = R := by
      rw [← dist_eq_norm]
      exact mem_sphere.mp hx0
    have hycenter :
        dist (center + (1 / 2 : Real) • (x0 - center)) center = R / 2 := by
      rw [dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2), hxnorm]
      ring
    have hle : dist z center ≤ R := by
      calc
        dist z center ≤
            dist z (center + (1 / 2 : Real) • (x0 - center)) +
              dist (center + (1 / 2 : Real) • (x0 - center)) center :=
          dist_triangle _ _ _
        _ ≤ R / 2 + R / 2 := add_le_add hz hycenter.le
        _ = R := by ring
    have hzeq : ‖z - center‖ = R := by
      rw [← dist_eq_norm]
      exact le_antisymm hle (le_of_not_gt hzin)
    have hsum :
        (z - center) + (z - x0) =
          (2 : Real) • (z - (center + (1 / 2 : Real) • (x0 - center))) := by
      module
    have hdiff : (z - center) - (z - x0) = x0 - center := by
      module
    have hp := parallelogram_law_with_norm Real (z - center) (z - x0)
    rw [hsum, hdiff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 2), hxnorm, hzeq] at hp
    have hzy :
        ‖z - (center + (1 / 2 : Real) • (x0 - center))‖ ≤ R / 2 := by
      rwa [dist_eq_norm] at hz
    have hzy_nonneg :=
      norm_nonneg (z - (center + (1 / 2 : Real) • (x0 - center)))
    have hzx_nonneg := norm_nonneg (z - x0)
    have hzy_sq :
        ‖z - (center + (1 / 2 : Real) • (x0 - center))‖ ^ 2 ≤
          (R / 2) ^ 2 := by
      nlinarith
    have hzx : ‖z - x0‖ = 0 := by
      nlinarith [sq_nonneg ‖z - x0‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp hzx)

/-- On any compact set away from the barrier center, continuous uniformly
elliptic coefficients admit one exponent for which the full operator applied
to the Hopf barrier is positive. -/
lemma exists_hopfBarrier_operator_pos_on_compact
    {n : Nat} [Nonempty (Fin n)] {S : Set (Euclidean n)}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    {lambda : Real} (hS : IsCompact S)
    (ha : ContinuousOn a S) (hb : ContinuousOn b S) (hc : ContinuousOn c S)
    (hlambda : 0 < lambda)
    (helliptic : ∀ x ∈ S, UniformlyElliptic (a x) lambda)
    {xbar : Euclidean n} (hxbar : xbar ∉ S) :
    ∃ alpha : Real, 0 < alpha ∧ ∀ x ∈ S,
      0 < nondivergenceOperator a b c
        (HanLinLectureNotes.hopfBarrier alpha xbar) x := by
  let e : Fin n → Euclidean n := fun i => EuclideanSpace.basisFun (Fin n) Real i
  have hspan : ∀ v : Euclidean n, (∀ i, inner Real v (e i) = 0) → v = 0 := by
    intro v hv
    ext i
    rw [← EuclideanSpace.inner_basisFun_real (Fin n) v i]
    simpa [e] using hv i
  have ha' : ∀ i j, ContinuousOn (fun x => a x i j) S :=
    fun i j =>
      (continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn ha)
  have hb' : ∀ i, ContinuousOn (fun x => b x i) S :=
    fun i => (continuous_apply i).comp_continuousOn hb
  have hpos : ∀ x ∈ S, ∀ xi : Fin n → Real, xi ≠ 0 →
      0 < ∑ i, ∑ j, a x i j * xi i * xi j := by
    intro x hx xi hxi
    obtain ⟨i, hi⟩ : ∃ i, xi i ≠ 0 := by
      by_contra h
      push Not at h
      exact hxi (funext h)
    have hsumsq : 0 < ∑ i, (xi i) ^ 2 := by
      apply Finset.sum_pos'
      · exact fun j _ => sq_nonneg (xi j)
      · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hq := helliptic x hx xi
    have hq' : lambda * (∑ i, (xi i) ^ 2) ≤
        ∑ i, ∑ j, a x i j * xi i * xi j := by
      simpa [UniformlyElliptic, dotProduct, Matrix.mulVec, Finset.mul_sum,
        mul_assoc, mul_comm, mul_left_comm] using hq
    exact lt_of_lt_of_le (mul_pos hlambda hsumsq) hq'
  obtain ⟨alpha, halpha, hbarrier⟩ :=
    HanLinLectureNotes.exists_pos_forall_hopfBarrier_operator_pos_with_zeroOrder
      e hspan (A := fun x i j => a x i j) (b := b) (c := c)
      hS ha' hb' hc hpos hxbar
  refine ⟨alpha, halpha, ?_⟩
  intro x hx
  have hsmooth : ContDiffAt Real 2 (HanLinLectureNotes.hopfBarrier alpha xbar) x :=
    ((HanLinLectureNotes.hopfBarrier_contDiff alpha xbar).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  rw [nondivergenceOperator_eq_coordinate hsmooth]
  exact hbarrier x hx

/-- Continuity extends a uniform ellipticity bound from an open Euclidean ball
to its closure. -/
lemma uniformlyElliptic_on_closedBall
    {n : Nat} {center : Euclidean n} {R : Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real} {lambda : Real}
    (hR : 0 < R) (ha : ContinuousOn a (closedBall center R))
    (helliptic : ∀ x ∈ ball center R, UniformlyElliptic (a x) lambda) :
    ∀ x ∈ closedBall center R, UniformlyElliptic (a x) lambda := by
  intro x hx xi
  have hqcont : ContinuousOn
      (fun y => xi ⬝ᵥ ((a y).mulVec xi)) (closedBall center R) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine continuousOn_finsetSum _ fun i _ => continuousOn_finsetSum _ fun j _ => ?_
    exact continuousOn_const.mul
      (((continuous_apply j).comp_continuousOn
        ((continuous_apply i).comp_continuousOn ha)).mul continuousOn_const)
  have hinterior : ∀ y ∈ ball center R,
      lambda * (∑ i, (xi i) ^ 2) ≤ xi ⬝ᵥ ((a y).mulVec xi) := by
    intro y hy
    exact helliptic y hy xi
  have hx' : x ∈ closure (ball center R) := by
    rwa [closure_ball center hR.ne']
  apply le_on_closure hinterior continuousOn_const _ hx'
  rwa [closure_ball center hR.ne']

/-- An outward direction enters the interior tangent annulus for all sufficiently
small positive times when followed backwards from the tangency point. -/
lemma eventually_sub_smul_mem_midpoint_annulus
    {n : Nat} {center x0 v : Euclidean n} {R : Real}
    (hR : 0 < R) (hx0 : x0 ∈ sphere center R)
    (hv : 0 < ⟪x0 - center, v⟫_Real) :
    ∀ᶠ t in 𝓝[>] (0 : Real),
      x0 - t • v ∈
        closedBall (center + (1 / 2 : Real) • (x0 - center)) (R / 2) \
          ball (center + (1 / 2 : Real) • (x0 - center)) (R / 4) := by
  have hv0 : v ≠ 0 := by
    intro h
    simp [h] at hv
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hxnorm : ‖x0 - center‖ = R := by
    rw [← dist_eq_norm]
    exact mem_sphere.mp hx0
  let tau : Real := min (⟪x0 - center, v⟫_Real / ‖v‖ ^ 2)
    (R / (4 * ‖v‖))
  have htau : 0 < tau := by
    dsimp [tau]
    exact lt_min (div_pos hv (sq_pos_of_pos hvnorm))
      (div_pos hR (mul_pos (by norm_num) hvnorm))
  filter_upwards [Ioo_mem_nhdsGT htau] with t ht
  have htpos : 0 < t := ht.1
  have htquad : t * ‖v‖ ^ 2 < ⟪x0 - center, v⟫_Real := by
    have hlt : t < ⟪x0 - center, v⟫_Real / ‖v‖ ^ 2 :=
      ht.2.trans_le (min_le_left _ _)
    simpa [mul_comm] using (lt_div_iff₀' (sq_pos_of_pos hvnorm)).mp hlt
  have htlin : t * ‖v‖ < R / 4 := by
    have hlt : t < R / (4 * ‖v‖) :=
      ht.2.trans_le (min_le_right _ _)
    have hden : 0 < 4 * ‖v‖ := mul_pos (by norm_num) hvnorm
    have := (lt_div_iff₀ hden).mp hlt
    nlinarith
  have hsub :
      x0 - t • v - (center + (1 / 2 : Real) • (x0 - center)) =
        (1 / 2 : Real) • (x0 - center) - t • v := by
    module
  have hsq :
      ‖(1 / 2 : Real) • (x0 - center) - t • v‖ ^ 2 =
        (R / 2) ^ 2 - t * ⟪x0 - center, v⟫_Real + t ^ 2 * ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [norm_smul, norm_smul]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2), abs_of_pos htpos, hxnorm]
    rw [real_inner_comm v x0, real_inner_comm v center]
    ring
  constructor
  · rw [mem_closedBall, dist_eq_norm, hsub]
    have hnonneg := norm_nonneg ((1 / 2 : Real) • (x0 - center) - t • v)
    have hR2 : 0 ≤ R / 2 := by linarith
    have hstrict :
        ‖(1 / 2 : Real) • (x0 - center) - t • v‖ ^ 2 < (R / 2) ^ 2 := by
      rw [hsq]
      have hmul : 0 < t * (⟪x0 - center, v⟫_Real - t * ‖v‖ ^ 2) :=
        mul_pos htpos (sub_pos.mpr htquad)
      nlinarith
    nlinarith [sq_nonneg
      (‖(1 / 2 : Real) • (x0 - center) - t • v‖ - R / 2)]
  · rw [mem_ball, dist_eq_norm, hsub]
    have htri :
        R / 2 ≤ ‖(1 / 2 : Real) • (x0 - center) - t • v‖ + ‖t • v‖ := by
      calc
        R / 2 = ‖(1 / 2 : Real) • (x0 - center)‖ := by
          rw [norm_smul]
          simp only [Real.norm_eq_abs,
            abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2), hxnorm]
          ring
        _ = ‖((1 / 2 : Real) • (x0 - center) - t • v) + t • v‖ := by
          congr 1
          module
        _ ≤ _ := norm_add_le _ _
    rw [norm_smul] at htri
    simp only [Real.norm_eq_abs, abs_of_pos htpos] at htri
    linarith

/-- The Hopf barrier difference quotient along an inward ray converges to its
explicit positive radial derivative. -/
lemma tendsto_hopfBarrier_sub_smul_div
    {n : Nat} {alpha R : Real} {y x0 v : Euclidean n}
    (hxnorm : ‖x0 - y‖ = R) :
    Tendsto
      (fun t : Real =>
        (HanLinLectureNotes.hopfBarrier alpha y (x0 - t • v) -
          Real.exp (-alpha * R ^ 2)) / t)
      (𝓝[≠] (0 : Real))
      (𝓝 (2 * alpha * Real.exp (-alpha * R ^ 2) * ⟪x0 - y, v⟫_Real)) := by
  have hline : HasDerivAt (fun t : Real => x0 - t • v) (-v) 0 := by
    have h : HasDerivAt (fun t : Real => x0 + t • (-v)) (-v) 0 := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id (0 : Real)).smul_const (-v)).const_add x0
    simpa only [smul_neg, sub_eq_add_neg] using h
  have hout : HasFDerivAt (HanLinLectureNotes.hopfBarrier alpha y)
      ((-2 * alpha * Real.exp (-alpha * ‖x0 - y‖ ^ 2)) • innerSL Real (x0 - y))
      ((fun t : Real => x0 - t • v) 0) := by
    simpa using HanLinLectureNotes.hasFDerivAt_hopfBarrier alpha y x0
  have hslope := (hout.comp_hasDerivAt 0 hline).tendsto_slope_zero
  have hvalue :
      HanLinLectureNotes.hopfBarrier alpha y x0 = Real.exp (-alpha * R ^ 2) :=
    HanLinLectureNotes.hopfBarrier_eq_of_norm_eq hxnorm
  convert hslope using 1
  · funext t
    simp only [Function.comp_apply, zero_add, zero_smul, sub_zero, hvalue, smul_eq_mul]
    simp only [div_eq_mul_inv]
    ring
  · congr 1
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul, inner_neg_right, hxnorm]
    ring

/-- Subtracting a constant changes a nondivergence operator only through its
zeroth-order term. -/
lemma nondivergenceOperator_sub_const
    {n : Nat} {u : Euclidean n → Real} {p : Euclidean n}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (k : Real) (hu : ContDiffAt Real 2 u p) :
    nondivergenceOperator a b c (fun x => u x - k) p =
      nondivergenceOperator a b c u p - c p * k := by
  have hone : ContDiffAt Real 2 (fun _ : Euclidean n => (1 : Real)) p :=
    contDiff_const.contDiffAt
  have hadd := nondivergenceOperator_add_const_smul
    (a := a) (b := b) (c := c) (-k) hu hone
  have hfun : (fun x => u x - k) =
      u + (-k) • (fun _ : Euclidean n => (1 : Real)) := by
    funext x
    change u x - k = u x + (-k) * 1
    ring
  rw [hfun, hadd]
  have hconst :
      nondivergenceOperator a b c (fun _ : Euclidean n => (1 : Real)) p = c p := by
    simp [nondivergenceOperator, hessianMatrix, secondDerivativeBilin]
  rw [hconst]
  ring

/-- The quantitative comparison at the heart of the Hopf boundary lemma.  A
positive multiple of the annular barrier may be added to `u` without exceeding
the boundary value at the tangency point. -/
lemma exists_hopf_boundary_comparison
    {n : Nat} [Nonempty (Fin n)] {center x0 : Euclidean n} {R : Real}
    (hR : 0 < R) (hx0 : x0 ∈ sphere center R)
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (ha : ContinuousOn a (closedBall center R))
    (hb : ContinuousOn b (closedBall center R))
    (hc_cont : ContinuousOn c (closedBall center R))
    (huC2 : ContDiffOn Real 2 u (ball center R))
    (hu_cont : ContinuousOn u (ball center R ∪ {x0}))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ ball center R, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ ball center R, 0 ≤ nondivergenceOperator a b c u x)
    (hc : ∀ x ∈ ball center R, c x ≤ 0)
    (hstrict : ∀ x ∈ ball center R, u x < u x0)
    (hu0 : 0 ≤ u x0) :
    ∃ (alpha eps : Real), 0 < alpha ∧ 0 < eps ∧
      ∀ z ∈ closedBall (center + (1 / 2 : Real) • (x0 - center)) (R / 2) \
          ball (center + (1 / 2 : Real) • (x0 - center)) (R / 4),
        u z + eps * (HanLinLectureNotes.hopfBarrier alpha
          (center + (1 / 2 : Real) • (x0 - center)) z -
            Real.exp (-alpha * (R / 2) ^ 2)) ≤ u x0 := by
  classical
  set y : Euclidean n := center + (1 / 2 : Real) • (x0 - center) with hy
  set A : Set (Euclidean n) := closedBall y (R / 2) \ ball y (R / 4) with hA
  have hxnorm : ‖x0 - center‖ = R := by
    rw [← dist_eq_norm]
    exact mem_sphere.mp hx0
  have hxynorm : ‖x0 - y‖ = R / 2 := by
    rw [hy]
    have heq : x0 - (center + (1 / 2 : Real) • (x0 - center)) =
        (1 / 2 : Real) • (x0 - center) := by
      module
    rw [heq, norm_smul]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2), hxnorm]
    ring
  have hKsub : closedBall y (R / 2) ⊆ ball center R ∪ {x0} := by
    simpa [hy] using closedBall_midpoint_subset_ball_insert hR hx0
  have hKclosed : closedBall y (R / 2) ⊆ closedBall center R := by
    intro z hz
    rcases hKsub hz with hzball | hzx
    · exact mem_closedBall.mpr (mem_ball.mp hzball).le
    · have hzx' : z = x0 := by simpa using hzx
      subst z
      exact mem_closedBall.mpr (mem_sphere.mp hx0).le
  have hAsub_closed : A ⊆ closedBall center R := fun z hz => hKclosed hz.1
  have hAsub_union : A ⊆ ball center R ∪ {x0} := fun z hz => hKsub hz.1
  have hAcompact : IsCompact A := by
    rw [hA]
    exact (isCompact_closedBall y (R / 2)).diff isOpen_ball
  have hyA : y ∉ A := by
    intro hyMem
    exact hyMem.2 (mem_ball_self (by linarith))
  have hx0A : x0 ∈ A := by
    rw [hA]
    constructor
    · rw [mem_closedBall, dist_eq_norm, hxynorm]
    · rw [mem_ball, dist_eq_norm, hxynorm]
      linarith
  obtain ⟨lambda, hlambda, helliptic⟩ := helliptic
  have helliptic_closed := uniformlyElliptic_on_closedBall hR ha helliptic
  obtain ⟨alpha, halpha, hbarrier⟩ := exists_hopfBarrier_operator_pos_on_compact
    hAcompact (ha.mono hAsub_closed) (hb.mono hAsub_closed)
      (hc_cont.mono hAsub_closed) hlambda
      (fun z hz => helliptic_closed z (hAsub_closed hz)) hyA
  set S : Set (Euclidean n) := sphere y (R / 4) with hS
  have hScompact : IsCompact S := by
    rw [hS]
    exact isCompact_sphere y (R / 4)
  have hSne : S.Nonempty := by
    rw [hS]
    exact NormedSpace.sphere_nonempty.mpr (by linarith)
  have hSsub_ball : S ⊆ ball center R := by
    intro z hz
    have hzdist : dist z y = R / 4 := by
      exact mem_sphere.mp hz
    have hzK : z ∈ closedBall y (R / 2) :=
      mem_closedBall.mpr (by linarith)
    rcases hKsub hzK with hzball | hzx
    · exact hzball
    · have hzx' : z = x0 := by simpa using hzx
      subst z
      exfalso
      have hxydist : dist x0 y = R / 2 := by
        rw [dist_eq_norm, hxynorm]
      linarith
  obtain ⟨ys, hys, hysmax⟩ := hScompact.exists_isMaxOn hSne
    (hu_cont.mono fun z hz => Or.inl (hSsub_ball hz))
  have hyslt : u ys < u x0 := hstrict ys (hSsub_ball hys)
  set delta : Real := u x0 - u ys with hdelta
  have hdeltaPos : 0 < delta := by
    rw [hdelta]
    linarith
  set eps : Real := delta / 2 with heps
  have hepsPos : 0 < eps := by
    rw [heps]
    positivity
  set c0 : Real := Real.exp (-alpha * (R / 2) ^ 2) with hc0
  set phi : Euclidean n → Real := fun z =>
    HanLinLectureNotes.hopfBarrier alpha y z - c0 with hphi
  set VE : Euclidean n → Real := u + eps • phi with hVE
  have hVEcont : ContinuousOn VE A := by
    rw [hVE]
    exact (hu_cont.mono hAsub_union).add
      (continuousOn_const.smul
        (((HanLinLectureNotes.hopfBarrier_contDiff alpha y).continuous.sub
          continuous_const).continuousOn))
  have hinner : ∀ z ∈ S, VE z < u x0 := by
    intro z hz
    have huz : u z ≤ u ys := hysmax hz
    have hphi_le : phi z ≤ 1 := by
      rw [hphi, hc0]
      have h1 := HanLinLectureNotes.hopfBarrier_le_one halpha.le y z
      have h2 := Real.exp_pos (-alpha * (R / 2) ^ 2)
      linarith
    have hepsphi : eps * phi z ≤ eps := by
      nlinarith
    rw [hVE]
    change u z + eps * phi z < u x0
    calc
      u z + eps * phi z ≤ u ys + eps := add_le_add huz hepsphi
      _ < u x0 := by rw [heps, hdelta]; linarith
  have hVEx0 : VE x0 = u x0 := by
    rw [hVE]
    change u x0 + eps * phi x0 = u x0
    rw [hphi]
    change u x0 + eps *
      (HanLinLectureNotes.hopfBarrier alpha y x0 - c0) = u x0
    rw [hc0, HanLinLectureNotes.hopfBarrier_eq_of_norm_eq hxynorm]
    ring
  obtain ⟨q, hqA, hqmax⟩ := hAcompact.exists_isMaxOn ⟨x0, hx0A⟩ hVEcont
  have hmq : u x0 ≤ VE q := by
    rw [← hVEx0]
    exact hqmax hx0A
  have hqge : R / 4 ≤ dist q y := by
    by_contra h
    push Not at h
    exact hqA.2 (mem_ball.mpr h)
  have hq_ne_inner : dist q y ≠ R / 4 := by
    intro heq
    have hqS : q ∈ S := by
      rw [hS, mem_sphere]
      exact heq
    linarith [hinner q hqS]
  have hq_not_interior : ¬ dist q y < R / 2 := by
    intro hqlt
    have hqgt : R / 4 < dist q y := lt_of_le_of_ne hqge (Ne.symm hq_ne_inner)
    set r0 : Real := min (dist q y - R / 4) (R / 2 - dist q y) with hr0
    have hr0Pos : 0 < r0 := lt_min (by linarith) (by linarith)
    have hballA : ball q r0 ⊆ A := by
      intro z hz
      rw [mem_ball] at hz
      constructor
      · rw [mem_closedBall]
        have hupper : dist z q < R / 2 - dist q y :=
          lt_of_lt_of_le hz (min_le_right _ _)
        calc
          dist z y ≤ dist z q + dist q y := dist_triangle _ _ _
          _ ≤ R / 2 := by linarith
      · intro hzinner
        rw [mem_ball] at hzinner
        have hlower : dist q y ≤ dist q z + dist z y := dist_triangle _ _ _
        have hqz : dist q z < dist q y - R / 4 := by
          rw [dist_comm]
          exact lt_of_lt_of_le hz (min_le_left _ _)
        linarith
    have hlocal : IsLocalMax VE q :=
      hqmax.isLocalMax (mem_of_superset (ball_mem_nhds q hr0Pos) hballA)
    have hqball : q ∈ ball center R := by
      rcases hAsub_union hqA with hqball | hqx0
      · exact hqball
      · have hqx0' : q = x0 := by simpa using hqx0
        subst q
        rw [dist_eq_norm, hxynorm] at hqlt
        linarith
    have huAt : ContDiffAt Real 2 u q :=
      (huC2 q hqball).contDiffAt (isOpen_ball.mem_nhds hqball)
    have hbarAt : ContDiffAt Real 2
        (HanLinLectureNotes.hopfBarrier alpha y) q :=
      ((HanLinLectureNotes.hopfBarrier_contDiff alpha y).of_le
        (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    have hphiAt : ContDiffAt Real 2 phi q := by
      rw [hphi]
      exact hbarAt.sub contDiffAt_const
    have hVEAt : ContDiffAt Real 2 VE q := by
      rw [hVE]
      exact huAt.add (hphiAt.const_smul eps)
    have hLphi : 0 < nondivergenceOperator a b c phi q := by
      rw [hphi, nondivergenceOperator_sub_const c0 hbarAt]
      have hbpos := hbarrier q hqA
      have hcq := hc q hqball
      have hc0pos : 0 < c0 := by rw [hc0]; exact Real.exp_pos _
      nlinarith
    have hLVE : 0 < nondivergenceOperator a b c VE q := by
      rw [hVE, nondivergenceOperator_add_const_smul eps huAt hphiAt]
      have hLuq := hLu q hqball
      have hepsL := mul_pos hepsPos hLphi
      linarith
    have hVEq_nonneg : 0 ≤ VE q := hu0.trans hmq
    have hnonpos := nondivergenceOperator_nonpos_at_nonnegative_localMax
      (b := b) hlambda.le (helliptic q hqball) hVEAt hlocal
        (hc q hqball) hVEq_nonneg
    linarith
  have hqouter : dist q y = R / 2 := by
    have hqle : dist q y ≤ R / 2 := mem_closedBall.mp hqA.1
    exact le_antisymm hqle (le_of_not_gt hq_not_interior)
  have hqnorm : ‖q - y‖ = R / 2 := by
    rw [← dist_eq_norm]
    exact hqouter
  have hphiq : phi q = 0 := by
    rw [hphi]
    change HanLinLectureNotes.hopfBarrier alpha y q - c0 = 0
    rw [hc0, HanLinLectureNotes.hopfBarrier_eq_of_norm_eq hqnorm]
    ring
  have hVEq : VE q = u q := by
    rw [hVE]
    change u q + eps * phi q = u q
    rw [hphiq]
    ring
  have hqx0 : q = x0 := by
    rcases hAsub_union hqA with hqball | hqx0
    · have hqstrict := hstrict q hqball
      rw [hVEq] at hmq
      linarith
    · simpa using hqx0
  subst q
  refine ⟨alpha, eps, halpha, hepsPos, ?_⟩
  intro z hz
  have hzA : z ∈ A := by simpa [hA, hy] using hz
  have hmaxz := hqmax hzA
  rw [hVEx0] at hmaxz
  simpa [hVE, hphi, hc0, hy] using hmaxz

/-- Han--Lin Theorem 2.6, the Hopf boundary-point lemma.  At a strict
nonnegative boundary maximum on a ball, every direction with positive outward
normal component has strictly positive lower one-sided difference quotient. -/
theorem hopf_boundary_point_liminf_pos
    {n : Nat} [Nonempty (Fin n)] {center x0 : Euclidean n} {R : Real}
    (hR : 0 < R) (hx0 : x0 ∈ sphere center R)
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (ha : ContinuousOn a (closedBall center R))
    (hb : ContinuousOn b (closedBall center R))
    (hc_cont : ContinuousOn c (closedBall center R))
    (huC2 : ContDiffOn Real 2 u (ball center R))
    (hu_cont : ContinuousOn u (ball center R ∪ {x0}))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ ball center R, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ ball center R, 0 ≤ nondivergenceOperator a b c u x)
    (hc : ∀ x ∈ ball center R, c x ≤ 0)
    (hstrict : ∀ x ∈ ball center R, u x < u x0)
    (hu0 : 0 ≤ u x0) {v : Euclidean n}
    (hv : 0 < ⟪v, R⁻¹ • (x0 - center)⟫_Real) :
    (0 : EReal) < Filter.liminf
      (fun t : Real =>
        (((u x0 - u (x0 - t • v)) / t : Real) : EReal))
      (𝓝[>] (0 : Real)) := by
  obtain ⟨alpha, eps, halpha, heps, hcomparison⟩ :=
    exists_hopf_boundary_comparison hR hx0 ha hb hc_cont huC2 hu_cont
      helliptic hLu hc hstrict hu0
  set y : Euclidean n := center + (1 / 2 : Real) • (x0 - center) with hy
  have hxnorm : ‖x0 - center‖ = R := by
    rw [← dist_eq_norm]
    exact mem_sphere.mp hx0
  have hxynorm : ‖x0 - y‖ = R / 2 := by
    rw [hy]
    have heq : x0 - (center + (1 / 2 : Real) • (x0 - center)) =
        (1 / 2 : Real) • (x0 - center) := by
      module
    rw [heq, norm_smul]
    simp only [Real.norm_eq_abs,
      abs_of_nonneg (by norm_num : (0 : Real) ≤ 1 / 2), hxnorm]
    ring
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  have hvdot : 0 < ⟪x0 - center, v⟫_Real := by
    rw [real_inner_smul_right] at hv
    rw [mul_comm] at hv
    have hv' : 0 < ⟪v, x0 - center⟫_Real :=
      pos_of_mul_pos_left hv hRinv.le
    rwa [real_inner_comm] at hv'
  have hxyv : 0 < ⟪x0 - y, v⟫_Real := by
    have heq : x0 - y = (1 / 2 : Real) • (x0 - center) := by
      rw [hy]
      module
    rw [heq, real_inner_smul_left]
    positivity
  set K : Real :=
    2 * alpha * Real.exp (-alpha * (R / 2) ^ 2) * ⟪x0 - y, v⟫_Real with hK
  have hKpos : 0 < K := by
    rw [hK]
    exact mul_pos (mul_pos (mul_pos (by norm_num) halpha) (Real.exp_pos _)) hxyv
  have hfilter : (𝓝[>] (0 : Real)) ≤ 𝓝[≠] (0 : Real) := by
    apply nhdsWithin_mono
    intro t ht
    simp only [mem_Ioi] at ht
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt ht
  have hslope := (tendsto_hopfBarrier_sub_smul_div
    (alpha := alpha) (v := v) hxynorm).mono_left hfilter
  have hslope_lower : ∀ᶠ t in 𝓝[>] (0 : Real),
      K / 2 <
        (HanLinLectureNotes.hopfBarrier alpha y (x0 - t • v) -
          Real.exp (-alpha * (R / 2) ^ 2)) / t := by
    exact hslope.eventually (eventually_gt_nhds (by rw [← hK]; linarith))
  have hmem := eventually_sub_smul_mem_midpoint_annulus hR hx0 hvdot
  have hlower : ∀ᶠ t in 𝓝[>] (0 : Real),
      eps * (K / 2) ≤ (u x0 - u (x0 - t • v)) / t := by
    filter_upwards [eventually_mem_nhdsWithin, hmem, hslope_lower] with t ht hta hs
    have htpos : 0 < t := by simpa only [mem_Ioi] using ht
    have hcomp := hcomparison (x0 - t • v) hta
    have hquot : eps *
        ((HanLinLectureNotes.hopfBarrier alpha y (x0 - t • v) -
          Real.exp (-alpha * (R / 2) ^ 2)) / t) ≤
        (u x0 - u (x0 - t • v)) / t := by
      rw [← mul_div_assoc]
      apply (div_le_div_iff_of_pos_right htpos).mpr
      nlinarith
    calc
      eps * (K / 2) ≤ eps *
          ((HanLinLectureNotes.hopfBarrier alpha y (x0 - t • v) -
            Real.exp (-alpha * (R / 2) ^ 2)) / t) :=
        (mul_le_mul_of_nonneg_left hs.le heps.le)
      _ ≤ _ := hquot
  have hlowerE : ∀ᶠ t in 𝓝[>] (0 : Real),
      ((eps * (K / 2) : Real) : EReal) ≤
        (((u x0 - u (x0 - t • v)) / t : Real) : EReal) :=
    hlower.mono fun t ht => EReal.coe_le_coe ht
  have hlim := Filter.le_liminf_of_le (f := 𝓝[>] (0 : Real)) (h := hlowerE)
  have hepsK : 0 < eps * (K / 2) := mul_pos heps (half_pos hKpos)
  exact (EReal.coe_pos.mpr hepsK).trans_le hlim

/-- A directional backward difference quotient converges to the Fréchet
derivative applied to that direction. -/
lemma tendsto_difference_quotient_eq_fderiv
    {n : Nat} {u : Euclidean n → Real} {p v : Euclidean n}
    (hu : ContDiffAt Real 1 u p) :
    Tendsto (fun t : Real => (u p - u (p - t • v)) / t)
      (𝓝[≠] (0 : Real)) (𝓝 (fderiv Real u p v)) := by
  have hline : HasDerivAt (fun t : Real => p - t • v) (-v) 0 := by
    have h : HasDerivAt (fun t : Real => p + t • (-v)) (-v) 0 := by
      simpa only [one_smul, id_eq] using
        ((hasDerivAt_id (0 : Real)).smul_const (-v)).const_add p
    simpa only [smul_neg, sub_eq_add_neg] using h
  have hudiff : DifferentiableAt Real u p := hu.differentiableAt (by norm_num)
  have hout : HasFDerivAt u (fderiv Real u p)
      ((fun t : Real => p - t • v) 0) := by
    simpa using hudiff.hasFDerivAt
  have hcomp := hout.comp_hasDerivAt 0 hline
  have hnum := (hasDerivAt_const (x := (0 : Real)) (c := u p)).sub hcomp
  have hderiv : (0 : Real) - fderiv Real u p (-v) =
      fderiv Real u p v := by
    rw [map_neg]
    ring
  rw [hderiv] at hnum
  have hslope := hnum.tendsto_slope_zero
  convert hslope using 1
  funext t
  simp only [Function.comp_apply, Pi.sub_apply, zero_add, zero_smul,
    sub_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- At a differentiable local maximum, every directional one-sided difference
quotient tends to zero.  We state this first on the punctured neighborhood so
that it can be restricted to either one-sided filter. -/
lemma tendsto_difference_quotient_zero_of_isLocalMax
    {n : Nat} {u : Euclidean n → Real} {p v : Euclidean n}
    (hu : ContDiffAt Real 2 u p) (hmax : IsLocalMax u p) :
    Tendsto (fun t : Real => (u p - u (p - t • v)) / t)
      (𝓝[≠] (0 : Real)) (𝓝 0) := by
  have hz : fderiv Real u p = (0 : Euclidean n →L[Real] Real) :=
    hmax.fderiv_eq_zero
  simpa only [hz, zero_apply] using
    tendsto_difference_quotient_eq_fderiv (v := v) (hu.of_le (by norm_num))

/-- Han--Lin Remark 2.7.  If the solution is differentiable at the tangent
point, the Hopf difference-quotient conclusion is a strictly positive outward
normal derivative. -/
theorem hopf_boundary_outward_normal_fderiv_pos
    {n : Nat} [Nonempty (Fin n)] {center x0 : Euclidean n} {R : Real}
    (hR : 0 < R) (hx0 : x0 ∈ sphere center R)
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (ha : ContinuousOn a (closedBall center R))
    (hb : ContinuousOn b (closedBall center R))
    (hc_cont : ContinuousOn c (closedBall center R))
    (huC2 : ContDiffOn Real 2 u (ball center R))
    (hu_cont : ContinuousOn u (ball center R ∪ {x0}))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ ball center R, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ ball center R, 0 ≤ nondivergenceOperator a b c u x)
    (hc : ∀ x ∈ ball center R, c x ≤ 0)
    (hstrict : ∀ x ∈ ball center R, u x < u x0)
    (hu0 : 0 ≤ u x0) (huC1 : ContDiffAt Real 1 u x0) :
    0 < fderiv Real u x0 (R⁻¹ • (x0 - center)) := by
  have hxnorm : ‖x0 - center‖ = R := by
    rw [← dist_eq_norm]
    exact mem_sphere.mp hx0
  have hnormal :
      0 < ⟪R⁻¹ • (x0 - center), R⁻¹ • (x0 - center)⟫_Real := by
    rw [real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hxnorm]
    positivity
  have hhopf := hopf_boundary_point_liminf_pos hR hx0 ha hb hc_cont
    huC2 hu_cont helliptic hLu hc hstrict hu0
      (v := R⁻¹ • (x0 - center)) hnormal
  have hfilter : (𝓝[>] (0 : Real)) ≤ 𝓝[≠] (0 : Real) := by
    apply nhdsWithin_mono
    intro t ht
    simp only [mem_Ioi] at ht
    simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt ht
  have hreal : Tendsto
      (fun t : Real =>
        (u x0 - u (x0 - t • (R⁻¹ • (x0 - center)))) / t)
      (𝓝[>] (0 : Real))
      (𝓝 (fderiv Real u x0 (R⁻¹ • (x0 - center)))) :=
    (tendsto_difference_quotient_eq_fderiv
      (v := R⁻¹ • (x0 - center)) huC1).mono_left hfilter
  have hereal : Tendsto
      (fun t : Real =>
        (((u x0 - u (x0 - t • (R⁻¹ • (x0 - center)))) / t : Real) : EReal))
      (𝓝[>] (0 : Real))
      (𝓝 ((fderiv Real u x0 (R⁻¹ • (x0 - center)) : Real) : EReal)) :=
    EReal.tendsto_coe.mpr hreal
  have hlim := hereal.liminf_eq
  rw [hlim] at hhopf
  exact EReal.coe_pos.mp hhopf

/-- A nonnegative interior maximum propagates to an open neighborhood.  The
nearest point of the maximum level set supplies the tangent ball on which the
Hopf boundary-point lemma contradicts the vanishing derivative at a maximum. -/
lemma exists_eqOn_neighborhood_of_nonnegative_max
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (ha : ContinuousOn a Omega)
    (hb : ContinuousOn b Omega)
    (hc_cont : ContinuousOn c Omega)
    (huC2 : ContDiffOn Real 2 u Omega)
    (hu_cont : ContinuousOn u Omega)
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c u x)
    (hc : ∀ x ∈ Omega, c x ≤ 0)
    {m : Real} (hm0 : 0 ≤ m) (hle : ∀ x ∈ Omega, u x ≤ m)
    {z : Euclidean n} (hz : z ∈ Omega) (hzm : u z = m) :
    ∃ O : Set (Euclidean n), IsOpen O ∧ z ∈ O ∧ O ⊆ Omega ∧
      ∀ x ∈ O, u x = m := by
  classical
  obtain ⟨r, hrpos, hball⟩ := Metric.isOpen_iff.mp hOmega_open z hz
  set rho : Real := r / 4 with hrho
  have hrhopos : 0 < rho := by rw [hrho]; positivity
  set K : Set (Euclidean n) := closedBall z (2 * rho) with hK
  have hKcompact : IsCompact K := by
    rw [hK]
    exact isCompact_closedBall _ _
  have hKOmega : K ⊆ Omega := by
    intro y hy
    apply hball
    rw [hK, mem_closedBall] at hy
    rw [mem_ball]
    rw [hrho] at hy
    linarith
  have hKcont : ContinuousOn u K := hu_cont.mono hKOmega
  refine ⟨ball z rho, isOpen_ball, mem_ball_self hrhopos, ?_, ?_⟩
  · intro x hx
    apply hball
    rw [mem_ball] at hx ⊢
    rw [hrho] at hx
    linarith
  · intro x hxpatch
    have hxOmega : x ∈ Omega := by
      apply hball
      rw [mem_ball] at hxpatch ⊢
      rw [hrho] at hxpatch
      linarith
    by_contra hxm
    have hux : u x < m := lt_of_le_of_ne (hle x hxOmega) hxm
    have hxK : x ∈ K := by
      rw [hK, mem_closedBall]
      rw [mem_ball] at hxpatch
      linarith
    set F : Set (Euclidean n) := K ∩ u ⁻¹' {m} with hF
    have hFmem : ∀ y, y ∈ F ↔ y ∈ K ∧ u y = m := fun y => by
      rw [hF, mem_inter_iff, mem_preimage, mem_singleton_iff]
    have hFclosed : IsClosed F := by
      rw [hF]
      exact hKcont.preimage_isClosed_of_isClosed isClosed_closedBall
        isClosed_singleton
    have hFcompact : IsCompact F :=
      hKcompact.of_isClosed_subset hFclosed fun y hy => hy.1
    have hzK : z ∈ K := by rw [hK]; exact mem_closedBall_self (by positivity)
    have hzF : z ∈ F := (hFmem z).mpr ⟨hzK, hzm⟩
    have hFne : F.Nonempty := ⟨z, hzF⟩
    have hxF : x ∉ F := fun h => absurd ((hFmem x).mp h).2 (ne_of_lt hux)
    obtain ⟨y1, hy1F, hRdist⟩ := hFcompact.exists_infDist_eq_dist hFne x
    set R : Real := Metric.infDist x F with hR
    have hRpos : 0 < R := by
      rcases (Metric.infDist_nonneg (s := F) (x := x)).lt_or_eq with hgt | heq
      · rw [hR]
        exact hgt
      · exfalso
        have hd0 : dist x y1 = 0 := by rw [← hRdist]; exact heq.symm
        rw [dist_eq_zero] at hd0
        exact hxF (hd0 ▸ hy1F)
    have hRrho : R < rho := by
      rw [hR]
      exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hzF)
        (mem_ball.mp hxpatch)
    have hcbK : closedBall x R ⊆ K := by
      intro y hy
      rw [hK, mem_closedBall]
      have hyx : dist y x ≤ R := mem_closedBall.mp hy
      have hxz : dist x z < rho := mem_ball.mp hxpatch
      calc
        dist y z ≤ dist y x + dist x z := dist_triangle _ _ _
        _ ≤ 2 * rho := by linarith
    have hcbOmega : closedBall x R ⊆ Omega := fun y hy => hKOmega (hcbK hy)
    have hlt_inside : ∀ y, dist y x < R → u y < m := by
      intro y hyd
      have hycb : y ∈ closedBall x R := mem_closedBall.mpr hyd.le
      have hyOmega : y ∈ Omega := hcbOmega hycb
      refine lt_of_le_of_ne (hle y hyOmega) fun hym => ?_
      have hyF : y ∈ F := (hFmem y).mpr ⟨hcbK hycb, hym⟩
      have hdist : R ≤ dist x y := by
        rw [hR]
        exact Metric.infDist_le_dist_of_mem hyF
      rw [dist_comm] at hdist
      linarith
    have hy1sphere : y1 ∈ sphere x R := by
      rw [mem_sphere, dist_comm, ← hRdist]
    have hy1K : y1 ∈ K := ((hFmem y1).mp hy1F).1
    have hy1Omega : y1 ∈ Omega := hKOmega hy1K
    have hy1eq : u y1 = m := ((hFmem y1).mp hy1F).2
    have hy1norm : ‖y1 - x‖ = R := by
      rw [← dist_eq_norm]
      exact mem_sphere.mp hy1sphere
    have hnormal : 0 < ⟪y1 - x, R⁻¹ • (y1 - x)⟫_Real := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hy1norm]
      positivity
    obtain ⟨lambda, hlambda, helliptic'⟩ := helliptic
    have hhopf := hopf_boundary_point_liminf_pos
      (center := x) (x0 := y1) (R := R) hRpos hy1sphere
      (ha.mono hcbOmega)
      (hb.mono hcbOmega)
      (hc_cont.mono hcbOmega)
      (huC2.mono fun y hy => hcbOmega (mem_closedBall.mpr (mem_ball.mp hy).le))
      (hu_cont.mono fun y hy => by
        rcases hy with hy | hy
        · exact hcbOmega (mem_closedBall.mpr (mem_ball.mp hy).le)
        · have hyy1 : y = y1 := by simpa only [mem_singleton_iff] using hy
          rw [hyy1]
          exact hy1Omega)
      ⟨lambda, hlambda, fun y hy =>
        helliptic' y (hcbOmega (mem_closedBall.mpr (mem_ball.mp hy).le))⟩
      (fun y hy => hLu y (hcbOmega (mem_closedBall.mpr (mem_ball.mp hy).le)))
      (fun y hy => hc y (hcbOmega (mem_closedBall.mpr (mem_ball.mp hy).le)))
      (fun y hy => by rw [hy1eq]; exact hlt_inside y (mem_ball.mp hy))
      (hy1eq.symm ▸ hm0) hnormal
    have hlocal : IsLocalMax u y1 := by
      filter_upwards [hOmega_open.mem_nhds hy1Omega] with y hy
      rw [hy1eq]
      exact hle y hy
    have hfilter : (𝓝[>] (0 : Real)) ≤ 𝓝[≠] (0 : Real) := by
      apply nhdsWithin_mono
      intro t ht
      simp only [mem_Ioi] at ht
      simpa only [mem_compl_iff, mem_singleton_iff] using ne_of_gt ht
    have hreal : Tendsto
        (fun t : Real => (u y1 - u (y1 - t • (y1 - x))) / t)
        (𝓝[>] (0 : Real)) (𝓝 0) :=
      (tendsto_difference_quotient_zero_of_isLocalMax
        (v := y1 - x)
        ((huC2 y1 hy1Omega).contDiffAt
          (hOmega_open.mem_nhds hy1Omega)) hlocal).mono_left hfilter
    have hereal : Tendsto
        (fun t : Real =>
          (((u y1 - u (y1 - t • (y1 - x))) / t : Real) : EReal))
        (𝓝[>] (0 : Real)) (𝓝 (0 : EReal)) :=
      EReal.tendsto_coe.mpr hreal
    have hlimzero := hereal.liminf_eq
    rw [hlimzero] at hhopf
    exact (lt_irrefl (0 : EReal)) hhopf

/-- Interior form of the strong maximum principle.  Only continuity on the
open domain is needed because no boundary value is asserted. -/
theorem strong_maximum_principle_interior
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a Omega)
    (hb : ContinuousOn b Omega)
    (hc_cont : ContinuousOn c Omega)
    (huC2 : ContDiffOn Real 2 u Omega)
    (hu_cont : ContinuousOn u Omega)
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c u x)
    (hc : ∀ x ∈ Omega, c x ≤ 0)
    {x0 : Euclidean n} (hx0 : x0 ∈ Omega)
    (hmax : ∀ x ∈ Omega, u x ≤ u x0) (hu0 : 0 ≤ u x0) :
    ∀ x ∈ Omega, u x = u x0 := by
  classical
  set m : Real := u x0 with hm
  have hle : ∀ x ∈ Omega, u x ≤ m := by simpa [hm] using hmax
  have hpatch : ∀ {z : Euclidean n}, z ∈ Omega → u z = m →
      ∃ O : Set (Euclidean n), IsOpen O ∧ z ∈ O ∧ O ⊆ Omega ∧
        ∀ x ∈ O, u x = m := by
    intro z hz hzm
    exact exists_eqOn_neighborhood_of_nonnegative_max hOmega_open ha hb
      hc_cont huC2 hu_cont helliptic hLu hc (hm ▸ hu0) hle hz hzm
  set Umax : Set (Euclidean n) :=
    ⋃ (z : {x // x ∈ Omega ∧ u x = m}),
      Classical.choose (hpatch z.2.1 z.2.2) with hUmax
  have hUmax_spec : ∀ z : {x // x ∈ Omega ∧ u x = m},
      IsOpen (Classical.choose (hpatch z.2.1 z.2.2)) ∧
        z.1 ∈ Classical.choose (hpatch z.2.1 z.2.2) ∧
        Classical.choose (hpatch z.2.1 z.2.2) ⊆ Omega ∧
        ∀ x ∈ Classical.choose (hpatch z.2.1 z.2.2), u x = m := by
    intro z
    exact Classical.choose_spec (hpatch z.2.1 z.2.2)
  have hUmax_open : IsOpen Umax :=
    isOpen_iUnion fun z => (hUmax_spec z).1
  have hUmax_eq : ∀ x ∈ Umax, u x = m := by
    intro x hx
    obtain ⟨O, ⟨z, rfl⟩, hxO⟩ := hx
    exact (hUmax_spec z).2.2.2 x hxO
  have hUmax_sub : Umax ⊆ Omega := by
    intro x hx
    obtain ⟨O, ⟨z, rfl⟩, hxO⟩ := hx
    exact (hUmax_spec z).2.2.1 hxO
  have hx0Umax : x0 ∈ Umax := by
    apply mem_iUnion.mpr
    refine ⟨⟨x0, hx0, rfl⟩, ?_⟩
    exact (hUmax_spec ⟨x0, hx0, rfl⟩).2.1
  have hUmax_closure : closure Umax ∩ Omega ⊆ Umax := by
    rintro x ⟨hxclosure, hxOmega⟩
    haveI : (𝓝[Umax] x).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hxclosure
    have htend : Tendsto u (𝓝[Umax] x) (𝓝 (u x)) :=
      ((hu_cont x hxOmega).mono hUmax_sub).tendsto
    have htend_const : Tendsto u (𝓝[Umax] x) (𝓝 m) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_mem_nhdsWithin] with y hy
      exact (hUmax_eq y hy).symm
    have hxm : u x = m := tendsto_nhds_unique htend htend_const
    exact mem_iUnion.mpr
      ⟨⟨x, hxOmega, hxm⟩, (hUmax_spec ⟨x, hxOmega, hxm⟩).2.1⟩
  have hOmega_sub : Omega ⊆ Umax :=
    hOmega_connected.isPreconnected.subset_of_closure_inter_subset
      hUmax_open ⟨x0, hx0, hx0Umax⟩ hUmax_closure
  intro x hx
  rw [hm]
  exact hUmax_eq x (hOmega_sub hx)

/-- Han--Lin Theorem 2.8, the strong maximum principle.  A nonnegative
maximum on the closure of a bounded connected domain is either attained on
the frontier or forces the function to be constant on the whole closure. -/
theorem strong_maximum_principle
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u : Euclidean n → Real}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (hOmega_open : IsOpen Omega)
    (_hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    (helliptic : ∃ lambda : Real, 0 < lambda ∧
      ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hLu : ∀ x ∈ Omega, 0 ≤ nondivergenceOperator a b c u x)
    (hc : ∀ x ∈ Omega, c x ≤ 0)
    {x0 : Euclidean n} (hx0 : x0 ∈ closure Omega)
    (hmax : ∀ x ∈ closure Omega, u x ≤ u x0) (hu0 : 0 ≤ u x0) :
    x0 ∈ frontier Omega ∨ ∀ x ∈ closure Omega, u x = u x0 := by
  classical
  by_cases hx0frontier : x0 ∈ frontier Omega
  · exact Or.inl hx0frontier
  right
  have hx0Omega : x0 ∈ Omega := by
    by_contra hx0not
    apply hx0frontier
    rw [hOmega_open.frontier_eq]
    exact ⟨hx0, hx0not⟩
  have hconst_Omega : ∀ x ∈ Omega, u x = u x0 :=
    strong_maximum_principle_interior hOmega_open hOmega_connected
      (ha.mono fun x hx => subset_closure hx)
      (hb.mono fun x hx => subset_closure hx)
      (hc_cont.mono fun x hx => subset_closure hx) huC2
      (hu_cont.mono fun x hx => subset_closure hx) helliptic hLu hc
      hx0Omega (fun x hx => hmax x (subset_closure hx)) hu0
  set E : Set (Euclidean n) := closure Omega ∩ u ⁻¹' {u x0} with hE
  have hEclosed : IsClosed E := by
    rw [hE]
    exact hu_cont.preimage_isClosed_of_isClosed isClosed_closure
      isClosed_singleton
  have hOmegaE : Omega ⊆ E := by
    intro x hx
    rw [hE, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨subset_closure hx, hconst_Omega x hx⟩
  have hclosureE : closure Omega ⊆ E := by
    rw [← hEclosed.closure_eq]
    exact closure_mono hOmegaE
  intro x hx
  have hxE := hclosureE hx
  rw [hE, mem_inter_iff, mem_preimage, mem_singleton_iff] at hxE
  exact hxE.2

end HanLinLectureNotes.Ch02

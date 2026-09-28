import HanLinLectureNotes.Ch02.WeakMaximum
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Han--Lin Chapter 2: a priori estimates

This file develops the exponential slab barrier used for the Dirichlet
sup-norm estimate in Theorem 2.24.
-/

open Filter InnerProductSpace Metric Set Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The one-coordinate exponential barrier on a slab of width at most twice
the diameter. -/
def slabBarrier {n : Nat} (alpha d : Real) (x0 : Euclidean n) (i : Fin n) :
    Euclidean n -> Real :=
  fun x => Real.exp (2 * alpha * d) -
    Real.exp (alpha * (d + inner Real (x - x0)
      (EuclideanSpace.basisFun (Fin n) Real i)))

lemma slabBarrier_contDiff {n : Nat} (alpha d : Real)
    (x0 : Euclidean n) (i : Fin n) :
    ContDiff Real ∞ (slabBarrier alpha d x0 i) := by
  unfold slabBarrier
  exact contDiff_const.sub
    (contDiff_const.mul
      (contDiff_const.add
        ((contDiff_id.sub contDiff_const).inner Real contDiff_const))).exp

lemma fderiv_slabBarrier {n : Nat} (alpha d : Real)
    (x0 x v : Euclidean n) (i : Fin n) :
    fderiv Real (slabBarrier alpha d x0 i) x v =
      -alpha * Real.exp (alpha * (d + inner Real (x - x0)
        (EuclideanSpace.basisFun (Fin n) Real i))) *
        inner Real (EuclideanSpace.basisFun (Fin n) Real i) v := by
  let e : Euclidean n := EuclideanSpace.basisFun (Fin n) Real i
  have hr : HasFDerivAt
      (fun y : Euclidean n => d + inner Real (y - x0) e) _ x :=
    (hasFDerivAt_const d x).add
      (((hasFDerivAt_id x).sub_const x0).inner Real (hasFDerivAt_const e x))
  have he := (hr.const_mul alpha).exp
  have hc : HasFDerivAt (fun _ : Euclidean n => Real.exp (2 * alpha * d))
      (0 : Euclidean n →L[Real] Real) x :=
    hasFDerivAt_const (Real.exp (2 * alpha * d)) x
  have h := hc.sub he
  change (fderiv Real
      ((fun _ : Euclidean n => Real.exp (2 * alpha * d)) -
        fun y => Real.exp (alpha * (d + inner Real (y - x0) e))) x) v = _
  rw [h.fderiv]
  simp [e, real_inner_comm]
  ring

lemma fderiv_fderiv_slabBarrier {n : Nat} (alpha d : Real)
    (x0 x u v : Euclidean n) (i : Fin n) :
    fderiv Real (fun y => fderiv Real (slabBarrier alpha d x0 i) y v) x u =
      -(alpha ^ 2) * Real.exp (alpha * (d + inner Real (x - x0)
        (EuclideanSpace.basisFun (Fin n) Real i))) *
        inner Real (EuclideanSpace.basisFun (Fin n) Real i) u *
        inner Real (EuclideanSpace.basisFun (Fin n) Real i) v := by
  let e : Euclidean n := EuclideanSpace.basisFun (Fin n) Real i
  have hfun : (fun y => fderiv Real (slabBarrier alpha d x0 i) y v) =
      fun y => (-alpha * inner Real e v) *
        Real.exp (alpha * (d + inner Real (y - x0) e)) := by
    funext y
    rw [fderiv_slabBarrier alpha d x0 y v i]
    dsimp [e]
    ring
  rw [hfun]
  have hr : HasFDerivAt
      (fun y : Euclidean n => d + inner Real (y - x0) e) _ x :=
    (hasFDerivAt_const d x).add
      (((hasFDerivAt_id x).sub_const x0).inner Real (hasFDerivAt_const e x))
  have he := (hr.const_mul alpha).exp
  have hmul := he.const_mul (-alpha * inner Real e v)
  rw [hmul.fderiv]
  simp [e, real_inner_comm]
  ring

lemma nondivergenceOperator_slabBarrier
    {n : Nat} {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (alpha d : Real) (x0 x : Euclidean n) (i : Fin n) :
    nondivergenceOperator a b c (slabBarrier alpha d x0 i) x =
      -(a x i i * alpha ^ 2 + b x i * alpha) *
        Real.exp (alpha * (d + inner Real (x - x0)
          (EuclideanSpace.basisFun (Fin n) Real i))) +
      c x * slabBarrier alpha d x0 i x := by
  rw [nondivergenceOperator_eq_coordinate
    ((slabBarrier_contDiff alpha d x0 i).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  simp_rw [fderiv_fderiv_slabBarrier, fderiv_slabBarrier]
  simp only [OrthonormalBasis.inner_eq_ite]
  simp
  ring

/-- Exponent chosen using only the ellipticity and drift bounds. -/
def dirichletAPrioriAlpha (lambda Lambda : Real) : Real :=
  (Lambda + lambda + 1) / lambda

/-- Explicit constant in the Dirichlet sup-norm estimate. -/
def dirichletAPrioriConstant (lambda Lambda d : Real) : Real :=
  Real.exp (2 * dirichletAPrioriAlpha lambda Lambda * d) - 1

lemma dirichletAPrioriAlpha_pos {lambda Lambda : Real}
    (hlambda : 0 < lambda) (hLambda : 0 <= Lambda) :
    0 < dirichletAPrioriAlpha lambda Lambda := by
  unfold dirichletAPrioriAlpha
  exact div_pos (by linarith) hlambda

lemma one_le_dirichletAPrioriAlpha {lambda Lambda : Real}
    (hlambda : 0 < lambda) (hLambda : 0 <= Lambda) :
    1 <= dirichletAPrioriAlpha lambda Lambda := by
  rw [dirichletAPrioriAlpha, le_div_iff₀ hlambda]
  linarith

lemma dirichletAPriori_coefficient_one_le
    {lambda Lambda A B : Real} (hlambda : 0 < lambda)
    (hLambda : 0 <= Lambda) (hA : lambda <= A) (hB : -Lambda <= B) :
    1 <= A * dirichletAPrioriAlpha lambda Lambda ^ 2 +
      B * dirichletAPrioriAlpha lambda Lambda := by
  set alpha := dirichletAPrioriAlpha lambda Lambda with halpha
  have halpha_pos : 0 < alpha := by
    rw [halpha]
    exact dirichletAPrioriAlpha_pos hlambda hLambda
  have halpha_one : 1 <= alpha := by
    rw [halpha]
    exact one_le_dirichletAPrioriAlpha hlambda hLambda
  have hkey : lambda * alpha = Lambda + lambda + 1 := by
    rw [halpha, dirichletAPrioriAlpha]
    field_simp
  have hbase : 1 <= lambda * alpha ^ 2 - Lambda * alpha := by
    rw [show lambda * alpha ^ 2 - Lambda * alpha =
      alpha * (lambda * alpha - Lambda) by ring, hkey]
    nlinarith
  have hleading : 0 <= (A - lambda) * alpha ^ 2 :=
    mul_nonneg (sub_nonneg.mpr hA) (sq_nonneg alpha)
  have hdrift : 0 <= (B + Lambda) * alpha :=
    mul_nonneg (by linarith) halpha_pos.le
  nlinarith

lemma diagonal_ge_of_uniformlyElliptic
    {n : Nat} {A : Matrix (Fin n) (Fin n) Real} {lambda : Real}
    (hA : UniformlyElliptic A lambda) (i : Fin n) :
    lambda <= A i i := by
  have h := hA (fun j => if j = i then 1 else 0)
  simp [dotProduct, Matrix.mulVec] at h
  simpa [eq_comm] using h

lemma abs_inner_basis_sub_le_diam
    {n : Nat} {Omega : Set (Euclidean n)}
    (hbounded : Bornology.IsBounded Omega)
    {x0 x : Euclidean n} (hx0 : x0 ∈ Omega) (hx : x ∈ closure Omega)
    (i : Fin n) :
    |inner Real (x - x0) (EuclideanSpace.basisFun (Fin n) Real i)| <=
      Metric.diam Omega := by
  have hdist : dist x x0 <= Metric.diam Omega := by
    have h := Metric.dist_le_diam_of_mem hbounded.closure hx (subset_closure hx0)
    rwa [Metric.diam_closure] at h
  calc
    |inner Real (x - x0) (EuclideanSpace.basisFun (Fin n) Real i)| <=
        ‖x - x0‖ * ‖EuclideanSpace.basisFun (Fin n) Real i‖ :=
      abs_real_inner_le_norm _ _
    _ = dist x x0 := by simp [dist_eq_norm]
    _ <= Metric.diam Omega := hdist

lemma slabBarrier_nonneg_and_le_constant_on_closure
    {n : Nat} {Omega : Set (Euclidean n)}
    {lambda Lambda : Real} (hlambda : 0 < lambda) (hLambda : 0 <= Lambda)
    (hbounded : Bornology.IsBounded Omega)
    {x0 x : Euclidean n} (hx0 : x0 ∈ Omega) (hx : x ∈ closure Omega)
    (i : Fin n) :
    0 <= slabBarrier (dirichletAPrioriAlpha lambda Lambda)
        (Metric.diam Omega) x0 i x ∧
      slabBarrier (dirichletAPrioriAlpha lambda Lambda)
          (Metric.diam Omega) x0 i x <=
        dirichletAPrioriConstant lambda Lambda (Metric.diam Omega) := by
  set alpha := dirichletAPrioriAlpha lambda Lambda with halpha
  set d := Metric.diam Omega with hd
  set r := d + inner Real (x - x0)
    (EuclideanSpace.basisFun (Fin n) Real i) with hr
  have halpha_nonneg : 0 <= alpha := by
    rw [halpha]
    exact (dirichletAPrioriAlpha_pos hlambda hLambda).le
  have hd_nonneg : 0 <= d := by
    rw [hd]
    exact Metric.diam_nonneg
  have hcoord := abs_inner_basis_sub_le_diam hbounded hx0 hx i
  have hr_nonneg : 0 <= r := by
    rw [hr, hd]
    linarith [neg_le_of_abs_le hcoord]
  have hr_le : r <= 2 * d := by
    rw [hr, hd]
    linarith [le_of_abs_le hcoord]
  have hexp_le : Real.exp (alpha * r) <= Real.exp (2 * alpha * d) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hone_le : 1 <= Real.exp (alpha * r) :=
    Real.one_le_exp (mul_nonneg halpha_nonneg hr_nonneg)
  constructor
  · rw [slabBarrier, ← hr]
    exact sub_nonneg.mpr hexp_le
  · rw [slabBarrier, dirichletAPrioriConstant, ← hr]
    linarith

lemma nondivergenceOperator_slabBarrier_le_neg_one
    {n : Nat} {Omega : Set (Euclidean n)}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    {lambda Lambda : Real} (hlambda : 0 < lambda) (hLambda : 0 <= Lambda)
    (hbounded : Bornology.IsBounded Omega)
    (helliptic : forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda)
    (hb : forall x, x ∈ Omega -> forall i, |b x i| <= Lambda)
    (hc : forall x, x ∈ Omega -> c x <= 0)
    {x0 x : Euclidean n} (hx0 : x0 ∈ Omega) (hx : x ∈ Omega)
    (i : Fin n) :
    nondivergenceOperator a b c
        (slabBarrier (dirichletAPrioriAlpha lambda Lambda)
          (Metric.diam Omega) x0 i) x <= -1 := by
  set alpha := dirichletAPrioriAlpha lambda Lambda with halpha
  set d := Metric.diam Omega with hd
  set r := d + inner Real (x - x0)
    (EuclideanSpace.basisFun (Fin n) Real i) with hr
  have hbarrier := slabBarrier_nonneg_and_le_constant_on_closure
    hlambda hLambda hbounded hx0 (subset_closure hx) i
  have hAii : lambda <= a x i i :=
    diagonal_ge_of_uniformlyElliptic (helliptic x hx) i
  have hbi : -Lambda <= b x i := neg_le_of_abs_le (hb x hx i)
  have hcoef : 1 <= a x i i * alpha ^ 2 + b x i * alpha := by
    rw [halpha]
    exact dirichletAPriori_coefficient_one_le hlambda hLambda hAii hbi
  have halpha_nonneg : 0 <= alpha := by
    rw [halpha]
    exact (dirichletAPrioriAlpha_pos hlambda hLambda).le
  have hd_nonneg : 0 <= d := by
    rw [hd]
    exact Metric.diam_nonneg
  have hcoord := abs_inner_basis_sub_le_diam hbounded hx0 (subset_closure hx) i
  have hr_nonneg : 0 <= r := by
    rw [hr, hd]
    linarith [neg_le_of_abs_le hcoord]
  have hexp : 1 <= Real.exp (alpha * r) :=
    Real.one_le_exp (mul_nonneg halpha_nonneg hr_nonneg)
  have hprod : 1 <=
      (a x i i * alpha ^ 2 + b x i * alpha) * Real.exp (alpha * r) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcoef) (sub_nonneg.mpr hexp)]
  have hzero : c x * slabBarrier alpha d x0 i x <= 0 :=
    mul_nonpos_of_nonpos_of_nonneg (hc x hx) (by
      simpa [halpha, hd] using hbarrier.1)
  rw [nondivergenceOperator_slabBarrier, ← hr]
  nlinarith

lemma nondivergenceOperator_const
    {n : Nat} {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (k : Real) (x : Euclidean n) :
    nondivergenceOperator a b c (fun _ => k) x = c x * k := by
  rw [nondivergenceOperator_eq_coordinate
    (contDiffAt_const (x := x) (c := k) (n := 2))]
  simp

lemma nondivergenceOperator_const_smul
    {n : Nat} {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    {u : Euclidean n -> Real} {x : Euclidean n}
    (t : Real) (hu : ContDiffAt Real 2 u x) :
    nondivergenceOperator a b c (t • u) x =
      t * nondivergenceOperator a b c u x := by
  have h := nondivergenceOperator_add_const_smul
    (a := a) (b := b) (c := c) t
    (contDiffAt_const (x := x) (c := (0 : Real)) (n := 2)) hu
  rw [show (fun _ : Euclidean n => (0 : Real)) + t • u = t • u by
    funext y
    simp] at h
  simpa [nondivergenceOperator_const] using h

private lemma nonpositive_on_closure_of_weak_maximum
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {v : Euclidean n -> Real}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (hOmega_open : IsOpen Omega) (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (hvC2 : ContDiffOn Real 2 v Omega)
    (hv_cont : ContinuousOn v (closure Omega))
    (helliptic : exists lambda : Real, 0 < lambda ∧
      forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda)
    (hLv : forall x, x ∈ Omega ->
      0 <= nondivergenceOperator a b c v x)
    (hc : forall x, x ∈ Omega -> c x <= 0)
    (hboundary : forall x, x ∈ frontier Omega -> v x <= 0) :
    forall x, x ∈ closure Omega -> v x <= 0 := by
  intro x hx
  by_contra hxpos
  rw [not_le] at hxpos
  have hcompact : IsCompact (closure Omega) :=
    isCompact_iff_isClosed_bounded.mpr
      ⟨isClosed_closure, hOmega_bounded.closure⟩
  have hclosure_ne : (closure Omega).Nonempty :=
    hOmega_connected.nonempty.mono subset_closure
  obtain ⟨x0, hx0, hx0max⟩ :=
    hcompact.exists_isMaxOn hclosure_ne hv_cont
  have hx0pos : 0 < v x0 :=
    hxpos.trans_le ((isMaxOn_iff.mp hx0max) x hx)
  obtain ⟨z, hzfrontier, hzmax⟩ :=
    weak_maximum_principle hOmega_open hOmega_bounded hOmega_connected
      ha hb hc_cont hvC2 hv_cont helliptic hLv hc hx0 hx0max hx0pos.le
  have hx0z : v x0 <= v z :=
    (isMaxOn_iff.mp hzmax) x0 hx0
  linarith [hboundary z hzfrontier]

/-- Han--Lin Theorem 2.24. A solution of a uniformly elliptic Dirichlet
problem with nonpositive zero-order coefficient is bounded by its boundary
data and forcing. The displayed constant depends only on the ellipticity
constant, the drift bound, and the diameter of the domain. -/
theorem dirichlet_apriori_estimate
    {n : Nat} [Nonempty (Fin n)] {Omega : Set (Euclidean n)}
    {u f : Euclidean n -> Real}
    {a : Euclidean n -> Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n -> Fin n -> Real} {c : Euclidean n -> Real}
    (hOmega_open : IsOpen Omega) (hOmega_bounded : Bornology.IsBounded Omega)
    (hOmega_connected : IsConnected Omega)
    (ha : ContinuousOn a (closure Omega))
    (hb_cont : ContinuousOn b (closure Omega))
    (hc_cont : ContinuousOn c (closure Omega))
    (huC2 : ContDiffOn Real 2 u Omega)
    (hu_cont : ContinuousOn u (closure Omega))
    {lambda Lambda Phi F : Real}
    (hlambda : 0 < lambda) (hLambda : 0 <= Lambda)
    (hPhi : 0 <= Phi) (hF : 0 <= F)
    (helliptic : forall x, x ∈ Omega -> UniformlyElliptic (a x) lambda)
    (hb : forall x, x ∈ Omega -> forall i, |b x i| <= Lambda)
    (hc : forall x, x ∈ Omega -> c x <= 0)
    (hLu : forall x, x ∈ Omega ->
      nondivergenceOperator a b c u x = f x)
    (hboundary : forall x, x ∈ frontier Omega -> |u x| <= Phi)
    (hf : forall x, x ∈ Omega -> |f x| <= F) :
    forall x, x ∈ closure Omega ->
      |u x| <= Phi +
        dirichletAPrioriConstant lambda Lambda (Metric.diam Omega) * F := by
  classical
  obtain ⟨x0, hx0⟩ := hOmega_connected.nonempty
  let i : Fin n := Classical.choice (inferInstance : Nonempty (Fin n))
  let psi : Euclidean n -> Real :=
    slabBarrier (dirichletAPrioriAlpha lambda Lambda)
      (Metric.diam Omega) x0 i
  let W : Euclidean n -> Real := fun x => Phi + F * psi x
  have hpsiC2 : ContDiff Real 2 psi := by
    simpa only [psi] using
      (slabBarrier_contDiff (dirichletAPrioriAlpha lambda Lambda)
        (Metric.diam Omega) x0 i).of_le
          (by decide : (2 : ℕ∞ω) <= (∞ : ℕ∞ω))
  have hWC2 : ContDiff Real 2 W := by
    simpa only [W] using contDiff_const.add (contDiff_const.mul hpsiC2)
  have hWcont : ContinuousOn W (closure Omega) :=
    hWC2.continuous.continuousOn
  have hpsi_bounds : forall x, x ∈ closure Omega ->
      0 <= psi x ∧ psi x <=
        dirichletAPrioriConstant lambda Lambda (Metric.diam Omega) := by
    intro x hx
    simpa only [psi] using
      slabBarrier_nonneg_and_le_constant_on_closure
        hlambda hLambda hOmega_bounded hx0 hx i
  have hW_nonneg : forall x, x ∈ closure Omega -> 0 <= W x := by
    intro x hx
    change 0 <= Phi + F * psi x
    exact add_nonneg hPhi (mul_nonneg hF (hpsi_bounds x hx).1)
  have hLW : forall x, x ∈ Omega ->
      nondivergenceOperator a b c W x <= -F := by
    intro x hx
    have hpsiAt : ContDiffAt Real 2 psi x := hpsiC2.contDiffAt
    have hconstAt : ContDiffAt Real 2 (fun _ : Euclidean n => Phi) x :=
      contDiffAt_const
    have hlinear := nondivergenceOperator_add_const_smul
      (a := a) (b := b) (c := c) F hconstAt hpsiAt
    have hpsiop := nondivergenceOperator_slabBarrier_le_neg_one
      hlambda hLambda hOmega_bounded helliptic hb hc hx0 hx i
    have hcPhi : c x * Phi <= 0 :=
      mul_nonpos_of_nonpos_of_nonneg (hc x hx) hPhi
    have hscaled : F * nondivergenceOperator a b c psi x <= -F := by
      have hpsiop' : nondivergenceOperator a b c psi x <= -1 := by
        simpa only [psi] using hpsiop
      nlinarith
    rw [show W = (fun _ : Euclidean n => Phi) + F • psi by
      funext y
      simp [W]]
    rw [hlinear, nondivergenceOperator_const]
    linarith
  let qplus : Euclidean n -> Real := fun x => u x - W x
  have hqplusC2 : ContDiffOn Real 2 qplus Omega := by
    simpa only [qplus] using huC2.sub hWC2.contDiffOn
  have hqplus_cont : ContinuousOn qplus (closure Omega) := by
    apply (hu_cont.sub hWcont).congr
    intro x hx
    rfl
  have hLqplus : forall x, x ∈ Omega ->
      0 <= nondivergenceOperator a b c qplus x := by
    intro x hx
    have huAt : ContDiffAt Real 2 u x :=
      (huC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hlinear := nondivergenceOperator_add_const_smul
      (a := a) (b := b) (c := c) (-1 : Real) huAt hWC2.contDiffAt
    rw [show qplus = u + (-1 : Real) • W by
      funext y
      change u y - W y = u y + (-1 : Real) * W y
      ring]
    rw [hlinear, hLu x hx]
    have hf_lower : -F <= f x := neg_le_of_abs_le (hf x hx)
    linarith [hLW x hx]
  have hqplus_boundary : forall x, x ∈ frontier Omega -> qplus x <= 0 := by
    intro x hx
    have hxclosure := frontier_subset_closure hx
    have huPhi : u x <= Phi :=
      (le_abs_self (u x)).trans (hboundary x hx)
    have hPhiW : Phi <= W x := by
      change Phi <= Phi + F * psi x
      exact le_add_of_nonneg_right
        (mul_nonneg hF (hpsi_bounds x hxclosure).1)
    change u x - W x <= 0
    linarith
  have hqplus_nonpos := nonpositive_on_closure_of_weak_maximum
    hOmega_open hOmega_bounded hOmega_connected ha hb_cont hc_cont
      hqplusC2 hqplus_cont ⟨lambda, hlambda, helliptic⟩ hLqplus hc
      hqplus_boundary
  have hu_le_W : forall x, x ∈ closure Omega -> u x <= W x := by
    intro x hx
    have h := hqplus_nonpos x hx
    change u x - W x <= 0 at h
    linarith
  let uneg : Euclidean n -> Real := fun x => -u x
  have hunegC2 : ContDiffOn Real 2 uneg Omega := by
    simpa only [uneg] using huC2.neg
  have huneg_cont : ContinuousOn uneg (closure Omega) := by
    apply hu_cont.neg.congr
    intro x hx
    rfl
  let qminus : Euclidean n -> Real := fun x => uneg x - W x
  have hqminusC2 : ContDiffOn Real 2 qminus Omega := by
    simpa only [qminus] using hunegC2.sub hWC2.contDiffOn
  have hqminus_cont : ContinuousOn qminus (closure Omega) := by
    apply (huneg_cont.sub hWcont).congr
    intro x hx
    rfl
  have hLqminus : forall x, x ∈ Omega ->
      0 <= nondivergenceOperator a b c qminus x := by
    intro x hx
    have huAt : ContDiffAt Real 2 u x :=
      (huC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hunegAt : ContDiffAt Real 2 uneg x :=
      (hunegC2 x hx).contDiffAt (hOmega_open.mem_nhds hx)
    have hlinear := nondivergenceOperator_add_const_smul
      (a := a) (b := b) (c := c) (-1 : Real) hunegAt hWC2.contDiffAt
    have hunegop : nondivergenceOperator a b c uneg x = -f x := by
      rw [show uneg = (-1 : Real) • u by
        funext y
        simp [uneg]]
      rw [nondivergenceOperator_const_smul (-1 : Real) huAt, hLu x hx]
      ring
    rw [show qminus = uneg + (-1 : Real) • W by
      funext y
      change uneg y - W y = uneg y + (-1 : Real) * W y
      ring]
    rw [hlinear, hunegop]
    have hf_upper : f x <= F := le_of_abs_le (hf x hx)
    linarith [hLW x hx]
  have hqminus_boundary : forall x, x ∈ frontier Omega -> qminus x <= 0 := by
    intro x hx
    have hxclosure := frontier_subset_closure hx
    have hnegPhi : -u x <= Phi :=
      (neg_le_abs (u x)).trans (hboundary x hx)
    have hPhiW : Phi <= W x := by
      change Phi <= Phi + F * psi x
      exact le_add_of_nonneg_right
        (mul_nonneg hF (hpsi_bounds x hxclosure).1)
    change -u x - W x <= 0
    linarith
  have hqminus_nonpos := nonpositive_on_closure_of_weak_maximum
    hOmega_open hOmega_bounded hOmega_connected ha hb_cont hc_cont
      hqminusC2 hqminus_cont ⟨lambda, hlambda, helliptic⟩ hLqminus hc
      hqminus_boundary
  have hneg_u_le_W : forall x, x ∈ closure Omega -> -u x <= W x := by
    intro x hx
    have h := hqminus_nonpos x hx
    change -u x - W x <= 0 at h
    linarith
  intro x hx
  have habs : |u x| <= W x := abs_le.mpr
    ⟨by linarith [hneg_u_le_W x hx], hu_le_W x hx⟩
  have hW_upper : W x <= Phi +
      dirichletAPrioriConstant lambda Lambda (Metric.diam Omega) * F := by
    change Phi + F * psi x <= Phi +
      dirichletAPrioriConstant lambda Lambda (Metric.diam Omega) * F
    have := (hpsi_bounds x hx).2
    nlinarith
  exact habs.trans hW_upper

end HanLinLectureNotes.Ch02

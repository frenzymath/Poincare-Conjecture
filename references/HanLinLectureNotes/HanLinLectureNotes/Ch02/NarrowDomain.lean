import HanLinLectureNotes.Ch02.PositiveSupersolution

/-!
# Han--Lin Chapter 2: maximum principle on narrow domains

A quadratic barrier gives the positive supersolution required by the general
maximum principle when the domain has sufficiently small width in one direction.
-/

open Filter InnerProductSpace Metric Set Topology
open scoped ContDiff RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The signed coordinate in the direction `e`, based at `x₀`. -/
def narrowCoordinate {n : Nat} (e x₀ : Euclidean n) (x : Euclidean n) : Real :=
  inner Real e (x - x₀)

/-- A positive concave quadratic barrier on a strip of width `d` about `x₀`. -/
def narrowDomainBarrier {n : Nat} (e x₀ : Euclidean n) (d : Real) :
    Euclidean n → Real :=
  fun x => 2 * d ^ 2 - (narrowCoordinate e x₀ x) ^ 2

lemma narrowCoordinate_contDiff {n : Nat} (e x₀ : Euclidean n) :
    ContDiff Real 2 (narrowCoordinate e x₀) := by
  unfold narrowCoordinate
  exact (innerSL Real e).contDiff.comp (contDiff_id.sub contDiff_const)

lemma narrowDomainBarrier_contDiff {n : Nat} (e x₀ : Euclidean n) (d : Real) :
    ContDiff Real 2 (narrowDomainBarrier e x₀ d) := by
  unfold narrowDomainBarrier
  exact contDiff_const.sub ((narrowCoordinate_contDiff e x₀).pow 2)

lemma hasFDerivAt_narrowCoordinate {n : Nat} (e x₀ x : Euclidean n) :
    HasFDerivAt (narrowCoordinate e x₀) (innerSL Real e) x := by
  unfold narrowCoordinate
  exact (innerSL Real e).hasFDerivAt.comp x
    ((hasFDerivAt_id x).sub_const x₀)

lemma fderiv_narrowDomainBarrier {n : Nat} (e x₀ : Euclidean n) (d : Real)
    (x v : Euclidean n) :
    fderiv Real (narrowDomainBarrier e x₀ d) x v =
      -2 * narrowCoordinate e x₀ x * inner Real v e := by
  have ht := hasFDerivAt_narrowCoordinate e x₀ x
  have hsquare := ht.mul ht
  have hconst : HasFDerivAt (fun _ : Euclidean n => 2 * d ^ 2) 0 x :=
    hasFDerivAt_const (𝕜 := Real) (2 * d ^ 2) x
  have hfun :
      (fun _ : Euclidean n => 2 * d ^ 2) -
          narrowCoordinate e x₀ * narrowCoordinate e x₀ =
        narrowDomainBarrier e x₀ d := by
    funext y
    simp only [Pi.sub_apply, Pi.mul_apply, narrowDomainBarrier, pow_two]
  have hbar : HasFDerivAt (narrowDomainBarrier e x₀ d)
      (0 - (narrowCoordinate e x₀ x • innerSL Real e +
        narrowCoordinate e x₀ x • innerSL Real e)) x := by
    rw [← hfun]
    exact hconst.sub hsquare
  rw [hbar.fderiv]
  simp only [sub_apply, zero_apply, add_apply, smul_apply, innerSL_apply_apply,
    smul_eq_mul]
  rw [real_inner_comm e v]
  ring

lemma fderiv_fderiv_narrowDomainBarrier {n : Nat}
    (e x₀ : Euclidean n) (d : Real) (x u v : Euclidean n) :
    fderiv Real (fun y => fderiv Real (narrowDomainBarrier e x₀ d) y v) x u =
      -2 * inner Real u e * inner Real v e := by
  have hfun :
      (fun y => fderiv Real (narrowDomainBarrier e x₀ d) y v) =
        fun y => -2 * narrowCoordinate e x₀ y * inner Real v e :=
    funext fun y => fderiv_narrowDomainBarrier e x₀ d y v
  rw [hfun]
  have ht := hasFDerivAt_narrowCoordinate e x₀ x
  have hscaled : HasFDerivAt
      (fun y => (-2 * inner Real v e) * narrowCoordinate e x₀ y)
      ((-2 * inner Real v e) • innerSL Real e) x :=
    ht.const_mul (-2 * inner Real v e)
  have heq :
      (fun y => -2 * narrowCoordinate e x₀ y * inner Real v e) =
        fun y => (-2 * inner Real v e) * narrowCoordinate e x₀ y := by
    funext y
    ring
  rw [heq, hscaled.fderiv]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm e u]
  ring

lemma nondivergenceOperator_narrowDomainBarrier
    {n : Nat} {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    (e x₀ : Euclidean n) (d : Real) (x : Euclidean n) :
    nondivergenceOperator a b c (narrowDomainBarrier e x₀ d) x =
      -2 * (e ⬝ᵥ ((a x).mulVec e)) -
        2 * narrowCoordinate e x₀ x * (∑ i, b x i * e i) +
        c x * narrowDomainBarrier e x₀ d x := by
  rw [nondivergenceOperator_eq_coordinate
    (narrowDomainBarrier_contDiff e x₀ d).contDiffAt]
  simp_rw [fderiv_fderiv_narrowDomainBarrier,
    fderiv_narrowDomainBarrier]
  have hebasis : ∀ i : Fin n,
      inner Real (EuclideanSpace.basisFun (Fin n) Real i) e = e i := by
    intro i
    rw [real_inner_comm]
    exact EuclideanSpace.inner_basisFun_real (Fin n) e i
  simp_rw [hebasis]
  have hsecond :
      (∑ i, ∑ j, a x i j * (-2 * e i * e j)) =
        -2 * ∑ i, ∑ j, e i * a x i j * e j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hfirst :
      (∑ i, b x i * (-2 * narrowCoordinate e x₀ x * e i)) =
        -2 * narrowCoordinate e x₀ x * ∑ i, b x i * e i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hdot :
      e ⬝ᵥ ((a x).mulVec e) = ∑ i, ∑ j, e i * a x i j * e j := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hsecond, hfirst, hdot]
  ring

lemma narrowCoordinate_abs_le_on_closure
    {n : Nat} {Omega : Set (Euclidean n)} {e x₀ : Euclidean n} {d : Real}
    (hx₀ : x₀ ∈ Omega)
    (hwidth : ∀ x ∈ Omega, ∀ y ∈ Omega,
      |inner Real (y - x) e| < d) :
    ∀ x ∈ closure Omega, |narrowCoordinate e x₀ x| ≤ d := by
  have hsubset : Omega ⊆ {x | |narrowCoordinate e x₀ x| ≤ d} := by
    intro x hx
    exact le_of_lt (by
      simpa only [narrowCoordinate, real_inner_comm] using
        hwidth x₀ hx₀ x hx)
  have hclosed : IsClosed {x | |narrowCoordinate e x₀ x| ≤ d} :=
    isClosed_le (narrowCoordinate_contDiff e x₀).continuous.abs continuous_const
  exact closure_minimal hsubset hclosed

lemma narrowDomainBarrier_bounds
    {n : Nat} {e x₀ x : Euclidean n} {d : Real}
    (hd : 0 < d) (hx : |narrowCoordinate e x₀ x| ≤ d) :
    0 < narrowDomainBarrier e x₀ d x ∧
      narrowDomainBarrier e x₀ d x ≤ 2 * d ^ 2 := by
  have hupper := (abs_le.mp hx).2
  have hlower := (abs_le.mp hx).1
  have hplus : 0 ≤ d + narrowCoordinate e x₀ x := by linarith
  have hsq : (narrowCoordinate e x₀ x) ^ 2 ≤ d ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hupper) hplus]
  constructor
  · unfold narrowDomainBarrier
    nlinarith [sq_pos_of_pos hd]
  · unfold narrowDomainBarrier
    nlinarith [sq_nonneg (narrowCoordinate e x₀ x)]

private lemma sum_sq_eq_one_of_norm_eq_one
    {n : Nat} {e : Euclidean n} (he : ‖e‖ = 1) :
    (∑ i, (e i) ^ 2) = 1 := by
  have h := EuclideanSpace.norm_sq_eq e
  rw [he] at h
  norm_num [Real.norm_eq_abs, sq_abs] at h ⊢
  exact h.symm

private lemma abs_coordinate_le_one_of_norm_eq_one
    {n : Nat} {e : Euclidean n} (he : ‖e‖ = 1) (i : Fin n) :
    |e i| ≤ 1 := by
  rw [← EuclideanSpace.inner_basisFun_real (Fin n) e i]
  have h := abs_real_inner_le_norm e
    (EuclideanSpace.basisFun (Fin n) Real i)
  simpa [he] using h

private lemma directional_drift_le
    {n : Nat} {b : Euclidean n → Fin n → Real}
    {B : Real} (hB : 0 ≤ B) {e : Euclidean n} (he : ‖e‖ = 1)
    {x : Euclidean n} (hb : ∀ i, |b x i| ≤ B) :
    |∑ i, b x i * e i| ≤ (n : Real) * B := by
  calc
    |∑ i, b x i * e i| ≤ ∑ i, |b x i * e i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin n, B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      calc
        |b x i| * |e i| ≤ B * 1 :=
          mul_le_mul (hb i) (abs_coordinate_le_one_of_norm_eq_one he i)
            (abs_nonneg _) hB
        _ = B := mul_one B
    _ = (n : Real) * B := by simp

/-- An explicit width threshold depending only on ellipticity and the uniform
drift and positive zero-order bounds (and the fixed ambient dimension). -/
def narrowDomainWidthThreshold (n : Nat) (lambda B C : Real) : Real :=
  min 1 (lambda / ((n : Real) * B + C + 1))

lemma narrowDomainWidthThreshold_pos
    {n : Nat} {lambda B C : Real}
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hC : 0 ≤ C) :
    0 < narrowDomainWidthThreshold n lambda B C := by
  have hdenom : 0 < (n : Real) * B + C + 1 := by positivity
  rw [narrowDomainWidthThreshold, lt_min_iff]
  exact ⟨zero_lt_one, div_pos hlambda hdenom⟩

private lemma narrowDomainWidthThreshold_small
    {n : Nat} {lambda B C d : Real}
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hd : 0 < d)
    (hd₀ : d ≤ narrowDomainWidthThreshold n lambda B C) :
    (n : Real) * B * d + C * d ^ 2 ≤ lambda := by
  have hdenom : 0 < (n : Real) * B + C + 1 := by positivity
  have hd_one : d ≤ 1 := hd₀.trans (min_le_left _ _)
  have hd_frac : d ≤ lambda / ((n : Real) * B + C + 1) :=
    hd₀.trans (min_le_right _ _)
  have hmul : d * ((n : Real) * B + C + 1) ≤ lambda :=
    (le_div_iff₀ hdenom).mp hd_frac
  have hdsq : d ^ 2 ≤ d := by nlinarith
  have hcpart : C * d ^ 2 ≤ C * d :=
    mul_le_mul_of_nonneg_left hdsq hC
  calc
    (n : Real) * B * d + C * d ^ 2 ≤
        (n : Real) * B * d + C * d := add_le_add_right hcpart _
    _ ≤ d * ((n : Real) * B + C + 1) := by nlinarith [hd.le]
    _ ≤ lambda := hmul

private lemma narrowDomainBarrier_operator_nonpos
    {n : Nat} {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    {lambda B C d : Real} (hB : 0 ≤ B) (hC : 0 ≤ C)
    {e x₀ x : Euclidean n} (he : ‖e‖ = 1) (hd : 0 < d)
    (helliptic : UniformlyElliptic (a x) lambda)
    (hb : ∀ i, |b x i| ≤ B) (hc : max (c x) 0 ≤ C)
    (hcoordinate : |narrowCoordinate e x₀ x| ≤ d)
    (hsmall : (n : Real) * B * d + C * d ^ 2 ≤ lambda) :
    nondivergenceOperator a b c (narrowDomainBarrier e x₀ d) x ≤ 0 := by
  have hquad : lambda ≤ e ⬝ᵥ ((a x).mulVec e) := by
    have h := helliptic e
    rw [sum_sq_eq_one_of_norm_eq_one he] at h
    simpa using h
  have hlead : -2 * (e ⬝ᵥ ((a x).mulVec e)) ≤ -2 * lambda :=
    mul_le_mul_of_nonpos_left hquad (by norm_num)
  have hdirection := directional_drift_le hB he hb
  have hproduct :
      |narrowCoordinate e x₀ x| * |∑ i, b x i * e i| ≤
        d * ((n : Real) * B) :=
    mul_le_mul hcoordinate hdirection (abs_nonneg _) hd.le
  have hdrift :
      -2 * narrowCoordinate e x₀ x * (∑ i, b x i * e i) ≤
        2 * ((n : Real) * B) * d := by
    calc
      -2 * narrowCoordinate e x₀ x * (∑ i, b x i * e i) ≤
          |-2 * narrowCoordinate e x₀ x * (∑ i, b x i * e i)| :=
        le_abs_self _
      _ = 2 * (|narrowCoordinate e x₀ x| * |∑ i, b x i * e i|) := by
        rw [abs_mul, abs_mul]
        ring
      _ ≤ 2 * (d * ((n : Real) * B)) :=
        mul_le_mul_of_nonneg_left hproduct (by norm_num)
      _ = 2 * ((n : Real) * B) * d := by ring
  have hbarrier := narrowDomainBarrier_bounds hd hcoordinate
  have hc_le : c x ≤ max (c x) 0 := le_max_left _ _
  have hzero :
      c x * narrowDomainBarrier e x₀ d x ≤ 2 * C * d ^ 2 := by
    calc
      c x * narrowDomainBarrier e x₀ d x ≤
          max (c x) 0 * narrowDomainBarrier e x₀ d x :=
        mul_le_mul_of_nonneg_right hc_le hbarrier.1.le
      _ ≤ C * narrowDomainBarrier e x₀ d x :=
        mul_le_mul_of_nonneg_right hc hbarrier.1.le
      _ ≤ C * (2 * d ^ 2) :=
        mul_le_mul_of_nonneg_left hbarrier.2 hC
      _ = 2 * C * d ^ 2 := by ring
  rw [nondivergenceOperator_narrowDomainBarrier]
  calc
    -2 * (e ⬝ᵥ ((a x).mulVec e)) -
          2 * narrowCoordinate e x₀ x * (∑ i, b x i * e i) +
          c x * narrowDomainBarrier e x₀ d x ≤
        -2 * lambda + 2 * ((n : Real) * B) * d + 2 * C * d ^ 2 := by
      linarith [hlead, hdrift, hzero]
    _ ≤ 0 := by nlinarith

/-- Han--Lin Proposition 2.15. Uniform ellipticity, coordinatewise drift
bounds, and a bound on the positive part of the zero-order coefficient give a
single positive width threshold. Every domain narrower than that threshold in
a unit direction admits the positive supersolution required by the general
maximum principle. -/
theorem exists_positive_supersolution_of_narrow_domain
    {n : Nat} {Omega : Set (Euclidean n)}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    {lambda B C : Real}
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hb : ∀ x ∈ Omega, ∀ i, |b x i| ≤ B)
    (hc : ∀ x ∈ Omega, max (c x) 0 ≤ C) :
    ∃ d₀ : Real, 0 < d₀ ∧
      ∀ (e : Euclidean n) (d : Real), ‖e‖ = 1 → 0 < d →
        (∀ x ∈ Omega, ∀ y ∈ Omega, |inner Real (y - x) e| < d) →
        d ≤ d₀ →
        ∃ w : Euclidean n → Real,
          ContDiffOn Real 2 w Omega ∧
          ContDiffOn Real 1 w (closure Omega) ∧
          (∀ x ∈ closure Omega, 0 < w x) ∧
          ∀ x ∈ Omega, nondivergenceOperator a b c w x ≤ 0 := by
  refine ⟨narrowDomainWidthThreshold n lambda B C,
    narrowDomainWidthThreshold_pos hlambda hB hC, ?_⟩
  intro e d he hd hwidth hd₀
  by_cases hOmega : Omega.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hOmega
    have hcoordinate := narrowCoordinate_abs_le_on_closure hx₀ hwidth
    let w := narrowDomainBarrier e x₀ d
    have hwC2 : ContDiff Real 2 w := narrowDomainBarrier_contDiff e x₀ d
    refine ⟨w, hwC2.contDiffOn, ?_, ?_, ?_⟩
    · exact (hwC2.of_le (by norm_num)).contDiffOn
    · intro x hx
      exact (narrowDomainBarrier_bounds hd (hcoordinate x hx)).1
    · intro x hx
      exact narrowDomainBarrier_operator_nonpos hB hC he hd
        (helliptic x hx) (hb x hx) (hc x hx)
        (hcoordinate x (subset_closure hx))
        (narrowDomainWidthThreshold_small hB hC hd hd₀)
  · have hOmega_empty : Omega = ∅ := not_nonempty_iff_eq_empty.mp hOmega
    subst Omega
    refine ⟨fun _ => 1, contDiff_const.contDiffOn,
      contDiff_const.contDiffOn, ?_, ?_⟩ <;> simp

/-- Han--Lin Remark 2.16. The narrow-domain positive-supersolution result does
not require the domain to be bounded. -/
theorem exists_positive_supersolution_of_narrow_unbounded_domain
    {n : Nat} {Omega : Set (Euclidean n)}
    {a : Euclidean n → Matrix (Fin n) (Fin n) Real}
    {b : Euclidean n → Fin n → Real} {c : Euclidean n → Real}
    {lambda B C : Real}
    (hlambda : 0 < lambda) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (helliptic : ∀ x ∈ Omega, UniformlyElliptic (a x) lambda)
    (hb : ∀ x ∈ Omega, ∀ i, |b x i| ≤ B)
    (hc : ∀ x ∈ Omega, max (c x) 0 ≤ C) :
    ∃ d₀ : Real, 0 < d₀ ∧
      ∀ (e : Euclidean n) (d : Real), ‖e‖ = 1 → 0 < d →
        (∀ x ∈ Omega, ∀ y ∈ Omega, |inner Real (y - x) e| < d) →
        d ≤ d₀ →
        ∃ w : Euclidean n → Real,
          ContDiffOn Real 2 w Omega ∧
          ContDiffOn Real 1 w (closure Omega) ∧
          (∀ x ∈ closure Omega, 0 < w x) ∧
          ∀ x ∈ Omega, nondivergenceOperator a b c w x ≤ 0 :=
  exists_positive_supersolution_of_narrow_domain
    hlambda hB hC helliptic hb hc

end HanLinLectureNotes.Ch02

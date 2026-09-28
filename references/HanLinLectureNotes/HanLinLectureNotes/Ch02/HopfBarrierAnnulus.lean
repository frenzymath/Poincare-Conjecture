import HanLinLectureNotes.Ch02.HopfBarrier

/-!
# Chapter 2: the Hopf barrier on a compact annulus

Uniform positivity of a nondivergence-form elliptic operator applied to the
Hopf barrier on a compact set avoiding the barrier center.
-/

open scoped InnerProductSpace

namespace HanLinLectureNotes

noncomputable section

/-- For a continuous elliptic operator, including its zeroth-order coefficient,
on a compact set away from the barrier center, one Hopf exponent makes the
operator applied to the barrier strictly positive everywhere. -/
theorem exists_pos_forall_hopfBarrier_operator_pos_with_zeroOrder
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (e : ι → E) (hspan : ∀ v : E, (∀ a, ⟪v, e a⟫_ℝ = 0) → v = 0)
    {A : E → ι → ι → ℝ} {b : E → ι → ℝ} {c : E → ℝ} {S : Set E}
    (hS : IsCompact S)
    (hA : ∀ a c, ContinuousOn (fun y => A y a c) S)
    (hb : ∀ k, ContinuousOn (fun y => b y k) S)
    (hc : ContinuousOn c S)
    (hpos : ∀ y ∈ S, ∀ xi : ι → ℝ, xi ≠ 0 →
      0 < ∑ a, ∑ c, A y a c * xi a * xi c)
    {x₀ : E} (hx₀ : x₀ ∉ S) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ y ∈ S,
      0 < (∑ a, ∑ c, A y a c *
            fderiv ℝ (fun z => fderiv ℝ (hopfBarrier alpha x₀) z (e c)) y (e a)) +
          ∑ k, b y k * fderiv ℝ (hopfBarrier alpha x₀) y (e k) +
          c y * hopfBarrier alpha x₀ y := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by intro y hy; exact (Set.notMem_empty y hy).elim⟩
  set Q : E → ℝ := fun y =>
    ∑ a, ∑ c, A y a c * ⟪y - x₀, e a⟫_ℝ * ⟪y - x₀, e c⟫_ℝ with hQ
  set T : E → ℝ := fun y => ∑ a, ∑ c, A y a c * ⟪e a, e c⟫_ℝ with hT
  set C : E → ℝ := fun y => ∑ k, b y k * ⟪y - x₀, e k⟫_ℝ with hC
  have hclosed : ∀ (alpha : ℝ) (y : E),
      (∑ a, ∑ c, A y a c *
          fderiv ℝ (fun z => fderiv ℝ (hopfBarrier alpha x₀) z (e c)) y (e a)) +
        ∑ k, b y k * fderiv ℝ (hopfBarrier alpha x₀) y (e k) +
        c y * hopfBarrier alpha x₀ y =
      Real.exp (-alpha * ‖y - x₀‖ ^ 2) *
        (4 * alpha ^ 2 * Q y - 2 * alpha * T y - 2 * alpha * C y + c y) := by
    intro alpha y
    have h1 : (∑ a, ∑ c, A y a c *
          fderiv ℝ (fun z => fderiv ℝ (hopfBarrier alpha x₀) z (e c)) y (e a)) =
        Real.exp (-alpha * ‖y - x₀‖ ^ 2) *
          (4 * alpha ^ 2 * Q y - 2 * alpha * T y) := by
      simp only [fderiv_fderiv_hopfBarrier, hQ, hT, mul_sub, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    have h2 : (∑ k, b y k * fderiv ℝ (hopfBarrier alpha x₀) y (e k)) =
        Real.exp (-alpha * ‖y - x₀‖ ^ 2) * (-(2 * alpha) * C y) := by
      simp only [fderiv_hopfBarrier, hC, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2, hopfBarrier]
    ring
  have hQpos : ∀ y ∈ S, 0 < Q y := by
    intro y hy
    have hxi : (fun a => ⟪y - x₀, e a⟫_ℝ) ≠ 0 := by
      intro h
      have hzero : ∀ a, ⟪y - x₀, e a⟫_ℝ = 0 := fun a => congrFun h a
      have hv : y - x₀ = 0 := hspan (y - x₀) hzero
      rw [sub_eq_zero] at hv
      exact hx₀ (hv ▸ hy)
    have hp := hpos y hy (fun a => ⟪y - x₀, e a⟫_ℝ) hxi
    simpa [hQ] using hp
  have hcont_inner : ∀ a : ι, ContinuousOn (fun y => ⟪y - x₀, e a⟫_ℝ) S :=
    fun a => ContinuousOn.inner (continuousOn_id.sub continuousOn_const) continuousOn_const
  have hQcont : ContinuousOn Q S := by
    rw [hQ]
    refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun c _ => ?_
    exact ((hA a c).mul (hcont_inner a)).mul (hcont_inner c)
  have hTCcont : ContinuousOn (fun y => T y + C y) S := by
    rw [hT, hC]
    refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finsetSum _ fun a _ => continuousOn_finsetSum _ fun c _ => ?_
      exact (hA a c).mul continuousOn_const
    · refine continuousOn_finsetSum _ fun k _ => ?_
      exact (hb k).mul (hcont_inner k)
  obtain ⟨ymin, hyminS, hymin⟩ := hS.exists_isMinOn hne hQcont
  obtain ⟨ymax, hymaxS, hymax⟩ := hS.exists_isMaxOn hne hTCcont
  obtain ⟨yc, hycS, hyc⟩ := hS.exists_isMinOn hne hc
  have hymin' : ∀ y ∈ S, Q ymin ≤ Q y := fun y hy => isMinOn_iff.mp hymin y hy
  have hymax' : ∀ y ∈ S, T y + C y ≤ T ymax + C ymax :=
    fun y hy => isMaxOn_iff.mp hymax y hy
  have hyc' : ∀ y ∈ S, c yc ≤ c y := fun y hy => isMinOn_iff.mp hyc y hy
  have hcQpos : 0 < Q ymin := hQpos ymin hyminS
  set cQ := Q ymin with hcQ
  set beta := T ymax + C ymax with hbeta
  set delta := c yc with hdelta
  refine ⟨(|beta| + |delta|) / (2 * cQ) + 1, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ (|beta| + |delta|) / (2 * cQ) :=
      div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by linarith)
    linarith
  · intro y hy
    rw [hclosed]
    set alpha := (|beta| + |delta|) / (2 * cQ) + 1 with halphaDef
    have halphaPos : 0 < alpha := by
      rw [halphaDef]
      have h0 : (0 : ℝ) ≤ (|beta| + |delta|) / (2 * cQ) :=
        div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by linarith)
      linarith
    have halphaOne : 1 ≤ alpha := by
      rw [halphaDef]
      have h0 : (0 : ℝ) ≤ (|beta| + |delta|) / (2 * cQ) :=
        div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by linarith)
      linarith
    have hQy : cQ ≤ Q y := hymin' y hy
    have hbetaY : T y + C y ≤ beta := hymax' y hy
    have hdeltaY : delta ≤ c y := hyc' y hy
    have hcQne : cQ ≠ 0 := hcQpos.ne'
    have hkey : 2 * alpha * cQ = |beta| + |delta| + 2 * cQ := by
      rw [halphaDef]
      field_simp
    have hP : |delta| < 2 * alpha * Q y - T y - C y := by
      have hu : 0 ≤ alpha * (Q y - cQ) :=
        mul_nonneg halphaPos.le (sub_nonneg.mpr hQy)
      nlinarith [hu, hkey, hbetaY, le_abs_self beta, hcQpos]
    have hPpos : 0 < 2 * alpha * Q y - T y - C y :=
      lt_of_le_of_lt (abs_nonneg delta) hP
    have hscale : 0 < (2 * alpha - 1) * (2 * alpha * Q y - T y - C y) :=
      mul_pos (by linarith [halphaOne]) hPpos
    have hbr :
        0 < 4 * alpha ^ 2 * Q y - 2 * alpha * T y - 2 * alpha * C y + c y := by
      nlinarith [hscale, hP, neg_abs_le delta, hdeltaY]
    exact mul_pos (Real.exp_pos _) hbr

/-- The compact barrier estimate when the operator has no zeroth-order term. -/
theorem exists_pos_forall_hopfBarrier_operator_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (e : ι → E) (hspan : ∀ v : E, (∀ a, ⟪v, e a⟫_ℝ = 0) → v = 0)
    {A : E → ι → ι → ℝ} {b : E → ι → ℝ} {S : Set E} (hS : IsCompact S)
    (hA : ∀ a c, ContinuousOn (fun y => A y a c) S)
    (hb : ∀ k, ContinuousOn (fun y => b y k) S)
    (hpos : ∀ y ∈ S, ∀ xi : ι → ℝ, xi ≠ 0 →
      0 < ∑ a, ∑ c, A y a c * xi a * xi c)
    {x₀ : E} (hx₀ : x₀ ∉ S) :
    ∃ alpha : ℝ, 0 < alpha ∧ ∀ y ∈ S,
      0 < (∑ a, ∑ c, A y a c *
            fderiv ℝ (fun z => fderiv ℝ (hopfBarrier alpha x₀) z (e c)) y (e a)) +
          ∑ k, b y k * fderiv ℝ (hopfBarrier alpha x₀) y (e k) := by
  simpa using
    (exists_pos_forall_hopfBarrier_operator_pos_with_zeroOrder e hspan
      (A := A) (b := b) (c := fun _ => 0) hS hA hb continuousOn_const hpos hx₀)

end

end HanLinLectureNotes

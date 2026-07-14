import MorganTianLib.Ch02.HopfBarrier

/-!
# Morgan–Tian Ch. 2 §2.2 — the barrier ellipticity estimate on the annulus

The analytic heart of the barrier step in the **Hopf strong maximum principle**
(Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2 §2.2, blueprint
`lem:hopf-strong-maximum`). Working in a real inner product space `E`, we apply
a second-order linear operator with continuous coefficients and a pointwise
positive-definite leading part to the Euclidean Hopf barrier
`w_α(x) = exp(−α‖x − x₀‖²)` and show that, on a compact set `S` avoiding the
barrier centre `x₀`, the exponent `α` can be chosen large enough to make the
result strictly positive on all of `S`.

The mechanism is the closed form
`L w_α(y) = exp(−α‖y − x₀‖²) · (4α² Q(y) − 2α T(y) − 2α C(y))`,
where `Q(y) = Σ A(y)ᵃᶜ ⟨y − x₀, eₐ⟩⟨y − x₀, e_c⟩` is a positive-definite
quadratic form (positive on `S` by the ellipticity hypothesis, since `y ≠ x₀`
there), and `T`, `C` collect the lower-order contributions. All three are
continuous on `S`, so `Q` attains a positive minimum and `T + C` a maximum;
choosing `α` beyond the resulting threshold forces the quadratic-in-`α` bracket
to be positive, and `exp > 0` finishes.

This is pure `Mathlib` calculus in an inner product space, built on the barrier
derivative closed forms of `MorganTianLib.Ch02.HopfBarrier`; there are no manifold
imports.

Blueprint: `lem:hopf-strong-maximum`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2 §2.2.
-/

open scoped InnerProductSpace

namespace MorganTianLib

noncomputable section

/-- **Math.** The **barrier ellipticity estimate**. Let `L = Σ A(y)ᵃᶜ ∂²/∂eₐ∂e_c
+ Σ b(y)ᵏ ∂/∂eₖ` be a second-order linear operator with continuous coefficients
`A`, `b` on a compact set `S` and pointwise positive-definite leading part `A`.
For the Euclidean Hopf barrier `w_α(x) = exp(−α‖x − x₀‖²)` centred at a point
`x₀ ∉ S`, there is an exponent `α > 0` for which `L w_α > 0` everywhere on `S`.

This is the barrier step of the Hopf strong maximum principle: making `L w_α`
strictly positive on the shrunken annulus by enlarging `α`.
Blueprint: `lem:hopf-strong-maximum`, Morgan–Tian Ch. 2 §2.2. -/
theorem exists_pos_forall_barrier_elliptic_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    (e : ι → E) (hspan : ∀ v : E, (∀ a, ⟪v, e a⟫_ℝ = 0) → v = 0)
    {A : E → ι → ι → ℝ} {b : E → ι → ℝ} {S : Set E} (hS : IsCompact S)
    (hA : ∀ a c, ContinuousOn (fun y => A y a c) S)
    (hb : ∀ k, ContinuousOn (fun y => b y k) S)
    (hpos : ∀ y ∈ S, ∀ ξ : ι → ℝ, ξ ≠ 0 →
      0 < ∑ a, ∑ c, A y a c * ξ a * ξ c)
    {x₀ : E} (hx₀ : x₀ ∉ S) :
    ∃ α : ℝ, 0 < α ∧ ∀ y ∈ S,
      0 < (∑ a, ∑ c, A y a c *
            fderiv ℝ (fun z => fderiv ℝ (hopfBarrier α x₀) z (e c)) y (e a))
          + ∑ k, b y k * fderiv ℝ (hopfBarrier α x₀) y (e k) := by
  -- Step 0: the empty set — any positive `α` works, the conclusion is vacuous.
  rcases S.eq_empty_or_nonempty with rfl | hne
  · exact ⟨1, one_pos, by intro y hy; exact (Set.notMem_empty y hy).elim⟩
  -- The quadratic form `Q`, the leading trace `T`, and the drift term `C`.
  set Q : E → ℝ := fun y => ∑ a, ∑ c, A y a c * ⟪y - x₀, e a⟫_ℝ * ⟪y - x₀, e c⟫_ℝ
    with hQ
  set T : E → ℝ := fun y => ∑ a, ∑ c, A y a c * ⟪e a, e c⟫_ℝ with hT
  set C : E → ℝ := fun y => ∑ k, b y k * ⟪y - x₀, e k⟫_ℝ with hC
  -- Step 2: the closed form of `L w_α`.
  have hclosed : ∀ (α : ℝ) (y : E),
      (∑ a, ∑ c, A y a c *
          fderiv ℝ (fun z => fderiv ℝ (hopfBarrier α x₀) z (e c)) y (e a))
        + ∑ k, b y k * fderiv ℝ (hopfBarrier α x₀) y (e k)
      = Real.exp (-α * ‖y - x₀‖ ^ 2) *
          (4 * α ^ 2 * Q y - 2 * α * T y - 2 * α * C y) := by
    intro α y
    have h1 : (∑ a, ∑ c, A y a c *
          fderiv ℝ (fun z => fderiv ℝ (hopfBarrier α x₀) z (e c)) y (e a))
        = Real.exp (-α * ‖y - x₀‖ ^ 2) * (4 * α ^ 2 * Q y - 2 * α * T y) := by
      simp only [fderiv_fderiv_hopfBarrier, hQ, hT, mul_sub, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    have h2 : (∑ k, b y k * fderiv ℝ (hopfBarrier α x₀) y (e k))
        = Real.exp (-α * ‖y - x₀‖ ^ 2) * (-(2 * α) * C y) := by
      simp only [fderiv_hopfBarrier, hC, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [h1, h2]; ring
  -- Step 3: `Q` is positive on `S` (via ellipticity, using `y ≠ x₀`).
  have hQpos : ∀ y ∈ S, 0 < Q y := by
    intro y hy
    have hξ : (fun a => ⟪y - x₀, e a⟫_ℝ) ≠ 0 := by
      intro h
      have hzero : ∀ a, ⟪y - x₀, e a⟫_ℝ = 0 := fun a => congrFun h a
      have hv : y - x₀ = 0 := hspan (y - x₀) hzero
      rw [sub_eq_zero] at hv
      exact hx₀ (hv ▸ hy)
    have hp := hpos y hy (fun a => ⟪y - x₀, e a⟫_ℝ) hξ
    simpa [hQ] using hp
  -- Step 4: continuity on `S` of `Q`, `T`, `C`.
  have hcont_inner : ∀ a : ι, ContinuousOn (fun y => ⟪y - x₀, e a⟫_ℝ) S := fun a =>
    ContinuousOn.inner (continuousOn_id.sub continuousOn_const) continuousOn_const
  have hQcont : ContinuousOn Q S := by
    rw [hQ]
    refine continuousOn_finset_sum _ fun a _ => continuousOn_finset_sum _ fun c _ => ?_
    exact ((hA a c).mul (hcont_inner a)).mul (hcont_inner c)
  have hTCcont : ContinuousOn (fun y => T y + C y) S := by
    rw [hT, hC]
    refine ContinuousOn.add ?_ ?_
    · refine continuousOn_finset_sum _ fun a _ => continuousOn_finset_sum _ fun c _ => ?_
      exact (hA a c).mul continuousOn_const
    · refine continuousOn_finset_sum _ fun k _ => ?_
      exact (hb k).mul (hcont_inner k)
  -- Step 5: extremes on the compact set.
  obtain ⟨ymin, hyminS, hymin⟩ := hS.exists_isMinOn hne hQcont
  obtain ⟨ymax, hymaxS, hymax⟩ := hS.exists_isMaxOn hne hTCcont
  have hymin' : ∀ y ∈ S, Q ymin ≤ Q y := fun y hy => isMinOn_iff.mp hymin y hy
  have hymax' : ∀ y ∈ S, T y + C y ≤ T ymax + C ymax :=
    fun y hy => isMaxOn_iff.mp hymax y hy
  have hcQpos : 0 < Q ymin := hQpos ymin hyminS
  set cQ := Q ymin with hcQ
  set β := T ymax + C ymax with hβ
  -- Step 6: choose `α` large enough.
  refine ⟨|β| / (2 * cQ) + 1, ?_, ?_⟩
  · have h0 : (0 : ℝ) ≤ |β| / (2 * cQ) := div_nonneg (abs_nonneg _) (by linarith)
    linarith
  · intro y hy
    rw [hclosed]
    set α := |β| / (2 * cQ) + 1 with hαdef
    have hαpos : 0 < α := by
      rw [hαdef]
      have h0 : (0 : ℝ) ≤ |β| / (2 * cQ) := div_nonneg (abs_nonneg _) (by linarith)
      linarith
    have hQy : cQ ≤ Q y := hymin' y hy
    have hβy : T y + C y ≤ β := hymax' y hy
    have hcQne : cQ ≠ 0 := hcQpos.ne'
    have hkey : 2 * α * cQ = |β| + 2 * cQ := by
      rw [hαdef]; field_simp
    have hP : 0 < 2 * α * Q y - T y - C y := by
      have hu : 0 ≤ α * (Q y - cQ) := mul_nonneg hαpos.le (sub_nonneg.mpr hQy)
      nlinarith [hu, hkey, hβy, le_abs_self β, hcQpos]
    have hbr : 0 < 4 * α ^ 2 * Q y - 2 * α * T y - 2 * α * C y := by
      nlinarith [mul_pos hαpos hP]
    exact mul_pos (Real.exp_pos _) hbr

end

end MorganTianLib

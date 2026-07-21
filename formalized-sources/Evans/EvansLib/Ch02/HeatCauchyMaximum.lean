import EvansLib.Ch02.HeatCauchyMaxPrinciple

/-!
# Evans, Ch. 2 §2.3.3 — the maximum principle for the Cauchy problem (small-time case)

Evans, *Partial Differential Equations* (2nd ed.), §2.3.3 Theorem 6 proves that a solution
`u` of the heat equation on `ℝⁿ × (0,T]` with continuous initial data `g` and the growth
bound `u(x,t) ≤ A e^{a‖x‖²}` satisfies `sup u = sup g`.

Evans splits the argument into the **small-time case** `4aT < 1` (the analytic heart) and a
**time-splitting** reduction of the general case to it. This file formalizes the small-time
case, `EvansLib.heat_cauchy_maxPrinciple_smallTime`, exactly as Evans proves it:

* choose `ε > 0` with `4a(T+ε) < 1`, set `τ = T+ε`, and compare `u` with the backward
  Gaussian `K = compKernelSpaceTime n y τ` via `v = u - μK` (`μ > 0`);
* `v` solves the heat equation (`sub_const_mul_compKernel_solvesHeat`), so the **weak
  maximum principle** `exists_parabolicBoundary_isMaxOn` applies on each ball cylinder
  `B(y,r) × (0,T]`, giving `v ≤ v z` for some parabolic-boundary point `z`;
* on the bottom of the boundary `v(x,0) ≤ u(x,0) = g(x) ≤ M`; on the lateral sphere
  `‖x-y‖ = r` the growth bound and the kernel lower bound give
  `v(x,t) ≤ A e^{a(‖y‖+r)²} − μ τ^{-n/2} e^{r²/(4τ)}`, which `→ −∞` as `r → ∞` (because
  `1/(4τ) > a`), hence `≤ M` for `r` large;
* therefore `v(y,t) ≤ M`, i.e. `u(y,t) ≤ M + μ τ^{-n/2}`; letting `μ → 0` gives
  `u(y,t) ≤ M`.

Here `M` is any upper bound for the initial data (`g x ≤ M`); taking `M = sup g` recovers
Evans's statement. Only the **weak** maximum principle is needed (Evans invokes the strong
one, but the conclusion "the max over the closed cylinder is attained on `Γ_T`" is exactly
the weak form).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.3, Theorem 6.
-/

open scoped ContDiff Topology
open Filter Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Elementary facts about the comparison kernel and space–time points -/

/-- Every space–time point is reconstructed from its time coordinate and spatial part. -/
lemma toSpaceTime_spacePart (p : SpaceTime n) :
    toSpaceTime (p 0) (spacePart p) = p := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [toSpaceTime, spacePart]

/-- The comparison kernel is strictly positive below the singular time. -/
lemma compKernelSpaceTime_pos {y : EuclideanSpace ℝ (Fin n)} {τ : ℝ} {p : SpaceTime n}
    (hp : p 0 < τ) : 0 < compKernelSpaceTime n y τ p := by
  have hs : 0 < τ - p 0 := sub_pos.2 hp
  rw [compKernelSpaceTime, compKernelSpatial]
  positivity

/-- Value of the comparison kernel at the centre `(y,t)`: the spatial argument vanishes,
so it reduces to the reversed-time power `(τ-t)^{-n/2}`. -/
lemma compKernelSpaceTime_center {y : EuclideanSpace ℝ (Fin n)} {τ t : ℝ} :
    compKernelSpaceTime n y τ (toSpaceTime t y) = (τ - t) ^ (-(n : ℝ) / 2) := by
  rw [compKernelSpaceTime, toSpaceTime_timeCoord, spacePart_toSpaceTime, sub_self,
    compKernelSpatial]
  simp

/-- Lower bound for the comparison kernel on the lateral sphere. If the spatial part is at
distance `≥ r` from `y` and the time lies in `[0,T]` (with `T < τ` the singular time), then
the kernel is at least `τ^{-n/2} e^{r²/(4τ)}`, a bound uniform in the point. -/
lemma compKernelSpaceTime_lateral_lower {y : EuclideanSpace ℝ (Fin n)} {τ T r : ℝ}
    (hTτ : T < τ) (hr : 0 ≤ r) {z : SpaceTime n}
    (hz0 : z 0 ∈ Icc 0 T) (hdist : r ≤ ‖spacePart z - y‖) :
    τ ^ (-(n : ℝ) / 2) * Real.exp (r ^ 2 / (4 * τ))
      ≤ compKernelSpaceTime n y τ z := by
  have hzT : z 0 ≤ T := hz0.2
  have hz0' : 0 ≤ z 0 := hz0.1
  have hτpos : 0 < τ := lt_of_le_of_lt (le_trans hz0' hzT) hTτ
  set s := τ - z 0 with hs_def
  have hsτ : s ≤ τ := by rw [hs_def]; linarith
  have hspos : 0 < s := by rw [hs_def]; linarith
  have hexpo : (-(n : ℝ) / 2) ≤ 0 := by
    have : (0 : ℝ) ≤ (n : ℝ) / 2 := by positivity
    linarith
  rw [compKernelSpaceTime, compKernelSpatial]
  apply mul_le_mul
  · exact Real.rpow_le_rpow_of_nonpos hspos hsτ hexpo
  · apply Real.exp_le_exp.mpr
    have hr2 : r ^ 2 ≤ ‖spacePart z - y‖ ^ 2 :=
      sq_le_sq' (by linarith [norm_nonneg (spacePart z - y)]) hdist
    exact div_le_div₀ (by positivity) hr2 (by positivity) (by linarith)
  · positivity
  · positivity

/-! ## The lateral growth term is eventually dominated by the kernel term -/

/-- **The `r → ∞` limit of Evans's boundary estimate (29).** With `a < b` (here `a` the
growth rate and `b = 1/(4τ) > a` the kernel rate, from `4aτ < 1`), the lateral bound
`A e^{a(r+off)²} − C e^{b r²}` tends to `−∞` as `r → ∞`, because the kernel exponential
`e^{b r²}` outgrows the growth exponential. Factoring
`= e^{b r²}(A e^{a(r+off)² − b r²} − C)` with the bracket exponent `→ −∞` (leading
coefficient `a − b < 0`), the prefactor `→ +∞` times a negative limit gives `−∞`. -/
lemma tendsto_exp_quadratic_diff_atBot {A C a b off : ℝ} (hC : 0 < C) (hb : 0 < b)
    (hab : a < b) :
    Tendsto (fun r : ℝ => A * Real.exp (a * (r + off) ^ 2) - C * Real.exp (b * r ^ 2))
      atTop atBot := by
  set d := b - a with hd_def
  have hd : 0 < d := by rw [hd_def]; linarith
  set K := a * off / d with hK_def
  set L := a ^ 2 * off ^ 2 / d + a * off ^ 2 with hL_def
  -- bracket exponent → atBot via completing the square: a(r+off)² − b r² = −d(r−K)² + L
  have hQ : Tendsto (fun r : ℝ => a * (r + off) ^ 2 - b * r ^ 2) atTop atBot := by
    have hEq : (fun r : ℝ => a * (r + off) ^ 2 - b * r ^ 2)
        = fun r => -d * (r - K) ^ 2 + L := by
      funext r
      rw [hd_def, hK_def, hL_def]
      have hd' : d ≠ 0 := hd.ne'
      field_simp
      ring
    rw [hEq]
    have hrK : Tendsto (fun r : ℝ => r - K) atTop atTop := by
      simpa using tendsto_atTop_add_const_right atTop (-K) tendsto_id
    have h1 : Tendsto (fun r : ℝ => (r - K) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).comp hrK
    have h2 : Tendsto (fun r : ℝ => -d * (r - K) ^ 2) atTop atBot := by
      have hdX : Tendsto (fun r : ℝ => d * (r - K) ^ 2) atTop atTop := h1.const_mul_atTop hd
      have heq2 : (fun r : ℝ => -d * (r - K) ^ 2) = fun r => -(d * (r - K) ^ 2) := by
        funext r; ring
      rw [heq2]
      exact tendsto_neg_atBot_iff.mpr hdX
    exact tendsto_atBot_add_const_right atTop L h2
  -- exp(bracket exponent) → 0
  have hexpQ : Tendsto (fun r : ℝ => Real.exp (a * (r + off) ^ 2 - b * r ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hQ
  -- prefactor e^{b r²} → atTop
  have hpre : Tendsto (fun r : ℝ => Real.exp (b * r ^ 2)) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_pow_atTop (two_ne_zero)).const_mul_atTop hb)
  -- rewrite f as e^{b r²}·(A e^{Q} − C)
  have hfEq : (fun r : ℝ => A * Real.exp (a * (r + off) ^ 2) - C * Real.exp (b * r ^ 2))
      = fun r => Real.exp (b * r ^ 2) * (A * Real.exp (a * (r + off) ^ 2 - b * r ^ 2) - C) := by
    funext r
    rw [Real.exp_sub]
    have hpos : Real.exp (b * r ^ 2) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
  rw [hfEq]
  have hbr : Tendsto (fun r : ℝ => A * Real.exp (a * (r + off) ^ 2 - b * r ^ 2) - C)
      atTop (𝓝 (-C)) := by
    have := (hexpQ.const_mul A).sub_const C
    simpa using this
  exact hpre.atTop_mul_neg (by linarith) hbr

/-! ## The maximum principle for the Cauchy problem — small-time case -/

/-- **Maximum principle for the heat Cauchy problem, small-time case** (Evans §2.3.3
Theorem 6, the case `4aT < 1`). If `u` is continuous, solves the heat equation on
`ℝⁿ × (0,T)`, is `C²` there, its initial values `u(·,0)` are bounded above by `M`, and it
obeys the growth estimate `u(x,t) ≤ A e^{a‖x‖²}` on `ℝⁿ × [0,T]`, then `u ≤ M` throughout
`ℝⁿ × [0,T]`. Taking `M = sup u(·,0)` recovers Evans's `sup u = sup g`.

This is Evans's step 1: choose `ε > 0` with `4a(T+ε) < 1`, compare `u` with `μ` times the
backward Gaussian `compKernelSpaceTime n y τ` (`τ = T+ε`), apply the weak maximum principle
`exists_parabolicBoundary_isMaxOn` on a large ball cylinder, bound the comparison function
on the parabolic boundary (bottom by `M`, lateral sphere by
`tendsto_exp_quadratic_diff_atBot`), and let `μ → 0`. The general case follows by
time-splitting (Evans's step 3), not formalized here. -/
theorem heat_cauchy_maxPrinciple_smallTime {u : SpaceTime n → ℝ}
    {T A a : ℝ} (hT : 0 < T) (ha : 0 < a) (hA : 0 < A)
    (hsmall : 4 * a * T < 1)
    (hcont : Continuous u)
    (hC2 : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hheat : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 u p = ∑ j : Fin n, (partialDeriv j.succ)^[2] u p)
    (hgrowth : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      u p ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2))
    {M : ℝ} (hM : ∀ x, u (toSpaceTime 0 x) ≤ M) :
    ∀ p : SpaceTime n, p 0 ∈ Icc 0 T → u p ≤ M := by
  -- 1. choose ε > 0 with 4a(T+ε) < 1
  obtain ⟨ε, hε, hεsmall⟩ : ∃ ε, 0 < ε ∧ 4 * a * (T + ε) < 1 := by
    refine ⟨(1 - 4 * a * T) / (8 * a), by positivity, ?_⟩
    have he : 4 * a * ((1 - 4 * a * T) / (8 * a)) = (1 - 4 * a * T) / 2 := by
      field_simp; ring
    rw [mul_add, he]; linarith
  set τ := T + ε with hτ_def
  have hτT : T < τ := by rw [hτ_def]; linarith
  have hτpos : 0 < τ := by linarith
  have h4aτ : 4 * a * τ < 1 := by rw [hτ_def]; exact hεsmall
  have hbpos : (0 : ℝ) < 1 / (4 * τ) := by positivity
  have hab : a < 1 / (4 * τ) := by
    rw [lt_div_iff₀ (by positivity)]
    have : a * (4 * τ) = 4 * a * τ := by ring
    rw [this]; exact h4aτ
  -- 2. main point
  intro p hp
  set y := spacePart p with hy_def
  set t := p 0 with ht_def
  rw [show p = toSpaceTime t y from (toSpaceTime_spacePart p).symm]
  rcases eq_or_lt_of_le hp.1 with ht0 | ht0pos
  · -- t = 0 (bottom of the slab)
    rw [← ht0]; exact hM y
  · -- 0 < t ≤ T
    have htT : t ≤ T := hp.2
    have hCtpos : (0 : ℝ) < (τ - t) ^ (-(n : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
    -- core bound: ∀ μ>0, u(t,y) ≤ M + μ (τ-t)^{-n/2}
    have hcore : ∀ μ : ℝ, 0 < μ →
        u (toSpaceTime t y) ≤ M + μ * (τ - t) ^ (-(n : ℝ) / 2) := by
      intro μ hμ
      -- choose r large so the lateral bound drops below M
      obtain ⟨r, hr1, hrM⟩ : ∃ r, 1 ≤ r ∧
          A * Real.exp (a * (r + ‖y‖) ^ 2)
            - (μ * τ ^ (-(n : ℝ) / 2)) * Real.exp ((1 / (4 * τ)) * r ^ 2) ≤ M := by
        have htends := tendsto_exp_quadratic_diff_atBot
          (A := A) (C := μ * τ ^ (-(n : ℝ) / 2)) (a := a) (b := 1 / (4 * τ)) (off := ‖y‖)
          (by positivity) hbpos hab
        obtain ⟨r, hrM, hr1⟩ :=
          ((htends.eventually (eventually_le_atBot M)).and (eventually_ge_atTop (1 : ℝ))).exists
        exact ⟨r, hr1, hrM⟩
      have hrpos : 0 < r := lt_of_lt_of_le one_pos hr1
      have hr0 : 0 ≤ r := hrpos.le
      have hUopen : IsOpen (Metric.ball y r) := Metric.isOpen_ball
      have hUbdd : Bornology.IsBounded (Metric.ball y r) := Metric.isBounded_ball
      have hUne : (Metric.ball y r).Nonempty := ⟨y, Metric.mem_ball_self hrpos⟩
      -- weak maximum principle hypotheses for v = u - μ K
      have hvcont : ContinuousOn (fun q => u q - μ * compKernelSpaceTime n y τ q)
          (closure (parabolicCylinder (Metric.ball y r) T)) := by
        intro q hq
        have hq0 : q 0 ≤ T := (closure_parabolicCylinder_subset _ _ hq).2.2
        have hqτ : q 0 < τ := lt_of_le_of_lt hq0 hτT
        exact ((hcont.continuousAt).sub (continuousAt_const.mul
          (compKernelSpaceTime_contDiffAt hqτ (k := 0)).continuousAt)).continuousWithinAt
      have hvC2 : ∀ q : SpaceTime n, spacePart q ∈ Metric.ball y r → q 0 ∈ Ioo 0 T →
          ContDiffAt ℝ 2 (fun q => u q - μ * compKernelSpaceTime n y τ q) q := by
        intro q _ hqt
        have hqτ : q 0 < τ := lt_trans hqt.2 hτT
        exact (hC2 q hqt).sub (contDiffAt_const.mul (compKernelSpaceTime_contDiffAt hqτ))
      have hvheat : ∀ q : SpaceTime n, spacePart q ∈ Metric.ball y r → q 0 ∈ Ioo 0 T →
          partialDeriv 0 (fun q => u q - μ * compKernelSpaceTime n y τ q) q
            = ∑ j : Fin n, (partialDeriv j.succ)^[2]
                (fun q => u q - μ * compKernelSpaceTime n y τ q) q := by
        intro q _ hqt
        have hqτ : q 0 < τ := lt_trans hqt.2 hτT
        exact sub_const_mul_compKernel_solvesHeat hqτ (hC2 q hqt) (hheat q hqt)
      obtain ⟨z, hzΓ, hzmax⟩ := exists_parabolicBoundary_isMaxOn hUopen hUbdd hUne hT
        hvcont hvC2 hvheat
      -- bound the comparison function at the boundary point z by M
      have hzsub := closure_parabolicCylinder_subset (Metric.ball y r) T hzΓ.1
      have hz0Icc : z 0 ∈ Icc 0 T := hzsub.2
      have hKzpos : 0 < compKernelSpaceTime n y τ z :=
        compKernelSpaceTime_pos (lt_of_le_of_lt hz0Icc.2 hτT)
      have hvzM : u z - μ * compKernelSpaceTime n y τ z ≤ M := by
        rcases eq_or_lt_of_le hz0Icc.1 with hz0 | hz0pos
        · -- bottom of the parabolic boundary: z 0 = 0
          have hrec : z = toSpaceTime 0 (spacePart z) := by
            conv_lhs => rw [← toSpaceTime_spacePart z]
            rw [← hz0]
          have huz : u z ≤ M := by rw [hrec]; exact hM (spacePart z)
          nlinarith [mul_pos hμ hKzpos]
        · -- lateral sphere: ‖spacePart z - y‖ = r
          have hz0Ioc : z 0 ∈ Ioc 0 T := ⟨hz0pos, hz0Icc.2⟩
          have hspNotBall : spacePart z ∉ Metric.ball y r := fun hmem =>
            hzΓ.2 ⟨hmem, hz0Ioc⟩
          have hclosedBall : spacePart z ∈ Metric.closedBall y r := by
            have := hzsub.1
            rwa [closure_ball y hrpos.ne'] at this
          have hdle : dist (spacePart z) y ≤ r := Metric.mem_closedBall.1 hclosedBall
          have hdge : r ≤ dist (spacePart z) y :=
            not_lt.mp (fun h => hspNotBall (Metric.mem_ball.2 h))
          have heqdist : ‖spacePart z - y‖ = r := by
            rw [← dist_eq_norm]; exact le_antisymm hdle hdge
          have hdist : r ≤ ‖spacePart z - y‖ := le_of_eq heqdist.symm
          have hnormle : ‖spacePart z‖ ≤ r + ‖y‖ := by
            have h3 : ‖spacePart z‖ ≤ ‖spacePart z - y‖ + ‖y‖ := by
              simpa using norm_add_le (spacePart z - y) y
            rw [heqdist] at h3; exact h3
          have hgrowthz : u z ≤ A * Real.exp (a * (r + ‖y‖) ^ 2) := by
            refine (hgrowth z hz0Icc).trans ?_
            apply mul_le_mul_of_nonneg_left _ hA.le
            apply Real.exp_le_exp.mpr
            apply mul_le_mul_of_nonneg_left _ ha.le
            exact sq_le_sq' (by linarith [norm_nonneg (spacePart z)]) hnormle
          have hKlb : τ ^ (-(n : ℝ) / 2) * Real.exp (r ^ 2 / (4 * τ))
              ≤ compKernelSpaceTime n y τ z :=
            compKernelSpaceTime_lateral_lower hτT hr0 hz0Icc hdist
          have hmulK : μ * (τ ^ (-(n : ℝ) / 2) * Real.exp (r ^ 2 / (4 * τ)))
              ≤ μ * compKernelSpaceTime n y τ z := mul_le_mul_of_nonneg_left hKlb hμ.le
          have hexparg : (μ * τ ^ (-(n : ℝ) / 2)) * Real.exp ((1 / (4 * τ)) * r ^ 2)
              = μ * (τ ^ (-(n : ℝ) / 2) * Real.exp (r ^ 2 / (4 * τ))) := by
            rw [show (1 / (4 * τ)) * r ^ 2 = r ^ 2 / (4 * τ) from by ring]; ring
          rw [hexparg] at hrM
          linarith [hgrowthz, hmulK, hrM]
      -- the centre point (t,y) lies in the closed cylinder
      have hcenter_mem : toSpaceTime t y ∈ closure (parabolicCylinder (Metric.ball y r) T) := by
        apply subset_closure
        exact ⟨by rw [spacePart_toSpaceTime]; exact Metric.mem_ball_self hrpos,
          by rw [toSpaceTime_timeCoord]; exact ⟨ht0pos, htT⟩⟩
      have hle := hzmax (toSpaceTime t y) hcenter_mem
      have hKc : compKernelSpaceTime n y τ (toSpaceTime t y) = (τ - t) ^ (-(n : ℝ) / 2) :=
        compKernelSpaceTime_center
      simp only at hle
      rw [hKc] at hle
      linarith [hle, hvzM]
    -- 3. let μ → 0
    apply le_of_forall_pos_le_add
    intro δ hδ
    have heq : δ / (τ - t) ^ (-(n : ℝ) / 2) * (τ - t) ^ (-(n : ℝ) / 2) = δ :=
      div_mul_cancel₀ δ hCtpos.ne'
    have := hcore (δ / (τ - t) ^ (-(n : ℝ) / 2)) (by positivity)
    rwa [heq] at this

/-! ## Uniqueness for the Cauchy problem — small-time case -/

/-- If `w` solves the heat equation at `p` (and is `C²` there), so does `-w`. -/
lemma neg_solvesHeat {w : SpaceTime n → ℝ} {p : SpaceTime n}
    (hC2 : ContDiffAt ℝ 2 w p)
    (hheat : partialDeriv 0 w p = ∑ j : Fin n, (partialDeriv j.succ)^[2] w p) :
    partialDeriv 0 (fun q => -w q) p
      = ∑ j : Fin n, (partialDeriv j.succ)^[2] (fun q => -w q) p := by
  have hdiff : DifferentiableAt ℝ w p := hC2.differentiableAt (by norm_num)
  have hev : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ w q :=
    (hC2.eventually (by simp)).mono fun q hq => hq.differentiableAt (by norm_num)
  have heq : (fun q => -w q) = fun q => (-1 : ℝ) * w q := by funext q; ring
  rw [heq, partialDeriv_const_mul (-1) hdiff 0, hheat, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  exact (partialDeriv_iterate_two_const_mul (-1) j.succ hev
    (differentiableAt_partialDeriv_of_contDiffAt hC2 j.succ)).symm

/-- **Uniqueness for the heat Cauchy problem, small-time case** (Evans §2.3.3 Theorem 7,
case `4aT<1`). Two solutions `u`, `v` of the same Cauchy problem — their difference solves
the homogeneous heat equation on `ℝⁿ × (0,T)` (as it does whenever both solve
`w_t - Δw = f` for a common source `f`) — with the same initial data and a Gaussian growth
bound `|u|,|v| ≤ A e^{a‖x‖²}` agree on `ℝⁿ × [0,T]`. Applies
`heat_cauchy_maxPrinciple_smallTime` to `±(u-v)` (growth constant `2A`, initial bound `0`).
-/
theorem heat_cauchy_uniqueness_smallTime {u v : SpaceTime n → ℝ} {T A a : ℝ}
    (hT : 0 < T) (ha : 0 < a) (hA : 0 < A) (hsmall : 4 * a * T < 1)
    (hcontu : Continuous u) (hcontv : Continuous v)
    (hC2u : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hC2v : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 v p)
    (hheat : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 (fun q => u q - v q) p
        = ∑ j : Fin n, (partialDeriv j.succ)^[2] (fun q => u q - v q) p)
    (hinit : ∀ x, u (toSpaceTime 0 x) = v (toSpaceTime 0 x))
    (hgrowthu : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      |u p| ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2))
    (hgrowthv : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      |v p| ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2)) :
    ∀ p : SpaceTime n, p 0 ∈ Icc 0 T → u p = v p := by
  have h2A : (0 : ℝ) < 2 * A := by positivity
  -- w = u - v: solves homogeneous heat, w(·,0)=0, w ≤ 2A e^{a‖x‖²}
  have hgroww : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      (fun q => u q - v q) p ≤ (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by
    intro p hpp
    calc u p - v p ≤ |u p| + |v p| := by
          have h1 := le_abs_self (u p); have h2 := neg_le_abs (v p); linarith
      _ ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2) + A * Real.exp (a * ‖spacePart p‖ ^ 2) := by
          linarith [hgrowthu p hpp, hgrowthv p hpp]
      _ = (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by ring
  have hinitw : ∀ x, (fun q => u q - v q) (toSpaceTime 0 x) ≤ 0 := by
    intro x; simp only; rw [hinit x]; simp
  have hupper := heat_cauchy_maxPrinciple_smallTime hT ha h2A hsmall
    (hcontu.sub hcontv) (fun p hpp => (hC2u p hpp).sub (hC2v p hpp)) hheat hgroww hinitw
  -- -w = v - u: same, via neg_solvesHeat
  have hheat' : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 (fun q => v q - u q) p
        = ∑ j : Fin n, (partialDeriv j.succ)^[2] (fun q => v q - u q) p := by
    intro p hpp
    have hvu : (fun q => v q - u q) = fun q => -(u q - v q) := by funext q; ring
    rw [hvu]
    exact neg_solvesHeat ((hC2u p hpp).sub (hC2v p hpp)) (hheat p hpp)
  have hgroww' : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      (fun q => v q - u q) p ≤ (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by
    intro p hpp
    calc v p - u p ≤ |v p| + |u p| := by
          have h1 := le_abs_self (v p); have h2 := neg_le_abs (u p); linarith
      _ ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2) + A * Real.exp (a * ‖spacePart p‖ ^ 2) := by
          linarith [hgrowthu p hpp, hgrowthv p hpp]
      _ = (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by ring
  have hinitw' : ∀ x, (fun q => v q - u q) (toSpaceTime 0 x) ≤ 0 := by
    intro x; simp only; rw [hinit x]; simp
  have hlower := heat_cauchy_maxPrinciple_smallTime hT ha h2A hsmall
    (hcontv.sub hcontu) (fun p hpp => (hC2v p hpp).sub (hC2u p hpp)) hheat' hgroww' hinitw'
  intro p hp
  have h1 := hupper p hp
  have h2 := hlower p hp
  simp only at h1 h2
  exact le_antisymm (by linarith) (by linarith)

end EvansLib

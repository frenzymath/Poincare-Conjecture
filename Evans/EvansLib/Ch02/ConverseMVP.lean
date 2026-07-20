import EvansLib.Ch02.BallMoments
import EvansLib.Ch02.Regularity

/-!
# Evans, Ch. 2 §2.2.2 Theorem 3 — converse to the mean-value property

Evans, *Partial Differential Equations* (2nd ed.), §2.2.2 Theorem 3: a `C²` function
satisfying the mean-value property on an open set `U ⊆ ℝⁿ` is harmonic. With the
solid-ball form of the property (`HasBallMeanValueProperty`) the `C²` hypothesis is
free — the mean-value property already forces `C^∞`
(`HasBallMeanValueProperty.contDiffOn`) — so the statement here asks only continuity.

The proof is an **averaged second-order Taylor expansion**, avoiding Evans's
`φ(r)`-derivative computation (which needs the Gauss–Green theorem on balls):
for `x ∈ U` set, for small `r > 0`,
`Φ(r) := r⁻² ∫_{B(0,1)} [u(x+rw) − u(x) − r Du(x)w − (r²/2) D²u(x)(w,w)] dw`.

* **Exact value.** The mean-value property makes `∫ u(x+rw) dw = |B(0,1)| u(x)`
  (`setIntegral_unitBall_smul`), odd moments kill the linear term
  (`setIntegral_ball_clm`), so `Φ(r) = −(1/2)∫_{B(0,1)} D²u(x)(w,w) dw` — constant.
* **Limit `0`.** Taylor's theorem (`Convex.taylor_approx_two_segment`) gives the
  pointwise limit `0` per direction `w`; a quadratic bound from the local Lipschitz
  continuity of `Du` (`norm_add_sub_sub_fderiv_le_of_lipschitzOnWith`) dominates, and
  dominated convergence gives `Φ(r) → 0` as `r ↓ 0`.
* Hence `∫_{B(0,1)} D²u(x)(w,w) dw = 0`; the trace formula
  (`setIntegral_ball_bilin`) and `κ₁ > 0` (`setIntegral_ball_sq_coord_pos`) force
  `∑ⱼ D²u(x)(eⱼ,eⱼ) = 0`, which is `Δu(x) = 0` by the Laplacian bridge
  (`laplacian_eq_sum_partialDeriv_iterate_two`).

Main results:
* `EvansLib.HasBallMeanValueProperty.laplacian_eq_zero` — `Δu = 0` pointwise on `U`.
* `EvansLib.HasBallMeanValueProperty.harmonicOnNhd` — `u` is harmonic on `U`
  (mathlib's `InnerProductSpace.HarmonicOnNhd`).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.2.
-/

open MeasureTheory Metric Set Filter Asymptotics
open InnerProductSpace Laplacian
open scoped ContDiff NNReal Topology

noncomputable section

namespace EvansLib

/-! ## Two general second-order Taylor facts

Both hold in any real normed space; they are stated so for reuse. -/

/-- **Quadratic Taylor bound from a Lipschitz derivative.** If `u` is differentiable on
`closedBall x ρ` and its derivative is `K`-Lipschitz there, then the first-order Taylor
remainder is quadratically small: `‖u(x+z) − u(x) − Du(x)z‖ ≤ K ‖z‖²` for `‖z‖ ≤ ρ`.
(Mean value inequality on `closedBall x ‖z‖`, with the linear part subtracted.) -/
lemma norm_add_sub_sub_fderiv_le_of_lipschitzOnWith
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {x : E} {ρ : ℝ} {K : ℝ≥0}
    (hdiff : ∀ y ∈ closedBall x ρ, DifferentiableAt ℝ u y)
    (hlip : LipschitzOnWith K (fderiv ℝ u) (closedBall x ρ))
    {z : E} (hz : ‖z‖ ≤ ρ) :
    ‖u (x + z) - u x - fderiv ℝ u x z‖ ≤ K * ‖z‖ ^ 2 := by
  have hsub : closedBall x ‖z‖ ⊆ closedBall x ρ := closedBall_subset_closedBall hz
  have hxmem : x ∈ closedBall x ρ := mem_closedBall_self ((norm_nonneg z).trans hz)
  have hbound : ∀ y ∈ closedBall x ‖z‖, ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ K * ‖z‖ := by
    intro y hy
    rw [← dist_eq_norm]
    calc dist (fderiv ℝ u y) (fderiv ℝ u x) ≤ K * dist y x :=
          hlip.dist_le_mul y (hsub hy) x hxmem
      _ ≤ K * ‖z‖ := by
          have := mem_closedBall.1 hy
          gcongr
  have hxz : x + z ∈ closedBall x ‖z‖ := by
    rw [mem_closedBall, dist_self_add_left]
  have h := (convex_closedBall x ‖z‖).norm_image_sub_le_of_norm_fderiv_le'
    (fun y hy => hdiff y (hsub hy)) hbound (mem_closedBall_self (norm_nonneg z)) hxz
  rw [add_sub_cancel_left] at h
  calc ‖u (x + z) - u x - fderiv ℝ u x z‖ ≤ K * ‖z‖ * ‖z‖ := h
    _ = K * ‖z‖ ^ 2 := by ring

/-- **Second-order Taylor expansion along a direction.** If `u` is differentiable on
`ball x ρ` and its derivative is differentiable at `x`, then for every direction `w`
the second-order Taylor remainder is `o(r²)` as `r ↓ 0`:
`[u(x+rw) − u(x) − r Du(x)w − (r²/2) D²u(x)(w,w)] / r² → 0`.
This packages `Convex.taylor_approx_two_segment` (with `v = 0` and the direction
rescaled to fit inside the ball) into the quotient form used by dominated
convergence. -/
lemma tendsto_taylor_two_quotient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : E → ℝ} {x : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ y ∈ ball x ρ, HasFDerivAt u (fderiv ℝ u y) y)
    (hB : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) x) x) (w : E) :
    Tendsto (fun r : ℝ => (u (x + r • w) - u x - r * fderiv ℝ u x w
        - r ^ 2 / 2 * fderiv ℝ (fderiv ℝ u) x w w) / r ^ 2) (𝓝[>] 0) (𝓝 0) := by
  set L := fderiv ℝ u x with hLdef
  set B := fderiv ℝ (fderiv ℝ u) x with hBdef
  set c : ℝ := ρ / (2 * (‖w‖ + 1)) with hcdef
  have hcpos : 0 < c := by positivity
  have hint : interior (closedBall x ρ) = ball x ρ := interior_closedBall x hρ.ne'
  -- Taylor expansion on the segment from `x` towards `x + c•w`
  have hv : x + (0 : E) ∈ interior (closedBall x ρ) := by
    rw [hint, add_zero]; exact mem_ball_self hρ
  have hw' : x + (0 : E) + c • w ∈ interior (closedBall x ρ) := by
    rw [hint, add_zero, mem_ball, dist_self_add_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hcpos]
    calc c * ‖w‖ < c * (‖w‖ + 1) := by
          have := norm_nonneg w
          nlinarith
      _ = ρ / 2 := by rw [hcdef]; field_simp
      _ < ρ := by linarith
  have TA := (convex_closedBall x ρ).taylor_approx_two_segment
    (f := u) (f' := fderiv ℝ u) (f'' := B)
    (fun y hy => hdiff y (by rwa [hint] at hy))
    (mem_closedBall_self hρ.le) (hB.hasFDerivWithinAt.mono interior_subset) hv hw'
  -- clean up the `v = 0` degeneracies and express the bilinear terms with `w`
  have TA' : (fun h : ℝ => u (x + (c * h) • w) - u x - (c * h) * L w
      - (c * h) ^ 2 / 2 * B w w) =o[𝓝[>] 0] fun h => h ^ 2 := by
    refine TA.congr (fun h => ?_) (fun h => rfl)
    have e1 : x + h • (0 : E) + h • (c • w) = x + (c * h) • w := by
      rw [smul_zero, add_zero, smul_smul, mul_comm]
    have e2 : x + h • (0 : E) = x := by rw [smul_zero, add_zero]
    have e3 : (fderiv ℝ u x) (c • w) = c * L w := by rw [map_smul, smul_eq_mul, hLdef]
    have e4 : B (0 : E) (c • w) = 0 := by rw [map_zero, ContinuousLinearMap.zero_apply]
    have e5 : B (c • w) (c • w) = c * (c * B w w) := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [e1, e2, e3, e4, e5]
    ring_nf
  -- reparametrize `h = r / c` to get the expansion in the radius `r`
  have hk : Tendsto (fun r : ℝ => r / c) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Tendsto (fun r : ℝ => r / c) (𝓝 0) (𝓝 (0 / c)) :=
        (continuous_id.div_const c).tendsto 0
      rw [zero_div] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hcpos
  have hO : ((fun h : ℝ => h ^ 2) ∘ fun r : ℝ => r / c) =O[𝓝[>] 0] fun r : ℝ => r ^ 2 := by
    have heq : ((fun h : ℝ => h ^ 2) ∘ fun r : ℝ => r / c)
        = fun r : ℝ => c⁻¹ ^ 2 * r ^ 2 := by
      funext r
      simp only [Function.comp_apply, div_pow]
      field_simp
    rw [heq]
    exact isBigO_const_mul_self _ _ _
  have TA'' := (TA'.comp_tendsto hk).trans_isBigO hO
  -- rewrite the composed error term as the target numerator
  have TA''' : (fun r : ℝ => u (x + r • w) - u x - r * L w - r ^ 2 / 2 * B w w)
      =o[𝓝[>] 0] fun r : ℝ => r ^ 2 := by
    refine TA''.congr (fun r => ?_) (fun r => rfl)
    have : c * (r / c) = r := by field_simp
    simp only [Function.comp_apply, this]
  exact TA'''.tendsto_div_nhds_zero

variable {n : ℕ}

/-! ## The Laplacian vanishes pointwise -/

/-- **Pointwise harmonicity from the mean-value property** — the analytic core of the
converse to the mean-value property (Evans §2.2.2 Thm 3). A continuous function with
the ball mean-value property on an open set `U` has vanishing Laplacian at every point
of `U`. Averaged second-order Taylor expansion; see the file docstring. -/
theorem HasBallMeanValueProperty.laplacian_eq_zero
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasBallMeanValueProperty u U) (hUopen : IsOpen U) (hcont : ContinuousOn u U)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    Δ u x = 0 := by
  -- smoothness from the mean-value property, and the second derivative at `x`
  have hsmooth : ContDiffOn ℝ ∞ u U := hu.contDiffOn hUopen hcont
  have hC2 : ContDiffAt ℝ 2 u x :=
    ((hsmooth x hx).contDiffAt (hUopen.mem_nhds hx)).of_le (by norm_cast)
  set B := fderiv ℝ (fderiv ℝ u) x with hBdef
  -- the Laplacian bridge: `Δ u x = ∑ⱼ B eⱼ eⱼ`
  have hbridge : Δ u x =
      ∑ j, B (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
    rw [laplacian_eq_sum_partialDeriv_iterate_two hC2]
    exact Finset.sum_congr rfl fun j _ => partialDeriv_iterate_two_eq_fderiv_fderiv hC2 j
  rcases isEmpty_or_nonempty (Fin n) with hempty | hne
  · rw [hbridge, Finset.univ_eq_empty, Finset.sum_empty]
  -- radii: `closedBall x ρ ⊆ U` and `Du` is `K`-Lipschitz on it
  obtain ⟨R, hRpos, hRsub⟩ := Metric.isOpen_iff.1 hUopen x hx
  have hC1' : ContDiffAt ℝ 1 (fderiv ℝ u) x := hC2.fderiv_right (m := 1) (by norm_num)
  obtain ⟨K, t, htmem, hlipt⟩ := hC1'.exists_lipschitzOnWith
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := Metric.nhds_basis_closedBall.mem_iff.1 htmem
  set ρ : ℝ := min (R / 2) ρ₁ with hρdef
  have hρpos : 0 < ρ := lt_min (by positivity) hρ₁pos
  have hρU : closedBall x ρ ⊆ U :=
    ((closedBall_subset_closedBall (min_le_left _ _)).trans
      (closedBall_subset_ball (by linarith))).trans hRsub
  have hlip : LipschitzOnWith K (fderiv ℝ u) (closedBall x ρ) :=
    hlipt.mono ((closedBall_subset_closedBall (min_le_right _ _)).trans hρ₁sub)
  -- differentiability data
  have hdiffcb : ∀ y ∈ closedBall x ρ, DifferentiableAt ℝ u y := fun y hy =>
    ((hsmooth y (hρU hy)).contDiffAt (hUopen.mem_nhds (hρU hy))).differentiableAt
      (by simp)
  have hdiffball : ∀ y ∈ ball x ρ, HasFDerivAt u (fderiv ℝ u y) y := fun y hy =>
    (hdiffcb y (ball_subset_closedBall hy)).hasFDerivAt
  have hBderiv : HasFDerivAt (fderiv ℝ u) B x :=
    (hC1'.differentiableAt one_ne_zero).hasFDerivAt
  set L := fderiv ℝ u x with hLdef
  -- the averaged Taylor quotient and the trace integral
  set F : ℝ → EuclideanSpace ℝ (Fin n) → ℝ := fun r w =>
    (u (x + r • w) - u x - r * L w - r ^ 2 / 2 * B w w) / r ^ 2 with hFdef
  set T : ℝ := ∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, B w w with hTdef
  have hIoo : Ioo (0 : ℝ) ρ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hρpos
  -- continuity of the quotient integrand at each fixed small radius
  have hFcont : ∀ r ∈ Ioo (0 : ℝ) ρ,
      ContinuousOn (F r) (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    intro r hr
    have hmaps : ∀ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, x + r • w ∈ U := by
      intro w hw
      refine hρU (mem_closedBall.2 ?_)
      rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
      calc r * ‖w‖ ≤ r * 1 :=
            mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hw) hr.1.le
        _ ≤ ρ := by rw [mul_one]; exact hr.2.le
    have h1 : ContinuousOn (fun w : EuclideanSpace ℝ (Fin n) => u (x + r • w))
        (closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
      hcont.comp (Continuous.continuousOn (by fun_prop)) hmaps
    have h2 : Continuous fun w : EuclideanSpace ℝ (Fin n) => B w w := by fun_prop
    exact ((((h1.sub continuousOn_const).sub
      (Continuous.continuousOn (by fun_prop))).sub
      ((continuous_const.mul h2).continuousOn)).div_const _)
  -- exact value: the mean-value property collapses the average to `-(T/2)`
  have hexact : ∀ r ∈ Ioo (0 : ℝ) ρ,
      ∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, F r w = -(T / 2) := by
    intro r hr
    have hsubU : closedBall x r ⊆ U :=
      (closedBall_subset_closedBall hr.2.le).trans hρU
    -- integrability of the four pieces on the unit ball
    have hint1 : IntegrableOn (fun w : EuclideanSpace ℝ (Fin n) => u (x + r • w))
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) volume := by
      have hmaps : ∀ w ∈ closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, x + r • w ∈ U := by
        intro w hw
        refine hsubU (mem_closedBall.2 ?_)
        rw [dist_self_add_left, norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
        calc r * ‖w‖ ≤ r * 1 :=
              mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hw) hr.1.le
          _ = r := mul_one r
      exact ((hcont.comp (Continuous.continuousOn (by fun_prop)) hmaps).integrableOn_compact
        (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
    have hint3 : IntegrableOn (fun w : EuclideanSpace ℝ (Fin n) => r * L w)
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) volume :=
      integrableOn_ball_of_continuousOn (U := (univ : Set (EuclideanSpace ℝ (Fin n))))
        (Continuous.continuousOn (by fun_prop)) (subset_univ _)
    have hint4 : IntegrableOn
        (fun w : EuclideanSpace ℝ (Fin n) => r ^ 2 / 2 * B w w)
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) volume :=
      integrableOn_ball_of_continuousOn (U := (univ : Set (EuclideanSpace ℝ (Fin n))))
        (Continuous.continuousOn (by fun_prop)) (subset_univ _)
    have hintc : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin n) => u x)
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) volume := integrableOn_const measure_ball_lt_top.ne
    have hint12 : IntegrableOn (fun w : EuclideanSpace ℝ (Fin n) => u (x + r • w) - u x)
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) volume := hint1.sub hintc
    have hint123 : IntegrableOn
        (fun w : EuclideanSpace ℝ (Fin n) => u (x + r • w) - u x - r * L w)
        (ball (0 : EuclideanSpace ℝ (Fin n)) 1) volume := hint12.sub hint3
    calc ∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, F r w
        = (∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1,
            (u (x + r • w) - u x - r * L w - r ^ 2 / 2 * B w w)) / r ^ 2 :=
          integral_div _ _
      _ = ((∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, u (x + r • w))
            - (∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, u x)
            - (∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, r * L w)
            - (∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, r ^ 2 / 2 * B w w)) / r ^ 2 := by
          rw [integral_sub hint123 hint4, integral_sub hint12 hint3,
            integral_sub hint1 hintc]
      _ = -(T / 2) := by
          rw [hu.setIntegral_unitBall_smul hr.1 hsubU, setIntegral_const, smul_eq_mul,
            integral_const_mul, integral_const_mul, setIntegral_ball_clm, ← hTdef]
          have hrne : r ≠ 0 := hr.1.ne'
          field_simp
          ring
  -- dominated convergence: the averaged quotient tends to `0` as `r ↓ 0`
  have hDCT : Tendsto (fun r : ℝ => ∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, F r w)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ _ in ball (0 : EuclideanSpace ℝ (Fin n)) 1, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun _ => (K : ℝ) + ‖B‖ / 2)
    · -- a.e.-measurability at each small radius
      filter_upwards [hIoo] with r hr
      exact ((hFcont r hr).mono ball_subset_closedBall).aestronglyMeasurable
        measurableSet_ball
    · -- the uniform quadratic bound
      filter_upwards [hIoo] with r hr
      rw [ae_restrict_iff' measurableSet_ball]
      refine ae_of_all _ fun w hw => ?_
      have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.1 hw
      have hz : ‖r • w‖ ≤ ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1]
        calc r * ‖w‖ ≤ r * 1 := mul_le_mul_of_nonneg_left hw1.le hr.1.le
          _ ≤ ρ := by rw [mul_one]; exact hr.2.le
      have hquad := norm_add_sub_sub_fderiv_le_of_lipschitzOnWith hdiffcb hlip hz
      have hL : fderiv ℝ u x (r • w) = r * L w := by rw [map_smul, smul_eq_mul, hLdef]
      rw [hL] at hquad
      have hnorm2 : ‖r • w‖ ^ 2 ≤ r ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr.1, mul_pow]
        calc r ^ 2 * ‖w‖ ^ 2 ≤ r ^ 2 * 1 ^ 2 :=
              mul_le_mul_of_nonneg_left (by nlinarith [norm_nonneg w]) (sq_nonneg r)
          _ = r ^ 2 := by ring
      have hBw : |B w w| ≤ ‖B‖ := by
        calc |B w w| ≤ ‖B‖ * ‖w‖ * ‖w‖ := B.le_opNorm₂ w w
          _ ≤ ‖B‖ * 1 * 1 := by gcongr
          _ = ‖B‖ := by ring
      have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr.1 2
      rw [hFdef]
      simp only [Real.norm_eq_abs, abs_div, abs_of_pos hr2]
      rw [div_le_iff₀ hr2]
      have hnum : |u (x + r • w) - u x - r * L w - r ^ 2 / 2 * B w w|
          ≤ K * r ^ 2 + r ^ 2 / 2 * ‖B‖ := by
        calc |u (x + r • w) - u x - r * L w - r ^ 2 / 2 * B w w|
            ≤ |u (x + r • w) - u x - r * L w| + |r ^ 2 / 2 * B w w| := abs_sub _ _
          _ ≤ K * ‖r • w‖ ^ 2 + r ^ 2 / 2 * |B w w| := by
              rw [abs_mul, abs_of_pos (div_pos hr2 two_pos)]
              gcongr
              exact hquad
          _ ≤ K * r ^ 2 + r ^ 2 / 2 * ‖B‖ := by gcongr
      calc |u (x + r • w) - u x - r * L w - r ^ 2 / 2 * B w w|
          ≤ K * r ^ 2 + r ^ 2 / 2 * ‖B‖ := hnum
        _ = ((K : ℝ) + ‖B‖ / 2) * r ^ 2 := by ring
    · exact integrable_const _
    · -- pointwise limit from the Taylor expansion
      rw [ae_restrict_iff' measurableSet_ball]
      refine ae_of_all _ fun w _ => ?_
      exact tendsto_taylor_two_quotient hρpos hdiffball hBderiv w
  -- the constant `-(T/2)` must be the limit `0`
  rw [integral_zero] at hDCT
  have hconst : (fun r : ℝ => ∫ w in ball (0 : EuclideanSpace ℝ (Fin n)) 1, F r w)
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => -(T / 2) := by
    filter_upwards [hIoo] with r hr using hexact r hr
  have hT0 : -(T / 2) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hDCT.congr' hconst)
  have hT : T = 0 := by linarith
  -- the trace formula turns `T = 0` into `∑ⱼ B eⱼ eⱼ = 0`
  obtain ⟨i₀⟩ := hne
  have hbilin := setIntegral_ball_bilin B 1 i₀
  have hκpos := setIntegral_ball_sq_coord_pos one_pos i₀
  have hS : ∑ j, B (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) = 0 := by
    have hmul : (∑ j, B (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) *
        ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) 1, (z i₀) ^ 2 = 0 := by
      rw [← hbilin, ← hTdef, hT]
    exact (mul_eq_zero.1 hmul).resolve_right hκpos.ne'
  rw [hbridge, hS]

/-! ## The converse to the mean-value property -/

/-- **Converse to the mean-value property, Evans §2.2.2 Theorem 3**
(`thm:converse-mean-value-property-laplace`, ball form). A continuous function with
the ball mean-value property on an open set `U ⊆ ℝⁿ` is harmonic on `U` — in
particular `C^∞`, so Evans's `C²` hypothesis is not needed in the solid-ball
formulation. -/
theorem HasBallMeanValueProperty.harmonicOnNhd
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasBallMeanValueProperty u U) (hUopen : IsOpen U) (hcont : ContinuousOn u U) :
    HarmonicOnNhd u U := by
  have hsmooth : ContDiffOn ℝ ∞ u U := hu.contDiffOn hUopen hcont
  intro x hx
  refine ⟨((hsmooth x hx).contDiffAt (hUopen.mem_nhds hx)).of_le (by norm_cast), ?_⟩
  filter_upwards [hUopen.mem_nhds hx] with y hy
  rw [Pi.zero_apply]
  exact hu.laplacian_eq_zero hUopen hcont hy

end EvansLib

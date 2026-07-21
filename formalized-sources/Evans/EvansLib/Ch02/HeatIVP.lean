import EvansLib.Ch02.Heat
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Evans, Ch. 2 §2.3.1 — The initial-value problem for the heat equation

This file continues `EvansLib.Ch02.Heat`, formalizing Evans, *Partial Differential
Equations* (2nd ed.), §2.3.1, formula (9): the candidate solution of the Cauchy
problem
$$\begin{cases} u_t - \Delta u = 0 & \text{in } \R^n\times(0,\infty) \\ u = g & \text{on } \R^n\times\{t=0\} \end{cases}$$
built by convolving the initial datum `g` with the fundamental solution `Φ`:
$$u(x,t) = \int_{\R^n} \Phi(x-y,t)\,g(y)\,dy \qquad (x\in\R^n,\ t>0).$$

The fundamental solution `Φ` and the facts that it is `C^∞` on `{t>0}`, integrates
to `1`, and solves the heat equation (`heatKernelSpatial_solves_heat`) are already
available from `EvansLib.Ch02.Heat`.

## Main results

* `heatSolution` — the convolution solution `u(x,t) = ∫ Φ(x-y,t) g(y) dy`.
* `heatSolution_integrable` — the integrand is integrable (for `g` continuous with
  compact support).
* `heatSolution_pos` — **Evans §2.3.1, infinite propagation speed** (the strict
  positivity remark): if `g ≥ 0` is continuous and positive *somewhere*, then
  `u(x,t) > 0` for *every* `x ∈ ℝⁿ` and `t > 0`.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.1.
-/

open scoped Real ContDiff Topology
open MeasureTheory Metric

noncomputable section

namespace EvansLib

/-! ## Differentiation under the integral against a compactly-supported weight

The following reusable lemma is the analytic engine for verifying that the heat
convolution solves the heat equation. It differentiates a one-parameter family of
full-space integrals `s ↦ ∫ K s y · g y dy` under the integral sign. Compact support
of the weight `g` reduces the domination hypothesis of the parametric-integral
differentiation theorem to a *constant bound on a compact set*, obtained from
continuity. The statement is deliberately iterable: the derivative is again an integral
of the same shape, so applying it twice yields second derivatives (the spatial
Laplacian). -/

/-- **Differentiation under the integral sign against a compactly-supported weight.**
Let `g` be continuous with compact support and let `K, K' : ℝ → ℝⁿ → ℝ` be such that on
an open set `U ∋ s₀` each slice `K s` is continuous in `y`, `K'` is jointly continuous,
and `s ↦ K s y` is differentiable with derivative `K' s y`. Then the parametrized
integral `s ↦ ∫ K s y · g y dy` is differentiable at `s₀`, with the derivative obtained
by differentiating under the integral sign:
`HasDerivAt (fun s ↦ ∫ K s y · g y) (∫ K' s₀ y · g y) s₀`. -/
lemma hasDerivAt_integral_mul_hasCompactSupport
    {n : ℕ} {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    {K K' : ℝ → EuclideanSpace ℝ (Fin n) → ℝ} {U : Set ℝ} (hU : IsOpen U) {s₀ : ℝ} (hs₀ : s₀ ∈ U)
    (hKcont : ∀ s ∈ U, Continuous (fun y => K s y))
    (hK'cont : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => K' p.1 p.2) (U ×ˢ Set.univ))
    (hderiv : ∀ s ∈ U, ∀ y, HasDerivAt (fun s => K s y) (K' s y) s) :
    HasDerivAt (fun s => ∫ y, K s y * g y) (∫ y, K' s₀ y * g y) s₀ := by
  obtain ⟨ε, εpos, hball⟩ := Metric.isOpen_iff.1 hU s₀ hs₀
  set ε' := ε / 2 with hε'
  have hε'pos : 0 < ε' := by positivity
  have hcball : Metric.closedBall s₀ ε' ⊆ U := by
    intro z hz
    exact hball (lt_of_le_of_lt (Metric.mem_closedBall.1 hz) (by simp [hε']; linarith))
  have hballU : Metric.ball s₀ ε' ⊆ U := (Metric.ball_subset_closedBall).trans hcball
  have hKset : IsCompact (Metric.closedBall s₀ ε' ×ˢ tsupport g) :=
    (isCompact_closedBall _ _).prod hgc
  have hcontφ : ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => K' p.1 p.2 * g p.2)
      (Metric.closedBall s₀ ε' ×ˢ tsupport g) := by
    apply ContinuousOn.mul
    · exact hK'cont.mono (Set.prod_mono hcball (Set.subset_univ _))
    · exact (hg.comp continuous_snd).continuousOn
  obtain ⟨C, hC⟩ := hKset.exists_bound_of_continuousOn hcontφ
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (bound := (tsupport g).indicator (fun _ => C'))
    (F := fun s y => K s y * g y) (F' := fun s y => K' s y * g y)
    (ball_mem_nhds s₀ hε'pos)
    (Filter.eventually_of_mem (hU.mem_nhds hs₀)
      (fun s' hs' => ((hKcont s' hs').mul hg).aestronglyMeasurable))
    ?_ ?_ ?_ ?_ ?_).2
  · exact ((hKcont s₀ hs₀).mul hg).integrable_of_hasCompactSupport hgc.mul_left
  · have hc : Continuous (fun y => K' s₀ y) := by
      have := hK'cont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun y => ⟨hs₀, Set.mem_univ _⟩)
      simpa using this
    exact (hc.mul hg).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y s' hs' => ?_)
    show ‖K' s' y * g y‖ ≤ (tsupport g).indicator (fun _ => C') y
    by_cases hy : y ∈ tsupport g
    · rw [Set.indicator_of_mem hy]
      exact (hC (s', y) ⟨Metric.ball_subset_closedBall hs', hy⟩).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hy, Set.indicator_of_notMem hy]
      simp
  · rw [integrable_indicator_iff (isClosed_tsupport g).measurableSet]
    exact integrableOn_const (hs := hgc.measure_lt_top.ne)
  · refine Filter.Eventually.of_forall (fun y s' hs' => ?_)
    exact (hderiv s' (hballU hs') y).mul_const (g y)

/-- **Evans §2.3.1, formula (9): the convolution solution of the heat Cauchy
problem.** Given initial data `g : ℝⁿ → ℝ`, the function
$$u(x,t) := \int_{\R^n} \Phi(x-y,t)\,g(y)\,dy$$
where `Φ(·,t) = heatKernelSpatial n t` is the fixed-time Gaussian slice of the
fundamental solution. -/
def heatSolution (n : ℕ) (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ → ℝ :=
  fun x t => ∫ y, heatKernelSpatial n t (x - y) * g y

/-- The heat kernel is strictly positive for every `t > 0`. -/
lemma heatKernelSpatial_pos {n : ℕ} {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    0 < heatKernelSpatial n t x := by
  rw [heatKernelSpatial]
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  positivity

/-- The kernel `y ↦ Φ(x−y,t)` is continuous. -/
lemma continuous_heatKernelSpatial_sub {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun y => heatKernelSpatial n t (x - y)) :=
  (heatKernelSpatial_contDiff n t).continuous.comp (continuous_const.sub continuous_id)

/-- **Integrability of the heat-convolution integrand.** For `g` continuous with
compact support, `y ↦ Φ(x−y,t) g(y)` is continuous with compact support, hence
integrable. -/
lemma heatSolution_integrable {n : ℕ} (t : ℝ) {g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => heatKernelSpatial n t (x - y) * g y) := by
  refine Continuous.integrable_of_hasCompactSupport
    ((continuous_heatKernelSpatial_sub t x).mul hg) ?_
  exact hgc.mul_left

/-- **Evans §2.3.1, infinite propagation speed (strict positivity).** If the initial
datum `g` is continuous, nonnegative, has compact support, and is positive somewhere
(`g x₀ > 0`), then the heat-convolution solution is *strictly positive everywhere*:
`u(x,t) > 0` for all `x ∈ ℝⁿ` and all `t > 0`. Thus a disturbance that is positive at
a single point instantly makes the temperature positive throughout space — the heat
equation propagates signals with infinite speed. -/
theorem heatSolution_pos {n : ℕ} {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg0 : 0 ≤ g) {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : 0 < g x₀)
    (x : EuclideanSpace ℝ (Fin n)) :
    0 < heatSolution n g x t := by
  rw [heatSolution]
  refine integral_pos_of_integrable_nonneg_nonzero
    ((continuous_heatKernelSpatial_sub t x).mul hg)
    (heatSolution_integrable t hg hgc x) ?_ (x := x₀) ?_
  · intro y
    exact mul_nonneg (heatKernelSpatial_pos ht _).le (hg0 y)
  · exact (mul_pos (heatKernelSpatial_pos ht _) hx₀).ne'

/-! ## The convolution solves the heat equation on `{t>0}`

We now verify Evans §2.3.1, Theorem (ii): for continuous initial data `g` with
compact support, the convolution `u(x,t) = ∫ Φ(x−y,t) g(y) dy` solves the heat
equation `u_t = Δu` for every `t > 0`. The derivatives pass under the integral by
`hasDerivAt_integral_mul_hasCompactSupport`, and the pointwise identity
`∂ₜΦ = Δ_xΦ` is `heatKernelSpatial_solves_heat` from `EvansLib.Ch02.Heat`. -/

/-- **Time HasDerivAt of the heat-kernel slice** (the `HasDerivAt` refinement of
`heatKernelSpatial_time_deriv`). For `t > 0`,
`d/ds Φ(x,s)|_{s=t} = Φ(x,t) · (‖x‖²/(4t²) − n/(2t))`. -/
lemma heatKernelSpatial_hasDerivAt_time {n : ℕ} {t : ℝ} (ht : 0 < t)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => heatKernelSpatial n s x)
      (heatKernelSpatial n t x * (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t))) t := by
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hH : HasDerivAt (fun s => -(n : ℝ) / 2 * Real.log (4 * Real.pi * s) - ‖x‖ ^ 2 / (4 * s))
      (‖x‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) t := by
    have hw : HasDerivAt (fun s : ℝ => 4 * Real.pi * s) (4 * Real.pi) t := by
      simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
    have hlog : HasDerivAt (fun s : ℝ => Real.log (4 * Real.pi * s)) (1 / t) t := by
      have := hw.log h4.ne'; convert this using 1; field_simp
    have h4s : HasDerivAt (fun s : ℝ => 4 * s) (4 : ℝ) t := by
      simpa using (hasDerivAt_id t).const_mul (4 : ℝ)
    have hdiv : HasDerivAt (fun s : ℝ => ‖x‖ ^ 2 / (4 * s)) (-(‖x‖ ^ 2) / (4 * t ^ 2)) t := by
      have := (hasDerivAt_const t (‖x‖ ^ 2)).div h4s (by positivity)
      convert this using 1; field_simp; ring
    have := (hlog.const_mul (-(n : ℝ) / 2)).sub hdiv
    convert this using 1; field_simp; ring
  have hev : (fun s => heatKernelSpatial n s x)
      =ᶠ[nhds t] fun s => Real.exp (-(n : ℝ) / 2 * Real.log (4 * Real.pi * s) - ‖x‖ ^ 2 / (4 * s)) := by
    filter_upwards [isOpen_Ioi.eventually_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)] with s hs
    exact heatKernelSpatial_eq_exp hs x
  have hd := (hH.exp).congr_of_eventuallyEq hev
  rw [← heatKernelSpatial_eq_exp ht x] at hd
  exact hd

/-- Joint continuity of `(s,y) ↦ Φ(x−y,s)` on `{s>0} × ℝⁿ`. -/
lemma heatKernelSpatial_sub_continuousOn {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) => heatKernelSpatial n p.1 (x - p.2))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  unfold heatKernelSpatial
  apply ContinuousOn.mul
  · intro p hp
    have hp1 : (0:ℝ) < p.1 := hp.1
    apply ContinuousAt.continuousWithinAt
    have hbase : ContinuousAt (fun p : ℝ × EuclideanSpace ℝ (Fin n) => 4 * Real.pi * p.1) p :=
      (continuous_const.mul continuous_fst).continuousAt
    exact hbase.rpow_const (Or.inl (by positivity))
  · apply Real.continuous_exp.comp_continuousOn
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp; have hp1 : (0:ℝ) < p.1 := hp.1; exact mul_ne_zero (by norm_num) hp1.ne'

/-- Joint continuity of the time-derivative kernel `(s,y) ↦ ∂ₜΦ(x−y,s)` on `{s>0}×ℝⁿ`. -/
lemma heatTimeDerivKernel_continuousOn {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousOn (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      heatKernelSpatial n p.1 (x - p.2) * (‖x - p.2‖ ^ 2 / (4 * p.1 ^ 2) - (n : ℝ) / (2 * p.1)))
      (Set.Ioi 0 ×ˢ Set.univ) := by
  apply (heatKernelSpatial_sub_continuousOn x).mul
  apply ContinuousOn.sub
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp; have hp1 : (0:ℝ) < p.1 := hp.1
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ hp1.ne')
  · apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro p hp; have hp1 : (0:ℝ) < p.1 := hp.1; exact mul_ne_zero (by norm_num) hp1.ne'

/-- **Time derivative of the heat convolution.** For `g` continuous with compact
support and `t > 0`, `∂ₜ u(x,t) = ∫ ∂ₜΦ(x−y,t) g(y) dy`. -/
lemma heatSolution_hasDerivAt_time {n : ℕ} {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => heatSolution n g x s)
      (∫ y, deriv (fun s => heatKernelSpatial n s (x - y)) t * g y) t := by
  have key := hasDerivAt_integral_mul_hasCompactSupport hg hgc isOpen_Ioi ht
    (K := fun s y => heatKernelSpatial n s (x - y))
    (K' := fun s y =>
      heatKernelSpatial n s (x - y) * (‖x - y‖ ^ 2 / (4 * s ^ 2) - (n : ℝ) / (2 * s)))
    (fun s _ => continuous_heatKernelSpatial_sub s x)
    (heatTimeDerivKernel_continuousOn x)
    (fun s hs y => heatKernelSpatial_hasDerivAt_time hs (x - y))
  have hint : (∫ y, heatKernelSpatial n t (x - y)
        * (‖x - y‖ ^ 2 / (4 * t ^ 2) - (n : ℝ) / (2 * t)) * g y)
      = ∫ y, deriv (fun s => heatKernelSpatial n s (x - y)) t * g y := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [(heatKernelSpatial_hasDerivAt_time ht (x - y)).deriv]
  rw [← hint]
  exact key

/-! ### Spatial derivatives of the heat convolution

For fixed `t > 0` the kernel `heatKernelSpatial n t` is `C^∞` on all of space, so the
line restriction `s ↦ Φ(z + s·eⱼ, t)` is smooth for every `s`. Its first two
derivatives have the closed forms below (`Φ · (−(zⱼ+s)/2t)` and
`Φ · ((zⱼ+s)²/4t² − 1/2t)`), which we feed to `hasDerivAt_integral_mul_hasCompactSupport`
twice to differentiate the convolution twice under the integral sign. -/

/-- **First derivative of the heat kernel along the `eⱼ`-line.** -/
lemma heatKernelSpatial_line_deriv1 {n : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) (s : ℝ) :
    HasDerivAt (fun s => heatKernelSpatial n t (z + s • EuclideanSpace.single j (1:ℝ)))
      (heatKernelSpatial n t (z + s • EuclideanSpace.single j (1:ℝ)) * (-(z j + s) / (2 * t))) s := by
  have ht0 : (t:ℝ) ≠ 0 := ht.ne'
  have hfun : (fun s => heatKernelSpatial n t (z + s • EuclideanSpace.single j (1:ℝ)))
      = fun s => (4 * Real.pi * t) ^ (-(n:ℝ)/2)
          * Real.exp (-(‖z‖^2 + 2*s*(z j) + s^2)/(4*t)) := by
    funext s; rw [heatKernelSpatial, norm_add_smul_single_sq]
  have hQ : HasDerivAt (fun s => -(‖z‖^2 + 2*s*(z j) + s^2)/(4*t))
      (-(2*(z j) + 2*s)/(4*t)) s := by
    have e1 : HasDerivAt (fun s : ℝ => 2 * s * (z j)) (2 * (z j)) s := by
      have h := ((hasDerivAt_id s).const_mul (2 : ℝ)).mul_const (z j); simpa using h
    have e2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * s) s := by simpa using hasDerivAt_pow 2 s
    have hnum : HasDerivAt (fun s : ℝ => ‖z‖^2 + 2*s*(z j) + s^2) (2*(z j) + 2*s) s := by
      have h := ((hasDerivAt_const s (‖z‖^2)).add e1).add e2; simpa using h
    exact hnum.neg.div_const (4*t)
  rw [hfun]
  have hd := (hQ.exp).const_mul ((4 * Real.pi * t) ^ (-(n:ℝ)/2))
  convert hd using 1
  rw [show heatKernelSpatial n t (z + s • EuclideanSpace.single j (1:ℝ))
      = (4 * Real.pi * t) ^ (-(n:ℝ)/2) * Real.exp (-(‖z‖^2 + 2*s*(z j) + s^2)/(4*t)) by
        rw [heatKernelSpatial, norm_add_smul_single_sq]]
  field_simp; ring

/-- **Second derivative of the heat kernel along the `eⱼ`-line.** Its value at `s = 0`
is `Φ · (zⱼ²/4t² − 1/2t) = (∂ⱼ² Φ(·,t))(z)` (`heatKernelSpatial_partial_sq`). -/
lemma heatKernelSpatial_line_deriv2 {n : ℕ} {t : ℝ} (ht : 0 < t)
    (z : EuclideanSpace ℝ (Fin n)) (j : Fin n) (s : ℝ) :
    HasDerivAt (fun s => heatKernelSpatial n t (z + s • EuclideanSpace.single j (1:ℝ))
        * (-(z j + s) / (2 * t)))
      (heatKernelSpatial n t (z + s • EuclideanSpace.single j (1:ℝ))
        * ((z j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t))) s := by
  have ht0 : (t:ℝ) ≠ 0 := ht.ne'
  have hL : HasDerivAt (fun s : ℝ => -(z j + s) / (2 * t)) (-1 / (2 * t)) s := by
    have h := (((hasDerivAt_const s (z j)).add (hasDerivAt_id s)).neg).div_const (2 * t)
    convert h using 1; ring
  have hmul := (heatKernelSpatial_line_deriv1 ht z j s).mul hL
  convert hmul using 1
  field_simp; ring

/-- Continuity of the spatial line kernel `(s,y) ↦ Φ((x−y)+s·eⱼ, t)` (fixed `t`). -/
lemma continuous_heatLineKernel {n : ℕ} (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      heatKernelSpatial n t ((x - p.2) + p.1 • EuclideanSpace.single j (1:ℝ))) :=
  (heatKernelSpatial_contDiff n t).continuous.comp
    ((continuous_const.sub continuous_snd).add (continuous_fst.smul continuous_const))

/-- **Spatial second derivative of the heat convolution.** For `g` continuous with
compact support and `t > 0`, the pure second partial of `u(·,t)` along `eⱼ` (written as
the second derivative of the line restriction at `s = 0`) passes under the integral:
`∂ⱼ² u(x,t) = ∫ (∂ⱼ² Φ(·,t))(x−y) g(y) dy`. Proved by two applications of
`hasDerivAt_integral_mul_hasCompactSupport` to the closed-form line derivatives. -/
lemma heatSolution_iteratedDeriv2_space {n : ℕ} {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
    iteratedDeriv 2 (fun s : ℝ => heatSolution n g (x + s • EuclideanSpace.single j (1:ℝ)) t) 0
      = ∫ y, (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y) * g y := by
  set e := EuclideanSpace.single j (1:ℝ) with he
  have hKcont1 : ∀ s : ℝ, Continuous (fun y => heatKernelSpatial n t ((x - y) + s • e)) :=
    fun s => (heatKernelSpatial_contDiff n t).continuous.comp
      ((continuous_const.sub continuous_id).add continuous_const)
  have H1 : ∀ s₀ : ℝ, HasDerivAt (fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y)
      (∫ y, heatKernelSpatial n t ((x - y) + s₀ • e) * (-((x - y) j + s₀) / (2 * t)) * g y) s₀ := by
    intro s₀
    refine hasDerivAt_integral_mul_hasCompactSupport hg hgc isOpen_univ (Set.mem_univ s₀)
      (K := fun s y => heatKernelSpatial n t ((x - y) + s • e))
      (K' := fun s y => heatKernelSpatial n t ((x - y) + s • e) * (-((x - y) j + s) / (2 * t)))
      (fun s _ => hKcont1 s)
      (((continuous_heatLineKernel t x j).mul (by fun_prop)).continuousOn)
      (fun s _ y => heatKernelSpatial_line_deriv1 ht (x - y) j s)
  have H2 : HasDerivAt
      (fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * (-((x - y) j + s) / (2 * t)) * g y)
      (∫ y, heatKernelSpatial n t ((x - y) + (0:ℝ) • e)
        * (((x - y) j + 0) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * g y) 0 := by
    refine hasDerivAt_integral_mul_hasCompactSupport hg hgc isOpen_univ (Set.mem_univ 0)
      (K := fun s y => heatKernelSpatial n t ((x - y) + s • e) * (-((x - y) j + s) / (2 * t)))
      (K' := fun s y => heatKernelSpatial n t ((x - y) + s • e)
        * (((x - y) j + s) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)))
      (fun s _ => (hKcont1 s).mul (by fun_prop))
      (((continuous_heatLineKernel t x j).mul (by fun_prop)).continuousOn)
      (fun s _ y => heatKernelSpatial_line_deriv2 ht (x - y) j s)
  have hFeq : (fun s : ℝ => heatSolution n g (x + s • e) t)
      = fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y := by
    funext s; rw [heatSolution]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    dsimp only
    rw [add_sub_right_comm]
  rw [hFeq, iteratedDeriv_succ, iteratedDeriv_one]
  have hderivF : (deriv fun s => ∫ y, heatKernelSpatial n t ((x - y) + s • e) * g y)
      = fun s₀ => ∫ y, heatKernelSpatial n t ((x - y) + s₀ • e)
          * (-((x - y) j + s₀) / (2 * t)) * g y := by
    funext s₀; exact (H1 s₀).deriv
  rw [hderivF, H2.deriv]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  simp only [zero_smul, add_zero]
  rw [← heatKernelSpatial_partial_sq ht (x - y) j]

/-- **Evans §2.3.1, Theorem (ii): the heat convolution solves the heat equation.**
For continuous initial data `g` with compact support and every `t > 0`, the convolution
`u(x,t) = ∫ Φ(x−y,t) g(y) dy` satisfies `u_t = Δu`, written here as
`∂ₜ u(x,t) = ∑ⱼ ∂ⱼ² u(x,t)` (the time derivative equals the sum of pure second spatial
derivatives). Both sides differentiate under the integral sign
(`heatSolution_hasDerivAt_time`, `heatSolution_iteratedDeriv2_space`), and the pointwise
identity `∂ₜΦ = Δ_xΦ` is `heatKernelSpatial_solves_heat` from `EvansLib.Ch02.Heat`. -/
theorem heatSolution_solves_heat {n : ℕ} {t : ℝ} (ht : 0 < t)
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (x : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => heatSolution n g x s) t
      = ∑ j : Fin n,
          iteratedDeriv 2 (fun s : ℝ => heatSolution n g (x + s • EuclideanSpace.single j (1:ℝ)) t) 0 := by
  have hint_ps : ∀ j : Fin n,
      Integrable (fun y => (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y) * g y) := by
    intro j
    have hc : Continuous (fun y => (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y)) := by
      have hcf : (fun y => (partialDeriv j)^[2] (heatKernelSpatial n t) (x - y))
          = fun y => heatKernelSpatial n t (x - y) * ((x - y) j ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) := by
        funext y; rw [heatKernelSpatial_partial_sq ht (x - y) j]
      rw [hcf]; exact (continuous_heatKernelSpatial_sub t x).mul (by fun_prop)
    exact (hc.mul hg).integrable_of_hasCompactSupport hgc.mul_left
  rw [(heatSolution_hasDerivAt_time ht hg hgc x).deriv,
    Finset.sum_congr rfl (fun j _ => heatSolution_iteratedDeriv2_space ht hg hgc x j),
    ← integral_finset_sum Finset.univ (fun j _ => hint_ps j)]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  dsimp only
  rw [← Finset.sum_mul]
  congr 1
  exact heatKernelSpatial_solves_heat ht (x - y)

end EvansLib

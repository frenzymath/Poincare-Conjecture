import EvansLib.Ch02.HeatIVP
import EvansLib.Ch02.HeatIVPLimit
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Evans, Ch. 2 §2.3.1 — Smoothness of the heat-convolution solution (part (i))

This file completes the last open part of Evans, *Partial Differential Equations*
(2nd ed.), §2.3.1, Theorem 1: **part (i)**, that the convolution solution
$$u(x,t) = \int_{\R^n} \Phi(x-y,t)\,g(y)\,dy$$
of the heat Cauchy problem is `C^∞` on `ℝⁿ × (0,∞)`.  Parts (ii) (solves the heat
equation, `EvansLib.heatSolution_solves_heat`) and (iii) (attains the initial datum,
`EvansLib.heatSolution_tendsto_initial`) are already available from `HeatIVP.lean` /
`HeatIVPLimit.lean`, both for `g` continuous with compact support; this file supplies
the matching smoothness statement, so all three parts of Evans's theorem are now
formalized for compactly-supported continuous data.

## The obstruction, and the route around it

The heat kernel `Φ(·,t)` is `C^∞` but **not** compactly supported (it is a Gaussian),
while the datum `g` is compactly supported but only continuous.  Mathlib's convolution
smoothness lemmas (`contDiffOn_convolution_right_with_param`) require the *smooth* factor
to be the compactly-supported one — exactly backwards from this setup — so they do not
apply directly.  The fix is a **cutoff**: multiply the kernel by a smooth bump `χ` that
equals `1` on a large ball.  The truncated kernel `χ·Φ(·,t)` is jointly `C^∞` in `(t,x)`
*and* compactly supported in space (uniformly in `t`), so the parametric convolution lemma
applies and yields joint smoothness of `(t,x) ↦ (g ⋆ (χ·Φ(·,t)))(x)`.  Near any target
point this truncated convolution *equals* the true `u` (because `χ ≡ 1` where the
integrand lives), so `u` inherits `C^∞`-smoothness there; the target point was arbitrary.

## Main results

* `EvansLib.heatKernelSpatial_contDiffOn_prod` — the heat kernel is jointly `C^∞` in
  `(t,x)` on `(0,∞) × ℝⁿ` (reusable kernel infrastructure).
* `EvansLib.heatSolution_contDiffOn` — **Evans §2.3.1 Thm 1(i)**: `u ∈ C^∞(ℝⁿ × (0,∞))`.
* `EvansLib.heatSolution_isSolutionOfIVP` — the full three-part theorem bundled for
  compactly-supported continuous data.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.1.
-/

open scoped Real ContDiff Convolution Topology
open MeasureTheory Metric Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Joint smoothness of the heat kernel in `(t,x)` -/

/-- **The heat kernel is jointly `C^∞` in `(t,x)` on `(0,∞) × ℝⁿ`.** The fixed-time
smoothness `heatKernelSpatial_contDiff` only handles the spatial variable; here the time
variable is included, using that `t ↦ (4πt)^{-n/2}` (an `rpow` with positive base) and
`(t,x) ↦ \exp(-‖x‖²/(4t))` are smooth on the open half-space `{t>0}`. This feeds the
truncated-kernel smoothness needed for the parametric convolution lemma. -/
theorem heatKernelSpatial_contDiffOn_prod (n : ℕ) :
    ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      heatKernelSpatial n q.1 q.2) (Set.Ioi 0 ×ˢ Set.univ) := by
  intro q hq
  have hq1 : (0 : ℝ) < q.1 := hq.1
  have hbne : (4 * Real.pi * q.1) ≠ 0 := by positivity
  have h4ne : (4 * q.1) ≠ 0 := by positivity
  apply ContDiffAt.contDiffWithinAt
  unfold heatKernelSpatial
  apply ContDiffAt.mul
  · -- `(4πt)^{-n/2}`: `rpow` with positive, hence nonzero, base
    have hbase : ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => 4 * Real.pi * q.1) q :=
      contDiffAt_const.mul contDiff_fst.contDiffAt
    exact (Real.contDiffAt_rpow_const_of_ne (p := -(n:ℝ)/2) hbne).comp q hbase
  · -- `exp(-‖x‖²/(4t))`: composite of smooth pieces on `{t>0}`
    apply Real.contDiff_exp.contDiffAt.comp q
    have hnsq : ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => ‖q.2‖ ^ 2) q :=
      (contDiff_norm_sq ℝ).contDiffAt.comp q contDiff_snd.contDiffAt
    have hden : ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) => 4 * q.1) q :=
      contDiffAt_const.mul contDiff_fst.contDiffAt
    exact hnsq.neg.div hden h4ne

/-! ## The cutoff argument -/

/-- **Smoothness of the truncated convolution.** For any smooth bump `χ`, the map
`(t,x) ↦ (g ⋆ (χ·Φ(·,t)))(x)` is `C^∞` on `(0,∞) × ℝⁿ`. The truncated kernel
`z ↦ χ(z)·Φ(z,t)` is jointly `C^∞` (product of the bump with the joint-smooth kernel)
and compactly supported in `z` uniformly in `t` (its support lies in `tsupport χ`), so
mathlib's parametric convolution-smoothness lemma applies with the datum `g` (only
locally integrable) as the non-smooth factor. -/
theorem truncConv_contDiffOn (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g)
    (χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n))) :
    ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun z => χ z * heatKernelSpatial n q.1 z)) q.2)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  have hgtrunc : ContDiffOn ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      χ q.2 * heatKernelSpatial n q.1 q.2) (Set.Ioi 0 ×ˢ Set.univ) :=
    ((χ.contDiff.comp contDiff_snd).contDiffOn).mul (heatKernelSpatial_contDiffOn_prod n)
  have hgs : ∀ (p : ℝ), ∀ (z : EuclideanSpace ℝ (Fin n)), p ∈ Set.Ioi (0:ℝ) →
      z ∉ tsupport χ → χ z * heatKernelSpatial n p z = 0 := by
    intro p z _ hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]
  exact contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℝ)
    isOpen_Ioi χ.hasCompactSupport hgs hg.locallyIntegrable hgtrunc

/-- **The truncated convolution agrees with `u` where `χ ≡ 1`.** If the bump `χ` is `1`
on every difference `x - y` with `y ∈ tsupport g`, then the truncated convolution equals
the genuine heat-convolution solution `heatSolution n g x t`. -/
theorem truncConv_eq (g : EuclideanSpace ℝ (Fin n) → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (h1 : ∀ y ∈ tsupport g, χ (x - y) = 1) :
    (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun z => χ z * heatKernelSpatial n t z)) x
      = heatSolution n g x t := by
  rw [convolution, heatSolution]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall (fun y => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  by_cases hy : y ∈ tsupport g
  · rw [h1 y hy, one_mul]; ring
  · rw [image_eq_zero_of_notMem_tsupport hy]; ring

/-! ## Evans §2.3.1, Theorem 1(i): smoothness of the heat-convolution solution -/

/-- **Evans §2.3.1, Theorem 1(i).** For `g` continuous with compact support, the heat
convolution solution `u(x,t) = ∫ Φ(x-y,t) g(y) dy` is `C^∞` on `ℝⁿ × (0,∞)`.

The proof is the cutoff argument: near any target `(x₀,t₀)` (with `t₀>0`) pick a bump
`χ` that is `1` on a ball large enough to contain every `x - y` for `x` near `x₀` and
`y ∈ tsupport g`; then `u` coincides on a neighbourhood with the smooth truncated
convolution `(t,x) ↦ (g ⋆ (χ·Φ(·,t)))(x)`, so it is `C^∞` there. -/
theorem heatSolution_contDiffOn (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
      (Set.univ ×ˢ Set.Ioi 0) := by
  have hcpt : IsCompact (tsupport g) := hgc
  obtain ⟨M₀, hM₀⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hcpt.isBounded
  set M : ℝ := max M₀ 0 with hMdef
  have hM : tsupport g ⊆ Metric.closedBall 0 M :=
    hM₀.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  intro p hp
  have ht₀ : (0 : ℝ) < p.2 := hp.2
  set x₀ := p.1 with hx₀
  set t₀ := p.2 with ht₀def
  set R : ℝ := ‖x₀‖ + 1 + M with hR
  have hMnn : 0 ≤ M := le_max_right M₀ 0
  have hRpos : 0 < R + 1 := by rw [hR]; have := norm_nonneg x₀; linarith
  -- a bump equal to `1` on `closedBall 0 (R+1)`, supported in `closedBall 0 (R+2)`
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
    { rIn := R + 1, rOut := R + 2, rIn_pos := hRpos, rIn_lt_rOut := by linarith }
  have hrIn : χ.rIn = R + 1 := rfl
  -- (i) the truncated convolution is smooth, in `(t,x)` order …
  have hCDat : ContDiffAt ℝ ∞ (fun q : ℝ × EuclideanSpace ℝ (Fin n) =>
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (fun z => χ z * heatKernelSpatial n q.1 z)) q.2)
      (t₀, x₀) :=
    (truncConv_contDiffOn g hg χ).contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht₀, Set.mem_univ _⟩)
  -- … reorder to `(x,t)` via the smooth coordinate swap …
  have hcomp := hCDat.comp (x₀, t₀)
    ((contDiff_snd.prodMk contDiff_fst).contDiffAt
      (x := (x₀, t₀)) (n := (∞ : WithTop ℕ∞)))
  -- … and `u` equals it on the neighbourhood `ball x₀ 1 × univ`
  have hnbhd : Metric.ball x₀ 1 ×ˢ (Set.univ : Set ℝ) ∈ 𝓝 (x₀, t₀) :=
    (Metric.isOpen_ball.prod isOpen_univ).mem_nhds ⟨Metric.mem_ball_self one_pos, Set.mem_univ _⟩
  have hEq : (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
      =ᶠ[𝓝 (x₀, t₀)]
      (fun r : EuclideanSpace ℝ (Fin n) × ℝ =>
        (g ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
          (fun z => χ z * heatKernelSpatial n (r.2) z)) r.1) := by
    refine Filter.eventually_of_mem hnbhd ?_
    rintro ⟨x, t⟩ ⟨hx, -⟩
    have h1 : ∀ y ∈ tsupport g, χ (x - y) = 1 := by
      intro y hy
      apply χ.one_of_mem_closedBall
      rw [Metric.mem_closedBall, dist_zero_right, hrIn]
      have hxb : ‖x‖ < ‖x₀‖ + 1 := by
        have hd : dist x x₀ < 1 := hx
        rw [dist_eq_norm] at hd
        calc ‖x‖ = ‖x₀ + (x - x₀)‖ := by rw [add_sub_cancel]
        _ ≤ ‖x₀‖ + ‖x - x₀‖ := norm_add_le _ _
        _ < ‖x₀‖ + 1 := by linarith
      have hyb : ‖y‖ ≤ M := by
        have := hM hy; rwa [Metric.mem_closedBall, dist_zero_right] at this
      have hxy : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      rw [hR]; linarith
    exact (truncConv_eq g t x χ h1).symm
  exact (hcomp.congr_of_eventuallyEq hEq).contDiffWithinAt

/-! ## Evans §2.3.1, Theorem 1: the three parts bundled -/

/-- **Evans §2.3.1, Theorem 1 (solution of the heat initial-value problem)**, for
compactly-supported continuous data. The convolution solution
`u(x,t) = ∫ Φ(x-y,t) g(y) dy` satisfies:
(i) `u ∈ C^∞(ℝⁿ × (0,∞))`;
(ii) `uₜ - Δu = 0` for `t>0` (in the coordinate-line form `∂ₜu = ∑ⱼ ∂ⱼ²u`);
(iii) `u(x,t) → g(x₀)` as `(x,t) → (x₀,0⁺)`.
This packages `heatSolution_contDiffOn`, `heatSolution_solves_heat`, and
`heatSolution_tendsto_initial`. (Evans states the theorem for `g ∈ C ∩ L^∞`; the
compact-support hypothesis is the scope of all three constituent results.) -/
theorem heatSolution_isSolutionOfIVP (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    ContDiffOn ℝ ∞ (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
        (Set.univ ×ˢ Set.Ioi 0)
      ∧ (∀ t : ℝ, 0 < t → ∀ x : EuclideanSpace ℝ (Fin n),
          deriv (fun s => heatSolution n g x s) t
            = ∑ j : Fin n, iteratedDeriv 2
                (fun s : ℝ => heatSolution n g (x + s • EuclideanSpace.single j (1:ℝ)) t) 0)
      ∧ (∀ x₀ : EuclideanSpace ℝ (Fin n),
          Filter.Tendsto (fun p : EuclideanSpace ℝ (Fin n) × ℝ => heatSolution n g p.1 p.2)
            (𝓝 x₀ ×ˢ 𝓝[>] (0:ℝ)) (𝓝 (g x₀))) :=
  ⟨heatSolution_contDiffOn g hg hgc,
    fun _t ht x => heatSolution_solves_heat ht hg hgc x,
    fun x₀ => heatSolution_tendsto_initial hg hgc x₀⟩

end EvansLib

import DoCarmoLib.Riemannian.Variation.IndexForm
import DoCarmoLib.Riemannian.Variation.VelocitySeededFrameAlong
import DoCarmoLib.Riemannian.Variation.ParallelCovariantField
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4RicciSectional
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality

/-!
# Bonnet–Myers: the index-form computation (do Carmo Ch. 9, §3, `thm:dc-ch9-3-1`)

This file assembles the **geometric heart** of Bonnet–Myers, `thm:dc-ch9-3-1`: along a
minimizing geodesic `γ : [0, 1] → M` of speed `ℓ`, if the Ricci curvature is bounded below by
`1/r² > 0` and `ℓ > π r`, then the sum of the index forms of the fields
`V_j(t) = (\sin \pi t)\,e_j(t)` (`e_j` the parallel orthonormal frame orthogonal to `γ'`) is
strictly negative — do Carmo's

$$\tfrac12\sum_j E_j''(0) = \int_0^1\big((n-1)\pi^2\cos^2\pi t - (\sin^2\pi t)\,\ell^2\,\mathrm{Ric}\big)\,dt < 0.$$

By formula (6) (`lem:dc-ch9-2-10-formula6`) each index form is `½E_j''(0)`; and since `γ`
minimizes energy each `E_j''(0) ≥ 0`, contradicting the strict negativity — so `ℓ ≤ π r`.  That
final second-variation-and-minimality bridge is the concrete exponential variation
(`prop:dc-ch9-2-2` + `prop:dc-ch9-2-8` for `exp`), still open; this file lands everything else.

The index-form value `indexForm_smul_eq` is surface-free: it is a pointwise multilinear
rewrite of `indexForm` for the field `V = φ·e`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 9, §3, Theorem 3.1 (Bonnet–Myers).
-/

open Set Riemannian intervalIntegral MeasureTheory
open scoped ContDiff Manifold Topology Real

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### A real-analysis lemma: the second-order necessary condition at a minimum -/

/-- **Math.** The **second-order necessary condition**: a function `f : ℝ → ℝ` with a local
minimum at `x`, continuous at `x` and twice differentiable there (`HasDerivAt (deriv f) f'' x`),
has `f''(x) ≥ 0`.  Mathlib has only the *sufficient* converse (`isLocalMax_of_deriv_deriv_neg`);
this necessary direction is proved by contradiction from it: if `f'' < 0` then `x` is also a
local *max*, so `f` is locally constant, its derivative is eventually `0`, and by uniqueness
`f'' = 0` — contradicting `f'' < 0`.

This is the fact that turns "a minimizing geodesic makes each `E_j` minimal at `s = 0`" into
`E_j''(0) ≥ 0` in do Carmo's Bonnet–Myers argument (`thm:dc-ch9-3-1`). -/
theorem isLocalMin_deriv_deriv_nonneg {f : ℝ → ℝ} {x f'' : ℝ}
    (hmin : IsLocalMin f x) (hcont : ContinuousAt f x)
    (hf'' : HasDerivAt (deriv f) f'' x) : 0 ≤ f'' := by
  by_contra h
  rw [not_le] at h
  have hderiv0 : deriv f x = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax f x :=
    isLocalMax_of_deriv_deriv_neg (by rw [hf''.deriv]; exact h) hderiv0 hcont
  -- `IsLocalMin ∧ IsLocalMax` ⟹ `f` is locally constant
  have hconst : f =ᶠ[𝓝 x] fun _ => f x := by
    filter_upwards [hmin, hmax] with y hy1 hy2 using le_antisymm hy2 hy1
  -- hence `deriv f` is eventually `0`
  have hderiv_eq : deriv f =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [hconst.eventuallyEq_nhds] with y hy
    simp [hy.deriv_eq]
  -- `deriv f` therefore has derivative `0` at `x`, forcing `f'' = 0`
  have h0 : HasDerivAt (deriv f) 0 x := (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hderiv_eq
  exact h.ne (hf''.unique h0)

/-! ### The index form of a scaled parallel field `V = φ·e` -/

/-- **Math.** do Carmo Ch. 9, §3.  The **index form of a scaled field** `V(t) = φ(t)·e(t)`,
whose covariant derivative is `V' = φ'·e` (for `e` parallel), unfolds to
$$I_a(V, V) = \int_a^b\Big((\varphi')^2\,\langle e, e\rangle
  - \varphi^2\,\langle R(\gamma', e)\gamma', e\rangle\Big)\,dt.$$
This is a pointwise multilinear rewrite of `indexForm`: pull the scalars `φ'` and `φ` out of the
metric term (bilinearity) and out of the two `e`-slots of the curvature term
(`curvatureFormAt_smul_snd`/`_fth`).  It needs no parallelism or covariant-pair structure — those
enter only when `e` is a parallel *unit* field, making `⟨e, e⟩ = 1`. -/
theorem indexForm_smul_eq (g : RiemannianMetric I M) (γ : ℝ → M) (e : ℝ → E) (φ : ℝ → ℝ)
    (a b : ℝ) :
    indexForm (I := I) g γ (fun t => φ t • e t) (fun t => deriv φ t • e t) a b
      = ∫ t in a..b, ((deriv φ t) ^ 2 * g.metricInner (γ t) (e t : TangentSpace I (γ t)) (e t)
          - (φ t) ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
              (DCVelocity (I := I) γ t) (e t) (DCVelocity (I := I) γ t) (e t)) := by
  rw [indexForm_def]
  refine intervalIntegral.integral_congr (fun t _ => ?_)
  rw [g.metricInner_smul_left, g.metricInner_smul_right,
    curvatureFormAt_smul_snd, curvatureFormAt_smul_fth]
  ring

/-- **Math.** do Carmo Ch. 9, §3, the index form of `V_j = φ·e_j` **evaluated in the
velocity-seeded frame**: if `e` is a `g`-unit field and `γ' = ℓ·e_n` (the frame's distinguished
member, `ℓ = |γ'|`), then
$$I_a(V, V) = \int_a^b\Big((\varphi')^2 - \varphi^2\,\ell^2\,\langle R(e_n, e)e_n, e\rangle\Big)\,dt.$$
The `⟨e, e⟩` factor becomes `1` (orthonormality), and the velocity is pulled out of the two
`γ'`-slots of the curvature term (`γ' = ℓ·e_n`, homogeneity in slots 1 and 3), leaving
`ℓ²⟨R(e_n, e)e_n, e⟩`.  Surface-free: only `indexForm_smul_eq` and multilinearity.  This is do
Carmo's `\sin^2\pi t\,(\pi^2 - \ell^2 K(e_n, e_j))` integrand, with `⟨R(e_n, e)e_n, e⟩` the bare
curvature-form numerator (equal to the sectional curvature `K(e_n, e)` when `e_n ⟂ e` are
orthonormal). -/
theorem indexForm_smul_frame_eq (g : RiemannianMetric I M) (γ : ℝ → M)
    (e en : ℝ → E) (φ : ℝ → ℝ) (ℓ : ℝ) {a b : ℝ} (hab : a ≤ b)
    (hunit : ∀ t ∈ Set.Icc a b, g.metricInner (γ t) (e t : TangentSpace I (γ t)) (e t) = 1)
    (hvel : ∀ t ∈ Set.Icc a b,
      DCVelocity (I := I) γ t = (ℓ • en t : TangentSpace I (γ t))) :
    indexForm (I := I) g γ (fun t => φ t • e t) (fun t => deriv φ t • e t) a b
      = ∫ t in a..b, ((deriv φ t) ^ 2
          - (φ t) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
              (en t) (e t) (en t) (e t))) := by
  rw [indexForm_smul_eq]
  refine intervalIntegral.integral_congr (fun t ht => ?_)
  rw [Set.uIcc_of_le hab] at ht
  rw [hunit t ht, hvel t ht, curvatureFormAt_smul_fst, curvatureFormAt_smul_trd]
  ring

/-! ### do Carmo's contradiction: the summed index form is negative -/

/-- **Math.** The **pure real-analysis core** of do Carmo's Bonnet–Myers contradiction: for any
real `A` and any function `S` continuous on `[0, 1]` with `S(t) > A\pi^2` throughout,
$$\int_0^1\Big(A\,(\pi\cos\pi t)^2 - (\sin\pi t)^2\,S(t)\Big)\,dt < 0.$$
Writing the integrand as `A\pi^2\cos(2\pi t) - (\sin\pi t)^2(S(t) - A\pi^2)`, the first part
integrates to `0` (`∫_0^1 cos(2π t) dt = 0`) and the second is the integral of a function that is
`\ge 0` on `[0,1]` and strictly positive on `(0,1)` (where `\sin\pi t > 0` and `S(t) - A\pi^2 > 0`),
hence strictly positive.  In do Carmo's Bonnet–Myers argument `A = n - 1` and
`S(t) = \ell^2\,\mathrm{Ric}_{\gamma(t)}` — see `sum_indexForm_smul_frame_neg`. -/
theorem integral_frame_sum_lt_zero (A : ℝ) (S : ℝ → ℝ)
    (hScont : ContinuousOn S (Set.Icc 0 1))
    (hS : ∀ t ∈ Set.Icc (0 : ℝ) 1, A * Real.pi ^ 2 < S t) :
    ∫ t in (0 : ℝ)..1,
        (A * (Real.pi * Real.cos (Real.pi * t)) ^ 2 - (Real.sin (Real.pi * t)) ^ 2 * S t) < 0 := by
  have hSuIcc : ContinuousOn S (Set.uIcc (0 : ℝ) 1) := by rwa [Set.uIcc_of_le (by norm_num)]
  set f1 : ℝ → ℝ := fun t => A * Real.pi ^ 2 * Real.cos (2 * Real.pi * t) with hf1
  set f2 : ℝ → ℝ := fun t => (Real.sin (Real.pi * t)) ^ 2 * (S t - A * Real.pi ^ 2) with hf2
  have key : Set.EqOn
      (fun t => A * (Real.pi * Real.cos (Real.pi * t)) ^ 2 - (Real.sin (Real.pi * t)) ^ 2 * S t)
      (fun t => f1 t - f2 t) (Set.uIcc (0 : ℝ) 1) := by
    intro t _
    simp only [hf1, hf2]
    have hc2 : Real.cos (2 * Real.pi * t)
        = Real.cos (Real.pi * t) ^ 2 - Real.sin (Real.pi * t) ^ 2 := by
      rw [show 2 * Real.pi * t = (Real.pi * t) + (Real.pi * t) by ring, Real.cos_add]; ring
    rw [hc2]; ring
  rw [intervalIntegral.integral_congr key]
  have hf1int : IntervalIntegrable f1 volume 0 1 := by
    apply Continuous.intervalIntegrable; simp only [hf1]; fun_prop
  have hf2int : IntervalIntegrable f2 volume 0 1 := by
    apply ContinuousOn.intervalIntegrable; simp only [hf2]
    exact (Continuous.continuousOn (by fun_prop)).mul (hSuIcc.sub continuousOn_const)
  rw [intervalIntegral.integral_sub hf1int hf2int]
  have hint1 : ∫ t in (0 : ℝ)..1, f1 t = 0 := by
    simp only [hf1]; rw [intervalIntegral.integral_const_mul]
    have hcos0 : ∫ t in (0 : ℝ)..1, Real.cos (2 * Real.pi * t) = 0 := by
      have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.sin (2 * Real.pi * t) / (2 * Real.pi))
          (Real.cos (2 * Real.pi * t)) t := by
        intro t
        have h2pi : (2 * Real.pi) ≠ 0 := by positivity
        have h := ((Real.hasDerivAt_sin (2 * Real.pi * t)).comp t
          ((hasDerivAt_id t).const_mul (2 * Real.pi))).div_const (2 * Real.pi)
        simpa [mul_comm, mul_div_assoc, mul_div_cancel_left₀, h2pi] using h
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
        (by apply Continuous.intervalIntegrable; fun_prop)]
      have e1 : (2 : ℝ) * Real.pi * 1 = 2 * Real.pi := by ring
      have e0 : (2 : ℝ) * Real.pi * 0 = 0 := by ring
      rw [e1, e0, Real.sin_two_pi, Real.sin_zero]; ring
    rw [hcos0]; ring
  rw [hint1]
  have hint2 : 0 < ∫ t in (0 : ℝ)..1, f2 t := by
    apply intervalIntegral_pos_of_pos_on hf2int _ (by norm_num)
    intro t ht
    simp only [hf2]
    apply mul_pos
    · have hsin : 0 < Real.sin (Real.pi * t) :=
        Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1)
          (by calc Real.pi * t < Real.pi * 1 := mul_lt_mul_of_pos_left ht.2 Real.pi_pos
                _ = Real.pi := mul_one _)
      positivity
    · have := hS t ⟨le_of_lt ht.1, le_of_lt ht.2⟩; linarith
  linarith

/-- **Math.** do Carmo Ch. 9, §3, the heart of the Bonnet–Myers contradiction
(`thm:dc-ch9-3-1`): **the sum of the index forms is strictly negative.**  For fields `e_j` along
`γ : [0, 1] → M` with each `e_j` (`j ≠ n₀`) a `g`-unit field (`hunit`) and velocity
`γ' = ℓ·e_{n₀}` (`hvel`) — in the intended application `e` is the velocity-seeded parallel
orthonormal frame of `exists_velocitySeededParallelOrthoFrameAlongOn`, of which the proof uses
only these two conditions (`e_{n₀}` need not be unit, and no orthogonality among the `e_j` is
assumed) — and with `V_j(t) = (\sin\pi t)\,e_j(t)` and `n ≥ 2` (`hne`: some `j ≠ n₀`),
$$\sum_{j\ne n_0} I_a(V_j, V_j) < 0 \qquad\text{whenever } \pi r < \ell,\ r > 0,$$
provided the raw curvature sum (do Carmo's unnormalized Ricci `Q(e_{n₀}, e_{n₀})`) is bounded
below by `(n-1)/r²` at every `t`.  This packages do Carmo's steps "summing on `j` and using the
definition of Ricci curvature ⇒ `½Σ E_j''(0) < 0`": each summand is `indexForm_smul_frame_eq`
with `φ = \sin\pi t`, and the total integrates to
`∫_0^1 ((n-1)(\pi\cos\pi t)^2 - (\sin\pi t)^2\,\ell^2\,Q)\,dt`, which `integral_frame_sum_lt_zero`
sends below zero because `\ell^2\,Q \ge \ell^2 (n-1)/r^2 > (n-1)\pi^2` when `\ell > \pi r`.

The curvature hypotheses are stated with the raw curvature sum
`∑_{j≠n₀} \langle R(e_{n₀}, e_j)e_{n₀}, e_j\rangle` rather than through `ricciForm`; that sum
equals the unnormalized Ricci form `Q(e_{n₀}, e_{n₀})` by
`ricciForm_self_eq_sum_sectionalCurvature` (`lem:dc-ch9-3-3-ricci-sectional`, for an orthonormal
basis at each `γ(t)`), so `hRic` is do Carmo's `Ric ≥ 1/r²` after clearing the `n-1`
normalization.  Continuity of each curvature term (`hCcont`) holds because the curvature form is
smooth and `γ`, `e` are (piecewise) differentiable; it is taken as a hypothesis here, matching this
chapter's discipline of carrying the analytic side conditions explicitly.

By formula (6) (`lem:dc-ch9-2-10-formula6`) each `I_a(V_j, V_j) = ½E_j''(0)` for the concrete
proper variation with variational field `V_j`; combined with `isLocalMin_deriv_deriv_nonneg`
(a minimizing `γ` forces `E_j''(0) ≥ 0`) this contradicts the strict negativity, giving
`ℓ ≤ π r`.  That last bridge is the concrete exponential variation (`prop:dc-ch9-2-2` +
`prop:dc-ch9-2-8` for `exp`), still open — this lemma is everything up to it. -/
theorem sum_indexForm_smul_frame_neg (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)) (ℓ r : ℝ)
    (hr : 0 < r) (hℓr : Real.pi * r < ℓ)
    (hne : (Finset.univ.erase n₀).Nonempty)
    (hunit : ∀ j ∈ Finset.univ.erase n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e j t) = 1)
    (hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DCVelocity (I := I) γ t = (ℓ • e n₀ t : TangentSpace I (γ t)))
    (hCcont : ∀ j ∈ Finset.univ.erase n₀,
      ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
        (e n₀ t) (e j t) (e n₀ t) (e j t)) (Set.Icc 0 1))
    (hRic : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((Finset.univ.erase n₀).card : ℝ) / r ^ 2 ≤
        ∑ j ∈ Finset.univ.erase n₀, g.leviCivitaConnection.curvatureFormAt g (γ t)
          (e n₀ t) (e j t) (e n₀ t) (e j t)) :
    ∑ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1 < 0 := by
  classical
  have hderiv : deriv (fun t : ℝ => Real.sin (Real.pi * t))
      = fun t => Real.pi * Real.cos (Real.pi * t) := by
    funext t
    have h : HasDerivAt (fun t : ℝ => Real.sin (Real.pi * t))
        (Real.cos (Real.pi * t) * Real.pi) t := by
      simpa using (Real.hasDerivAt_sin (Real.pi * t)).comp t ((hasDerivAt_id t).const_mul Real.pi)
    rw [h.deriv]; ring
  -- step 1: rewrite each index form via the frame formula, with `deriv (sin π·) = π cos π·`
  have step1 : ∀ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1
      = ∫ t in (0 : ℝ)..1, ((Real.pi * Real.cos (Real.pi * t)) ^ 2
          - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
              (e n₀ t) (e j t) (e n₀ t) (e j t))) := by
    intro j hj
    rw [indexForm_smul_frame_eq g γ (e j) (e n₀) (fun t => Real.sin (Real.pi * t)) ℓ
      (by norm_num) (hunit j hj) hvel]
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hderiv]
  rw [Finset.sum_congr rfl step1]
  -- step 2: swap the finite sum with the integral
  have hint : ∀ j ∈ Finset.univ.erase n₀, IntervalIntegrable
      (fun t => (Real.pi * Real.cos (Real.pi * t)) ^ 2
        - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
            (e n₀ t) (e j t) (e n₀ t) (e j t))) volume 0 1 := by
    intro j hj
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    refine (Continuous.continuousOn (by fun_prop)).sub (ContinuousOn.mul
      (Continuous.continuousOn (by fun_prop)) (continuousOn_const.mul (hCcont j hj)))
  rw [← intervalIntegral.integral_finsetSum hint]
  -- step 3: collapse the summand to `(n-1)(π cos)² − (sin)²·(ℓ²·∑ Q)`
  have hcombine : Set.EqOn
      (fun t => ∑ j ∈ Finset.univ.erase n₀, ((Real.pi * Real.cos (Real.pi * t)) ^ 2
        - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * g.leviCivitaConnection.curvatureFormAt g (γ t)
            (e n₀ t) (e j t) (e n₀ t) (e j t))))
      (fun t => ((Finset.univ.erase n₀).card : ℝ) * (Real.pi * Real.cos (Real.pi * t)) ^ 2
        - (Real.sin (Real.pi * t)) ^ 2 * (ℓ ^ 2 * ∑ j ∈ Finset.univ.erase n₀,
            g.leviCivitaConnection.curvatureFormAt g (γ t) (e n₀ t) (e j t) (e n₀ t) (e j t)))
      (Set.uIcc (0 : ℝ) 1) := by
    intro t _
    dsimp only
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [intervalIntegral.integral_congr hcombine]
  -- step 4: the arithmetic core
  refine integral_frame_sum_lt_zero _ _ ?_ ?_
  · exact continuousOn_const.mul (continuousOn_finsetSum _ (fun j hj => hCcont j hj))
  · intro t ht
    have hcard : 0 < ((Finset.univ.erase n₀).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hr2 : (0 : ℝ) < r ^ 2 := by positivity
    have hRt := hRic t ht
    rw [div_le_iff₀ hr2] at hRt
    have hπr' : Real.pi ^ 2 * r ^ 2 < ℓ ^ 2 := by nlinarith [hℓr, mul_pos Real.pi_pos hr]
    have hsum_pos : 0 < ∑ j ∈ Finset.univ.erase n₀,
        g.leviCivitaConnection.curvatureFormAt g (γ t) (e n₀ t) (e j t) (e n₀ t) (e j t) := by
      nlinarith [hRt, hcard, hr2]
    nlinarith [hRt, hπr', hsum_pos, sq_nonneg Real.pi]

/-- **Math.** do Carmo Ch. 9, §3, the immediate consequence of `sum_indexForm_smul_frame_neg`:
**some** `V_j = (\sin\pi t)\,e_j` has strictly negative index form.  A strictly negative finite
sum has a strictly negative summand.  This is the field do Carmo picks to derive
`E_j''(0) < 0`, contradicting the minimality of `γ` via formula (6) and
`isLocalMin_deriv_deriv_nonneg`. -/
theorem exists_indexForm_smul_frame_neg (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)) (ℓ r : ℝ)
    (hr : 0 < r) (hℓr : Real.pi * r < ℓ)
    (hne : (Finset.univ.erase n₀).Nonempty)
    (hunit : ∀ j ∈ Finset.univ.erase n₀, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e j t) = 1)
    (hvel : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      DCVelocity (I := I) γ t = (ℓ • e n₀ t : TangentSpace I (γ t)))
    (hCcont : ∀ j ∈ Finset.univ.erase n₀,
      ContinuousOn (fun t => g.leviCivitaConnection.curvatureFormAt g (γ t)
        (e n₀ t) (e j t) (e n₀ t) (e j t)) (Set.Icc 0 1))
    (hRic : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ((Finset.univ.erase n₀).card : ℝ) / r ^ 2 ≤
        ∑ j ∈ Finset.univ.erase n₀, g.leviCivitaConnection.curvatureFormAt g (γ t)
          (e n₀ t) (e j t) (e n₀ t) (e j t)) :
    ∃ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1 < 0 := by
  have hlt : ∑ j ∈ Finset.univ.erase n₀,
      indexForm (I := I) g γ (fun t => Real.sin (Real.pi * t) • e j t)
        (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1
      < ∑ _j ∈ Finset.univ.erase n₀, (0 : ℝ) := by
    rw [Finset.sum_const_zero]
    exact sum_indexForm_smul_frame_neg g γ e n₀ ℓ r hr hℓr hne hunit hvel hCcont hRic
  exact Finset.exists_lt_of_sum_lt hlt

end Riemannian.Variation

end

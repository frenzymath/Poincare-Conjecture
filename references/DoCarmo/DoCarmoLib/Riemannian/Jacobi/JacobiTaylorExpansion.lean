import DoCarmoLib.Riemannian.Jacobi.JacobiField
import Mathlib.Analysis.Calculus.Taylor

/-!
# do Carmo Ch. 5, §2, Proposition 2.7 — the Taylor expansion of `|J(t)|²`

For a Jacobi field `J` along a geodesic `γ` with `J(0) = 0`, `J'(0) = w`, do Carmo proves
the fourth-order Taylor expansion (his equation (3))

  `|J(t)|² = |w|²·t² − (1/3)·⟨R(v, w)v, w⟩·t⁴ + R(t)`,   `R(t)/t⁴ → 0`,

where `v = γ'(0)`.  do Carmo's proof needs the auxiliary identity (his (4))
`∇_{γ'}(R(γ', J)γ')(0) = R(γ', J')γ'(0)`, whose proof uses the covariant derivative of the
curvature tensor.  **In a parallel orthonormal frame `e₁,…,eₙ` along `γ` this identity is
automatic**: writing `J = Σᵢ fᵢ eᵢ`, the frame is parallel so `D^k J/dt^k = Σᵢ fᵢ^{(k)} eᵢ`,
the metric becomes Euclidean, `|J(t)|² = Σᵢ fᵢ(t)² = ‖f(t)‖²`, and the Jacobi equation is the
plain second-order linear ODE `f'' = −A(t) f` with `A(t) = (⟨R(γ', eᵢ)γ', eⱼ⟩)` the frame
curvature.  do Carmo's `∇R`-identity collapses to the elementary fact that, since `f(0) = 0`,
the `A'` terms drop out at `t = 0`.

This file develops that **analytic heart** abstractly, over any real inner product space `E`:
for the ODE `f' = v`, `v' = −A(t) f` with smooth coefficient `A` and `f(0) = 0`, the scalar
`g(t) = ⟨f(t), f(t)⟩ = ‖f(t)‖²` has

  `g(t) = ‖v(0)‖²·t² − (1/3)·⟨v(0), A(0) v(0)⟩·t⁴ + o(t⁴)`.

The four Taylor coefficients are `g(0) = 0`, `g'(0) = 0`, `g''(0) = 2‖v0‖²`, `g'''(0) = 0`,
`g''''(0) = −8⟨v0, A(0) v0⟩`, computed by an explicit `HasDerivAt` chain, and the little-`o`
remainder is `taylor_isLittleO`.  The frame identification
`⟨v0, A(0) v0⟩ = ⟨R(γ', w)γ', w⟩ = ⟨R(v, w)v, w⟩` (`aᵢⱼ = ⟨R(γ', eᵢ)γ', eⱼ⟩`) then closes
`prop:dc-ch5-2-7`; `cor:dc-ch5-2-9` reads the coefficient as the sectional curvature and
`cor:dc-ch5-2-10` takes the square root.

Blueprint: `lem:dc-ch5-2-7-taylor-ode` (this file's analytic heart), `prop:dc-ch5-2-7`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Proposition 2.7.
-/

open Set Filter
open scoped Topology InnerProductSpace ContDiff

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## The four derivatives of `g(t) = ⟨f(t), f(t)⟩` along the Jacobi ODE -/

section AbstractODE

variable {A : ℝ → E →L[ℝ] E} {f v : ℝ → E}

/-- **Math.** `g(t) = ⟨f(t), f(t)⟩ = ‖f(t)‖²`, the squared norm of the Jacobi field. -/
abbrev gg0 (f : ℝ → E) : ℝ → ℝ := fun t => ⟪f t, f t⟫_ℝ

/-- **Math.** First derivative `g'(t) = 2⟨f(t), v(t)⟩` (metric compatibility, `f' = v`). -/
abbrev gg1 (f v : ℝ → E) : ℝ → ℝ := fun t => 2 * ⟪f t, v t⟫_ℝ

/-- **Math.** Second derivative `g''(t) = 2⟨v, v⟩ − 2⟨f, A f⟩` (using `v' = −A f`). -/
abbrev gg2 (A : ℝ → E →L[ℝ] E) (f v : ℝ → E) : ℝ → ℝ :=
  fun t => 2 * ⟪v t, v t⟫_ℝ - 2 * ⟪f t, A t (f t)⟫_ℝ

/-- **Math.** Third derivative `g'''(t) = −6⟨v, A f⟩ − 2⟨f, A' f⟩ − 2⟨f, A v⟩`. -/
abbrev gg3 (A : ℝ → E →L[ℝ] E) (f v : ℝ → E) : ℝ → ℝ :=
  fun t => -6 * ⟪v t, A t (f t)⟫_ℝ - 2 * ⟪f t, (deriv A t) (f t)⟫_ℝ - 2 * ⟪f t, A t (v t)⟫_ℝ

/-- **Math.** `g' = g₁`: `d/dt ⟨f, f⟩ = 2⟨f, v⟩`. (Stated pointwise so it is usable when `f`
solves the Jacobi ODE only on an open time interval.) -/
theorem hasDerivAt_gg0 {t : ℝ} (hfvt : HasDerivAt f (v t) t) :
    HasDerivAt (gg0 f) (gg1 f v t) t := by
  have h := hfvt.inner ℝ hfvt
  -- `d⟨f,f⟩ = ⟨f, v⟩ + ⟨v, f⟩ = 2⟨f, v⟩`
  have hcomm : ⟪f t, v t⟫_ℝ + ⟪v t, f t⟫_ℝ = 2 * ⟪f t, v t⟫_ℝ := by
    rw [real_inner_comm (v t) (f t)]; ring
  rw [hcomm] at h
  exact h

/-- **Math.** `g'' = g₂`: differentiating `2⟨f, v⟩` with `f' = v`, `v' = −A f`. -/
theorem hasDerivAt_gg1 {t : ℝ} (hfvt : HasDerivAt f (v t) t)
    (hvAt : HasDerivAt v (-(A t) (f t)) t) :
    HasDerivAt (gg1 f v) (gg2 A f v t) t := by
  have h := (hfvt.inner ℝ hvAt).const_mul (2 : ℝ)
  -- `h : HasDerivAt (fun t => 2 * ⟨f, v⟩) (2 * (⟨f, −A f⟩ + ⟨v, v⟩)) t`
  have hval : 2 * (⟪f t, -(A t) (f t)⟫_ℝ + ⟪v t, v t⟫_ℝ) = gg2 A f v t := by
    simp only [gg2, inner_neg_right]; ring
  rw [hval] at h
  exact h

/-- **Math.** `g''' = g₃`: differentiating `2⟨v, v⟩ − 2⟨f, A f⟩`, using `(A f)' = A' f + A v`. -/
theorem hasDerivAt_gg2 {t : ℝ} (hfvt : HasDerivAt f (v t) t)
    (hvAt : HasDerivAt v (-(A t) (f t)) t) (hAdt : HasDerivAt A (deriv A t) t) :
    HasDerivAt (gg2 A f v) (gg3 A f v t) t := by
  -- derivative of `2⟨v, v⟩`
  have hvv := (hvAt.inner ℝ hvAt).const_mul (2 : ℝ)
  -- derivative of `p = A f`
  have hp : HasDerivAt (fun s => A s (f s)) ((deriv A t) (f t) + A t (v t)) t :=
    hAdt.clm_apply hfvt
  -- derivative of `2⟨f, A f⟩`
  have hfp := (hfvt.inner ℝ hp).const_mul (2 : ℝ)
  have h := hvv.sub hfp
  have hval : gg3 A f v t
      = 2 * (⟪v t, -(A t) (f t)⟫_ℝ + ⟪-(A t) (f t), v t⟫_ℝ)
        - 2 * (⟪f t, (deriv A t) (f t) + A t (v t)⟫_ℝ + ⟪v t, A t (f t)⟫_ℝ) := by
    simp only [gg3, inner_neg_right, inner_neg_left, inner_add_right,
      real_inner_comm (A t (f t)) (v t)]
    ring
  rw [hval]
  exact h

/-- **Math.** `g''''(0) = −8⟨v(0), A(0) v(0)⟩`. This is where `f(0) = 0` does the work of do
Carmo's identity (4): every term of `g'''` carrying a factor of `f` (in particular the `A'`
terms) vanishes at `0`, leaving `−6⟨w, A(0)w⟩ − 0 − 2⟨w, A(0)w⟩`. -/
theorem hasDerivAt_gg3_zero (hfv0 : HasDerivAt f (v 0) 0)
    (hvA0 : HasDerivAt v (-(A 0) (f 0)) 0) (hAd0 : HasDerivAt A (deriv A 0) 0)
    (hAd2_0 : HasDerivAt (deriv A) (deriv (deriv A) 0) 0) (hf0 : f 0 = 0) :
    HasDerivAt (gg3 A f v) (-8 * ⟪v 0, A 0 (v 0)⟫_ℝ) 0 := by
  -- the inner constituents `A f`, `A' f`, `A v` and their derivatives at `0`
  have hq : HasDerivAt (fun s => A s (f s)) ((deriv A 0) (f 0) + A 0 (v 0)) 0 :=
    hAd0.clm_apply hfv0
  have hr : HasDerivAt (fun s => (deriv A s) (f s))
      ((deriv (deriv A) 0) (f 0) + (deriv A 0) (v 0)) 0 :=
    hAd2_0.clm_apply hfv0
  have hs : HasDerivAt (fun s => A s (v s)) ((deriv A 0) (v 0) + A 0 (-(A 0) (f 0))) 0 :=
    hAd0.clm_apply hvA0
  -- the three terms of `g'''`
  have hT1 := (hvA0.inner ℝ hq).const_mul (-6 : ℝ)
  have hT2 := (hfv0.inner ℝ hr).const_mul (2 : ℝ)
  have hT3 := (hfv0.inner ℝ hs).const_mul (2 : ℝ)
  have h := (hT1.sub hT2).sub hT3
  convert h using 1 <;> try rfl
  simp only [hf0, map_zero, neg_zero, inner_zero_left, inner_zero_right, add_zero, zero_add,
    mul_zero]
  ring

/-! ## The Taylor expansion of `g(t) = ‖f(t)‖²` -/

/-- **Math.** **do Carmo Ch. 5, Proposition 2.7 — the analytic heart (`lem:dc-ch5-2-7-taylor-ode`).**
Let `f' = v`, `v' = −A(t) f` be the Jacobi ODE in a parallel orthonormal frame (so
`g(t) = ⟨f(t), f(t)⟩ = ‖f(t)‖²`), with smooth coefficient `A` and initial value `f(0) = 0`.
Writing `w = v(0) = J'(0)`, the squared norm has the fourth-order Taylor expansion

  `⟨f(t), f(t)⟩ = ⟨w, w⟩·t² − (1/3)·⟨w, A(0) w⟩·t⁴ + o(t⁴)`.

The four coefficients `g(0) = g'(0) = g'''(0) = 0`, `g''(0) = 2⟨w, w⟩`, `g''''(0) = −8⟨w, A(0)w⟩`
are computed by the explicit `HasDerivAt` chain `gg0 → gg1 → gg2 → gg3`; the remainder is
`taylor_isLittleO`.  Substituting the frame curvature `A(0)` via `⟨w, A(0)w⟩ = ⟨R(v, w)v, w⟩`
gives do Carmo's `|J(t)|² = |w|²t² − (1/3)⟨R(v,w)v,w⟩t⁴ + R(t)`, `R(t)/t⁴ → 0`. -/
theorem norm_sq_jacobi_isLittleO {A : ℝ → E →L[ℝ] E} {f v : ℝ → E}
    (hf : ContDiff ℝ ∞ f) (hA : ContDiff ℝ ∞ A)
    (hfv : ∀ t, HasDerivAt f (v t) t) (hvA : ∀ t, HasDerivAt v (-(A t) (f t)) t)
    (hf0 : f 0 = 0) :
    (fun t => ⟪f t, f t⟫_ℝ - (⟪v 0, v 0⟫_ℝ * t ^ 2 - (1 / 3) * ⟪v 0, A 0 (v 0)⟫_ℝ * t ^ 4))
      =o[𝓝 (0 : ℝ)] fun t => t ^ 4 := by
  -- smoothness of `A` and `deriv A`
  have hAd : ∀ s, HasDerivAt A (deriv A s) s := fun s =>
    (hA.differentiable (by simp)).differentiableAt.hasDerivAt
  have hderivA : ContDiff ℝ ∞ (deriv A) := (contDiff_infty_iff_deriv.mp hA).2
  have hAd2 : ∀ s, HasDerivAt (deriv A) (deriv (deriv A) s) s := fun s =>
    (hderivA.differentiable (by simp)).differentiableAt.hasDerivAt
  -- the derivative chain `deriv (gg_k) = gg_{k+1}`
  have h01 : deriv (gg0 f) = gg1 f v := funext fun t => (hasDerivAt_gg0 (hfv t)).deriv
  have h12 : deriv (gg1 f v) = gg2 A f v := funext fun t => (hasDerivAt_gg1 (hfv t) (hvA t)).deriv
  have h23 : deriv (gg2 A f v) = gg3 A f v :=
    funext fun t => (hasDerivAt_gg2 (hfv t) (hvA t) (hAd t)).deriv
  -- the five iterated derivatives at `0`
  have e0 : iteratedDeriv 0 (gg0 f) 0 = 0 := by
    rw [iteratedDeriv_zero]; simp [gg0, hf0]
  have e1 : iteratedDeriv 1 (gg0 f) 0 = 0 := by
    have hchain : iteratedDeriv 1 (gg0 f) = gg1 f v :=
      calc iteratedDeriv 1 (gg0 f) = iteratedDeriv 0 (deriv (gg0 f)) := iteratedDeriv_succ'
        _ = deriv (gg0 f) := iteratedDeriv_zero
        _ = gg1 f v := h01
    rw [hchain]; simp [gg1, hf0]
  have e2 : iteratedDeriv 2 (gg0 f) 0 = 2 * ⟪v 0, v 0⟫_ℝ := by
    have hchain : iteratedDeriv 2 (gg0 f) = gg2 A f v :=
      calc iteratedDeriv 2 (gg0 f) = iteratedDeriv 1 (deriv (gg0 f)) := iteratedDeriv_succ'
        _ = iteratedDeriv 1 (gg1 f v) := by rw [h01]
        _ = iteratedDeriv 0 (deriv (gg1 f v)) := iteratedDeriv_succ'
        _ = deriv (gg1 f v) := iteratedDeriv_zero
        _ = gg2 A f v := h12
    rw [hchain]; simp only [gg2, hf0, map_zero, inner_zero_left, mul_zero, sub_zero]
  have e3 : iteratedDeriv 3 (gg0 f) 0 = 0 := by
    have hchain : iteratedDeriv 3 (gg0 f) = gg3 A f v :=
      calc iteratedDeriv 3 (gg0 f) = iteratedDeriv 2 (deriv (gg0 f)) := iteratedDeriv_succ'
        _ = iteratedDeriv 2 (gg1 f v) := by rw [h01]
        _ = iteratedDeriv 1 (deriv (gg1 f v)) := iteratedDeriv_succ'
        _ = iteratedDeriv 1 (gg2 A f v) := by rw [h12]
        _ = iteratedDeriv 0 (deriv (gg2 A f v)) := iteratedDeriv_succ'
        _ = deriv (gg2 A f v) := iteratedDeriv_zero
        _ = gg3 A f v := h23
    rw [hchain]; simp [gg3, hf0]
  have e4 : iteratedDeriv 4 (gg0 f) 0 = -8 * ⟪v 0, A 0 (v 0)⟫_ℝ := by
    have hchain : iteratedDeriv 4 (gg0 f) = deriv (gg3 A f v) :=
      calc iteratedDeriv 4 (gg0 f) = iteratedDeriv 3 (deriv (gg0 f)) := iteratedDeriv_succ'
        _ = iteratedDeriv 3 (gg1 f v) := by rw [h01]
        _ = iteratedDeriv 2 (deriv (gg1 f v)) := iteratedDeriv_succ'
        _ = iteratedDeriv 2 (gg2 A f v) := by rw [h12]
        _ = iteratedDeriv 1 (deriv (gg2 A f v)) := iteratedDeriv_succ'
        _ = iteratedDeriv 1 (gg3 A f v) := by rw [h23]
        _ = iteratedDeriv 0 (deriv (gg3 A f v)) := iteratedDeriv_succ'
        _ = deriv (gg3 A f v) := iteratedDeriv_zero
    rw [hchain, (hasDerivAt_gg3_zero (hfv 0) (hvA 0) (hAd 0) (hAd2 0) hf0).deriv]
  -- the Taylor polynomial of degree 4
  have hpoly : ∀ t : ℝ, taylorWithinEval (gg0 f) 4 univ 0 t
      = ⟪v 0, v 0⟫_ℝ * t ^ 2 - (1 / 3) * ⟪v 0, A 0 (v 0)⟫_ℝ * t ^ 4 := by
    intro t
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, iteratedDerivWithin_univ,
      e0, e1, e2, e3, e4, sub_zero, smul_eq_mul, Nat.factorial]
    norm_num
    ring
  -- assemble via `taylor_isLittleO`
  have hgcd : ContDiff ℝ ∞ (gg0 f) := hf.inner ℝ hf
  have htay := taylor_isLittleO (f := gg0 f) (n := 4) convex_univ (mem_univ (0 : ℝ))
    (hgcd.of_le (by norm_cast)).contDiffOn
  rw [nhdsWithin_univ] at htay
  have hEqR : (fun x : ℝ => (x - 0) ^ 4) = fun x => x ^ 4 := by funext x; rw [sub_zero]
  rw [hEqR] at htay
  have hEqL : (fun t => ⟪f t, f t⟫_ℝ
        - (⟪v 0, v 0⟫_ℝ * t ^ 2 - (1 / 3) * ⟪v 0, A 0 (v 0)⟫_ℝ * t ^ 4))
      = fun x => gg0 f x - taylorWithinEval (gg0 f) 4 univ 0 x := by
    funext t; rw [hpoly t]
  rw [hEqL]
  exact htay

/-- **Math.** **do Carmo Ch. 5, Proposition 2.7 — the analytic heart, local form.**  Same Taylor
expansion as `norm_sq_jacobi_isLittleO`, but with the Jacobi ODE data required to be smooth and to
solve the equation only on an **open interval** `s ∋ 0`, rather than on all of `ℝ`.  This is the
form the manifold instantiation needs: the geodesic `t ↦ exp_p(t v)` and its parallel frame are
smooth only on the open time interval where the geodesic stays in a fixed chart around `p`, so the
frame coefficient `f`, its velocity `v`, and the frame curvature `A` are only `ContDiffOn ℝ ∞ · s`
and satisfy `f' = v`, `v' = −A f` only for `t ∈ s`.  The little-`o` is at `𝓝 0`, which only sees a
neighbourhood of `0`, so the open-interval hypotheses suffice.

The proof reuses the pointwise derivative chain `gg0 → gg1 → gg2 → gg3`, computes the five Taylor
coefficients at `0` through `iteratedDeriv` germ-congruence (`EventuallyEq.iteratedDeriv_eq`,
valid since the chain identities hold on `s ∈ 𝓝 0`), and applies `taylor_isLittleO` on the convex
open set `s` (`iteratedDerivWithin` collapses to `iteratedDeriv` on the open `s`). -/
theorem norm_sq_jacobi_isLittleO_local {A : ℝ → E →L[ℝ] E} {f v : ℝ → E} {s : Set ℝ}
    (hs_open : IsOpen s) (hs_conv : Convex ℝ s) (hs0 : (0 : ℝ) ∈ s)
    (hf : ContDiffOn ℝ ∞ f s) (hA : ContDiffOn ℝ ∞ A s)
    (hfv : ∀ t ∈ s, HasDerivAt f (v t) t) (hvA : ∀ t ∈ s, HasDerivAt v (-(A t) (f t)) t)
    (hf0 : f 0 = 0) :
    (fun t => ⟪f t, f t⟫_ℝ - (⟪v 0, v 0⟫_ℝ * t ^ 2 - (1 / 3) * ⟪v 0, A 0 (v 0)⟫_ℝ * t ^ 4))
      =o[𝓝 (0 : ℝ)] fun t => t ^ 4 := by
  -- smoothness of `A` and `deriv A` on the open set, and the pointwise derivatives they give
  have hderivA : ContDiffOn ℝ ∞ (deriv A) s := by
    have h : ContDiffOn ℝ ∞ (derivWithin A s) s := hA.derivWithin hs_open.uniqueDiffOn (by simp)
    rwa [contDiffOn_congr (fun x hx => (derivWithin_of_isOpen hs_open hx))] at h
  have hAd : ∀ t ∈ s, HasDerivAt A (deriv A t) t := fun t ht =>
    ((hA.differentiableOn (by simp)).differentiableAt (hs_open.mem_nhds ht)).hasDerivAt
  have hAd2_0 : HasDerivAt (deriv A) (deriv (deriv A) 0) 0 :=
    ((hderivA.differentiableOn (by simp)).differentiableAt (hs_open.mem_nhds hs0)).hasDerivAt
  have hsnhds : s ∈ 𝓝 (0 : ℝ) := hs_open.mem_nhds hs0
  -- the derivative chain, holding on the open set `s`, hence eventually at `𝓝 0`
  have hd01 : deriv (gg0 f) =ᶠ[𝓝 0] gg1 f v :=
    eventuallyEq_of_mem hsnhds (fun t ht => (hasDerivAt_gg0 (hfv t ht)).deriv)
  have hd12 : deriv (gg1 f v) =ᶠ[𝓝 0] gg2 A f v :=
    eventuallyEq_of_mem hsnhds (fun t ht => (hasDerivAt_gg1 (hfv t ht) (hvA t ht)).deriv)
  have hd23 : deriv (gg2 A f v) =ᶠ[𝓝 0] gg3 A f v :=
    eventuallyEq_of_mem hsnhds (fun t ht => (hasDerivAt_gg2 (hfv t ht) (hvA t ht) (hAd t ht)).deriv)
  -- the five iterated derivatives at `0`, via germ-congruence of the chain
  have e0 : iteratedDeriv 0 (gg0 f) 0 = 0 := by rw [iteratedDeriv_zero]; simp [gg0, hf0]
  have e1 : iteratedDeriv 1 (gg0 f) 0 = 0 := by
    rw [iteratedDeriv_one, hd01.eq_of_nhds]; simp [gg1, hf0]
  have e2 : iteratedDeriv 2 (gg0 f) 0 = 2 * ⟪v 0, v 0⟫_ℝ := by
    rw [iteratedDeriv_succ', hd01.iteratedDeriv_eq 1, iteratedDeriv_one, hd12.eq_of_nhds]
    simp only [gg2, hf0, map_zero, inner_zero_left, mul_zero, sub_zero]
  have e3 : iteratedDeriv 3 (gg0 f) 0 = 0 := by
    rw [iteratedDeriv_succ', hd01.iteratedDeriv_eq 2, iteratedDeriv_succ',
      hd12.iteratedDeriv_eq 1, iteratedDeriv_one, hd23.eq_of_nhds]
    simp [gg3, hf0]
  have e4 : iteratedDeriv 4 (gg0 f) 0 = -8 * ⟪v 0, A 0 (v 0)⟫_ℝ := by
    rw [iteratedDeriv_succ', hd01.iteratedDeriv_eq 3, iteratedDeriv_succ',
      hd12.iteratedDeriv_eq 2, iteratedDeriv_succ', hd23.iteratedDeriv_eq 1, iteratedDeriv_one,
      (hasDerivAt_gg3_zero (hfv 0 hs0) (hvA 0 hs0) (hAd 0 hs0) hAd2_0 hf0).deriv]
  -- the degree-4 Taylor polynomial on `s`
  have hgcd : ContDiffOn ℝ ∞ (gg0 f) s := hf.inner ℝ hf
  have hpoly : ∀ x : ℝ, taylorWithinEval (gg0 f) 4 s 0 x
      = ⟪v 0, v 0⟫_ℝ * x ^ 2 - (1 / 3) * ⟪v 0, A 0 (v 0)⟫_ℝ * x ^ 4 := by
    intro x
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero,
      iteratedDerivWithin_of_isOpen hs_open hs0, e0, e1, e2, e3, e4, sub_zero, smul_eq_mul,
      Nat.factorial]
    norm_num; ring
  -- assemble via `taylor_isLittleO` on the open convex `s` (`𝓝[s] 0 = 𝓝 0`)
  have htay := taylor_isLittleO (f := gg0 f) (n := 4) hs_conv hs0 (hgcd.of_le (by norm_cast))
  rw [hs_open.nhdsWithin_eq hs0] at htay
  have hEqR : (fun x : ℝ => (x - 0) ^ 4) = fun x => x ^ 4 := by funext x; rw [sub_zero]
  rw [hEqR] at htay
  have hEqL : (fun t => ⟪f t, f t⟫_ℝ
        - (⟪v 0, v 0⟫_ℝ * t ^ 2 - (1 / 3) * ⟪v 0, A 0 (v 0)⟫_ℝ * t ^ 4))
      = fun x => gg0 f x - taylorWithinEval (gg0 f) 4 s 0 x := by
    funext t; rw [hpoly t]
  rw [hEqL]
  exact htay

end AbstractODE

/-! ## Corollary 2.10 — the square root of the `|J(t)|²` expansion -/

/-- **Math.** **do Carmo Ch. 5, Corollary 2.10 — the analytic core (`lem:dc-ch5-2-10-sqrt`).**
Taking the square root of the `|J(t)|²` expansion.  If a nonnegative scalar `g` (playing the role
of `|J(t)|²`) has the fourth-order expansion `g(t) = t² − c·t⁴ + o(t⁴)` (do Carmo's (5), with
`c = (1/3)K(p,σ)` after the sectional-curvature identification of `cor:dc-ch5-2-9`), then its
square root has the third-order expansion

  `√(g t) = t − (c/2)·t³ + o(t³)`,   `t → 0⁺`.

With `c = (1/3)K` this is do Carmo's `|J(t)| = t − (1/6)K(p,σ)t³ + R̃(t)`, `R̃(t)/t³ → 0` (his (6)),
since `|J(t)| = √(|J(t)|²)`.  The odd-power expansion is one-sided (`𝓝[>] 0`): `√(t²) = |t|`
matches `t` only for `t ≥ 0`, which is do Carmo's range `t ∈ [0, ℓ]`.

Proof: writing `p t = t − (c/2)t³`, the numerator `g − p² = (g − (t² − c t⁴)) − (c²/4)t⁶` is
`o(t⁴)`, and `√g − p = (g − p²)/(√g + p)` with the denominator `≥ t/2 > 0` near `0⁺`, so the
quotient is `o(t³)`. -/
theorem sqrt_isLittleO_of_sq_isLittleO {g : ℝ → ℝ} {c : ℝ}
    (hg : ∀ t, 0 ≤ g t)
    (hgexp : (fun t => g t - (t ^ 2 - c * t ^ 4)) =o[𝓝 (0 : ℝ)] fun t => t ^ 4) :
    (fun t => Real.sqrt (g t) - (t - (c / 2) * t ^ 3)) =o[𝓝[>] (0 : ℝ)] fun t => t ^ 3 := by
  set p : ℝ → ℝ := fun t => t - (c / 2) * t ^ 3 with hp_def
  set N : ℝ → ℝ := fun t => g t - (p t) ^ 2 with hN_def
  -- Step 1: `N =o[𝓝 0] t^4`, restricted to `𝓝[>] 0`
  have hN : N =o[𝓝 (0 : ℝ)] fun t => t ^ 4 := by
    have heq : N = fun t => (g t - (t ^ 2 - c * t ^ 4)) - (c ^ 2 / 4) * t ^ 6 := by
      funext t
      show g t - (p t) ^ 2 = (g t - (t ^ 2 - c * t ^ 4)) - (c ^ 2 / 4) * t ^ 6
      have hpt : p t = t - (c / 2) * t ^ 3 := rfl
      rw [hpt]; ring
    rw [heq]
    have h6 : (fun t : ℝ => t ^ 6) =o[𝓝 (0 : ℝ)] fun t => t ^ 4 :=
      Asymptotics.isLittleO_pow_pow (by norm_num)
    exact hgexp.sub (h6.const_mul_left (c ^ 2 / 4))
  have hN' : N =o[𝓝[>] (0 : ℝ)] fun t => t ^ 4 := hN.mono nhdsWithin_le_nhds
  -- Step 2: denominator eventually bounded below by `t/2`
  have hp_ge : ∀ᶠ t in 𝓝[>] (0 : ℝ), t / 2 ≤ p t := by
    have hc : Tendsto (fun t : ℝ => (c / 2) * t ^ 2) (𝓝 0) (𝓝 0) := by
      have h1 : Continuous (fun t : ℝ => (c / 2) * t ^ 2) := by continuity
      simpa using h1.tendsto (0 : ℝ)
    have h2 : ∀ᶠ t in 𝓝 (0 : ℝ), (c / 2) * t ^ 2 < 1 / 2 := hc.eventually_lt_const (by norm_num)
    have h3 := h2.filter_mono (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    filter_upwards [h3, self_mem_nhdsWithin] with t ht htpos
    have hpt : p t = t - (c / 2) * t ^ 3 := rfl
    rw [hpt]
    have : (0 : ℝ) < t := htpos
    nlinarith [ht, this]
  have hden : ∀ᶠ t in 𝓝[>] (0 : ℝ), t / 2 ≤ Real.sqrt (g t) + p t := by
    filter_upwards [hp_ge] with t ht
    have h0 := Real.sqrt_nonneg (g t)
    linarith
  -- Step 3: reduce to a `Tendsto` and squeeze
  have hvac : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ^ 3 = 0 → Real.sqrt (g t) - p t = 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht h
    exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) (ne_of_gt ht)
  rw [Asymptotics.isLittleO_iff_tendsto' hvac]
  have hfactor : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (Real.sqrt (g t) - p t) / t ^ 3 = N t / ((Real.sqrt (g t) + p t) * t ^ 3) := by
    filter_upwards [self_mem_nhdsWithin, hden] with t htpos hdent
    have ht3 : (0 : ℝ) < t := htpos
    have hdenpos : 0 < Real.sqrt (g t) + p t := by linarith
    have hsqrt_sq : Real.sqrt (g t) ^ 2 = g t := Real.sq_sqrt (hg t)
    have hNeq : N t = (Real.sqrt (g t) - p t) * (Real.sqrt (g t) + p t) := by
      have hNt : N t = g t - (p t) ^ 2 := rfl
      rw [hNt]
      have hexpand : (Real.sqrt (g t) - p t) * (Real.sqrt (g t) + p t)
          = Real.sqrt (g t) ^ 2 - p t ^ 2 := by ring
      rw [hexpand, hsqrt_sq]
    rw [hNeq]
    have hne : (Real.sqrt (g t) + p t) ≠ 0 := ne_of_gt hdenpos
    field_simp
  have hbound : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖(Real.sqrt (g t) - p t) / t ^ 3‖ ≤ 2 * ‖N t / t ^ 4‖ := by
    filter_upwards [hfactor, self_mem_nhdsWithin, hden] with t hfac htpos hdent
    have ht3 : (0 : ℝ) < t := htpos
    have hdenpos : 0 < Real.sqrt (g t) + p t := by linarith
    rw [hfac, Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div,
      abs_of_pos (show (0 : ℝ) < (Real.sqrt (g t) + p t) * t ^ 3 by positivity),
      abs_of_pos (show (0 : ℝ) < t ^ 4 by positivity)]
    have hge : t ^ 4 / 2 ≤ (Real.sqrt (g t) + p t) * t ^ 3 := by
      have hprod : (t / 2) * t ^ 3 ≤ (Real.sqrt (g t) + p t) * t ^ 3 :=
        mul_le_mul_of_nonneg_right hdent (by positivity)
      nlinarith [hprod]
    have key : |N t| / ((Real.sqrt (g t) + p t) * t ^ 3) ≤ |N t| / (t ^ 4 / 2) :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hge
    calc |N t| / ((Real.sqrt (g t) + p t) * t ^ 3) ≤ |N t| / (t ^ 4 / 2) := key
      _ = 2 * (|N t| / t ^ 4) := by ring
  have hbound_tendsto : Tendsto (fun t => 2 * ‖N t / t ^ 4‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h1 : Tendsto (fun t => N t / t ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 0) := hN'.tendsto_div_nhds_zero
    have h2 : Tendsto (fun t => ‖N t / t ^ 4‖) (𝓝[>] (0 : ℝ)) (𝓝 0) := by simpa using h1.norm
    simpa using h2.const_mul (2 : ℝ)
  exact squeeze_zero_norm' hbound hbound_tendsto

end Riemannian.Jacobi

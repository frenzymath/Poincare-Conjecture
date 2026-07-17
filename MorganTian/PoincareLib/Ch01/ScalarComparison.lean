import PoincareLib.Ch01.ComparisonFunctions

/-!
# Morgan–Tian Ch. 1, §1.4 — Scalar Riccati and Sturm comparison

The two scalar ODE-comparison results that carry the analytic content of the
chapter's comparison theorems:

* **Scalar Riccati comparison** (`scalar_riccati_comparison`, blueprint
  `lem:scalar-riccati-comparison`): if `φ' + φ² ≤ k` on `(0, r₀)` and
  `φ(r) − 1/r → 0` as `r → 0⁺`, then `φ ≤ sn_k'/sn_k` on `(0, r₀)`. This is
  the engine behind the sectional/Ricci curvature comparison theorems
  (`thm:sectional-curvature-comparison`, `thm:ricci-curvature-comparison`):
  the shape-operator eigenvalues/trace satisfy the Riccati inequality, the
  model value is `sn_k'/sn_k`.

* **Scalar Sturm comparison** (`scalar_sturm_comparison`): if `f'' ≥ −K f`
  on `(0, t₁)` with `f(0) = 0`, `f > 0` inside, `f'` bounded near `0`, and
  `f(t)/t → c > 0`, then `f ≥ c · s_K` on `(0, t₁]` — in particular `f`
  cannot vanish again before `π/√K`. This is the analytic core of
  `lem:conjugate-sturm` (no conjugate points under an upper curvature
  bound): there `f = |Y|` for a Jacobi field `Y` orthogonal to the geodesic,
  the Cauchy–Schwarz inequality gives `f'' ≥ −K f`, and `c = |∇Y(0)|`.

Both proofs follow the blueprint verbatim. For the Riccati comparison: the
model solution `a = sn_k'/sn_k` satisfies `a' + a² = k` and `a − 1/r → 0`,
and `ψ = sn_k²(φ − a)` has `ψ' ≤ −sn_k²(φ − a)² ≤ 0` with `ψ(0⁺) = 0`,
forcing `ψ ≤ 0`. For the Sturm comparison: the Wronskian
`W = f'·s_K − f·s_K'` is non-decreasing with `W(0⁺) = 0`, so `f/s_K` is
non-decreasing with limit `c` at `0⁺`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4
(blueprint `lem:scalar-riccati-comparison`, `lem:conjugate-sturm`).
-/

open Real Filter Set
open scoped Topology

namespace PoincareLib

/-! ### The model solution `a = sn_k'/sn_k` of the Riccati equation -/

/-- **Math.** The logarithmic derivative `a = sn_k'/sn_k` of the sinh
comparison function solves the Riccati equation `a' = k − a²` on `(0, ∞)`.

Blueprint: `lem:scalar-riccati-comparison` (the model solution). -/
theorem hasDerivAt_csK_div_snK (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    HasDerivAt (fun x => csK k x / snK k x)
      (k - (csK k r / snK k r) ^ 2) r := by
  have hsn : snK k r ≠ 0 := (snK_pos k r hk hr).ne'
  have h := (hasDerivAt_csK k r hk).div (hasDerivAt_snK k r hk) hsn
  have heq : (k * snK k r * snK k r - csK k r * csK k r) / snK k r ^ 2
      = k - (csK k r / snK k r) ^ 2 := by
    field_simp
  rwa [heq] at h

/-- **Math.** The two-sided elementary bound
`0 ≤ sn_k'(r)/sn_k(r) − 1/r ≤ k·r/2` for `r > 0`, `k ≥ 0`: quantitative form
of the asymptotics `sn_k'/sn_k = 1/r + O(r)` as `r → 0⁺`, obtained by
integrating `(r·sn_k' − sn_k)' = k·r·sn_k` twice against the monotonicity of
`sn_k`.

Blueprint: `lem:scalar-riccati-comparison` (the asymptotics of the model
solution `a(r) − 1/r → 0`). -/
theorem csK_div_snK_sub_inv_mem_Icc (k r : ℝ) (hk : 0 ≤ k) (hr : 0 < r) :
    csK k r / snK k r - 1 / r ∈ Icc 0 (k * r / 2) := by
  have hsnpos : 0 < snK k r := snK_pos k r hk hr
  -- `h₁(r) = r·sn_k'(r) − sn_k(r)` is nonnegative on `[0, ∞)`:
  -- it vanishes at `0` and has derivative `k·r·sn_k(r) ≥ 0`.
  set h₁ : ℝ → ℝ := fun x => x * csK k x - snK k x with hh₁
  have hd₁ : ∀ x : ℝ, HasDerivAt h₁ (k * x * snK k x) x := by
    intro x
    have h := ((hasDerivAt_id x).mul (hasDerivAt_csK k x hk)).sub
      (hasDerivAt_snK k x hk)
    have heq : 1 * csK k x + id x * (k * snK k x) - csK k x = k * x * snK k x := by
      simp only [id_eq]
      ring
    rwa [heq] at h
  have hmono₁ : MonotoneOn h₁ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd₁ x).continuousAt.continuousWithinAt)
      (fun x hx => (hd₁ x).hasDerivWithinAt) fun x hx => ?_
    rw [interior_Ici] at hx
    have hx0 : (0 : ℝ) < x := hx
    have := snK_nonneg k x hk hx0.le
    positivity
  have h₁0 : h₁ 0 = 0 := by simp [hh₁]
  have h₁nonneg : 0 ≤ h₁ r := by
    have := hmono₁ (self_mem_Ici) (mem_Ici.2 hr.le) hr.le
    rwa [h₁0] at this
  -- `h₂(r) = (k·r²/2)·sn_k(r) − h₁(r)` is nonnegative on `[0, ∞)`:
  -- it vanishes at `0` and has derivative `(k·r²/2)·sn_k'(r) ≥ 0`.
  set h₂ : ℝ → ℝ := fun x => k * x ^ 2 / 2 * snK k x - h₁ x with hh₂
  have hd₂ : ∀ x : ℝ, HasDerivAt h₂ (k * x ^ 2 / 2 * csK k x) x := by
    intro x
    have hpoly : HasDerivAt (fun y : ℝ => k * y ^ 2 / 2) (k * x) x := by
      have h := (hasDerivAt_pow 2 x).const_mul k
      have h' := h.div_const 2
      have heq : k * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) / 2 = k * x := by
        push_cast
        ring
      rwa [heq] at h'
    have h := (hpoly.mul (hasDerivAt_snK k x hk)).sub (hd₁ x)
    have heq : k * x * snK k x + k * x ^ 2 / 2 * csK k x - k * x * snK k x
        = k * x ^ 2 / 2 * csK k x := by ring
    rwa [heq] at h
  have hmono₂ : MonotoneOn h₂ (Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun x _ => (hd₂ x).continuousAt.continuousWithinAt)
      (fun x hx => (hd₂ x).hasDerivWithinAt) fun x hx => ?_
    have := (csK_pos k x hk).le
    positivity
  have h₂0 : h₂ 0 = 0 := by simp [hh₂, h₁0]
  have h₂nonneg : 0 ≤ h₂ r := by
    have := hmono₂ (self_mem_Ici) (mem_Ici.2 hr.le) hr.le
    rwa [h₂0] at this
  -- rewrite `a − 1/r` as `h₁(r)/(r·sn_k(r))` and apply the two bounds
  have hkey : csK k r / snK k r - 1 / r = h₁ r / (r * snK k r) := by
    rw [hh₁]
    field_simp
  constructor
  · rw [hkey]
    positivity
  · rw [hkey]
    have hbound : h₁ r ≤ k * r ^ 2 / 2 * snK k r := by
      have := h₂nonneg
      rw [hh₂] at this
      linarith
    calc h₁ r / (r * snK k r) ≤ k * r ^ 2 / 2 * snK k r / (r * snK k r) :=
          div_le_div_of_nonneg_right hbound (by positivity)
        _ = k * r / 2 := by field_simp

/-- **Math.** The asymptotics `sn_k'(r)/sn_k(r) − 1/r → 0` as `r → 0⁺`, for
`k ≥ 0` (squeeze from `csK_div_snK_sub_inv_mem_Icc`).

Blueprint: `lem:scalar-riccati-comparison`. -/
theorem tendsto_csK_div_snK_sub_inv (k : ℝ) (hk : 0 ≤ k) :
    Tendsto (fun r => csK k r / snK k r - 1 / r) (𝓝[>] 0) (𝓝 0) := by
  have hupper : Tendsto (fun r : ℝ => k * r / 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have : Tendsto (fun r : ℝ => k * r / 2) (𝓝 (0 : ℝ)) (𝓝 (k * 0 / 2)) :=
      ((continuous_const.mul continuous_id).div_const 2).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact (csK_div_snK_sub_inv_mem_Icc k r hk hr).1
  · filter_upwards [eventually_mem_nhdsWithin] with r hr
    exact (csK_div_snK_sub_inv_mem_Icc k r hk hr).2

/-! ### The scalar Riccati comparison -/

/-- **Math.** **Scalar Riccati comparison** (Morgan–Tian, Ch. 1, §1.4). Fix
`k ≥ 0` and `r₀ > 0`. Suppose `φ` is differentiable on `(0, r₀)` with
`φ' + φ² ≤ k` there, and `φ(r) − 1/r → 0` as `r → 0⁺`. Then
`φ(r) ≤ sn_k'(r)/sn_k(r)` for all `r ∈ (0, r₀)`.

Proof, following the blueprint: the model solution `a = sn_k'/sn_k`
satisfies `a' + a² = k` and `a(r) − 1/r → 0`; the function
`ψ = sn_k²·(φ − a)` tends to `0` at `0⁺` and satisfies
`ψ' ≤ −sn_k²(φ − a)² ≤ 0`, hence `ψ ≤ 0`, hence `φ ≤ a`.

Blueprint: `lem:scalar-riccati-comparison`. -/
theorem scalar_riccati_comparison {k r₀ : ℝ} (hk : 0 ≤ k) {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioo (0 : ℝ) r₀, φ' r + φ r ^ 2 ≤ k)
    (h0 : Tendsto (fun r => φ r - 1 / r) (𝓝[>] 0) (𝓝 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, φ r ≤ csK k r / snK k r := by
  -- the model solution and the weighted difference ψ = sn_k²(φ − a)
  set a : ℝ → ℝ := fun x => csK k x / snK k x with ha
  set ψ : ℝ → ℝ := fun x => snK k x ^ 2 * (φ x - a x) with hψ
  set ψ' : ℝ → ℝ := fun x =>
    2 * snK k x * csK k x * (φ x - a x) + snK k x ^ 2 * (φ' x - (k - a x ^ 2))
    with hψ'
  -- ψ is differentiable on (0, r₀) with derivative ψ'
  have hdψ : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt ψ (ψ' r) r := by
    intro r hr
    have hsq : HasDerivAt (fun x => snK k x ^ 2) (2 * snK k r * csK k r) r := by
      have h := (hasDerivAt_snK k r hk).pow 2
      have heq : ((2 : ℕ) : ℝ) * snK k r ^ (2 - 1) * csK k r
          = 2 * snK k r * csK k r := by
        push_cast
        ring
      rwa [heq] at h
    have hsub : HasDerivAt (fun x => φ x - a x) (φ' r - (k - a r ^ 2)) r :=
      (hφ r hr).sub (hasDerivAt_csK_div_snK k r hk hr.1)
    exact hsq.mul hsub
  -- the derivative is nonpositive: ψ' ≤ −sn_k²(φ − a)² ≤ 0
  have hψ'le : ∀ r ∈ Ioo (0 : ℝ) r₀, ψ' r ≤ 0 := by
    intro r hr
    have hsnpos : 0 < snK k r := snK_pos k r hk hr.1
    have hcs : csK k r = snK k r * a r := by
      rw [ha]
      field_simp
    have hφle : φ' r - k ≤ -φ r ^ 2 := by
      have := hric r hr
      linarith
    have hmul : snK k r ^ 2 * (φ' r - k) ≤ snK k r ^ 2 * (-φ r ^ 2) :=
      mul_le_mul_of_nonneg_left hφle (sq_nonneg _)
    simp only [hψ', hcs]
    nlinarith [sq_nonneg (snK k r * (φ r - a r))]
  -- ψ is antitone on (0, r₀)
  have hanti : AntitoneOn ψ (Ioo (0 : ℝ) r₀) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := ψ') (convex_Ioo _ _)
      (fun x hx => (hdψ x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx
      exact (hdψ x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      exact hψ'le x hx
  -- ψ → 0 as r → 0⁺
  have hψ0 : Tendsto ψ (𝓝[>] 0) (𝓝 0) := by
    have hsn0 : Tendsto (fun r => snK k r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Tendsto (snK k) (𝓝 (0 : ℝ)) (𝓝 (snK k 0)) :=
        (hasDerivAt_snK k 0 hk).continuousAt.tendsto
      rw [snK_zero_right] at hc
      have hc' : Tendsto (snK k) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        hc.mono_left nhdsWithin_le_nhds
      simpa using hc'.pow 2
    have hdiff : Tendsto (fun r => (φ r - 1 / r) - (a r - 1 / r)) (𝓝[>] (0 : ℝ))
        (𝓝 0) := by
      have := h0.sub (tendsto_csK_div_snK_sub_inv k hk)
      simpa using this
    have := hsn0.mul hdiff
    rw [zero_mul] at this
    refine this.congr fun r => ?_
    rw [hψ]
    ring
  -- conclude: for each r, ψ(r) ≤ lim ψ = 0, then divide by sn_k² > 0
  intro r hr
  have hψr : ψ r ≤ 0 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ψ r ≤ ψ s := by
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioi (0 : ℝ) := eventually_mem_nhdsWithin
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < r :=
        (eventually_lt_nhds hr.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2] with s hs1 hs2
      exact hanti ⟨hs1, hs2.trans hr.2⟩ hr hs2.le
    exact ge_of_tendsto hψ0 hev
  have hsn2 : 0 < snK k r ^ 2 := pow_pos (snK_pos k r hk hr.1) 2
  have : snK k r ^ 2 * (φ r - a r) ≤ 0 := hψr
  nlinarith

/-- **Math.** Scalar Riccati comparison on all of `(0, ∞)` (the case
`r₀ = ∞` of `lem:scalar-riccati-comparison`).

Blueprint: `lem:scalar-riccati-comparison`. -/
theorem scalar_riccati_comparison_Ioi {k : ℝ} (hk : 0 ≤ k) {φ φ' : ℝ → ℝ}
    (hφ : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt φ (φ' r) r)
    (hric : ∀ r ∈ Ioi (0 : ℝ), φ' r + φ r ^ 2 ≤ k)
    (h0 : Tendsto (fun r => φ r - 1 / r) (𝓝[>] 0) (𝓝 0)) :
    ∀ r ∈ Ioi (0 : ℝ), φ r ≤ csK k r / snK k r := fun r hr =>
  scalar_riccati_comparison hk (fun s hs => hφ s hs.1) (fun s hs => hric s hs.1)
    h0 r ⟨hr, lt_add_one r⟩

/-! ### The scalar Sturm comparison -/

/-- **Math.** **Scalar Sturm comparison** — the analytic core of
`lem:conjugate-sturm` (no conjugate points under an upper curvature bound).
Fix `K ≥ 0` and `t₁ > 0` with `√K · t₁ < π` (i.e. `t₁ < π/√K`, no condition
when `K = 0`). Suppose `f` is continuous on `[0, t₁]` and twice
differentiable on `(0, t₁)` with `f'' ≥ −K·f` there, `f(0) = 0`, `f > 0` on
`(0, t₁)`, `f'` bounded near `0⁺`, and `f(t)/t → c` as `t → 0⁺`. Then
`f(t) ≥ c · s_K(t)` for all `t ∈ (0, t₁]`.

In the application to `lem:conjugate-sturm`, `f = |Y|` for a Jacobi field
`Y ⟂ γ'` with `Y(0) = 0`, the Jacobi equation and Cauchy–Schwarz give
`f'' ≥ −K f`, and `c = |∇Y(0)| > 0`; the conclusion `f(t₁) ≥ c·s_K(t₁) > 0`
contradicts a conjugate point at `t₁ < π/√K`.

Proof, following the blueprint: the Wronskian `W = f'·s_K − f·s_K'`
satisfies `W' = (f'' + K f)·s_K ≥ 0` and `W(0⁺) = 0`, so `W ≥ 0`, so
`(f/s_K)' = W/s_K² ≥ 0`; the ratio `f/s_K` is non-decreasing with limit
`c` at `0⁺`, whence `f/s_K ≥ c` on `(0, t₁)`, and the endpoint follows by
continuity.

Blueprint: `lem:conjugate-sturm` (scalar core). -/
theorem scalar_sturm_comparison {K t₁ c C : ℝ} (hK : 0 ≤ K) (ht₁ : 0 < t₁)
    (hπ : Real.sqrt K * t₁ < Real.pi) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 t₁))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) t₁, HasDerivAt f (f' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) t₁, HasDerivAt f' (f'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) t₁, -(K * f t) ≤ f'' t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) t₁, 0 < f t)
    (hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), |f' t| ≤ C)
    (hslope : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 c)) :
    ∀ t ∈ Ioc (0 : ℝ) t₁, c * sinK K t ≤ f t := by
  -- s_K is positive on (0, t₁) (and at t₁ it is nonneg; positivity holds
  -- there too but is not needed)
  have hsinpos : ∀ t ∈ Ioc (0 : ℝ) t₁, 0 < sinK K t := by
    intro t ht
    refine sinK_pos K t hK ht.1 (lt_of_le_of_lt ?_ hπ)
    exact mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)
  -- the Wronskian W = f'·s − f·s' and its derivative
  set W : ℝ → ℝ := fun t => f' t * sinK K t - f t * cosK K t with hW
  have hdW : ∀ t ∈ Ioo (0 : ℝ) t₁,
      HasDerivAt W (sinK K t * (f'' t + K * f t)) t := by
    intro t ht
    have h := ((hd2 t ht).mul (hasDerivAt_sinK K t hK)).sub
      ((hd1 t ht).mul (hasDerivAt_cosK K t hK))
    have heq : f'' t * sinK K t + f' t * cosK K t -
        (f' t * cosK K t + f t * -(K * sinK K t))
        = sinK K t * (f'' t + K * f t) := by ring
    rwa [heq] at h
  -- W is monotone on (0, t₁): W' = s·(f'' + K f) ≥ 0
  have hWmono : MonotoneOn W (Ioo (0 : ℝ) t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => sinK K t * (f'' t + K * f t)) (convex_Ioo _ _)
      (fun x hx => (hdW x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx
      exact (hdW x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      have hsn : 0 ≤ sinK K x := (hsinpos x ⟨hx.1, hx.2.le⟩).le
      have hj : 0 ≤ f'' x + K * f x := by have := hjac x hx; linarith
      positivity
  -- f → 0 at 0⁺ (from the slope limit)
  have hf0 : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have := hslope.mul hid
    rw [mul_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
    field_simp
  -- W → 0 at 0⁺
  have hW0 : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsin0 : Tendsto (sinK K) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Tendsto (sinK K) (𝓝 (0 : ℝ)) (𝓝 (sinK K 0)) :=
        (hasDerivAt_sinK K 0 hK).continuousAt.tendsto
      rw [sinK_zero_right] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have hterm1 : Tendsto (fun t => f' t * sinK K t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine squeeze_zero_norm' (a := fun t => C * |sinK K t|) ?_ ?_
      · filter_upwards [hbdd] with t ht
        calc ‖f' t * sinK K t‖ = |f' t| * |sinK K t| := abs_mul _ _
          _ ≤ C * |sinK K t| := mul_le_mul_of_nonneg_right ht (abs_nonneg _)
      · have : Tendsto (fun t => C * |sinK K t|) (𝓝[>] (0 : ℝ)) (𝓝 (C * |0|)) :=
          (hsin0.abs.const_mul C)
        simpa using this
    have hterm2 : Tendsto (fun t => f t * cosK K t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hcos : Tendsto (cosK K) (𝓝[>] (0 : ℝ)) (𝓝 (cosK K 0)) :=
        ((hasDerivAt_cosK K 0 hK).continuousAt.tendsto).mono_left
          nhdsWithin_le_nhds
      have := hf0.mul hcos
      rw [zero_mul] at this
      exact this
    have := hterm1.sub hterm2
    rw [sub_zero] at this
    exact this
  -- W ≥ 0 on (0, t₁)
  have hWnonneg : ∀ t ∈ Ioo (0 : ℝ) t₁, 0 ≤ W t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), W s ≤ W t := by
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioi (0 : ℝ) := eventually_mem_nhdsWithin
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t :=
        (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2] with s hs1 hs2
      exact hWmono ⟨hs1, hs2.trans ht.2⟩ ht hs2.le
    exact le_of_tendsto hW0 hev
  -- the ratio Q = f/s_K is monotone on (0, t₁): Q' = W/s_K² ≥ 0
  set Q : ℝ → ℝ := fun t => f t / sinK K t with hQ
  have hdQ : ∀ t ∈ Ioo (0 : ℝ) t₁,
      HasDerivAt Q (W t / sinK K t ^ 2) t := by
    intro t ht
    have hsn : sinK K t ≠ 0 := (hsinpos t ⟨ht.1, ht.2.le⟩).ne'
    exact (hd1 t ht).div (hasDerivAt_sinK K t hK) hsn
  have hQmono : MonotoneOn Q (Ioo (0 : ℝ) t₁) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg
      (f' := fun t => W t / sinK K t ^ 2) (convex_Ioo _ _)
      (fun x hx => (hdQ x hx).continuousAt.continuousWithinAt)
      (fun x hx => ?_) (fun x hx => ?_)
    · rw [interior_Ioo] at hx
      exact (hdQ x hx).hasDerivWithinAt
    · rw [interior_Ioo] at hx
      have h1 := hWnonneg x hx
      have h2 : 0 < sinK K x ^ 2 := pow_pos (hsinpos x ⟨hx.1, hx.2.le⟩) 2
      positivity
  -- Q → c at 0⁺
  have hQ0 : Tendsto Q (𝓝[>] (0 : ℝ)) (𝓝 c) := by
    have hratio : Tendsto (fun t => t / sinK K t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h := (tendsto_sinK_div_self K hK).inv₀ one_ne_zero
      rw [inv_one] at h
      refine h.congr fun t => ?_
      rw [inv_div]
    have := hslope.mul hratio
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with t (ht : (0 : ℝ) < t)
    rcases eq_or_ne (sinK K t) 0 with hs | hs
    · rw [hQ]; simp [hs]
    · rw [hQ]
      field_simp
  -- c ≤ Q on (0, t₁)
  have hQge : ∀ t ∈ Ioo (0 : ℝ) t₁, c ≤ Q t := by
    intro t ht
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), Q s ≤ Q t := by
      have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioi (0 : ℝ) := eventually_mem_nhdsWithin
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s < t :=
        (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds
      filter_upwards [h1, h2] with s hs1 hs2
      exact hQmono ⟨hs1, hs2.trans ht.2⟩ ht hs2.le
    exact le_of_tendsto hQ0 hev
  -- conclude on the open interval, then extend to t₁ by continuity
  have hmain : ∀ t ∈ Ioo (0 : ℝ) t₁, c * sinK K t ≤ f t := by
    intro t ht
    have hsn : 0 < sinK K t := hsinpos t ⟨ht.1, ht.2.le⟩
    have := hQge t ht
    rw [hQ] at this
    exact (le_div_iff₀ hsn).1 this
  intro t ht
  rcases lt_or_eq_of_le ht.2 with hlt | heq
  · exact hmain t ⟨ht.1, hlt⟩
  · -- t = t₁: take the limit along 𝓝[Ioo 0 t₁] t₁
    subst heq
    have hne : (𝓝[Ioo (0 : ℝ) t] t).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo ht.1.ne]
      exact ⟨ht.1.le, le_refl t⟩
    have hft : Tendsto f (𝓝[Ioo (0 : ℝ) t] t) (𝓝 (f t)) := by
      have hcw : ContinuousWithinAt f (Icc 0 t) t :=
        hf t ⟨ht.1.le, le_refl t⟩
      exact hcw.tendsto.mono_left (nhdsWithin_mono t Ioo_subset_Icc_self)
    have hst : Tendsto (fun s => c * sinK K s) (𝓝[Ioo (0 : ℝ) t] t)
        (𝓝 (c * sinK K t)) := by
      have : Tendsto (fun s => c * sinK K s) (𝓝 t) (𝓝 (c * sinK K t)) :=
        (((hasDerivAt_sinK K t hK).continuousAt).tendsto.const_mul c)
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto hst hft ?_
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    exact hmain s hs

/-- **Math.** Endpoint positivity form of the scalar Sturm comparison: under
the hypotheses of `scalar_sturm_comparison` with `c > 0`, the function `f`
is still (strictly) positive at `t₁ < π/√K` — a positive solution of
`f'' ≥ −K f` vanishing at `0` with nonzero initial slope cannot vanish
again before `π/√K`. This is the form used to rule out conjugate points.

Blueprint: `lem:conjugate-sturm` (scalar core). -/
theorem scalar_sturm_pos {K t₁ c C : ℝ} (hK : 0 ≤ K) (ht₁ : 0 < t₁)
    (hπ : Real.sqrt K * t₁ < Real.pi) {f f' f'' : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 t₁))
    (hd1 : ∀ t ∈ Ioo (0 : ℝ) t₁, HasDerivAt f (f' t) t)
    (hd2 : ∀ t ∈ Ioo (0 : ℝ) t₁, HasDerivAt f' (f'' t) t)
    (hjac : ∀ t ∈ Ioo (0 : ℝ) t₁, -(K * f t) ≤ f'' t)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) t₁, 0 < f t)
    (hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), |f' t| ≤ C)
    (hc : 0 < c)
    (hslope : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 c)) :
    0 < f t₁ := by
  have h := scalar_sturm_comparison hK ht₁ hπ hf hd1 hd2 hjac hpos hbdd hslope
    t₁ ⟨ht₁, le_refl t₁⟩
  have hsn : 0 < sinK K t₁ := sinK_pos K t₁ hK ht₁ hπ
  calc (0 : ℝ) < c * sinK K t₁ := by positivity
    _ ≤ f t₁ := h

/-! ### Ratio monotonicity under a logarithmic-derivative bound -/

private theorem hasDerivAt_div_sq {r₀ : ℝ} {s s' h h' : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt h (h' r) r) :
    ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt (fun u => h u / s u ^ 2)
      ((h' r * s r ^ 2 - h r * (2 * s r * s' r)) / (s r ^ 2) ^ 2) r := by
  intro r hr
  have hpos := hspos r hr
  have hsq : HasDerivAt (fun u => s u ^ 2) (2 * s r * s' r) r := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hs r hr).pow 2
  exact (hh r hr).div hsq (by positivity)

/-- **Math.** *Ratio monotonicity, upper form.* If `s` is positive and
differentiable on `(0, r₀)` and `h` is differentiable with
`h' ≤ 2(s'/s)·h` there, then `h/s²` is non-increasing on `(0, r₀)`:
`(h/s²)' = (h' − 2(s'/s)h)/s² ≤ 0`. This is the scalar core of the metric
estimate `g_{ij} ≤ sn_k²·ĝ_{ij}` in `thm:sectional-curvature-comparison`.
Blueprint: `lem:ratio-monotone`. -/
theorem antitoneOn_div_sq_of_deriv_le {r₀ : ℝ} {s s' h h' : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt h (h' r) r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, h' r ≤ 2 * (s' r / s r) * h r) :
    AntitoneOn (fun r => h r / s r ^ 2) (Ioo 0 r₀) := by
  have hD := hasDerivAt_div_sq hs hspos hh
  apply antitoneOn_of_deriv_nonpos (convex_Ioo 0 r₀)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hD r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hD r hr).deriv]
    have hpos := hspos r hr
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    have h1 := hle r hr
    have key : 2 * (s' r / s r) * h r * s r ^ 2 = h r * (2 * s r * s' r) := by
      field_simp
    have h3 : h' r * s r ^ 2 ≤ 2 * (s' r / s r) * h r * s r ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    rw [key] at h3
    linarith

/-- **Math.** *Ratio monotonicity, lower form.* If `s` is positive and
differentiable on `(0, r₀)` and `h` is differentiable with
`h' ≥ 2(s'/s)·h` there, then `h/s²` is non-decreasing on `(0, r₀)` — the
mirror form, the scalar core of the metric estimate `g_{ij} ≥ s²·ĝ_{ij}` in
`lem:rauch-lower`. Blueprint: `lem:ratio-monotone`. -/
theorem monotoneOn_div_sq_of_le_deriv {r₀ : ℝ} {s s' h h' : ℝ → ℝ}
    (hs : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt s (s' r) r)
    (hspos : ∀ r ∈ Ioo (0 : ℝ) r₀, 0 < s r)
    (hh : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt h (h' r) r)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r₀, 2 * (s' r / s r) * h r ≤ h' r) :
    MonotoneOn (fun r => h r / s r ^ 2) (Ioo 0 r₀) := by
  have hD := hasDerivAt_div_sq hs hspos hh
  apply monotoneOn_of_deriv_nonneg (convex_Ioo 0 r₀)
  · exact fun r hr => (hD r hr).continuousAt.continuousWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    exact (hD r hr).differentiableAt.differentiableWithinAt
  · intro r hr
    rw [interior_Ioo] at hr
    rw [(hD r hr).deriv]
    have hpos := hspos r hr
    apply div_nonneg _ (by positivity)
    have h1 := hle r hr
    have key : 2 * (s' r / s r) * h r * s r ^ 2 = h r * (2 * s r * s' r) := by
      field_simp
    have h3 : 2 * (s' r / s r) * h r * s r ^ 2 ≤ h' r * s r ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    rw [key] at h3
    linarith

end PoincareLib

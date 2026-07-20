import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hyperbolic space `Hⁿ`: the conformal-metric curvature computation (do Carmo Ch. 8 §3)

do Carmo introduces the hyperbolic space `Hⁿ = {x ∈ ℝⁿ : xₙ > 0}` with the
metric `gᵢⱼ = δᵢⱼ / xₙ²` and proves it has constant sectional curvature `-1` by
a coordinate computation for the general conformal metric `gᵢⱼ = δᵢⱼ / F²`
(`F = e^f > 0`), specialized to `F = xₙ`.

This file formalizes that **coordinate/algebraic computation** faithfully:

* `christoffelFromMetric_eq` — the Christoffel symbols of the conformal metric
  `gᵢⱼ = δᵢⱼ/F²`, computed from the standard formula
  `Γᵏᵢⱼ = ½ Σₗ gᵏˡ(∂ᵢgⱼₗ + ∂ⱼgᵢₗ − ∂ₗgᵢⱼ)`, equal do Carmo's closed form
  `Γᵏᵢⱼ = −δⱼₖfᵢ − δₖᵢfⱼ + δᵢⱼfₖ`;
* `Rcoeff_diag` — the coordinate curvature coefficient satisfies do Carmo's
  identity `F²Rᵢⱼᵢⱼ = −Σₗ fₗ² + fᵢ² + fⱼ² + fᵢᵢ + fⱼⱼ` (his displayed §3
  formula), where `fₐ = ∂f/∂xₐ` and `fₐᵦ = ∂²f/∂xₐ∂xᵦ`;
* `hyperbolic_sectionalCurvature` — specializing the data to `f = log xₙ`
  (`fₐ = δₐₙ/xₙ`, `fₐᵦ = −δₐₙδᵦₙ/xₙ²`, `F = xₙ`) gives the coordinate-frame
  sectional curvature `Kᵢⱼ = Rᵢⱼᵢⱼ·F⁴ ≡ −1` for every coordinate 2-plane `i ≠ j`.

Everything here is a **coordinate/algebraic computation**: the objects are
ℝ-valued functions of the index set `Fin n`, and the partial derivatives `f`, `H`
are carried as data (the anchoring lemmas `hyperbolic_first_partial` and
`hyperbolic_second_partial` record that the specialized values `1/xₙ`, `−1/xₙ²`
are indeed the first and second derivatives of `t ↦ log t` at `xₙ`, so the
`f = log xₙ` instantiation is the genuine one). This is do Carmo's own displayed
§3 computation. Two things are deliberately **not** proved here and are tracked
separately as `\notready`: extending curvature `−1` from the coordinate
2-planes to *all* 2-planes (do Carmo does this via `cor:dc-ch4-3-5`), and tying
this coordinate computation to `DoCarmoLib`'s intrinsic `sectionalCurvature` on
the Riemannian manifold `Hⁿ`; both are collected in the blueprint node
`prop:dc-ch8-3-const-curv`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3.
-/

open scoped BigOperators

noncomputable section

namespace Riemannian.Hyperbolic

variable {n : ℕ}

/-- Kronecker delta valued in `ℝ`. -/
def kron (i j : Fin n) : ℝ := if i = j then 1 else 0

@[simp] theorem kron_self (i : Fin n) : kron i i = 1 := by simp [kron]

theorem kron_comm (i j : Fin n) : kron i j = kron j i := by
  unfold kron
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h)]

theorem kron_eq_zero {i j : Fin n} (h : i ≠ j) : kron i j = 0 := by simp [kron, h]

/-- `∑ₗ δᵢₗ · c l = c i`. -/
theorem sum_kron_left (c : Fin n → ℝ) (i : Fin n) :
    ∑ l, kron i l * c l = c i := by
  simp [kron, Finset.sum_ite_eq]

/-- `∑ₗ δₗᵢ · c l = c i`. -/
theorem sum_kron_right (c : Fin n → ℝ) (i : Fin n) :
    ∑ l, kron l i * c l = c i := by
  rw [Finset.sum_congr rfl (fun l _ => by rw [kron_comm l i])]
  exact sum_kron_left c i

/-- `∑ₗ δₖₗ δⱼₗ · c l = δₖⱼ · c k`: the double Kronecker delta collapses to the
diagonal. -/
theorem sum_kron_kron (c : Fin n → ℝ) (k j : Fin n) :
    ∑ l, kron k l * kron j l * c l = kron k j * c k := by
  have : ∑ l, kron k l * kron j l * c l = ∑ l, kron k l * (kron j l * c l) := by
    apply Finset.sum_congr rfl; intro l _; ring
  rw [this, sum_kron_left (fun l => kron j l * c l) k, kron_comm j k]

/-- `∑ₗ δₖₗ δⱼₗ = δₖⱼ`. -/
theorem sum_kron_kron_one (k j : Fin n) :
    ∑ l, kron k l * kron j l = kron k j := by
  simpa using sum_kron_kron (fun _ => (1 : ℝ)) k j

/-! ## Christoffel symbols of the conformal metric `gᵢⱼ = δᵢⱼ/F²` -/

/-- do Carmo's closed form for the Christoffel symbols of `gᵢⱼ = δᵢⱼ/F²`,
`Γᵏᵢⱼ = −δⱼₖ fᵢ − δₖᵢ fⱼ + δᵢⱼ fₖ`. Arguments: lower indices `i j`, upper index
`k`; `f a = ∂f/∂xₐ` where `f = log F`. -/
def Gamma (f : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  -kron j k * f i - kron k i * f j + kron i j * f k

/-- The Christoffel symbols computed from the metric `gᵢⱼ = δᵢⱼ/F²` via the
standard formula `Γᵏᵢⱼ = ½ Σₗ gᵏˡ(∂ᵢgⱼₗ + ∂ⱼgᵢₗ − ∂ₗgᵢⱼ)`. Here
`gᵏˡ = δₖₗ F²` is the inverse metric and `∂ₘgₐᵦ = −2 δₐᵦ fₘ / F²`
(do Carmo's displayed derivative of the metric). -/
def christoffelFromMetric (F : ℝ) (f : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  (1 / 2) * ∑ l, (kron k l * F ^ 2) *
    ((-2 * kron j l * f i / F ^ 2) + (-2 * kron i l * f j / F ^ 2)
      - (-2 * kron i j * f l / F ^ 2))

/-- **do Carmo Ch. 8 §3 (Christoffel symbols).** The Christoffel symbols of the
conformal metric `gᵢⱼ = δᵢⱼ/F²`, computed from the metric via the Koszul
formula, equal do Carmo's closed form `Γᵏᵢⱼ = −δⱼₖfᵢ − δₖᵢfⱼ + δᵢⱼfₖ`. -/
theorem christoffelFromMetric_eq (F : ℝ) (hF : F ≠ 0) (f : Fin n → ℝ)
    (i j k : Fin n) :
    christoffelFromMetric F f i j k = Gamma f i j k := by
  have hF2 : F ^ 2 ≠ 0 := pow_ne_zero 2 hF
  unfold christoffelFromMetric Gamma
  have hsummand : ∀ l : Fin n,
      (kron k l * F ^ 2) *
        ((-2 * kron j l * f i / F ^ 2) + (-2 * kron i l * f j / F ^ 2)
          - (-2 * kron i j * f l / F ^ 2))
      = (-2 * f i) * (kron k l * kron j l)
        + (-2 * f j) * (kron k l * kron i l)
        + (2 * kron i j) * (kron k l * f l) := by
    intro l; field_simp; ring
  rw [Finset.sum_congr rfl (fun l _ => hsummand l)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_kron_kron_one k j, sum_kron_kron_one k i, sum_kron_left f k]
  rw [kron_comm k j, kron_comm k i]
  ring

/-! ## Coordinate curvature coefficients -/

/-- Derivative `∂ₘ Γᵏᵢⱼ` of do Carmo's Christoffel symbols. Since
`Γᵏᵢⱼ = −δⱼₖ fᵢ − δₖᵢ fⱼ + δᵢⱼ fₖ` differentiates term by term replacing each
first partial `fₐ` by the second partial `Hₘₐ = ∂ₘ∂ₐ f`, we have
`∂ₘΓᵏᵢⱼ = −δⱼₖ Hₘᵢ − δₖᵢ Hₘⱼ + δᵢⱼ Hₘₖ`. -/
def dGamma (H : Fin n → Fin n → ℝ) (m i j k : Fin n) : ℝ :=
  -kron j k * H m i - kron k i * H m j + kron i j * H m k

/-- The coordinate curvature coefficient `Rˢᵢⱼₖ` of the connection with
Christoffel symbols `Γ` (do Carmo's sign convention, `R(∂ᵢ,∂ⱼ)∂ₖ = Σₛ Rˢᵢⱼₖ ∂ₛ`,
matching `R(X,Y)Z = ∇_Y∇_X Z − ∇_X∇_Y Z + ∇_{[X,Y]}Z`):

`Rˢᵢⱼₖ = ∂ⱼΓˢᵢₖ − ∂ᵢΓˢⱼₖ + Σₗ (Γˡᵢₖ Γˢⱼₗ − Γˡⱼₖ Γˢᵢₗ)`.

Arguments: `i j k` are the lower indices `R(∂ᵢ,∂ⱼ)∂ₖ`, `s` the upper index. -/
def Rcoeff (f : Fin n → ℝ) (H : Fin n → Fin n → ℝ) (i j k s : Fin n) : ℝ :=
  dGamma H j i k s - dGamma H i j k s
    + ∑ l, (Gamma f i k l * Gamma f j l s - Gamma f j k l * Gamma f i l s)

/-- **do Carmo Ch. 8 §3 (curvature coefficient).** For distinct coordinate
directions `i ≠ j`, the curvature coefficient contracts to do Carmo's displayed
formula for `F²Rᵢⱼᵢⱼ`:

`Rᵢⱼᵢⱼ (upper index j) = −Σₗ fₗ² + fᵢ² + fⱼ² + fᵢᵢ + fⱼⱼ`,

with `fₐ = ∂f/∂xₐ` and `fₐᵦ = ∂²f/∂xₐ∂xᵦ`. Since `gⱼⱼ = 1/F²`, this quantity is
exactly `F²Rᵢⱼᵢⱼ`. -/
theorem Rcoeff_diag (f : Fin n → ℝ) (H : Fin n → Fin n → ℝ) {i j : Fin n}
    (hne : i ≠ j) :
    Rcoeff f H i j i j
      = -(∑ l, (f l) ^ 2) + (f i) ^ 2 + (f j) ^ 2 + H i i + H j j := by
  have hji : j ≠ i := hne.symm
  -- Normalize each summand of the ΓΓ sum to a polynomial in Kronecker deltas.
  have hsum : ∀ l : Fin n,
      Gamma f i i l * Gamma f j l j - Gamma f j i l * Gamma f i l j
        = (2 * f i) * (kron i l * f l) - (f l) ^ 2
          + kron i l * kron i l * (f j) ^ 2
          - kron j l * kron j l * (f i) ^ 2 := by
    intro l
    simp only [Gamma, kron_comm l i, kron_comm l j, kron_self, kron_eq_zero hji]
    ring
  unfold Rcoeff dGamma
  rw [Finset.sum_congr rfl (fun l _ => hsum l)]
  -- Split the sum and collapse each piece by the Kronecker deltas.
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, sum_kron_left f i,
    sum_kron_kron (fun _ => (f j) ^ 2) i i, sum_kron_kron (fun _ => (f i) ^ 2) j j,
    kron_self, kron_self, kron_eq_zero hne, kron_eq_zero hji]
  ring

/-! ## Specialization to `Hⁿ`: `F = xₙ`, `f = log xₙ`, giving `K ≡ −1` -/

/-- The first partials of `f = log(x_e)` on `Hⁿ`: `fₐ = ∂ₐ log x_e = δₐₑ / x_e`.
Here `e` is the distinguished coordinate (do Carmo's last coordinate `xₙ`) and
`xn = x_e` its value at the point. -/
def fH (xn : ℝ) (e a : Fin n) : ℝ := if a = e then 1 / xn else 0

/-- The second partials (Hessian) of `f = log(x_e)`:
`fₐᵦ = ∂ₐ∂ᵦ log x_e = −δₐₑ δᵦₑ / x_e²`. -/
def HH (xn : ℝ) (e a b : Fin n) : ℝ := if a = e ∧ b = e then -(1 / xn ^ 2) else 0

/-- For hyperbolic data, at every index `(fₐ)² + fₐₐ = 0`: the diagonal Hessian
exactly cancels the squared gradient, since `(1/x_e)² = 1/x_e²`. -/
theorem fH_sq_add_HH (xn : ℝ) (e a : Fin n) :
    (fH xn e a) ^ 2 + HH xn e a a = 0 := by
  unfold fH HH
  by_cases h : a = e
  · simp only [h, and_self, if_true]; ring
  · simp [h]

/-- `∑ₗ (fₗ)² = 1/x_e²`: only the distinguished coordinate contributes. -/
theorem sum_fH_sq (xn : ℝ) (e : Fin n) :
    ∑ l, (fH xn e l) ^ 2 = 1 / xn ^ 2 := by
  have hpt : ∀ l : Fin n, (fH xn e l) ^ 2 = if l = e then 1 / xn ^ 2 else 0 := by
    intro l; unfold fH; by_cases h : l = e
    · simp only [h, if_true]; ring
    · simp [h]
  rw [Finset.sum_congr rfl (fun l _ => hpt l), Finset.sum_ite_eq' Finset.univ e]
  simp

/-- **do Carmo Ch. 8 §3 (curvature of `Hⁿ`).** For the hyperbolic data
(`f = log x_e`, `fₐ = δₐₑ/x_e`, `fₐᵦ = −δₐₑδᵦₑ/x_e²`), the curvature coefficient
`F²Rᵢⱼᵢⱼ` equals `−1/x_e²` on every coordinate 2-plane `i ≠ j`. -/
theorem hyperbolic_Rcoeff (xn : ℝ) (e : Fin n) {i j : Fin n} (hne : i ≠ j) :
    Rcoeff (fH xn e) (HH xn e) i j i j = -(1 / xn ^ 2) := by
  rw [Rcoeff_diag _ _ hne, sum_fH_sq]
  have hi := fH_sq_add_HH xn e i
  have hj := fH_sq_add_HH xn e j
  linarith [hi, hj]

/-- **do Carmo Ch. 8 §3 (sectional curvature of `Hⁿ` in coordinates).** With the
conformal factor `F = x_e`, the coordinate-frame sectional curvature of the
2-plane spanned by `∂ᵢ, ∂ⱼ` (`i ≠ j`) is `Kᵢⱼ = Rᵢⱼᵢⱼ · F⁴ = (F²Rᵢⱼᵢⱼ) · F² ≡ −1`.
The passage from these coordinate 2-planes to *all* 2-planes and to the intrinsic
curvature of the manifold `Hⁿ` (do Carmo's `cor:dc-ch4-3-5` step) is not proved
here; see `prop:dc-ch8-3-const-curv`. -/
theorem hyperbolic_sectionalCurvature (xn : ℝ) (hxn : xn ≠ 0) (e : Fin n)
    {i j : Fin n} (hne : i ≠ j) :
    Rcoeff (fH xn e) (HH xn e) i j i j * xn ^ 2 = -1 := by
  rw [hyperbolic_Rcoeff xn e hne]
  have hxn2 : xn ^ 2 ≠ 0 := pow_ne_zero 2 hxn
  field_simp

/-! ## Anchoring the data: these are the genuine derivatives of `t ↦ log t` -/

/-- `∂ₑ log(x_e) = 1/x_e`: the value used in `fH` is the first derivative of
`Real.log`. -/
theorem hyperbolic_first_partial (xn : ℝ) : deriv Real.log xn = 1 / xn := by
  rw [Real.deriv_log, one_div]

/-- `∂ₑ∂ₑ log(x_e) = −1/x_e²`: the value used in `HH` is the second derivative of
`Real.log` (the derivative of `t ↦ 1/t`). -/
theorem hyperbolic_second_partial (xn : ℝ) :
    deriv (deriv Real.log) xn = -(1 / xn ^ 2) := by
  have hlog : deriv Real.log = fun x : ℝ => x⁻¹ := by
    funext x; exact Real.deriv_log x
  rw [hlog, deriv_inv, one_div]

end Riemannian.Hyperbolic

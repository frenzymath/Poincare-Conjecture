import PoincareLib.Ch01.ScalarComparison
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Algebra.Order.Chebyshev

/-!
# Morgan–Tian Ch. 1, §1.4 — Trace Riccati comparison

The traced (Ricci-level) form of the Riccati comparison: for a differentiable
family `A(r)` of symmetric endomorphisms of an `m`-dimensional real inner
product space with

* `Tr A'(r) + Tr(A(r)²) ≤ m·k` on `(0, r₀)` (in the application: the traced
  matrix Riccati equation `(Tr A)' + Tr(A²) + Ric(γ',γ') = 0` together with
  the lower Ricci bound `Ric ≥ −(n−1)k`), and
* `Tr A(r) − m/r → 0` as `r → 0⁺` (from `A(r) = (1/r)Id + O(r)`),

one has `Tr A(r) ≤ m·sn_k'(r)/sn_k(r)` on `(0, r₀)`
(`trace_riccati_comparison`). This is the analytic engine of the Ricci
curvature comparison theorem (`thm:ricci-curvature-comparison`) and of the
volume-element monotonicity (`lem:volume-element-comparison`) behind the
Bishop–Gromov inequality: there `A` is the shape operator of the geodesic
spheres in a parallel orthonormal trivialization of `γ'^⊥` along the radial
geodesic, `m = n − 1`, and `Tr A = ∂_r log λ` for the polar volume element
`λ`.

The key algebraic step is the trace Cauchy–Schwarz inequality
`(Tr A)² ≤ m·Tr(A²)` for symmetric `A`
(`sq_trace_le_finrank_mul_trace_comp_self`): in an orthonormal basis `(eᵢ)`,
`Tr(A²) = Σᵢ ‖A eᵢ‖² ≥ Σᵢ ⟪A eᵢ, eᵢ⟫²` and
`(Σᵢ ⟪A eᵢ, eᵢ⟫)² ≤ m·Σᵢ ⟪A eᵢ, eᵢ⟫²`. Granted this, `φ = Tr A/m`
satisfies the scalar Riccati inequality `φ' + φ² ≤ k` and the comparison
follows from `PoincareLib.scalar_riccati_comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4
(blueprint `lem:trace-riccati-comparison`).
-/

open Real Filter Set Module
open scoped Topology RealInnerProductSpace

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- **Math.** **Trace Cauchy–Schwarz inequality** for a symmetric endomorphism
`A` of an `m`-dimensional real inner product space: `(Tr A)² ≤ m·Tr(A²)`.
In an orthonormal basis `(eᵢ)`, symmetry gives `Tr(A²) = Σᵢ ‖A eᵢ‖²`, the
Cauchy–Schwarz inequality in `E` gives `‖A eᵢ‖² ≥ ⟪A eᵢ, eᵢ⟫²` for each `i`,
and the Cauchy–Schwarz inequality in `ℝᵐ` gives
`(Σᵢ ⟪A eᵢ, eᵢ⟫)² ≤ m·Σᵢ ⟪A eᵢ, eᵢ⟫²`. Equality in the eigenvalue picture:
this is `(Σ λᵢ)² ≤ m·Σ λᵢ²`. Blueprint: `lem:trace-riccati-comparison`. -/
theorem sq_trace_le_finrank_mul_trace_comp_self {A : E →L[ℝ] E}
    (hsym : ∀ v w : E, ⟪A v, w⟫ = ⟪v, A w⟫) :
    LinearMap.trace ℝ E ↑A ^ 2
      ≤ (finrank ℝ E : ℝ) * LinearMap.trace ℝ E ↑(A ∘L A) := by
  classical
  set b := stdOrthonormalBasis ℝ E with hb
  rw [LinearMap.trace_eq_sum_inner _ b, LinearMap.trace_eq_sum_inner _ b]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  -- each diagonal entry of `A²` dominates the square of that of `A`
  have hdiag : ∀ i, ⟪b i, A (b i)⟫ ^ 2 ≤ ⟪b i, A (A (b i))⟫ := by
    intro i
    have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
    have h1 : ⟪b i, A (A (b i))⟫ = ‖A (b i)‖ ^ 2 := by
      rw [real_inner_comm, hsym (A (b i)) (b i), real_inner_self_eq_norm_sq]
    have h2 : |⟪b i, A (b i)⟫| ≤ ‖A (b i)‖ := by
      have := abs_real_inner_le_norm (b i) (A (b i))
      rwa [hnorm, one_mul] at this
    rw [h1]
    nlinarith [mul_self_le_mul_self (abs_nonneg ⟪b i, A (b i)⟫) h2,
      sq_abs ⟪b i, A (b i)⟫]
  -- discrete Cauchy–Schwarz over the basis index
  have hsum : (∑ i, ⟪b i, A (b i)⟫) ^ 2
      ≤ (finrank ℝ E : ℝ) * ∑ i, ⟪b i, A (b i)⟫ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset (Fin (finrank ℝ E))))
      (f := fun i => ⟪b i, A (b i)⟫)
    simpa using h
  calc (∑ i, ⟪b i, A (b i)⟫) ^ 2
      ≤ (finrank ℝ E : ℝ) * ∑ i, ⟪b i, A (b i)⟫ ^ 2 := hsum
    _ ≤ (finrank ℝ E : ℝ) * ∑ i, ⟪b i, A (A (b i))⟫ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hdiag i)
          (Nat.cast_nonneg _)

/-- **Math.** **Trace Riccati comparison** — the analytic engine of the Ricci
curvature comparison theorem. Fix `k ≥ 0` and `r₀`. Let `E` be a real inner
product space of finite dimension `m ≥ 1` and let `A(r)`, `0 < r < r₀`, be a
differentiable family of symmetric endomorphisms of `E` with
`Tr A'(r) + Tr(A(r)²) ≤ m·k` and `Tr A(r) − m/r → 0` as `r → 0⁺`. Then
`Tr A(r) ≤ m·sn_k'(r)/sn_k(r)` for all `r ∈ (0, r₀)`.

Proof, following the blueprint: `φ = Tr A/m` is differentiable with
`φ' + φ² = (Tr A' + (Tr A)²/m)/m ≤ (Tr A' + Tr(A²))/m ≤ k`, using the trace
Cauchy–Schwarz inequality `(Tr A)² ≤ m·Tr(A²)`
(`sq_trace_le_finrank_mul_trace_comp_self`), and `φ − 1/r → 0` as `r → 0⁺`;
the scalar Riccati comparison (`scalar_riccati_comparison`) gives
`φ ≤ sn_k'/sn_k`.

In the application to `lem:volume-element-comparison`, `E = γ'(r)^⊥` in a
parallel orthonormal trivialization along the radial geodesic (`m = n−1`),
`A(r)` is the shape operator of the geodesic sphere, the traced matrix
Riccati equation gives `Tr A' + Tr(A²) = −Ric(γ',γ') ≤ (n−1)k`, and
`A(r) = (1/r)Id + O(r)` gives the asymptotics.

Blueprint: `lem:trace-riccati-comparison`. -/
theorem trace_riccati_comparison [Nontrivial E] {k r₀ : ℝ} (hk : 0 ≤ k)
    {A A' : ℝ → E →L[ℝ] E}
    (hA : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt A (A' r) r)
    (hsym : ∀ r ∈ Ioo (0 : ℝ) r₀, ∀ v w : E, ⟪A r v, w⟫ = ⟪v, A r w⟫)
    (hRic : ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A' r) + LinearMap.trace ℝ E ↑(A r ∘L A r)
        ≤ (finrank ℝ E : ℝ) * k)
    (h0 : Tendsto
      (fun r => LinearMap.trace ℝ E ↑(A r) - (finrank ℝ E : ℝ) / r)
      (𝓝[>] 0) (𝓝 0)) :
    ∀ r ∈ Ioo (0 : ℝ) r₀,
      LinearMap.trace ℝ E ↑(A r) ≤ (finrank ℝ E : ℝ) * (csK k r / snK k r) := by
  have hm : (0 : ℝ) < (finrank ℝ E : ℝ) := by
    exact_mod_cast finrank_pos
  -- the trace functional as a continuous linear map on endomorphisms
  let L : (E →L[ℝ] E) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.trace ℝ E).comp (ContinuousLinearMap.coeLM ℝ))
  have hL : ∀ T : E →L[ℝ] E, L T = LinearMap.trace ℝ E ↑T := fun T => rfl
  -- the normalized trace `φ = Tr A / m` and its derivative
  set m : ℝ := (finrank ℝ E : ℝ) with hmdef
  set φ : ℝ → ℝ := fun r => LinearMap.trace ℝ E ↑(A r) / m with hφdef
  set φ' : ℝ → ℝ := fun r => LinearMap.trace ℝ E ↑(A' r) / m with hφ'def
  have hφd : ∀ r ∈ Ioo (0 : ℝ) r₀, HasDerivAt φ (φ' r) r := by
    intro r hr
    have h := (L.hasFDerivAt.comp_hasDerivAt r (hA r hr)).div_const m
    simpa only [Function.comp_def, hL] using h
  -- the scalar Riccati inequality `φ' + φ² ≤ k`
  have hric : ∀ r ∈ Ioo (0 : ℝ) r₀, φ' r + φ r ^ 2 ≤ k := by
    intro r hr
    have hCS := sq_trace_le_finrank_mul_trace_comp_self (hsym r hr)
    have hR := hRic r hr
    have key : LinearMap.trace ℝ E ↑(A' r) * m
        + LinearMap.trace ℝ E ↑(A r) ^ 2 ≤ k * m ^ 2 := by
      nlinarith [hCS, mul_le_mul_of_nonneg_left hR hm.le]
    have heq : φ' r + φ r ^ 2
        = (LinearMap.trace ℝ E ↑(A' r) * m
            + LinearMap.trace ℝ E ↑(A r) ^ 2) / m ^ 2 := by
      rw [hφ'def, hφdef]
      field_simp
    rw [heq, div_le_iff₀ (pow_pos hm 2)]
    exact key
  -- the asymptotics `φ − 1/r → 0`
  have h0' : Tendsto (fun r => φ r - 1 / r) (𝓝[>] 0) (𝓝 0) := by
    have h := h0.div_const m
    rw [zero_div] at h
    refine h.congr fun r => ?_
    rw [hφdef]
    rw [sub_div]
    congr 1
    rw [div_div, mul_comm r m, ← div_div, div_self hm.ne']
  -- conclude by the scalar Riccati comparison
  have hcmp := scalar_riccati_comparison hk hφd hric h0'
  intro r hr
  have h := hcmp r hr
  rw [hφdef] at h
  have := (div_le_iff₀ hm).mp h
  linarith [this, mul_comm (csK k r / snK k r) m]

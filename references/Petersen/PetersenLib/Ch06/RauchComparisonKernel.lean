import PetersenLib.Ch06.RiccatiEstimate

/-!
# Petersen Ch. 6, §6.4 — scalar Rauch comparison kernel

The geometric statement of Rauch comparison (`thm:pet-ch6-rauch-comparison`) is a
comparison of the radial Hessian with the model ratios
`sn_K' / sn_K` and `sn_k' / sn_k`.  The Jacobi-to-Riccati and Hessian-identification
bridges are separate manifold constructions.  This file records the scalar core
that remains after those bridges have supplied a radial coefficient `ρ`:

* a lower sectional-curvature bound `k ≤ sec` gives `ρ ≤ sn_k' / sn_k`;
* an upper bound `sec ≤ K` gives `sn_K' / sn_K ≤ ρ` before the first positive
  zero of `sn_K`;
* the first comparison also carries the sharp endpoint `b ≤ π / √k` when `k > 0`.

All analytic work is delegated to `riccatiComparisonEstimate`; keeping this
wrapper separate makes the remaining geometric bridge explicit instead of
silently presenting a scalar statement as a tensor inequality.
-/

open Set

noncomputable section

namespace PetersenLib

/-- **Math.** Petersen Theorem 6.4.3, scalar radial core.  If a radial Hessian
coefficient `ρ` has the standard `1/t + O(t)` initial behaviour and its Riccati
equation is squeezed by the sectional-curvature bounds `k ≤ sec ≤ K`, then it is
squeezed by the corresponding space-form ratios.  The upper comparison is only
asserted before the first positive `K`-model zero, where that ratio is defined.

The hypotheses are deliberately expressed as the two scalar Riccati inequalities;
the Jacobi-field-to-`ρ` construction and the interpretation as an operator
inequality are the geometric bridge consumed by the blueprint headline. -/
theorem rauchComparisonHessian {b k K : ℝ} {ρ ρ' : ℝ → ℝ}
    (hρ : ∀ t ∈ Ioo (0 : ℝ) b, HasDerivAt ρ (ρ' t) t)
    (hO : OneOverAddBigO ρ)
    (hLower : ∀ t ∈ Ioo (0 : ℝ) b,
      ρ' t + (ρ t) ^ 2 ≤ -k)
    (hUpper : ∀ t ∈ Ioo (0 : ℝ) b,
      -K ≤ ρ' t + (ρ t) ^ 2) :
    (0 < k → b ≤ Real.pi / Real.sqrt k) ∧
      (∀ t ∈ Ioo (0 : ℝ) b, ρ t ≤ snRatio k t) ∧
      (∀ t ∈ Ioo (0 : ℝ) b,
        (0 < K → t < Real.pi / Real.sqrt K) → snRatio K t ≤ ρ t) := by
  have hcomparison := riccatiComparisonEstimate (b := b) (k := k) hρ hO
  have hcomparisonK := riccatiComparisonEstimate (b := b) (k := K) hρ hO
  have hlow := hcomparison.1 hLower
  have hupp := hcomparisonK.2 hUpper
  exact ⟨hlow.1, hlow.2, hupp⟩

end PetersenLib

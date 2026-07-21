import PetersenLib.Ch04.ScalarFlatODE
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Topology.Order.IntermediateValue

/-!
# Petersen Ch. 4, §4.2.3 — classification of the scalar-flat family by the sign of `C`

The first-order family `ρ̇² = 1 + C·ρ^{2-n}` (with `n ≥ 3` and `ρ > 0`, see
`Ch04/ScalarFlatODE.lean`) splits into three qualitatively different regimes
according to the sign of the integration constant `C`:

* `C = 0`: the equation degenerates to `ρ̇² ≡ 1`, so `ρ(r) = a + r` or
  `ρ(r) = a - r` and the metric is Euclidean
  (`scalarFlat_affine_of_C_zero`);
* `C > 0`: there is **no** positive solution defined on all of `ℝ` — from
  `ρ̇² = 1 + C·ρ^{2-n} ≥ 1` the derivative has constant sign `≥ 1` or `≤ -1`,
  and either way `ρ` is forced below `0` in finite time
  (`scalarFlat_no_global_solution_of_C_pos`);
* `C < 0`, written `C = -ρ₀^{n-2}` with `ρ₀ > 0`: any positive global solution
  stays above `ρ₀`, has `|ρ̇| ≤ 1`, and is convex
  (`scalarFlat_bounds_of_C_neg`).

The anchor `scalarFlatRotSymCases` packages the trichotomy. The lemma
`scalarFlatEvenSolution_symm` records that an *even* solution automatically has
`ρ̇(0) = 0` and hence `C = -ρ(0)^{n-2}`, identifying Petersen's `ρ₀` with the
central value `ρ(0)`; existence and uniqueness of the global even solution in
the `C < 0` case (Petersen's "Schwarzschild-like" metric) is genuine ODE work
and is *not* formalized here.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §4.2.3, pp. 140–141.
-/

noncomputable section

namespace PetersenLib

/-- A continuous nowhere-vanishing real function on `ℝ` has constant sign, by
the intermediate value theorem. (Auxiliary for Petersen §4.2.3.) -/
theorem pos_or_neg_of_continuous_ne_zero {f : ℝ → ℝ} (hf : Continuous f)
    (hne : ∀ r, f r ≠ 0) : (∀ r, 0 < f r) ∨ (∀ r, f r < 0) := by
  rcases (hne 0).lt_or_gt with h0 | h0
  · refine Or.inr fun r => ?_
    rcases (hne r).lt_or_gt with hr | hr
    · exact hr
    · exfalso
      have hmem : (0 : ℝ) ∈ Set.uIcc (f 0) (f r) :=
        Set.mem_uIcc.mpr (Or.inl ⟨h0.le, hr.le⟩)
      obtain ⟨c, -, hc⟩ := intermediate_value_uIcc hf.continuousOn hmem
      exact hne c hc
  · refine Or.inl fun r => ?_
    rcases (hne r).lt_or_gt with hr | hr
    · exfalso
      have hmem : (0 : ℝ) ∈ Set.uIcc (f 0) (f r) :=
        Set.mem_uIcc.mpr (Or.inr ⟨hr.le, h0.le⟩)
      obtain ⟨c, -, hc⟩ := intermediate_value_uIcc hf.continuousOn hmem
      exact hne c hc
    · exact hr

/-- A `C²` function has continuously differentiable derivative. (Auxiliary.) -/
theorem contDiff_one_deriv {ρ : ℝ → ℝ} (hsm : ContDiff ℝ 2 ρ) :
    ContDiff ℝ 1 (deriv ρ) := by
  have h21 : (2 : WithTop ℕ∞) = 1 + 1 := by norm_num
  rw [h21] at hsm
  exact (contDiff_succ_iff_deriv.mp hsm).2.2

/-- **Math.** Petersen §4.2.3, case `C = 0`: the first-order equation
degenerates to `ρ̇² ≡ 1`; since `ρ̇` is continuous and never `0`, it is
identically `1` or identically `-1`, so `ρ(r) = a + r` or `ρ(r) = a - r`
(with `a = ρ(0)`) and the metric `dr² + ρ²(r)ds²_{n-1}` is Euclidean. -/
theorem scalarFlat_affine_of_C_zero {n : ℕ} {ρ : ℝ → ℝ}
    (hsm : ContDiff ℝ 2 ρ) (h : scalarFlatFirstOrder n 0 ρ) :
    ∃ a : ℝ, (∀ r, ρ r = a + r) ∨ (∀ r, ρ r = a - r) := by
  have hρdiff : Differentiable ℝ ρ := hsm.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv ρ) := contDiff_one_deriv hsm
  have hsq : ∀ r, (deriv ρ r) ^ 2 = 1 := by
    intro r
    simpa using (h r).1
  have hne : ∀ r, deriv ρ r ≠ 0 := by
    intro r h0
    have h1 := hsq r
    rw [h0] at h1
    norm_num at h1
  refine ⟨ρ 0, ?_⟩
  rcases pos_or_neg_of_continuous_ne_zero hd1.continuous hne with hpos | hneg
  · -- `ρ̇ ≡ 1`, hence `ρ r - r` is constant
    left
    have hone : ∀ x, deriv ρ x = 1 := by
      intro x
      rcases sq_eq_one_iff.mp (hsq x) with h1 | h1
      · exact h1
      · exact absurd (hpos x) (by rw [h1]; norm_num)
    have hg : ∀ x : ℝ, HasDerivAt (fun s => ρ s - s) 0 x := by
      intro x
      have := ((hρdiff x).hasDerivAt).sub (hasDerivAt_id x)
      simpa [hone x] using this
    intro r
    have key : ρ r - r = ρ 0 - 0 :=
      is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
        (fun y => (hg y).deriv) r 0
    linarith
  · -- `ρ̇ ≡ -1`, hence `ρ r + r` is constant
    right
    have hone : ∀ x, deriv ρ x = -1 := by
      intro x
      rcases sq_eq_one_iff.mp (hsq x) with h1 | h1
      · exact absurd (hneg x) (by rw [h1]; norm_num)
      · exact h1
    have hg : ∀ x : ℝ, HasDerivAt (fun s => ρ s + s) 0 x := by
      intro x
      have := ((hρdiff x).hasDerivAt).add (hasDerivAt_id x)
      simpa [hone x] using this
    intro r
    have key : ρ r + r = ρ 0 + 0 :=
      is_const_of_deriv_eq_zero (fun y => (hg y).differentiableAt)
        (fun y => (hg y).deriv) r 0
    linarith

/-- **Math.** Petersen §4.2.3, case `C > 0`: the first-order equation has no
positive solution on all of `ℝ`. Indeed `ρ̇² = 1 + C·ρ^{2-n} ≥ 1`, so the
continuous derivative never vanishes and by the intermediate value theorem has
constant sign; if `ρ̇ ≥ 1` everywhere then `ρ(r) ≤ ρ(0) + r` for `r ≤ 0` forces
`ρ(-ρ(0)) ≤ 0`, and if `ρ̇ ≤ -1` everywhere then `ρ(r) ≤ ρ(0) - r` for `r ≥ 0`
forces `ρ(ρ(0)) ≤ 0` — either way contradicting positivity. -/
theorem scalarFlat_no_global_solution_of_C_pos {n : ℕ} {C : ℝ} {ρ : ℝ → ℝ}
    (hsm : ContDiff ℝ 2 ρ) (hρ : ∀ r, 0 < ρ r) (hC : 0 < C)
    (h : scalarFlatFirstOrder n C ρ) : False := by
  have hρdiff : Differentiable ℝ ρ := hsm.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv ρ) := contDiff_one_deriv hsm
  have hsq : ∀ r, 1 ≤ (deriv ρ r) ^ 2 := by
    intro r
    have h1 := (h r).1
    have hz : 0 < ρ r ^ ((2 : ℤ) - n) := zpow_pos (hρ r) _
    nlinarith [mul_pos hC hz]
  have hne : ∀ r, deriv ρ r ≠ 0 := by
    intro r h0
    have h1 := hsq r
    rw [h0] at h1
    norm_num at h1
  rcases pos_or_neg_of_continuous_ne_zero hd1.continuous hne with hpos | hneg
  · -- `ρ̇ ≥ 1`: then `ρ r - r` is nondecreasing, so `ρ r ≤ ρ 0 + r` for `r ≤ 0`
    have hone : ∀ x, 1 ≤ deriv ρ x := by
      intro x
      nlinarith [hsq x, hpos x]
    have hg : ∀ x : ℝ, HasDerivAt (fun s => ρ s - s) (deriv ρ x - 1) x :=
      fun x => ((hρdiff x).hasDerivAt).sub (hasDerivAt_id x)
    have hmono : Monotone fun s => ρ s - s :=
      monotone_of_deriv_nonneg (fun x => (hg x).differentiableAt)
        (fun x => by rw [(hg x).deriv]; linarith [hone x])
    have hkey : ρ (-ρ 0) - -ρ 0 ≤ ρ 0 - 0 :=
      hmono (show -ρ 0 ≤ 0 by linarith [hρ 0])
    linarith [hρ (-ρ 0)]
  · -- `ρ̇ ≤ -1`: then `ρ r + r` is nonincreasing, so `ρ r ≤ ρ 0 - r` for `r ≥ 0`
    have hone : ∀ x, deriv ρ x ≤ -1 := by
      intro x
      nlinarith [hsq x, hneg x]
    have hg : ∀ x : ℝ, HasDerivAt (fun s => ρ s + s) (deriv ρ x + 1) x :=
      fun x => ((hρdiff x).hasDerivAt).add (hasDerivAt_id x)
    have hanti : Antitone fun s => ρ s + s :=
      antitone_of_deriv_nonpos (fun x => (hg x).differentiableAt)
        (fun x => by rw [(hg x).deriv]; linarith [hone x])
    have hkey : ρ (ρ 0) + ρ 0 ≤ ρ 0 + 0 :=
      hanti (show (0 : ℝ) ≤ ρ 0 by linarith [hρ 0])
    linarith [hρ (ρ 0)]

/-- **Math.** Petersen §4.2.3, case `C < 0`, written `C = -ρ₀^{n-2}` with
`ρ₀ > 0`: every positive global solution of the first-order equation satisfies
(i) `ρ₀ ≤ ρ` — otherwise `(ρ₀/ρ)^{n-2} > 1` would make `ρ̇² < 0`;
(ii) `ρ̇² ≤ 1`, since the subtracted term `ρ₀^{n-2}·ρ^{2-n}` is positive; and
(iii) convexity `ρ̈ ≥ 0`, from `ρ̈ = (n-2)/2 · ρ₀^{n-2}·ρ^{1-n} ≥ 0`. -/
theorem scalarFlat_bounds_of_C_neg {n : ℕ} (hn : 3 ≤ n) {ρ : ℝ → ℝ} {ρ₀ : ℝ}
    (hρ : ∀ r, 0 < ρ r) (hρ₀ : 0 < ρ₀)
    (h : scalarFlatFirstOrder n (-ρ₀ ^ (n - 2)) ρ) :
    (∀ r, ρ₀ ≤ ρ r) ∧ (∀ r, (deriv ρ r) ^ 2 ≤ 1) ∧ (∀ r, 0 ≤ deriv (deriv ρ) r) := by
  have hzpow : ∀ r, (ρ r : ℝ) ^ ((2 : ℤ) - n) = (ρ r ^ (n - 2))⁻¹ := by
    intro r
    rw [← zpow_natCast (ρ r) (n - 2), ← zpow_neg]
    congr 1
    push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
    ring
  refine ⟨fun r => ?_, fun r => ?_, fun r => ?_⟩
  · -- (i) the lower barrier `ρ₀ ≤ ρ r`
    have h1 := (h r).1
    rw [hzpow r] at h1
    have hpow_pos : 0 < ρ r ^ (n - 2) := pow_pos (hρ r) _
    have hsqn := sq_nonneg (deriv ρ r)
    rw [h1] at hsqn
    have hquot : ρ₀ ^ (n - 2) * (ρ r ^ (n - 2))⁻¹ ≤ 1 := by linarith
    have hle : ρ₀ ^ (n - 2) ≤ ρ r ^ (n - 2) := by
      have := mul_le_mul_of_nonneg_right hquot hpow_pos.le
      rwa [one_mul, mul_assoc, inv_mul_cancel₀ hpow_pos.ne', mul_one] at this
    exact le_of_pow_le_pow_left₀ (by omega) (hρ r).le hle
  · -- (ii) the gradient bound `ρ̇² ≤ 1`
    have h1 := (h r).1
    rw [hzpow r] at h1
    have hpos : 0 < ρ₀ ^ (n - 2) * (ρ r ^ (n - 2))⁻¹ :=
      mul_pos (pow_pos hρ₀ _) (inv_pos.mpr (pow_pos (hρ r) _))
    linarith
  · -- (iii) convexity `0 ≤ ρ̈`
    have h2 := (h r).2
    rw [h2]
    have hz : 0 < ρ r ^ ((1 : ℤ) - n) := zpow_pos (hρ r) _
    have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by
      have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have hp : (0 : ℝ) < ρ₀ ^ (n - 2) := pow_pos hρ₀ _
    nlinarith [mul_nonneg (mul_nonneg hn2 hp.le) hz.le]

/-- **Math.** Petersen §4.2.3 (classification of the scalar-flat family): for
`n ≥ 3` and a positive `C²` solution `ρ` of `ρ̇² = 1 + C·ρ^{2-n}` on all of
`ℝ`, the sign of `C` gives the trichotomy: for `C = 0` the solution is affine
`ρ(r) = a ± r` (Euclidean metric); for `C > 0` no global positive solution
exists; and for `C = -ρ₀^{n-2} < 0` the solution satisfies `ρ₀ ≤ ρ`,
`ρ̇² ≤ 1`, and `ρ̈ ≥ 0` (Schwarzschild-like regime). -/
theorem scalarFlatRotSymCases {n : ℕ} (hn : 3 ≤ n) {C : ℝ} {ρ : ℝ → ℝ}
    (hsm : ContDiff ℝ 2 ρ) (hρ : ∀ r, 0 < ρ r) (h : scalarFlatFirstOrder n C ρ) :
    (C = 0 → ∃ a : ℝ, (∀ r, ρ r = a + r) ∨ (∀ r, ρ r = a - r)) ∧
    (0 < C → False) ∧
    (∀ ρ₀ : ℝ, 0 < ρ₀ → C = -ρ₀ ^ (n - 2) →
      (∀ r, ρ₀ ≤ ρ r) ∧ (∀ r, (deriv ρ r) ^ 2 ≤ 1) ∧ (∀ r, 0 ≤ deriv (deriv ρ) r)) := by
  refine ⟨fun hC => ?_, fun hC => ?_, fun ρ₀ hρ₀ hC => ?_⟩
  · rw [hC] at h
    exact scalarFlat_affine_of_C_zero hsm h
  · exact scalarFlat_no_global_solution_of_C_pos hsm hρ hC h
  · rw [hC] at h
    exact scalarFlat_bounds_of_C_neg hn hρ hρ₀ h

/-- **Math.** Petersen §4.2.3 (the even solution): if a positive solution of
the first-order family is additionally *even*, then its derivative vanishes at
the origin — the derivative of an even function is odd — and evaluating
`ρ̇² = 1 + C·ρ^{2-n}` at `r = 0` identifies the constant as `C = -ρ(0)^{n-2}`.
In particular the even solution belongs to the `C < 0` (Schwarzschild-like)
regime with `ρ₀ = ρ(0)`. Existence and uniqueness of the global even solution
is analytic ODE work not formalized here. -/
theorem scalarFlatEvenSolution_symm {n : ℕ} (hn : 3 ≤ n) {C : ℝ} {ρ : ℝ → ℝ}
    (hρ : ∀ r, 0 < ρ r) (heven : ∀ r, ρ (-r) = ρ r)
    (h : scalarFlatFirstOrder n C ρ) :
    deriv ρ 0 = 0 ∧ C = -ρ 0 ^ (n - 2) := by
  have hd0 : deriv ρ 0 = 0 := by
    have hfun : (fun x : ℝ => ρ (-x)) = ρ := funext heven
    have hodd : deriv (fun x : ℝ => ρ (-x)) 0 = -deriv ρ (-0 : ℝ) :=
      deriv_comp_neg ρ 0
    rw [hfun, neg_zero] at hodd
    linarith [hodd]
  constructor
  · exact hd0
  · have h1 := (h 0).1
    rw [hd0] at h1
    have hzpow : (ρ 0 : ℝ) ^ ((2 : ℤ) - n) = (ρ 0 ^ (n - 2))⁻¹ := by
      rw [← zpow_natCast (ρ 0) (n - 2), ← zpow_neg]
      congr 1
      push_cast [Nat.cast_sub (by omega : 2 ≤ n)]
      ring
    rw [hzpow] at h1
    have hpow_pos : 0 < ρ 0 ^ (n - 2) := pow_pos (hρ 0) _
    have h2 : C * (ρ 0 ^ (n - 2))⁻¹ = -1 := by
      have h0 : (0 : ℝ) ^ 2 = 0 := by norm_num
      rw [h0] at h1
      linarith
    field_simp at h2
    linarith

end PetersenLib

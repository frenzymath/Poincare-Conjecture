import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

/-!
# Evans, Chapter 2: radial identities for odd-dimensional waves

This file records the elementary one-variable identities used in the method of
descent.  The operator `radialOp` is the literal operator `r⁻¹ d/dr` (with the
harmless value `0` at the singular point), and `radialIter` is its iterate.

The useful bookkeeping device is a two-parameter expansion for
`radialIter m (r^q * φ)`.  Its coefficients are defined by the recurrence coming
from differentiating one monomial term.  Evans' coefficients are the special
case `q = 2*k - 1`, `m = k - 1`.
-/

noncomputable section

namespace EvansLib

open scoped BigOperators

/-- The radial derivative `r⁻¹ d/dr`.  Its value at `r = 0` is immaterial for all
the identities below, which are stated on the positive half-line. -/
def radialOp (f : ℝ → ℝ) : ℝ → ℝ := fun r => deriv f r / r

/-- Iteration of `radialOp`. -/
def radialIter : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | m + 1, f => radialOp (radialIter m f)

@[simp] lemma radialIter_zero (f : ℝ → ℝ) : radialIter 0 f = f := rfl

@[simp] lemma radialIter_succ (m : ℕ) (f : ℝ → ℝ) :
    radialIter (m + 1) f = radialOp (radialIter m f) := rfl

/-- The radial operator commutes with multiplication by a constant. -/
lemma radialOp_const_smul (c : ℝ) (f : ℝ → ℝ) :
    radialOp (c • f) = c • radialOp f := by
  funext r
  simp only [radialOp, Pi.smul_apply, smul_eq_mul, deriv_const_smul_field]
  ring

/-- Every iterate of the radial operator commutes with multiplication by a
constant. -/
lemma radialIter_const_smul (m : ℕ) (c : ℝ) (f : ℝ → ℝ) :
    radialIter m (c • f) = c • radialIter m f := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [radialIter_succ, radialIter_succ, ih]
      exact radialOp_const_smul c (radialIter m f)

/-- Coefficients for the general radial expansion.  The third argument is
zero outside the range that can occur, as follows from the recurrence. -/
def radialCoeff : ℕ → ℕ → ℕ → ℝ
  | 0, _q, j => if j = 0 then 1 else 0
  | m + 1, q, j =>
      ((q : ℝ) - 2 * (m : ℝ) + (j : ℝ)) * radialCoeff m q j +
        if j = 0 then 0 else radialCoeff m q (j - 1)

@[simp] lemma radialCoeff_zero (q : ℕ) : radialCoeff 0 q 0 = 1 := by
  simp [radialCoeff]

@[simp] lemma radialCoeff_zero_succ (q j : ℕ) : radialCoeff 0 q (j + 1) = 0 := by
  simp [radialCoeff]

lemma radialCoeff_succ (m q j : ℕ) :
    radialCoeff (m + 1) q j =
      ((q : ℝ) - 2 * (m : ℝ) + (j : ℝ)) * radialCoeff m q j +
        if j = 0 then 0 else radialCoeff m q (j - 1) := by
  rfl

lemma radialCoeff_eq_zero_of_lt (m q j : ℕ) (h : m < j) : radialCoeff m q j = 0 := by
  induction m generalizing q j with
  | zero => cases j <;> simp_all [radialCoeff]
  | succ m ih =>
      rw [radialCoeff_succ]
      have hj : j ≠ 0 := by omega
      have hj' : m < j - 1 := by omega
      simp [hj, ih q j (by omega), ih q (j - 1) hj']

lemma radialCoeff_succ_zero (m q : ℕ) :
    radialCoeff (m + 1) q 0 = ((q : ℝ) - 2 * (m : ℝ)) * radialCoeff m q 0 := by
  rw [radialCoeff_succ]
  simp

/-! ## The one-term differentiation calculation -/

lemma deriv_pow_mul_iteratedDeriv_at_of_order {m q j : ℕ} {φ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hφ : ContDiffAt ℝ (m + 1) φ r)
    (hj : j ≤ m) (hq : 2 * (m + 1) ≤ q) :
    deriv (fun s => s ^ (q - 2 * m + j) * iteratedDeriv j φ s) r / r =
      ((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * (m + 1) + j) *
          iteratedDeriv j φ r +
        r ^ (q - 2 * (m + 1) + (j + 1)) * iteratedDeriv (j + 1) φ r := by
  have hfdj : DifferentiableAt ℝ (iteratedDeriv j φ) r := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.differentiable
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm).differentiableAt.comp r
      (hφ.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j < m + 1 by omega)))
  have hderivj : HasDerivAt (iteratedDeriv j φ)
      (iteratedDeriv (j + 1) φ r) r := by
    have h := hfdj.hasDerivAt
    rw [← iteratedDeriv_succ] at h
    exact h
  have hpow : HasDerivAt (fun s : ℝ => s ^ (q - 2 * m + j))
      (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1)) r := by
    simpa using hasDerivAt_pow (q - 2 * m + j) r
  have hmul := hpow.mul hderivj
  have hquot := hmul.deriv
  change deriv ((fun s => s ^ (q - 2 * m + j)) * iteratedDeriv j φ) r / r = _
  rw [hquot]
  have he : q - 2 * m + j = (q - 2 * (m + 1) + j) + 2 := by omega
  have he' : q - 2 * m + j - 1 = (q - 2 * (m + 1) + j) + 1 := by omega
  have he'' : q - 2 * (m + 1) + (j + 1) = (q - 2 * (m + 1) + j) + 1 := by omega
  rw [he', he, he'']
  field_simp [ne_of_gt hr]
  simp [pow_add, pow_succ]
  ring

lemma hasDerivAt_pow_mul_iteratedDeriv_at_of_order
    {m q j : ℕ} {φ : ℝ → ℝ} {r : ℝ}
    (hφ : ContDiffAt ℝ (m + 1) φ r) (hj : j ≤ m) :
    HasDerivAt (fun s => s ^ (q - 2 * m + j) * iteratedDeriv j φ s)
      (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1) *
          iteratedDeriv j φ r +
        r ^ (q - 2 * m + j) * iteratedDeriv (j + 1) φ r) r := by
  have hfdj : DifferentiableAt ℝ (iteratedDeriv j φ) r := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.differentiable
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm).differentiableAt.comp r
      (hφ.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j < m + 1 by omega)))
  have hderivj : HasDerivAt (iteratedDeriv j φ)
      (iteratedDeriv (j + 1) φ r) r := by
    have h := hfdj.hasDerivAt
    rw [← iteratedDeriv_succ] at h
    exact h
  have hpow : HasDerivAt (fun s : ℝ => s ^ (q - 2 * m + j))
      (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1)) r := by
    simpa using hasDerivAt_pow (q - 2 * m + j) r
  convert hpow.mul hderivj using 1 <;> rfl

/-- Historical one-term quotient rule with one additional derivative
available. -/
lemma deriv_pow_mul_iteratedDeriv_at {m q j : ℕ} {φ : ℝ → ℝ} {r : ℝ}
    (hr : 0 < r) (hφ : ContDiffAt ℝ (m + 2) φ r)
    (hj : j ≤ m + 1) (hq : 2 * (m + 1) ≤ q) :
    deriv (fun s => s ^ (q - 2 * m + j) * iteratedDeriv j φ s) r / r =
      ((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * (m + 1) + j) *
          iteratedDeriv j φ r +
        r ^ (q - 2 * (m + 1) + (j + 1)) * iteratedDeriv (j + 1) φ r := by
  have hfdj : DifferentiableAt ℝ (iteratedDeriv j φ) r := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.differentiable
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm).differentiableAt.comp r
      (hφ.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j < m + 2 by omega)))
  have hderivj : HasDerivAt (iteratedDeriv j φ)
      (iteratedDeriv (j + 1) φ r) r := by
    have h := hfdj.hasDerivAt
    rw [← iteratedDeriv_succ] at h
    exact h
  have hpow : HasDerivAt (fun s : ℝ => s ^ (q - 2 * m + j))
      (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1)) r := by
    simpa using hasDerivAt_pow (q - 2 * m + j) r
  have hmul := hpow.mul hderivj
  have hquot := hmul.deriv
  change deriv ((fun s => s ^ (q - 2 * m + j)) * iteratedDeriv j φ) r / r = _
  rw [hquot]
  have he : q - 2 * m + j = (q - 2 * (m + 1) + j) + 2 := by omega
  have he' : q - 2 * m + j - 1 = (q - 2 * (m + 1) + j) + 1 := by omega
  have he'' : q - 2 * (m + 1) + (j + 1) = (q - 2 * (m + 1) + j) + 1 := by omega
  rw [he', he, he'']
  field_simp [ne_of_gt hr]
  simp [pow_add, pow_succ]
  ring

/-- Historical one-term product rule with one additional derivative
available. -/
lemma hasDerivAt_pow_mul_iteratedDeriv_at
    {m q j : ℕ} {φ : ℝ → ℝ} {r : ℝ}
    (hφ : ContDiffAt ℝ (m + 2) φ r) (hj : j ≤ m + 1) :
    HasDerivAt (fun s => s ^ (q - 2 * m + j) * iteratedDeriv j φ s)
      (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1) *
          iteratedDeriv j φ r +
        r ^ (q - 2 * m + j) * iteratedDeriv (j + 1) φ r) r := by
  have hfdj : DifferentiableAt ℝ (iteratedDeriv j φ) r := by
    rw [iteratedDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.differentiable
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin j) ℝ).symm).differentiableAt.comp r
      (hφ.differentiableAt_iteratedFDeriv (by exact_mod_cast (show j < m + 2 by omega)))
  have hderivj : HasDerivAt (iteratedDeriv j φ)
      (iteratedDeriv (j + 1) φ r) r := by
    have h := hfdj.hasDerivAt
    rw [← iteratedDeriv_succ] at h
    exact h
  have hpow : HasDerivAt (fun s : ℝ => s ^ (q - 2 * m + j))
      (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1)) r := by
    simpa using hasDerivAt_pow (q - 2 * m + j) r
  convert hpow.mul hderivj using 1 <;> rfl

/-! ## A finite-sum reindexing lemma -/

lemma radialCoeff_sum_step (m q : ℕ) (X : ℕ → ℝ) (hq : 2 * m ≤ q) :
    (∑ j ∈ Finset.range (m + 1),
      (((q - 2 * m + j : ℕ) : ℝ) * radialCoeff m q j * X j +
        radialCoeff m q j * X (j + 1))) =
      ∑ j ∈ Finset.range (m + 2), radialCoeff (m + 1) q j * X j := by
  rw [Finset.sum_add_distrib]
  have hA :
      (∑ j ∈ Finset.range (m + 1),
        ((q - 2 * m + j : ℕ) : ℝ) * radialCoeff m q j * X j) =
        ∑ j ∈ Finset.range (m + 2),
          ((q - 2 * m + j : ℕ) : ℝ) * radialCoeff m q j * X j := by
    symm
    rw [Finset.sum_range_succ]
    have hz : radialCoeff m q (m + 1) = 0 :=
      radialCoeff_eq_zero_of_lt m q (m + 1) (by omega)
    simp [hz]
  have hB :
      (∑ j ∈ Finset.range (m + 1), radialCoeff m q j * X (j + 1)) =
        ∑ j ∈ Finset.range (m + 2),
          (if j = 0 then 0 else radialCoeff m q (j - 1)) * X j := by
    rw [Finset.sum_range_succ' (fun j =>
      (if j = 0 then 0 else radialCoeff m q (j - 1)) * X j) (m + 1)]
    simp only [Nat.add_sub_cancel]
    simp
  rw [hA, hB, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hcast : ((q - 2 * m + j : ℕ) : ℝ) =
      (q : ℝ) - 2 * (m : ℝ) + (j : ℝ) := by
    rw [Nat.cast_add, Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast]
  rw [radialCoeff_succ]
  ring

/-! ## The general radial expansion -/

/-- Iterating `r⁻¹ d/dr` `m` times on `r^q φ` uses exactly `m` derivatives of
`φ`. The condition `2*m ≤ q` ensures that all exponents remain natural. -/
theorem radialIter_pow_mul_expansion_of_order (m q : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ m φ) (hq : 2 * m ≤ q) {r : ℝ} (hr : 0 < r) :
    radialIter m (fun s => s ^ q * φ s) r =
      ∑ j ∈ Finset.range (m + 1),
        radialCoeff m q j * r ^ (q - 2 * m + j) * iteratedDeriv j φ r := by
  induction m generalizing q φ r with
  | zero =>
      simp [radialIter, radialCoeff]
  | succ m ih =>
      have hqm : 2 * m ≤ q := by omega
      have hφm : ContDiff ℝ m φ := by
        apply hφ.of_le
        exact_mod_cast (Nat.le_succ m)
      let S : ℝ → ℝ := fun s =>
        ∑ j ∈ Finset.range (m + 1),
          radialCoeff m q j * s ^ (q - 2 * m + j) * iteratedDeriv j φ s
      have heq : radialIter m (fun s => s ^ q * φ s) =ᶠ[nhds r] S := by
        filter_upwards [Ioi_mem_nhds hr] with s hs
        exact ih q hφm hqm hs
      rw [radialIter_succ, radialOp, heq.deriv_eq]
      have hS : HasDerivAt S
          (∑ j ∈ Finset.range (m + 1),
            radialCoeff m q j *
              (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1) *
                  iteratedDeriv j φ r +
                r ^ (q - 2 * m + j) * iteratedDeriv (j + 1) φ r)) r := by
        dsimp only [S]
        apply HasDerivAt.fun_sum
        intro j hj
        have hjle : j ≤ m := by simpa using Finset.mem_range.mp hj
        simpa only [mul_assoc] using
          (hasDerivAt_pow_mul_iteratedDeriv_at_of_order (m := m) (q := q) (j := j)
            hφ.contDiffAt (by omega)).const_mul (radialCoeff m q j)
      rw [hS.deriv, Finset.sum_div]
      let X : ℕ → ℝ := fun j =>
        r ^ (q - 2 * (m + 1) + j) * iteratedDeriv j φ r
      calc
        ∑ j ∈ Finset.range (m + 1),
            (radialCoeff m q j *
              (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1) *
                  iteratedDeriv j φ r +
                r ^ (q - 2 * m + j) * iteratedDeriv (j + 1) φ r)) / r =
            ∑ j ∈ Finset.range (m + 1),
              (((q - 2 * m + j : ℕ) : ℝ) * radialCoeff m q j * X j +
                radialCoeff m q j * X (j + 1)) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hjle : j ≤ m := by simpa using Finset.mem_range.mp hj
          have hterm := hasDerivAt_pow_mul_iteratedDeriv_at_of_order
            (m := m) (q := q) (j := j)
            (r := r) hφ.contDiffAt (by omega)
          have hterm_deriv := hterm.deriv
          have hrad := deriv_pow_mul_iteratedDeriv_at_of_order
            hr hφ.contDiffAt (by omega) hq
            (m := m) (q := q) (j := j)
          dsimp only [X]
          calc
            (radialCoeff m q j *
                (((q - 2 * m + j : ℕ) : ℝ) * r ^ (q - 2 * m + j - 1) *
                    iteratedDeriv j φ r +
                  r ^ (q - 2 * m + j) * iteratedDeriv (j + 1) φ r)) / r =
                radialCoeff m q j * (deriv
                  (fun s => s ^ (q - 2 * m + j) * iteratedDeriv j φ s) r) / r := by
              rw [hterm_deriv]
            _ = radialCoeff m q j *
                (deriv (fun s => s ^ (q - 2 * m + j) * iteratedDeriv j φ s) r / r) := by
              ring
            _ = radialCoeff m q j *
                (↑(q - 2 * m + j) * r ^ (q - 2 * (m + 1) + j) *
                    iteratedDeriv j φ r +
                  r ^ (q - 2 * (m + 1) + (j + 1)) *
                    iteratedDeriv (j + 1) φ r) := by rw [hrad]
            _ = (((q - 2 * m + j : ℕ) : ℝ) * radialCoeff m q j * X j +
                radialCoeff m q j * X (j + 1)) := by ring
        _ = ∑ j ∈ Finset.range (m + 2), radialCoeff (m + 1) q j * X j :=
          radialCoeff_sum_step m q X hqm
        _ = ∑ j ∈ Finset.range (m + 2),
            radialCoeff (m + 1) q j *
              r ^ (q - 2 * (m + 1) + j) * iteratedDeriv j φ r := by
          simp [X, mul_assoc]

/-- Backwards-compatible form of `radialIter_pow_mul_expansion_of_order` with
one additional derivative available. -/
theorem radialIter_pow_mul_expansion (m q : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (m + 1 : ℕ) φ) (hq : 2 * m ≤ q) {r : ℝ} (hr : 0 < r) :
    radialIter m (fun s => s ^ q * φ s) r =
      ∑ j ∈ Finset.range (m + 1),
        radialCoeff m q j * r ^ (q - 2 * m + j) * iteratedDeriv j φ r := by
  apply radialIter_pow_mul_expansion_of_order m q
  · exact hφ.of_le (by exact_mod_cast (show m ≤ m + 1 by omega))
  · exact hq
  · exact hr

/-! ## Evans' coefficients: identities (ii) and (iii) -/

/-- The coefficient `β_j^k` in Evans' radial identity. -/
def evansRadialCoeff (k j : ℕ) : ℝ := radialCoeff (k - 1) (2 * k - 1) j

/-- Sharp finite-order form of Evans' identity (ii): `k-1` radial operators
use only the first `k-1` derivatives of `φ`. -/
theorem waveRadial_expansion_of_order {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (k - 1 : ℕ) φ) {r : ℝ} (hr : 0 < r) :
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) * φ s) r =
      ∑ j ∈ Finset.range k,
        evansRadialCoeff k j * r ^ (j + 1) * iteratedDeriv j φ r := by
  have hm : k - 1 + 1 = k := by omega
  have hq : 2 * (k - 1) ≤ 2 * k - 1 := by omega
  have hgen := radialIter_pow_mul_expansion_of_order (k - 1) (2 * k - 1)
    (hm ▸ hφ) hq hr
  rw [hm] at hgen
  simpa only [evansRadialCoeff] using hgen.trans (by
    apply Finset.sum_congr rfl
    intro j hj
    have he : 2 * k - 1 - 2 * (k - 1) + j = j + 1 := by omega
    rw [he])

/-- Evans' identity (ii), retaining the historical `C^k` interface. -/
theorem waveRadial_expansion {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ k φ) {r : ℝ} (hr : 0 < r) :
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) * φ s) r =
      ∑ j ∈ Finset.range k,
        evansRadialCoeff k j * r ^ (j + 1) * iteratedDeriv j φ r :=
  waveRadial_expansion_of_order hk
    (hφ.of_le (by exact_mod_cast (show k - 1 ≤ k by omega))) hr

/-- The finite-sum extension of Evans's odd-dimensional radial transform.
Unlike `radialIter`, this formula is regular at the origin and agrees with the
singular expression at every positive radius. -/
def waveRadialExtension (k : ℕ) (φ : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ j ∈ Finset.range k,
    evansRadialCoeff k j * r ^ (j + 1) * iteratedDeriv j φ r

/-- The regular finite-sum extension agrees with Evans's iterated radial
operator away from the origin. -/
theorem waveRadialExtension_eq_radialIter {k : ℕ} (hk : 1 ≤ k)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ k φ) {r : ℝ} (hr : 0 < r) :
    waveRadialExtension k φ r =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) * φ s) r :=
  (waveRadial_expansion hk hφ hr).symm

/-- The regular radial extension vanishes at the origin. -/
@[simp] theorem waveRadialExtension_zero (k : ℕ) (φ : ℝ → ℝ) :
    waveRadialExtension k φ 0 = 0 := by
  simp [waveRadialExtension]

/-- The regular radial extension retains every differentiability order `q`
available after taking the highest profile derivative in its finite sum. -/
theorem waveRadialExtension_contDiff_of_order {k q : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (k + q - 1 : ℕ) φ) :
    ContDiff ℝ q (waveRadialExtension k φ) := by
  unfold waveRadialExtension
  apply ContDiff.sum
  intro j hj
  have hjlt : j < k := Finset.mem_range.mp hj
  have hiter : ContDiff ℝ q (iteratedDeriv j φ) := by
    rw [iteratedDeriv_eq_iterate]
    exact ContDiff.iterate_deriv' q j (hφ.of_le (by
      exact_mod_cast (show q + j ≤ k + q - 1 by omega)))
  exact (contDiff_const.mul (contDiff_id.pow (j + 1))).mul hiter

/-- The zero-th coefficient of the general radial expansion is the descending
product of the monomial exponents encountered by the operator. -/
theorem radialCoeff_zero_eq_prod (m q : ℕ) :
    radialCoeff m q 0 =
      ∏ i ∈ Finset.range m, ((q : ℝ) - 2 * (i : ℝ)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [radialCoeff_succ_zero, ih, Finset.prod_range_succ]
      ring

/-- The odd product `1 * 3 * ... * (2*k-1)`, written in the descending order
generated by repeated radial differentiation.  The factor `1` is omitted, as
it does not change the product. -/
def evansOddProduct (k : ℕ) : ℝ :=
  ∏ i ∈ Finset.range (k - 1), (2 * (k : ℝ) - 1 - 2 * (i : ℝ))

/-- Evans' identity (iii), first in the literal product form: `β_0^k` is the
product of the odd integers through `2*k-1`. -/
theorem evansRadialCoeff_zero_eq_oddProduct {k : ℕ} (hk : 1 ≤ k) :
    evansRadialCoeff k 0 = evansOddProduct k := by
  rw [evansRadialCoeff, radialCoeff_zero_eq_prod, evansOddProduct]
  apply Finset.prod_congr rfl
  intro i hi
  have hcast : ((2 * k - 1 : ℕ) : ℝ) = 2 * (k : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  simpa using hcast

/-- The derivative at the origin of the regular radial extension is Evans's
odd product times the center value of the profile. -/
theorem deriv_waveRadialExtension_zero {k : ℕ} (hk : 1 ≤ k)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ k φ) :
    deriv (waveRadialExtension k φ) 0 = evansOddProduct k * φ 0 := by
  have hsum : HasDerivAt (waveRadialExtension k φ)
      (∑ j ∈ Finset.range k,
        evansRadialCoeff k j *
          (((j + 1 : ℕ) : ℝ) * 0 ^ j * iteratedDeriv j φ 0 +
            0 ^ (j + 1) * deriv (iteratedDeriv j φ) 0)) 0 := by
    apply HasDerivAt.fun_sum
    intro j hj
    have hjlt : j < k := Finset.mem_range.mp hj
    have hiter : Differentiable ℝ (iteratedDeriv j φ) :=
      ContDiff.differentiable_iteratedDeriv j hφ (by exact_mod_cast hjlt)
    simpa only [waveRadialExtension, Pi.mul_apply, Nat.add_sub_cancel, mul_assoc] using
      ((hasDerivAt_pow (j + 1) (0 : ℝ)).mul
        (hiter 0).hasDerivAt).const_mul (evansRadialCoeff k j)
  rw [hsum.deriv]
  have hzero_mem : 0 ∈ Finset.range k := Finset.mem_range.mpr (by omega)
  rw [Finset.sum_eq_single 0]
  · simp [evansRadialCoeff_zero_eq_oddProduct hk]
  · intro j hj hj0
    simp [hj0]
  · intro h
    exact (h hzero_mem).elim

/-- If the profile has zero first derivative at the origin, then the regular
radial extension has zero second derivative there.  Only the terms with
radial powers one and two can contribute, and both contributions are
multiples of the profile's first derivative. -/
theorem iteratedDeriv_two_waveRadialExtension_zero {k : ℕ} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (k + 1 : ℕ) φ)
    (hφzero : deriv φ 0 = 0) :
    iteratedDeriv 2 (waveRadialExtension k φ) 0 = 0 := by
  unfold waveRadialExtension
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_eq_zero
    intro j hj
    have hjlt : j < k := Finset.mem_range.mp hj
    have hiter : ContDiff ℝ 2 (iteratedDeriv j φ) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv' 2 j (hφ.of_le (by
        exact_mod_cast (show 2 + j ≤ k + 1 by omega)))
    rw [show (fun r => evansRadialCoeff k j * r ^ (j + 1) *
        iteratedDeriv j φ r) =
        fun r => evansRadialCoeff k j *
          (r ^ (j + 1) * iteratedDeriv j φ r) by
      funext r
      ring]
    rw [iteratedDeriv_const_mul_field]
    change evansRadialCoeff k j *
      iteratedDeriv 2 ((fun r : ℝ => r ^ (j + 1)) * iteratedDeriv j φ) 0 = 0
    rw [iteratedDeriv_mul (n := 2) (x := (0 : ℝ))
      (f := fun r : ℝ => r ^ (j + 1)) (g := iteratedDeriv j φ)
      (contDiff_id.pow (j + 1)).contDiffAt hiter.contDiffAt]
    apply mul_eq_zero_of_right
    obtain _ | j := j
    · simp [iteratedDeriv_fun_id_zero, iteratedDeriv_one, hφzero]
    obtain _ | j := j
    · simp [Finset.sum_range_succ, iteratedDeriv_pow,
        iteratedDeriv_one, hφzero]
    simp [Finset.sum_range_succ, iteratedDeriv_pow]
  · intro j hj
    have hjlt : j < k := Finset.mem_range.mp hj
    have hiter : ContDiff ℝ 2 (iteratedDeriv j φ) := by
      rw [iteratedDeriv_eq_iterate]
      exact ContDiff.iterate_deriv' 2 j (hφ.of_le (by
        exact_mod_cast (show 2 + j ≤ k + 1 by omega)))
    exact ((contDiff_const.mul (contDiff_id.pow (j + 1))).mul hiter).contDiffAt

lemma evansOddProduct_succ {k : ℕ} (hk : 1 ≤ k) :
    evansOddProduct (k + 1) = (2 * (k : ℝ) + 1) * evansOddProduct k := by
  rw [evansOddProduct, evansOddProduct]
  have hk1 : k + 1 - 1 = k := by omega
  rw [hk1]
  rw [show Finset.range k = Finset.range ((k - 1) + 1) by congr 1; omega]
  rw [Finset.prod_range_succ']
  have hshift :
      (∏ i ∈ Finset.range (k - 1),
        (2 * ((k + 1 : ℕ) : ℝ) - 1 - 2 * (((i + 1 : ℕ) : ℝ)))) =
      ∏ i ∈ Finset.range (k - 1), (2 * (k : ℝ) - 1 - 2 * (i : ℝ)) := by
    apply Finset.prod_congr rfl
    intro i hi
    push_cast
    ring
  rw [hshift]
  push_cast
  ring

/-- The descending odd product agrees with mathlib's double factorial. -/
theorem evansOddProduct_eq_doubleFactorial (n : ℕ) :
    evansOddProduct (n + 1) = ((Nat.doubleFactorial (2 * (n + 1) - 1) : ℕ) : ℝ) := by
  induction n with
  | zero => simp [evansOddProduct]
  | succ n ih =>
      rw [evansOddProduct_succ (show 1 ≤ n + 1 by omega), ih]
      have hindex : 2 * (n + 1 + 1) - 1 = (2 * (n + 1) - 1) + 2 := by omega
      rw [hindex, Nat.doubleFactorial_add_two]
      push_cast
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * (n + 1))]
      push_cast
      ring

/-- Evans' identity (iii) in standard notation:
`β_0^k = (2*k-1)‼ = 1 * 3 * ... * (2*k-1)`. -/
theorem evansRadialCoeff_zero_eq_doubleFactorial {k : ℕ} (hk : 1 ≤ k) :
    evansRadialCoeff k 0 = ((Nat.doubleFactorial (2 * k - 1) : ℕ) : ℝ) := by
  rw [evansRadialCoeff_zero_eq_oddProduct hk]
  have hk' : k - 1 + 1 = k := by omega
  simpa only [hk'] using evansOddProduct_eq_doubleFactorial (k - 1)

/-! ## The second-derivative intertwining identity -/

lemma radialIter_succ_right (m : ℕ) (f : ℝ → ℝ) :
    radialIter (m + 1) f = radialIter m (radialOp f) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change radialOp (radialIter (m + 1) f) = radialOp (radialIter m (radialOp f))
      rw [ih]

/-- Equality on the positive half-line is preserved by every iterate of the
radial operator. Derivatives only require equality on a neighborhood of the
positive evaluation point. -/
lemma radialIter_congr_Ioi (m : ℕ) {f g : ℝ → ℝ}
    (hfg : Set.EqOn f g (Set.Ioi 0)) :
    Set.EqOn (radialIter m f) (radialIter m g) (Set.Ioi 0) := by
  induction m with
  | zero => simpa only [radialIter_zero] using hfg
  | succ m ih =>
      intro r hr
      rw [radialIter_succ, radialIter_succ, radialOp, radialOp]
      have heq : radialIter m f =ᶠ[nhds r] radialIter m g := by
        filter_upwards [Ioi_mem_nhds hr] with s hs
        exact ih hs
      rw [heq.deriv_eq]

lemma radialOp_pow_mul_eq (q : ℕ) (hq : 3 ≤ q) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) :
    radialOp (fun r => r ^ q * φ r) = fun r =>
      (q : ℝ) * r ^ (q - 2) * φ r + r ^ (q - 1) * deriv φ r := by
  funext r
  have hφ' : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hprod := (hasDerivAt_pow q r).mul (hφ' r).hasDerivAt
  rw [radialOp]
  change deriv ((fun x => x ^ q) * φ) r / r = _
  rw [hprod.deriv]
  by_cases hr : r = 0
  · subst r
    have hq1 : q - 1 ≠ 0 := by omega
    have hq2 : q - 2 ≠ 0 := by omega
    simp [hq1, hq2]
  · have he1 : q - 1 = (q - 2) + 1 := by omega
    have he2 : q = (q - 1) + 1 := by omega
    rw [he1, he2, pow_succ, pow_succ]
    field_simp [hr]
    have he3 : q - 1 + 1 - 2 = q - 2 := by omega
    rw [he3]
    have hp : r ^ (q - 1) = r * r ^ (q - 2) := by
      rw [show q - 1 = 1 + (q - 2) by omega, pow_add]
      simp [pow_one]
    rw [hp]
    ring

lemma waveRadial_step (m : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) :
    radialIter (m + 1) (fun r => r ^ (2 * m + 3) * φ r) =
      radialIter m (fun r =>
        r ^ (2 * m + 1) * ((2 * m + 3 : ℝ) * φ r + r * deriv φ r)) := by
  rw [radialIter_succ_right, radialOp_pow_mul_eq (2 * m + 3) (by omega) hφ]
  congr 1
  funext r
  have he1 : 2 * m + 3 - 2 = 2 * m + 1 := by omega
  have he2 : 2 * m + 3 - 1 = (2 * m + 1) + 1 := by omega
  rw [he1, he2, pow_succ]
  push_cast
  ring

lemma deriv_waveRadial_profile (m : ℕ) {φ : ℝ → ℝ} (hφ : ContDiff ℝ 3 φ) :
    deriv (fun r => (2 * m + 3 : ℝ) * φ r + r * deriv φ r) =
      fun r => (2 * m + 4 : ℝ) * deriv φ r + r * deriv (deriv φ) r := by
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ2 : Differentiable ℝ (deriv φ) :=
    (hφ.of_le (by norm_num)).differentiable_deriv_two
  funext r
  have hleft : HasDerivAt (fun s => (2 * m + 3 : ℝ) * φ s)
      ((2 * m + 3 : ℝ) * deriv φ r) r :=
    (hφ1 r).hasDerivAt.const_mul _
  have hright : HasDerivAt (fun s => s * deriv φ s)
      (deriv φ r + r * deriv (deriv φ) r) r := by
    convert (hasDerivAt_id r).mul (hφ2 r).hasDerivAt using 1 <;> first | rfl | simp
  change deriv ((fun s => (2 * m + 3 : ℝ) * φ s) +
      (fun s => s * deriv φ s)) r = _
  rw [(hleft.add hright).deriv]
  ring

/-- The second derivative intertwines consecutive radial operators.  This is
Evans' useful identity (i), indexed here by the number of radial operators on
the left-hand side. -/
theorem radialIter_second_deriv (m : ℕ) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (m + 2 : ℕ) φ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (radialIter m (fun s => s ^ (2 * m + 1) * φ s))) r =
      radialIter (m + 1) (fun s => s ^ (2 * m + 2) * deriv φ s) r := by
  induction m generalizing φ r with
  | zero =>
      have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
      have hφ2 : Differentiable ℝ (deriv φ) := hφ.differentiable_deriv_two
      have hfirst : deriv (fun s => s * φ s) = fun s => φ s + s * deriv φ s := by
        funext s
        convert ((hasDerivAt_id s).mul (hφ1 s).hasDerivAt).deriv using 1 <;>
          first | rfl | simp
      have hsecond : HasDerivAt (fun s => φ s + s * deriv φ s)
          (2 * deriv φ r + r * deriv (deriv φ) r) r := by
        convert (hφ1 r).hasDerivAt.add
          ((hasDerivAt_id r).mul (hφ2 r).hasDerivAt) using 1 <;>
          first | rfl | simp [two_mul, add_assoc]
      have hright : HasDerivAt (fun s => s ^ 2 * deriv φ s)
          (2 * r * deriv φ r + r ^ 2 * deriv (deriv φ) r) r := by
        convert (hasDerivAt_pow 2 r).mul (hφ2 r).hasDerivAt using 1 <;>
          first | rfl | simp
      rw [show 2 * 0 + 1 = 1 by omega, show 2 * 0 + 2 = 2 by omega]
      rw [radialIter_zero, radialIter_succ, radialIter_zero, radialOp]
      simp only [pow_one]
      rw [hfirst, hsecond.deriv, hright.deriv]
      field_simp [ne_of_gt hr]
  | succ m ih =>
      have hφ2 : ContDiff ℝ 2 φ := by
        apply hφ.of_le
        exact_mod_cast (show 2 ≤ m + 1 + 2 by omega)
      have hφlow : ContDiff ℝ (m + 2 : ℕ) φ := by
        apply hφ.of_le
        exact_mod_cast (show m + 2 ≤ m + 1 + 2 by omega)
      have hφderiv : ContDiff ℝ (m + 2 : ℕ) (deriv φ) := by
        have hs : ContDiff ℝ ((m + 2 : ℕ) + 1) φ := by
          exact hφ
        exact (contDiff_succ_iff_deriv.mp hs).2.2
      have hψ : ContDiff ℝ (m + 2 : ℕ)
          (fun s => (2 * m + 3 : ℝ) * φ s + s * deriv φ s) :=
        (contDiff_const.mul hφlow).add (contDiff_id.mul hφderiv)
      have hexp1 : 2 * (m + 1) + 1 = 2 * m + 3 := by omega
      have hexp2 : 2 * (m + 1) + 2 = 2 * m + 4 := by omega
      have hiter : m + 1 + 1 = m + 2 := by omega
      rw [hexp1, hexp2, hiter]
      rw [waveRadial_step m hφ2]
      rw [ih hψ hr]
      rw [deriv_waveRadial_profile m (hφ.of_le (by
        exact_mod_cast (show 3 ≤ m + 1 + 2 by omega)))]
      rw [radialIter_succ_right (m + 1)]
      have hφderiv2 : ContDiff ℝ 2 (deriv φ) := by
        apply hφderiv.of_le
        exact_mod_cast (show 2 ≤ m + 2 by omega)
      rw [radialOp_pow_mul_eq (2 * m + 4) (by omega) hφderiv2]
      congr 2
      funext s
      have he2 : 2 * m + 4 - 2 = 2 * m + 2 := by omega
      have he3 : 2 * m + 4 - 1 = 2 * m + 3 := by omega
      have he : 2 * m + 3 = (2 * m + 2) + 1 := by omega
      rw [he2, he3, he, pow_succ]
      push_cast
      ring

/-- Evans' useful identity (i): two ordinary derivatives of the transformed
radial profile equal one further application of `r⁻¹ d/dr` to the derivative
profile. -/
theorem waveRadial_second_deriv {k : ℕ} (hk : 1 ≤ k) {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ (k + 1 : ℕ) φ) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (radialIter (k - 1) (fun s => s ^ (2 * k - 1) * φ s))) r =
      radialIter k (fun s => s ^ (2 * k) * deriv φ s) r := by
  have hm : k - 1 + 1 = k := by omega
  have hleft : 2 * (k - 1) + 1 = 2 * k - 1 := by omega
  have hright : 2 * (k - 1) + 2 = 2 * k := by omega
  have hφm : ContDiff ℝ (k - 1 + 2 : ℕ) φ := by
    rw [show k - 1 + 2 = k + 1 by omega]
    exact hφ
  simpa only [hm, hleft, hright] using radialIter_second_deriv (k - 1) hφm hr

/-- The algebraic core of the odd-dimensional Euler--Poisson--Darboux
transformation. If the divergence-form radial equation identifies
`radialOp (r^(2k) φ')` with `r^(2k-1) ψ` on positive radii, then Evans's
transformed profile has second derivative equal to the transform of `ψ`. -/
theorem waveRadial_transform_of_epd {k : ℕ} (hk : 1 ≤ k) {φ ψ : ℝ → ℝ}
    (hφ : ContDiff ℝ (k + 1 : ℕ) φ)
    (hEPD : ∀ s, 0 < s →
      radialOp (fun z => z ^ (2 * k) * deriv φ z) s =
        s ^ (2 * k - 1) * ψ s)
    {r : ℝ} (hr : 0 < r) :
    deriv (deriv (radialIter (k - 1)
      (fun s => s ^ (2 * k - 1) * φ s))) r =
      radialIter (k - 1) (fun s => s ^ (2 * k - 1) * ψ s) r := by
  calc
    deriv (deriv (radialIter (k - 1)
        (fun s => s ^ (2 * k - 1) * φ s))) r =
        radialIter k (fun s => s ^ (2 * k) * deriv φ s) r :=
      waveRadial_second_deriv hk hφ hr
    _ = radialIter (k - 1)
        (radialOp (fun s => s ^ (2 * k) * deriv φ s)) r := by
      simpa only [Nat.sub_add_cancel hk] using congrFun
        (radialIter_succ_right (k - 1)
          (fun s => s ^ (2 * k) * deriv φ s)) r
    _ = radialIter (k - 1) (fun s => s ^ (2 * k - 1) * ψ s) r :=
      radialIter_congr_Ioi (k - 1) (fun s hs => hEPD s hs) hr

/-- The odd-dimensional radial transform vanishes at the singular radius.  For
`k = 1` this is the explicit factor `r`; for larger `k`, the outermost
`radialOp` is defined to be zero at `r = 0`. -/
theorem waveRadial_transform_zero {k : ℕ} (hk : 1 ≤ k) (φ : ℝ → ℝ) :
    radialIter (k - 1) (fun s => s ^ (2 * k - 1) * φ s) 0 = 0 := by
  obtain rfl | k := k
  · omega
  cases k with
  | zero => simp
  | succ k => simp [radialOp]

end EvansLib

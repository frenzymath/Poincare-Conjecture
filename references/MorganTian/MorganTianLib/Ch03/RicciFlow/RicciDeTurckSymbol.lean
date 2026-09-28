import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Morgan--Tian Ch. 3 -- the Ricci--DeTurck principal symbol

The harmonic-coordinate discussion preceding the local existence theorem has a
finite-dimensional core.  In a fixed frame, the Ricci symbol has a gauge
kernel, while the DeTurck correction cancels the gauge terms and leaves the
scalar symbol `|xi|^2`.  This file records that algebra exactly.  It does not
claim the missing chart linearisation or the analytic parabolic existence
theorem.

The calculation follows the fixed-frame expansion used in the corresponding
Ricci-flow existence arguments in Chow--Knopf and Topping.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace MorganTianLib

/-! ## Fixed-frame symbols -/

/-- **Math.** A covector in an `n`-dimensional fixed frame. -/
abbrev RicciCovector (n : ℕ) := Fin n → ℝ

/-- **Math.** The squared Euclidean norm of a fixed-frame covector. -/
def ricciCovectorNormSq {n : ℕ} (xi : RicciCovector n) : ℝ :=
  ∑ k, xi k ^ 2

/-! The finite-dimensional test-tensor norm used by the strict-parabolic
coercivity statement below.  We index entries by the product so that the
positivity argument has one finite sum rather than an implicit norm choice. -/

def ricciMatrixNormSq {n : ℕ} (h : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ ij : Fin n × Fin n, h ij.1 ij.2 ^ 2

def ricciMatrixPairing {n : ℕ}
    (h k : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ ij : Fin n × Fin n, h ij.1 ij.2 * k ij.1 ij.2

theorem ricciCovectorNormSq_nonneg {n : ℕ} (xi : RicciCovector n) :
    0 ≤ ricciCovectorNormSq xi := by
  classical
  exact Finset.sum_nonneg (fun k _ => sq_nonneg (xi k))

theorem ricciCovectorNormSq_pos {n : ℕ} {xi : RicciCovector n}
    (hxi : xi ≠ 0) : 0 < ricciCovectorNormSq xi := by
  classical
  have hex : ∃ k : Fin n, xi k ≠ 0 := by
    by_contra h
    push Not at h
    apply hxi
    funext k
    exact h k
  exact Finset.sum_pos' (fun k _ => sq_nonneg (xi k))
    (by
      obtain ⟨k, hk⟩ := hex
      have hsq : 0 < xi k ^ 2 := by
        rcases lt_or_gt_of_ne hk with hkneg | hkpos <;>
          nlinarith [sq_nonneg (xi k)]
      exact ⟨k, Finset.mem_univ _, hsq⟩)

theorem ricciMatrixNormSq_nonneg {n : ℕ}
    (h : Matrix (Fin n) (Fin n) ℝ) : 0 ≤ ricciMatrixNormSq h := by
  classical
  exact Finset.sum_nonneg (fun ij _ => sq_nonneg (h ij.1 ij.2))

theorem ricciMatrixNormSq_pos {n : ℕ} {h : Matrix (Fin n) (Fin n) ℝ}
    (hh : h ≠ 0) : 0 < ricciMatrixNormSq h := by
  classical
  have hex : ∃ ij : Fin n × Fin n, h ij.1 ij.2 ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hh
    ext i j
    exact h' (i, j)
  exact Finset.sum_pos' (fun ij _ => sq_nonneg (h ij.1 ij.2))
    (by
      obtain ⟨ij, hij⟩ := hex
      have hsq : 0 < h ij.1 ij.2 ^ 2 := by
        rcases lt_or_gt_of_ne hij with hneg | hpos <;>
          nlinarith [sq_nonneg (h ij.1 ij.2)]
      exact ⟨ij, Finset.mem_univ _, hsq⟩)

/-- **Math.** The raw Ricci principal symbol in a fixed frame. -/
def ricciLinearisationSymbol {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    ricciCovectorNormSq xi * h i j
      - xi i * (∑ k, h k j * xi k)
      - xi j * (∑ k, h i k * xi k)
      + xi i * xi j * (∑ k, h k k)

/-- **Math.** The gauge contribution in the raw Ricci symbol. -/
def ricciGaugeSymbol {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    -xi i * (∑ k, h k j * xi k)
      - xi j * (∑ k, h i k * xi k)
      + xi i * xi j * (∑ k, h k k)

/-- **Math.** The DeTurck correction cancels the gauge contribution. -/
def deTurckGaugeCancellationSymbol {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => -ricciGaugeSymbol xi h i j

/-- **Math.** The corrected Ricci--DeTurck principal symbol. -/
def deTurckLinearisationSymbol {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ricciLinearisationSymbol xi h i j +
    deTurckGaugeCancellationSymbol xi h i j

@[simp] theorem ricciLinearisationSymbol_apply {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ricciLinearisationSymbol xi h i j =
      ricciCovectorNormSq xi * h i j
        - xi i * (∑ k, h k j * xi k)
        - xi j * (∑ k, h i k * xi k)
        + xi i * xi j * (∑ k, h k k) :=
  rfl

@[simp] theorem ricciGaugeSymbol_apply {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ricciGaugeSymbol xi h i j =
      -xi i * (∑ k, h k j * xi k)
        - xi j * (∑ k, h i k * xi k)
        + xi i * xi j * (∑ k, h k k) :=
  rfl

/-- **Math.** The raw Ricci symbol vanishes on the rank-one gauge direction `xi ⊗ xi`.
This is the fixed-frame obstruction to strict parabolicity before gauge fixing.
-/
theorem ricciLinearisationSymbol_rankOne {n : ℕ} (xi : RicciCovector n) :
    ricciLinearisationSymbol xi (fun i j => xi i * xi j) = 0 := by
  classical
  ext i j
  simp only [ricciLinearisationSymbol, ricciCovectorNormSq, Matrix.zero_apply]
  have hleft :
      (∑ k, xi k ^ 2) * (xi i * xi j) =
        xi i * (xi j * ∑ k, xi k ^ 2) := by
    ring
  have hright :
      xi i * (∑ k, xi k * xi j * xi k) =
        xi i * (xi j * ∑ k, xi k ^ 2) := by
    congr 1
    calc
      ∑ k, xi k * xi j * xi k = ∑ k, xi j * (xi k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = xi j * ∑ k, xi k ^ 2 := by rw [Finset.mul_sum]
  have hmiddle :
      xi j * (∑ k, xi i * xi k * xi k) =
        xi j * (xi i * ∑ k, xi k ^ 2) := by
    congr 1
    calc
      ∑ k, xi i * xi k * xi k = ∑ k, xi i * (xi k ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ = xi i * ∑ k, xi k ^ 2 := by rw [Finset.mul_sum]
  have hsum : (∑ k, xi k * xi k) = ∑ k, xi k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hright, hmiddle, hsum]
  ring

/-! An infinitesimal diffeomorphism direction is in the same gauge kernel. -/
theorem ricciLinearisationSymbol_gaugeKernel {n : ℕ}
    (xi omega : RicciCovector n) :
    ricciLinearisationSymbol xi
      (fun i j => xi i * omega j + omega i * xi j) = 0 := by
  classical
  ext i j
  simp only [ricciLinearisationSymbol, ricciCovectorNormSq, Matrix.zero_apply]
  let a : ℝ := ∑ k, xi k * omega k
  have hxx : (∑ k, xi k * xi k) = ∑ k, xi k ^ 2 := by
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hox : (∑ k, omega k * xi k) = a := by
    dsimp only [a]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hcol :
      (∑ k, (xi k * omega j + omega k * xi j) * xi k) =
        omega j * (∑ k, xi k ^ 2) + xi j * a := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    calc
      (∑ k, xi k * omega j * xi k) + ∑ k, omega k * xi j * xi k
          = omega j * (∑ k, xi k * xi k) +
              xi j * (∑ k, omega k * xi k) := by
              congr 1 <;> rw [Finset.mul_sum]
              · apply Finset.sum_congr rfl
                intro k hk
                ring
              · apply Finset.sum_congr rfl
                intro k hk
                ring
      _ = omega j * (∑ k, xi k ^ 2) + xi j * a := by rw [hxx, hox]
  have hrow :
      (∑ k, (xi i * omega k + omega i * xi k) * xi k) =
        xi i * a + omega i * (∑ k, xi k ^ 2) := by
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    calc
      (∑ k, xi i * omega k * xi k) + ∑ k, omega i * xi k * xi k
          = xi i * (∑ k, xi k * omega k) +
              omega i * (∑ k, xi k * xi k) := by
              congr 1 <;> rw [Finset.mul_sum]
              · apply Finset.sum_congr rfl
                intro k hk
                ring
              · apply Finset.sum_congr rfl
                intro k hk
                ring
      _ = xi i * a + omega i * (∑ k, xi k ^ 2) := by
            dsimp only [a]
            rw [hxx]
  have htrace :
      (∑ k, (xi k * omega k + omega k * xi k)) = 2 * a := by
    rw [Finset.sum_add_distrib, hox]
    dsimp only [a]
    ring
  rw [hcol, hrow, htrace]
  ring

/-- **Math.** The DeTurck correction leaves the scalar symbol `|xi|² h`. -/
theorem deTurckLinearisationSymbol_eq_scalar {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    deTurckLinearisationSymbol xi h = ricciCovectorNormSq xi • h := by
  classical
  ext i j
  simp only [deTurckLinearisationSymbol, deTurckGaugeCancellationSymbol,
    ricciGaugeSymbol, ricciLinearisationSymbol, ricciCovectorNormSq,
    Matrix.smul_apply, smul_eq_mul]
  ring

/-! Pairing the corrected symbol with a test tensor exposes the positive
multiple of the identity explicitly. -/

theorem deTurckLinearisationSymbol_pairing_self {n : ℕ}
    (xi : RicciCovector n) (h : Matrix (Fin n) (Fin n) ℝ) :
    ricciMatrixPairing h (deTurckLinearisationSymbol xi h) =
      ricciCovectorNormSq xi * ricciMatrixNormSq h := by
  classical
  rw [deTurckLinearisationSymbol_eq_scalar]
  simp only [ricciMatrixPairing, ricciMatrixNormSq, Matrix.smul_apply,
    smul_eq_mul]
  calc
    (∑ ij : Fin n × Fin n,
        h ij.1 ij.2 * (ricciCovectorNormSq xi * h ij.1 ij.2)) =
        ∑ ij : Fin n × Fin n,
          ricciCovectorNormSq xi * (h ij.1 ij.2 * h ij.1 ij.2) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ricciCovectorNormSq xi *
        ∑ ij : Fin n × Fin n, h ij.1 ij.2 * h ij.1 ij.2 := by
      rw [Finset.mul_sum]
    _ = ricciCovectorNormSq xi * ricciMatrixNormSq h := by
      apply congrArg (fun z : ℝ => ricciCovectorNormSq xi * z)
      apply Finset.sum_congr rfl
      intro ij hij
      ring

/-- **Math.** In a nonzero covector direction the corrected symbol is strictly elliptic
on every matrix component; the nonzero hypothesis records the intended
principal-symbol regime. -/
theorem deTurckLinearisationSymbol_strictlyParabolic {n : ℕ}
    {xi : RicciCovector n} (_hxi : xi ≠ 0)
    (h : Matrix (Fin n) (Fin n) ℝ) :
    deTurckLinearisationSymbol xi h = ricciCovectorNormSq xi • h :=
  deTurckLinearisationSymbol_eq_scalar xi h

/-! **Math.** The fixed-frame DeTurck symbol is strictly positive on every
nonzero test tensor in every nonzero covector direction.  This is the actual
coercivity content behind the scalar-symbol identity; the chart and compact
uniformity bridges needed for Hamilton's theorem remain separate. -/
theorem deTurckLinearisationSymbol_coercive {n : ℕ}
    {xi : RicciCovector n} (hxi : xi ≠ 0)
    {h : Matrix (Fin n) (Fin n) ℝ} (hh : h ≠ 0) :
    0 < ricciMatrixPairing h (deTurckLinearisationSymbol xi h) := by
  rw [deTurckLinearisationSymbol_pairing_self]
  exact mul_pos (ricciCovectorNormSq_pos hxi) (ricciMatrixNormSq_pos hh)

end MorganTianLib

end

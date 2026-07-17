import PoincareLib.Ch01.JacobiODE
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Poincaré Ch. 1 — invertibility and inverse asymptotics of the matrix Jacobi solution

In `lem:geodesic-polar-form`(3) the matrix Jacobi field `𝒥` (the solution of
`𝒥'' + ℛ(r) 𝒥 = 0` with `𝒥(0) = 0`, `𝒥'(0) = Id` in a parallel frame) is
inverted near `r = 0`, and the shape operator `A(r) = 𝒥'(r) 𝒥(r)⁻¹` is shown
to satisfy `A(r) = (1/r)·Id + O(r)`. This file provides those two facts as
manifold-free lemmas over an arbitrary unital real Banach algebra `A`
(applied with `A = E →L[ℝ] E`), building on the small-time asymptotics of
`PoincareLib.Ch01.JacobiODE`:

* `IsJacobiSolOn.isUnit_fst` — for `0 < t` with `C M t² < 6` (where
  `M = e^{Kb}`, `K = max 1 C`), the solution value `y t` is invertible: from
  `‖y t − t·1‖ ≤ C M t³/6` the rescaling `t⁻¹ y t` is within distance `< 1`
  of `1`, hence a unit by the geometric series;
* `IsJacobiSolOn.norm_snd_mul_inverse_fst_sub_le` — for `0 < t` with
  `C M t² ≤ 3`, `‖v t · (y t)⁻¹ − t⁻¹·1‖ ≤ 2 C M t`, the
  `A(r) = (1/r)·Id + O(r)` asymptotics of `lem:geodesic-polar-form`(3).

Blueprint: `lem:jacobi-matrix-inverse`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1,
Lemma `lem:geodesic-polar-form`(3).
-/

open Set
open scoped Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]

namespace IsJacobiSolOn

variable {R : ℝ → A →L[ℝ] A} {b C : ℝ} {y v : ℝ → A}

/-- **Math.** Rescaled distance to the identity: with `y 0 = 0`, `v 0 = 1`,
`‖1 − t⁻¹ • y t‖ ≤ C M t²/6` for `t ∈ (0, b]`, where `M = e^{Kb}`,
`K = max 1 C`. Rescaling of the cubic estimate of `lem:jacobi-small-time`.
Blueprint: `lem:jacobi-matrix-inverse`. -/
theorem norm_one_sub_inv_smul_fst_le
    (h : IsJacobiSolOn R 0 b y v) (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0) (hv0 : v 0 = 1)
    {t : ℝ} (ht : t ∈ Ioc 0 b) :
    ‖1 - t⁻¹ • y t‖ ≤ C * Real.exp (max 1 C * b) * t ^ 2 / 6 := by
  have htI : t ∈ Icc 0 b := ⟨ht.1.le, ht.2⟩
  have h3 := h.norm_fst_sub_le hR hC hy0 t htI
  rw [hv0, norm_one, one_mul] at h3
  have hrw : 1 - t⁻¹ • y t = t⁻¹ • (t • (1 : A) - y t) := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ ht.1.ne', one_smul]
  rw [hrw, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht.1,
    norm_sub_rev]
  calc t⁻¹ * ‖y t - t • (1 : A)‖
      ≤ t⁻¹ * (C * Real.exp (max 1 C * b) * t ^ 3 / 6) :=
        mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr ht.1.le)
    _ = C * Real.exp (max 1 C * b) * t ^ 2 / 6 := by
        have hr : t⁻¹ * (C * Real.exp (max 1 C * b) * t ^ 3 / 6)
            = C * Real.exp (max 1 C * b) * t ^ 2 / 6 * (t⁻¹ * t) := by ring
        rw [hr, inv_mul_cancel₀ ht.1.ne', mul_one]

/-- **Math.** **Invertibility of the matrix Jacobi solution for small time**:
with `y 0 = 0`, `v 0 = 1`, the value `y t` is a unit for `t ∈ (0, b]` with
`C M t² < 6` (`M = e^{Kb}`, `K = max 1 C`): the rescaling `t⁻¹ • y t` lies
within distance `< 1` of `1`, hence is a unit by the geometric series, and
`y t` is the product of this unit with the invertible scalar `t`.

Blueprint: `lem:jacobi-matrix-inverse`. -/
theorem isUnit_fst (h : IsJacobiSolOn R 0 b y v) (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0) (hv0 : v 0 = 1)
    {t : ℝ} (ht : t ∈ Ioc 0 b)
    (hsmall : C * Real.exp (max 1 C * b) * t ^ 2 < 6) :
    IsUnit (y t) := by
  have hw := h.norm_one_sub_inv_smul_fst_le hR hC hy0 hv0 ht
  have hw1 : ‖1 - t⁻¹ • y t‖ < 1 := lt_of_le_of_lt hw (by linarith)
  have hz : IsUnit (t⁻¹ • y t) := by
    have := isUnit_one_sub_of_norm_lt_one hw1
    rwa [sub_sub_cancel] at this
  have hyt : y t = t • (t⁻¹ • y t) := by
    rw [smul_smul, mul_inv_cancel₀ ht.1.ne', one_smul]
  rw [hyt, Algebra.smul_def]
  exact ((isUnit_iff_ne_zero.mpr ht.1.ne').map (algebraMap ℝ A)).mul hz

/-- **Math.** **Inverse asymptotics of the matrix Jacobi solution**: with
`y 0 = 0`, `v 0 = 1`, for `t ∈ (0, b]` with `C M t² ≤ 3` (`M = e^{Kb}`,
`K = max 1 C`),
`‖v t · (y t)⁻¹ − t⁻¹ • 1‖ ≤ 2 C M t`.
This is the `A(r) = 𝒥'(r) 𝒥(r)⁻¹ = (1/r)·Id + O(r)` estimate of
`lem:geodesic-polar-form`(3): writing `y t = t • z` with `z = t⁻¹ • y t`,
the quadratic and cubic estimates of `lem:jacobi-small-time` give
`‖v t − z‖ ≤ (2/3) C M t²` and `‖z⁻¹‖ ≤ 2` (geometric series, since
`‖1 − z‖ ≤ 1/2`), whence
`v t (y t)⁻¹ − t⁻¹·1 = t⁻¹ • ((v t − z) z⁻¹)` has norm `≤ (4/3) C M t`.

Blueprint: `lem:jacobi-matrix-inverse`. -/
theorem norm_snd_mul_inverse_fst_sub_le
    (h : IsJacobiSolOn R 0 b y v) (hR : ContinuousOn R (Icc 0 b))
    (hC : ∀ s ∈ Icc 0 b, ‖R s‖ ≤ C) (hy0 : y 0 = 0) (hv0 : v 0 = 1)
    {t : ℝ} (ht : t ∈ Ioc 0 b)
    (hsmall : C * Real.exp (max 1 C * b) * t ^ 2 ≤ 3) :
    ‖v t * Ring.inverse (y t) - t⁻¹ • 1‖
      ≤ 2 * (C * Real.exp (max 1 C * b)) * t := by
  have htI : t ∈ Icc 0 b := ⟨ht.1.le, ht.2⟩
  set M : ℝ := Real.exp (max 1 C * b) with hM
  have hC0 : (0 : ℝ) ≤ C := (norm_nonneg (R 0)).trans (hC 0 ⟨le_rfl, ht.1.le.trans ht.2⟩)
  have hM0 : (0 : ℝ) < M := Real.exp_pos _
  set z : A := t⁻¹ • y t with hz
  set w : A := 1 - z with hwdef
  -- the rescaled solution is within 1/2 of the identity
  have hw6 : ‖w‖ ≤ C * M * t ^ 2 / 6 :=
    h.norm_one_sub_inv_smul_fst_le hR hC hy0 hv0 ht
  have hwhalf : ‖w‖ ≤ 1 / 2 := hw6.trans (by linarith)
  have hw1 : ‖w‖ < 1 := lt_of_le_of_lt hwhalf (by norm_num)
  have hzw : (1 : A) - w = z := sub_sub_cancel 1 z
  -- z is a unit with ‖z⁻¹‖ ≤ 2
  have hzu : IsUnit z := by
    have := isUnit_one_sub_of_norm_lt_one hw1
    rwa [hzw] at this
  have hinvz_eq : Ring.inverse z = ∑' n : ℕ, w ^ n := by
    rw [← hzw, ← geom_series_eq_inverse w hw1]
  have hinvz_norm : ‖Ring.inverse z‖ ≤ 2 := by
    rw [hinvz_eq]
    have := tsum_geometric_le_of_norm_lt_one w hw1
    rw [norm_one] at this
    have h2 : (1 - ‖w‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      linarith
    linarith
  -- inverse of y t via the rescaling
  have hyz : y t = t • z := by
    rw [hz, smul_smul, mul_inv_cancel₀ ht.1.ne', one_smul]
  have hmul : y t * (t⁻¹ • Ring.inverse z) = 1 := by
    rw [hyz, smul_mul_smul_comm, mul_inv_cancel₀ ht.1.ne',
      Ring.mul_inverse_cancel z hzu, one_smul]
  have huy : IsUnit (y t) := by
    rw [hyz, Algebra.smul_def]
    exact ((isUnit_iff_ne_zero.mpr ht.1.ne').map (algebraMap ℝ A)).mul hzu
  have hinv_y : Ring.inverse (y t) = t⁻¹ • Ring.inverse z := by
    calc Ring.inverse (y t)
        = Ring.inverse (y t) * (y t * (t⁻¹ • Ring.inverse z)) := by
          rw [hmul, mul_one]
      _ = (Ring.inverse (y t) * y t) * (t⁻¹ • Ring.inverse z) := by
          rw [mul_assoc]
      _ = t⁻¹ • Ring.inverse z := by
          rw [Ring.inverse_mul_cancel (y t) huy, one_mul]
  -- the difference as a single product
  have hkey : v t * Ring.inverse (y t) - t⁻¹ • 1
      = t⁻¹ • ((v t - z) * Ring.inverse z) := by
    rw [hinv_y, mul_smul_comm, ← smul_sub, sub_mul,
      Ring.mul_inverse_cancel z hzu]
  -- the two factors
  have hv1 : ‖v t - 1‖ ≤ C * M * t ^ 2 / 2 := by
    have h2 := h.norm_snd_sub_le hR hC hy0 t htI
    rwa [hv0, norm_one, one_mul] at h2
  have hvz : ‖v t - z‖ ≤ 2 / 3 * (C * M * t ^ 2) := by
    have : v t - z = (v t - 1) + w := by rw [hwdef]; abel
    rw [this]
    calc ‖(v t - 1) + w‖ ≤ ‖v t - 1‖ + ‖w‖ := norm_add_le _ _
      _ ≤ C * M * t ^ 2 / 2 + C * M * t ^ 2 / 6 := add_le_add hv1 hw6
      _ = 2 / 3 * (C * M * t ^ 2) := by ring
  -- assemble
  rw [hkey, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos ht.1]
  calc t⁻¹ * ‖(v t - z) * Ring.inverse z‖
      ≤ t⁻¹ * (‖v t - z‖ * ‖Ring.inverse z‖) :=
        mul_le_mul_of_nonneg_left (norm_mul_le _ _) (inv_nonneg.mpr ht.1.le)
    _ ≤ t⁻¹ * (2 / 3 * (C * M * t ^ 2) * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr ht.1.le)
        exact mul_le_mul hvz hinvz_norm (norm_nonneg _)
          (mul_nonneg (by norm_num)
            (mul_nonneg (mul_nonneg hC0 hM0.le) (sq_nonneg t)))
    _ = 4 / 3 * (C * M) * t := by
        have hr : t⁻¹ * (2 / 3 * (C * M * t ^ 2) * 2)
            = 4 / 3 * (C * M) * t * (t⁻¹ * t) := by ring
        rw [hr, inv_mul_cancel₀ ht.1.ne', mul_one]
    _ ≤ 2 * (C * M) * t := by
        have h0 : (0 : ℝ) ≤ C * M * t := mul_nonneg (mul_nonneg hC0 hM0.le) ht.1.le
        nlinarith

end IsJacobiSolOn

end PoincareLib

end

import MorganTianLib.Ch01.IndexForm

/-!
# Poincaré Ch. 1 — a conjugate point makes the index form indefinite

This is the analytic heart of `prop:minimal-geodesic-no-conjugate`, and it is
proved here entirely **without variations, without the energy functional and
without the exponential map** — over an abstract inner-product space, for the
Jacobi ODE `y'' + R y = 0` of `JacobiODE`.

Suppose the geodesic (read in a parallel orthonormal frame, so that a Jacobi field
is a solution `(y, v)` of the ODE) has a **conjugate point at an interior time**
`t₀ ∈ (0, 1)`: a nontrivial Jacobi field `y` with `y 0 = 0` and `y t₀ = 0`.  Then
the index form on `[0, 1]` takes a **strictly negative** value on a piecewise-`C¹`
field vanishing at both endpoints (`exists_indexForm_neg_of_jacobi_vanishing`).

The construction is Morgan–Tian's, made explicit:

* **the truncated Jacobi field** `W = y·1_{[0,t₀]}`, extended by zero past `t₀`.
  It is continuous (because `y t₀ = 0`), piecewise `C¹`, and vanishes at `0` and
  `1`.  Its index is `0`: on `[0, t₀]` it is the Jacobi field, whose index
  vanishes by `IsJacobiSolOn.indexForm_self_eq_zero`; on `[t₀, 1]` it is
  identically zero.  So `W` is a **null direction** of the index form.
  Crucially `W` is *not* smooth at `t₀` — its derivative jumps from `v t₀ ≠ 0`
  to `0` — and it is exactly this corner that the argument exploits.

* **the test field** `Z t = t(1 − t) • v t₀`.  Morgan–Tian take a bump function
  times a parallel field; over the coefficient space a parallel field is a
  *constant vector*, so the bump can be taken to be the **polynomial** `t(1 − t)`,
  which is smooth, vanishes at `0` and `1`, and is nonzero at `t₀`.  No
  `ContDiffBump` machinery is needed.

  Pairing `W` against `Z` sees only the corner: integrating by parts on `[0, t₀]`
  and getting `0` on `[t₀, 1]`,
  `I(W, Z) = ⟨v t₀, Z t₀⟩ = t₀(1 − t₀)·‖v t₀‖² > 0`.

* **the perturbation.**  `W` is a null direction with `I(W, Z) ≠ 0`, so
  `exists_indexForm_neg` produces `c` with `I(W + c·Z) < 0`.

`v t₀ ≠ 0` is automatic: a Jacobi field with `y t₀ = 0` and `v t₀ = 0` vanishes
identically (`IsJacobiSolOn.eqOn_of_right`), contradicting nontriviality.  That is
`IsJacobiSolOn.snd_ne_zero_of_ne_zero` below.

What this does **not** prove — and what the blueprint still owes — is the other
half, `I ≥ 0` for a minimizing geodesic, which genuinely needs the second
variation of energy.  See the status note on `prop:minimal-geodesic-no-conjugate`.

Blueprint: `claim:second-variation-minimal-geodesic`, `prop:minimal-geodesic-no-conjugate`.
-/

open Set intervalIntegral MeasureTheory
open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-! ### A scalar function vanishing off a null set -/

/-- A function that vanishes on `Ioc a b` is interval-integrable on `[a, b]` with
integral zero.  The point of using `Ioc` (rather than `Icc`) is that the interval
integral does not see the left endpoint — which is exactly where the truncated
Jacobi field's derivative jumps. -/
theorem intervalIntegrable_of_eqOn_zero_Ioc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f 0 (Ioc a b)) :
    IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact (integrableOn_congr_fun h measurableSet_Ioc).mpr (integrableOn_zero)

theorem integral_eq_zero_of_eqOn_zero_Ioc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : EqOn f 0 (Ioc a b)) :
    ∫ t in a..b, f t = 0 := by
  rw [intervalIntegral.integral_of_le hab,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioc h]
  simp

/-! ### Nontriviality of the transverse derivative at a conjugate point -/

/-- **Math.** A Jacobi field vanishing at the *right* endpoint whose covariant
derivative also vanishes there is identically zero.  Contrapositively: at a
conjugate point of a **nontrivial** Jacobi field the covariant derivative is
nonzero — the corner of the truncated field is genuine. -/
theorem IsJacobiSolOn.snd_ne_zero_of_ne_zero {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v : ℝ → F}
    (hR : ContinuousOn R (Icc a b)) (hy : IsJacobiSolOn R a b y v)
    (hyb : y b = 0) (hne : ∃ t ∈ Icc a b, y t ≠ 0) :
    v b ≠ 0 := by
  intro hvb
  obtain ⟨t, ht, hyt⟩ := hne
  refine hyt ?_
  have h := hy.eqOn_of_right hR (isJacobiSolOn_zero R a b)
    (by simpa using hyb) (by simpa using hvb)
  simpa using h.1 ht

/-! ### The truncated Jacobi field and the test field -/

variable (t₀ : ℝ) (y v : ℝ → F)

/-- **Math.** The **truncated Jacobi field**: `y` on `[0, t₀]`, extended by zero.
Continuous when `y t₀ = 0`; piecewise `C¹` with a corner at `t₀`. -/
def truncField : ℝ → F := fun t => if t ≤ t₀ then y t else 0

/-- **Math.** The (piecewise) derivative of the truncated Jacobi field: `v` on
`[0, t₀]`, zero afterwards.  At `t₀` it takes the value `v t₀` — the *left*
derivative — and jumps to `0`. -/
def truncDeriv : ℝ → F := fun t => if t ≤ t₀ then v t else 0

variable {t₀ y v}

theorem truncField_of_le {t : ℝ} (ht : t ≤ t₀) : truncField t₀ y t = y t := if_pos ht

theorem truncDeriv_of_le {t : ℝ} (ht : t ≤ t₀) : truncDeriv t₀ v t = v t := if_pos ht

theorem truncField_of_gt {t : ℝ} (ht : t₀ < t) : truncField t₀ y t = 0 := if_neg (not_le.mpr ht)

theorem truncDeriv_of_gt {t : ℝ} (ht : t₀ < t) : truncDeriv t₀ v t = 0 := if_neg (not_le.mpr ht)

/-- On `[0, t₀]` the truncated field *is* the Jacobi field. -/
theorem eqOn_truncField_Icc : EqOn (truncField t₀ y) y (Icc 0 t₀) :=
  fun _ ht => truncField_of_le ht.2

theorem eqOn_truncDeriv_Icc : EqOn (truncDeriv t₀ v) v (Icc 0 t₀) :=
  fun _ ht => truncDeriv_of_le ht.2

/-- **Math.** Past the conjugate point the truncated field vanishes *including at
`t₀` itself* — because `y t₀ = 0`.  This is what makes it continuous. -/
theorem eqOn_truncField_zero (hyt : y t₀ = 0) : EqOn (truncField t₀ y) 0 (Icc t₀ 1) := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with h | h
  · simp [truncField, ← h, hyt]
  · simp [truncField_of_gt h]

/-- The truncated derivative vanishes on `Ioc t₀ 1` — note the *open* left end:
at `t₀` itself it equals `v t₀ ≠ 0`.  The interval integral does not see that
point, which is precisely why the corner costs nothing on `[t₀, 1]`. -/
theorem eqOn_truncDeriv_zero : EqOn (truncDeriv t₀ v) 0 (Ioc t₀ 1) :=
  fun _ ht => truncDeriv_of_gt ht.1

/-- **Math.** The **test field** `Z t = t(1 − t) • v t₀`: smooth, vanishing at
`0` and `1`, and equal to `t₀(1 − t₀) • v t₀ ≠ 0` at the conjugate time. -/
def testField (w : F) : ℝ → F := fun t => (t * (1 - t)) • w

/-- The derivative of the test field. -/
def testDeriv (w : F) : ℝ → F := fun t => (1 - 2 * t) • w

theorem hasDerivAt_testField (w : F) (t : ℝ) :
    HasDerivAt (testField w) (testDeriv w t) t := by
  have hpoly : HasDerivAt (fun s : ℝ => s * (1 - s)) (1 - 2 * t) t := by
    have h1 : HasDerivAt (fun s : ℝ => s - s ^ 2) (1 - 2 * t) t := by
      simpa using (hasDerivAt_id t).sub (hasDerivAt_pow 2 t)
    have hfun : (fun s : ℝ => s * (1 - s)) = fun s : ℝ => s - s ^ 2 := by
      funext s; ring
    rw [hfun]; exact h1
  simpa [testField, testDeriv] using hpoly.smul_const w

theorem continuous_testField (w : F) : Continuous (testField w) :=
  (continuous_id.mul (continuous_const.sub continuous_id)).smul continuous_const

theorem continuous_testDeriv (w : F) : Continuous (testDeriv w) :=
  (continuous_const.sub (continuous_const.mul continuous_id)).smul continuous_const

@[simp] theorem testField_zero (w : F) : testField w 0 = 0 := by simp [testField]

@[simp] theorem testField_one (w : F) : testField w 1 = 0 := by simp [testField]

/-! ### The main construction -/

section Main

variable {R : ℝ → F →L[ℝ] F}

/-- Continuity of the truncated field on `[0, 1]`. -/
theorem continuousOn_truncField (ht₀ : 0 ≤ t₀) (ht₁ : t₀ ≤ 1)
    (hy : IsJacobiSolOn R 0 t₀ y v) (hyt : y t₀ = 0) :
    ContinuousOn (truncField t₀ y) (Icc 0 1) := by
  have hsplit : Icc (0 : ℝ) 1 = Icc 0 t₀ ∪ Icc t₀ 1 := (Icc_union_Icc_eq_Icc ht₀ ht₁).symm
  rw [hsplit]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · exact hy.continuousOn_fst.congr (fun t ht => eqOn_truncField_Icc ht)
  · exact continuousOn_const.congr (fun t ht => eqOn_truncField_zero hyt ht)

/-- **Math.** **A conjugate point at an interior time makes the index form
indefinite.**

Let `(y, v)` be a nontrivial solution of the Jacobi ODE on `[0, t₀]` with
`y 0 = 0` and `y t₀ = 0` — i.e. a Jacobi field exhibiting `t₀ ∈ (0, 1)` as a
point conjugate to the origin.  Then there is a **piecewise-`C¹` field `W`
vanishing at both endpoints of `[0, 1]`** whose index is **strictly negative**.

Since a minimizing geodesic has nonnegative index form (the second-variation
half, not proved here), this is exactly the contradiction that establishes
`prop:minimal-geodesic-no-conjugate`.

The conclusion records `W` together with its piecewise derivative `DW`: `DW` is
the derivative of `W` on `[0, t₀]` and on `(t₀, 1]`, with a jump at `t₀`. -/
theorem exists_indexForm_neg_of_jacobi_vanishing
    (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hR : ContinuousOn R (Icc (0 : ℝ) 1))
    (hRsymm : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hy : IsJacobiSolOn R 0 t₀ y v)
    (hy0 : y 0 = 0) (hyt : y t₀ = 0) (hne : ∃ t ∈ Icc 0 t₀, y t ≠ 0) :
    ∃ W DW : ℝ → F,
      W 0 = 0 ∧ W 1 = 0 ∧
      ContinuousOn W (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc 0 t₀, HasDerivWithinAt W (DW t) (Icc 0 t₀) t) ∧
      (∀ t ∈ Ioc t₀ 1, HasDerivWithinAt W (DW t) (Icc t₀ 1) t) ∧
      indexForm R 0 1 W DW W DW < 0 := by
  have ht₀le : (0 : ℝ) ≤ t₀ := ht₀.le
  have ht₁le : t₀ ≤ (1 : ℝ) := ht₁.le
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  -- `R` restricted to the two pieces
  have hR₁ : ContinuousOn R (Icc 0 t₀) := hR.mono (Icc_subset_Icc le_rfl ht₁le)
  have hR₂ : ContinuousOn R (Icc t₀ 1) := hR.mono (Icc_subset_Icc ht₀le le_rfl)
  -- the transverse derivative at the conjugate point is nonzero
  have hv : v t₀ ≠ 0 := hy.snd_ne_zero_of_ne_zero hR₁ hyt hne
  set W : ℝ → F := truncField t₀ y with hW
  set DW : ℝ → F := truncDeriv t₀ v with hDW
  set Z : ℝ → F := testField (v t₀) with hZ
  set DZ : ℝ → F := testDeriv (v t₀) with hDZ
  -- ### basic pointwise facts
  have hWzero : EqOn W 0 (Icc t₀ 1) := eqOn_truncField_zero hyt
  have hDWzero : EqOn DW 0 (Ioc t₀ 1) := eqOn_truncDeriv_zero
  have hWcont : ContinuousOn W (Icc (0 : ℝ) 1) :=
    continuousOn_truncField ht₀le ht₁le hy hyt
  have hWy : EqOn W y (Icc 0 t₀) := eqOn_truncField_Icc
  have hDWv : EqOn DW v (Icc 0 t₀) := eqOn_truncDeriv_Icc
  have hZc : Continuous Z := continuous_testField _
  have hDZc : Continuous DZ := continuous_testDeriv _
  -- ### the index integrands vanish on `Ioc t₀ 1`
  have hkill : ∀ z ζ : ℝ → F, EqOn (indexIntegrand R W DW z ζ) 0 (Ioc t₀ 1) := by
    intro z ζ t ht
    have h1 : DW t = 0 := hDWzero ht
    have h2 : W t = 0 := hWzero ⟨ht.1.le, ht.2⟩
    simp [indexIntegrand, h1, h2]
  -- ### integrability on the two pieces, hence on `[0, 1]`
  have hint₁ : ∀ z ζ : ℝ → F, ContinuousOn z (Icc 0 t₀) → ContinuousOn ζ (Icc 0 t₀) →
      IntervalIntegrable (indexIntegrand R W DW z ζ) volume 0 t₀ := by
    intro z ζ hz hζ
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;>
      rw [uIcc_of_le ht₀le]
    · exact hR₁
    · exact hy.continuousOn_fst.congr fun t ht => hWy ht
    · exact hy.continuousOn_snd.congr fun t ht => hDWv ht
    · exact hz
    · exact hζ
  have hint₂ : ∀ z ζ : ℝ → F,
      IntervalIntegrable (indexIntegrand R W DW z ζ) volume t₀ 1 := fun z ζ =>
    intervalIntegrable_of_eqOn_zero_Ioc ht₁le (hkill z ζ)
  have hintZZ : IntervalIntegrable (indexIntegrand R Z DZ Z DZ) volume 0 1 := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;> rw [uIcc_of_le h01]
    · exact hR
    · exact hZc.continuousOn
    · exact hDZc.continuousOn
    · exact hZc.continuousOn
    · exact hDZc.continuousOn
  have hintWW : IntervalIntegrable (indexIntegrand R W DW W DW) volume 0 1 :=
    ((hint₁ W DW (hy.continuousOn_fst.congr fun t ht => hWy ht)
      (hy.continuousOn_snd.congr fun t ht => hDWv ht)).trans (hint₂ W DW))
  have hintWZ : IntervalIntegrable (indexIntegrand R W DW Z DZ) volume 0 1 :=
    ((hint₁ Z DZ hZc.continuousOn hDZc.continuousOn).trans (hint₂ Z DZ))
  -- ### the truncated field is a NULL direction: `I(W, W) = 0`
  have hWW : indexForm R 0 1 W DW W DW = 0 := by
    rw [← indexForm_add_adjacent
      (hint₁ W DW (hy.continuousOn_fst.congr fun t ht => hWy ht)
        (hy.continuousOn_snd.congr fun t ht => hDWv ht))
      (hint₂ W DW)]
    have e₁ : indexForm R 0 t₀ W DW W DW = indexForm R 0 t₀ y v y v := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le ht₀le] at ht
      simp [indexIntegrand, hWy ht, hDWv ht]
    have e₂ : indexForm R t₀ 1 W DW W DW = 0 :=
      integral_eq_zero_of_eqOn_zero_Ioc ht₁le (hkill W DW)
    rw [e₁, e₂, hy.indexForm_self_eq_zero ht₀le hR₁ hy0 hyt, add_zero]
  -- ### but it is NOT index-orthogonal to the test field: `I(W, Z) = t₀(1−t₀)‖v t₀‖² > 0`
  have hWZ : indexForm R 0 1 W DW Z DZ = t₀ * (1 - t₀) * ‖v t₀‖ ^ 2 := by
    rw [← indexForm_add_adjacent (hint₁ Z DZ hZc.continuousOn hDZc.continuousOn) (hint₂ Z DZ)]
    have e₂ : indexForm R t₀ 1 W DW Z DZ = 0 :=
      integral_eq_zero_of_eqOn_zero_Ioc ht₁le (hkill Z DZ)
    have e₁ : indexForm R 0 t₀ W DW Z DZ = indexForm R 0 t₀ y v Z DZ := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [uIcc_of_le ht₀le] at ht
      simp [indexIntegrand, hWy ht, hDWv ht]
    -- integrate by parts against the Jacobi field: only the boundary survives
    have hbp : indexForm R 0 t₀ y v Z DZ = ⟪v t₀, Z t₀⟫ - ⟪v 0, Z 0⟫ :=
      hy.indexForm_eq_sub ht₀le hR₁
        (fun t _ => (hasDerivAt_testField (v t₀) t).hasDerivWithinAt) hDZc.continuousOn
    rw [e₁, e₂, add_zero, hbp]
    have hZ0 : Z 0 = 0 := testField_zero _
    rw [hZ0, hZ, testField]
    simp only [inner_zero_right, sub_zero, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hWZne : indexForm R 0 1 W DW Z DZ ≠ 0 := by
    rw [hWZ]
    have : 0 < t₀ * (1 - t₀) * ‖v t₀‖ ^ 2 := by
      have h1 : 0 < 1 - t₀ := by linarith
      have h2 : 0 < ‖v t₀‖ := norm_pos_iff.mpr hv
      positivity
    exact ne_of_gt this
  -- ### perturb the null direction: the index form goes strictly negative
  obtain ⟨c, hc⟩ := exists_indexForm_neg hRsymm hintWW hintWZ hintZZ hWW hWZne
  have hW0 : W 0 = 0 := by rw [hW, truncField_of_le ht₀le, hy0]
  have hW1 : W 1 = 0 := by rw [hW, truncField_of_gt ht₁]
  have hZ0 : Z 0 = 0 := by rw [hZ]; exact testField_zero _
  have hZ1 : Z 1 = 0 := by rw [hZ]; exact testField_one _
  refine ⟨W + c • Z, DW + c • DZ, ?_, ?_, ?_, ?_, ?_, hc⟩
  · simp [hW0, hZ0]
  · simp [hW1, hZ1]
  · exact hWcont.add (continuousOn_const.smul hZc.continuousOn)
  · intro t ht
    have hDZt : HasDerivWithinAt Z (DZ t) (Icc 0 t₀) t := by
      rw [hZ, hDZ]; exact (hasDerivAt_testField (v t₀) t).hasDerivWithinAt
    have hWd : HasDerivWithinAt W (DW t) (Icc 0 t₀) t := by
      rw [hDWv ht]
      exact (hy.hasDerivWithinAt_fst t ht).congr (fun s hs => hWy hs) (hWy ht)
    exact hWd.add (hDZt.const_smul c)
  · intro t ht
    have hDZt : HasDerivWithinAt Z (DZ t) (Icc t₀ 1) t := by
      rw [hZ, hDZ]; exact (hasDerivAt_testField (v t₀) t).hasDerivWithinAt
    have hWd : HasDerivWithinAt W (DW t) (Icc t₀ 1) t := by
      have h0 : DW t = 0 := hDWzero ht
      rw [h0]
      exact (hasDerivWithinAt_const t (Icc t₀ 1) (0 : F)).congr
        (fun s hs => hWzero hs) (hWzero ⟨ht.1.le, ht.2⟩)
    exact hWd.add (hDZt.const_smul c)

end Main

end MorganTianLib

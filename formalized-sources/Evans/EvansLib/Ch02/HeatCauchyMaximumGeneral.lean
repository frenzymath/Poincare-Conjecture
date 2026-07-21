import EvansLib.Ch02.HeatCauchyMaximum

/-!
# Evans, Ch. 2 §2.3.3 — the Cauchy-problem maximum principle, general time

This file removes the small-time restriction `4aT < 1` from
`EvansLib.heat_cauchy_maxPrinciple_smallTime` by Evans's **time-splitting** (§2.3.3, step 3):
partition `[0,T]` into slabs of length `T₁ = 1/(8a)` (each with `4aT₁ = 1/2 < 1`) and chain
the small-time result across them, carrying the bound `u(·, kT₁) ≤ M` forward.

The technical device is **time translation**: on the slab `[t₀, t₀+S]` we apply the
small-time result to `ũ(q) := u(q + t₀ e₀)`. The reusable translation lemmas
(`partialDeriv_comp_add_const`, `partialDeriv_iterate_two_comp_add_const`) express that
partial derivatives commute with translation of the argument by a constant vector (whose
Fréchet derivative is the identity).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.3.3, Theorem 6,
step 3.
-/

open scoped ContDiff Topology
open Filter Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Partial derivatives commute with translation of the argument -/

/-- **First partial through a constant translation.** Translating the argument of `u` by a
fixed vector `w` (an affine map with identity derivative) commutes with `∂ᵢ`. -/
lemma partialDeriv_comp_add_const {m : ℕ} {u : EuclideanSpace ℝ (Fin m) → ℝ}
    (w : EuclideanSpace ℝ (Fin m)) (i : Fin m) {p : EuclideanSpace ℝ (Fin m)}
    (hu : DifferentiableAt ℝ u (p + w)) :
    partialDeriv i (fun q => u (q + w)) p = partialDeriv i u (p + w) := by
  have hT : HasFDerivAt (fun q : EuclideanSpace ℝ (Fin m) => q + w)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m))) p :=
    (hasFDerivAt_id p).add_const w
  have hcomp : HasFDerivAt (fun q => u (q + w)) (fderiv ℝ u (p + w)) p := by
    have := hu.hasFDerivAt.comp p hT
    simpa using this
  rw [partialDeriv_apply, partialDeriv_apply, hcomp.fderiv]

/-- **Second partial through a constant translation.** -/
lemma partialDeriv_iterate_two_comp_add_const {m : ℕ} {u : EuclideanSpace ℝ (Fin m) → ℝ}
    (w : EuclideanSpace ℝ (Fin m)) (i : Fin m) {p : EuclideanSpace ℝ (Fin m)}
    (hu : ContDiffAt ℝ 2 u (p + w)) :
    (partialDeriv i)^[2] (fun q => u (q + w)) p = (partialDeriv i)^[2] u (p + w) := by
  have huev : ∀ᶠ r in 𝓝 (p + w), DifferentiableAt ℝ u r :=
    (hu.eventually (by simp)).mono fun r hr => hr.differentiableAt (by norm_num)
  have hpull : ∀ᶠ q in 𝓝 p, DifferentiableAt ℝ u (q + w) :=
    (Continuous.tendsto (by fun_prop) p).eventually huev
  have hev : partialDeriv i (fun q => u (q + w)) =ᶠ[𝓝 p] fun q => partialDeriv i u (q + w) := by
    filter_upwards [hpull] with q hq using partialDeriv_comp_add_const w i hq
  rw [show (partialDeriv i)^[2] (fun q => u (q + w)) p
      = partialDeriv i (partialDeriv i (fun q => u (q + w))) p from by
        rw [Function.iterate_succ_apply', Function.iterate_one],
    partialDeriv_congr_of_eventuallyEq i hev,
    show (partialDeriv i)^[2] u (p + w) = partialDeriv i (partialDeriv i u) (p + w) from by
        rw [Function.iterate_succ_apply', Function.iterate_one]]
  exact partialDeriv_comp_add_const w i (differentiableAt_partialDeriv_of_contDiffAt hu i)

/-! ## The small-time maximum principle on a time-shifted slab -/

/-- **The small-time maximum principle on the slab `[t₀, t₀+S]`** (`4aS < 1`). Applying
`heat_cauchy_maxPrinciple_smallTime` to the time-translate `ũ(q) = u(q + t₀ e₀)`: `ũ`
inherits continuity, `C²`-ness and the heat equation on `(0,S)` (via the translation lemmas)
and the growth bound (translation fixes the spatial part), and its initial data `ũ(·,0) =
u(·,t₀)` is bounded by `M`. This is the building block Evans iterates in his step 3. -/
theorem heat_cauchy_maxPrinciple_shifted {u : SpaceTime n → ℝ}
    {t₀ S T A a : ℝ} (ht₀ : 0 ≤ t₀) (hS : 0 < S) (hTsum : t₀ + S ≤ T)
    (ha : 0 < a) (hA : 0 < A) (hsmall : 4 * a * S < 1)
    (hcont : Continuous u)
    (hC2 : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hheat : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 u p = ∑ j : Fin n, (partialDeriv j.succ)^[2] u p)
    (hgrowth : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      u p ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2))
    {M : ℝ} (hM : ∀ x, u (toSpaceTime t₀ x) ≤ M) :
    ∀ p : SpaceTime n, p 0 ∈ Icc t₀ (t₀ + S) → u p ≤ M := by
  set e : SpaceTime n := EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) with he_def
  have hw0 : ∀ q : SpaceTime n, (q + t₀ • e) 0 = q 0 + t₀ := fun q =>
    timeCoord_add_smul_single_zero q t₀
  have hwsp : ∀ q : SpaceTime n, spacePart (q + t₀ • e) = spacePart q := fun q =>
    spacePart_add_smul_single_zero q t₀
  have hshiftC : Continuous (fun q : SpaceTime n => q + t₀ • e) := by fun_prop
  have hshiftCD : ContDiff ℝ 2 (fun q : SpaceTime n => q + t₀ • e) :=
    contDiff_id.add contDiff_const
  have key : ∀ p : SpaceTime n, p 0 ∈ Icc 0 S → u (p + t₀ • e) ≤ M := by
    refine heat_cauchy_maxPrinciple_smallTime (u := fun q => u (q + t₀ • e)) (M := M)
      hS ha hA hsmall (hcont.comp hshiftC) ?_ ?_ ?_ ?_
    · intro q hq
      have hmem : (q + t₀ • e) 0 ∈ Ioo 0 T := by
        rw [hw0]; exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
      exact (hC2 _ hmem).comp q hshiftCD.contDiffAt
    · intro q hq
      have hmem : (q + t₀ • e) 0 ∈ Ioo 0 T := by
        rw [hw0]; exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
      rw [partialDeriv_comp_add_const _ 0 ((hC2 _ hmem).differentiableAt (by norm_num)),
        hheat _ hmem]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact (partialDeriv_iterate_two_comp_add_const _ j.succ (hC2 _ hmem)).symm
    · intro q hq
      have hmem : (q + t₀ • e) 0 ∈ Icc 0 T := by
        rw [hw0]; exact ⟨by linarith [hq.1], by linarith [hq.2]⟩
      have hg := hgrowth _ hmem
      rwa [hwsp] at hg
    · intro x
      show u (toSpaceTime (0 : ℝ) x + t₀ • e) ≤ M
      have hpt : toSpaceTime (0 : ℝ) x + t₀ • e = toSpaceTime t₀ x := by
        rw [← toSpaceTime_spacePart (toSpaceTime (0 : ℝ) x + t₀ • e)]
        have h1 : (toSpaceTime (0 : ℝ) x + t₀ • e) 0 = t₀ := by
          rw [hw0, toSpaceTime_timeCoord, zero_add]
        have h2 : spacePart (toSpaceTime (0 : ℝ) x + t₀ • e) = x := by
          rw [hwsp, spacePart_toSpaceTime]
        rw [h1, h2]
      rw [hpt]; exact hM x
  intro p hp
  have hsub : ((p - t₀ • e) + t₀ • e) 0 = (p - t₀ • e) 0 + t₀ := hw0 (p - t₀ • e)
  rw [sub_add_cancel] at hsub
  have hq0 : (p - t₀ • e) 0 ∈ Icc 0 S :=
    ⟨by linarith [hp.1, hsub], by linarith [hp.2, hsub]⟩
  have hkey := key (p - t₀ • e) hq0
  rwa [sub_add_cancel] at hkey

/-! ## The maximum principle for the Cauchy problem — general `T` -/

/-- **Maximum principle for the heat Cauchy problem** (Evans §2.3.3 Theorem 6, full
statement). A continuous solution `u` of the heat equation on `ℝⁿ × (0,T)`, `C²` there,
with initial data bounded above by `M` and the Gaussian growth bound
`u(x,t) ≤ A e^{a‖x‖²}` on `ℝⁿ × [0,T]`, satisfies `u ≤ M` on `ℝⁿ × [0,T]` — with **no**
restriction on `T`. Taking `M = sup u(·,0)` gives `sup u = sup g`.

Evans's step 3: split `[0,T]` into slabs of length `T₁ = 1/(8a)` (so `4aT₁ = 1/2 < 1`) and
induct, chaining `heat_cauchy_maxPrinciple_shifted` across slabs while carrying the bound
`u(·, kT₁) ≤ M` forward. -/
theorem heat_cauchy_maxPrinciple {u : SpaceTime n → ℝ}
    {T A a : ℝ} (hT : 0 < T) (ha : 0 < a) (hA : 0 < A)
    (hcont : Continuous u)
    (hC2 : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hheat : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 u p = ∑ j : Fin n, (partialDeriv j.succ)^[2] u p)
    (hgrowth : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      u p ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2))
    {M : ℝ} (hM : ∀ x, u (toSpaceTime 0 x) ≤ M) :
    ∀ p : SpaceTime n, p 0 ∈ Icc 0 T → u p ≤ M := by
  set T₁ := 1 / (8 * a) with hT₁_def
  have hT₁pos : 0 < T₁ := by rw [hT₁_def]; positivity
  have h4aT₁ : 4 * a * T₁ = 1 / 2 := by rw [hT₁_def]; field_simp; ring
  -- P(k): u ≤ M on the time-slab [0, kT₁] ∩ [0,T]
  have hP : ∀ k : ℕ, ∀ p : SpaceTime n, p 0 ∈ Icc 0 T → p 0 ≤ (k : ℝ) * T₁ → u p ≤ M := by
    intro k
    induction k with
    | zero =>
      intro p hp hp0
      simp only [Nat.cast_zero, zero_mul] at hp0
      have hp00 : p 0 = 0 := le_antisymm hp0 hp.1
      have hrec : p = toSpaceTime 0 (spacePart p) := by
        conv_lhs => rw [← toSpaceTime_spacePart p]
        rw [hp00]
      rw [hrec]; exact hM (spacePart p)
    | succ k ih =>
      intro p hp hp0
      push_cast at hp0
      by_cases hcase : p 0 ≤ (k : ℝ) * T₁
      · exact ih p hp hcase
      · rw [not_le] at hcase
        have hkT0 : 0 ≤ (k : ℝ) * T₁ := by positivity
        have hkT : (k : ℝ) * T₁ < T := lt_of_lt_of_le hcase hp.2
        set T' := min (((k : ℝ) + 1) * T₁) T with hT'_def
        have hexp : ((k : ℝ) + 1) * T₁ = (k : ℝ) * T₁ + T₁ := by ring
        have hkltk1 : (k : ℝ) * T₁ < ((k : ℝ) + 1) * T₁ := by rw [hexp]; linarith
        have hkltT' : (k : ℝ) * T₁ < T' := by rw [hT'_def, lt_min_iff]; exact ⟨hkltk1, hkT⟩
        have hT'leT : T' ≤ T := min_le_right _ _
        set S := T' - (k : ℝ) * T₁ with hS_def
        have hSpos : 0 < S := by rw [hS_def]; linarith
        have hSle : S ≤ T₁ := by
          rw [hS_def]; have := min_le_left (((k : ℝ) + 1) * T₁) T; rw [← hT'_def] at this
          linarith [hexp]
        have hsmall : 4 * a * S < 1 := by nlinarith [hSle, ha, h4aT₁]
        have hM' : ∀ x, u (toSpaceTime ((k : ℝ) * T₁) x) ≤ M := by
          intro x
          refine ih (toSpaceTime ((k : ℝ) * T₁) x) ⟨?_, ?_⟩ ?_
          · rw [toSpaceTime_timeCoord]; exact hkT0
          · rw [toSpaceTime_timeCoord]; exact hkT.le
          · rw [toSpaceTime_timeCoord]
        have hsum : (k : ℝ) * T₁ + S = T' := by rw [hS_def]; ring
        refine heat_cauchy_maxPrinciple_shifted hkT0 hSpos (by rw [hsum]; exact hT'leT)
          ha hA hsmall hcont hC2 hheat hgrowth hM' p ⟨hcase.le, ?_⟩
        rw [hsum, hT'_def, le_min_iff]
        exact ⟨hp0, hp.2⟩
  -- for k large the slab covers [0,T]
  intro p hp
  obtain ⟨k, hk⟩ : ∃ k : ℕ, T ≤ (k : ℝ) * T₁ := by
    refine ⟨Nat.ceil (8 * a * T), ?_⟩
    have hceil : 8 * a * T ≤ (Nat.ceil (8 * a * T) : ℝ) := Nat.le_ceil _
    have hval : 8 * a * T * T₁ = T := by rw [hT₁_def]; field_simp
    calc T = 8 * a * T * T₁ := hval.symm
      _ ≤ (Nat.ceil (8 * a * T) : ℝ) * T₁ := by
          exact mul_le_mul_of_nonneg_right hceil hT₁pos.le
  exact hP k p hp (le_trans hp.2 hk)

/-- **Uniqueness for the heat Cauchy problem** (Evans §2.3.3 Theorem 7, full statement). Two
solutions `u, v` of the same Cauchy problem — their difference solves the homogeneous heat
equation on `ℝⁿ × (0,T)` — with the same initial data and Gaussian growth bounds agree on
`ℝⁿ × [0,T]`, with no restriction on `T`. Applies the general maximum principle
`heat_cauchy_maxPrinciple` to `±(u-v)`. -/
theorem heat_cauchy_uniqueness {u v : SpaceTime n → ℝ} {T A a : ℝ}
    (hT : 0 < T) (ha : 0 < a) (hA : 0 < A)
    (hcontu : Continuous u) (hcontv : Continuous v)
    (hC2u : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 u p)
    (hC2v : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T → ContDiffAt ℝ 2 v p)
    (hheat : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 (fun q => u q - v q) p
        = ∑ j : Fin n, (partialDeriv j.succ)^[2] (fun q => u q - v q) p)
    (hinit : ∀ x, u (toSpaceTime 0 x) = v (toSpaceTime 0 x))
    (hgrowthu : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      |u p| ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2))
    (hgrowthv : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      |v p| ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2)) :
    ∀ p : SpaceTime n, p 0 ∈ Icc 0 T → u p = v p := by
  have h2A : (0 : ℝ) < 2 * A := by positivity
  have hgroww : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      (fun q => u q - v q) p ≤ (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by
    intro p hpp
    calc u p - v p ≤ |u p| + |v p| := by
          have h1 := le_abs_self (u p); have h2 := neg_le_abs (v p); linarith
      _ ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2) + A * Real.exp (a * ‖spacePart p‖ ^ 2) := by
          linarith [hgrowthu p hpp, hgrowthv p hpp]
      _ = (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by ring
  have hinitw : ∀ x, (fun q => u q - v q) (toSpaceTime 0 x) ≤ 0 := by
    intro x; simp only; rw [hinit x]; simp
  have hupper := heat_cauchy_maxPrinciple hT ha h2A
    (hcontu.sub hcontv) (fun p hpp => (hC2u p hpp).sub (hC2v p hpp)) hheat hgroww hinitw
  have hheat' : ∀ p : SpaceTime n, p 0 ∈ Ioo 0 T →
      partialDeriv 0 (fun q => v q - u q) p
        = ∑ j : Fin n, (partialDeriv j.succ)^[2] (fun q => v q - u q) p := by
    intro p hpp
    have hvu : (fun q => v q - u q) = fun q => -(u q - v q) := by funext q; ring
    rw [hvu]
    exact neg_solvesHeat ((hC2u p hpp).sub (hC2v p hpp)) (hheat p hpp)
  have hgroww' : ∀ p : SpaceTime n, p 0 ∈ Icc 0 T →
      (fun q => v q - u q) p ≤ (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by
    intro p hpp
    calc v p - u p ≤ |v p| + |u p| := by
          have h1 := le_abs_self (v p); have h2 := neg_le_abs (u p); linarith
      _ ≤ A * Real.exp (a * ‖spacePart p‖ ^ 2) + A * Real.exp (a * ‖spacePart p‖ ^ 2) := by
          linarith [hgrowthu p hpp, hgrowthv p hpp]
      _ = (2 * A) * Real.exp (a * ‖spacePart p‖ ^ 2) := by ring
  have hinitw' : ∀ x, (fun q => v q - u q) (toSpaceTime 0 x) ≤ 0 := by
    intro x; simp only; rw [hinit x]; simp
  have hlower := heat_cauchy_maxPrinciple hT ha h2A
    (hcontv.sub hcontu) (fun p hpp => (hC2v p hpp).sub (hC2u p hpp)) hheat' hgroww' hinitw'
  intro p hp
  have h1 := hupper p hp
  have h2 := hlower p hp
  simp only at h1 h2
  exact le_antisymm (by linarith) (by linarith)

end EvansLib

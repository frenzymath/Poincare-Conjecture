import EvansLib.Ch02.LaplaceMeanValueAux
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth radial profiles for the Laplace mean-value argument

The weak radial identity in `LaplaceMeanValueAux` is parametrized by a smooth
profile `g` in the squared radius. This file supplies the one-dimensional
range construction needed to use that identity: a compactly supported smooth
test `φ` on `(0,R)` is encoded as

`2 * r ^ n * g'(r ^ 2) = φ r`.

The construction is global: the quotient by the power of `sqrt` is used only
at positive arguments and is extended by zero elsewhere; the support gap at
zero makes this extension smooth. The primitive is an interval integral
ending at `R^2`, so it vanishes above `R^2` automatically.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff Interval
open InnerProductSpace

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The inverse profile for the map `g ↦ 2 * r^n * g'(r^2)`. -/
def invProfile (φ : ℝ → ℝ) (n : ℕ) (ρ : ℝ) : ℝ :=
  if 0 < ρ then φ (√ρ) / (2 * (√ρ) ^ n) else 0

/-- The primitive used to recover a squared-radius profile from `φ`. -/
def radialPrimitive (φ : ℝ → ℝ) (n : ℕ) (R : ℝ) (ρ : ℝ) : ℝ :=
  ∫ t in R ^ 2..ρ, invProfile φ n t

lemma invProfile_eq_zero_of_sqrt_not_mem {φ : ℝ → ℝ} {n : ℕ}
    {ρ : ℝ} (hρ : √ρ ∉ tsupport φ) : invProfile φ n ρ = 0 := by
  rw [invProfile]
  by_cases h : 0 < ρ
  · rw [if_pos h, image_eq_zero_of_notMem_tsupport hρ, zero_div]
  · simp [h]

lemma invProfile_eq_zero_of_nonpos {φ : ℝ → ℝ} {n : ℕ} {ρ : ℝ}
    {R : ℝ} (hφsupp : tsupport φ ⊆ Ioo (0 : ℝ) R) (hρ : ρ ≤ 0) :
    invProfile φ n ρ = 0 := by
  apply invProfile_eq_zero_of_sqrt_not_mem
  rw [Real.sqrt_eq_zero_of_nonpos hρ]
  intro hmem
  exact (show (0 : ℝ) ∉ Ioo (0 : ℝ) R by simp) (hφsupp hmem)

/-- The inverse profile is smooth across the zero extension when `φ` has a
support gap at zero. -/
lemma invProfile_contDiff {φ : ℝ → ℝ} {n : ℕ} {R : ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (hφsupp : tsupport φ ⊆ Ioo (0 : ℝ) R) :
    ContDiff ℝ ∞ (invProfile φ n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x 0 with hx | hx
  · have hev : invProfile φ n =ᶠ[nhds x] (fun _ : ℝ => 0) := by
      filter_upwards [Metric.mem_nhds_iff.2 ⟨-x / 2, by linarith,
        fun y hy => by
          have habs : |y - x| < -x / 2 := by
            simpa [mem_ball, Real.dist_eq] using hy
          rw [abs_lt] at habs
          have : y < 0 := by linarith
          exact invProfile_eq_zero_of_nonpos (n := n) hφsupp this.le⟩] with y hy
      exact hy
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · rcases eq_or_lt_of_le hx with rfl | hxpos
    · have hzero : (0 : ℝ) ∉ tsupport φ := by
        intro h0
        exact (show (0 : ℝ) ∉ Ioo (0 : ℝ) R by simp) (hφsupp h0)
      have hopen : (tsupport φ)ᶜ ∈ nhds (0 : ℝ) :=
        (isClosed_tsupport φ).isOpen_compl.mem_nhds hzero
      obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 hopen
      have hδ : 0 < min 1 (ε ^ 2) := lt_min (by norm_num) (sq_pos_of_pos hε)
      have hev : invProfile φ n =ᶠ[nhds (0 : ℝ)] (fun _ : ℝ => 0) := by
        filter_upwards [Metric.mem_nhds_iff.2 ⟨min 1 (ε ^ 2), hδ,
          fun y hy => by
            have hy' : |y| < min 1 (ε ^ 2) := by
              simpa [mem_ball, Real.dist_eq] using hy
            have hyupper : y < ε ^ 2 :=
              lt_of_le_of_lt (le_abs_self y)
                (lt_of_lt_of_le hy' (min_le_right _ _))
            have hsqrt : √y < ε := by
              by_cases hy0 : y ≤ 0
              · rw [Real.sqrt_eq_zero_of_nonpos hy0]
                exact hε
              · have hypos : 0 < y := lt_of_not_ge hy0
                have hsnonneg : 0 ≤ √y := Real.sqrt_nonneg _
                have hsq : (√y) ^ 2 = y := Real.sq_sqrt hypos.le
                nlinarith
            have hs : √y ∈ ball (0 : ℝ) ε := by
              rw [mem_ball, Real.dist_eq]
              simpa [sub_zero, abs_of_nonneg (Real.sqrt_nonneg y)] using hsqrt
            exact invProfile_eq_zero_of_sqrt_not_mem (n := n) (hεsub hs)
          ⟩] with y hy
        exact hy
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hsqrt : ContDiffAt ℝ ∞ (fun y : ℝ => √y) x :=
        Real.contDiffAt_sqrt hxpos.ne'
      have hnum : ContDiffAt ℝ ∞ (fun y : ℝ => φ (√y)) x :=
        hφ.contDiffAt.comp x hsqrt
      have hden : ContDiffAt ℝ ∞ (fun y : ℝ => 2 * (√y) ^ n) x := by
        exact contDiffAt_const.mul (hsqrt.pow n)
      have hquot : ContDiffAt ℝ ∞
          (fun y : ℝ => φ (√y) / (2 * (√y) ^ n)) x :=
        hnum.div hden (by positivity)
      have hev : invProfile φ n =ᶠ[nhds x]
          (fun y : ℝ => φ (√y) / (2 * (√y) ^ n)) := by
        filter_upwards [Metric.mem_nhds_iff.2 ⟨x / 2, by linarith,
          fun y hy => by
            have hy' : |y - x| < x / 2 := by
              simpa [mem_ball, Real.dist_eq] using hy
            have : 0 < y := by
              rw [abs_lt] at hy'
              linarith
            change (if 0 < y then φ (√y) / (2 * (√y) ^ n) else 0) =
              φ (√y) / (2 * (√y) ^ n)
            rw [if_pos this]⟩] with y hy
        exact hy
      exact hquot.congr_of_eventuallyEq hev

lemma invProfile_eq_zero_of_sq_lt {φ : ℝ → ℝ} {n : ℕ} {R ρ : ℝ}
    (hR : 0 ≤ R) (hφsupp : tsupport φ ⊆ Ioo (0 : ℝ) R)
    (hρ : R ^ 2 < ρ) : invProfile φ n ρ = 0 := by
  apply invProfile_eq_zero_of_sqrt_not_mem (n := n)
  intro hmem
  have hmemI := hφsupp hmem
  have hρ0 : 0 ≤ ρ := by nlinarith [sq_nonneg R]
  have hs : (√ρ) ^ 2 = ρ := Real.sq_sqrt hρ0
  have hsnonneg : 0 ≤ √ρ := Real.sqrt_nonneg _
  have hsR : R < √ρ := by nlinarith
  exact (not_lt_of_ge hmemI.2.le) hsR

/-- A smooth squared-radius profile realizing an arbitrary smooth test on
`(0,R)`. -/
theorem exists_smooth_radial_primitive
    {φ : ℝ → ℝ} {n : ℕ} {R : ℝ}
    (hφ : ContDiff ℝ ∞ φ)
    (hφsupp : tsupport φ ⊆ Ioo (0 : ℝ) R)
    (hR : 0 ≤ R) :
    ∃ g : ℝ → ℝ,
      ContDiff ℝ ∞ g ∧
      (∀ ρ, deriv g ρ = invProfile φ n ρ) ∧
      (∀ ρ, R ^ 2 < ρ → g ρ = 0) ∧
      (∀ r, 0 < r → 2 * r ^ n * deriv g (r ^ 2) = φ r) := by
  let h : ℝ → ℝ := invProfile φ n
  let g : ℝ → ℝ := fun ρ => ∫ t in R ^ 2..ρ, h t
  have hh : ContDiff ℝ ∞ h := invProfile_contDiff hφ hφsupp
  have hc : Continuous h := hh.continuous
  have hhas : ∀ ρ, HasDerivAt g (h ρ) ρ := by
    intro ρ
    simpa [g] using (hc.integral_hasStrictDerivAt (R ^ 2) ρ).hasDerivAt
  have hderiv : ∀ ρ, deriv g ρ = h ρ := by
    intro ρ
    exact (hhas ρ).deriv
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun ρ => (hhas ρ).differentiableAt, ?_⟩
    rw [funext hderiv]
    exact hh
  have hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0 := by
    intro ρ hρ
    simp only [g]
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht' : t ∈ Ioc (R ^ 2) ρ := by
      rw [uIoc_of_le hρ.le] at ht
      exact ht
    exact invProfile_eq_zero_of_sq_lt hR hφsupp ht'.1
  refine ⟨g, hg, ?_, hzero, ?_⟩
  · intro ρ
    simpa [h] using hderiv ρ
  · intro r hr
    have hfac : 2 * r ^ n * h (r ^ 2) = φ r := by
      simp only [h, invProfile, if_pos (sq_pos_of_pos hr), Real.sqrt_sq hr.le]
      field_simp [pow_ne_zero n hr.ne']
    rw [hderiv, hfac]

/-- Differentiating the factor identity gives the radial Laplace operator.
This is the exact form needed to feed the shell identity. -/
lemma radialODE_eq_deriv_of_factor
    {φ g : ℝ → ℝ} {n : ℕ}
    (hn : 0 < n) (hφ : ContDiff ℝ ∞ φ) (hg : ContDiff ℝ ∞ g)
    (hfactor : ∀ r, 0 < r → 2 * r ^ n * deriv g (r ^ 2) = φ r) :
    ∀ r, 0 < r →
      r ^ (n - 1) *
        (4 * r ^ 2 * deriv (deriv g) (r ^ 2) + 2 * n * deriv g (r ^ 2)) =
        deriv φ r := by
  intro r hr
  have hgd : ContDiff ℝ ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hpow : HasDerivAt (fun s : ℝ => s ^ n)
      (n * r ^ (n - 1)) r := by
    convert (hasDerivAt_id r).pow n using 1
    · rfl
    · exact Module.ext rfl
    · rfl
    · norm_num [id]
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · rfl
    · exact Module.ext rfl
    · rfl
    · norm_num [id]
  have hinner : HasDerivAt (fun s : ℝ => deriv g (s ^ 2))
      (deriv (deriv g) (r ^ 2) * (2 * r)) r := by
    convert ((hgd.differentiable (by simp) (r ^ 2)).hasDerivAt.comp r hsq) using 1
    · rfl
    · exact Module.ext rfl
    · rfl
  have hleft : HasDerivAt (fun s : ℝ => 2 * s ^ n * deriv g (s ^ 2))
      (2 * (n * r ^ (n - 1)) * deriv g (r ^ 2) +
        2 * r ^ n * (deriv (deriv g) (r ^ 2) * (2 * r))) r := by
    convert ((hasDerivAt_const r (2 : ℝ)).mul hpow).mul hinner using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · simp only [Pi.mul_apply]
      ring
  have hev : (fun s : ℝ => 2 * s ^ n * deriv g (s ^ 2)) =ᶠ[nhds r] φ := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact hfactor s hs
  have hright : HasDerivAt (fun s : ℝ => 2 * s ^ n * deriv g (s ^ 2))
      (deriv φ r) r :=
    ((hφ.differentiable (by simp) r).hasDerivAt).congr_of_eventuallyEq hev
  have heq := hleft.unique hright
  have hrpow : r ^ n = r ^ (n - 1) * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    exact pow_succ _ _
  rw [← heq, hrpow]
  ring

/-- The weak radial Laplace identity annihilates the derivative of every
smooth test compactly supported in `(0,R)`. -/
theorem integral_unitSphereRadialIntegral_mul_deriv_test_eq_zero
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hφsupp : tsupport φ ⊆ Ioo (0 : ℝ) R) :
    ∫ r in Ioi (0 : ℝ), unitSphereRadialIntegral u r * deriv φ r = 0 := by
  obtain ⟨g, hg, _, hzero, hfactor⟩ :=
    exists_smooth_radial_primitive hφ hφsupp hR
  have hgd : ContDiff ℝ ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hg' : ∀ ρ, 0 < ρ → HasDerivAt g (deriv g ρ) ρ := by
    intro ρ _
    exact (hg.differentiable (by simp) ρ).hasDerivAt
  have hg'' : ∀ ρ, 0 < ρ → HasDerivAt (deriv g) (deriv (deriv g) ρ) ρ := by
    intro ρ _
    exact (hgd.differentiable (by simp) ρ).hasDerivAt
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hode := radialODE_eq_deriv_of_factor hn hφ hg hfactor
  have hshell := integral_radius_unitSphereRadialIntegral_radialODE_eq_zero
    hU hu hR hball hg hg' hg'' hzero
  calc
    ∫ r in Ioi (0 : ℝ), unitSphereRadialIntegral u r * deriv φ r =
        ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * unitSphereRadialIntegral u r *
          (4 * r ^ 2 * deriv (deriv g) (r ^ 2) + 2 * n * deriv g (r ^ 2)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume)
        (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
      rw [← hode r hr]
      ring
    _ = 0 := hshell

end EvansLib

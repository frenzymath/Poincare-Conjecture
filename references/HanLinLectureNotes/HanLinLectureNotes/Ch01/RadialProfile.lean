import HanLinLectureNotes.Ch01.RadialMeanValueAux
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth radial profiles for the harmonic mean-value argument

The weak radial identity is parametrized by a smooth profile in the squared
radius. This module realizes every smooth compactly supported test on `(0, R)`
as such a profile.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff Interval
open InnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- The inverse profile for the map `g -> 2 * r^n * g'(r^2)`. -/
def invProfile (phi : Real -> Real) (n : Nat) (rho : Real) : Real :=
  if 0 < rho then phi (Real.sqrt rho) / (2 * (Real.sqrt rho) ^ n) else 0

lemma invProfile_eq_zero_of_sqrt_not_mem {phi : Real -> Real} {n : Nat}
    {rho : Real} (hrho : Real.sqrt rho ∉ tsupport phi) : invProfile phi n rho = 0 := by
  rw [invProfile]
  by_cases h : 0 < rho
  · rw [if_pos h, image_eq_zero_of_notMem_tsupport hrho, zero_div]
  · simp [h]

lemma invProfile_eq_zero_of_nonpos {phi : Real -> Real} {n : Nat} {rho : Real}
    {R : Real} (hphiSupp : tsupport phi ⊆ Ioo (0 : Real) R) (hrho : rho <= 0) :
    invProfile phi n rho = 0 := by
  apply invProfile_eq_zero_of_sqrt_not_mem
  rw [Real.sqrt_eq_zero_of_nonpos hrho]
  intro hmem
  exact (show (0 : Real) ∉ Ioo (0 : Real) R by simp) (hphiSupp hmem)

/-- The inverse profile is smooth across the zero extension when the test has a
support gap at zero. -/
lemma invProfile_contDiff {phi : Real -> Real} {n : Nat} {R : Real}
    (hphi : ContDiff Real ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : Real) R) :
    ContDiff Real ∞ (invProfile phi n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_or_ge x 0 with hx | hx
  · have hev : invProfile phi n =ᶠ[nhds x] (fun _ : Real => 0) := by
      filter_upwards [Metric.mem_nhds_iff.2 ⟨-x / 2, by linarith,
        fun y hy => by
          have habs : |y - x| < -x / 2 := by
            simpa [mem_ball, Real.dist_eq] using hy
          rw [abs_lt] at habs
          have : y < 0 := by linarith
          exact invProfile_eq_zero_of_nonpos (n := n) hphiSupp this.le⟩] with y hy
      exact hy
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · rcases eq_or_lt_of_le hx with rfl | hxpos
    · have hzero : (0 : Real) ∉ tsupport phi := by
        intro h0
        exact (show (0 : Real) ∉ Ioo (0 : Real) R by simp) (hphiSupp h0)
      have hopen : (tsupport phi)ᶜ ∈ nhds (0 : Real) :=
        (isClosed_tsupport phi).isOpen_compl.mem_nhds hzero
      obtain ⟨epsilon, hepsilon, hepsilonSub⟩ := Metric.mem_nhds_iff.1 hopen
      have hdelta : 0 < min 1 (epsilon ^ 2) :=
        lt_min (by norm_num) (sq_pos_of_pos hepsilon)
      have hev : invProfile phi n =ᶠ[nhds (0 : Real)] (fun _ : Real => 0) := by
        filter_upwards [Metric.mem_nhds_iff.2 ⟨min 1 (epsilon ^ 2), hdelta,
          fun y hy => by
            have hy' : |y| < min 1 (epsilon ^ 2) := by
              simpa [mem_ball, Real.dist_eq] using hy
            have hyupper : y < epsilon ^ 2 :=
              lt_of_le_of_lt (le_abs_self y)
                (lt_of_lt_of_le hy' (min_le_right _ _))
            have hsqrt : Real.sqrt y < epsilon := by
              by_cases hy0 : y <= 0
              · rw [Real.sqrt_eq_zero_of_nonpos hy0]
                exact hepsilon
              · have hypos : 0 < y := lt_of_not_ge hy0
                have hsnonneg : 0 <= Real.sqrt y := Real.sqrt_nonneg _
                have hsq : (Real.sqrt y) ^ 2 = y := Real.sq_sqrt hypos.le
                nlinarith
            have hs : Real.sqrt y ∈ ball (0 : Real) epsilon := by
              rw [mem_ball, Real.dist_eq]
              simpa [sub_zero, abs_of_nonneg (Real.sqrt_nonneg y)] using hsqrt
            exact invProfile_eq_zero_of_sqrt_not_mem (n := n) (hepsilonSub hs)⟩]
            with y hy
        exact hy
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hsqrt : ContDiffAt Real ∞ (fun y : Real => Real.sqrt y) x :=
        Real.contDiffAt_sqrt hxpos.ne'
      have hnum : ContDiffAt Real ∞ (fun y : Real => phi (Real.sqrt y)) x :=
        hphi.contDiffAt.comp x hsqrt
      have hden : ContDiffAt Real ∞
          (fun y : Real => 2 * (Real.sqrt y) ^ n) x :=
        contDiffAt_const.mul (hsqrt.pow n)
      have hquot : ContDiffAt Real ∞
          (fun y : Real => phi (Real.sqrt y) / (2 * (Real.sqrt y) ^ n)) x :=
        hnum.div hden (by positivity)
      have hev : invProfile phi n =ᶠ[nhds x]
          (fun y : Real => phi (Real.sqrt y) / (2 * (Real.sqrt y) ^ n)) := by
        filter_upwards [Metric.mem_nhds_iff.2 ⟨x / 2, by linarith,
          fun y hy => by
            have hy' : |y - x| < x / 2 := by
              simpa [mem_ball, Real.dist_eq] using hy
            have : 0 < y := by
              rw [abs_lt] at hy'
              linarith
            change (if 0 < y then phi (Real.sqrt y) /
              (2 * (Real.sqrt y) ^ n) else 0) =
                phi (Real.sqrt y) / (2 * (Real.sqrt y) ^ n)
            rw [if_pos this]⟩] with y hy
        exact hy
      exact hquot.congr_of_eventuallyEq hev

lemma invProfile_eq_zero_of_sq_lt {phi : Real -> Real} {n : Nat} {R rho : Real}
    (hR : 0 <= R) (hphiSupp : tsupport phi ⊆ Ioo (0 : Real) R)
    (hrho : R ^ 2 < rho) : invProfile phi n rho = 0 := by
  apply invProfile_eq_zero_of_sqrt_not_mem (n := n)
  intro hmem
  have hmemI := hphiSupp hmem
  have hrho0 : 0 <= rho := by nlinarith [sq_nonneg R]
  have hs : (Real.sqrt rho) ^ 2 = rho := Real.sq_sqrt hrho0
  have hsnonneg : 0 <= Real.sqrt rho := Real.sqrt_nonneg _
  have hsR : R < Real.sqrt rho := by nlinarith
  exact (not_lt_of_ge hmemI.2.le) hsR

/-- A smooth squared-radius profile realizing an arbitrary smooth test on
`(0, R)`. -/
theorem exists_smooth_radial_primitive
    {phi : Real -> Real} {n : Nat} {R : Real}
    (hphi : ContDiff Real ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : Real) R)
    (hR : 0 <= R) :
    ∃ g : Real -> Real,
      ContDiff Real ∞ g ∧
      (∀ rho, deriv g rho = invProfile phi n rho) ∧
      (∀ rho, R ^ 2 < rho -> g rho = 0) ∧
      (∀ r, 0 < r -> 2 * r ^ n * deriv g (r ^ 2) = phi r) := by
  let h : Real -> Real := invProfile phi n
  let g : Real -> Real := fun rho => ∫ t in R ^ 2..rho, h t
  have hh : ContDiff Real ∞ h := invProfile_contDiff hphi hphiSupp
  have hc : Continuous h := hh.continuous
  have hhas : ∀ rho, HasDerivAt g (h rho) rho := by
    intro rho
    simpa [g] using (hc.integral_hasStrictDerivAt (R ^ 2) rho).hasDerivAt
  have hderiv : ∀ rho, deriv g rho = h rho := by
    intro rho
    exact (hhas rho).deriv
  have hg : ContDiff Real ∞ g := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun rho => (hhas rho).differentiableAt, ?_⟩
    rw [funext hderiv]
    exact hh
  have hzero : ∀ rho, R ^ 2 < rho -> g rho = 0 := by
    intro rho hrho
    simp only [g]
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    have ht' : t ∈ Ioc (R ^ 2) rho := by
      rw [uIoc_of_le hrho.le] at ht
      exact ht
    exact invProfile_eq_zero_of_sq_lt hR hphiSupp ht'.1
  refine ⟨g, hg, ?_, hzero, ?_⟩
  · intro rho
    simpa [h] using hderiv rho
  · intro r hr
    have hfac : 2 * r ^ n * h (r ^ 2) = phi r := by
      simp only [h, invProfile, if_pos (sq_pos_of_pos hr), Real.sqrt_sq hr.le]
      field_simp [pow_ne_zero n hr.ne']
    rw [hderiv, hfac]

/-- Differentiating the factor identity gives the radial Laplace operator. -/
lemma radialODE_eq_deriv_of_factor
    {phi g : Real -> Real} {n : Nat}
    (hn : 0 < n) (hphi : ContDiff Real ∞ phi) (hg : ContDiff Real ∞ g)
    (hfactor : ∀ r, 0 < r -> 2 * r ^ n * deriv g (r ^ 2) = phi r) :
    ∀ r, 0 < r ->
      r ^ (n - 1) *
        (4 * r ^ 2 * deriv (deriv g) (r ^ 2) + 2 * n * deriv g (r ^ 2)) =
        deriv phi r := by
  intro r hr
  have hgd : ContDiff Real ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hpow : HasDerivAt (fun s : Real => s ^ n)
      (n * r ^ (n - 1)) r := by
    convert (hasDerivAt_id r).pow n using 1
    · rfl
    · exact Module.ext rfl
    · rfl
    · norm_num [id]
  have hsq : HasDerivAt (fun s : Real => s ^ 2) (2 * r) r := by
    convert (hasDerivAt_id r).pow 2 using 1
    · rfl
    · exact Module.ext rfl
    · rfl
    · norm_num [id]
  have hinner : HasDerivAt (fun s : Real => deriv g (s ^ 2))
      (deriv (deriv g) (r ^ 2) * (2 * r)) r := by
    convert ((hgd.differentiable (by simp) (r ^ 2)).hasDerivAt.comp r hsq) using 1
    · rfl
    · exact Module.ext rfl
    · rfl
  have hleft : HasDerivAt (fun s : Real => 2 * s ^ n * deriv g (s ^ 2))
      (2 * (n * r ^ (n - 1)) * deriv g (r ^ 2) +
        2 * r ^ n * (deriv (deriv g) (r ^ 2) * (2 * r))) r := by
    convert ((hasDerivAt_const r (2 : Real)).mul hpow).mul hinner using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · simp only [Pi.mul_apply]
      ring
  have hev : (fun s : Real => 2 * s ^ n * deriv g (s ^ 2)) =ᶠ[nhds r] phi := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact hfactor s hs
  have hright : HasDerivAt (fun s : Real => 2 * s ^ n * deriv g (s ^ 2))
      (deriv phi r) r :=
    ((hphi.differentiable (by simp) r).hasDerivAt).congr_of_eventuallyEq hev
  have heq := hleft.unique hright
  have hrpow : r ^ n = r ^ (n - 1) * r := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    exact pow_succ _ _
  rw [← heq, hrpow]
  ring

/-- The weak radial Laplace identity annihilates the derivative of every smooth
test compactly supported in `(0, R)`. -/
theorem integral_unitSphereRadialIntegral_mul_deriv_test_eq_zero
    [Nonempty (Fin n)] {U : Set (EuclideanSpace Real (Fin n))}
    {u : EuclideanSpace Real (Fin n) -> Real} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : Real} (hR : 0 <= R)
    (hball : closedBall (0 : EuclideanSpace Real (Fin n)) R ⊆ U)
    {phi : Real -> Real} (hphi : ContDiff Real ∞ phi)
    (hphiSupp : tsupport phi ⊆ Ioo (0 : Real) R) :
    ∫ r in Ioi (0 : Real), unitSphereRadialIntegral u r * deriv phi r = 0 := by
  obtain ⟨g, hg, _, hzero, hfactor⟩ :=
    exists_smooth_radial_primitive hphi hphiSupp hR
  have hgd : ContDiff Real ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hg' : ∀ rho, 0 < rho -> HasDerivAt g (deriv g rho) rho := by
    intro rho _
    exact (hg.differentiable (by simp) rho).hasDerivAt
  have hg'' : ∀ rho, 0 < rho ->
      HasDerivAt (deriv g) (deriv (deriv g) rho) rho := by
    intro rho _
    exact (hgd.differentiable (by simp) rho).hasDerivAt
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hode := radialODE_eq_deriv_of_factor hn hphi hg hfactor
  have hshell := integral_radius_unitSphereRadialIntegral_radialODE_eq_zero
    hU hu hR hball hg hg' hg'' hzero
  calc
    ∫ r in Ioi (0 : Real), unitSphereRadialIntegral u r * deriv phi r =
        ∫ r in Ioi (0 : Real), r ^ (n - 1) * unitSphereRadialIntegral u r *
          (4 * r ^ 2 * deriv (deriv g) (r ^ 2) + 2 * n * deriv g (r ^ 2)) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := volume)
        (show MeasurableSet (Ioi (0 : Real)) from measurableSet_Ioi)] with r hr
      rw [← hode r hr]
      ring
    _ = 0 := hshell

end HanLinLectureNotes.Ch01

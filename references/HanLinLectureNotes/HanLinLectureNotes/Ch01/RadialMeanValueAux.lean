import HanLinLectureNotes.Ch01.PolarIntegration
import HanLinLectureNotes.Ch01.RadialLaplacian
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Radial tests for the harmonic mean-value formula

This module specializes the weak Green identity to smooth squared-radial test
functions and rewrites the result as a one-dimensional shell equation.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : ℕ}

/-- A test function obtained by composing a profile with squared radius. -/
def squaredRadialTest (g : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  g (‖z‖ ^ 2)

/-- The one-variable expression for the Laplacian of a squared-radial test. -/
def squaredRadialLaplacianProfile (n : ℕ) (g' g'' : ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  4 * ‖z‖ ^ 2 * g'' (‖z‖ ^ 2) + 2 * n * g' (‖z‖ ^ 2)

/-- The integral of `u` on the unit sphere after radial scaling. -/
def unitSphereRadialIntegral [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) : ℝ :=
  ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    u (r • (omega : EuclideanSpace ℝ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- The spherical shell integral is continuous in the radius on a containing
closed ball. -/
lemma continuousOn_unitSphereRadialIntegral [Nonempty (Fin n)]
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {R : ℝ}
    (hu : ContinuousOn u (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
    ContinuousOn (unitSphereRadialIntegral u) (Icc (0 : ℝ) R) := by
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).exists_bound_of_continuousOn hu
  have hmem (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R)
      (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      r • (omega : EuclideanSpace ℝ (Fin n)) ∈
        closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    have homega : ‖(omega : EuclideanSpace ℝ (Fin n))‖ = 1 :=
      mem_sphere_zero_iff_norm.1 omega.2
    rw [mem_closedBall, dist_zero_right, norm_smul, homega, mul_one,
      Real.norm_eq_abs, abs_of_nonneg hr.1]
    exact hr.2
  have hcontOmega (r : ℝ) (hr : r ∈ Icc (0 : ℝ) R) :
      Continuous (fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        u (r • (omega : EuclideanSpace ℝ (Fin n)))) := by
    have hscale : Continuous
        (fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          r • (omega : EuclideanSpace ℝ (Fin n))) := by
      have hrcont : Continuous
          (fun _ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => r) :=
        continuous_const
      exact hrcont.smul continuous_subtype_val
    exact hu.comp_continuous hscale (fun omega => hmem r hr omega)
  have hcontRadius (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ContinuousOn
        (fun r : ℝ => u (r • (omega : EuclideanSpace ℝ (Fin n))))
        (Icc (0 : ℝ) R) :=
    hu.comp (continuous_id.smul continuous_const).continuousOn
      (fun r hr => hmem r hr omega)
  intro r0 hr0
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hcontOmega r hr).aestronglyMeasurable
  · refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [] with omega
    exact hC _ (hmem r hr omega)
  · filter_upwards [] with omega
    exact hcontRadius omega r0 hr0

/-- A profile vanishing beyond `R^2` gives a test supported in the closed ball
of radius `R`. -/
lemma tsupport_squaredRadialTest_subset_closedBall {g : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    tsupport (squaredRadialTest (n := n) g) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  rw [Function.mem_support] at hz
  rw [mem_closedBall, dist_zero_right]
  by_contra hzr
  exact hz (hzero _ (by nlinarith [norm_nonneg z]))

/-- Compact support of a squared-radial test. -/
lemma hasCompactSupport_squaredRadialTest {g : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    HasCompactSupport (squaredRadialTest (n := n) g) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).of_isClosed_subset
    (isClosed_tsupport _)
    (tsupport_squaredRadialTest_subset_closedBall hR hzero)

/-- The Laplacian of a smooth squared-radial test agrees almost everywhere
with its explicit radial profile. -/
lemma laplacian_squaredRadialTest_ae [Nonempty (Fin n)]
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho) :
    (fun z : EuclideanSpace ℝ (Fin n) =>
      Δ (squaredRadialTest (n := n) g) z) =ᵐ[volume]
        squaredRadialLaplacianProfile n g' g'' := by
  have hw : ContDiff ℝ ∞ (squaredRadialTest (n := n) g) :=
    hg.comp (contDiff_norm_sq ℝ)
  filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin n))] with z hz
  rw [laplacian_eq_sum_partialDeriv_iterate_two
    (hw.contDiffAt.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  exact sum_partialDeriv_two_comp_normSq hg' hg''
    (fun _ _ => hg.contDiffAt) (fun _ _ => rfl) hz

/-- The product of a locally harmonic function and the Laplacian of an
admissible squared-radial test is integrable. -/
lemma integrable_mul_laplacian_squaredRadialTest
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    Integrable (fun z => u z * Δ (squaredRadialTest (n := n) g) z) := by
  classical
  let w := squaredRadialTest (n := n) g
  have hw : ContDiff ℝ ∞ w := hg.comp (contDiff_norm_sq ℝ)
  have hwU : tsupport w ⊆ U :=
    (tsupport_squaredRadialTest_subset_closedBall hR hzero).trans hball
  have hwc : HasCompactSupport w :=
    hasCompactSupport_squaredRadialTest hR hzero
  have hpart (i : Fin n) :
      Integrable (fun z => u z * (partialDeriv i)^[2] w z) := by
    simp only [Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq]
    have hwi : ContDiff ℝ ∞ (partialDeriv i w) := partialDeriv_contDiff hw i
    have hwii : ContDiff ℝ ∞ (partialDeriv i (partialDeriv i w)) :=
      partialDeriv_contDiff hwi i
    have hwiU : tsupport (partialDeriv i w) ⊆ U :=
      (tsupport_partialDeriv_subset i).trans hwU
    have hwiiU : tsupport (partialDeriv i (partialDeriv i w)) ⊆ U :=
      (tsupport_partialDeriv_subset i).trans hwiU
    have hwic : HasCompactSupport (partialDeriv i w) :=
      hwc.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_partialDeriv_subset i)
    have hwiic : HasCompactSupport (partialDeriv i (partialDeriv i w)) :=
      hwic.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_partialDeriv_subset i)
    exact integrable_mul_of_continuousOn_of_tsupport_subset hU
      hu.contDiffOn.continuousOn hwii.continuous hwiic hwiiU
  have hsum : Integrable
      (fun z => ∑ i : Fin n, u z * (partialDeriv i)^[2] w z) :=
    integrable_finsetSum Finset.univ (fun i _ => hpart i)
  have hlap : (fun z => u z * Δ w z) =
      fun z => ∑ i : Fin n, u z * (partialDeriv i)^[2] w z := by
    funext z
    rw [laplacian_eq_sum_partialDeriv_iterate_two
      (hw.contDiffAt.of_le (WithTop.coe_le_coe.mpr
        (show (2 : ℕ∞) ≤ ⊤ from le_top))), Finset.mul_sum]
  rw [hlap]
  exact hsum

/-- The explicit radial Laplacian profile is integrable against a locally
harmonic function. -/
lemma integrable_mul_squaredRadialLaplacianProfile [Nonempty (Fin n)]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    Integrable
      (fun z => u z * squaredRadialLaplacianProfile n g' g'' z) := by
  have hint :=
    integrable_mul_laplacian_squaredRadialTest hU hu hR hball hg hzero
  apply hint.congr
  filter_upwards [laplacian_squaredRadialTest_ae hg hg' hg''] with z hz
  rw [hz]

/-- Weak Green identity specialized to squared-radial tests. -/
theorem integral_mul_squaredRadialLaplacianProfile_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    ∫ z, u z * squaredRadialLaplacianProfile n g' g'' z = 0 := by
  have hw : ContDiff ℝ ∞ (squaredRadialTest (n := n) g) :=
    hg.comp (contDiff_norm_sq ℝ)
  have hwU : tsupport (squaredRadialTest (n := n) g) ⊆ U :=
    (tsupport_squaredRadialTest_subset_closedBall hR hzero).trans hball
  have hweak := integral_mul_laplacian_eq_zero_of_harmonicOnNhd hU hu hw
    (hasCompactSupport_squaredRadialTest hR hzero) hwU
  calc
    ∫ z, u z * squaredRadialLaplacianProfile n g' g'' z =
        ∫ z, u z * Δ (squaredRadialTest (n := n) g) z := by
      apply integral_congr_ae
      filter_upwards [laplacian_squaredRadialTest_ae hg hg' hg''] with z hz
      rw [hz]
    _ = 0 := hweak

/-- Radius-outer shell form of the weak radial ODE. -/
theorem integral_radius_unitSphereRadialIntegral_radialODE_eq_zero
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * unitSphereRadialIntegral u r *
      (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2)) = 0 := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    u z * squaredRadialLaplacianProfile n g' g'' z
  have hf : Integrable f :=
    integrable_mul_squaredRadialLaplacianProfile hU hu hR hball hg hg' hg'' hzero
  have hpolar :=
    integral_eq_polar_radius (volume : Measure (EuclideanSpace ℝ (Fin n))) hf
  have hweak :=
    integral_mul_squaredRadialLaplacianProfile_eq_zero_of_harmonicOnNhd
      hU hu hR hball hg hg' hg'' hzero
  rw [hweak] at hpolar
  refine Eq.trans ?_ hpolar.symm
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume)
    (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
  have hinner :
      (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          f (r • (omega : EuclideanSpace ℝ (Fin n)))
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) =
        unitSphereRadialIntegral u r *
          (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2)) := by
    rw [unitSphereRadialIntegral, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards [] with omega
    have homega : ‖(omega : EuclideanSpace ℝ (Fin n))‖ = 1 :=
      mem_sphere_zero_iff_norm.1 omega.2
    have hrnorm : ‖r • (omega : EuclideanSpace ℝ (Fin n))‖ = r := by
      rw [norm_smul, homega, mul_one, Real.norm_eq_abs, abs_of_pos hr]
    simp only [f, squaredRadialLaplacianProfile]
    rw [hrnorm]
  rw [finrank_euclideanSpace, Fintype.card_fin, hinner]
  simp only [smul_eq_mul]
  ring

end HanLinLectureNotes.Ch01

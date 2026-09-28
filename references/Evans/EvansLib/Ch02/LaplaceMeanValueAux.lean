import EvansLib.Ch02.GreensIdentity
import EvansLib.Ch02.Laplace
import EvansLib.Ch02.PolarIntegration
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Evans, Ch. 2 §2.2.2 — radial tests for the Laplace mean-value formula

This file connects two pieces of infrastructure used in the compact-test-function
route to the mean-value formula:

* `sum_partialDeriv_two_comp_normSq` computes the Laplacian of a squared-radial
  function away from the origin;
* `integral_mul_laplacian_eq_zero_of_harmonicOnNhd` says that a harmonic function
  annihilates the Laplacian of a smooth compactly supported test function.

The resulting weak radial ODE identity is the exact analytic input needed before
solving the one-variable radial equation.  It deliberately does not claim the
ball mean-value formula: turning this family of smooth-test identities into a
sharp ball average still requires a radial layer-cake or approximation argument.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.2.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- A test function obtained by composing a one-variable profile with the
squared Euclidean radius. -/
def squaredRadialTest (g : ℝ → ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  g (‖z‖ ^ 2)

/-- The one-variable expression corresponding to the Laplacian of
`g (‖z‖²)`: `4 ‖z‖² g''(‖z‖²) + 2 n g'(‖z‖²)`. -/
def squaredRadialLaplacianProfile (n : ℕ) (g' g'' : ℝ → ℝ)
    (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  4 * ‖z‖ ^ 2 * g'' (‖z‖ ^ 2) + 2 * n * g' (‖z‖ ^ 2)

/-- The integral of `u` on the unit sphere after radial scaling by `r`. -/
def unitSphereRadialIntegral [Nonempty (Fin n)]
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) : ℝ :=
  ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    u (r • (omega : EuclideanSpace ℝ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- The spherical shell integral varies continuously with the radius as long
as the underlying function is continuous on the containing closed ball. -/
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
        u (r • (omega : EuclideanSpace ℝ (Fin n)))) :=
    by
      have hscale : Continuous (fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
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
  intro r₀ hr₀
  apply tendsto_integral_filter_of_norm_le_const
  · filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hcontOmega r hr).aestronglyMeasurable
  · refine ⟨C, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr
    filter_upwards [] with omega
    exact hC _ (hmem r hr omega)
  · filter_upwards [] with omega
    exact hcontRadius omega r₀ hr₀

/-- If a profile vanishes beyond `R²`, its squared-radial test is supported in
the closed ball of radius `R`. -/
lemma tsupport_squaredRadialTest_subset_closedBall {g : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
    tsupport (squaredRadialTest (n := n) g) ⊆
      closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
  apply closure_minimal _ isClosed_closedBall
  intro z hz
  rw [Function.mem_support] at hz
  rw [mem_closedBall, dist_zero_right]
  by_contra hzr
  exact hz (hzero _ (by nlinarith [norm_nonneg z]))

/-- A squared-radial test whose profile vanishes beyond `R²` has compact
support. -/
lemma hasCompactSupport_squaredRadialTest {g : ℝ → ℝ} {R : ℝ}
    (hR : 0 ≤ R) (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
    HasCompactSupport (squaredRadialTest (n := n) g) :=
  (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_squaredRadialTest_subset_closedBall hR hzero)

/-- The intrinsic Laplacian of a smooth squared-radial test agrees almost
everywhere with its one-variable radial expression.  The existing pointwise
formula excludes the origin; positive-dimensional Lebesgue measure makes that
single exceptional point null. -/
lemma laplacian_squaredRadialTest_ae [Nonempty (Fin n)]
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg'' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ) :
    (fun z : EuclideanSpace ℝ (Fin n) ↦ Δ (squaredRadialTest (n := n) g) z)
      =ᵐ[volume] squaredRadialLaplacianProfile n g' g'' := by
  have hw : ContDiff ℝ ∞ (squaredRadialTest (n := n) g) := by
    exact hg.comp (contDiff_norm_sq ℝ)
  filter_upwards [volume.ae_ne (0 : EuclideanSpace ℝ (Fin n))] with z hz
  rw [laplacian_eq_sum_partialDeriv_iterate_two
    (hw.contDiffAt.of_le (WithTop.coe_le_coe.mpr
      (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
  exact sum_partialDeriv_two_comp_normSq hg' hg''
    (fun _ _ ↦ hg.contDiffAt) (fun _ _ ↦ rfl) hz

/-- The product of a locally harmonic function with the Laplacian of an
admissible squared-radial test is integrable on the whole space. -/
lemma integrable_mul_laplacian_squaredRadialTest
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
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
    have hwi : ContDiff ℝ ∞ (partialDeriv i w) :=
      partialDeriv_contDiff hw i
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

/-- The explicit one-variable radial Laplacian profile is integrable against a
locally harmonic function under the hypotheses of the weak radial identity. -/
lemma integrable_mul_squaredRadialLaplacianProfile
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg'' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ)
    (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
    Integrable (fun z => u z * squaredRadialLaplacianProfile n g' g'' z) := by
  have hint := integrable_mul_laplacian_squaredRadialTest hU hu hR hball hg hzero
  apply hint.congr
  filter_upwards [laplacian_squaredRadialTest_ae hg hg' hg''] with z hz
  rw [hz]

/-- **Weak radial ODE identity for harmonic functions.**  If `u` is harmonic
on an open set containing `closedBall 0 R`, then for every smooth profile `g`
which vanishes beyond `R²`,

`∫ u(z) [4 ‖z‖² g''(‖z‖²) + 2 n g'(‖z‖²)] dz = 0`.

This is Green's identity specialized to compactly supported squared-radial test
functions.  It is a centered, smooth-test precursor of the ball mean-value
formula, not the mean-value formula itself. -/
theorem integral_mul_squaredRadialLaplacianProfile_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg'' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ)
    (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
    ∫ z, u z * squaredRadialLaplacianProfile n g' g'' z = 0 := by
  have hw : ContDiff ℝ ∞ (squaredRadialTest (n := n) g) := by
    exact hg.comp (contDiff_norm_sq ℝ)
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

/-- **Polar form of the weak radial ODE.** Under the hypotheses of the weak
radial identity, polar disintegration rewrites it as

`∫_{Sⁿ⁻¹} ∫₀^∞ rⁿ⁻¹ u(rω) (4r²g''(r²) + 2n g'(r²)) dr dω = 0`.

This is the one-variable distributional ODE from which the centered sphere and
ball mean-value formulas follow. -/
theorem integral_sphere_integral_radius_radialODE_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg'' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ)
    (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
    (∫ (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1),
        (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * u (r • (omega : EuclideanSpace ℝ (Fin n))) *
          (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2)))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) = 0 := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    u z * squaredRadialLaplacianProfile n g' g'' z
  have hf : Integrable f :=
    integrable_mul_squaredRadialLaplacianProfile hU hu hR hball hg hg' hg'' hzero
  have hpolar := integral_eq_polar (volume : Measure (EuclideanSpace ℝ (Fin n))) hf
  have hweak :=
    integral_mul_squaredRadialLaplacianProfile_eq_zero_of_harmonicOnNhd
      hU hu hR hball hg hg' hg'' hzero
  rw [hweak] at hpolar
  refine Eq.trans ?_ hpolar.symm
  apply integral_congr_ae
  filter_upwards [] with omega
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume)
    (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
  have homega : ‖(omega : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    mem_sphere_zero_iff_norm.1 omega.2
  have hrnorm : ‖r • (omega : EuclideanSpace ℝ (Fin n))‖ = r := by
    rw [norm_smul, homega, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  simp only [f, squaredRadialLaplacianProfile, smul_eq_mul]
  rw [finrank_euclideanSpace, Fintype.card_fin, hrnorm]
  ring

/-- **Shell-integral form of the weak radial ODE.** Writing
`Sᵤ(r) = ∫_{Sⁿ⁻¹} u(rω) dω`, the weak Green identity becomes the genuinely
one-dimensional statement

`∫₀^∞ rⁿ⁻¹ Sᵤ(r) (4r²g''(r²) + 2n g'(r²)) dr = 0`.

This is the radius-outer form used to solve for the spherical mean. -/
theorem integral_radius_unitSphereRadialIntegral_radialODE_eq_zero
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ ρ, 0 < ρ → HasDerivAt g (g' ρ) ρ)
    (hg'' : ∀ ρ, 0 < ρ → HasDerivAt g' (g'' ρ) ρ)
    (hzero : ∀ ρ, R ^ 2 < ρ → g ρ = 0) :
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

/-- A one-dimensional distributional pairing determines a shell function up to a
constant.  This is the fundamental-lemma step used after the radial ODE has
been solved: vanishing pairings with all smooth compactly supported tests in
`(0, R)` force `A = c` almost everywhere there. -/
lemma ae_eq_const_of_integral_contDiff_smul_eq_zero
    {A : ℝ → ℝ} {R c : ℝ}
    (hA : LocallyIntegrableOn A (Ioo (0 : ℝ) R) (volume : Measure ℝ))
    (hzero : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) R →
      ∫ t, φ t * (A t - c) ∂(volume : Measure ℝ) = 0) :
    ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) R → A t = c := by
  have hdist : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) R → A t - c = 0 := by
    let B : ℝ → ℝ := fun t => A t - c
    have hB : LocallyIntegrableOn B (Ioo (0 : ℝ) R) (volume : Measure ℝ) := by
      exact hA.sub (locallyIntegrableOn_const _)
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo hB
    intro φ hφ hφc hφU
    simpa [B, smul_eq_mul] using hzero φ hφ hφc hφU
  filter_upwards [hdist] with t ht
  intro htI
  linarith [ht htI]

end EvansLib

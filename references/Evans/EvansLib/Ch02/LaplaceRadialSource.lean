import EvansLib.Ch02.LaplaceMeanValueAux

/-!
# Sourced weak radial Laplace equation

The harmonic radial identity in `LaplaceMeanValueAux` is the zero-source case
of a more general statement.  For a smooth function `u`, Green's identity and
polar disintegration identify the radial test pairing of its spherical mean
with the corresponding pairing of the spherical mean of `Δu`.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

lemma integrable_mul_laplacian_squaredRadialTest_of_contDiffOn
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {R : ℝ} (hR : 0 ≤ R)
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
      hu.continuousOn hwii.continuous hwiic hwiiU
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

lemma integrable_mul_squaredRadialLaplacianProfile_of_contDiffOn
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    Integrable (fun z =>
      u z * squaredRadialLaplacianProfile n g' g'' z) := by
  have hint := integrable_mul_laplacian_squaredRadialTest_of_contDiffOn
    hU hu hR hball hg hzero
  apply hint.congr
  filter_upwards [laplacian_squaredRadialTest_ae hg hg' hg''] with z hz
  rw [hz]

lemma integrable_laplacian_mul_squaredRadialTest
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    Integrable (fun z => Δ u z * squaredRadialTest (n := n) g z) := by
  classical
  let w := squaredRadialTest (n := n) g
  have hw : ContDiff ℝ ∞ w := hg.comp (contDiff_norm_sq ℝ)
  have hwU : tsupport w ⊆ U :=
    (tsupport_squaredRadialTest_subset_closedBall hR hzero).trans hball
  have hwc : HasCompactSupport w :=
    hasCompactSupport_squaredRadialTest hR hzero
  have hright (i : Fin n) :
      Integrable (fun y => (partialDeriv i)^[2] u y * w y) := by
    simp only [Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq]
    have hui : ContDiffOn ℝ 1 (partialDeriv i u) U :=
      ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply
        contDiffOn_const)
    have huii : ContinuousOn (partialDeriv i (partialDeriv i u)) U :=
      (((hui.fderiv_of_isOpen hU (m := 0) (by norm_num)).clm_apply
        contDiffOn_const).continuousOn)
    exact integrable_mul_of_continuousOn_of_tsupport_subset hU huii
      hw.continuous hwc hwU
  have hsum0 : Integrable
      (fun y => ∑ i : Fin n, (partialDeriv i)^[2] u y * w y) :=
    integrable_finsetSum Finset.univ (fun i _ => hright i)
  have hsum : Integrable
      (fun y => (∑ i : Fin n, (partialDeriv i)^[2] u y) * w y) := by
    simpa only [Finset.sum_mul] using hsum0
  apply hsum.congr
  filter_upwards [] with y
  by_cases hy : y ∈ tsupport w
  · have huy : ContDiffAt ℝ 2 u y :=
      (hu y (hwU hy)).contDiffAt (hU.mem_nhds (hwU hy))
    rw [laplacian_eq_sum_partialDeriv_iterate_two huy]
  · have hw0 : w y = 0 := image_eq_zero_of_notMem_tsupport hy
    have htest0 : squaredRadialTest (n := n) g y = 0 := by
      simpa [w] using hw0
    simp [hw0, htest0]

/-- Green's identity for a squared-radial test, with its nonzero Laplacian
source retained. -/
theorem integral_mul_squaredRadialLaplacianProfile_eq_source
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    ∫ z, u z * squaredRadialLaplacianProfile n g' g'' z =
      ∫ z, Δ u z * squaredRadialTest (n := n) g z := by
  have hw : ContDiff ℝ ∞ (squaredRadialTest (n := n) g) :=
    hg.comp (contDiff_norm_sq ℝ)
  have hwU : tsupport (squaredRadialTest (n := n) g) ⊆ U :=
    (tsupport_squaredRadialTest_subset_closedBall hR hzero).trans hball
  calc
    ∫ z, u z * squaredRadialLaplacianProfile n g' g'' z =
        ∫ z, u z * Δ (squaredRadialTest (n := n) g) z := by
      apply integral_congr_ae
      filter_upwards [laplacian_squaredRadialTest_ae hg hg' hg''] with z hz
      rw [hz]
    _ = ∫ z, Δ u z * squaredRadialTest (n := n) g z :=
      integral_mul_laplacian_eq_integral_laplacian_mul hU hu hw
        (hasCompactSupport_squaredRadialTest hR hzero) hwU

/-- Polar form of the sourced weak radial equation. -/
theorem integral_radius_unitSphereRadialIntegral_radialODE_eq_source
    [Nonempty (Fin n)] {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 2 u U) {R : ℝ} (hR : 0 ≤ R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U)
    {g g' g'' : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hg' : ∀ rho, 0 < rho → HasDerivAt g (g' rho) rho)
    (hg'' : ∀ rho, 0 < rho → HasDerivAt g' (g'' rho) rho)
    (hzero : ∀ rho, R ^ 2 < rho → g rho = 0) :
    ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * unitSphereRadialIntegral u r *
        (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2)) =
      ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegral (Δ u) r * g (r ^ 2) := by
  let fleft : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    u z * squaredRadialLaplacianProfile n g' g'' z
  let fright : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    Δ u z * squaredRadialTest (n := n) g z
  have hfl : Integrable fleft :=
    integrable_mul_squaredRadialLaplacianProfile_of_contDiffOn
      hU hu hR hball hg hg' hg'' hzero
  have hfr : Integrable fright :=
    integrable_laplacian_mul_squaredRadialTest hU hu hR hball hg hzero
  have hpolarLeft :=
    integral_eq_polar_radius (volume : Measure (EuclideanSpace ℝ (Fin n))) hfl
  have hpolarRight :=
    integral_eq_polar_radius (volume : Measure (EuclideanSpace ℝ (Fin n))) hfr
  have hweak := integral_mul_squaredRadialLaplacianProfile_eq_source
    hU hu hR hball hg hg' hg'' hzero
  have hleft :
      (∫ r in Ioi (0 : ℝ), r ^ (n - 1) * unitSphereRadialIntegral u r *
        (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2))) =
        ∫ z, fleft z := by
    refine Eq.trans ?_ hpolarLeft.symm
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume)
      (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
    have hinner :
        (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          fleft (r • (omega : EuclideanSpace ℝ (Fin n)))
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
      simp only [fleft, squaredRadialLaplacianProfile]
      rw [hrnorm]
    rw [finrank_euclideanSpace, Fintype.card_fin, hinner]
    simp only [smul_eq_mul]
    ring
  have hright :
      (∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegral (Δ u) r * g (r ^ 2)) =
        ∫ z, fright z := by
    refine Eq.trans ?_ hpolarRight.symm
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem (μ := volume)
      (show MeasurableSet (Ioi (0 : ℝ)) from measurableSet_Ioi)] with r hr
    have hinner :
        (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          fright (r • (omega : EuclideanSpace ℝ (Fin n)))
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) =
          unitSphereRadialIntegral (Δ u) r * g (r ^ 2) := by
      rw [unitSphereRadialIntegral, ← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with omega
      have homega : ‖(omega : EuclideanSpace ℝ (Fin n))‖ = 1 :=
        mem_sphere_zero_iff_norm.1 omega.2
      have hrnorm : ‖r • (omega : EuclideanSpace ℝ (Fin n))‖ = r := by
        rw [norm_smul, homega, mul_one, Real.norm_eq_abs, abs_of_pos hr]
      simp only [fright, squaredRadialTest]
      rw [hrnorm]
    rw [finrank_euclideanSpace, Fintype.card_fin, hinner]
    simp only [smul_eq_mul]
    ring
  calc
    ∫ r in Ioi (0 : ℝ), r ^ (n - 1) * unitSphereRadialIntegral u r *
        (4 * r ^ 2 * g'' (r ^ 2) + 2 * n * g' (r ^ 2)) =
      ∫ z, fleft z := hleft
    _ = ∫ z, fright z := by simpa [fleft, fright] using hweak
    _ = ∫ r in Ioi (0 : ℝ), r ^ (n - 1) *
        unitSphereRadialIntegral (Δ u) r * g (r ^ 2) := hright.symm

end EvansLib

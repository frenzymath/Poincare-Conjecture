import HanLinLectureNotes.Ch01.Harmonic
import HanLinLectureNotes.Ch01.MeanValueShellConstancy
import HanLinLectureNotes.Ch01.RadialProfile
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Average

/-!
# Mean-value formulas for harmonic functions

This module completes the native radial-test argument and packages both the
spherical and solid-ball identities from Han--Lin Theorem 1.6.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- The preimage of a domain under translation by `x`. -/
def translatedPreimage (x : EuclideanSpace Real (Fin n))
    (U : Set (EuclideanSpace Real (Fin n))) :
    Set (EuclideanSpace Real (Fin n)) :=
  {z | x + z ∈ U}

lemma isOpen_translatedPreimage {x : EuclideanSpace Real (Fin n)}
    {U : Set (EuclideanSpace Real (Fin n))} (hU : IsOpen U) :
    IsOpen (translatedPreimage x U) := by
  exact hU.preimage (continuous_const.add continuous_id)

/-- Translation preserves local harmonicity. -/
lemma harmonicOnNhd_translatedPreimage
    {x : EuclideanSpace Real (Fin n)}
    {U : Set (EuclideanSpace Real (Fin n))}
    {u : EuclideanSpace Real (Fin n) -> Real}
    (hu : HarmonicOnNhd u U) :
    HarmonicOnNhd (fun z => u (x + z)) (translatedPreimage x U) := by
  intro z hz
  have hzU : x + z ∈ U := hz
  have hpoint := hu (x + z) hzU
  refine ⟨hpoint.1.comp z (by fun_prop), ?_⟩
  have hlap : Δ (fun w : EuclideanSpace Real (Fin n) => u (x + w)) =
      fun w => Δ u (x + w) := by
    rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
      laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    funext w
    apply Finset.sum_congr rfl
    intro i hi
    rw [iteratedFDeriv_comp_add_left]
  rw [hlap]
  convert hpoint.2.comp_tendsto
    (continuous_const.add continuous_id).continuousAt using 1
  · rfl
  · rfl

/-- The integral of `u` on the unit sphere after radial scaling around `x`. -/
def unitSphereRadialIntegralAt [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (x : EuclideanSpace Real (Fin n)) (r : Real) : Real :=
  ∫ omega : sphere (0 : EuclideanSpace Real (Fin n)) 1,
    u (x + r • (omega : EuclideanSpace Real (Fin n)))
      ∂((volume : Measure (EuclideanSpace Real (Fin n))).toSphere)

/-- The normalized unit-sphere average after radial scaling around `x`. -/
def unitSphereRadialAverageAt [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (x : EuclideanSpace Real (Fin n)) (r : Real) : Real :=
  average
    ((volume : Measure (EuclideanSpace Real (Fin n))).toSphere)
    (fun omega : sphere (0 : EuclideanSpace Real (Fin n)) 1 =>
      u (x + r • (omega : EuclideanSpace Real (Fin n))))

lemma unitSphereRadialAverageAt_eq [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (x : EuclideanSpace Real (Fin n)) (r : Real) :
    unitSphereRadialAverageAt u x r =
      (((volume : Measure (EuclideanSpace Real (Fin n))).toSphere).real univ)⁻¹ *
        unitSphereRadialIntegralAt u x r := by
  rw [unitSphereRadialAverageAt, MeasureTheory.average_eq]
  rfl

lemma closedBall_zero_subset_translatedPreimage
    {x : EuclideanSpace Real (Fin n)}
    {U : Set (EuclideanSpace Real (Fin n))} {R : Real}
    (hball : closedBall x R ⊆ U) :
    closedBall (0 : EuclideanSpace Real (Fin n)) R ⊆
      translatedPreimage x U := by
  intro z hz
  apply hball
  rw [mem_closedBall, dist_self_add_left]
  rw [mem_closedBall, dist_zero_right] at hz
  exact hz

/-- The spherical shell integral of a harmonic function centered at zero is
constant from radius zero through every admissible closed ball. -/
theorem unitSphereRadialIntegral_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)]
    {U : Set (EuclideanSpace Real (Fin n))}
    {u : EuclideanSpace Real (Fin n) -> Real} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : Real} (hR : 0 < R)
    (hball : closedBall (0 : EuclideanSpace Real (Fin n)) R ⊆ U) :
    ∀ r ∈ Icc (0 : Real) R,
      unitSphereRadialIntegral u r = unitSphereRadialIntegral u 0 := by
  have hucont : ContinuousOn u
      (closedBall (0 : EuclideanSpace Real (Fin n)) R) :=
    hu.contDiffOn.continuousOn.mono hball
  have hScont : ContinuousOn (unitSphereRadialIntegral u) (Icc (0 : Real) R) :=
    continuousOn_unitSphereRadialIntegral hucont
  have hSloc : LocallyIntegrableOn (unitSphereRadialIntegral u)
      (Ioo (0 : Real) R) (volume : Measure Real) :=
    (hScont.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hderiv : ∀ (phi : Real -> Real), ContDiff Real ∞ phi ->
      HasCompactSupport phi -> tsupport phi ⊆ Ioo (0 : Real) R ->
      ∫ t, unitSphereRadialIntegral u t * deriv phi t
        ∂(volume : Measure Real) = 0 := by
    intro phi hphi _hphiCompact hphiSupp
    have hset := integral_unitSphereRadialIntegral_mul_deriv_test_eq_zero
      hU hu hR.le hball hphi hphiSupp
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ioi (0 : Real))
      (f := fun t => unitSphereRadialIntegral u t * deriv phi t)]
    · exact hset
    · intro t ht
      have htmem : t ∉ tsupport phi := by
        intro htphi
        exact ht (hphiSupp htphi).1
      rw [deriv_of_notMem_tsupport htmem, mul_zero]
  obtain ⟨c, hcae⟩ :=
    exists_ae_eq_const_of_integral_mul_deriv_eq_zero hSloc hderiv
  have hae : unitSphereRadialIntegral u =ᵐ[
      (volume : Measure Real).restrict (Ioo (0 : Real) R)] fun _ => c := by
    change ∀ᵐ t ∂(volume : Measure Real).restrict (Ioo (0 : Real) R),
      unitSphereRadialIntegral u t = c
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hcae
  have heqOpen : EqOn (unitSphereRadialIntegral u) (fun _ => c)
      (Ioo (0 : Real) R) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
      (hScont.mono Ioo_subset_Icc_self) continuousOn_const
  have heqClosed : EqOn (unitSphereRadialIntegral u) (fun _ => c)
      (Icc (0 : Real) R) := by
    apply heqOpen.of_subset_closure hScont continuousOn_const Ioo_subset_Icc_self
    rw [closure_Ioo hR.ne]
  intro r hr
  exact (heqClosed hr).trans (heqClosed ⟨le_rfl, hR.le⟩).symm

/-- The spherical shell integral centered at an arbitrary point is constant
from radius zero through every admissible closed ball. -/
theorem unitSphereRadialIntegralAt_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)]
    {U : Set (EuclideanSpace Real (Fin n))}
    {u : EuclideanSpace Real (Fin n) -> Real} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {x : EuclideanSpace Real (Fin n)}
    {R : Real} (hR : 0 < R) (hball : closedBall x R ⊆ U) :
    ∀ r ∈ Icc (0 : Real) R,
      unitSphereRadialIntegralAt u x r = unitSphereRadialIntegralAt u x 0 := by
  let V := translatedPreimage x U
  let v : EuclideanSpace Real (Fin n) -> Real := fun z => u (x + z)
  have hV : IsOpen V := isOpen_translatedPreimage hU
  have hv : HarmonicOnNhd v V := by
    simpa [V, v] using (harmonicOnNhd_translatedPreimage (x := x) hu)
  have hVball : closedBall (0 : EuclideanSpace Real (Fin n)) R ⊆ V :=
    closedBall_zero_subset_translatedPreimage hball
  have hcenter := unitSphereRadialIntegral_eq_zero_of_harmonicOnNhd
    hV hv hR hVball
  intro r hr
  simpa [unitSphereRadialIntegralAt, unitSphereRadialIntegral, v] using
    hcenter r hr

/-- At radius zero, the spherical integral is the value at the center times
the surface mass of the unit sphere. -/
lemma unitSphereRadialIntegralAt_zero [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (x : EuclideanSpace Real (Fin n)) :
    unitSphereRadialIntegralAt u x 0 =
      n * volume.real (ball (0 : EuclideanSpace Real (Fin n)) 1) * u x := by
  rw [unitSphereRadialIntegralAt]
  simp only [zero_smul, add_zero]
  rw [integral_const]
  simp [Measure.toSphere_real_apply_univ, smul_eq_mul]

@[simp] lemma unitSphereRadialAverageAt_zero [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (x : EuclideanSpace Real (Fin n)) :
    unitSphereRadialAverageAt u x 0 = u x := by
  rw [unitSphereRadialAverageAt_eq, unitSphereRadialIntegralAt_zero,
    Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin]
  have hn : (n : Real) ≠ 0 := by
    exact_mod_cast (Fin.pos_iff_nonempty.mpr inferInstance).ne'
  have hvol : volume.real
      (ball (0 : EuclideanSpace Real (Fin n)) 1) ≠ 0 := by
    rw [Measure.real]
    exact (ENNReal.toReal_pos
      (measure_ball_pos volume (0 : EuclideanSpace Real (Fin n)) one_pos).ne'
      measure_ball_lt_top.ne).ne'
  field_simp

/-- A locally harmonic function on an open set has the spherical mean-value
property on every admissible closed ball. -/
theorem HarmonicOnNhd.hasSphericalMeanValueProperty [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : HarmonicOnNhd u U) (hU : IsOpen U) :
    HasSphericalMeanValueProperty u U := by
  intro x r hr hball
  change u x = unitSphereRadialAverageAt u x r
  have hshell := unitSphereRadialIntegralAt_eq_zero_of_harmonicOnNhd
    hU hu hr hball r ⟨hr.le, le_rfl⟩
  let massInv : Real :=
    (((volume : Measure (EuclideanSpace Real (Fin n))).toSphere).real univ)⁻¹
  calc
    u x = unitSphereRadialAverageAt u x 0 :=
      (unitSphereRadialAverageAt_zero u x).symm
    _ = massInv * unitSphereRadialIntegralAt u x 0 := by
      exact unitSphereRadialAverageAt_eq u x 0
    _ = massInv * unitSphereRadialIntegralAt u x r := by rw [hshell]
    _ = unitSphereRadialAverageAt u x r :=
      (unitSphereRadialAverageAt_eq u x r).symm

/-- The radial density has mass `r^n / n` on `(0, r)` in positive dimension. -/
lemma integral_Ioo_pow_nat_sub_one [Nonempty (Fin n)] {r : Real} (hr : 0 < r) :
    ∫ t in Ioo (0 : Real) r, t ^ (n - 1) = r ^ n / n := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hr.le,
    integral_pow, Nat.sub_add_cancel hn]
  simp only [zero_pow hn.ne', sub_zero]
  rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hn.ne')]
  norm_num

/-- Constant spherical shells give the corresponding solid-ball integral. -/
theorem setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt
    [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)} {r : Real} (hr : 0 < r)
    (hint : IntegrableOn u (ball x r) volume)
    (hshell : ∀ t ∈ Ioo (0 : Real) r,
      unitSphereRadialIntegralAt u x t =
        n * volume.real (ball (0 : EuclideanSpace Real (Fin n)) 1) * u x) :
    ∫ y in ball x r, u y = volume.real (ball x r) * u x := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hpolar := setIntegral_ball_eq_polar_radius_add
    (volume : Measure (EuclideanSpace Real (Fin n))) x hint
  have hvol : volume.real (ball x r) =
      r ^ n * volume.real (ball (0 : EuclideanSpace Real (Fin n)) 1) := by
    rw [Measure.real, Measure.real, Measure.addHaar_ball_of_pos volume x hr,
      finrank_euclideanSpace_fin, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity)]
  calc
    ∫ y in ball x r, u y =
        ∫ t in Ioo (0 : Real) r, t ^ (n - 1) *
          unitSphereRadialIntegralAt u x t := by
      simpa only [finrank_euclideanSpace_fin, smul_eq_mul,
        unitSphereRadialIntegralAt] using hpolar
    _ = ∫ t in Ioo (0 : Real) r, t ^ (n - 1) *
          (n * volume.real (ball (0 : EuclideanSpace Real (Fin n)) 1) * u x) := by
      exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by rw [hshell t ht]
    _ = volume.real (ball x r) * u x := by
      rw [integral_mul_const, integral_Ioo_pow_nat_sub_one hr, hvol]
      field_simp

theorem setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt_eq_zero
    [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)} {r : Real} (hr : 0 < r)
    (hint : IntegrableOn u (ball x r) volume)
    (hshell : ∀ t ∈ Ioo (0 : Real) r,
      unitSphereRadialIntegralAt u x t = unitSphereRadialIntegralAt u x 0) :
    ∫ y in ball x r, u y = volume.real (ball x r) * u x := by
  apply setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt hr hint
  intro t ht
  rw [hshell t ht, unitSphereRadialIntegralAt_zero]

/-- A locally harmonic function on an open set has the solid-ball mean-value
property on every admissible closed ball. -/
theorem HarmonicOnNhd.hasBallMeanValueProperty [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : HarmonicOnNhd u U) (hU : IsOpen U) :
    HasBallMeanValueProperty u U := by
  intro x r hr hball
  have hint : IntegrableOn u (ball x r) volume :=
    integrableOn_ball_of_continuousOn hu.contDiffOn.continuousOn hball
  have hshell : ∀ t ∈ Ioo (0 : Real) r,
      unitSphereRadialIntegralAt u x t = unitSphereRadialIntegralAt u x 0 := by
    intro t ht
    exact unitSphereRadialIntegralAt_eq_zero_of_harmonicOnNhd
      hU hu hr hball t ⟨ht.1.le, ht.2.le⟩
  have hI := setIntegral_ball_eq_volume_mul_of_unitSphereRadialIntegralAt_eq_zero
    hr hint hshell
  rw [setAverage_eq, hI, smul_eq_mul]
  have hvol : 0 < volume.real (ball x r) := measureReal_ball_pos hr
  field_simp

/-- Han--Lin Theorem 1.6: every harmonic function on an open set satisfies both
mean-value identities. -/
theorem IsHarmonicOn.hasMeanValueProperties [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {U : Set (EuclideanSpace Real (Fin n))}
    (hu : IsHarmonicOn u U) (hU : IsOpen U) :
    HasMeanValueProperties u U := by
  have hnhd : HarmonicOnNhd u U :=
    (harmonicOnNhd_iff_isHarmonicOn hU).2 hu
  exact ⟨hu.continuousOn,
    HarmonicOnNhd.hasSphericalMeanValueProperty hnhd hU,
    HarmonicOnNhd.hasBallMeanValueProperty hnhd hU⟩

end HanLinLectureNotes.Ch01

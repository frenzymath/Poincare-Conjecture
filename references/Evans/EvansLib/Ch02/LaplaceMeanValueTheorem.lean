import EvansLib.Ch02.LaplaceMeanValueFormula
import EvansLib.Ch02.LaplaceRadialProfile
import EvansLib.Ch02.LaplaceShellConstancy

/-!
# Evans, Ch. 2 - the mean-value theorem for harmonic functions

This file composes the compact radial-test argument developed in the preceding
modules.  The weak Green identity gives a vanishing distributional derivative
for the spherical shell integral.  Distributional constancy and continuity at
radius zero then give the spherical mean-value formula, and polar integration
gives the solid-ball formula packaged as `HasBallMeanValueProperty`.
-/

open MeasureTheory Metric Set
open scoped ContDiff Real
open InnerProductSpace Laplacian

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The spherical shell integral of a harmonic function centered at zero is
constant from radius zero through every closed ball contained in the domain. -/
theorem unitSphereRadialIntegral_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {R : ℝ} (hR : 0 < R)
    (hball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ U) :
    ∀ r ∈ Icc (0 : ℝ) R,
      unitSphereRadialIntegral u r = unitSphereRadialIntegral u 0 := by
  have hucont : ContinuousOn u
      (closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    hu.contDiffOn.continuousOn.mono hball
  have hScont : ContinuousOn (unitSphereRadialIntegral u) (Icc (0 : ℝ) R) :=
    continuousOn_unitSphereRadialIntegral hucont
  have hSloc : LocallyIntegrableOn (unitSphereRadialIntegral u)
      (Ioo (0 : ℝ) R) (volume : Measure ℝ) :=
    (hScont.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo
  have hderiv : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) R →
      ∫ t, unitSphereRadialIntegral u t * deriv φ t
        ∂(volume : Measure ℝ) = 0 := by
    intro φ hφ _hφc hφsupp
    have hset := integral_unitSphereRadialIntegral_mul_deriv_test_eq_zero
      hU hu hR.le hball hφ hφsupp
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ioi (0 : ℝ)) (f := fun t =>
        unitSphereRadialIntegral u t * deriv φ t)]
    · exact hset
    · intro t ht
      have htmem : t ∉ tsupport φ := by
        intro htφ
        exact ht (hφsupp htφ).1
      rw [deriv_of_notMem_tsupport htmem, mul_zero]
  obtain ⟨c, hcae⟩ :=
    exists_ae_eq_const_of_integral_mul_deriv_eq_zero hSloc hderiv
  have hae : unitSphereRadialIntegral u =ᵐ[
      (volume : Measure ℝ).restrict (Ioo (0 : ℝ) R)] fun _ => c := by
    change ∀ᵐ t ∂(volume : Measure ℝ).restrict (Ioo (0 : ℝ) R),
      unitSphereRadialIntegral u t = c
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact hcae
  have heqOpen : Set.EqOn (unitSphereRadialIntegral u) (fun _ => c)
      (Ioo (0 : ℝ) R) :=
    Measure.eqOn_open_of_ae_eq hae isOpen_Ioo
      (hScont.mono Ioo_subset_Icc_self) continuousOn_const
  have heqClosed : Set.EqOn (unitSphereRadialIntegral u) (fun _ => c)
      (Icc (0 : ℝ) R) := by
    apply heqOpen.of_subset_closure hScont continuousOn_const Ioo_subset_Icc_self
    rw [closure_Ioo hR.ne]
  intro r hr
  exact (heqClosed hr).trans (heqClosed ⟨le_rfl, hR.le⟩).symm

/-- The spherical shell integral centered at an arbitrary point is constant
from radius zero through every admissible closed ball. -/
theorem unitSphereRadialIntegralAt_eq_zero_of_harmonicOnNhd
    [Nonempty (Fin n)]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {x : EuclideanSpace ℝ (Fin n)}
    {R : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ U) :
    ∀ r ∈ Icc (0 : ℝ) R,
      unitSphereRadialIntegralAt u x r = unitSphereRadialIntegralAt u x 0 := by
  let V := translatedPreimage x U
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z => u (x + z)
  have hV : IsOpen V := isOpen_translatedPreimage hU
  have hv : HarmonicOnNhd v V := by
    simpa [V, v] using (harmonicOnNhd_translatedPreimage (x := x) hu)
  have hVball : closedBall (0 : EuclideanSpace ℝ (Fin n)) R ⊆ V :=
    closedBall_zero_subset_translatedPreimage hball
  have hcenter := unitSphereRadialIntegral_eq_zero_of_harmonicOnNhd
    hV hv hR hVball
  intro r hr
  simpa [unitSphereRadialIntegralAt, unitSphereRadialIntegral, v] using
    hcenter r hr

/-- **Spherical form of Evans's Laplace mean-value theorem.**  The integral on
the unit sphere after scaling by `r` equals its surface mass times the value at
the center.  Dividing by that mass is the usual spherical average formula. -/
theorem unitSphereRadialIntegralAt_eq_volume_mul_of_harmonicOnNhd
    [Nonempty (Fin n)]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U)
    (hu : HarmonicOnNhd u U) {x : EuclideanSpace ℝ (Fin n)}
    {R r : ℝ} (hR : 0 < R) (hball : closedBall x R ⊆ U)
    (hr : r ∈ Icc (0 : ℝ) R) :
    unitSphereRadialIntegralAt u x r =
      n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) * u x := by
  rw [unitSphereRadialIntegralAt_eq_zero_of_harmonicOnNhd hU hu hR hball r hr,
    unitSphereRadialIntegralAt_zero]

/-- **Evans's Laplace mean-value theorem.** Every harmonic function on an open
set has the solid-ball mean-value property on every ball whose closure lies in
the set. -/
theorem HarmonicOnNhd.hasBallMeanValueProperty [Nonempty (Fin n)]
    {U : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : HarmonicOnNhd u U)
    (hU : IsOpen U) : HasBallMeanValueProperty u U := by
  apply hasBallMeanValueProperty_of_unitSphereRadialIntegralAt_eq_zero
    hu.contDiffOn.continuousOn
  intro x r hr hball t ht
  exact unitSphereRadialIntegralAt_eq_zero_of_harmonicOnNhd
    hU hu hr hball t ⟨ht.1.le, ht.2.le⟩

end EvansLib

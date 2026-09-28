import EvansLib.Ch02.WaveEnergy

/-!
# Continuity of the wave-energy fields

The energy method differentiates and integrates the pointwise density and flux.
This file records the basic regularity bridge: a `C²` wave has continuous first
derivatives, hence continuous energy density and flux fields.  Keeping these
facts separate from the algebraic conservation identity makes them available to
both fixed-domain and moving-ball integration arguments.
-/

open scoped BigOperators

noncomputable section

namespace EvansLib

/-- The time derivative of a `C²` space-time field is continuous. -/
lemma continuous_waveTimeDerivative_of_contDiff {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (waveTimeDerivative u) := by
  apply continuous_iff_continuousAt.2
  intro p
  change ContinuousAt (fun q => (fderiv ℝ u q) (timeDir n)) p
  exact (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt.clm_apply
    continuousAt_const

/-- Each spatial derivative of a `C²` space-time field is continuous. -/
lemma continuous_waveSpatialDerivative_of_contDiff {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin n) :
    Continuous (waveSpatialDerivative u i) := by
  apply continuous_iff_continuousAt.2
  intro p
  change ContinuousAt (fun q => (fderiv ℝ u q) (spaceDir n i)) p
  exact (hu.contDiffAt.fderiv_right (m := 1) (by norm_num)).continuousAt.clm_apply
    continuousAt_const

/-- The pointwise wave-energy density is continuous for a `C²` field. -/
lemma continuous_waveEnergyDensity_of_contDiff {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (waveEnergyDensity u) := by
  unfold waveEnergyDensity
  exact (continuous_waveTimeDerivative_of_contDiff hu).pow 2 |>.add
    (continuous_finsetSum Finset.univ (fun i _ =>
      (continuous_waveSpatialDerivative_of_contDiff hu i).pow 2))

/-- Every spatial component of the wave-energy flux is continuous for a `C²` field. -/
lemma continuous_waveEnergyFlux_of_contDiff {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u) (i : Fin n) :
    Continuous (waveEnergyFlux u i) := by
  unfold waveEnergyFlux
  exact (continuous_const.mul (continuous_waveTimeDerivative_of_contDiff hu)).mul
    (continuous_waveSpatialDerivative_of_contDiff hu i)

/-- The normal component of the wave-energy flux is continuous for a `C²` field. -/
lemma continuous_waveNormalEnergyFlux_of_contDiff {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u) (ν : EuclideanℝN n) :
    Continuous (waveNormalEnergyFlux u ν) := by
  unfold waveNormalEnergyFlux
  exact continuous_finsetSum Finset.univ (fun i _ =>
    (continuous_const.mul (continuous_waveEnergyFlux_of_contDiff hu i)))

end EvansLib

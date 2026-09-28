import MorganTianLib.Ch01.BishopGromovManifold
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Morgan--Tian Ch. 1, Issue 16: the flat model measure bridge

The comparison denominator in `BishopGromovBall` is defined as a Haar chart
integral.  In the flat case its density is identically one, so this abstract
object agrees exactly with the ordinary Euclidean volume of a metric ball.
This is the source-faithful `k = 0` model-space measure identification; the
corresponding curved model-manifold construction is a separate obligation.
-/

open MeasureTheory Measure Metric Set Module Filter
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [Nontrivial E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-! ### Flat density and ball measure -/

/-- **Math.** The flat model density is one everywhere, including its totalized value at the
origin. -/
theorem modelDensity_zero_eq_one (x : E) : modelDensity (E := E) 0 x = 1 := by
  by_cases hx : ‖x‖ = 0
  · simp [modelDensity, hx]
  · simp [modelDensity, hx, snK_zero_left]

/-- **Math.** For `k = 0`, the abstract model ball volume is exactly Euclidean ball volume. -/
theorem modelBallVolume_zero_eq_volume_ball (r : ℝ) :
    modelBallVolume (volume : Measure E) 0 r = volume (Metric.ball (0 : E) r) := by
  rw [modelBallVolume]
  have hden : (fun x : E => ENNReal.ofReal (modelDensity (E := E) 0 x)) =
      (fun _ : E => (1 : ℝ≥0∞)) := by
    funext x
    rw [modelDensity_zero_eq_one (E := E) x, ENNReal.ofReal_one]
  rw [hden, setLIntegral_one]

/-- **Math.** The flat model ball has Mathlib's closed-form Euclidean power law. -/
theorem modelBallVolume_zero_eq_euclidean_power (r : ℝ) :
    modelBallVolume (volume : Measure E) 0 r =
      (ENNReal.ofReal r) ^ Module.finrank ℝ E *
        ENNReal.ofReal
          (Real.sqrt Real.pi ^ Module.finrank ℝ E /
            Real.Gamma (Module.finrank ℝ E / 2 + 1)) := by
  rw [modelBallVolume_zero_eq_volume_ball (E := E) r]
  exact InnerProductSpace.volume_ball (0 : E) r

end MorganTianLib

end

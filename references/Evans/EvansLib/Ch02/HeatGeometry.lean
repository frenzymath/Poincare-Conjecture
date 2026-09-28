import EvansLib.Ch02.HeatMaxPrinciple
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Space-time measure geometry for the heat equation

This file records the canonical measure-preserving identification
`SpaceTime n \simeq R x R^n` obtained by splitting off the time coordinate.  The
resulting Fubini formula is stated using `toSpaceTime`, so later heat-equation
arguments can integrate directly in the time and space variables used by Evans.
-/

open MeasureTheory

noncomputable section

namespace EvansLib

/-- The canonical measurable identification of space-time with time times space. -/
def spaceTimeMeasurableEquiv (n : ℕ) :
    SpaceTime n ≃ᵐ ℝ × EuclideanSpace ℝ (Fin n) :=
  (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm.trans <|
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0).trans <|
      MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (MeasurableEquiv.toLp 2 (Fin n → ℝ))

@[simp] theorem spaceTimeMeasurableEquiv_apply (n : ℕ) (p : SpaceTime n) :
    spaceTimeMeasurableEquiv n p = (p 0, spacePart p) := by
  rfl

@[simp] theorem spaceTimeMeasurableEquiv_symm_apply (n : ℕ)
    (q : ℝ × EuclideanSpace ℝ (Fin n)) :
    (spaceTimeMeasurableEquiv n).symm q = toSpaceTime q.1 q.2 := by
  apply (spaceTimeMeasurableEquiv n).injective
  simp

/-- Splitting the time coordinate from space-time preserves Lebesgue measure. -/
theorem spaceTimeMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (spaceTimeMeasurableEquiv n) := by
  have h_toPi :
      MeasurePreserving (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (n + 1))
  have h_split :
      MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
  have h_tail :
      MeasurePreserving
        (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.toLp 2 (Fin n → ℝ)))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        ((volume : Measure ℝ).prod
          (volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    convert (MeasurePreserving.id (volume : Measure ℝ)).prod
      (PiLp.volume_preserving_toLp (Fin n)) using 1
    rfl
  have hcomp := h_tail.comp (h_split.comp h_toPi)
  have hfun : (spaceTimeMeasurableEquiv n : SpaceTime n →
      ℝ × EuclideanSpace ℝ (Fin n)) =
      (Prod.map (id : ℝ → ℝ) (MeasurableEquiv.toLp 2 (Fin n → ℝ))) ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0) ∘
          (MeasurableEquiv.toLp 2 (Fin (n + 1) → ℝ)).symm := by
    funext p
    rfl
  rw [hfun]
  exact hcomp

/-- Fubini's theorem on space-time, written in Evans's `(t,x)` coordinates. -/
theorem integral_toSpaceTime {n : ℕ} {f : SpaceTime n → ℝ} (hf : Integrable f) :
    ∫ p, f p = ∫ t : ℝ, ∫ x : EuclideanSpace ℝ (Fin n), f (toSpaceTime t x) := by
  let e := spaceTimeMeasurableEquiv n
  have he : MeasurePreserving e := spaceTimeMeasurableEquiv_measurePreserving n
  have he_symm : MeasurePreserving e.symm := he.symm e
  have hprod : Integrable (fun q : ℝ × EuclideanSpace ℝ (Fin n) => f (e.symm q)) := by
    exact he_symm.integrable_comp_of_integrable hf
  calc
    ∫ p, f p = ∫ p, (fun q => f (e.symm q)) (e p) := by simp
    _ = ∫ q, f (e.symm q) := by
      simpa only using (he.integral_comp' (fun q => f (e.symm q)))
    _ = ∫ t : ℝ, ∫ x : EuclideanSpace ℝ (Fin n), f (e.symm (t, x)) :=
      integral_prod _ hprod
    _ = ∫ t : ℝ, ∫ x : EuclideanSpace ℝ (Fin n), f (toSpaceTime t x) := by simp [e]

/-- At fixed time, the canonical embedding of space into space-time is measurable. -/
theorem measurable_toSpaceTime (n : ℕ) (t : ℝ) :
    Measurable (toSpaceTime t : EuclideanSpace ℝ (Fin n) → SpaceTime n) := by
  have hpair : Measurable (fun x : EuclideanSpace ℝ (Fin n) ↦ (t, x)) :=
    Measurable.prodMk measurable_const measurable_id
  rw [show (toSpaceTime t : EuclideanSpace ℝ (Fin n) → SpaceTime n) =
      fun x ↦ (spaceTimeMeasurableEquiv n).symm (t, x) by
    funext x
    simp]
  exact (spaceTimeMeasurableEquiv n).symm.measurable.comp hpair

/-- A measurable space-time set has a measurable spatial slice at every fixed time. -/
theorem measurableSet_spaceTimeSlice {n : ℕ} {s : Set (SpaceTime n)}
    (hs : MeasurableSet s) (t : ℝ) :
    MeasurableSet {x : EuclideanSpace ℝ (Fin n) | toSpaceTime t x ∈ s} :=
  hs.preimage (measurable_toSpaceTime n t)

/-- Fubini's theorem for a restricted space-time integral, expressed through
the spatial slice of the integration set at each time. -/
theorem setIntegral_toSpaceTime {n : ℕ} {s : Set (SpaceTime n)}
    (hs : MeasurableSet s) {f : SpaceTime n → ℝ} (hf : IntegrableOn f s) :
    ∫ p in s, f p =
      ∫ t : ℝ, ∫ x in {x : EuclideanSpace ℝ (Fin n) | toSpaceTime t x ∈ s},
        f (toSpaceTime t x) := by
  have hFubini := integral_toSpaceTime (n := n) (f := s.indicator f)
    (hf.integrable_indicator hs)
  rw [← integral_indicator hs]
  rw [hFubini]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [← integral_indicator (measurableSet_spaceTimeSlice hs t)]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : toSpaceTime t x ∈ s
  · simp [hx]
  · simp [hx]

end EvansLib

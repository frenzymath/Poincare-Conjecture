import MorganTianLib.Ch03.RicciFlow.EvolvingEpsilonNeck

/-!
# Morgan--Tian Ch. 3 - consequences for evolving epsilon-necks

This module records elementary consequences of the source-faithful
`EvolvingEpsilonNeck` contract.  The results expose the affine actual-time
interval, its central slice, and the positive shrinking-cylinder parameter
without adding hypotheses to the definition itself.
-/

open Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

/-! ## The backward rescaled-time interval -/

/-- **Math.** The backward rescaled-time interval is nonempty exactly when
the prescribed backward depth is positive. -/
theorem evolvingEpsilonNeckTimeSet_nonempty_iff {tau : ℝ} :
    (evolvingEpsilonNeckTimeSet tau).Nonempty ↔ 0 < tau := by
  constructor
  · rintro ⟨s, hs⟩
    linarith [hs.1, hs.2]
  · intro htau
    exact ⟨0, by constructor <;> linarith⟩

/-- **Math.** The distinguished zero-time point has rescaled coordinate zero. -/
@[simp] theorem evolvingEpsilonNeckZeroTime_value {tau : ℝ}
    (htau : 0 < tau) :
    (evolvingEpsilonNeckZeroTime htau : ℝ) = 0 := by
  rfl

/-- **Math.** The affine actual-time map sends the distinguished zero-time
point to the central time, for every scale. -/
@[simp] theorem evolvingEpsilonNeckActualTime_zeroTime
    {t0 R tau : ℝ} (htau : 0 < tau) :
    evolvingEpsilonNeckActualTime t0 R
        (evolvingEpsilonNeckZeroTime htau : ℝ) = t0 := by
  rw [evolvingEpsilonNeckZeroTime_value htau]
  exact evolvingEpsilonNeckActualTime_zero t0 R

/-- **Math.** Multiplying the actual-time displacement by the scalar-curvature
scale recovers the rescaled time parameter. -/
theorem evolvingEpsilonNeckActualTime_rescaled_sub
    {t0 R s : ℝ} (hR : R ≠ 0) :
    R * (evolvingEpsilonNeckActualTime t0 R s - t0) = s := by
  dsimp [evolvingEpsilonNeckActualTime]
  field_simp [hR]
  ring

/-- **Math.** For a positive scale, every backward rescaled time has actual
time in the corresponding half-open affine interval. -/
theorem evolvingEpsilonNeckActualTime_mem_Ioc
    {tau t0 R : ℝ} (hR : 0 < R) {s : ℝ}
    (hs : s ∈ evolvingEpsilonNeckTimeSet tau) :
    evolvingEpsilonNeckActualTime t0 R s ∈
      Ioc (t0 - R⁻¹ * tau) t0 := by
  rcases hs with ⟨hslo, hshi⟩
  constructor
  · dsimp [evolvingEpsilonNeckActualTime]
    have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
    have hmul := mul_lt_mul_of_pos_left hslo hRinv
    nlinarith
  · dsimp [evolvingEpsilonNeckActualTime]
    have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
    have hmul := mul_nonpos_of_nonneg_of_nonpos hRinv.le hshi
    nlinarith

/-- **Math.** For a positive scale, the actual-time map carries the complete
backward rescaled interval onto its affine actual-time interval. -/
theorem evolvingEpsilonNeckActualTime_image_timeSet
    {tau t0 R : ℝ} (hR : 0 < R) :
    evolvingEpsilonNeckActualTime t0 R ''
        evolvingEpsilonNeckTimeSet tau =
      Ioc (t0 - R⁻¹ * tau) t0 := by
  ext y
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact evolvingEpsilonNeckActualTime_mem_Ioc hR hs
  · intro hy
    have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
    have hlow : -R⁻¹ * tau < y - t0 := by
      linarith [hy.1]
    have hhigh : y - t0 ≤ 0 := by
      linarith [hy.2]
    let s : ℝ := (y - t0) / R⁻¹
    have hslo : -tau < s := by
      dsimp [s]
      apply (lt_div_iff₀ hRinv).2
      simpa [mul_comm] using hlow
    have hshi : s ≤ 0 := by
      dsimp [s]
      exact div_nonpos_of_nonpos_of_nonneg hhigh hRinv.le
    refine ⟨s, ⟨hslo, hshi⟩, ?_⟩
    dsimp [s, evolvingEpsilonNeckActualTime]
    field_simp [hR.ne']
    ring

/-- **Math.** The positive-scale actual-time map is strictly increasing in
rescaled time. -/
theorem evolvingEpsilonNeckActualTime_strictMono
    {t0 R : ℝ} (hR : 0 < R) :
    StrictMono (evolvingEpsilonNeckActualTime t0 R) := by
  intro s u hsu
  dsimp [evolvingEpsilonNeckActualTime]
  have hRinv : 0 < R⁻¹ := inv_pos.mpr hR
  have hmul := mul_lt_mul_of_pos_left hsu hRinv
  linarith

/-! ## Consequences for a stored evolving neck -/

section Neck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

variable {epsilon : ℝ} {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
  {x : M} {t0 : J} {tau : ℝ}

/-- **Math.** Every actual time stored by an evolving neck belongs both to its
ambient time domain and to the affine interval determined by the central
scalar-curvature scale. -/
theorem EvolvingEpsilonNeck.actualTime_mem_domain
    (N : EvolvingEpsilonNeck epsilon g J x t0 tau)
    (s : evolvingEpsilonNeckTimeSet tau) :
    evolvingEpsilonNeckActualTime t0.1
        (canonicalScalarCurvature (g t0.1) x) s.1 ∈
      J ∩ Ioc
        (t0.1 - (canonicalScalarCurvature (g t0.1) x)⁻¹ * tau) t0.1 := by
  refine ⟨N.time_available s, ?_⟩
  exact evolvingEpsilonNeckActualTime_mem_Ioc
    N.scalar_curvature_pos s.property

/-- **Math.** The central-time subtype of an evolving neck is the original
central-time subtype, not merely an equal real number. -/
theorem EvolvingEpsilonNeck.centralTime_eq_t0
    (N : EvolvingEpsilonNeck epsilon g J x t0 tau) :
    N.centralTime = t0 := by
  apply Subtype.ext
  exact N.centralTime_value

end Neck

/-! ## The standard shrinking-cylinder parameter -/

/-- **Math.** On the backward rescaled-time interval, the spherical scale
`1 - s` is positive. -/
theorem standardShrinkingCylinder_scale_pos_of_mem {tau : ℝ}
    (s : evolvingEpsilonNeckTimeSet tau) :
    0 < 1 - s.1 := by
  linarith [s.2.2]

/-- **Math.** On the backward rescaled-time interval, the spherical scale
`1 - s` is at least its central value one. -/
theorem standardShrinkingCylinder_scale_ge_one_of_mem {tau : ℝ}
    (s : evolvingEpsilonNeckTimeSet tau) :
    1 ≤ 1 - s.1 := by
  linarith [s.2.2]

/-- **Math.** The standard shrinking-cylinder scalar-curvature parameter
`(1 - s)⁻¹` is positive throughout the backward interval. -/
theorem standardShrinkingCylinder_scalarCurvature_pos_of_mem {tau : ℝ}
    (s : evolvingEpsilonNeckTimeSet tau) :
    0 < (1 - s.1)⁻¹ := by
  exact inv_pos.mpr (standardShrinkingCylinder_scale_pos_of_mem s)

/-- **Math.** At rescaled time zero, the standard shrinking-cylinder inner
product is the round product inner product. -/
theorem standardShrinkingCylinderInner_zero
    {epsilon tau : ℝ} (htau : 0 < tau)
    (p : epsilonNeckDomain epsilon)
    (v w : TangentSpace EpsilonNeckCylinderModel p) :
    standardShrinkingCylinderInner
        (evolvingEpsilonNeckZeroTime htau : ℝ) p v w =
      roundSphereMetric.metricInner p.1.1
          (EuclideanSpace.finAddEquivProd v).1
          (EuclideanSpace.finAddEquivProd w).1 +
        inner ℝ (EuclideanSpace.finAddEquivProd v).2
          (EuclideanSpace.finAddEquivProd w).2 := by
  rw [evolvingEpsilonNeckZeroTime_value htau]
  simp [standardShrinkingCylinderInner]

/-- **Math.** Any standard shrinking-cylinder family has the round product
inner product on its central rescaled-time slice. -/
theorem standardShrinkingCylinderFamily_metricInner_zero
    {epsilon tau : ℝ}
    {h : evolvingEpsilonNeckTimeSet tau →
      RiemannianMetric EpsilonNeckCylinderModel
        (epsilonNeckDomain epsilon)}
    (hh : IsStandardShrinkingCylinderFamily epsilon tau h)
    (htau : 0 < tau)
    (p : epsilonNeckDomain epsilon)
    (v w : TangentSpace EpsilonNeckCylinderModel p) :
    (h (evolvingEpsilonNeckZeroTime htau)).metricInner p v w =
      roundSphereMetric.metricInner p.1.1
          (EuclideanSpace.finAddEquivProd v).1
          (EuclideanSpace.finAddEquivProd w).1 +
        inner ℝ (EuclideanSpace.finAddEquivProd v).2
          (EuclideanSpace.finAddEquivProd w).2 := by
  have hzero := hh (evolvingEpsilonNeckZeroTime htau) p v w
  rw [evolvingEpsilonNeckZeroTime_value htau] at hzero
  simpa using hzero

end MorganTianLib

end

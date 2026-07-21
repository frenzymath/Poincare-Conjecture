import PetersenLib.Ch05.DistanceEDistBridge
import PetersenLib.Ch05.PiecewiseArclength

/-!
# Petersen Ch. 5, §5.3 — Example 5.3.3: straight segments in Euclidean space

**Example 5.3.3.** In `ℝⁿ`, the constant-speed straight curve `t ↦ p + t • v`
(with `v` a unit vector) is a **segment** in the sense of
`PetersenLib.IsSegment`: its length realizes the Riemannian distance between its
endpoints, and it is parametrized proportionally to arc length.

The key intermediate fact, of independent interest, is the exact computation of
the Petersen Riemannian distance on `(ℝⁿ, g_{ℝⁿ})`:
`riemannianDistance (euclideanMetric n) x y = ‖x − y‖`.  The upper bound is the
explicit straight segment; the lower bound `‖x − y‖ ≤ d(x, y)` comes from the
`≤`-half of the distance bridge `riemannianEDist_le_ofReal_riemannianDistance`
combined with the mathlib fact `edist = riemannianEDist` on an inner product
space (`IsRiemannianManifold 𝓘(ℝ, F) F`), whose fibre norm is exactly the
ambient norm carried by `euclideanMetric`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

section Euclidean

variable (n : ℕ) [NeZero n]

/-- The ambient finite-dimensionality nondegeneracy needed by the Ch. 5 metric
API: `dim ℝⁿ = n ≠ 0`. -/
instance : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]; infer_instance

/-- **Eng.** The intrinsic squared speed of the affine straight curve
`t ↦ p + t • v` in `(ℝⁿ, g_{ℝⁿ})` is the constant `‖v‖²`: its velocity is the
constant vector `v`, and the Euclidean metric reads off `⟪v, v⟫ = ‖v‖²`. -/
theorem curveSpeedSq_euclidean_straight (p v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    curveSpeedSq (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (euclideanMetric n)
        (fun s => p + s • v) t = ‖v‖ ^ 2 := by
  have hderiv : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  have hmd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (fun s => p + s • v) t :=
    mdifferentiableAt_iff_differentiableAt.mpr hderiv.differentiableAt
  rw [curveSpeedSq_eq_metricInner_velocity (euclideanMetric n) hmd,
    euclideanMetric_apply, velocity_eq_deriv, hderiv.deriv,
    real_inner_self_eq_norm_sq]

/-- **Eng.** The Petersen length of the affine straight curve `t ↦ p + t • v` on
`[a, c]` is `‖v‖ · (c − a)`: constant speed `‖v‖` integrated over the interval. -/
theorem curveLength_euclidean_straight (p v : EuclideanSpace ℝ (Fin n)) (a c : ℝ) :
    curveLength (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (euclideanMetric n)
        (fun s => p + s • v) a c = ‖v‖ * (c - a) := by
  rw [curveLength_def]
  have hcongr : ∀ s ∈ Set.uIcc a c,
      Real.sqrt (curveSpeedSq (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (euclideanMetric n)
        (fun s => p + s • v) s) = ‖v‖ := by
    intro s _
    rw [curveSpeedSq_euclidean_straight, Real.sqrt_sq (norm_nonneg _)]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const,
    smul_eq_mul, mul_comm]

/-- **Eng.** The affine straight curve `t ↦ p + t • v` is piecewise `C^∞` on any
`[a, b]` with `a ≤ b`: it is globally smooth, so the trivial one-piece partition
works. -/
theorem isPiecewiseSmoothCurve_euclidean_straight (p v : EuclideanSpace ℝ (Fin n))
    {a b : ℝ} (hab : a ≤ b) :
    IsPiecewiseSmoothCurve (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (fun s => p + s • v) a b := by
  have hsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞
      (fun s => p + s • v) :=
    contMDiff_iff_contDiff.mpr
      (contDiff_const.add ((contDiff_id).smul contDiff_const))
  have hmono : Monotone (![a, b] : Fin 2 → ℝ) :=
    Fin.monotone_iff_le_succ.mpr (fun i => by fin_cases i; simpa using hab)
  have := isPiecewiseSmoothCurve_of_forall_contMDiffOn
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (γ := fun s => p + s • v)
    (u := ![a, b]) hmono (fun i => by fin_cases i <;> exact hsmooth.contMDiffOn)
  simpa using this

/-- **Math.** **The Euclidean Riemannian distance is the norm distance**
(`ex:pet-ch5-euclidean-segments`, distance computation): on `(ℝⁿ, g_{ℝⁿ})`,
`riemannianDistance (euclideanMetric n) x y = ‖x − y‖`.  The `≤` bound uses the
explicit straight segment from `x` to `y`; the `≥` bound uses the `≤`-half of the
distance bridge together with `edist = riemannianEDist` on the inner product
space. -/
theorem riemannianDistance_euclideanMetric (x y : EuclideanSpace ℝ (Fin n)) :
    riemannianDistance (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (euclideanMetric n) x y
      = ‖x - y‖ := by
  refine le_antisymm ?_ ?_
  · -- upper bound: the straight segment from `x` to `y` on `[0, 1]`
    have hpsc := isPiecewiseSmoothCurve_euclidean_straight n x (y - x) (zero_le_one)
    have hlen := curveLength_euclidean_straight n x (y - x) 0 1
    have h0 : x + (0 : ℝ) • (y - x) = x := by simp
    have h1 : x + (1 : ℝ) • (y - x) = y := by simp
    have hle := riemannianDistance_le_curveLength (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (euclideanMetric n) hpsc h0 h1
    rw [hlen] at hle
    rw [norm_sub_rev x y]
    simpa using hle
  · -- lower bound via the distance bridge and `edist = riemannianEDist`
    have h1 : edist x y = Manifold.riemannianEDist 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x y :=
      IsRiemannianManifold.out x y
    have h2 := riemannianEDist_le_ofReal_riemannianDistance (euclideanMetric n) x y
    have hbound : edist x y
        ≤ ENNReal.ofReal (riemannianDistance (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
            (euclideanMetric n) x y) := h1.trans_le h2
    rw [edist_dist, dist_eq_norm] at hbound
    exact (ENNReal.ofReal_le_ofReal_iff
      (riemannianDistance_nonneg (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (euclideanMetric n) x y)).mp hbound

/-- **Math.** **Example 5.3.3** (Petersen §5.3, `ex:pet-ch5-euclidean-segments`).
In `(ℝⁿ, g_{ℝⁿ})`, the constant-speed straight curve `t ↦ p + t • v` for a
**unit** vector `v` is a **segment** (`PetersenLib.IsSegment`) on every interval
`[a, b]`: its length realizes the Riemannian distance between its endpoints and
it is parametrized proportionally to arc length (here by arc length itself, since
`‖v‖ = 1`).  This is the model case of Petersen's `lem:pet-ch5-distance-function-segments`
for the linear distance function `r(x) = ⟪v, x⟫`. -/
theorem euclideanSegmentsAreStraightLines (p v : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ = 1) {a b : ℝ} (hab : a ≤ b) :
    IsSegment (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (euclideanMetric n)
      (fun t => p + t • v) a b := by
  refine ⟨isPiecewiseSmoothCurve_euclidean_straight n p v hab, ?_, ?_⟩
  · -- length equals distance between the endpoints
    rw [curveLength_euclidean_straight, riemannianDistance_euclideanMetric]
    have hsub : (p + a • v) - (p + b • v) = (a - b) • v := by
      rw [sub_smul]; abel
    rw [hv, one_mul, hsub, norm_smul, hv, mul_one, Real.norm_eq_abs, abs_sub_comm,
      abs_of_nonneg (show (0 : ℝ) ≤ b - a by linarith)]
  · -- proportional-to-arc-length parametrization, with `k = ‖v‖ = 1`
    refine ⟨‖v‖, norm_nonneg _, fun t _ => ?_⟩
    rw [curveLength_euclidean_straight]

end Euclidean

end PetersenLib

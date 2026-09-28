import MorganTianLib.Ch04.PositiveRicciPinching
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open Filter
open scoped Topology

/-!
# Trace-free Ricci gap bounds

The Hamilton pinching quotient controls the scalar-free part of Ricci.  This
file records the elementary pointwise consequence needed when that quotient is
combined with a diverging scalar scale: every Ricci eigenvalue, and hence every
three-dimensional sectional-curvature eigenvalue, is close to its normalized
average.
-/

noncomputable section

namespace MorganTianLib

/-- **Math.** Each squared eigenvalue deviation from the scalar average is bounded by the
trace-free Ricci norm. -/
theorem ricciEigen_deviation_sq_le_traceFreeRicciEigenNormSq
    (a b c : ℝ) :
    (a - ricciEigenScalar a b c / 3) ^ 2 ≤
      traceFreeRicciEigenNormSq a b c := by
  unfold traceFreeRicciEigenNormSq ricciEigenNormSq ricciEigenScalar
  nlinarith [sq_nonneg (b - c), sq_nonneg (a - b), sq_nonneg (a - c)]

/-- **Math.** The corresponding bound for the first sectional-curvature eigenvalue
`(b+c-a)/2`, after normalization by a positive scalar curvature. -/
theorem normalizedSectionalEigen_deviation_sq_le
    {a b c : ℝ} (hR : 0 < ricciEigenScalar a b c) :
    (((b + c - a) / 2) / ricciEigenScalar a b c - 1 / 6) ^ 2 ≤
      traceFreeRicciEigenNormSq a b c /
        ricciEigenScalar a b c ^ 2 := by
  have hdev := ricciEigen_deviation_sq_le_traceFreeRicciEigenNormSq a b c
  have hsq : 0 < ricciEigenScalar a b c ^ 2 := sq_pos_of_pos hR
  have hscaled := (div_le_div_of_nonneg_right hdev (le_of_lt hsq))
  have hid : (((b + c - a) / 2) / ricciEigenScalar a b c - 1 / 6) ^ 2 =
      (a - ricciEigenScalar a b c / 3) ^ 2 /
        ricciEigenScalar a b c ^ 2 := by
    field_simp [ricciEigenScalar, hR.ne']
    unfold ricciEigenScalar
    ring
  rw [hid]
  exact hscaled

/-- **Math.** If the trace-free norm is bounded by `C R^(2-epsilon)`, the normalized
sectional deviation is bounded by `C / R^epsilon`. -/
theorem normalizedSectionalEigen_deviation_sq_le_of_weighted_bound
    {a b c R C epsilon : ℝ} (hR : 0 < R)
    (hscalar : ricciEigenScalar a b c = R)
    (hbound : traceFreeRicciEigenNormSq a b c ≤ C * R ^ (2 - epsilon)) :
    (((b + c - a) / 2) / R - 1 / 6) ^ 2 ≤ C / R ^ epsilon := by
  have hbase := normalizedSectionalEigen_deviation_sq_le (a := a) (b := b) (c := c)
    (hR := hscalar ▸ hR)
  rw [hscalar] at hbase
  have hdiv := div_le_div_of_nonneg_right hbound (by positivity : 0 ≤ R ^ 2)
  calc
    (((b + c - a) / 2) / R - 1 / 6) ^ 2 ≤
        traceFreeRicciEigenNormSq a b c / R ^ 2 := hbase
    _ ≤ C * R ^ (2 - epsilon) / R ^ 2 := hdiv
    _ = C / R ^ epsilon := by
      rw [Real.rpow_sub hR 2 epsilon, Real.rpow_two]
      field_simp

/-- **Math.** Weighted trace-free pinching and scalar blow-up force each
sectional eigenvalue, divided by scalar curvature, to tend to `1/6`.
The pinching and blow-up are assumptions here; their geometric PDE producers
are separate obligations. -/
theorem tendsto_normalizedSectionalEigen_of_weighted_bound
    {α : Type*} {F : Filter α} {a b c R : α → ℝ} {C epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hR : Tendsto R F atTop)
    (hscalar : ∀ᶠ t in F, ricciEigenScalar (a t) (b t) (c t) = R t)
    (hbound : ∀ᶠ t in F, traceFreeRicciEigenNormSq (a t) (b t) (c t) ≤
      C * R t ^ (2 - epsilon)) :
    Tendsto (fun t => ((b t + c t - a t) / 2) / R t) F (𝓝 (1 / 6)) := by
  have hpos : ∀ᶠ t in F, 0 < R t := hR.eventually (eventually_gt_atTop 0)
  have hpow : Tendsto (fun t => C / R t ^ epsilon) F (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop hepsilon).comp hR).const_mul C
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [hpos] with t ht
    simp only [Function.comp_apply, Real.rpow_neg ht.le, div_eq_mul_inv]
  have hsq : Tendsto (fun t => (((b t + c t - a t) / 2) / R t - 1 / 6) ^ 2)
      F (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun t => sq_nonneg _) _ hpow
    filter_upwards [hpos, hscalar, hbound] with t ht hst hbt
    exact normalizedSectionalEigen_deviation_sq_le_of_weighted_bound ht hst hbt
  have habs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simp only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero] at habs
  exact tendsto_iff_dist_tendsto_zero.mpr (by simpa only [Real.dist_eq] using habs)

end MorganTianLib

#print axioms MorganTianLib.ricciEigen_deviation_sq_le_traceFreeRicciEigenNormSq
#print axioms MorganTianLib.normalizedSectionalEigen_deviation_sq_le
#print axioms MorganTianLib.normalizedSectionalEigen_deviation_sq_le_of_weighted_bound
#print axioms MorganTianLib.tendsto_normalizedSectionalEigen_of_weighted_bound

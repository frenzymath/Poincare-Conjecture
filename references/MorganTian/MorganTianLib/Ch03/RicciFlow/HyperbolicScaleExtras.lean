import MorganTianLib.Ch03.RicciFlow.HyperbolicExample
import MorganTianLib.Ch03.RicciFlow.ExactSolutionConsequences

/-!
# Canonical nonnegative-time hyperbolic Ricci flow

`HyperbolicExample` proves the Einstein contraction and the exact scaled
Ricci-flow equation once positivity of the affine scale is supplied.  The
source example uses the canonical expanding half-line.  This file supplies
that positivity producer and specializes the equation to `Ici 0`.
-/

open Filter Set
open scoped ContMDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

open Riemannian.Hyperbolic

variable {n : ℕ} [NeZero n]

noncomputable instance hyperbolicUpperHalfSpacePreconnected (e : Fin n) :
    PreconnectedSpace ↥(upperHalfSpace e) :=
  Subtype.preconnectedSpace <| by
    simpa [upperHalfSpace] using
      (convex_halfSpace_gt
        (EuclideanSpace.proj (𝕜 := ℝ) e).isLinear (0 : ℝ)).isPreconnected

private theorem hyperbolicEinsteinScale_pos_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    0 < einsteinScale
      (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t := by
  have hn : (1 : ℝ) ≤
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) := by
    have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
    simpa using (show (1 : ℝ) ≤ n by
      exact_mod_cast (Nat.succ_le_iff.mpr hn0))
  have hprod : 0 ≤
      ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * t :=
    mul_nonneg (sub_nonneg.mpr hn) ht
  unfold einsteinScale
  nlinarith

omit [NeZero n] in
private theorem hyperbolicEinsteinScale_tendsto_atTop_aux
    (hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    Tendsto
      (einsteinScale
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)))
      atTop atTop := by
  have hdim' : (1 : ℝ) <
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) := by
    exact_mod_cast hdim
  have hc : 0 < 2 *
      ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) := by
    positivity
  have hmul : Tendsto
      (fun t : ℝ => 2 *
        ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * t)
      atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
  have hadd : Tendsto
      (fun t : ℝ => 1 + 2 *
        ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * t)
      atTop atTop := by
    apply Filter.tendsto_atTop_mono' atTop
      (show (fun t : ℝ => 2 *
          ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * t)
        ≤ᶠ[atTop] (fun t : ℝ => 1 + 2 *
          ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * t) from
        Filter.Eventually.of_forall (fun t => by linarith)) hmul
  convert hadd using 1
  ext t
  simp [einsteinScale]
  ring

omit [NeZero n] in
/-- **Math.** For dimension at least two, the expanding hyperbolic Einstein
scale diverges along the canonical nonnegative-time half-line. -/
theorem hyperbolicEinsteinScale_tendsto_atTop
    (hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :
    Tendsto
      (einsteinScale
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)))
      atTop atTop :=
  hyperbolicEinsteinScale_tendsto_atTop_aux hdim

/-- **Math.** Distinct points in the canonical expanding hyperbolic flow
separate to infinite distance as time tends to infinity. -/
theorem hyperbolicMetric_canonicalDist_tendsto_atTop
    (e : Fin n)
    (hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (p q : ↥(upperHalfSpace e)) (hpq : p ≠ q) :
    Tendsto
      (fun t : ℝ =>
        @dist _
          (canonicalMetricSpace
            (einsteinMetricFamilyOn (hyperbolicMetric e) (Ici 0)
              (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1))
              (by
                intro s hs
                exact hyperbolicEinsteinScale_pos_of_nonneg hs) t)
            ).toPseudoMetricSpace.toDist p q)
      atTop atTop := by
  let hpos : ∀ t ∈ Ici (0 : ℝ),
      0 < einsteinScale
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t := by
    intro t ht
    exact hyperbolicEinsteinScale_pos_of_nonneg ht
  have hsqrt : Tendsto
      (fun t : ℝ => Real.sqrt (einsteinScale
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t))
      atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (hyperbolicEinsteinScale_tendsto_atTop_aux hdim)
  let d₀ : ℝ := @dist _
    (canonicalMetricSpace (hyperbolicMetric e)).toPseudoMetricSpace.toDist p q
  have hd₀ : 0 < d₀ := by
    dsimp [d₀]
    exact (@dist_pos _ (canonicalMetricSpace (hyperbolicMetric e))).mpr hpq
  have hmul : Tendsto (fun t : ℝ =>
      Real.sqrt (einsteinScale
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t) * d₀)
      atTop atTop := hsqrt.atTop_mul_const hd₀
  apply hmul.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simpa [d₀] using (einsteinMetricFamilyOn_canonicalDist
    (hyperbolicMetric e) (Ici 0)
    (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) hpos ht p q).symm

/-- **Math.** Every fixed sectional-curvature component of the canonical
expanding hyperbolic flow tends to zero as time tends to infinity. -/
theorem hyperbolicMetric_sectionalCurvature_tendsto_zero
    (e : Fin n)
    (hdim : 1 < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))
    (p : ↥(upperHalfSpace e)) (v w : TangentSpace
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) :
    Tendsto
      (fun t : ℝ => sectionalCurvatureAt
        (einsteinMetricFamilyOn (hyperbolicMetric e) (Ici 0)
          (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1))
          (by
            intro s hs
            exact hyperbolicEinsteinScale_pos_of_nonneg hs) t)
        (einsteinMetricFamilyOn (hyperbolicMetric e) (Ici 0)
          (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1))
          (by
            intro s hs
            exact hyperbolicEinsteinScale_pos_of_nonneg hs) t).leviCivitaConnection
        p v w)
      atTop (𝓝 0) := by
  let hpos : ∀ t ∈ Ici (0 : ℝ),
      0 < einsteinScale
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t := by
    intro t ht
    exact hyperbolicEinsteinScale_pos_of_nonneg ht
  have hcurv : Tendsto (fun t : ℝ =>
      sectionalCurvatureAt (hyperbolicMetric e)
        (hyperbolicMetric e).leviCivitaConnection p v w /
        einsteinScale
          (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t)
      atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (hyperbolicEinsteinScale_tendsto_atTop_aux hdim)
  apply hcurv.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  simpa using (einsteinMetricFamilyOn_sectionalCurvatureAt
    (hyperbolicMetric e) (Ici 0)
    (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) hpos ht p v w).symm

end MorganTianLib

end

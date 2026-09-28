import MorganTianLib.Ch03.RicciFlow.EvolvingTransportRegularity

/-!
# Morgan--Tian Ch. 3 -- metric pairing for operator-valued transport

The compact-interval transport is assembled as a curve of continuous linear
maps.  This module applies the evolving metric derivative to that operator
curve, exposing the cancellation which makes transported pairings constant.
-/

open Set
open scoped NNReal

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-- **Math.** The pairing of two vectors transported by the operator-valued
ODE has zero derivative on the compact time interval. -/
theorem evolvingTransportCurveOn_pairing_hasDerivWithinAt_zero
    {J : Set ℝ} (G : EvolvingMetricData V J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hdualLeft : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t (A t v) w = G.ricci t v w)
    (hdualRight : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t v (A t w) = G.ricci t v w)
    (v w : V) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt
      (fun s => G.metric s
        (evolvingTransportCurveOn A hab hcont hK s v)
        (evolvingTransportCurveOn A hab hcont hK s w))
      0 (Icc a b) t := by
  let u : ℝ → V := fun s => evolvingTransportCurveOn A hab hcont hK s v
  let z : ℝ → V := fun s => evolvingTransportCurveOn A hab hcont hK s w
  have hmetric : HasDerivWithinAt G.metric
      (-2 • G.ricci t) (Icc a b) t :=
    @HasDerivAt.hasDerivWithinAt ℝ _ (V →L[ℝ] V →L[ℝ] ℝ) _ _
      G.metric (-2 • G.ricci t) t (Icc a b) (G.metric_deriv t)
  have hu : HasDerivWithinAt u ((A t) (u t)) (Icc a b) t := by
    simpa [u] using (evolvingTransportCurveOn_hasDerivWithinAt
      A hab hcont hK ht).clm_apply (hasDerivWithinAt_const t (Icc a b) v)
  have hz : HasDerivWithinAt z ((A t) (z t)) (Icc a b) t := by
    simpa [z] using (evolvingTransportCurveOn_hasDerivWithinAt
      A hab hcont hK ht).clm_apply (hasDerivWithinAt_const t (Icc a b) w)
  have h₁ : HasDerivWithinAt
      (fun s => G.metric s (u s))
      ((-2 • G.ricci t) (u t) + G.metric t ((A t) (u t)))
      (Icc a b) t :=
    @HasDerivWithinAt.clm_apply ℝ _ V _ _ t (Icc a b) (V →L[ℝ] ℝ) _ _
      G.metric (-2 • G.ricci t) u
      ((A t) (u t)) hmetric hu
  have h₂ : HasDerivWithinAt
      (fun s => G.metric s (u s) (z s))
      (((-2 • G.ricci t) (u t) + G.metric t ((A t) (u t))) (z t) +
        G.metric t (u t) ((A t) (z t)))
      (Icc a b) t :=
    @HasDerivWithinAt.clm_apply ℝ _ V _ _ t (Icc a b) ℝ _ _
      (fun s => G.metric s (u s))
      (((-2 • G.ricci t) (u t) + G.metric t ((A t) (u t)))) z
      ((A t) (z t)) h₁ hz
  apply h₂.congr_deriv
  simp only [smul_apply, add_apply]
  rw [hdualLeft t ht, hdualRight t ht]
  ring

/-- **Math.** Operator-valued transport preserves the metric pairing with the
left endpoint throughout a nondegenerate compact interval. -/
theorem evolvingTransportCurveOn_pairing_eq_left
    {J : Set ℝ} (G : EvolvingMetricData V J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hdualLeft : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t (A t v) w = G.ricci t v w)
    (hdualRight : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t v (A t w) = G.ricci t v w)
    (v w : V) {t : ℝ} (ht : t ∈ Icc a b) :
    G.metric t
        (evolvingTransportCurveOn A hab.le hcont hK t v)
        (evolvingTransportCurveOn A hab.le hcont hK t w) =
      G.metric a v w := by
  let f : ℝ → ℝ := fun s => G.metric s
    (evolvingTransportCurveOn A hab.le hcont hK s v)
    (evolvingTransportCurveOn A hab.le hcont hK s w)
  have hdiff : DifferentiableOn ℝ f (Icc a b) := by
    intro s hs
    exact (evolvingTransportCurveOn_pairing_hasDerivWithinAt_zero
      G A hab.le hcont hK hdualLeft hdualRight v w hs).differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a b, derivWithin f (Icc a b) s = 0 := by
    intro s hs
    exact (evolvingTransportCurveOn_pairing_hasDerivWithinAt_zero
      G A hab.le hcont hK hdualLeft hdualRight v w
        ⟨hs.1, hs.2.le⟩).derivWithin
      ((uniqueDiffOn_Icc hab) s ⟨hs.1, hs.2.le⟩)
  have hconst := constant_of_derivWithin_zero hdiff hderiv t ht
  change G.metric t
      (evolvingTransportCurveOn A hab.le hcont hK t v)
      (evolvingTransportCurveOn A hab.le hcont hK t w) =
    G.metric a
      (evolvingTransportCurveOn A hab.le hcont hK a v)
      (evolvingTransportCurveOn A hab.le hcont hK a w) at hconst
  rw [evolvingTransportCurveOn_apply_of_mem A hab.le hcont hK ht v,
    evolvingTransportCurveOn_apply_of_mem A hab.le hcont hK ht w] at hconst
  have hta : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  rw [evolvingTransportCurveOn_apply_of_mem A hab.le hcont hK hta v,
    evolvingTransportCurveOn_apply_of_mem A hab.le hcont hK hta w] at hconst
  rw [evolvingTransportCurveOn_apply_of_mem A hab.le hcont hK ht v,
    evolvingTransportCurveOn_apply_of_mem A hab.le hcont hK ht w]
  simpa [Riemannian.LinearODE.solOf_left hab.le hcont hK] using hconst

end MorganTianLib

end

#print axioms MorganTianLib.evolvingTransportCurveOn_pairing_hasDerivWithinAt_zero
#print axioms MorganTianLib.evolvingTransportCurveOn_pairing_eq_left

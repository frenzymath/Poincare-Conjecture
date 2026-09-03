import MorganTianLib.Ch03.RicciFlow.EvolvingTransportOn

/-!
# Morgan--Tian Ch. 3 -- metric preservation for compact-interval transport

The compact-interval linear ODE producer supplies a canonical transport from
the left endpoint.  This module connects that analytic construction to the
Ricci-dual frame equation: the transported pairing is constant, each time
slice is a linear equivalence, and an initially orthonormal family remains
orthonormal.  Smooth dependence on the base point and bundle globalization
remain separate geometric obligations.
-/

open Set
open scoped NNReal

noncomputable section

namespace MorganTianLib

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [CompleteSpace V] [FiniteDimensional ℝ V]

/-! ## Pairing preservation along the canonical ODE solutions -/

set_option maxHeartbeats 800000 in
/-- **Math.** Along two solutions of the Ricci-dual linear ODE, the evolving
metric pairing has zero derivative within the compact time interval. -/
theorem evolvingTransportCurve_pairing_hasDerivWithinAt_zero
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
        (Riemannian.LinearODE.solOf hab hcont hK v s)
        (Riemannian.LinearODE.solOf hab hcont hK w s))
      0 (Icc a b) t := by
  let u : ℝ → V := Riemannian.LinearODE.solOf hab hcont hK v
  let z : ℝ → V := Riemannian.LinearODE.solOf hab hcont hK w
  have hmetric : HasDerivWithinAt G.metric
      (-2 • G.ricci t) (Icc a b) t :=
    @HasDerivAt.hasDerivWithinAt ℝ _ (V →L[ℝ] V →L[ℝ] ℝ) _ _
      G.metric (-2 • G.ricci t) t (Icc a b) (G.metric_deriv t)
  have hu : HasDerivWithinAt u (A t (u t)) (Icc a b) t :=
    evolvingTransportOn_hasDerivWithinAt A hab hcont hK v ht
  have hz : HasDerivWithinAt z (A t (z t)) (Icc a b) t :=
    evolvingTransportOn_hasDerivWithinAt A hab hcont hK w ht
  have h₁ : HasDerivWithinAt
      (fun s => G.metric s (u s))
      ((-2 • G.ricci t) (u t) + G.metric t (A t (u t)))
      (Icc a b) t :=
    @HasDerivWithinAt.clm_apply ℝ _ V _ _ t (Icc a b) (V →L[ℝ] ℝ) _ _
      G.metric (-2 • G.ricci t) u
      (A t (u t)) hmetric hu
  have h₂ : HasDerivWithinAt
      (fun s => G.metric s (u s) (z s))
      (((-2 • G.ricci t) (u t) + G.metric t (A t (u t))) (z t) +
        G.metric t (u t) (A t (z t)))
      (Icc a b) t :=
    @HasDerivWithinAt.clm_apply ℝ _ V _ _ t (Icc a b) ℝ _ _
      (fun s => G.metric s (u s))
      ((-2 • G.ricci t) (u t) + G.metric t (A t (u t))) z
      (A t (z t)) h₁ hz
  apply h₂.congr_deriv
  simp only [smul_apply, add_apply]
  rw [hdualLeft t ht, hdualRight t ht]
  ring

/-- **Math.** The metric pairing of two canonical ODE solutions equals its
value at the left endpoint throughout a nondegenerate compact interval. -/
theorem evolvingTransportCurve_pairing_eq_left
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
        (Riemannian.LinearODE.solOf hab.le hcont hK v t)
        (Riemannian.LinearODE.solOf hab.le hcont hK w t) =
      G.metric a v w := by
  let f : ℝ → ℝ := fun s => G.metric s
    (Riemannian.LinearODE.solOf hab.le hcont hK v s)
    (Riemannian.LinearODE.solOf hab.le hcont hK w s)
  have hdiff : DifferentiableOn ℝ f (Icc a b) := by
    intro s hs
    exact (evolvingTransportCurve_pairing_hasDerivWithinAt_zero
      G A hab.le hcont hK hdualLeft hdualRight v w hs).differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a b, derivWithin f (Icc a b) s = 0 := by
    intro s hs
    exact (evolvingTransportCurve_pairing_hasDerivWithinAt_zero
      G A hab.le hcont hK hdualLeft hdualRight v w
        ⟨hs.1, hs.2.le⟩).derivWithin
      ((uniqueDiffOn_Icc hab) s ⟨hs.1, hs.2.le⟩)
  have hconst := constant_of_derivWithin_zero hdiff hderiv t ht
  simpa [f, Riemannian.LinearODE.solOf_left hab.le hcont hK] using hconst

/-- **Math.** The canonical compact-interval transport pulls the evolving
metric at time `t` back to the metric at the left endpoint. -/
theorem evolvingTransportOn_pullback_metric_eq_left
    {J : Set ℝ} (G : EvolvingMetricData V J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hdualLeft : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t (A t v) w = G.ricci t v w)
    (hdualRight : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t v (A t w) = G.ricci t v w)
    (t : Icc a b) (v w : V) :
    G.metric t
        (evolvingTransportOn A hab.le hcont hK t v)
        (evolvingTransportOn A hab.le hcont hK t w) =
      G.metric a v w := by
  exact evolvingTransportCurve_pairing_eq_left
    G A hab hcont hK hdualLeft hdualRight v w t.2

/-! ## Pointwise automorphisms and orthonormal frames -/

/-- **Math.** Each time slice of the canonical transport on a nondegenerate
compact interval is a continuous linear equivalence. -/
noncomputable def evolvingTransportEquivOn
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (t : Icc a b) : V ≃L[ℝ] V :=
  (LinearEquiv.ofBijective
    (evolvingTransportOn A hab.le hcont hK t).toLinearMap
    (evolvingTransportOn_bijective A hab hcont hK t.2)).toContinuousLinearEquiv

@[simp] theorem evolvingTransportEquivOn_apply
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (t : Icc a b) (v : V) :
    evolvingTransportEquivOn A hab hcont hK t v =
      evolvingTransportOn A hab.le hcont hK t v := rfl

/-- **Math.** The pointwise transport equivalence is an isometry for the
left-endpoint metric and the evolving metric at time `t`. -/
theorem evolvingTransportEquivOn_pullback_metric_eq_left
    {J : Set ℝ} (G : EvolvingMetricData V J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hdualLeft : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t (A t v) w = G.ricci t v w)
    (hdualRight : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t v (A t w) = G.ricci t v w)
    (t : Icc a b) (v w : V) :
    G.metric t
        (evolvingTransportEquivOn A hab hcont hK t v)
        (evolvingTransportEquivOn A hab hcont hK t w) =
      G.metric a v w := by
  simpa only [evolvingTransportEquivOn_apply] using
    evolvingTransportOn_pullback_metric_eq_left
      G A hab hcont hK hdualLeft hdualRight t v w

/-- **Math.** Applying the canonical transport to an orthonormal family at the
left endpoint produces an orthonormal family at every time in the interval. -/
theorem evolvingTransportOn_isOrthonormal_of_left
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {J : Set ℝ} (G : EvolvingMetricData V J)
    (A : ℝ → V →L[ℝ] V) {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn A (Icc a b))
    {K : ℝ≥0} (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K)
    (hdualLeft : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t (A t v) w = G.ricci t v w)
    (hdualRight : ∀ t ∈ Icc a b, ∀ v w,
      G.metric t v (A t w) = G.ricci t v w)
    (basis : ι → V)
    (hinit : ∀ i j, G.metric a (basis i) (basis j) =
      if i = j then 1 else 0)
    (t : Icc a b) :
    ∀ i j,
      G.metric t
          (evolvingTransportOn A hab.le hcont hK t (basis i))
          (evolvingTransportOn A hab.le hcont hK t (basis j)) =
        if i = j then 1 else 0 := by
  intro i j
  rw [evolvingTransportOn_pullback_metric_eq_left
    G A hab hcont hK hdualLeft hdualRight t]
  exact hinit i j

end MorganTianLib

end

#print axioms MorganTianLib.evolvingTransportCurve_pairing_eq_left
#print axioms MorganTianLib.evolvingTransportOn_pullback_metric_eq_left
#print axioms MorganTianLib.evolvingTransportEquivOn_pullback_metric_eq_left
#print axioms MorganTianLib.evolvingTransportOn_isOrthonormal_of_left

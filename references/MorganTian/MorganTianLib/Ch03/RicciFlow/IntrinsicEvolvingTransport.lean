import MorganTianLib.Ch03.RicciFlow.RicciFlowMetricDerivative
import MorganTianLib.Ch03.RicciFlow.ScalarEvolution
import MorganTianLib.Ch03.RicciFlow.EvolvingTransportRegularity

/-!
# Metric preservation by intrinsic Ricci transport

At a fixed point, the linear ODE `v' = Ric(v)` preserves the evolving
Ricci-flow metric pairing. The metric derivative and the two vector
derivatives cancel. Applying this identity to the canonical compact-interval
ODE construction produces the metric-preserving transport used by an evolving
orthonormal frame.
-/

open Set
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace NNReal

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Raising the first Ricci index recovers the Ricci tensor when
paired with the metric. -/
theorem metricInner_ricciEndomorphismAt (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    g.metricInner p (ricciEndomorphismAt g p v) w = ricciTensorAt g p v w := by
  exact inner_ricciEndomorphismAt g p v w

/-- **Math.** Raising the second Ricci index gives the same pairing by symmetry. -/
theorem metricInner_ricciEndomorphismAt_right (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    g.metricInner p v (ricciEndomorphismAt g p w) = ricciTensorAt g p v w := by
  rw [g.metricInner_comm, metricInner_ricciEndomorphismAt, ricciTensorAt_symm]

/-- **Math.** Along two intrinsic Ricci-dual vector curves, the actual
Ricci-flow metric pairing has zero derivative, including one-sided times. -/
theorem metricInner_hasDerivWithinAt_zero_of_ricciTransport
    {g : ℝ → RiemannianMetric I M} {J S : Set ℝ}
    (hflow : IsRicciFlowOn g J) (p : M) (hS : S ⊆ J)
    {u v : ℝ → E} {t : ℝ} (ht : t ∈ S)
    (hu : HasDerivWithinAt u (ricciEndomorphismAt (g t) p (u t)) S t)
    (hv : HasDerivWithinAt v (ricciEndomorphismAt (g t) p (v t)) S t) :
    HasDerivWithinAt (fun s => (g s).metricInner p (u s) (v s)) 0 S t := by
  have hg : HasDerivWithinAt (fun s => ((g s).inner p : E →L[ℝ] E →L[ℝ] ℝ))
      ((-2 : ℝ) • ricciContinuousBilinearAt (g t) p) S t := by
    apply @HasDerivWithinAt.mono ℝ _ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ t S J _ hS
    convert hflow.inner_hasDerivWithinAt (hS ht) p using 1
  have hpair := (hg.clm_apply (F := E) (G := E →L[ℝ] ℝ) hu).clm_apply
    (F := E) (G := ℝ) hv
  apply hpair.congr_deriv
  simp only [smul_apply, add_apply, ricciContinuousBilinearAt_apply]
  change -2 * ricciTensorAt (g t) p (u t) (v t) +
    (g t).metricInner p (ricciEndomorphismAt (g t) p (u t)) (v t) +
    (g t).metricInner p (u t) (ricciEndomorphismAt (g t) p (v t)) = 0
  rw [metricInner_ricciEndomorphismAt, metricInner_ricciEndomorphismAt_right]
  ring

/-- **Math.** Canonical transport built from the actual Ricci endomorphism
has zero evolving metric derivative on each controlled closed time slab. -/
theorem intrinsicEvolvingTransport_metricInner_hasDerivWithinAt_zero
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (p : M) {a b : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ J)
    (hcont : ContinuousOn (fun s => (ricciEndomorphismAt (g s) p : E →L[ℝ] E)) (Icc a b))
    {K : ℝ≥0} (hK : ∀ s ∈ Icc a b,
      @nnnorm (E →L[ℝ] E) _ (ricciEndomorphismAt (g s) p) ≤ K)
    (v w : E) {t : ℝ} (ht : t ∈ Icc a b) :
    HasDerivWithinAt
      (fun s => (g s).metricInner p
        (evolvingTransportCurveOn (V := E) (fun r => ricciEndomorphismAt (g r) p)
          hab hcont hK s v)
        (evolvingTransportCurveOn (V := E) (fun r => ricciEndomorphismAt (g r) p)
          hab hcont hK s w)) 0 (Icc a b) t := by
  apply metricInner_hasDerivWithinAt_zero_of_ricciTransport hflow p hJ ht
  · convert (evolvingTransportCurveOn_hasDerivWithinAt (V := E)
      (fun r => ricciEndomorphismAt (g r) p) hab hcont hK ht).clm_apply
        (F := E) (G := E) (hasDerivWithinAt_const t (Icc a b) v) using 1
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
    rfl
  · convert (evolvingTransportCurveOn_hasDerivWithinAt (V := E)
      (fun r => ricciEndomorphismAt (g r) p) hab hcont hK ht).clm_apply
        (F := E) (G := E) (hasDerivWithinAt_const t (Icc a b) w) using 1
    simp only [ContinuousLinearMap.comp_apply, map_zero, add_zero]
    rfl

/-- **Math.** The canonical Ricci-dual transport preserves the actual
evolving metric pairing with its value at the left endpoint. -/
theorem intrinsicEvolvingTransport_metricInner_eq_left
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (p : M) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ J)
    (hcont : ContinuousOn (fun s => (ricciEndomorphismAt (g s) p : E →L[ℝ] E)) (Icc a b))
    {K : ℝ≥0} (hK : ∀ s ∈ Icc a b,
      @nnnorm (E →L[ℝ] E) _ (ricciEndomorphismAt (g s) p) ≤ K)
    (v w : E) {t : ℝ} (ht : t ∈ Icc a b) :
    (g t).metricInner p
      (evolvingTransportCurveOn (V := E) (fun r => ricciEndomorphismAt (g r) p)
        hab.le hcont hK t v)
      (evolvingTransportCurveOn (V := E) (fun r => ricciEndomorphismAt (g r) p)
        hab.le hcont hK t w) = (g a).metricInner p v w := by
  let f : ℝ → ℝ := fun s => (g s).metricInner p
    (evolvingTransportCurveOn (V := E) (fun r => ricciEndomorphismAt (g r) p) hab.le hcont hK s v)
    (evolvingTransportCurveOn (V := E) (fun r => ricciEndomorphismAt (g r) p) hab.le hcont hK s w)
  have hdiff : DifferentiableOn ℝ f (Icc a b) := by
    intro s hs
    exact (intrinsicEvolvingTransport_metricInner_hasDerivWithinAt_zero
      hflow p hab.le hJ hcont hK v w hs).differentiableWithinAt
  have hderiv : ∀ s ∈ Ico a b, derivWithin f (Icc a b) s = 0 := by
    intro s hs
    exact (intrinsicEvolvingTransport_metricInner_hasDerivWithinAt_zero
      hflow p hab.le hJ hcont hK v w ⟨hs.1, hs.2.le⟩).derivWithin
        ((uniqueDiffOn_Icc hab) s ⟨hs.1, hs.2.le⟩)
  have hconst := constant_of_derivWithin_zero hdiff hderiv t ht
  change f t = (g a).metricInner p v w
  rw [hconst]
  dsimp [f]
  rw [evolvingTransportCurveOn_apply_of_mem (V := E) _ hab.le hcont hK ⟨le_rfl, hab.le⟩,
    evolvingTransportCurveOn_apply_of_mem (V := E) _ hab.le hcont hK ⟨le_rfl, hab.le⟩]
  rw [Riemannian.LinearODE.solOf_left (E := E) hab.le hcont hK v,
    Riemannian.LinearODE.solOf_left (E := E) hab.le hcont hK w]

end MorganTianLib

end

#print axioms MorganTianLib.metricInner_hasDerivWithinAt_zero_of_ricciTransport
#print axioms MorganTianLib.intrinsicEvolvingTransport_metricInner_eq_left

import DoCarmoLib.Riemannian.Manifold.PullbackMetric
import Topping.RicciFlow.Existence.ShortTimeExistence

/-!
# Concrete metric pullback for the Hamilton gauge

The Hamilton gauge interface records the pullback relation coefficientwise.
Here a diffeomorphism and a Riemannian metric produce the actual smooth
pullback metric.  This discharges the metric-construction part of the gauge
step; differentiating a time-dependent pullback and proving Ricci naturality
remain separate geometric theorems.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A smooth diffeomorphism is a smooth immersion. -/
private theorem diffeomorph_isSmoothImmersion
    (φ : Diffeomorph I I M M ∞) :
    DCSmoothImmersion (I := I) (I' := I) (φ : M → M) := by
  refine ⟨φ.isLocalDiffeomorph.contMDiff, fun p => ?_⟩
  have hcoe := φ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv_coe
    (n := ∞) (by simp) p
  simp only [← hcoe, ContinuousLinearEquiv.coe_coe]
  exact (φ.isLocalDiffeomorph.mfderivToContinuousLinearEquiv
    (n := ∞) (by simp) p).injective

/-- **Math.** The concrete pullback `φ^* g` as a smooth Riemannian metric. -/
noncomputable def gaugePullbackMetric
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞) :
    RiemannianMetric I M := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact RiemannianMetric.pullbackOfSmoothImmersion g (φ : M → M)
    (diffeomorph_isSmoothImmersion φ)

/-- **Math.** The constructed metric has exactly the Hamilton-gauge pullback
coefficients. -/
theorem gaugePullbackMetric_metricInner
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞)
    (p : M) (v w : TangentSpace I p) :
    (gaugePullbackMetric g φ).metricInner p v w =
      MorganTianLib.gaugePullbackValue g φ p v w := by
  simp only [gaugePullbackMetric,
    RiemannianMetric.pullbackOfSmoothImmersion_metricInner]
  rfl

/-- **Math.** The diffeomorphism preserves the concrete pullback metric. -/
theorem gaugePullbackMetric_dcPreservesMetric
    (g : RiemannianMetric I M) (φ : Diffeomorph I I M M ∞) :
    DCPreservesMetric (gaugePullbackMetric g φ) g (φ : M → M) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact RiemannianMetric.dcPreservesMetric_pullbackOfSmoothImmersion
    g (φ : M → M) (diffeomorph_isSmoothImmersion φ)

/-- **Math.** Pullback by the identity diffeomorphism is the original metric. -/
theorem gaugePullbackMetric_refl (g : RiemannianMetric I M) :
    gaugePullbackMetric g (Diffeomorph.refl I M ∞) = g := by
  apply MorganTianLib.riemannianMetric_eq_of_metricInner_eq
  intro p v w
  rw [gaugePullbackMetric_metricInner]
  exact MorganTianLib.gaugePullbackValue_refl g p v w

/-- **Math.** Pulling back first by `ψ` and then by `φ` is pullback by
the composite `ψ ∘ φ`. -/
theorem gaugePullbackMetric_trans (g : RiemannianMetric I M)
    (φ ψ : Diffeomorph I I M M ∞) :
    gaugePullbackMetric (gaugePullbackMetric g ψ) φ =
      gaugePullbackMetric g (φ.trans ψ) := by
  apply MorganTianLib.riemannianMetric_eq_of_metricInner_eq
  intro p v w
  rw [gaugePullbackMetric_metricInner, gaugePullbackMetric_metricInner]
  unfold MorganTianLib.gaugePullbackValue
  rw [gaugePullbackMetric_metricInner]
  rw [Diffeomorph.coe_trans]
  rw [mfderiv_comp p
    (ψ.contMDiff.mdifferentiableAt (by decide))
    (φ.contMDiff.mdifferentiableAt (by decide))]
  rfl

/-- **Math.** Pullback by a diffeomorphism and then by its inverse cancels. -/
theorem gaugePullbackMetric_symm_right (g : RiemannianMetric I M)
    (φ : Diffeomorph I I M M ∞) :
    gaugePullbackMetric (gaugePullbackMetric g φ) φ.symm = g := by
  rw [gaugePullbackMetric_trans, φ.symm_trans_self, gaugePullbackMetric_refl]

/-- **Math.** Pullback by the inverse and then by the diffeomorphism cancels. -/
theorem gaugePullbackMetric_symm_left (g : RiemannianMetric I M)
    (φ : Diffeomorph I I M M ∞) :
    gaugePullbackMetric (gaugePullbackMetric g φ.symm) φ = g := by
  rw [gaugePullbackMetric_trans, φ.self_trans_symm, gaugePullbackMetric_refl]

/-- **Math.** Pullback by a fixed diffeomorphism is injective on metrics. -/
theorem gaugePullbackMetric_injective (φ : Diffeomorph I I M M ∞) :
    Function.Injective (fun g : RiemannianMetric I M => gaugePullbackMetric g φ) := by
  intro g h hpull
  have hcanceled := congrArg (fun k => gaugePullbackMetric k φ.symm) hpull
  simpa only [gaugePullbackMetric_symm_right] using hcanceled

/-- **Math.** Apply the concrete pullback construction at every time. -/
noncomputable def gaugePullbackMetricFamily
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞) :
    ℝ → RiemannianMetric I M :=
  fun t => gaugePullbackMetric (gBar t) (φ t)

/-- **Math.** The concrete family supplies the coefficientwise pullback
predicate used by Hamilton-gauge transport. -/
theorem gaugePullbackMetricFamily_isGaugePullbackOn
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞) (J : Set ℝ) :
    MorganTianLib.IsGaugePullbackOn gBar
      (gaugePullbackMetricFamily gBar φ) φ J := by
  intro t ht p v w
  exact gaugePullbackMetric_metricInner (gBar t) (φ t) p v w

/-- **Math.** An identity gauge at time zero preserves the initial metric. -/
theorem gaugePullbackMetricFamily_zero
    (gBar : ℝ → RiemannianMetric I M)
    (φ : ℝ → Diffeomorph I I M M ∞)
    (hφ0 : φ 0 = Diffeomorph.refl I M ∞) :
    gaugePullbackMetricFamily gBar φ 0 = gBar 0 := by
  rw [gaugePullbackMetricFamily, hφ0]
  exact gaugePullbackMetric_refl (gBar 0)

/-- **Math.** Build the Hamilton-gauge transport structure with its metric
family fixed to the concrete pullback construction.  The remaining fields are
exactly the independent smoothness, transport, and Ricci-naturality outputs
of the gauge argument. -/
noncomputable def HamiltonGaugeTransport.of_concretePullback
    {g₀ : RiemannianMetric I M}
    (S : MorganTianLib.RicciDeTurckLocalSolution g₀)
    (φ : ℝ → Diffeomorph I I M M ∞)
    (hsmooth :
      ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
        ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (MorganTianLib.horizontalMetricSection
          (gaugePullbackMetricFamily S.gBar φ))
        ((Set.univ : Set M) ×ˢ Ico 0 S.T))
    (hφ0 : φ 0 = Diffeomorph.refl I M ∞)
    (htransport :
      MorganTianLib.IsHamiltonGaugeTransportOn S.gBar
        (gaugePullbackMetricFamily S.gBar φ) S.V φ (Ico 0 S.T))
    (hnaturality :
      MorganTianLib.IsRicciPullbackCompatible S.gBar
        (gaugePullbackMetricFamily S.gBar φ) φ (Ico 0 S.T)) :
    MorganTianLib.HamiltonGaugeTransport S :=
  { g := gaugePullbackMetricFamily S.gBar φ
    φ := φ
    smooth_raw := hsmooth
    gaugeAtZero := hφ0
    pullback_raw := by
      intro t ht p v w
      exact gaugePullbackMetric_metricInner (S.gBar t) (φ t) p v w
    transport_raw := by
      intro t ht p v w
      exact htransport t ht p v w
    ricciNaturality_raw := by
      intro t ht p v w
      exact hnaturality t ht p v w }

#print axioms gaugePullbackMetric_metricInner
#print axioms gaugePullbackMetric_dcPreservesMetric
#print axioms gaugePullbackMetric_refl
#print axioms gaugePullbackMetric_trans
#print axioms gaugePullbackMetric_symm_right
#print axioms gaugePullbackMetric_symm_left
#print axioms gaugePullbackMetric_injective
#print axioms gaugePullbackMetricFamily_isGaugePullbackOn
#print axioms gaugePullbackMetricFamily_zero

end Topping

end

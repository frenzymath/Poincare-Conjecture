import MorganTianLib.Ch03.RicciFlow.HamiltonGauge

/-!
# Morgan--Tian Ch. 3 -- split local-existence interfaces

The Hamilton--DeTurck construction has two independent analytic outputs.  A
strictly parabolic solver produces the gauge-fixed metric, while the flow of
the time-dependent DeTurck field produces the pullback.  This module keeps
those outputs in separate primitive structures and proves the assembly and
overlap consequences.  No existence claim is hidden in either structure.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Independent PDE and gauge outputs -/

/-- **Math.** Primitive output of the closed-manifold Ricci--DeTurck PDE
solver.  The three fields are exactly the metric regularity, equation, and
initial trace needed by the Hamilton gauge transfer; they do not assert that
such a solver exists. -/
structure RicciDeTurckLocalSolution (g₀ : RiemannianMetric I M) where
  T : ℝ
  hT : 0 < T
  gBar : ℝ → RiemannianMetric I M
  V : ℝ → SmoothVectorField I M
  smooth_raw :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection gBar)
      ((Set.univ : Set M) ×ˢ Ico 0 T)
  equation_raw :
    ∀ t ∈ (Ico 0 T : Set ℝ), ∀ (p : M) (v w : TangentSpace I p),
      HasDerivWithinAt (fun s => (gBar s).metricInner p v w)
        (ricciDeTurckVariation (gBar t) (V t) p v w) (Ico 0 T) t
  initial_raw :
    ∀ (p : M) (v w : TangentSpace I p),
      (gBar 0).metricInner p v w = g₀.metricInner p v w

/-- **Math.** Primitive output of the time-dependent Hamilton gauge ODE for a
fixed DeTurck solution.  The pullback, transport derivative, and Ricci
naturality are kept as coefficient identities so each can be discharged by a
separate geometric producer. -/
structure HamiltonGaugeTransport
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀) where
  g : ℝ → RiemannianMetric I M
  φ : ℝ → Diffeomorph I I M M ∞
  smooth_raw :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection g)
      ((Set.univ : Set M) ×ˢ Ico 0 S.T)
  gaugeAtZero : φ 0 = Diffeomorph.refl I M ∞
  pullback_raw :
    ∀ t ∈ (Ico 0 S.T : Set ℝ), ∀ (p : M) (v w : TangentSpace I p),
      (g t).metricInner p v w =
        gaugePullbackValue (S.gBar t) (φ t) p v w
  transport_raw :
    ∀ t ∈ (Ico 0 S.T : Set ℝ), ∀ (p : M) (v w : TangentSpace I p),
      HasDerivWithinAt (fun s => (g s).metricInner p v w)
        (gaugeTransportVariationValue S.gBar S.V φ t p v w)
        (Ico 0 S.T) t
  ricciNaturality_raw :
    ∀ t ∈ (Ico 0 S.T : Set ℝ), ∀ (p : M) (v w : TangentSpace I p),
      ricciTensorAt (g t) p v w =
        gaugePullbackRicciValue (S.gBar t) (φ t) p v w

/-! ## Adapters for downstream consumers -/

theorem RicciDeTurckLocalSolution.smooth
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀) :
    IsSmoothMetricFamilyOn S.gBar (Ico 0 S.T) := S.smooth_raw

theorem RicciDeTurckLocalSolution.deTurckEquation
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀) :
    IsRicciDeTurckEquationOn S.gBar S.V (Ico 0 S.T) := S.equation_raw

theorem RicciDeTurckLocalSolution.initial
    {g₀ : RiemannianMetric I M}
    (S : RicciDeTurckLocalSolution g₀) : S.gBar 0 = g₀ := by
  exact riemannianMetric_eq_of_metricInner_eq S.initial_raw

/-! ## Assembly -/

/-- **Math.** The split PDE and Hamilton-gauge outputs assemble into the
primitive certificate consumed by the Ricci-flow transfer theorem. -/
def HamiltonGaugeTransport.certificate
    {g₀ : RiemannianMetric I M}
    {S : RicciDeTurckLocalSolution g₀}
    (G : HamiltonGaugeTransport S) : HamiltonGaugeCertificate g₀ :=
  { T := S.T
    hT := S.hT
    gBar := S.gBar
    g := G.g
    V := S.V
    φ := G.φ
    smooth_raw := G.smooth_raw
    deTurckSmooth_raw := S.smooth_raw
    deTurckEquation_raw := S.equation_raw
    deTurckInitial_raw := S.initial_raw
    gaugeAtZero := G.gaugeAtZero
    pullback_raw := G.pullback_raw
    transport_raw := G.transport_raw
    ricciNaturality_raw := G.ricciNaturality_raw }

/-- **Math.** A split Hamilton--DeTurck output yields a closed-manifold local
Ricci flow with the prescribed initial metric. -/
theorem exists_localRicciFlow_of_splitHamiltonGauge
    {g₀ : RiemannianMetric I M}
    {S : RicciDeTurckLocalSolution g₀}
    (G : HamiltonGaugeTransport S) :
    ∃ T : ℝ, 0 < T ∧ ∃ g : ℝ → RiemannianMetric I M,
      IsRicciFlowOn g (Ico 0 T) ∧ g 0 = g₀ := by
  exact exists_localRicciFlow_of_hamiltonGaugeCertificate G.certificate

/-- **Math.** The split transport has the prescribed initial metric. -/
theorem HamiltonGaugeTransport.initial
    {g₀ : RiemannianMetric I M}
    {S : RicciDeTurckLocalSolution g₀}
    (G : HamiltonGaugeTransport S) :
    G.g 0 = g₀ := by
  exact (G.certificate).initial

/-! The exact-time flow projection is useful when a consumer needs the
transported family rather than the existential packaging. -/

theorem HamiltonGaugeTransport.isRicciFlowOn
    {g₀ : RiemannianMetric I M}
    {S : RicciDeTurckLocalSolution g₀}
    (G : HamiltonGaugeTransport S) :
    IsRicciFlowOn G.g (Ico 0 S.T) :=
  (G.certificate).isRicciFlowOn

/-! ## Uniqueness on the common time interval -/

/-- **Math.** Two Hamilton transports with the same gauge-fixed metric and the
same diffeomorphism agree on the overlap of their short-time intervals.  This
is the source uniqueness conclusion after the separate DeTurck PDE and gauge
ODE uniqueness producers have identified those two data. -/
theorem HamiltonGaugeTransport.eq_on_overlap
    {g₀₁ g₀₂ : RiemannianMetric I M}
    {S₁ : RicciDeTurckLocalSolution g₀₁}
    {S₂ : RicciDeTurckLocalSolution g₀₂}
    (G₁ : HamiltonGaugeTransport S₁)
    (G₂ : HamiltonGaugeTransport S₂)
    (hbar : ∀ t ∈ (Ico 0 (min S₁.T S₂.T) : Set ℝ),
      S₁.gBar t = S₂.gBar t)
    (hφ : ∀ t ∈ (Ico 0 (min S₁.T S₂.T) : Set ℝ),
      G₁.φ t = G₂.φ t) :
    ∀ t ∈ (Ico 0 (min S₁.T S₂.T) : Set ℝ), G₁.g t = G₂.g t := by
  apply metricFamily_eq_of_sameGauge hbar hφ
  · intro t ht p v w
    exact G₁.pullback_raw t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ p v w
  · intro t ht p v w
    exact G₂.pullback_raw t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ p v w

/-- **Math.** The overlap equality also gives coefficient-level agreement,
which is convenient when the two gauge transports are compared before metric
extensionality is invoked. -/
theorem HamiltonGaugeTransport.agreement_on_overlap
    {g₀₁ g₀₂ : RiemannianMetric I M}
    {S₁ : RicciDeTurckLocalSolution g₀₁}
    {S₂ : RicciDeTurckLocalSolution g₀₂}
    (G₁ : HamiltonGaugeTransport S₁)
    (G₂ : HamiltonGaugeTransport S₂)
    (hbar : ∀ t ∈ (Ico 0 (min S₁.T S₂.T) : Set ℝ),
      S₁.gBar t = S₂.gBar t)
    (hφ : ∀ t ∈ (Ico 0 (min S₁.T S₂.T) : Set ℝ),
      G₁.φ t = G₂.φ t) :
    MetricFamilyAgreementOn G₁.g G₂.g (Ico 0 (min S₁.T S₂.T)) := by
  exact metricFamilyAgreementOn_of_sameGauge hbar hφ
    (fun t ht p v w =>
      G₁.pullback_raw t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩ p v w)
    (fun t ht p v w =>
      G₂.pullback_raw t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩ p v w)

#print axioms RicciDeTurckLocalSolution
#print axioms HamiltonGaugeTransport.certificate
#print axioms exists_localRicciFlow_of_splitHamiltonGauge
#print axioms HamiltonGaugeTransport.eq_on_overlap
#print axioms HamiltonGaugeTransport.agreement_on_overlap

end MorganTianLib

end

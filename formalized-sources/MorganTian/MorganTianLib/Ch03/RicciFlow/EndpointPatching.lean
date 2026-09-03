import MorganTianLib.Ch03.RicciFlow.SmoothPatchingFlow
import MorganTianLib.Ch03.RicciFlow.SmoothPatchingTwoSided
import MorganTianLib.Ch03.RicciFlow.SmoothEndpointBootstrap

/-!
# Endpoint limits and restart certificates for Ricci flow

The endpoint argument in the convergence chapter has three logically distinct
inputs: coefficient limits at the old endpoint, a smooth restarted flow, and
the smoothness of the family obtained by joining the two pieces.  This module
keeps those inputs explicit and proves the bookkeeping consequences used by
maximal-interval arguments.  The analytic work which supplies the limits and
the joint smoothness remains a separate producer.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## One-sided endpoint limits -/

/-- **Math.** A one-sided limit at a genuine left endpoint is unique. -/
theorem leftEndpointLimit_unique
    {F : Type*} [TopologicalSpace F] [T2Space F]
    {a b : ℝ} (hab : a < b) {f : ℝ → F} {x y : F}
    (hx : Tendsto f (𝓝[Ioo a b] b) (𝓝 x))
    (hy : Tendsto f (𝓝[Ioo a b] b) (𝓝 y)) :
    x = y := by
  have hne : NeBot (𝓝[Ioo a b] b) := by
    rw [nhdsWithin_Ioo_eq_nhdsLT hab]
    exact nhdsLT_neBot_of_exists_lt ⟨a, hab⟩
  exact tendsto_nhds_unique' hne hx hy

/-- **Math.** Uniform convergence on a set of coefficient parameters gives the
pointwise one-sided endpoint limit at every parameter in that set. -/
theorem leftEndpoint_tendsto_of_tendstoUniformlyOn
    {A F : Type*} [TopologicalSpace A] [UniformSpace F]
    {a b : ℝ} (_hab : a < b) {K : Set A}
    {u : ℝ → A → F} {u₀ : A → F}
    (h : TendstoUniformlyOn u u₀ (𝓝[Ioo a b] b) K)
    {z : A} (hz : z ∈ K) :
    Tendsto (fun t => u t z) (𝓝[Ioo a b] b) (𝓝 (u₀ z)) := by
  exact h.tendsto_at hz

/-- **Math.** Locally uniform convergence on a set gives the corresponding
pointwise one-sided endpoint limit. -/
theorem leftEndpoint_tendsto_of_tendstoLocallyUniformlyOn
    {A F : Type*} [TopologicalSpace A] [UniformSpace F]
    {a b : ℝ} (_hab : a < b) {K : Set A}
    {u : ℝ → A → F} {u₀ : A → F}
    (h : TendstoLocallyUniformlyOn u u₀ (𝓝[Ioo a b] b) K)
    {z : A} (hz : z ∈ K) :
    Tendsto (fun t => u t z) (𝓝[Ioo a b] b) (𝓝 (u₀ z)) := by
  exact h.tendsto_at hz

/-- **Math.** Continuity at the endpoint supplies a one-sided limit from any
nonempty interval immediately to its left. -/
theorem leftEndpoint_tendsto_of_continuousAt
    {F : Type*} [TopologicalSpace F]
  {a b : ℝ} (_hab : a < b) {u : ℝ → F}
    (hu : ContinuousAt u b) :
    Tendsto u (𝓝[Ioo a b] b) (𝓝 (u b)) := by
  exact hu.tendsto.mono_left nhdsWithin_le_nhds

/-- **Math.** The metric and Ricci coefficients at an endpoint are the two
limits needed to join a left flow to a restarted right flow. -/
structure EndpointCoefficientLimits
    (a b : ℝ) (gLeft gRight : ℝ → RiemannianMetric I M) : Prop where
  metric : ∀ (p : M) (x y : TangentSpace I p),
    Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
      (𝓝 ((gRight b).metricInner p x y))
  ricci : ∀ (p : M) (x y : TangentSpace I p),
    Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
      (𝓝 (ricciTensorAt (gRight b) p x y))

/-- **Math.** If every metric and Ricci coefficient extends continuously to the
chosen endpoint value, those extensions provide the endpoint-limit certificate.
This is the coefficient-bootstrap interface used by the restart construction. -/
theorem endpointCoefficientLimits_of_continuousAt
    {a b : ℝ} (hab : a < b)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (hMetricCont : ∀ (p : M) (x y : TangentSpace I p),
      ContinuousAt (fun t => (gLeft t).metricInner p x y) b)
    (hMetricValue : ∀ (p : M) (x y : TangentSpace I p),
      (gLeft b).metricInner p x y = (gRight b).metricInner p x y)
    (hRicciCont : ∀ (p : M) (x y : TangentSpace I p),
      ContinuousAt (fun t => ricciTensorAt (gLeft t) p x y) b)
    (hRicciValue : ∀ (p : M) (x y : TangentSpace I p),
      ricciTensorAt (gLeft b) p x y = ricciTensorAt (gRight b) p x y) :
    EndpointCoefficientLimits a b gLeft gRight := by
  refine ⟨?_, ?_⟩
  · intro p x y
    rw [← hMetricValue p x y]
    exact leftEndpoint_tendsto_of_continuousAt hab (hMetricCont p x y)
  · intro p x y
    rw [← hRicciValue p x y]
    exact leftEndpoint_tendsto_of_continuousAt hab (hRicciCont p x y)

/-- **Math.** The endpoint metric coefficient limit is unchanged when the left
family is replaced by the actual patched family. -/
theorem EndpointCoefficientLimits.patched_metric
    {a b : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (_hab : a < b) (h : EndpointCoefficientLimits a b gLeft gRight)
    (p : M) (x y : TangentSpace I p) :
    Tendsto
      (fun t => (patchedMetricFamily b gLeft gRight t).metricInner p x y)
      (𝓝[Ioo a b] b) (𝓝 ((gRight b).metricInner p x y)) := by
  apply (h.metric p x y).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact congrArg (fun g : RiemannianMetric I M => g.metricInner p x y)
    (patchedMetricFamily_of_lt b gLeft gRight ht.2).symm

/-- **Math.** The endpoint Ricci coefficient limit is unchanged when the left
family is replaced by the actual patched family. -/
theorem EndpointCoefficientLimits.patched_ricci
    {a b : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (_hab : a < b) (h : EndpointCoefficientLimits a b gLeft gRight)
    (p : M) (x y : TangentSpace I p) :
    Tendsto
      (fun t => ricciTensorAt (patchedMetricFamily b gLeft gRight t) p x y)
      (𝓝[Ioo a b] b) (𝓝 (ricciTensorAt (gRight b) p x y)) := by
  apply (h.ricci p x y).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact congrArg (fun g : RiemannianMetric I M => ricciTensorAt g p x y)
    (patchedMetricFamily_of_lt b gLeft gRight ht.2).symm

/-- **Math.** Two endpoint metrics that realize the same left coefficient limit
have identical metric coefficients at the joining time. -/
theorem endpointMetricCoefficient_unique_of_limits
    {a b : ℝ} (hab : a < b)
    {gLeft gRight₁ gRight₂ : ℝ → RiemannianMetric I M}
    (h₁ : EndpointCoefficientLimits a b gLeft gRight₁)
    (h₂ : EndpointCoefficientLimits a b gLeft gRight₂)
    (p : M) (x y : TangentSpace I p) :
    (gRight₁ b).metricInner p x y = (gRight₂ b).metricInner p x y := by
  exact leftEndpointLimit_unique hab (h₁.metric p x y) (h₂.metric p x y)

/-- **Math.** Two endpoint Ricci tensors that realize the same left coefficient
limit have identical Ricci coefficients at the joining time. -/
theorem endpointRicciCoefficient_unique_of_limits
    {a b : ℝ} (hab : a < b)
    {gLeft gRight₁ gRight₂ : ℝ → RiemannianMetric I M}
    (h₁ : EndpointCoefficientLimits a b gLeft gRight₁)
    (h₂ : EndpointCoefficientLimits a b gLeft gRight₂)
    (p : M) (x y : TangentSpace I p) :
    ricciTensorAt (gRight₁ b) p x y = ricciTensorAt (gRight₂ b) p x y := by
  exact leftEndpointLimit_unique hab (h₁.ricci p x y) (h₂.ricci p x y)

/-! ## Explicit extension relation -/

/-- **Math.** `gNew` extends `gOld` on a larger time set when it is a genuine
Ricci flow there and agrees with the old family on every old time. -/
def RicciFlowExtensionOn
    (gOld : ℝ → RiemannianMetric I M) (JOld : Set ℝ)
    (gNew : ℝ → RiemannianMetric I M) (JNew : Set ℝ) : Prop :=
  JOld ⊆ JNew ∧ IsRicciFlowOn gNew JNew ∧
    ∀ t ∈ JOld, gNew t = gOld t

/-- **Math.** Consumer adapter. A smooth restarted piece, together with endpoint
coefficient limits, is the bundled certificate consumed by the local patching
theorem. The analytic producer is `SmoothEndpointRestartData` below; this
adapter deliberately exposes the already-derived `Is*` predicates for existing
downstream APIs. -/
structure SmoothEndpointRestart
    (a b c : ℝ) (gLeft gRight : ℝ → RiemannianMetric I M) : Prop where
  hab : a < b
  hbc : b < c
  left : IsRicciFlowOn gLeft (Ico a b)
  right : IsRicciFlowOn gRight (Ico b c)
  smooth : IsSmoothMetricFamilyOn
    (patchedMetricFamily b gLeft gRight) (Ico a c)
  limits : EndpointCoefficientLimits a b gLeft gRight

/-!
The source-facing producer keeps the analytic inputs primitive. In particular,
it stores section-level `ContMDiffOn` and coefficient-level derivative fields,
not a target-shaped `IsRicciFlowOn` or `IsSmoothMetricFamilyOn` proposition.
The global extension is the raw gluing datum used to derive smoothness of the
joined family.
-/

/-- **Math.** Primitive data for an endpoint restart and smooth patch.
The two side equations are the coefficient Ricci-flow equations on their
half-open intervals; `extension` supplies the smooth section germ across the
join. -/
structure SmoothEndpointRestartData
    (a b c : ℝ) (gLeft gRight : ℝ → RiemannianMetric I M) where
  hab : a < b
  hbc : b < c
  left_smooth_raw :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection gLeft)
      ((Set.univ : Set M) ×ˢ Ico a b)
  right_smooth_raw :
    ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
      ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (horizontalMetricSection gRight)
      ((Set.univ : Set M) ×ˢ Ico b c)
  left_equation_raw :
    ∀ t ∈ (Ico a b : Set ℝ), ∀ (p : M)
      (x y : TangentSpace I p),
      HasDerivWithinAt (fun s => (gLeft s).metricInner p x y)
        (-2 * ricciTensorAt (gLeft t) p x y) (Ico a b) t
  right_equation_raw :
    ∀ t ∈ (Ico b c : Set ℝ), ∀ (p : M)
      (x y : TangentSpace I p),
      HasDerivWithinAt (fun s => (gRight s).metricInner p x y)
        (-2 * ricciTensorAt (gRight t) p x y) (Ico b c) t
  extension : SmoothEndpointExtension (I := I) (a := a) (b := b) (c := c)
    gLeft gRight
  limits : EndpointCoefficientLimits a b gLeft gRight

/-- **Math.** Primitive endpoint data assemble into the legacy consumer
certificate. -/
theorem SmoothEndpointRestartData.toAdapter
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointRestartData (I := I) a b c gLeft gRight) :
    SmoothEndpointRestart a b c gLeft gRight := by
  have hleftNontrivial : (Ico a b : Set ℝ).Nontrivial := by
    apply nontrivial_of_mem_mem_ne
      (show a ∈ (Ico a b : Set ℝ) from ⟨le_rfl, h.hab⟩)
      (show (a + b) / 2 ∈ (Ico a b : Set ℝ) by constructor <;> linarith [h.hab])
      (by linarith [h.hab])
  have hrightNontrivial : (Ico b c : Set ℝ).Nontrivial := by
    apply nontrivial_of_mem_mem_ne
      (show b ∈ (Ico b c : Set ℝ) from ⟨le_rfl, h.hbc⟩)
      (show (b + c) / 2 ∈ (Ico b c : Set ℝ) by constructor <;> linarith [h.hbc])
      (by linarith [h.hbc])
  have hleft : IsRicciFlowOn gLeft (Ico a b) :=
    { ordConnected := ordConnected_Ico
      nontrivial := hleftNontrivial
      smooth := h.left_smooth_raw
      equation := h.left_equation_raw }
  have hright : IsRicciFlowOn gRight (Ico b c) :=
    { ordConnected := ordConnected_Ico
      nontrivial := hrightNontrivial
      smooth := h.right_smooth_raw
      equation := h.right_equation_raw }
  have hpatched : IsSmoothMetricFamilyOn
      (patchedMetricFamily b gLeft gRight) (Ico a c) :=
    smoothMetricFamilyOn_patchedMetricFamily_of_extension
      h.hab h.hbc h.extension
  exact
    { hab := h.hab
      hbc := h.hbc
      left := hleft
      right := hright
      smooth := hpatched
      limits := h.limits }

/-- **Math.** The restart certificate produces a Ricci flow on the joined
interval. -/
theorem SmoothEndpointRestart.isRicciFlowOn
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointRestart a b c gLeft gRight) :
    IsRicciFlowOn (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  exact isRicciFlowOn_patchedMetricFamily_of_smooth
    h.hab h.hbc gLeft gRight h.left h.right h.smooth
    h.limits.metric h.limits.ricci

/-- **Math.** The patched family agrees with the old flow on its pre-endpoint
interval. -/
theorem SmoothEndpointRestart.agrees_left
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (_h : SmoothEndpointRestart a b c gLeft gRight) :
    ∀ t ∈ Ico a b, patchedMetricFamily b gLeft gRight t = gLeft t := by
  intro t ht
  exact patchedMetricFamily_of_lt b gLeft gRight ht.2

/-- **Math.** The patched family agrees with the restarted flow from the joining
time onward. -/
theorem SmoothEndpointRestart.agrees_right
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (_h : SmoothEndpointRestart a b c gLeft gRight) :
    ∀ t ∈ Ico b c, patchedMetricFamily b gLeft gRight t = gRight t := by
  intro t ht
  exact patchedMetricFamily_of_le b gLeft gRight ht.1

/-- **Math.** The joined flow is an extension of its left-hand piece. -/
theorem SmoothEndpointRestart.extends_left
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointRestart a b c gLeft gRight) :
    RicciFlowExtensionOn gLeft (Ico a b)
      (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  refine ⟨?_, h.isRicciFlowOn, h.agrees_left⟩
  intro t ht
  exact ⟨ht.1, lt_trans ht.2 h.hbc⟩

/-- **Math.** The joined flow contains the restarted right-hand piece as its
post-endpoint restriction. -/
theorem SmoothEndpointRestart.extends_right
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointRestart a b c gLeft gRight) :
    RicciFlowExtensionOn gRight (Ico b c)
      (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  refine ⟨?_, h.isRicciFlowOn, h.agrees_right⟩
  intro t ht
  exact ⟨(le_of_lt h.hab).trans ht.1, ht.2⟩

/-- **Math.** The metric coefficients of a restart certificate have the
Ricci-flow derivative at the joining time, including the two-sided statement. -/
theorem SmoothEndpointRestart.hasDerivAt_join
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointRestart a b c gLeft gRight)
    (p : M) (x y : TangentSpace I p) :
    HasDerivAt
      (fun t => (patchedMetricFamily b gLeft gRight t).metricInner p x y)
      (-2 * ricciTensorAt (gRight b) p x y) b := by
  exact patchedMetricFamily_hasDerivAt_at_join h.hab h.hbc gLeft gRight
    h.left.equation h.right.equation h.limits.metric h.limits.ricci p x y

/-- **Math.** A closed-left endpoint flow can be joined directly to a restarted
flow.  The restriction from `[a,b]` to `[a,b)` is proved here, so endpoint
consumers need not duplicate the interval bookkeeping. -/
theorem isRicciFlowOn_patchedMetricFamily_of_closed_left
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : IsRicciFlowOn gLeft (Icc a b))
    (hRight : IsRicciFlowOn gRight (Ico b c))
    (hSmooth : IsSmoothMetricFamilyOn
      (patchedMetricFamily b gLeft gRight) (Ico a c))
    (hLimits : EndpointCoefficientLimits a b gLeft gRight) :
    IsRicciFlowOn (patchedMetricFamily b gLeft gRight) (Ico a c) := by
  have hIcoNontrivial : (Ico a b : Set ℝ).Nontrivial := by
    apply nontrivial_of_mem_mem_ne
      (show a ∈ (Ico a b : Set ℝ) from ⟨le_rfl, hab⟩)
      (show (a + b) / 2 ∈ (Ico a b : Set ℝ) by constructor <;> linarith)
      (by linarith)
  have hLeftIco : IsRicciFlowOn gLeft (Ico a b) := by
    refine
      { ordConnected := ordConnected_Ico
        nontrivial := hIcoNontrivial
        smooth := hLeft.smooth.mono (Set.prod_mono subset_rfl ?_)
        equation := ?_ }
    · intro t ht
      exact ⟨ht.1, le_of_lt ht.2⟩
    · intro t ht p x y
      exact (hLeft.equation t ⟨ht.1, le_of_lt ht.2⟩ p x y).mono
        (fun s hs => ⟨hs.1, le_of_lt hs.2⟩)
  exact isRicciFlowOn_patchedMetricFamily_of_smooth
    hab hbc gLeft gRight hLeftIco hRight hSmooth
    hLimits.metric hLimits.ricci

#print axioms leftEndpointLimit_unique
#print axioms EndpointCoefficientLimits.patched_metric
#print axioms EndpointCoefficientLimits.patched_ricci
#print axioms endpointMetricCoefficient_unique_of_limits
#print axioms endpointRicciCoefficient_unique_of_limits
#print axioms SmoothEndpointRestartData.toAdapter
#print axioms SmoothEndpointRestart.isRicciFlowOn
#print axioms SmoothEndpointRestart.extends_left
#print axioms SmoothEndpointRestart.extends_right
#print axioms SmoothEndpointRestart.hasDerivAt_join
#print axioms isRicciFlowOn_patchedMetricFamily_of_closed_left

end MorganTianLib

end

import Topping.RicciFlow.Existence.EndpointControl

/-!
# Fiberwise endpoint metric data

The coefficient-limit theorem gives a scalar limit for every fixed pair of
tangent vectors.  This file assembles those limits at one fixed base point
into a coherent positive-definite bilinear form.  No continuity in the base
point, smooth endpoint tensor, or Ricci-flow extension is asserted here.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [Nonempty M] [CompactSpace M]

/-- **Math.** A positive-definite symmetric bilinear form on one fixed fiber.

This is intentionally fiber-local: the structure carries no topology or
dependence on a base point.  Such additional regularity belongs to the
separate endpoint-extension argument.
-/
structure EndpointFiberBilinearForm (V : Type*) [AddCommGroup V] [Module ℝ V] where
  inner : V → V → ℝ
  add_left : ∀ x₁ x₂ y, inner (x₁ + x₂) y = inner x₁ y + inner x₂ y
  smul_left : ∀ (c : ℝ) x y, inner (c • x) y = c * inner x y
  add_right : ∀ x y₁ y₂, inner x (y₁ + y₂) = inner x y₁ + inner x y₂
  smul_right : ∀ (c : ℝ) x y, inner x (c • y) = c * inner x y
  symm : ∀ x y, inner x y = inner y x
  pos : ∀ x, x ≠ 0 → 0 < inner x x

/-- **Math.** The left endpoint limits at a fixed point assemble into a coherent
positive-definite bilinear form.  The final conjunct records the coefficient
limit represented by the assembled form.
-/
theorem exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (p : M) :
    ∃ B : EndpointFiberBilinearForm (TangentSpace I p),
      ∀ x y : TangentSpace I p,
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 (B.inner x y)) := by
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hExists : ∀ x y : TangentSpace I p, ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 L) := by
    intro x y
    exact exists_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
      hT hM hflow hRic p x y
  choose L hL using hExists
  have hadd_left : ∀ x₁ x₂ y : TangentSpace I p,
      L (x₁ + x₂) y = L x₁ y + L x₂ y := by
    intro x₁ x₂ y
    have hsum : Tendsto
        (fun t => (g t).metricInner p x₁ y + (g t).metricInner p x₂ y)
        (nhdsWithin T (Iio T)) (𝓝 (L x₁ y + L x₂ y)) :=
      (hL x₁ y).add (hL x₂ y)
    have hsum' : Tendsto
        (fun t => (g t).metricInner p (x₁ + x₂) y)
        (nhdsWithin T (Iio T)) (𝓝 (L x₁ y + L x₂ y)) := by
      simpa only [RiemannianMetric.metricInner_add_left] using hsum
    exact tendsto_nhds_unique (hL (x₁ + x₂) y) hsum'
  have hsmul_left : ∀ (c : ℝ) (x y : TangentSpace I p),
      L (c • x) y = c * L x y := by
    intro c x y
    have hmul : Tendsto
        (fun t => c * (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 (c * L x y)) :=
      (tendsto_const_nhds.mul (hL x y))
    have hmul' : Tendsto
        (fun t => (g t).metricInner p (c • x) y)
        (nhdsWithin T (Iio T)) (𝓝 (c * L x y)) := by
      simpa only [RiemannianMetric.metricInner_smul_left] using hmul
    exact tendsto_nhds_unique (hL (c • x) y) hmul'
  have hadd_right : ∀ x y₁ y₂ : TangentSpace I p,
      L x (y₁ + y₂) = L x y₁ + L x y₂ := by
    intro x y₁ y₂
    have hsum : Tendsto
        (fun t => (g t).metricInner p x y₁ + (g t).metricInner p x y₂)
        (nhdsWithin T (Iio T)) (𝓝 (L x y₁ + L x y₂)) :=
      (hL x y₁).add (hL x y₂)
    have hsum' : Tendsto
        (fun t => (g t).metricInner p x (y₁ + y₂))
        (nhdsWithin T (Iio T)) (𝓝 (L x y₁ + L x y₂)) := by
      simpa only [RiemannianMetric.metricInner_add_right] using hsum
    exact tendsto_nhds_unique (hL x (y₁ + y₂)) hsum'
  have hsmul_right : ∀ (c : ℝ) (x y : TangentSpace I p),
      L x (c • y) = c * L x y := by
    intro c x y
    have hmul : Tendsto
        (fun t => c * (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 (c * L x y)) :=
      (tendsto_const_nhds.mul (hL x y))
    have hmul' : Tendsto
        (fun t => (g t).metricInner p x (c • y))
        (nhdsWithin T (Iio T)) (𝓝 (c * L x y)) := by
      simpa only [RiemannianMetric.metricInner_smul_right] using hmul
    exact tendsto_nhds_unique (hL x (c • y)) hmul'
  have hsymm : ∀ x y : TangentSpace I p, L x y = L y x := by
    intro x y
    have hxy : Tendsto
        (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 (L y x)) := by
      simpa only [RiemannianMetric.metricInner_comm] using hL y x
    exact tendsto_nhds_unique (hL x y) hxy
  have hpos : ∀ x : TangentSpace I p, x ≠ 0 → 0 < L x x := by
    intro x hx
    obtain ⟨L', hL', hL'pos⟩ :=
      exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
        hT hM hflow hRic p x
    have hEq : L x x = L' := tendsto_nhds_unique (hL x x) hL'
    rw [hEq]
    exact hL'pos hx
  refine ⟨{ inner := L
            add_left := hadd_left
            smul_left := hsmul_left
            add_right := hadd_right
            smul_right := hsmul_right
            symm := hsymm
            pos := hpos }, ?_⟩
  exact hL

/-! The pointwise construction can be indexed simultaneously over the base.
This is the global field of endpoint fibers; it deliberately does not assert
continuity or smoothness in the base point. -/

/-- **Math.** A uniform Ricci bound supplies one endpoint bilinear form on
every tangent fiber at once.  The family is obtained from the pointwise
construction above, so its positivity and coefficient-limit properties are
retained without adding any regularity hypothesis on the base dependence. -/
theorem exists_globalEndpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T)) :
    ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
      ∀ (p : M) (x y : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 ((B p).inner x y)) := by
  choose B hB using (fun p : M =>
    exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
      hT hM hflow hRic p)
  exact ⟨B, fun p x y => hB p x y⟩

/-! The quantitative coefficient-limit bounds can be carried through the
fiberwise assembly.  This is the coercivity interface used by endpoint metric
and restart constructions. -/

/-- **Math.** The endpoint bilinear form at a fixed base point inherits the
two-sided metric-equivalence bounds from the pre-endpoint flow. -/
theorem exists_endpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (p : M) :
    ∃ B : EndpointFiberBilinearForm (TangentSpace I p),
      (∀ x y : TangentSpace I p,
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 (B.inner x y))) ∧
      (∀ x : TangentSpace I p,
        (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤ B.inner x x) ∧
      (∀ x : TangentSpace I p,
        B.inner x x ≤ Real.exp (2 * M0 * T) * (g 0).metricInner p x x) := by
  obtain ⟨B, hB⟩ :=
    exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
      hT hM hflow hRic p
  refine ⟨B, hB, ?_, ?_⟩
  · intro x
    obtain ⟨L, hL, hLower, _hUpper⟩ :=
      exists_metricCoefficient_limit_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
        hT hM hflow hRic p x
    have hEq : L = B.inner x x := tendsto_nhds_unique (hL) (hB x x)
    rw [← hEq]
    exact hLower
  · intro x
    obtain ⟨L, hL, _hLower, hUpper⟩ :=
      exists_metricCoefficient_limit_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
        hT hM hflow hRic p x
    have hEq : L = B.inner x x := tendsto_nhds_unique (hL) (hB x x)
    rw [← hEq]
    exact hUpper

/-- **Math.** The globally indexed endpoint fiber family can be chosen with
uniform two-sided comparison constants, while retaining its coefficient-limit
property at every base point. -/
theorem exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T)) :
    ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
      (∀ (p : M) (x y : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 ((B p).inner x y))) ∧
      (∀ (p : M) (x : TangentSpace I p),
        (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤ (B p).inner x x) ∧
      (∀ (p : M) (x : TangentSpace I p),
        (B p).inner x x ≤ Real.exp (2 * M0 * T) * (g 0).metricInner p x x) := by
  choose B hB hLower hUpper using (fun p : M =>
    exists_endpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
      hT hM hflow hRic p)
  refine ⟨B, ?_, ?_, ?_⟩
  · intro p x y
    exact hB p x y
  · intro p x
    exact hLower p x
  · intro p x
    exact hUpper p x

/-- **Math.** A Hilbert--Schmidt Ricci bound supplies a coherent endpoint
fiber form together with the two-sided metric-equivalence bounds. -/
theorem exists_endpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T))
    (p : M) :
    ∃ B : EndpointFiberBilinearForm (TangentSpace I p),
      (∀ x y : TangentSpace I p,
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 (B.inner x y))) ∧
      (∀ x : TangentSpace I p,
        (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤ B.inner x x) ∧
      (∀ x : TangentSpace I p,
        B.inner x x ≤ Real.exp (2 * M0 * T) * (g 0).metricInner p x x) := by
  exact exists_endpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic) p

/-- **Math.** The same norm-bound endpoint construction is simultaneous over
all base points. -/
theorem exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T)) :
    ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
      (∀ (p : M) (x y : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 ((B p).inner x y))) ∧
      (∀ (p : M) (x : TangentSpace I p),
        (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤ (B p).inner x x) ∧
      (∀ (p : M) (x : TangentSpace I p),
        (B p).inner x x ≤ Real.exp (2 * M0 * T) * (g 0).metricInner p x x) := by
  exact exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic)

/-- **Math.** A uniform pre-endpoint curvature bound supplies the bounded
endpoint fiber family with the same quantitative comparison constants. -/
theorem exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) :
    ∃ M0 : ℝ, 0 ≤ M0 ∧
      ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
        (∀ (p : M) (x y : TangentSpace I p),
          Tendsto (fun t => (g t).metricInner p x y)
            (nhdsWithin T (Iio T)) (𝓝 ((B p).inner x y))) ∧
        (∀ (p : M) (x : TangentSpace I p),
          (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤ (B p).inner x x) ∧
        (∀ (p : M) (x : TangentSpace I p),
          (B p).inner x x ≤ Real.exp (2 * M0 * T) * (g 0).metricInner p x x) := by
  obtain ⟨M0, hM, hRic⟩ :=
    exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore hRm
  exact ⟨M0, hM,
    exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_hasRicciNormBoundOn
      hT hM hflow hRic⟩

/-! The same fiberwise endpoint form can be consumed directly from the
source-level norm and curvature hypotheses. -/

/-- **Math.** A Hilbert--Schmidt Ricci bound produces the same coherent endpoint form. -/
theorem exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T))
    (p : M) :
    ∃ B : EndpointFiberBilinearForm (TangentSpace I p),
      ∀ x y : TangentSpace I p,
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 (B.inner x y)) := by
  exact exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic) p

/-- **Math.** A Hilbert--Schmidt Ricci bound supplies a globally indexed
endpoint fiber family. -/
theorem exists_globalEndpointFiberBilinearForm_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T)) :
    ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
      ∀ (p : M) (x y : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 ((B p).inner x y)) := by
  exact exists_globalEndpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic)

/-- **Math.** A uniform pre-endpoint curvature bound produces the same endpoint form. -/
theorem exists_endpointFiberBilinearForm_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) (p : M) :
    ∃ B : EndpointFiberBilinearForm (TangentSpace I p),
      ∀ x y : TangentSpace I p,
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 (B.inner x y)) := by
  obtain ⟨M0, hM, hRicNorm⟩ :=
    exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore hRm
  exact exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRicNorm) p

/-- **Math.** A uniform pre-endpoint curvature bound supplies a globally
indexed endpoint fiber family. -/
theorem exists_globalEndpointFiberBilinearForm_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) :
    ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
      ∀ (p : M) (x y : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 ((B p).inner x y)) := by
  obtain ⟨M0, hM, hRicNorm⟩ :=
    exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore hRm
  exact exists_globalEndpointFiberBilinearForm_of_isRicciFlowOn_of_hasRicciNormBoundOn
    hT hM hflow hRicNorm

/-- **Math.** A uniform pre-endpoint curvature bound supplies the globally
indexed endpoint fiber family on the interior-left filter used by smooth
patching and restart consumers. -/
theorem exists_globalEndpointFiberBilinearForm_Ioo_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) :
    ∃ B : (p : M) → EndpointFiberBilinearForm (TangentSpace I p),
      ∀ (p : M) (x y : TangentSpace I p),
        Tendsto (fun t => (g t).metricInner p x y)
          (𝓝[Ioo (0 : ℝ) T] T) (𝓝 ((B p).inner x y)) := by
  obtain ⟨B, hB⟩ :=
    exists_globalEndpointFiberBilinearForm_of_hasUniformCurvatureBoundBefore
      hT hflow hRm
  refine ⟨B, ?_⟩
  intro p x y
  rw [nhdsWithin_Ioo_eq_nhdsLT hT]
  exact hB p x y

#print axioms exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_endpointFiberBilinearForm_of_isRicciFlowOn_of_hasRicciNormBoundOn
#print axioms exists_endpointFiberBilinearForm_of_hasUniformCurvatureBoundBefore
#print axioms exists_globalEndpointFiberBilinearForm_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_globalEndpointFiberBilinearForm_of_isRicciFlowOn_of_hasRicciNormBoundOn
#print axioms exists_globalEndpointFiberBilinearForm_of_hasUniformCurvatureBoundBefore
#print axioms exists_globalEndpointFiberBilinearForm_Ioo_of_hasUniformCurvatureBoundBefore
#print axioms exists_endpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_endpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_hasRicciNormBoundOn
#print axioms exists_globalEndpointFiberBilinearForm_with_metric_bounds_of_isRicciFlowOn_of_hasRicciNormBoundOn

end Topping

end

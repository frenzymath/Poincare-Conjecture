import MorganTianLib.Ch03.RicciFlow.EndpointCoefficientControl

/-!
# Fiberwise endpoint metric data

The coefficient-limit argument gives a scalar limit for every fixed pair of
tangent vectors.  This file assembles those limits at one fixed base point
into a coherent positive-definite bilinear form.  No continuity in the base
point, smooth endpoint tensor, or Ricci-flow extension is asserted here.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Filter Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A positive-definite symmetric bilinear form on one fixed tangent fiber.

This is deliberately fiber-local: regularity in the base point belongs to a
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

/-- **Math.** Fixed-vector endpoint limits assemble into a coherent positive-definite
bilinear form on each tangent fiber. -/
theorem exists_endpointFiberBilinearForm_of_ricciQuadraticControlOn
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRic : RicciQuadraticControlOn g (Ico 0 T) C)
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
    exact exists_metricCoefficient_limit_of_ricciQuadraticControlOn
      hT hC hflow hRic p x y
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
      tendsto_const_nhds.mul (hL x y)
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
      tendsto_const_nhds.mul (hL x y)
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
      exists_pos_metricCoefficient_limit_of_ricciQuadraticControlOn
        hT hC hflow hRic p x
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

/-- **Math.** A curvature-operator bound supplies the fiberwise endpoint form
through the Ricci quadratic-control adapter. -/
theorem exists_endpointFiberBilinearForm_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Ico 0 T) K)
    (p : M) :
    ∃ B : EndpointFiberBilinearForm (TangentSpace I p),
      ∀ x y : TangentSpace I p,
        Tendsto (fun t => (g t).metricInner p x y)
          (nhdsWithin T (Iio T)) (𝓝 (B.inner x y)) := by
  exact exists_endpointFiberBilinearForm_of_ricciQuadraticControlOn
    hT (mul_nonneg (Nat.cast_nonneg _) hK) hflow
    (ricciQuadraticControlOn_of_hasCurvatureOperatorNormLeOnTime hK hRm) p

#print axioms exists_endpointFiberBilinearForm_of_ricciQuadraticControlOn
#print axioms exists_endpointFiberBilinearForm_of_curvatureOperatorNormLeOnTime

end MorganTianLib

end

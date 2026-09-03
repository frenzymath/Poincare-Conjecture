import MorganTianLib.Ch01.BishopGromovManifold
import MorganTianLib.Ch01.BishopGromovManifoldProducers
import MorganTianLib.Ch01.ExpRiemannianJacobianMeasurable
import MorganTianLib.Ch01.MeasureNormalization

/-!
# Morgan--Tian Ch. 1: explicit Bishop--Gromov normalization

The fixed `gpHaar` convention has a non-unit origin density.  This module
transports the checked Bishop--Gromov comparison and small-radius limit through
the explicit inverse-density scalar.  The scalar is kept visible in the
interface, so the source normalization is obtained without changing the
underlying metric or silently assuming a preferred chart normalization.
-/

open MeasureTheory Measure Set Filter Function Metric Riemannian Riemannian.Geodesic Module
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]
  [CompleteSpace M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** The Haar reference normalized by the positive origin density of
the preferred exponential chart. -/
def normalizedGpHaar (g : RiemannianMetric I M) (p : M) : Measure E :=
  (gpHaarOriginDensity (I := I) g p)⁻¹ • gpHaar (I := I) g p

/-- **Math.** The normalization scalar is nonzero and finite. -/
theorem normalizedGpHaar_scalar_ne_zero_top
    (g : RiemannianMetric I M) (p : M) :
    (gpHaarOriginDensity (I := I) g p)⁻¹ ≠ 0 ∧
      (gpHaarOriginDensity (I := I) g p)⁻¹ ≠ (⊤ : ℝ≥0∞) := by
  have hpos : 0 < gpHaarOriginDensity (I := I) g p :=
    gpHaarOriginDensity_pos (I := I) g p
  have hzero : gpHaarOriginDensity (I := I) g p ≠ 0 := ne_of_gt hpos
  have htop : gpHaarOriginDensity (I := I) g p ≠ (⊤ : ℝ≥0∞) := by
    rw [gpHaarOriginDensity]
    exact ENNReal.ofReal_ne_top
  exact ⟨ENNReal.inv_ne_zero.mpr htop,
    ENNReal.inv_ne_top.mpr hzero⟩

private theorem normalized_measure_apply
    (g : RiemannianMetric I M) (p : M) (r : ℝ) :
    riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p r) =
      (gpHaarOriginDensity (I := I) g p)⁻¹ *
        riemannianMeasure (I := I) g (gpHaar (I := I) g p)
          (Metric.ball p r) := by
  rw [normalizedGpHaar, riemannianMeasure_smul, Measure.smul_apply]
  rfl

/-- **Math.** Bishop--Gromov antitonicity survives the explicit
inverse-origin-density normalization of the Haar reference. -/
theorem antitoneOn_normalized_riemannianMeasure_ratio
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) {k R : ℝ} (hk : 0 ≤ k) (hR : 0 < R)
    (hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      -(((Module.finrank ℝ E : ℝ) - 1) * k) * g.metricInner x v v
        ≤ ricciAt g g.leviCivitaConnection hLC x v v) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
            (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) k r)
      (Ioo 0 R) := by
  have hbase := bishop_gromov_manifold_ratio (I := I) g hg p hk hR hcompact
    hdim hLC hric
    (measurable_transportedJacobian_of_measurable_expRiemannianJacobian
      (I := I) g hg p
      (measurable_expRiemannianJacobian (I := I) g hg p))
  intro r₁ hr₁ r₂ hr₂ h₁₂
  have hbase' := hbase hr₁ hr₂ h₁₂
  change
    riemannianMeasure (I := I) g (gpHaar (I := I) g p)
        (Metric.ball p r₂) /
      modelBallVolume (volume : Measure 𝔼) k r₂ ≤
      riemannianMeasure (I := I) g (gpHaar (I := I) g p)
        (Metric.ball p r₁) /
      modelBallVolume (volume : Measure 𝔼) k r₁ at hbase'
  have hscale : 0 ≤ (gpHaarOriginDensity (I := I) g p)⁻¹ :=
    by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase' hscale
  change
    riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p r₂) /
      modelBallVolume (volume : Measure 𝔼) k r₂ ≤
      riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p r₁) /
      modelBallVolume (volume : Measure 𝔼)  k r₁
  rw [normalized_measure_apply (I := I) g p r₁,
    normalized_measure_apply (I := I) g p r₂]
  calc
    (gpHaarOriginDensity (I := I) g p)⁻¹ *
        riemannianMeasure (I := I) g (gpHaar (I := I) g p)
          (Metric.ball p r₂) /
      modelBallVolume (volume : Measure 𝔼) k r₂ =
      (gpHaarOriginDensity (I := I) g p)⁻¹ *
        (riemannianMeasure (I := I) g (gpHaar (I := I) g p)
          (Metric.ball p r₂) /
        modelBallVolume (volume : Measure 𝔼) k r₂) := by
          rw [mul_div_assoc]
    _ ≤ (gpHaarOriginDensity (I := I) g p)⁻¹ *
        (riemannianMeasure (I := I) g (gpHaar (I := I) g p)
          (Metric.ball p r₁) /
        modelBallVolume (volume : Measure 𝔼) k r₁) := hscaled
    _ = (gpHaarOriginDensity (I := I) g p)⁻¹ *
        riemannianMeasure (I := I) g (gpHaar (I := I) g p)
          (Metric.ball p r₁) /
      modelBallVolume (volume : Measure 𝔼) k r₁ := by
          rw [mul_div_assoc]

/-- **Math.** The normalized Haar convention has unit small-radius volume/model limit. -/
theorem tendsto_normalized_riemannianMeasure_ball_ratio_nhdsGT_zero
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) :
    Tendsto
      (fun r : ℝ =>
        riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
            (Metric.ball p r) /
          modelBallVolume (volume : Measure 𝔼) 0 r)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa only [normalizedGpHaar] using
    (bishop_gromov_manifold_small_radius_normalization_smul
      (I := I) (g := g) (hg := hg) (p := p)
      (bishop_gromov_manifold_producers_of_available
        (I := I) (g := g) (hg := hg) (p := p) (R := 1)))

/-- **Math.** In the normalized convention and under nonnegative Ricci
curvature, the flat-model power denominator gives the usual antitone volume
ratio. -/
theorem antitoneOn_normalized_riemannianMeasure_div_power
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      0 ≤ ricciAt g g.leviCivitaConnection hLC x v v) :
    AntitoneOn
      (fun r =>
        riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
            (Metric.ball p r) /
          ENNReal.ofReal (r ^ Module.finrank ℝ E))
      (Ioo 0 R) := by
  obtain ⟨C, hCpos, hCtop, hCeq⟩ :=
    flat_modelBallVolume_power (E := E) (R := R) hR
  have hratio := antitoneOn_normalized_riemannianMeasure_ratio
    (I := I) (g := g) (hg := hg) (p := p) (k := 0) (by norm_num)
    hR hcompact hdim hLC (by
      intro x hx v
      simpa using hric x hx v)
  have hC0 : C ≠ 0 := ne_of_gt hCpos
  intro r₁ hr₁ r₂ hr₂ h₁₂
  have hbase := hratio hr₁ hr₂ h₁₂
  change
    riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p r₂) /
      modelBallVolume (volume : Measure 𝔼) 0 r₂ ≤
      riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p r₁) /
      modelBallVolume (volume : Measure 𝔼) 0 r₁ at hbase
  have hP₁pos : 0 < ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr₁.1 _)
  have hP₂pos : 0 < ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) :=
    ENNReal.ofReal_pos.mpr (pow_pos hr₂.1 _)
  have hP₁0 : ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) ≠ 0 := ne_of_gt hP₁pos
  have hP₂0 : ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) ≠ 0 := ne_of_gt hP₂pos
  have hP₁top : ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hP₂top : ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hrewrite₁ :
      riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₁) /
          (C * ENNReal.ofReal (r₁ ^ Module.finrank ℝ E)) =
        (riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₁) /
          ENNReal.ofReal (r₁ ^ Module.finrank ℝ E)) / C := by
    calc
      _ = riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₁) * 1 /
          (ENNReal.ofReal (r₁ ^ Module.finrank ℝ E) * C) := by simp [mul_comm]
      _ = (riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₁) /
          ENNReal.ofReal (r₁ ^ Module.finrank ℝ E)) * (1 / C) :=
        ENNReal.mul_div_mul_comm (Or.inl hP₁0) (Or.inl hP₁top)
      _ = _ := by simp [div_eq_mul_inv, mul_comm]
  have hrewrite₂ :
      riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₂) /
          (C * ENNReal.ofReal (r₂ ^ Module.finrank ℝ E)) =
        (riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₂) /
          ENNReal.ofReal (r₂ ^ Module.finrank ℝ E)) / C := by
    calc
      _ = riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₂) * 1 /
          (ENNReal.ofReal (r₂ ^ Module.finrank ℝ E) * C) := by simp [mul_comm]
      _ = (riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
          (Metric.ball p r₂) /
          ENNReal.ofReal (r₂ ^ Module.finrank ℝ E)) * (1 / C) :=
        ENNReal.mul_div_mul_comm (Or.inl hP₂0) (Or.inl hP₂top)
      _ = _ := by simp [div_eq_mul_inv, mul_comm]
  rw [hCeq r₁ hr₁, hCeq r₂ hr₂, hrewrite₁, hrewrite₂] at hbase
  have hmul := (ENNReal.le_div_iff_mul_le (Or.inl hC0) (Or.inl hCtop)).mp hbase
  rw [ENNReal.div_mul_cancel hC0 hCtop] at hmul
  exact hmul

/-- **Math.** Under nonnegative Ricci curvature, the normalized volume of each
admissible ball is at most the volume of the flat model ball.  This is the
pointwise Bishop--Gromov comparison obtained by combining antitonicity with the
unit small-radius limit. -/
theorem normalized_riemannianMeasure_ball_le_flat_model
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [ConnectedSpace M] (p : M) {R r : ℝ} (hR : 0 < R)
    (hr : r ∈ Ioo (0 : ℝ) R)
    (hcompact : IsCompact (closure (Metric.ball p R)))
    (hdim : 2 ≤ Module.finrank ℝ E)
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (hric : ∀ x ∈ Metric.closedBall p R, ∀ v : TangentSpace I x,
      0 ≤ ricciAt g g.leviCivitaConnection hLC x v v) :
    riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p r) ≤
      modelBallVolume (volume : Measure 𝔼) 0 r := by
  let f : ℝ → ℝ≥0∞ := fun s =>
    riemannianMeasure (I := I) g (normalizedGpHaar (I := I) g p)
        (Metric.ball p s) /
      modelBallVolume (volume : Measure 𝔼) 0 s
  have hanti : AntitoneOn f (Ioo 0 R) :=
    antitoneOn_normalized_riemannianMeasure_ratio
      (I := I) (g := g) (hg := hg) (p := p) (k := 0) (by norm_num)
      hR hcompact hdim hLC (by
        intro x hx v
        simpa using hric x hx v)
  have hlim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_normalized_riemannianMeasure_ball_ratio_nhdsGT_zero
      (I := I) g hg p
  have hratio : f r ≤ 1 := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
    filter_upwards [Ioo_mem_nhdsGT hr.1] with s hs
    exact hanti ⟨hs.1, hs.2.trans hr.2⟩ hr hs.2.le
  have hden0 : modelBallVolume (volume : Measure 𝔼) 0 r ≠ 0 :=
    (modelBallVolume_pos (volume : Measure 𝔼) (by norm_num) hr.1).ne'
  have hdentop : modelBallVolume (volume : Measure 𝔼) 0 r ≠ ⊤ :=
    modelBallVolume_ne_top (volume : Measure 𝔼) (by norm_num) r
  simpa [f] using (ENNReal.div_le_iff hden0 hdentop).mp hratio

end MorganTianLib

end

#print axioms MorganTianLib.antitoneOn_normalized_riemannianMeasure_ratio
#print axioms MorganTianLib.tendsto_normalized_riemannianMeasure_ball_ratio_nhdsGT_zero
#print axioms MorganTianLib.antitoneOn_normalized_riemannianMeasure_div_power
#print axioms MorganTianLib.normalized_riemannianMeasure_ball_le_flat_model

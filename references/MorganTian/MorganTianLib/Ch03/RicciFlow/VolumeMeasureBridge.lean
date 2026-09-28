import MorganTianLib.Ch03.RicciFlow.VolumeDistortion
import MorganTianLib.Ch02.GreenIdentity

/-!
# Measure-level volume distortion for Chapter 3

`VolumeDistortion.lean` proves the scalar exponential comparison for a positive
volume density.  The book's second conclusion is a statement about the volume
of an open set, so a separate change-of-representation step is needed: a real
density `rho` is represented by the measure
`nu.withDensity (fun x => ENNReal.ofReal (rho x))` and the pointwise comparison
is integrated on the set.

This file keeps that step independent of a choice of atlas.  A geometric
producer only has to provide the measurable densities and the pointwise bounds;
the final adapter below obtains those bounds from the already checked scalar
evolution theorem.  No canonical-measure equality is hidden in a predicate.
-/

open Set MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace MorganTianLib

variable {alpha : Type*} [MeasurableSpace alpha]

/-- **Math.** A measure represented by a nonnegative real density with respect to `nu`.

The use of `ENNReal.ofReal` makes the construction meaningful even away from
the region where a geometric density producer has proved positivity. -/
def realDensityMeasure (nu : Measure alpha) (rho : alpha -> ℝ) : Measure alpha :=
  nu.withDensity (fun x => ENNReal.ofReal (rho x))

/-- **Math.** The set-mass formula for `realDensityMeasure`. -/
theorem realDensityMeasure_apply
    (nu : Measure alpha) (rho : alpha -> ℝ) {s : Set alpha}
    (hs : MeasurableSet s) :
    realDensityMeasure nu rho s =
      ∫⁻ x in s, ENNReal.ofReal (rho x) ∂nu := by
  rw [realDensityMeasure, withDensity_apply _ hs]

/-- **Math.** A pointwise lower density bound integrates to a lower measure bound. -/
theorem realDensityMeasure_mul_le
    (nu : Measure alpha) {rho₀ rho₁ : alpha -> ℝ} {s : Set alpha} {C : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : Measurable rho₀)
    (hρ₁ : Measurable rho₁)
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, C * rho₀ x ≤ rho₁ x) :
    ENNReal.ofReal C * realDensityMeasure nu rho₀ s ≤
      realDensityMeasure nu rho₁ s := by
  rw [realDensityMeasure_apply nu rho₁ hs, realDensityMeasure_apply nu rho₀ hs]
  calc
    ENNReal.ofReal C * (∫⁻ x in s, ENNReal.ofReal (rho₀ x) ∂nu) =
        ∫⁻ x in s, ENNReal.ofReal C * ENNReal.ofReal (rho₀ x) ∂nu := by
      rw [lintegral_const_mul (μ := nu.restrict s) (ENNReal.ofReal C)]
      exact hρ₀.ennreal_ofReal
    _ = ∫⁻ x in s, ENNReal.ofReal (C * rho₀ x) ∂nu := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change ENNReal.ofReal C * ENNReal.ofReal (rho₀ x) =
        ENNReal.ofReal (C * rho₀ x)
      rw [ENNReal.ofReal_mul hC]
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (rho₁ x) ∂nu := by
      apply setLIntegral_mono_ae
      · exact (hρ₁.ennreal_ofReal).aemeasurable.restrict
      · exact Eventually.of_forall
          (fun x hx => ENNReal.ofReal_le_ofReal (hpoint x hx))

/-- **Math.** A pointwise upper density bound integrates to an upper measure bound. -/
theorem realDensityMeasure_le_mul
    (nu : Measure alpha) {rho₀ rho₁ : alpha -> ℝ} {s : Set alpha} {C : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : Measurable rho₀)
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, rho₁ x ≤ C * rho₀ x) :
    realDensityMeasure nu rho₁ s ≤
      ENNReal.ofReal C * realDensityMeasure nu rho₀ s := by
  rw [realDensityMeasure_apply nu rho₁ hs, realDensityMeasure_apply nu rho₀ hs]
  calc
    (∫⁻ x in s, ENNReal.ofReal (rho₁ x) ∂nu) ≤
        ∫⁻ x in s, ENNReal.ofReal (C * rho₀ x) ∂nu := by
      apply setLIntegral_mono_ae
      · exact ((hρ₀.const_mul C).ennreal_ofReal).aemeasurable.restrict
      · exact Eventually.of_forall
          (fun x hx => ENNReal.ofReal_le_ofReal (hpoint x hx))
    _ = ∫⁻ x in s, ENNReal.ofReal C * ENNReal.ofReal (rho₀ x) ∂nu := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change ENNReal.ofReal (C * rho₀ x) =
        ENNReal.ofReal C * ENNReal.ofReal (rho₀ x)
      rw [ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal C * (∫⁻ x in s, ENNReal.ofReal (rho₀ x) ∂nu) := by
      rw [← lintegral_const_mul (μ := nu.restrict s) (ENNReal.ofReal C)]
      exact hρ₀.ennreal_ofReal

/-! ### Setwise measurable-density variants

The canonical chart density is smooth only on the chart target; outside that
target its definition is deliberately an arbitrary extension.  The measure
comparison therefore needs only `AEMeasurable` on the measured set, rather
than a global measurability hypothesis. -/

/-- **Math.** A pointwise lower density bound integrates when both densities
are only almost-everywhere measurable on the measured set. -/
theorem realDensityMeasure_mul_le_of_aemeasurable
    (nu : Measure alpha) {rho₀ rho₁ : alpha -> ℝ} {s : Set alpha} {C : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : AEMeasurable rho₀ (nu.restrict s))
    (hρ₁ : AEMeasurable rho₁ (nu.restrict s))
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, C * rho₀ x ≤ rho₁ x) :
    ENNReal.ofReal C * realDensityMeasure nu rho₀ s ≤
      realDensityMeasure nu rho₁ s := by
  rw [realDensityMeasure_apply nu rho₁ hs, realDensityMeasure_apply nu rho₀ hs]
  calc
    ENNReal.ofReal C * (∫⁻ x in s, ENNReal.ofReal (rho₀ x) ∂nu) =
        ∫⁻ x in s, ENNReal.ofReal C * ENNReal.ofReal (rho₀ x) ∂nu := by
      rw [lintegral_const_mul'' (μ := nu.restrict s) (ENNReal.ofReal C)]
      exact hρ₀.ennreal_ofReal
    _ = ∫⁻ x in s, ENNReal.ofReal (C * rho₀ x) ∂nu := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change ENNReal.ofReal C * ENNReal.ofReal (rho₀ x) =
        ENNReal.ofReal (C * rho₀ x)
      rw [ENNReal.ofReal_mul hC]
    _ ≤ ∫⁻ x in s, ENNReal.ofReal (rho₁ x) ∂nu := by
      apply setLIntegral_mono_ae
      · exact hρ₁.ennreal_ofReal
      · exact Eventually.of_forall
          (fun x hx => ENNReal.ofReal_le_ofReal (hpoint x hx))

/-- **Math.** A pointwise upper density bound integrates when the reference
density is only almost-everywhere measurable on the measured set. -/
theorem realDensityMeasure_le_mul_of_aemeasurable
    (nu : Measure alpha) {rho₀ rho₁ : alpha -> ℝ} {s : Set alpha} {C : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : AEMeasurable rho₀ (nu.restrict s))
    (hC : 0 ≤ C)
    (hpoint : ∀ x ∈ s, rho₁ x ≤ C * rho₀ x) :
    realDensityMeasure nu rho₁ s ≤
      ENNReal.ofReal C * realDensityMeasure nu rho₀ s := by
  rw [realDensityMeasure_apply nu rho₁ hs, realDensityMeasure_apply nu rho₀ hs]
  calc
    (∫⁻ x in s, ENNReal.ofReal (rho₁ x) ∂nu) ≤
        ∫⁻ x in s, ENNReal.ofReal (C * rho₀ x) ∂nu := by
      apply setLIntegral_mono_ae
      · exact (hρ₀.const_mul C).ennreal_ofReal
      · exact Eventually.of_forall
          (fun x hx => ENNReal.ofReal_le_ofReal (hpoint x hx))
    _ = ∫⁻ x in s, ENNReal.ofReal C * ENNReal.ofReal (rho₀ x) ∂nu := by
      apply setLIntegral_congr_fun hs
      intro x hx
      change ENNReal.ofReal (C * rho₀ x) =
        ENNReal.ofReal C * ENNReal.ofReal (rho₀ x)
      rw [ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal C * (∫⁻ x in s, ENNReal.ofReal (rho₀ x) ∂nu) := by
      rw [← lintegral_const_mul'' (μ := nu.restrict s) (ENNReal.ofReal C)]
      exact hρ₀.ennreal_ofReal

/-- **Math.** A two-sided pointwise density comparison integrates under
setwise almost-everywhere measurability. -/
theorem realDensityMeasure_exp_comparison_of_aemeasurable
    (nu : Measure alpha) {rho₀ rho₁ : alpha -> ℝ} {s : Set alpha} {C t : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : AEMeasurable rho₀ (nu.restrict s))
    (hρ₁ : AEMeasurable rho₁ (nu.restrict s))
    (hpoint : ∀ x ∈ s,
      Real.exp (-C * t) * rho₀ x ≤ rho₁ x ∧
        rho₁ x ≤ Real.exp (C * t) * rho₀ x) :
    ENNReal.ofReal (Real.exp (-C * t)) * realDensityMeasure nu rho₀ s ≤
        realDensityMeasure nu rho₁ s ∧
      realDensityMeasure nu rho₁ s ≤
        ENNReal.ofReal (Real.exp (C * t)) * realDensityMeasure nu rho₀ s := by
  constructor
  · apply realDensityMeasure_mul_le_of_aemeasurable nu hs hρ₀ hρ₁
      (Real.exp_pos _).le
    intro x hx
    exact (hpoint x hx).1
  · apply realDensityMeasure_le_mul_of_aemeasurable nu hs hρ₀
      (Real.exp_pos _).le
    intro x hx
    exact (hpoint x hx).2

/-- **Math.** A two-sided pointwise comparison gives the corresponding comparison of
the induced measures on a measurable set. -/
theorem realDensityMeasure_exp_comparison
    (nu : Measure alpha) {rho₀ rho₁ : alpha -> ℝ} {s : Set alpha} {C t : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : Measurable rho₀)
    (hρ₁ : Measurable rho₁)
    (hpoint : ∀ x ∈ s,
      Real.exp (-C * t) * rho₀ x ≤ rho₁ x ∧
        rho₁ x ≤ Real.exp (C * t) * rho₀ x) :
    ENNReal.ofReal (Real.exp (-C * t)) * realDensityMeasure nu rho₀ s ≤
        realDensityMeasure nu rho₁ s ∧
      realDensityMeasure nu rho₁ s ≤
        ENNReal.ofReal (Real.exp (C * t)) * realDensityMeasure nu rho₀ s := by
  constructor
  · apply realDensityMeasure_mul_le nu hs hρ₀ hρ₁ (Real.exp_pos _).le
    intro x hx
    exact (hpoint x hx).1
  · apply realDensityMeasure_le_mul nu hs hρ₀ (Real.exp_pos _).le
    intro x hx
    exact (hpoint x hx).2

/-- **Math.** The time-dependent density evolution law used by the scalar volume
calculation, now with an explicit spatial parameter. -/
def IsRealDensityEvolutionOn (rho R : ℝ -> alpha -> ℝ) (J : Set ℝ) : Prop :=
  ∀ x, IsVolumeDensityEvolution (fun t => rho t x) (fun t => R t x) J

/-- **Math.** Integrate the scalar Ricci-flow density comparison on a measurable set.

The hypotheses expose the complete producer contract: pointwise evolution,
pointwise positivity, a uniform scalar bound, and measurability of the two time
slices.  Smooth geometric chart densities satisfy these hypotheses through
their existing regularity lemmas. -/
theorem realDensityMeasure_exp_comparison_of_isRealDensityEvolution
    (nu : Measure alpha) {rho R : ℝ -> alpha -> ℝ} {s : Set alpha}
    {C T t : ℝ}
    (hs : MeasurableSet s)
    (hρ₀ : Measurable (rho 0))
    (hρt : Measurable (rho t))
    (hevolution : IsRealDensityEvolutionOn rho R (Icc (0 : ℝ) T))
    (hbound : ∀ x, HasAbsoluteScalarBoundOn
      (fun u => R u x) (Icc (0 : ℝ) T) C)
    (hpositive : ∀ x, ∀ u ∈ Icc (0 : ℝ) T, 0 < rho u x)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ENNReal.ofReal (Real.exp (-C * t)) * realDensityMeasure nu (rho 0) s ≤
        realDensityMeasure nu (rho t) s ∧
      realDensityMeasure nu (rho t) s ≤
        ENNReal.ofReal (Real.exp (C * t)) * realDensityMeasure nu (rho 0) s := by
  apply realDensityMeasure_exp_comparison nu hs hρ₀ hρt
  intro x hx
  exact volumeDensity_exp_comparison
    (hevolution x) (hbound x) (hpositive x) ht

variable [TopologicalSpace alpha] [BorelSpace alpha]

/-- **Math.** The same adapter specialized to open sets, matching the volume statement in
Morgan--Tian's metric/volume distortion lemma. -/
theorem realDensityMeasure_exp_comparison_of_isOpen
    (nu : Measure alpha) {rho R : ℝ -> alpha -> ℝ} {U : Set alpha}
    {C T t : ℝ}
    (hU : IsOpen U)
    (hρ₀ : Measurable (rho 0))
    (hρt : Measurable (rho t))
    (hevolution : IsRealDensityEvolutionOn rho R (Icc (0 : ℝ) T))
    (hbound : ∀ x, HasAbsoluteScalarBoundOn
      (fun u => R u x) (Icc (0 : ℝ) T) C)
    (hpositive : ∀ x, ∀ u ∈ Icc (0 : ℝ) T, 0 < rho u x)
    (ht : t ∈ Icc (0 : ℝ) T) :
    ENNReal.ofReal (Real.exp (-C * t)) * realDensityMeasure nu (rho 0) U ≤
        realDensityMeasure nu (rho t) U ∧
      realDensityMeasure nu (rho t) U ≤
        ENNReal.ofReal (Real.exp (C * t)) * realDensityMeasure nu (rho 0) U := by
  exact realDensityMeasure_exp_comparison_of_isRealDensityEvolution
    nu hU.measurableSet hρ₀ hρt hevolution hbound hpositive ht

section CanonicalChartBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [Nonempty M] [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** On a set contained in one chart, pointwise comparison of two
coordinate volume densities induces the corresponding comparison of the
canonical Riemannian measures.  The chart formula from `RiemannianMeasure`
is used explicitly, so this adapter does not identify a local chart measure
with the global measure by definition. -/
theorem riemannianMeasure_chartDensity_comparison
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g₀ g₁ : RiemannianMetric I M} (alpha : M) {s : Set M}
    (hs : MeasurableSet s) (hsalpha : s ⊆ (extChartAt I alpha).source)
    {Cminus Cplus : ℝ} (hCminus : 0 ≤ Cminus) (hCplus : 0 ≤ Cplus)
    (hρ0 : Measurable
      (fun y : E => chartVolumeDensity (I := I) g₀ alpha y))
    (hρ₁ : Measurable
      (fun y : E => chartVolumeDensity (I := I) g₁ alpha y))
    (hpoint : ∀ y ∈ chartPreimage (I := I) alpha s,
      Cminus * chartVolumeDensity (I := I) g₀ alpha y ≤
          chartVolumeDensity (I := I) g₁ alpha y ∧
        chartVolumeDensity (I := I) g₁ alpha y ≤
          Cplus * chartVolumeDensity (I := I) g₀ alpha y) :
    ENNReal.ofReal Cminus * riemannianMeasure (I := I) g₀ mu s ≤
        riemannianMeasure (I := I) g₁ mu s ∧
      riemannianMeasure (I := I) g₁ mu s ≤
        ENNReal.ofReal Cplus * riemannianMeasure (I := I) g₀ mu s := by
  let q : Set E := chartPreimage (I := I) alpha s
  have hq : MeasurableSet q := measurableSet_chartPreimage (I := I) alpha hs
  have hzero : riemannianMeasure (I := I) g₀ mu s =
      realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := by
    rw [riemannianMeasure_apply_chart mu g₀ alpha hs hsalpha,
      realDensityMeasure_apply mu _ hq]
  have hone : riemannianMeasure (I := I) g₁ mu s =
      realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := by
    rw [riemannianMeasure_apply_chart mu g₁ alpha hs hsalpha,
      realDensityMeasure_apply mu _ hq]
  have hlow : ENNReal.ofReal Cminus *
        realDensityMeasure mu
          (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q ≤
      realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := by
    apply realDensityMeasure_mul_le mu hq hρ0 hρ₁ hCminus
    intro y hy
    exact (hpoint y hy).1
  have hupp : realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q ≤
      ENNReal.ofReal Cplus * realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := by
    apply realDensityMeasure_le_mul mu hq hρ0 hCplus
    intro y hy
    exact (hpoint y hy).2
  constructor
  · calc
      ENNReal.ofReal Cminus * riemannianMeasure (I := I) g₀ mu s =
          ENNReal.ofReal Cminus * realDensityMeasure mu
            (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := by
        rw [hzero]
      _ ≤ realDensityMeasure mu
          (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := hlow
      _ = riemannianMeasure (I := I) g₁ mu s := by
        rw [hone]
  · calc
      riemannianMeasure (I := I) g₁ mu s =
          realDensityMeasure mu
            (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := by
        rw [hone]
      _ ≤ ENNReal.ofReal Cplus * realDensityMeasure mu
          (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := hupp
      _ = ENNReal.ofReal Cplus * riemannianMeasure (I := I) g₀ mu s := by
        rw [hzero]

/-- **Math.** The chart-local canonical-measure form of the Ricci-flow
volume-density distortion estimate.  This is the direct composition of the
pointwise chart estimate with `riemannianMeasure_chartDensity_comparison`.
The measurable-set and chart-containment hypotheses are intentional: no
global atlas or partition argument is hidden in this contract. -/
theorem riemannianMeasure_chartDensity_exp_comparison_of_curvatureOperatorNormLeOnTime
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hK : 0 ≤ K) (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K)
    (alpha : M) {s : Set M}
    (hs : MeasurableSet s) (hsalpha : s ⊆ (extChartAt I alpha).source)
    {t : ℝ} (ht : t ∈ Icc 0 T)
    (hρ0 : Measurable
      (fun y : E => chartVolumeDensity (I := I) (g 0) alpha y))
    (hρt : Measurable
      (fun y : E => chartVolumeDensity (I := I) (g t) alpha y)) :
    ENNReal.ofReal
        (Real.exp (-((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t)) *
        riemannianMeasure (I := I) (g 0) mu s ≤
      riemannianMeasure (I := I) (g t) mu s ∧
    riemannianMeasure (I := I) (g t) mu s ≤
      ENNReal.ofReal
        (Real.exp (((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t)) *
        riemannianMeasure (I := I) (g 0) mu s := by
  let C : ℝ := (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E : ℝ) * K
  apply riemannianMeasure_chartDensity_comparison mu alpha hs hsalpha
    (Real.exp_pos _).le (Real.exp_pos _).le hρ0 hρt
  intro y hy
  exact chartVolumeDensity_exp_comparison_of_curvatureOperatorNormLeOnTime
    hK hflow hRm alpha (chartPreimage_subset_target (I := I) alpha s hy) ht

omit [SecondCountableTopology M] [Nonempty M] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** A smooth chart volume density is almost-everywhere measurable
on every measurable chart preimage.  This is the explicit geometric producer
used by the chart-local measure bridge; no global measurability of the
off-target extension is asserted. -/
theorem chartVolumeDensity_aemeasurable_on_chartPreimage
    (mu : Measure E) (g : RiemannianMetric I M) (alpha : M)
    {s : Set M} (hs : MeasurableSet s) :
    AEMeasurable
      (fun y : E => chartVolumeDensity (I := I) g alpha y)
      (mu.restrict (chartPreimage (I := I) alpha s)) := by
  let q : Set E := chartPreimage (I := I) alpha s
  have hq : MeasurableSet q := measurableSet_chartPreimage (I := I) alpha hs
  have hqt : q ⊆ (extChartAt I alpha).target := by
    intro y hy
    exact chartPreimage_subset_target (I := I) alpha s hy
  exact ((contDiffOn_chartVolumeDensity (I := I) g alpha).continuousOn.mono hqt).aemeasurable hq

omit [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** On a chart-contained measurable set, pointwise comparison of
coordinate volume densities induces canonical-measure comparison using the
setwise measurability supplied by `chartVolumeDensity_aemeasurable_on_chartPreimage`. -/
theorem riemannianMeasure_chartDensity_comparison_of_aemeasurable
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g₀ g₁ : RiemannianMetric I M} (alpha : M) {s : Set M}
    (hs : MeasurableSet s) (hsalpha : s ⊆ (extChartAt I alpha).source)
    {Cminus Cplus : ℝ} (hCminus : 0 ≤ Cminus) (hCplus : 0 ≤ Cplus)
    (hρ0 : AEMeasurable
      (fun y : E => chartVolumeDensity (I := I) g₀ alpha y)
      (mu.restrict (chartPreimage (I := I) alpha s)))
    (hρ₁ : AEMeasurable
      (fun y : E => chartVolumeDensity (I := I) g₁ alpha y)
      (mu.restrict (chartPreimage (I := I) alpha s)))
    (hpoint : ∀ y ∈ chartPreimage (I := I) alpha s,
      Cminus * chartVolumeDensity (I := I) g₀ alpha y ≤
          chartVolumeDensity (I := I) g₁ alpha y ∧
        chartVolumeDensity (I := I) g₁ alpha y ≤
          Cplus * chartVolumeDensity (I := I) g₀ alpha y) :
    ENNReal.ofReal Cminus * riemannianMeasure (I := I) g₀ mu s ≤
        riemannianMeasure (I := I) g₁ mu s ∧
      riemannianMeasure (I := I) g₁ mu s ≤
        ENNReal.ofReal Cplus * riemannianMeasure (I := I) g₀ mu s := by
  let q : Set E := chartPreimage (I := I) alpha s
  have hq : MeasurableSet q := measurableSet_chartPreimage (I := I) alpha hs
  have hzero : riemannianMeasure (I := I) g₀ mu s =
      realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := by
    rw [riemannianMeasure_apply_chart mu g₀ alpha hs hsalpha,
      realDensityMeasure_apply mu _ hq]
  have hone : riemannianMeasure (I := I) g₁ mu s =
      realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := by
    rw [riemannianMeasure_apply_chart mu g₁ alpha hs hsalpha,
      realDensityMeasure_apply mu _ hq]
  have hlow : ENNReal.ofReal Cminus *
        realDensityMeasure mu
          (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q ≤
      realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := by
    apply realDensityMeasure_mul_le_of_aemeasurable mu hq hρ0 hρ₁ hCminus
    intro y hy
    exact (hpoint y hy).1
  have hupp : realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q ≤
      ENNReal.ofReal Cplus * realDensityMeasure mu
        (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := by
    apply realDensityMeasure_le_mul_of_aemeasurable mu hq hρ0 hCplus
    intro y hy
    exact (hpoint y hy).2
  constructor
  · calc
      ENNReal.ofReal Cminus * riemannianMeasure (I := I) g₀ mu s =
          ENNReal.ofReal Cminus * realDensityMeasure mu
            (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := by
        rw [hzero]
      _ ≤ realDensityMeasure mu
          (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := hlow
      _ = riemannianMeasure (I := I) g₁ mu s := by
        rw [hone]
  · calc
      riemannianMeasure (I := I) g₁ mu s =
          realDensityMeasure mu
            (fun y : E => chartVolumeDensity (I := I) g₁ alpha y) q := by
        rw [hone]
      _ ≤ ENNReal.ofReal Cplus * realDensityMeasure mu
          (fun y : E => chartVolumeDensity (I := I) g₀ alpha y) q := hupp
      _ = ENNReal.ofReal Cplus * riemannianMeasure (I := I) g₀ mu s := by
        rw [hzero]

/-- **Math.** The chart-local Ricci-flow volume-distortion estimate with its
measurability hypotheses discharged by the smooth chart-density producer. -/
theorem riemannianMeasure_chartDensity_exp_comparison_of_curvatureOperatorNormLeOnTime_of_smooth
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hK : 0 ≤ K) (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K)
    (alpha : M) {s : Set M}
    (hs : MeasurableSet s) (hsalpha : s ⊆ (extChartAt I alpha).source)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    ENNReal.ofReal
        (Real.exp (-((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t)) *
        riemannianMeasure (I := I) (g 0) mu s ≤
      riemannianMeasure (I := I) (g t) mu s ∧
    riemannianMeasure (I := I) (g t) mu s ≤
      ENNReal.ofReal
        (Real.exp (((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t)) *
        riemannianMeasure (I := I) (g 0) mu s := by
  let C : ℝ := (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E : ℝ) * K
  apply riemannianMeasure_chartDensity_comparison_of_aemeasurable mu alpha hs hsalpha
    (Real.exp_pos _).le (Real.exp_pos _).le
    (chartVolumeDensity_aemeasurable_on_chartPreimage mu (g 0) alpha hs)
    (chartVolumeDensity_aemeasurable_on_chartPreimage mu (g t) alpha hs)
  intro y hy
  exact chartVolumeDensity_exp_comparison_of_curvatureOperatorNormLeOnTime
    hK hflow hRm alpha (chartPreimage_subset_target (I := I) alpha s hy) ht

end CanonicalChartBridge

#print axioms MorganTianLib.realDensityMeasure_apply
#print axioms MorganTianLib.realDensityMeasure_mul_le
#print axioms MorganTianLib.realDensityMeasure_le_mul
#print axioms MorganTianLib.realDensityMeasure_mul_le_of_aemeasurable
#print axioms MorganTianLib.realDensityMeasure_le_mul_of_aemeasurable
#print axioms MorganTianLib.realDensityMeasure_exp_comparison_of_aemeasurable
#print axioms MorganTianLib.realDensityMeasure_exp_comparison
#print axioms MorganTianLib.realDensityMeasure_exp_comparison_of_isRealDensityEvolution
#print axioms MorganTianLib.realDensityMeasure_exp_comparison_of_isOpen
#print axioms MorganTianLib.riemannianMeasure_chartDensity_comparison
#print axioms MorganTianLib.riemannianMeasure_chartDensity_exp_comparison_of_curvatureOperatorNormLeOnTime
#print axioms MorganTianLib.chartVolumeDensity_aemeasurable_on_chartPreimage
#print axioms MorganTianLib.riemannianMeasure_chartDensity_comparison_of_aemeasurable
#print axioms MorganTianLib.riemannianMeasure_chartDensity_exp_comparison_of_curvatureOperatorNormLeOnTime_of_smooth

end MorganTianLib

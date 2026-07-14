import PetersenLib.Ch05.MetricStructure
import PetersenLib.Ch01.ArcLength
import PetersenLib.Ch03.DistanceFunctions
import OpenGALib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# Petersen Ch. 5, §5.3 — distance functions and segments (Lemma 5.3.2)

If `r : U → ℝ` is a smooth distance function (`|∇r| ≡ 1`) on an open set
`U ⊆ M`, then along any curve staying in `U`,
`r(c(b)) − r(c(a)) ≤ L(c)`, with equality along integral curves of `∇r`.
Consequently the integral curves of `∇r` are length-minimising among curves in
`U` with the same endpoints — the *segments in `U`* of Petersen's
`lem:pet-ch5-distance-function-segments`.

The heart is the intrinsic pointwise Cauchy–Schwarz bound
`(r ∘ c)'(t) = dr(ċ) = g(∇r, ċ) ≤ |∇r|·|ċ| = |ċ|`
(the last step using `|∇r| = 1`), integrated by the fundamental theorem of
calculus.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless]

/-! ## The velocity of a curve as the chart-local derivative -/

/-- **Eng.** The chart-`γ t` representation `s ↦ φ_{γ t}(γ s)` of a curve has
`HasDerivAt` at `t` with value the intrinsic velocity `ċ(t) = mfderiv γ t 1`
(both read in `T_{γ t}M ≅ E`).  This bridges the chart-local velocity used by
`curveSpeedSq` to the `mfderiv` velocity used by `PetersenLib.velocity`. -/
theorem hasDerivAt_chartLocalCurve {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    HasDerivAt (Geodesic.chartLocalCurve (I := I) γ t) (velocity (I := I) γ t) t := by
  have hmf : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t (mfderiv 𝓘(ℝ, ℝ) I γ t) := hγ.hasMFDerivAt
  have h2 := hmf.2
  have hwrite : writtenInExtChartAt 𝓘(ℝ, ℝ) I t γ
      = Geodesic.chartLocalCurve (I := I) γ t := by
    funext s
    simp [writtenInExtChartAt, Geodesic.chartLocalCurve]
  have hpt : ((extChartAt 𝓘(ℝ, ℝ) t) t) = t := by
    simp
  have hrange : (range (𝓘(ℝ, ℝ) : ModelWithCorners ℝ ℝ ℝ)) = univ := by simp
  rw [hwrite, hpt, hrange] at h2
  have hfd : HasFDerivAt (Geodesic.chartLocalCurve (I := I) γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t) t := hasFDerivWithinAt_univ.mp h2
  simpa [velocity] using hfd.hasDerivAt

/-- **Eng.** The `curveSpeedSq` of `γ` at a point of differentiability is the
intrinsic squared norm of the `mfderiv` velocity: `|ċ|² = g(ċ, ċ)`.  This
identifies the Ch. 5 speed integrand with the Ch. 1 `arcLength` integrand. -/
theorem curveSpeedSq_eq_metricInner_velocity (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    curveSpeedSq (I := I) g γ t
      = g.metricInner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := by
  rw [curveSpeedSq_def, (hasDerivAt_chartLocalCurve hγ).deriv]
  rfl

/-! ## The pointwise Cauchy–Schwarz bound -/

/-- **Math.** Petersen Lemma 5.3.2 (pointwise identity): along a curve `γ`
through the domain of a smooth distance function `r`, the derivative of `r ∘ γ`
is the metric pairing of the radial field `∇r` with the velocity:
`(r ∘ γ)'(t) = dr(ċ) = g(∇r, ċ)`. -/
theorem hasDerivAt_distanceFunction_comp {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {γ : ℝ → M} {t : ℝ} (hmem : γ t ∈ U)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    HasDerivAt (fun s => r (γ s))
      (g.metricInner (γ t) (gradient g r (γ t)) (velocity (I := I) γ t)) t := by
  have hrmd : MDifferentiableAt I 𝓘(ℝ, ℝ) r (γ t) :=
    (hr.1.contMDiffAt (hU.mem_nhds hmem)).mdifferentiableAt (by norm_num)
  have hcomp : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (r ∘ γ) t := hrmd.comp t hγ
  have hdiff : DifferentiableAt ℝ (r ∘ γ) t := by
    rwa [mdifferentiableAt_iff_differentiableAt] at hcomp
  have hval : deriv (r ∘ γ) t
      = g.metricInner (γ t) (gradient g r (γ t)) (velocity (I := I) γ t) := by
    rw [← velocity_eq_deriv, velocity_comp t hrmd hγ, ← metricInner_gradient]
  have := hdiff.hasDerivAt
  rw [hval] at this
  exact this

/-- **Math.** Cauchy–Schwarz for the intrinsic metric on a tangent fibre:
`g(u, v) ≤ √(g(u,u))·√(g(v,v))`. -/
theorem metricInner_le_sqrt_mul_sqrt (g : RiemannianMetric I M) (x : M)
    (u v : TangentSpace I x) :
    g.metricInner x u v
      ≤ Real.sqrt (g.metricInner x u u) * Real.sqrt (g.metricInner x v v) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have h1 : g.metricInner x u v = @inner ℝ _ _ u v := rfl
  have h2 : g.metricInner x u u = @inner ℝ _ _ u u := rfl
  have h3 : g.metricInner x v v = @inner ℝ _ _ v v := rfl
  rw [h1, h2, h3, ← norm_eq_sqrt_real_inner u, ← norm_eq_sqrt_real_inner v]
  exact real_inner_le_norm u v

/-- **Math.** Petersen Lemma 5.3.2 (pointwise bound): along a curve `γ` through
the domain of a distance function `r`, the derivative of `r ∘ γ` is bounded by
the speed: `(r ∘ γ)'(t) = g(∇r, ċ) ≤ |∇r|·|ċ| = |ċ|`, the last step using the
eikonal equation `|∇r| = 1`. -/
theorem distanceFunction_deriv_le_speed {g : RiemannianMetric I M}
    {U : Set M} {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {γ : ℝ → M} {t : ℝ} (hmem : γ t ∈ U)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    g.metricInner (γ t) (gradient g r (γ t)) (velocity (I := I) γ t)
      ≤ Real.sqrt (curveSpeedSq (I := I) g γ t) := by
  have hcs := metricInner_le_sqrt_mul_sqrt g (γ t) (gradient g r (γ t)) (velocity (I := I) γ t)
  rw [hr.2 (γ t) hmem, Real.sqrt_one, one_mul,
    ← curveSpeedSq_eq_metricInner_velocity g hγ] at hcs
  exact hcs

/-! ## The core inequality of Lemma 5.3.2 -/

/-- **Eng.** The speed integrand `√|ċ|²` of a smooth curve is continuous. -/
theorem continuous_sqrt_curveSpeedSq (g : RiemannianMetric I M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) :
    Continuous (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) := by
  refine (continuous_sqrt_metricInner_velocity g hγ).congr (fun s => ?_)
  rw [curveSpeedSq_eq_metricInner_velocity g (hγ.mdifferentiableAt (by norm_num))]

/-- **Math.** Petersen **Lemma 5.3.2**, core inequality: if `r` is a smooth
distance function (`|∇r| = 1`) on an open set `U` and `γ` is a smooth curve
whose image over `[a, b]` lies in `U`, then
`r(γ(b)) − r(γ(a)) ≤ L(γ)|_a^b`.
Indeed `L(γ) = ∫|ċ| ≥ ∫ g(∇r, ċ) = ∫ (r∘γ)' = r(γ(b)) − r(γ(a))`. -/
theorem distanceFunction_curveLength_ge {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hmem : ∀ t ∈ Icc a b, γ t ∈ U) :
    r (γ b) - r (γ a) ≤ curveLength (I := I) g γ a b := by
  set D : ℝ → ℝ :=
    fun s => g.metricInner (γ s) (gradient g r (γ s)) (velocity (I := I) γ s) with hD
  have hderiv : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun s => r (γ s)) (D s) s := by
    intro s hs
    rw [Set.uIcc_of_le hab] at hs
    exact hasDerivAt_distanceFunction_comp hU hr (hmem s hs)
      (hγ.mdifferentiableAt (by norm_num))
  have hspeed_int :
      IntervalIntegrable (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) volume a b :=
    (continuous_sqrt_curveSpeedSq g hγ).intervalIntegrable a b
  have hD_int : IntervalIntegrable D volume a b := by
    have hV : IsOpen (γ ⁻¹' U) := hU.preimage hγ.continuous
    have hsub : Set.uIcc a b ⊆ γ ⁻¹' U := by
      rw [Set.uIcc_of_le hab]; exact fun s hs => hmem s hs
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => r (γ s)) (γ ⁻¹' U) :=
      hr.1.comp hγ.contMDiffOn (fun s hs => hs)
    have hcd : ContDiffOn ℝ ∞ (fun s => r (γ s)) (γ ⁻¹' U) := hcomp.contDiffOn
    have huniq : UniqueDiffOn ℝ (γ ⁻¹' U) := hV.uniqueDiffOn
    have hdw : ContinuousOn (derivWithin (fun s => r (γ s)) (γ ⁻¹' U)) (γ ⁻¹' U) :=
      hcd.continuousOn_derivWithin huniq (by norm_num)
    have hderivcont : ContinuousOn (deriv (fun s => r (γ s))) (γ ⁻¹' U) :=
      hdw.congr (fun s hs => (derivWithin_of_mem_nhds (hV.mem_nhds hs)).symm)
    have hDeq : Set.EqOn D (deriv (fun s => r (γ s))) (Set.uIcc a b) :=
      fun s hs => ((hderiv s hs).deriv).symm
    exact ((hderivcont.mono hsub).congr hDeq).intervalIntegrable
  have hFTC : ∫ s in a..b, D s = r (γ b) - r (γ a) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hD_int
    simpa using h
  have hpt : ∀ s ∈ Set.Icc a b, D s ≤ Real.sqrt (curveSpeedSq (I := I) g γ s) := by
    intro s hs
    exact distanceFunction_deriv_le_speed hr (hmem s hs) (hγ.mdifferentiableAt (by norm_num))
  rw [curveLength_def, ← hFTC]
  exact intervalIntegral.integral_mono_on hab hD_int hspeed_int hpt

/-! ## Integral curves of `∇r` are segments in `U` -/

/-- **Math.** Petersen **Lemma 5.3.2** (length identity): an integral curve `c`
of `∇r` in `U` (unit speed, since `|∇r| = 1`) has length equal to the potential
difference: `L(c)|_a^b = r(c(b)) − r(c(a)) = b − a`. -/
theorem distanceFunction_integralCurve_curveLength {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (hint : ∀ t ∈ Icc a b, velocity (I := I) c t = gradient g r (c t)) :
    curveLength (I := I) g c a b = r (c b) - r (c a) := by
  have hspeed : ∀ s ∈ Icc a b, curveSpeedSq (I := I) g c s = 1 := by
    intro s hs
    rw [curveSpeedSq_eq_metricInner_velocity g (hc.mdifferentiableAt (by norm_num)),
      hint s hs, hr.2 (c s) (hcU s hs)]
  have hlen : curveLength (I := I) g c a b = b - a := by
    rw [curveLength_def,
      intervalIntegral.integral_congr (g := fun _ => (1 : ℝ))
        (fun s hs => by
          rw [hspeed s (by rwa [uIcc_of_le hab] at hs), Real.sqrt_one])]
    simp
  have hDone : ∀ s ∈ uIcc a b, HasDerivAt (fun s => r (c s)) 1 s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    have h := hasDerivAt_distanceFunction_comp hU hr (hcU s hs)
      (hc.mdifferentiableAt (by norm_num))
    rwa [hint s hs, hr.2 (c s) (hcU s hs)] at h
  have hrdiff : r (c b) - r (c a) = b - a := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hDone
      (intervalIntegrable_const)
    simpa using h.symm
  rw [hlen, hrdiff]

/-- **Math.** Petersen **Lemma 5.3.2** (segments in `U`): an integral curve `c`
of `∇r` is a **segment in `U`** — it minimises length among curves staying in
`U` with the same endpoints. If `c'` is any smooth curve through `U` with
`c'(a') = c(a)`, `c'(b') = c(b)`, then `L(c)|_a^b ≤ L(c')|_{a'}^{b'}`.

(The full Lean `IsSegment` predicate measures length against the *global*
Riemannian distance, an infimum over all curves in `M`; an integral curve of
`∇r` need only minimise among curves *in `U`*, which is the content faithfully
captured here.  Cf. Example 5.3.4, where a long circular arc leaves the domain
and is no longer a global segment.) -/
theorem distanceFunction_integralCurvesAreSegments {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {a b : ℝ} (hab : a ≤ b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (hint : ∀ t ∈ Icc a b, velocity (I := I) c t = gradient g r (c t))
    {c' : ℝ → M} {a' b' : ℝ} (hab' : a' ≤ b') (hc' : ContMDiff 𝓘(ℝ, ℝ) I ∞ c')
    (hc'U : ∀ t ∈ Icc a' b', c' t ∈ U) (he0 : c' a' = c a) (he1 : c' b' = c b) :
    curveLength (I := I) g c a b ≤ curveLength (I := I) g c' a' b' := by
  have hA := distanceFunction_integralCurve_curveLength hU hr hab hc hcU hint
  have hcore := distanceFunction_curveLength_ge hU hr hab' hc' hc'U
  rw [hA, ← he1, ← he0]
  exact hcore

end PetersenLib

import DoCarmoLib.Riemannian.Geodesic.FlowReadback
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodInterior

set_option linter.unusedSectionVars false

/-!
# Length of a geodesic segment: metric payload for uniform-flow segments

do Carmo Ch. 3, §3–4. The totally-normal-neighborhood machinery
(`isGeodesicOn_uniform_flow_segment_Ioo`, `exists_totallyNormal_c1_diffeo`)
produces, for every base point `q` near `p` and every small chart velocity `w`,
an intrinsic geodesic segment `γ(s) = φ_p⁻¹((Z(φ_p q, T⁻¹ • w)(sT))₁)` joining
`q` to a nearby point — but with *no metric content*: neither its length nor
the distance it realizes is recorded anywhere in the totally-normal theorems.

This file supplies that missing payload. First a general primitive: a
continuous intrinsic geodesic on a connected open set of times has length equal
to its (constant) speed times the elapsed parameter,
`ℓ(γ|[a,b]) = √⟨γ',γ'⟩_g · (b−a)` (`IsGeodesicOn.pathELength_eq`) — the
metric-length reading of the constant-speed property `IsGeodesicOn.speedSq_eq`,
the equality underlying the Lipschitz bound `IsGeodesicOn.edist_le`.

Reading the speed in the fixed chart at `p` then gives, for the uniform-flow
segment, the closed form
`ℓ(γ|[0,1]) = √⟨w,w⟩_{G_p(y)}` (`pathELength_uniform_flow_segment_Ioo`),
uniformly in the base point `y = φ_p(q)`, and hence the radial *upper* bound
`d(q, γ 1) ≤ √⟨w,w⟩_{G_p(y)}` (`edist_uniform_flow_segment_le`).

This is the length half of do Carmo's Proposition 3.6, the metric input to the
minimizing clause of Proposition 4.2 (convex neighborhoods,
`prop:dc-ch3-4-2`). The *lower* bound `d(q, γ 1) = √⟨w,w⟩` — radial geodesics
realize the distance, uniformly in the center — remains the open crux,
requiring a base-uniform Gauss estimate not yet available.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section Length

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **A geodesic segment has length = speed × elapsed parameter.**
On a connected open set of times, a continuous intrinsic geodesic `γ` has
constant intrinsic speed `√⟨γ',γ'⟩_g` (do Carmo Ch. 3, the constant-speed
lemma `IsGeodesicOn.speedSq_eq`), so its `pathELength` over `[a,b]` is that
speed times `b − a`. This is the metric-length reading of the constant-speed
property, the equality underlying the Lipschitz bound `IsGeodesicOn.edist_le`. -/
theorem IsGeodesicOn.pathELength_eq
    {g : RiemannianMetric I M} {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsGeodesicOn (I := I) g γ s) (hs : IsOpen s)
    (hconn : IsPreconnected s) (hcont : ContinuousOn γ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I γ a b
      = ENNReal.ofReal (Real.sqrt (speedSq (I := I) g γ a) * (b - a)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hIcc : Icc a b ⊆ s := hconn.ordConnected.out ha hb
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hpt : ∀ τ ∈ Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ τ 1‖ₑ
      = ENNReal.ofReal (Real.sqrt (speedSq (I := I) g γ a)) := by
    intro τ hτ
    rw [enorm_tangent_eq_sqrt_metricInner (I := I) g (γ τ)]
    rw [show g.metricInner (γ τ) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1)
      = speedSq (I := I) g γ τ from rfl]
    rw [hγ.speedSq_eq hs hconn hcont (hIcc hτ) ha]
  rw [setLIntegral_congr_fun measurableSet_Icc hpt, setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

end Length

section FlowSegment

variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The uniform-flow geodesic segment has length `√⟨w,w⟩_{G_p(y)}`.**
For the rescaled chart-`p` spray segment `γ(s) = φ_p⁻¹((Z(y, T⁻¹ • w)(sT))₁)` of
`isGeodesicOn_uniform_flow_segment_Ioo` (do Carmo Ch. 3, the geodesic joining
`q = φ_p⁻¹(y)` to a nearby point), the `pathELength` over `[0,1]` equals the
chart-Gram norm of the initial velocity `w` read at the base `y`. This is the
metric payload that the totally-normal-neighborhood theorems otherwise omit:
the length identity is exactly the `≤` half of the normal-ball minimizing
property (Prop. 3.6), *uniform in the base point* `y`. -/
theorem pathELength_uniform_flow_segment_Ioo
    (g : RiemannianMetric I M) (p : M) {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 1
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y w w)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hγ0, hγcont, hγgeo, hγread, hγd0, hγdint⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := ⟨by linarith, hεT⟩
  have h1J : (1 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := by
    refine ⟨by linarith, ?_⟩
    rw [lt_div_iff₀ hT, one_mul]; exact hTε
  -- length via the constant-speed primitive
  rw [IsGeodesicOn.pathELength_eq hγgeo isOpen_Ioo isPreconnected_Ioo hγcont h0J h1J]
  -- the speed at `s = 0`, read in the chart at `p`
  have hcont0 : ContinuousAt
      (fun s : ℝ => (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 :=
    hγcont.continuousAt (isOpen_Ioo.mem_nhds h0J)
  have hspeed0 := Exponential.speedSq_eq_chartMetricInner_extChartAt (I := I) g hcont0
    (hγread 0 h0J).1 hγd0
  rw [hspeed0, (hγread 0 h0J).2, zero_mul, (hflow _ hmem).1, sub_zero, mul_one]

/-- **Math.** **The uniform-flow geodesic segment has arclength-proportional length.**
The same segment `γ(s) = φ_p⁻¹((Z(y, T⁻¹ • w)(sT))₁)`, restricted to `[0, t]` for any
`t ∈ [0, 1]`, has `pathELength` equal to `√⟨w,w⟩_{G_p(y)} · t` — the length grows linearly
in the elapsed parameter (constant speed). This is the arclength-proportional reading of the
minimizing `≤` payload, the input the distance-realization machinery
(`edist_segment_of_arclength`) consumes to certify that the *whole* joining geodesic, not just
its endpoints, realizes the distance proportionally. -/
theorem pathELength_uniform_flow_segment_Ioo_le_one
    (g : RiemannianMetric I M) (p : M) {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I (fun s : ℝ => (extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 t
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y w w) * t) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hγ0, hγcont, hγgeo, hγread, hγd0, hγdint⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have h1lt : (1 : ℝ) < ε / T := (one_lt_div hT).mpr hTε
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := ⟨by linarith, hεT⟩
  have htJ : t ∈ Ioo (-(ε / T)) (ε / T) :=
    ⟨by linarith [ht.1], lt_of_le_of_lt ht.2 h1lt⟩
  rw [IsGeodesicOn.pathELength_eq hγgeo isOpen_Ioo isPreconnected_Ioo hγcont h0J htJ]
  have hcont0 : ContinuousAt
      (fun s : ℝ => (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) 0 :=
    hγcont.continuousAt (isOpen_Ioo.mem_nhds h0J)
  have hspeed0 := Exponential.speedSq_eq_chartMetricInner_extChartAt (I := I) g hcont0
    (hγread 0 h0J).1 hγd0
  rw [hspeed0, (hγread 0 h0J).2, zero_mul, (hflow _ hmem).1, sub_zero]

/-- **Math.** **Uniform radial upper bound.** The distance from the base point
`q = φ_p⁻¹(y)` to the endpoint of the uniform-flow geodesic segment is at most
the chart-Gram norm of the initial velocity: `d(q, γ 1) ≤ √⟨w,w⟩_{G_p(y)}`,
uniformly in the base point `y`. This is the radial geodesic realizing an upper
bound on the distance (the `≤` of do Carmo Prop. 3.6, `edist` form). Requires the
standing hypothesis that the ambient distance is the Riemannian distance of `g`. -/
theorem edist_uniform_flow_segment_le
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {y w : E}
    (hmem : ((y, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    edist ((extChartAt I p).symm y)
        ((extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (1 * T)).1))
      ≤ ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y w w)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M := hg
  obtain ⟨hγ0, hγcont, hγgeo, hγread, hγd0, hγdint⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  have hεT : 0 < ε / T := div_pos (hT.trans hTε) hT
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := ⟨by linarith, hεT⟩
  have h1J : (1 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := by
    refine ⟨by linarith, ?_⟩
    rw [lt_div_iff₀ hT, one_mul]; exact hTε
  have hIcc : Icc (0 : ℝ) 1 ⊆ Ioo (-(ε / T)) (ε / T) :=
    (isPreconnected_Ioo.ordConnected).out h0J h1J
  have hC1 : ContMDiffOn 𝓘(ℝ, ℝ) I 1
      (fun s : ℝ => (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1)) (Icc 0 1) :=
    (hγgeo.contMDiffOn isOpen_Ioo hγcont).mono hIcc
  have hle := OpenGA.HopfRinow.edist_le_pathELength_of_cmdiff hC1 zero_le_one
  have hlen := pathELength_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  rw [hlen] at hle
  -- rewrite the (beta-reduced) starting point `φ_p⁻¹(Z(y,·)(0)) = φ_p⁻¹(y)`
  have hγ0' : (extChartAt I p).symm ((Z ((y, T⁻¹ • w) : E × E) ((0 : ℝ) * T)).1)
      = (extChartAt I p).symm y := hγ0
  rw [← hγ0']
  exact hle

end FlowSegment

end Geodesic
end Riemannian

end

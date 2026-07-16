import OpenGALib.Riemannian.Exponential.MovingBaseNormalBallEDist
import OpenGALib.Riemannian.Exponential.UniformSegmentLength

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# The base-uniform Proposition 3.6 lower bound (`Hlb`) — supporting lemmas (do Carmo Ch. 3, §4)

This file assembles the base-uniform lower-bound crux `Hlb` of `prop:dc-ch3-4-2`
(`exists_stronglyConvex_closedBall_of_lower_bound` in `ConvexNeighborhoodConvex.lean`): short
geodesics of small initial velocity near `p` realize the distance between their endpoints,
uniformly over the ball of centres.

The two clean supporting facts landed here are the *geometry-free* halves of the assembly:

* `movingBase_geodesic_pathELength_eq` — a geodesic `γ` on an open time window with initial chart-`p`
  velocity `w` has `pathELength(γ|[0,1]) = √⟨w,w⟩_{p,φ_p(γ 0)}` (constant speed), so the abstract
  length parameter `ℓ` of `Hlb` is forced to equal the chart-Gram length of `w`;
* `movingBase_geodesic_endpoint_eq_flow_reading` — such a `γ` (near the fixed base `p`, small `w`)
  reaches exactly the flow-reading endpoint `φ_p⁻¹((Z(φ_p(γ 0), T⁻¹ • w) T)₁)`, by intrinsic
  geodesic uniqueness on the asymmetric overlap window `(lo, hi) ∩ (-(ε/T), ε/T)` — this sidesteps
  the symmetric-window restriction of `IsGeodesicOn.eq_uniform_flow_readback`, so it applies to the
  raw `lo < 0 < 1 < hi` window that `exists_convex_join_ball` (and `Hlb`) provide.

The remaining crux is the base-uniform *competitor bound* (every curve to the flow endpoint is at
least as long as `√⟨w,w⟩_y`), which combines the moving-base core comparison
`exists_movingBase_pathELength_core_bound` with a moving-base escape estimate; that is developed
alongside.
-/

noncomputable section

open Bundle Manifold MeasureTheory Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal ENNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M')]

/-- **Math.** **Constant-speed length of a moving-base geodesic.** A continuous intrinsic geodesic
`γ` on an open preconnected time window `S ∋ 0, 1`, whose foot `γ 0` lies in the chart at `p` and
whose chart-`p` coordinate velocity at `0` is `w`, has `pathELength` over `[0,1]` equal to the
chart-Gram length `√⟨w,w⟩_{p,φ_p(γ 0)}` of that velocity. This is the constant-speed reading of the
geodesic (`IsGeodesicOn.pathELength_eq`) with the initial speed read in the fixed chart at `p`
(`speedSq_eq_chartMetricInner_extChartAt`). It forces the abstract length rate `ℓ` of `Hlb`
(defined by `pathELength(γ|[0,t]) = ofReal(ℓ·t)`) to be `√⟨w,w⟩_y`. -/
theorem movingBase_geodesic_pathELength_eq
    (g : RiemannianMetric I M') (p : M') {γ : ℝ → M'} {S : Set ℝ} {w : E}
    (hgeo : IsGeodesicOn (I := I) g γ S) (hSopen : IsOpen S) (hSconn : IsPreconnected S)
    (hcont : ContinuousOn γ S) (h0S : (0 : ℝ) ∈ S) (h1S : (1 : ℝ) ∈ S)
    (hsrc : γ 0 ∈ (chartAt H p).source)
    (hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Manifold.pathELength I γ 0 1
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p (γ 0)) w w)) := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [IsGeodesicOn.pathELength_eq hgeo hSopen hSconn hcont h0S h1S]
  have hcont0 : ContinuousAt γ 0 := hcont.continuousAt (hSopen.mem_nhds h0S)
  have hspeed0 := speedSq_eq_chartMetricInner_extChartAt (I := I) g hcont0 hsrc hvel
  rw [hspeed0, sub_zero, mul_one]

/-- **Math.** **A short moving-base geodesic reaches the flow-reading endpoint.** Let `Z` be a
uniform local flow of the chart-`p` geodesic spray on the closed `rF`-ball around the zero section
(the flow of `exists_totallyNormal_c1_diffeo`). A continuous intrinsic geodesic `γ` on an open
window `(lo, hi) ⊋ [0,1]` starting at `q₁` (near `p`) with initial chart-`p` velocity `w` small
enough that `(φ_p q₁, T⁻¹ • w)` lies in the flow ball, coincides with the rescaled flow line
`s ↦ φ_p⁻¹((Z(φ_p q₁, T⁻¹ • w)(sT))₁)` on the overlap window, hence
`γ 1 = φ_p⁻¹((Z(φ_p q₁, T⁻¹ • w) T)₁)`.

The identification is by intrinsic geodesic uniqueness (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`)
on the *asymmetric* open overlap `(lo, hi) ∩ (-(εF/T), εF/T)` — which contains `[0,1]` because
`hi > 1` and `εF/T > 1` — avoiding the symmetric window `(-a, a)` that
`IsGeodesicOn.eq_uniform_flow_readback` requires. -/
theorem movingBase_geodesic_endpoint_eq_flow_reading
    (g : RiemannianMetric I M') (p : M') {lo hi T rF εF : ℝ} {Z : E × E → ℝ → E × E}
    {γ : ℝ → M'} {q₁ : M'} {w : E}
    (hTpos : 0 < T) (hTεF : T < εF)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) rF,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-εF) εF, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-εF) εF) t) ∧
      (∀ t ∈ Icc (-εF) εF, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    (hmem : ((extChartAt I p q₁, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) rF)
    (hlo : lo < 0) (hhi : 1 < hi)
    (hgeo : IsGeodesicOn (I := I) g γ (Ioo lo hi)) (hcont : ContinuousOn γ (Ioo lo hi))
    (hγ0 : γ 0 = q₁) (hqsrc : q₁ ∈ (chartAt H p).source)
    (hvel : HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0) :
    γ 1 = (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) T).1) := by
  classical
  set y : E := extChartAt I p q₁ with hydef
  set gw : ℝ → M' := fun s : ℝ => (extChartAt I p).symm
    ((Z ((y, T⁻¹ • w) : E × E) (s * T)).1) with hgwdef
  obtain ⟨hgw0, hgwcont, hgwgeo, hgwread, hgwd0, hgwdint⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hTpos hTεF hflow hmem
  have hεT : 0 < εF / T := div_pos (hTpos.trans hTεF) hTpos
  have h1lt : (1 : ℝ) < εF / T := (one_lt_div hTpos).mpr hTεF
  -- the asymmetric overlap window
  set S : Set ℝ := Ioo (max lo (-(εF / T))) (min hi (εF / T)) with hSdef
  have hloneg : max lo (-(εF / T)) < 0 := max_lt hlo (by linarith)
  have hhipos : (0 : ℝ) < min hi (εF / T) := lt_min (by linarith) hεT
  have h1max : max lo (-(εF / T)) < 1 := lt_trans hloneg one_pos
  have h1min : (1 : ℝ) < min hi (εF / T) := lt_min hhi h1lt
  have h0S : (0 : ℝ) ∈ S := ⟨hloneg, hhipos⟩
  have h1S : (1 : ℝ) ∈ S := ⟨h1max, h1min⟩
  have hS_lo : S ⊆ Ioo lo hi :=
    Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)
  have hS_J : S ⊆ Ioo (-(εF / T)) (εF / T) :=
    Ioo_subset_Ioo (le_max_right _ _) (min_le_right _ _)
  -- both curves are geodesic and continuous on `S`
  have hγS : IsGeodesicOn (I := I) g γ S := hgeo.mono hS_lo
  have hgwS : IsGeodesicOn (I := I) g gw S := hgwgeo.mono hS_J
  have hγcS : ContinuousOn γ S := hcont.mono hS_lo
  have hgwcS : ContinuousOn gw S := hgwcont.mono hS_J
  -- position match at `0`: `γ 0 = q₁ = φ_p⁻¹(y) = gw 0`
  have hγ0src : γ 0 ∈ (chartAt H p).source := by rw [hγ0]; exact hqsrc
  have hstart : gw 0 = q₁ := by
    have : gw 0 = (extChartAt I p).symm y := hgw0
    rw [this, hydef, (extChartAt I p).left_inv (by rw [extChartAt_source]; exact hqsrc)]
  have heq0 : γ 0 = gw 0 := by rw [hγ0, hstart]
  -- chart-`p` velocity match at `0`: both `w`
  have hvγ : deriv (chartReading (I := I) p γ) 0 = w := hvel.deriv
  have hvgw : deriv (chartReading (I := I) p gw) 0 = w := hgwd0.deriv
  -- uniqueness on the asymmetric open preconnected window
  have hEq : Set.EqOn γ gw S :=
    IsGeodesicOn.eqOn_of_deriv_chartReading_eq isOpen_Ioo isPreconnected_Ioo
      hγS hgwS hγcS hgwcS h0S heq0 hγ0src (hvγ.trans hvgw.symm)
  have h1eq : γ 1 = gw 1 := hEq h1S
  rw [h1eq, hgwdef]
  simp only [one_mul]

/-- **Math.** **The base-uniform competitor bound** (do Carmo Ch. 3, Prop. 3.6, base-uniform, both
the core comparison and its escape case). For every `p` there are radii `β, ρ' > 0`, a time scale
`T`, a geodesic-spray flow `Z` on the closed `rF`-ball around the zero section, such that
`closedBall p β ⊆ (chartAt H p).source`, and for every base point `q ∈ closedBall p β` and every
chart-`p` velocity `w` with `‖w‖ < ρ'`, **every** `C¹` curve `σ` from `q` to the flow-reading
endpoint `φ_p⁻¹((Z(φ_p q, T⁻¹ • w) T)₁)` has `pathELength` over `[0,1]` at least the chart-Gram
length `√⟨w,w⟩_{p,φ_p q}` of `w`. This is do Carmo's Proposition 3.6 (radial geodesics realize the
distance) stated over the whole ball of centres `q` at once — the analytic heart of the lower-bound
crux `Hlb` of `prop:dc-ch3-4-2`.

The proof combines, uniformly in `q`, the Gauss radius comparison of
`exists_movingBase_pathELength_core_bound` for curves confined to the closed `r'`-region (the polar
lift is controlled by the transported radial lower bound `movingBase_flow_reading_radial_lower_bound`)
with the escape estimate: a curve leaving the region crosses the coordinate `r'`-sphere at a
first-exit time, where the confined comparison plus the coordinate-norm bound
`exists_sq_norm_le_chartMetricInner` already forces length `≥ r'/√c > √⟨w,w⟩_y` (the last strict
inequality is the base-uniform smallness `exists_forall_chartMetricInner_self_lt_uniform`). -/
theorem exists_movingBase_competitor_le_pathELength
    (g : RiemannianMetric I M') (p : M') :
    ∃ (β ρ' T : ℝ) (Z : E × E → ℝ → E × E) (rF εF : ℝ),
      0 < β ∧ 0 < ρ' ∧ 0 < T ∧ 0 < rF ∧ 0 < εF ∧ T < εF ∧
      closedBall p β ⊆ (chartAt H p).source ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) rF,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-εF) εF, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-εF) εF) t) ∧
        (∀ t ∈ Icc (-εF) εF, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∀ q ∈ closedBall p β, ∀ w : E, ‖w‖ < ρ' →
        ((extChartAt I p q, T⁻¹ • w) : E × E) ∈
          closedBall ((extChartAt I p p, (0 : E)) : E × E) rF) ∧
      (∀ q ∈ closedBall p β, ∀ w : E, ‖w‖ < ρ' →
        ∀ (σ : ℝ → M'), ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ (Icc 0 1) → σ 0 = q →
          σ 1 = (extChartAt I p).symm ((Z ((extChartAt I p q, T⁻¹ • w) : E × E) T).1) →
          (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) :=
            ⟨g.toRiemannianMetric⟩
           ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q) w w))
             ≤ Manifold.pathELength I σ 0 1)) := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨W, δ, δ₁, T, Z, Ginv, hWopen, hpW, hWsub, hδpos, hδ₁pos, hTpos, hWchart,
    hmemW, hcover, hGC1, hGinj, hGopen, hGleft, hGright, hGinvC1, hrange, hdiag,
    rF, εF, hrF, hεF, hTεF, hflow⟩ := exists_totallyNormal_c1_diffeo (I := I) g p
  set y₀ : E := extChartAt I p p with hy₀def
  obtain ⟨ηR, ρR, hηRpos, hρRpos, Hradial⟩ :=
    movingBase_flow_reading_radial_lower_bound (I := I) g p hTpos hTεF hrF hflow
  obtain ⟨c, Vc, hcpos, hVc, hVctgt, hgramV⟩ :=
    Geodesic.exists_sq_norm_le_chartMetricInner (I := I) g p
  -- working radii
  set ρ : ℝ := min ρR δ with hρdef
  have hρpos : 0 < ρ := lt_min hρRpos hδpos
  set r' : ℝ := ρ / 2 with hr'def
  have hr'pos : 0 < r' := by positivity
  have hr'ρ : r' < ρ := by rw [hr'def]; linarith
  have hr'ρR : r' < ρR := lt_of_lt_of_le hr'ρ (min_le_left _ _)
  have hr'δ : r' < δ := lt_of_lt_of_le hr'ρ (min_le_right _ _)
  have hsqcpos : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
  -- base-uniform smallness of the Gram form (escape needs `√⟨w,w⟩_y < r'/√c`)
  obtain ⟨ηU, εU, hηUpos, hεUpos, hupper⟩ :=
    exists_forall_chartMetricInner_self_lt_uniform (I := I) g p
      (θ := (r' / Real.sqrt c) ^ 2) (by positivity)
  -- a coordinate ball inside the Gram neighbourhood `Vc`
  obtain ⟨rV, hrVpos, hrVsub⟩ := Metric.mem_nhds_iff.mp hVc
  -- the base-neighbourhood radius, forcing `y = φ_p q` into all the constraint balls
  set ηy : ℝ := min (min (min ηR δ₁) rF) (min ηU rV) with hηydef
  have hηy_ηR : ηy ≤ ηR := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hηy_δ₁ : ηy ≤ δ₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hηy_rF : ηy ≤ rF := le_trans (min_le_left _ _) (min_le_right _ _)
  have hηy_ηU : ηy ≤ ηU := le_trans (min_le_right _ _) (min_le_left _ _)
  have hηy_rV : ηy ≤ rV := le_trans (min_le_right _ _) (min_le_right _ _)
  have hηypos : 0 < ηy :=
    lt_min (lt_min (lt_min hηRpos hδ₁pos) hrF) (lt_min hηUpos hrVpos)
  have hnhd : extChartAt I p ⁻¹' ball y₀ ηy ∩ W ∈ 𝓝 p := by
    refine inter_mem ?_ (hWopen.mem_nhds hpW)
    exact (continuousAt_extChartAt (I := I) p).preimage_mem_nhds
      (isOpen_ball.mem_nhds (by rw [hy₀def]; exact mem_ball_self hηypos))
  obtain ⟨β, hβpos, hβsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnhd
  -- the velocity radius: fits the region, the smallness box, and the flow ball
  set ρ' : ℝ := min (min r' εU) (T * rF) with hρ'def
  have hρ'pos : 0 < ρ' := lt_min (lt_min hr'pos hεUpos) (by positivity)
  have hρ'r' : ρ' ≤ r' := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ'εU : ρ' ≤ εU := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ'box : ρ' ≤ T * rF := min_le_right _ _
  have hβsrc : closedBall p β ⊆ (chartAt H p).source := fun q hq => hWsub (hβsub hq).2
  refine ⟨β, ρ', T, Z, rF, εF, hβpos, hρ'pos, hTpos, hrF, hεF, hTεF, hβsrc, hflow, ?_, ?_⟩
  · -- `hbox`: the initial condition lies in the flow ball
    intro q hq w hw
    have hqmem : q ∈ extChartAt I p ⁻¹' ball y₀ ηy ∩ W := hβsub hq
    have hydist : dist (extChartAt I p q) y₀ < ηy := mem_ball.mp hqmem.1
    rw [mem_closedBall, Prod.dist_eq]
    refine max_le (le_trans hydist.le hηy_rF) ?_
    rw [dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg hTpos.le,
      inv_mul_le_iff₀ hTpos]
    exact le_trans hw.le hρ'box
  -- `hcompete`: the competitor bound
  intro q hq w hw σ hσ hσ0 hσ1
  set y : E := extChartAt I p q with hydef
  have hqmem : q ∈ extChartAt I p ⁻¹' ball y₀ ηy ∩ W := hβsub hq
  have hqW : q ∈ W := hqmem.2
  have hydist : dist y y₀ < ηy := mem_ball.mp hqmem.1
  have hyηR : dist y y₀ < ηR := lt_of_lt_of_le hydist hηy_ηR
  have hyδ₁ : y ∈ ball y₀ δ₁ := mem_ball.mpr (lt_of_lt_of_le hydist hηy_δ₁)
  have hyrF : dist y y₀ < rF := lt_of_lt_of_le hydist hηy_rF
  have hyηU : dist y y₀ < ηU := lt_of_lt_of_le hydist hηy_ηU
  have hyVc : y ∈ Vc := hrVsub (mem_ball.mpr (lt_of_lt_of_le hydist hηy_rV))
  have hqsrcE : q ∈ (extChartAt I p).source := by rw [extChartAt_source]; exact hWsub hqW
  have hytgt : y ∈ (extChartAt I p).target := (extChartAt I p).map_source hqsrcE
  set G : E × E → E × E := fun x => ((x.1 : E), (Z ((x.1, T⁻¹ • x.2) : E × E) T).1) with hGdef
  set f : E → E := fun w => (Z ((y, T⁻¹ • w) : E × E) T).1 with hfdef
  set finv : E → E := fun z => (Ginv ((y, z) : E × E)).2 with hfinvdef
  -- ## per-`q` region data (mirrors `exists_movingBase_pathELength_core_bound`)
  have hregion : ∀ z : E, ‖z‖ < δ → f z ∈ (extChartAt I p).target := by
    intro z hzδ
    obtain ⟨γz, -, -, -, -, hγzsrc, -, -⟩ := hmemW q hqW z hzδ
    obtain ⟨hγz1src, hγz1read⟩ := hγzsrc 1 (right_mem_Icc.mpr zero_le_one)
    rw [one_mul] at hγz1read
    show (Z ((y, T⁻¹ • z) : E × E) T).1 ∈ (extChartAt I p).target
    rw [← hγz1read]
    exact (extChartAt I p).map_source (by rw [extChartAt_source]; exact hγz1src)
  have hf0 : f 0 = y := by
    have hmem0 : ((y, (0 : E)) : E × E) ∈ closedBall ((y₀, (0 : E)) : E × E) rF := by
      rw [mem_closedBall, Prod.dist_eq]
      exact max_le hyrF.le (by rw [dist_self]; exact hrF.le)
    have hequil := geodesicFlow_eqOn_of_zero_velocity (I := I) g p hεF hflow hmem0
    have hZ0 := hequil T ⟨by linarith [hεF, hTpos], hTεF⟩
    show (Z ((y, T⁻¹ • (0 : E)) : E × E) T).1 = y
    rw [smul_zero, hZ0]
  have hGyleft : ∀ v : E, ‖v‖ < δ → Ginv ((y, f v) : E × E) = ((y, v) : E × E) := by
    intro v hv'
    have h := hGleft ((y, v) : E × E) ⟨hyδ₁, mem_ball_zero_iff.mpr hv'⟩
    simpa [hGdef] using h
  have hfopen : IsOpen (f '' ball (0 : E) δ) := by
    have hset : f '' ball (0 : E) δ
        = (fun z : E => ((y, z) : E × E)) ⁻¹'
            (G '' (ball y₀ δ₁ ×ˢ ball (0 : E) δ)) := by
      ext z
      constructor
      · rintro ⟨v, hv', rfl⟩
        exact ⟨(y, v), ⟨hyδ₁, hv'⟩, rfl⟩
      · rintro ⟨x, hx, hxz⟩
        have hx1 : x.1 = y := congrArg Prod.fst hxz
        refine ⟨x.2, hx.2, ?_⟩
        have hx2 : (G x).2 = z := congrArg Prod.snd hxz
        rw [hfdef]; simp only
        rw [← hx1]; exact hx2
    rw [hset]
    exact hGopen.preimage (continuous_const.prodMk continuous_id)
  have hf_C1 : ContDiffOn ℝ 1 f (ball (0 : E) δ) := by
    have hincl : ContDiff ℝ 1 (fun v : E => ((y, v) : E × E)) :=
      contDiff_const.prodMk contDiff_id
    have hmaps : MapsTo (fun v : E => ((y, v) : E × E)) (ball (0 : E) δ)
        (ball y₀ δ₁ ×ˢ ball (0 : E) δ) := fun v hv' => ⟨hyδ₁, hv'⟩
    have hGcomp : ContDiffOn ℝ 1 (fun v : E => G ((y, v) : E × E)) (ball (0 : E) δ) :=
      hGC1.comp hincl.contDiffOn hmaps
    exact (ContinuousLinearMap.snd ℝ E E).contDiff.comp_contDiffOn hGcomp
  have hfinvC1 : ContDiffOn ℝ 1 finv (f '' ball (0 : E) δ) := by
    have hincl : ContDiff ℝ 1 (fun z : E => ((y, z) : E × E)) :=
      contDiff_const.prodMk contDiff_id
    have hmaps : MapsTo (fun z : E => ((y, z) : E × E)) (f '' ball (0 : E) δ)
        (G '' (ball y₀ δ₁ ×ˢ ball (0 : E) δ)) := by
      rintro z ⟨v, hv', rfl⟩
      exact ⟨(y, v), ⟨hyδ₁, hv'⟩, rfl⟩
    have hGinvcomp : ContDiffOn ℝ 1 (fun z : E => Ginv ((y, z) : E × E))
        (f '' ball (0 : E) δ) := hGinvC1.comp hincl.contDiffOn hmaps
    exact (ContinuousLinearMap.snd ℝ E E).contDiff.comp_contDiffOn hGinvcomp
  have hfinv_fderiv_cont : ContinuousOn (fderiv ℝ finv) (f '' ball (0 : E) δ) :=
    hfinvC1.continuousOn_fderiv_of_isOpen hfopen le_rfl
  have hradial : ∀ v ξ : E, ‖v‖ < ρ →
      chartMetricInner (I := I) g p y v ξ ^ 2
        ≤ chartMetricInner (I := I) g p y v v
          * chartMetricInner (I := I) g p (f v) (fderiv ℝ f v ξ) (fderiv ℝ f v ξ) :=
    fun v ξ hv' => Hradial y hyηR hytgt v ξ (lt_of_lt_of_le hv' (min_le_left _ _))
  have htgt_ρ : ∀ u : E, ‖u‖ < ρ → f u ∈ (extChartAt I p).target :=
    fun u hu => hregion u (lt_of_lt_of_le hu (min_le_right _ _))
  have hf_C1_ρ : ContDiffOn ℝ 1 f (ball (0 : E) ρ) :=
    hf_C1.mono (ball_subset_ball (min_le_right _ _))
  -- the polar radius: `f` shrinks nothing radially, so confined curves are long
  have hcore_q : ∀ (σ' : ℝ → M') (τ : ℝ), 0 < τ → τ ≤ 1 →
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 σ' (Icc 0 1) → σ' 0 = q →
      (∀ t ∈ Icc (0 : ℝ) τ, ∃ z : E, ‖z‖ ≤ r' ∧
        σ' t = (extChartAt I p).symm ((Z ((y, T⁻¹ • z) : E × E) T).1)) →
      ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y
          ((Ginv ((y, extChartAt I p (σ' τ)) : E × E)).2)
          ((Ginv ((y, extChartAt I p (σ' τ)) : E × E)).2)))
        ≤ Manifold.pathELength I σ' 0 τ := by
    intro σ' τ hτ0 hτ1 hσ' hσ'0 hstay
    have hsub : Icc (0 : ℝ) τ ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc le_rfl hτ1
    have hsrcσ : ∀ t ∈ Icc (0 : ℝ) τ, σ' t ∈ (chartAt H p).source := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      rw [hσt]
      have hfztgt : f z ∈ (extChartAt I p).target := hregion z (lt_of_le_of_lt hz hr'δ)
      have h := (extChartAt I p).map_target hfztgt
      rwa [extChartAt_source] at h
    set u : ℝ → E := fun s => extChartAt I p (σ' s) with hudef
    set u' : ℝ → E := derivWithin u (Icc 0 τ) with hu'def
    have huC1 : ContDiffOn ℝ 1 u (Icc 0 τ) :=
      contDiffOn_extChartAt_comp (hσ'.mono hsub) hsrcσ
    have hu'cont : ContinuousOn u' (Icc 0 τ) :=
      huC1.continuousOn_derivWithin (uniqueDiffOn_Icc hτ0) le_rfl
    have hu'deriv : ∀ t ∈ Ioo (0 : ℝ) τ, HasDerivAt u (u' t) t := fun t ht =>
      ((huC1.differentiableOn one_ne_zero t (Ioo_subset_Icc_self ht)).hasDerivWithinAt).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    set wlift : ℝ → E := fun s => finv (u s) with hwliftdef
    have hwz : ∀ t ∈ Icc (0 : ℝ) τ, ‖wlift t‖ ≤ r' ∧ f (wlift t) = u t := by
      intro t ht
      obtain ⟨z, hz, hσt⟩ := hstay t ht
      have hzδ : ‖z‖ < δ := lt_of_le_of_lt hz hr'δ
      have hfztgt : f z ∈ (extChartAt I p).target := hregion z hzδ
      have hut : u t = f z := by
        rw [hudef]; simp only; rw [hσt, (extChartAt I p).right_inv hfztgt]
      have hwt : wlift t = z := by
        rw [hwliftdef]; simp only; rw [hut, hfinvdef]; simp only
        rw [hGyleft z hzδ]
      rw [hwt]; exact ⟨hz, by rw [← hut]⟩
    have humem : ∀ t ∈ Icc (0 : ℝ) τ, u t ∈ f '' ball (0 : E) δ := fun t ht =>
      ⟨wlift t, mem_ball_zero_iff.mpr ((hwz t ht).1.trans_lt hr'δ), (hwz t ht).2⟩
    have hw_cont : ContinuousOn wlift (Icc 0 τ) :=
      hfinvC1.continuousOn.comp huC1.continuousOn humem
    have hw_deriv : ∀ t ∈ Ioo (0 : ℝ) τ, HasDerivAt wlift (fderiv ℝ finv (u t) (u' t)) t := by
      intro t ht
      have hfinv_at : HasFDerivAt finv (fderiv ℝ finv (u t)) (u t) :=
        ((hfinvC1.contDiffAt (hfopen.mem_nhds (humem t (Ioo_subset_Icc_self ht)))).differentiableAt
          one_ne_zero).hasFDerivAt
      simpa [Function.comp_def] using hfinv_at.comp_hasDerivAt t (hu'deriv t ht)
    have hw'_cont : ContinuousOn (fun t => fderiv ℝ finv (u t) (u' t)) (Icc 0 τ) :=
      (hfinv_fderiv_cont.comp huC1.continuousOn humem).clm_apply hu'cont
    have hwball : ∀ t ∈ Icc (0 : ℝ) τ, ‖wlift t‖ < ρ :=
      fun t ht => (hwz t ht).1.trans_lt hr'ρ
    have hcompare := gauss_radius_reach_at (I := I) g p f y hytgt htgt_ρ hf_C1_ρ hradial
      (w := wlift) (w' := fun t => fderiv ℝ finv (u t) (u' t)) hw_cont
      (fun t ht => hw_deriv t ht) hw'_cont hwball (t₁ := τ) ⟨hτ0.le, le_rfl⟩
    have hw0 : wlift 0 = 0 := by
      have hu0 : u 0 = y := by rw [hudef]; simp only; rw [hσ'0]
      rw [hwliftdef]; simp only; rw [hu0, hfinvdef]; simp only
      have hGy0 : Ginv ((y, f 0) : E × E) = ((y, (0 : E)) : E × E) :=
        hGyleft 0 (by rw [norm_zero]; exact hδpos)
      rw [hf0] at hGy0
      rw [hGy0]
    rw [hw0, chartMetricInner_zero_left, Real.sqrt_zero, sub_zero] at hcompare
    have hcongr : (∫ t in (0 : ℝ)..τ, Real.sqrt (chartMetricInner (I := I) g p
          (f (wlift t)) (fderiv ℝ f (wlift t) (fderiv ℝ finv (u t) (u' t)))
          (fderiv ℝ f (wlift t) (fderiv ℝ finv (u t) (u' t)))))
        = ∫ t in (0 : ℝ)..τ, Real.sqrt (chartMetricInner (I := I) g p
            (u t) (u' t) (u' t)) := by
      rw [intervalIntegral.integral_of_le hτ0.le, intervalIntegral.integral_of_le hτ0.le,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
      have htIcc : t ∈ Icc (0 : ℝ) τ := Ioo_subset_Icc_self ht
      have hf_at : HasFDerivAt f (fderiv ℝ f (wlift t)) (wlift t) :=
        ((hf_C1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr
          ((hwz t htIcc).1.trans_lt hr'δ)))).differentiableAt one_ne_zero).hasFDerivAt
      have hfw : HasDerivAt (fun s => f (wlift s))
          (fderiv ℝ f (wlift t) (fderiv ℝ finv (u t) (u' t))) t := by
        simpa [Function.comp_def] using hf_at.comp_hasDerivAt t (hw_deriv t ht)
      have hfw_u : HasDerivAt u (fderiv ℝ f (wlift t) (fderiv ℝ finv (u t) (u' t))) t := by
        refine hfw.congr_of_eventuallyEq ?_
        filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs
        exact ((hwz s hs).2).symm
      have hfd : fderiv ℝ f (wlift t) (fderiv ℝ finv (u t) (u' t)) = u' t :=
        hfw_u.unique (hu'deriv t ht)
      rw [(hwz t htIcc).2, hfd]
    rw [hcongr] at hcompare
    have hlen : Manifold.pathELength I σ' 0 τ
        = ENNReal.ofReal (∫ t in (0 : ℝ)..τ, Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' t) (u' t))) :=
      pathELength_eq_ofReal_integral_chartMetricInner (I := I) g (α := p) hτ0.le
        (hσ'.mono hsub) hsrcσ
    calc ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y
            ((Ginv ((y, extChartAt I p (σ' τ)) : E × E)).2)
            ((Ginv ((y, extChartAt I p (σ' τ)) : E × E)).2)))
        = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y (wlift τ) (wlift τ))) := rfl
      _ ≤ ENNReal.ofReal (∫ t in (0 : ℝ)..τ, Real.sqrt
            (chartMetricInner (I := I) g p (u t) (u' t) (u' t))) :=
          ENNReal.ofReal_le_ofReal hcompare
      _ = Manifold.pathELength I σ' 0 τ := hlen.symm
  -- ## the region and its topology
  set expq : E → M' := fun z => (extChartAt I p).symm ((Z ((y, T⁻¹ • z) : E × E) T).1) with hexpqdef
  have hexpq_f : ∀ z : E, expq z = (extChartAt I p).symm (f z) := fun z => rfl
  set U : Set M' := expq '' ball (0 : E) r' with hUdef
  -- `f '' ball 0 r'` is open (the `finv`-homeomorphism restricts openness)
  have hfopen_r' : IsOpen (f '' ball (0 : E) r') := by
    have hset : f '' ball (0 : E) r'
        = f '' ball (0 : E) δ ∩ finv ⁻¹' (ball (0 : E) r') := by
      ext z
      constructor
      · rintro ⟨v, hv', rfl⟩
        have hvδ : ‖v‖ < δ := (mem_ball_zero_iff.mp hv').trans hr'δ
        refine ⟨⟨v, mem_ball_zero_iff.mpr hvδ, rfl⟩, ?_⟩
        have : finv (f v) = v := by rw [hfinvdef]; simp only; rw [hGyleft v hvδ]
        rw [mem_preimage, this]; exact hv'
      · rintro ⟨⟨v, hv', rfl⟩, hz2⟩
        have hvδ : ‖v‖ < δ := mem_ball_zero_iff.mp hv'
        have hfinvfv : finv (f v) = v := by rw [hfinvdef]; simp only; rw [hGyleft v hvδ]
        refine ⟨v, ?_, rfl⟩
        rw [mem_preimage, hfinvfv] at hz2; exact hz2
    rw [hset]
    exact hfinvC1.continuousOn.isOpen_inter_preimage hfopen isOpen_ball
  -- `expq` is continuous on the closed `r'`-ball, so the region image is compact
  have hexpq_cont : ContinuousOn expq (closedBall (0 : E) r') := by
    have h1 : ContinuousOn f (closedBall (0 : E) r') :=
      hf_C1.continuousOn.mono (closedBall_subset_ball hr'δ)
    have hmap : MapsTo f (closedBall (0 : E) r') (extChartAt I p).target :=
      fun z hz => hregion z ((mem_closedBall_zero_iff.mp hz).trans_lt hr'δ)
    exact (continuousOn_extChartAt_symm p).comp h1 hmap
  -- `U` is open in `M'`
  have hUopen : IsOpen U := by
    have hUeq : U = (extChartAt I p).source ∩ extChartAt I p ⁻¹' (f '' ball (0 : E) r') := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        have hzδ : ‖z‖ < δ := (mem_ball_zero_iff.mp hz).trans hr'δ
        have hftgt : f z ∈ (extChartAt I p).target := hregion z hzδ
        refine ⟨(extChartAt I p).map_target hftgt, ?_⟩
        rw [hexpq_f, mem_preimage, (extChartAt I p).right_inv hftgt]
        exact ⟨z, hz, rfl⟩
      · rintro ⟨hxsrc, hxpre⟩
        obtain ⟨z, hz, hfz⟩ := hxpre
        refine ⟨z, hz, ?_⟩
        rw [hexpq_f, hfz, (extChartAt I p).left_inv hxsrc]
    rw [hUeq]
    have hsrcopen : IsOpen (extChartAt I p).source := by
      rw [extChartAt_source]; exact (chartAt H p).open_source
    exact (continuousOn_extChartAt (I := I) p).isOpen_inter_preimage hsrcopen hfopen_r'
  have hpU : q ∈ U := by
    refine ⟨0, mem_ball_self hr'pos, ?_⟩
    rw [hexpq_f, hf0, (extChartAt I p).left_inv hqsrcE]
  have hpolar : ∀ x ∈ U, ∃ z : E, ‖z‖ < r' ∧ x = expq z := by
    rintro x ⟨z, hz, rfl⟩; exact ⟨z, mem_ball_zero_iff.mp hz, rfl⟩
  -- ## the case split: the competitor either stays in the region or escapes
  by_cases hstay : ∀ t ∈ Icc (0 : ℝ) 1, σ t ∈ U
  · -- staying case: the polar endpoint is `w`, giving `√⟨w,w⟩_y ≤ pathELength`
    have hstay' : ∀ t ∈ Icc (0 : ℝ) 1, ∃ z : E, ‖z‖ ≤ r' ∧
        σ t = (extChartAt I p).symm ((Z ((y, T⁻¹ • z) : E × E) T).1) := by
      intro t ht
      obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hstay t ht)
      exact ⟨z, hz.le, hzeq⟩
    have hbound := hcore_q σ 1 one_pos le_rfl hσ hσ0 hstay'
    have hwlt : ‖w‖ < δ := hw.trans_le (le_trans hρ'r' hr'δ.le)
    have hendpt : extChartAt I p (σ 1) = f w := by
      rw [hσ1, (extChartAt I p).right_inv (hregion w hwlt)]
    have hfinvw : (Ginv ((y, extChartAt I p (σ 1)) : E × E)).2 = w := by
      rw [hendpt, hGyleft w hwlt]
    rw [hfinvw] at hbound
    exact hbound
  · -- escape case: a first-exit time on the `r'`-sphere forces length `≥ r'/√c > √⟨w,w⟩_y`
    push_neg at hstay
    -- the closed region is compact
    set K : Set M' := expq '' closedBall (0 : E) r' with hKdef
    have hKcompact : IsCompact K :=
      (isCompact_closedBall (0 : E) r').image_of_continuousOn hexpq_cont
    have hKclosed : IsClosed K := hKcompact.isClosed
    have hUK : U ⊆ K := image_mono ball_subset_closedBall
    -- first-exit time
    obtain ⟨t₀, ht₀, ht₀U⟩ := hstay
    set A : Set ℝ := Icc (0 : ℝ) 1 ∩ σ ⁻¹' Uᶜ with hAdef
    have hA_closed : IsClosed A :=
      hσ.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc hUopen.isClosed_compl
    have hA_ne : A.Nonempty := ⟨t₀, ht₀, ht₀U⟩
    have hA_bdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    set Texit : ℝ := sInf A with hTexitdef
    have hTA : Texit ∈ A := hA_closed.csInf_mem hA_ne hA_bdd
    have hT01 : Texit ∈ Icc (0 : ℝ) 1 := hTA.1
    have hT_pos : 0 < Texit := by
      rcases eq_or_lt_of_le hT01.1 with h | h
      · exact absurd (h ▸ (hσ0 ▸ hpU) : σ Texit ∈ U) hTA.2
      · exact h
    have hbefore : ∀ t, 0 ≤ t → t < Texit → σ t ∈ U := by
      intro t ht0 htT
      by_contra hnot
      exact absurd (csInf_le hA_bdd ⟨⟨ht0, htT.le.trans hT01.2⟩, hnot⟩) (not_le.mpr htT)
    have hσT_K : σ Texit ∈ K := by
      have hne : (𝓝[Ioo (0 : ℝ) Texit] Texit).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.mp (by
          rw [closure_Ioo hT_pos.ne]
          exact right_mem_Icc.mpr hT_pos.le)
      have htend : Tendsto σ (𝓝[Ioo (0 : ℝ) Texit] Texit) (𝓝 (σ Texit)) :=
        ((hσ.continuousOn Texit hT01).mono
          (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hT01.2))).tendsto
      exact hKclosed.mem_of_tendsto htend
        (eventually_nhdsWithin_of_forall fun t ht => hUK (hbefore t ht.1.le ht.2))
    obtain ⟨z₀, hz₀mem, hz₀eq⟩ := hσT_K
    have hz₀norm : ‖z₀‖ = r' := by
      rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hz₀mem) with h | h
      · exact absurd (⟨z₀, mem_ball_zero_iff.mpr h, hz₀eq⟩ : σ Texit ∈ U) hTA.2
      · exact h
    -- the curve stays in the closed region up to `Texit`
    have hstayT : ∀ t ∈ Icc (0 : ℝ) Texit, ∃ z : E, ‖z‖ ≤ r' ∧
        σ t = (extChartAt I p).symm ((Z ((y, T⁻¹ • z) : E × E) T).1) := by
      intro t ht
      rcases eq_or_lt_of_le ht.2 with rfl | htT
      · exact ⟨z₀, hz₀norm.le, hz₀eq.symm⟩
      · obtain ⟨z, hz, hzeq⟩ := hpolar (σ t) (hbefore t ht.1 htT)
        exact ⟨z, hz.le, hzeq⟩
    have hbound := hcore_q σ Texit hT_pos hT01.2 hσ hσ0 hstayT
    -- the polar endpoint at the exit is `z₀`
    have hz₀δ : ‖z₀‖ < δ := hz₀norm ▸ hr'δ
    have hendptT : extChartAt I p (σ Texit) = f z₀ := by
      rw [← hz₀eq, hexpq_f, (extChartAt I p).right_inv (hregion z₀ hz₀δ)]
    have hfinvz₀ : (Ginv ((y, extChartAt I p (σ Texit)) : E × E)).2 = z₀ := by
      rw [hendptT, hGyleft z₀ hz₀δ]
    rw [hfinvz₀] at hbound
    -- `√⟨z₀,z₀⟩_y ≥ r'/√c`
    have hQz₀nn : 0 ≤ chartMetricInner (I := I) g p y z₀ z₀ :=
      chartMetricInner_self_nonneg_of_mem_target (I := I) g p hytgt z₀
    have h2 : r' ^ 2 / c ≤ chartMetricInner (I := I) g p y z₀ z₀ := by
      rw [div_le_iff₀ hcpos, mul_comm]
      calc r' ^ 2 = ‖z₀‖ ^ 2 := by rw [hz₀norm]
        _ ≤ c * chartMetricInner (I := I) g p y z₀ z₀ := hgramV y hyVc z₀
    have hzradius : r' / Real.sqrt c
        ≤ Real.sqrt (chartMetricInner (I := I) g p y z₀ z₀) := by
      calc r' / Real.sqrt c = Real.sqrt (r' ^ 2 / c) := by
            rw [Real.sqrt_div (by positivity) c, Real.sqrt_sq hr'pos.le]
        _ ≤ Real.sqrt (chartMetricInner (I := I) g p y z₀ z₀) := Real.sqrt_le_sqrt h2
    -- `√⟨w,w⟩_y < r'/√c` (base-uniform smallness)
    have hwsmall : Real.sqrt (chartMetricInner (I := I) g p y w w) < r' / Real.sqrt c := by
      have hQw : chartMetricInner (I := I) g p y w w < (r' / Real.sqrt c) ^ 2 :=
        hupper y hyηU w (hw.trans_le hρ'εU)
      have hnn : 0 ≤ chartMetricInner (I := I) g p y w w :=
        chartMetricInner_self_nonneg_of_mem_target (I := I) g p hytgt w
      calc Real.sqrt (chartMetricInner (I := I) g p y w w)
          < Real.sqrt ((r' / Real.sqrt c) ^ 2) := Real.sqrt_lt_sqrt hnn hQw
        _ = r' / Real.sqrt c := Real.sqrt_sq (by positivity)
    calc ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y w w))
        ≤ ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p y z₀ z₀)) :=
          ENNReal.ofReal_le_ofReal (le_trans hwsmall.le hzradius)
      _ ≤ Manifold.pathELength I σ 0 Texit := hbound
      _ ≤ Manifold.pathELength I σ 0 1 := Manifold.pathELength_mono le_rfl hT01.2

/-- **Math.** **The base-uniform lower-bound crux `Hlb` of do Carmo Proposition 4.2**
(`prop:dc-ch3-4-2`; do Carmo Proposition 3.6 stated base-uniformly). For every `p` there are radii
`βH, ρH > 0` such that every geodesic `γ` on an open window `(lo, hi) ⊋ [0,1]` joining two points
`q₁, q₂` within `βH` of `p`, with small initial chart-`p` velocity `w` (`‖w‖ < ρH`) and
constant-speed length rate `ℓ` (`pathELength(γ|[0,t]) = ofReal(ℓ·t)`), realizes the distance:
`ofReal ℓ ≤ edist q₁ q₂`. Equivalently, such a short geodesic is minimizing.

The proof assembles the three components landed above: the constant-speed reading
`movingBase_geodesic_pathELength_eq` forces `ℓ = √⟨w,w⟩_{q₁}`; the flow-reading endpoint
identification `movingBase_geodesic_endpoint_eq_flow_reading` shows `q₂` is exactly the radial
endpoint `φ_p⁻¹((Z(φ_p q₁, T⁻¹ • w) T)₁)`; and the base-uniform competitor bound
`exists_movingBase_competitor_le_pathELength` makes every `C¹` curve from `q₁` to `q₂` at least as
long as `√⟨w,w⟩_{q₁}`. The metric-space distance is the Riemannian distance
(`IsRiemannianManifold.out`), whose defining infimum over `C¹` curves
(`Manifold.exists_lt_of_riemannianEDist_lt`) is then `≥ ofReal ℓ`.

This discharges the hypothesis `Hlb` of `exists_stronglyConvex_closedBall_of_lower_bound`; the
remaining crux of Proposition 4.2 is the local uniqueness `Huniq`. -/
theorem exists_movingBase_prop36_lower_bound
    (g : RiemannianMetric I M') (hg : g.IsRiemannianDist) (p : M') :
    ∃ βH ρH : ℝ, 0 < βH ∧ 0 < ρH ∧ ∀ (q₁ q₂ : M') (γ : ℝ → M') (w : E)
      (lo hi ℓ : ℝ), 0 ≤ ℓ →
      dist p q₁ ≤ βH → dist p q₂ ≤ βH → lo < 0 → 1 < hi → γ 0 = q₁ → γ 1 = q₂ →
      IsGeodesicOn (I := I) g γ (Ioo lo hi) → ContinuousOn γ (Ioo lo hi) →
      HasDerivAt (fun s : ℝ => extChartAt I p (γ s)) w 0 → ‖w‖ < ρH →
      (letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
       ∀ t ∈ Icc (0 : ℝ) 1, Manifold.pathELength I γ 0 t = ENNReal.ofReal (ℓ * t)) →
      ENNReal.ofReal ℓ ≤ edist q₁ q₂ := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI : IsRiemannianManifold I M' := hg
  obtain ⟨β, ρ', T, Z, rF, εF, hβpos, hρ'pos, hTpos, hrFpos, hεFpos, hTεF, hβsrc, hflow,
    hbox, hcompete⟩ := exists_movingBase_competitor_le_pathELength (I := I) g p
  refine ⟨β, ρ', hβpos, hρ'pos, ?_⟩
  intro q₁ q₂ γ w lo hi ℓ hℓnn hpq₁ hpq₂ hlo hhi hγ0 hγ1 hgeo hcont hvel hw hlen
  have hq₁ball : q₁ ∈ closedBall p β := mem_closedBall.mpr (by rw [dist_comm]; exact hpq₁)
  have hqsrc : q₁ ∈ (chartAt H p).source := hβsrc hq₁ball
  have hmem : ((extChartAt I p q₁, T⁻¹ • w) : E × E) ∈
      closedBall ((extChartAt I p p, (0 : E)) : E × E) rF := hbox q₁ hq₁ball w hw
  -- the endpoint `q₂` is the radial flow endpoint of `w`
  have hendpt : γ 1 = (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) T).1) :=
    movingBase_geodesic_endpoint_eq_flow_reading (I := I) g p hTpos hTεF hflow hmem hlo hhi
      hgeo hcont hγ0 hqsrc hvel
  -- constant speed forces `ℓ = √⟨w,w⟩_{q₁}`
  have h0S : (0 : ℝ) ∈ Ioo lo hi := ⟨hlo, by linarith⟩
  have h1S : (1 : ℝ) ∈ Ioo lo hi := ⟨by linarith, hhi⟩
  have hpatheq := movingBase_geodesic_pathELength_eq (I := I) g p hgeo isOpen_Ioo
    isPreconnected_Ioo hcont h0S h1S (by rw [hγ0]; exact hqsrc) hvel
  have hpath1 := hlen 1 (right_mem_Icc.mpr zero_le_one)
  rw [mul_one] at hpath1
  have hℓeq : ENNReal.ofReal ℓ
      = ENNReal.ofReal (Real.sqrt (chartMetricInner (I := I) g p (extChartAt I p q₁) w w)) := by
    have hcombine := hpath1.symm.trans hpatheq
    rwa [hγ0] at hcombine
  -- the distance is the Riemannian distance, so it dominates every competitor's length
  rw [hℓeq, IsRiemannianManifold.out (I := I) q₁ q₂]
  by_contra hlt
  push_neg at hlt
  obtain ⟨σ, hσ0, hσ1, hσC1, hσlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hσ1' : σ 1 = (extChartAt I p).symm ((Z ((extChartAt I p q₁, T⁻¹ • w) : E × E) T).1) :=
    hσ1.trans (hγ1.symm.trans hendpt)
  have hbd := hcompete q₁ hq₁ball w hw σ hσC1 hσ0 hσ1'
  exact absurd hσlen (not_lt.mpr hbd)

end Exponential

end Riemannian

end

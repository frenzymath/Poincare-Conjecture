import MorganTianLib.Ch02.EndsConvStep
import DoCarmoLib.Riemannian.Geodesic.IntrinsicUniqueness
import DoCarmoLib.Riemannian.Exponential.ConvexNeighborhoodInterior

/-!
# Morgan–Tian Ch. 2 — geodesics depend continuously on their initial conditions

Blueprint `lem:geodesic-continuous-dependence`.  On a complete Riemannian
manifold `(M, g)` (ambient distance = the Riemannian distance of `g`):

* **(1) Existence and uniqueness.**  Every `(q, v) ∈ TM` is the initial datum of
  a geodesic `γ_{q,v} : ℝ → M` (`exists_globalGeodesic_initial`, from Hopf–Rinow
  `c ⟹ d`), and any geodesic sharing the initial position and chart velocity is a
  restriction of it (`eqOn_of_initial_data`, intrinsic uniqueness).

* **(2) Continuous dependence.**  If a sequence of geodesics `γs n` has chart
  states (position *and* chart velocity) converging at time `0` to those of a
  limit geodesic `γ` — this is exactly convergence `(qₙ, vₙ) → (q, v)` in `TM`,
  by the description in part (2) of the blueprint statement — then the chart
  states converge at *every* time (`convAt_of_convAt_zero`), positions converge
  pointwise (`tendsto_apply_of_convAt_zero`), and the convergence is *uniform on
  every compact time interval* (`tendstoUniformlyOn_of_convAt_zero`).

The engine is the flow-box convergence invariant `Riemannian.Geodesic.ConvAt`
and the discharged step `MorganTianLib.convStepProperty` of `EndsConvStep.lean`.
The clopen propagation of `ConvAt` is *base-point agnostic* (unlike
`GeodesicEndpointContinuity`, which fixes the common origin `p`), so it delivers
the general statement in which the initial *points* `qₙ = γs n 0` also vary.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.2;
do Carmo, *Riemannian Geometry*, Ch. 3 (uniqueness) and Ch. 7, Thm 2.8.
-/

open Set Filter Metric Riemannian Riemannian.Geodesic Riemannian.Exponential
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space (TangentBundle I M)]

/-! ### Part (1): existence and uniqueness -/

/-- **Math.** **Existence** (blueprint `lem:geodesic-continuous-dependence`(1)).
On a complete manifold every initial datum `(q, v)` — with `v` recorded as the
chart-`q` coordinate velocity — is realised by a geodesic defined on all of `ℝ`.
This is Hopf–Rinow `c ⟹ d` (`DoCarmoLib`'s `exists_global_geodesic`). -/
theorem exists_globalGeodesic_initial (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (q : M) (v : E) :
    ∃ γ : ℝ → M, γ 0 = q ∧
      HasDerivAt (fun τ => extChartAt I q (γ τ)) v 0 ∧
      Continuous γ ∧ IsGeodesic (I := I) g γ :=
  exists_global_geodesic (I := I) g hg q (v : TangentSpace I q)

/-- **Math.** **Uniqueness / restriction** (blueprint
`lem:geodesic-continuous-dependence`(1)).  Two geodesics on a preconnected open
time set `s ∋ 0` that share the initial point and the initial chart-`γ₁ 0`
coordinate velocity coincide on `s`; in particular a geodesic on any interval
about `0` is the restriction of the global geodesic with the same initial data. -/
theorem eqOn_of_initial_data (g : RiemannianMetric I M)
    {γ₁ γ₂ : ℝ → M} {s : Set ℝ} (hs : IsOpen s) (hconn : IsPreconnected s)
    (h0 : (0 : ℝ) ∈ s)
    (h₁ : IsGeodesicOn (I := I) g γ₁ s) (h₂ : IsGeodesicOn (I := I) g γ₂ s)
    (hc₁ : ContinuousOn γ₁ s) (hc₂ : ContinuousOn γ₂ s)
    (hq : γ₁ 0 = γ₂ 0)
    (hv : deriv (fun τ => extChartAt I (γ₁ 0) (γ₁ τ)) 0
        = deriv (fun τ => extChartAt I (γ₁ 0) (γ₂ τ)) 0) :
    Set.EqOn γ₁ γ₂ s :=
  IsGeodesicOn.eqOn_of_deriv_chartReading_eq (I := I) (β := γ₁ 0) hs hconn h₁ h₂
    hc₁ hc₂ h0 hq (mem_chart_source H (γ₁ 0)) hv

/-! ### Part (2): continuous dependence via the flow-box invariant -/

/-- **Math.** **The chart-state invariant propagates from time `0` to every
time.**  Base-point-agnostic core of continuous dependence: if the convergence
invariant `ConvAt γ γs` (positions and chart-at-the-limit velocities converge)
holds at `t = 0`, then it holds at every `t`.  The set of good times is clopen
(the discharged flow-box step `convStepProperty` propagates it both ways) and
nonempty, hence all of `ℝ`. -/
theorem convAt_of_convAt_zero (g : RiemannianMetric I M)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hγsc : ∀ n, Continuous (γs n))
    (h0 : ConvAt (I := I) γ γs 0) (t : ℝ) :
    ConvAt (I := I) γ γs t := by
  set S : Set ℝ := {t | ConvAt (I := I) γ γs t} with hSdef
  have hstep' := convStepProperty g γ γs hγgeo hγc hγsgeo hγsc
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ρ, hρ, hprop⟩ := hstep' t
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hρ) ?_
    intro u hu
    have hut : |u - t| ≤ ρ := by
      rw [Metric.mem_ball, Real.dist_eq] at hu; exact hu.le
    exact hprop t u (by simp [abs_zero, hρ.le]) hut ht
  have hScompl : IsOpen Sᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    obtain ⟨ρ, hρ, hprop⟩ := hstep' t
    refine Filter.mem_of_superset (Metric.ball_mem_nhds t hρ) ?_
    intro u hu huS
    have hut : |u - t| ≤ ρ := by
      rw [Metric.mem_ball, Real.dist_eq] at hu; exact hu.le
    exact ht (hprop u t hut (by simp [abs_zero, hρ.le]) huS)
  have hSclopen : IsClopen S := ⟨isOpen_compl_iff.mp hScompl, hSopen⟩
  have hSuniv : S = Set.univ := hSclopen.eq_univ ⟨0, h0⟩
  have : t ∈ S := by rw [hSuniv]; exact Set.mem_univ t
  exact this

/-- **Math.** **Pointwise position convergence** (blueprint
`lem:geodesic-continuous-dependence`(2)): if chart states converge at `0`, then
`γs n t → γ t` for every fixed `t`. -/
theorem tendsto_apply_of_convAt_zero (g : RiemannianMetric I M)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγgeo : IsGeodesic (I := I) g γ) (hγc : Continuous γ)
    (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n)) (hγsc : ∀ n, Continuous (γs n))
    (h0 : ConvAt (I := I) γ γs 0) (t : ℝ) :
    Tendsto (fun n => γs n t) atTop (𝓝 (γ t)) :=
  (convAt_of_convAt_zero g hγgeo hγc hγsgeo hγsc h0 t).1

/-! ### The uniform speed bound for a varying base point -/

/-- **Math.** **Joint continuity of the diagonal chart Gram form.** For a base
point `α` and a chart-target coordinate `y₀`, the map
`(y, ξ) ↦ ⟨ξ, ξ⟩_y = chartMetricInner g α y ξ ξ` is continuous at `(y₀, ξ₀)`:
the Gram entries `chartGramOnE g α i j` are `C^∞` on the (open) chart target and
each coordinate `ξ ↦ ξ^i` is a continuous linear functional. -/
theorem continuousAt_chartMetricInner_diag (g : RiemannianMetric I M) (α : M)
    {y₀ ξ₀ : E} (hy₀ : y₀ ∈ (extChartAt I α).target) :
    ContinuousAt (fun p : E × E => chartMetricInner (I := I) g α p.1 p.2 p.2)
      (y₀, ξ₀) := by
  have htgt : (extChartAt I α).target ×ˢ (univ : Set E) ∈ 𝓝 (y₀, ξ₀) :=
    prod_mem_nhds ((isOpen_extChartAt_target (I := I) α).mem_nhds hy₀) univ_mem
  have hON : ContinuousOn (fun p : E × E => chartMetricInner (I := I) g α p.1 p.2 p.2)
      ((extChartAt I α).target ×ˢ (univ : Set E)) := by
    simp only [chartMetricInner_def]
    refine continuousOn_finset_sum _ (fun i _ => continuousOn_finset_sum _ (fun j _ => ?_))
    have hG : ContinuousOn (fun p : E × E => chartGramOnE (I := I) g α i j p.1)
        ((extChartAt I α).target ×ˢ (univ : Set E)) :=
      (chartGramOnE_contDiffOn (I := I) g α i j).continuousOn.comp continuousOn_fst
        (fun p hp => hp.1)
    have hVi : ContinuousOn (fun p : E × E => Geodesic.chartCoord (E := E) i p.2)
        ((extChartAt I α).target ×ˢ (univ : Set E)) :=
      (Geodesic.continuous_chartCoord (E := E) i).comp_continuousOn continuousOn_snd
    have hVj : ContinuousOn (fun p : E × E => Geodesic.chartCoord (E := E) j p.2)
        ((extChartAt I α).target ×ˢ (univ : Set E)) :=
      (Geodesic.continuous_chartCoord (E := E) j).comp_continuousOn continuousOn_snd
    exact (hG.mul hVi).mul hVj
  exact hON.continuousAt htgt

/-- **Math.** **The conserved speeds converge** (hence are bounded).  If chart
states converge at `0`, the squared speeds `speedSq (γs n) 0` converge to
`speedSq γ 0`.  Read in the chart at the *limit* base `γ 0`, the speed is the
diagonal chart Gram form of the (converging) chart velocity at the (converging)
base position, so it converges by joint continuity of that form. -/
theorem tendsto_speedSq_of_convAt_zero (g : RiemannianMetric I M)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγc : Continuous γ) (hγgeo : IsGeodesic (I := I) g γ)
    (hγsc : ∀ n, Continuous (γs n)) (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n))
    (h0 : ConvAt (I := I) γ γs 0) :
    Tendsto (fun n => speedSq (I := I) g (γs n) 0) atTop
      (𝓝 (speedSq (I := I) g γ 0)) := by
  obtain ⟨h0pos, h0vel⟩ := h0
  set ξs : ℕ → E := fun n => deriv (fun τ => extChartAt I (γ 0) (γs n τ)) 0 with hξs
  set ξ : E := deriv (fun τ => extChartAt I (γ 0) (γ τ)) 0 with hξ
  -- Seal the heavy `chartMetricInner` behind an opaque `Q` (defeq-loop gotcha).
  set Q : E × E → ℝ := fun p => chartMetricInner (I := I) g (γ 0) p.1 p.2 p.2 with hQ
  have hQval : ∀ y a : E, chartMetricInner (I := I) g (γ 0) y a a = Q (y, a) := fun _ _ => rfl
  -- chart states at `0` converge: velocities `ξs n → ξ` and positions `γs n 0 → γ 0`.
  have hvel : Tendsto ξs atTop (𝓝 ξ) := h0vel
  have hbaseTgt : extChartAt I (γ 0) (γ 0) ∈ (extChartAt I (γ 0)).target :=
    mem_extChartAt_target (γ 0)
  -- limit speed as the diagonal Gram form.
  have hdγ : HasDerivAt (fun τ => extChartAt I (γ 0) (γ τ)) ξ 0 :=
    ((hγgeo.hasGeodesicEquationAt 0).hasDerivAt_extChartAt_deriv hγc.continuousAt
      (mem_chart_source H (γ 0)))
  have hspeedγ : speedSq (I := I) g γ 0 = Q (extChartAt I (γ 0) (γ 0), ξ) := by
    rw [speedSq_eq_chartMetricInner_extChartAt (I := I) g hγc.continuousAt
      (mem_chart_source H (γ 0)) hdγ, hQval]
  -- base positions read in the chart at `γ 0` converge.
  have hpos : Tendsto (fun n => extChartAt I (γ 0) (γs n 0)) atTop
      (𝓝 (extChartAt I (γ 0) (γ 0))) :=
    ((continuousAt_extChartAt (γ 0)).tendsto).comp h0pos
  -- the Gram form of the converging chart states converges.
  have hcont : ContinuousAt Q (extChartAt I (γ 0) (γ 0), ξ) :=
    continuousAt_chartMetricInner_diag (I := I) g (γ 0)
      (y₀ := extChartAt I (γ 0) (γ 0)) (ξ₀ := ξ) hbaseTgt
  have hGram : Tendsto (fun n => Q (extChartAt I (γ 0) (γs n 0), ξs n)) atTop
      (𝓝 (Q (extChartAt I (γ 0) (γ 0), ξ))) :=
    hcont.tendsto.comp (hpos.prodMk_nhds hvel)
  rw [hspeedγ]
  -- eventually, the speed of `γs n` equals that Gram form.
  refine hGram.congr' ?_
  have hsrc : ∀ᶠ n in atTop, γs n 0 ∈ (chartAt H (γ 0)).source :=
    h0pos.eventually ((chartAt H (γ 0)).open_source.mem_nhds (mem_chart_source H (γ 0)))
  filter_upwards [hsrc] with n hn
  have hdn : HasDerivAt (fun τ => extChartAt I (γ 0) (γs n τ)) (ξs n) 0 :=
    ((hγsgeo n).hasGeodesicEquationAt 0).hasDerivAt_extChartAt_deriv (hγsc n).continuousAt hn
  rw [speedSq_eq_chartMetricInner_extChartAt (I := I) g (hγsc n).continuousAt hn hdn, hQval]

/-- **Math.** **A common Lipschitz constant.**  If chart states converge at `0`,
there is a `C` bounding every conserved speed, so the limit geodesic `γ` and all
`γs n` are `√C`-Lipschitz on `ℝ` (their speeds are constant along their length,
`IsGeodesicOn.speedSq_eq`, and bounded by `C`). -/
theorem exists_lipschitz_of_convAt_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγc : Continuous γ) (hγgeo : IsGeodesic (I := I) g γ)
    (hγsc : ∀ n, Continuous (γs n)) (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n))
    (h0 : ConvAt (I := I) γ γs 0) :
    ∃ C : ℝ,
      (∀ (n : ℕ) (s t : ℝ), dist (γs n s) (γs n t) ≤ Real.sqrt C * |s - t|) ∧
      (∀ s t : ℝ, dist (γ s) (γ t) ≤ Real.sqrt C * |s - t|) := by
  have hTend := tendsto_speedSq_of_convAt_zero g hγc hγgeo hγsc hγsgeo h0
  obtain ⟨C, hCub⟩ := hTend.bddAbove_range
  have hCn : ∀ n, speedSq (I := I) g (γs n) 0 ≤ C := fun n => hCub ⟨n, rfl⟩
  have hCγ : speedSq (I := I) g γ 0 ≤ C :=
    le_of_tendsto hTend (Filter.Eventually.of_forall hCn)
  -- generic Lipschitz estimate for a geodesic with speed bounded at `0` by `C`
  have hkey : ∀ (σ : ℝ → M), IsGeodesic (I := I) g σ → Continuous σ →
      speedSq (I := I) g σ 0 ≤ C → ∀ s t : ℝ,
        dist (σ s) (σ t) ≤ Real.sqrt C * |s - t| := by
    intro σ hσgeo hσc hσC s t
    have hgon : IsGeodesicOn (I := I) g σ Set.univ := hσgeo.isGeodesicOn _
    have hconton : ContinuousOn σ Set.univ := hσc.continuousOn
    have hmono : ∀ a b : ℝ, a ≤ b →
        dist (σ a) (σ b) ≤ Real.sqrt C * (b - a) := by
      intro a b hab
      have hd := hgon.dist_le g hg isOpen_univ isPreconnected_univ hconton
        (Set.mem_univ a) (Set.mem_univ b) hab
      have hspeed_ab : speedSq (I := I) g σ a = speedSq (I := I) g σ 0 :=
        hgon.speedSq_eq isOpen_univ isPreconnected_univ hconton
          (Set.mem_univ a) (Set.mem_univ 0)
      rw [hspeed_ab] at hd
      exact hd.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hσC) (by linarith))
    rcases le_total s t with hst | hst
    · have := hmono s t hst
      rwa [abs_of_nonpos (by linarith : s - t ≤ 0), neg_sub]
    · have := hmono t s hst
      rw [dist_comm]
      rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t)]
  exact ⟨C, fun n s t => hkey (γs n) (hγsgeo n) (hγsc n) (hCn n) s t,
    fun s t => hkey γ hγgeo hγc hCγ s t⟩

/-- **Math.** **Uniform convergence on compact time intervals** (blueprint
`lem:geodesic-continuous-dependence`(2)): if chart states converge at `0`, then
`γs n → γ` uniformly on every `[-T, T]`.  Pointwise convergence
(`tendsto_apply_of_convAt_zero`) plus the common `√C`-Lipschitz bound
(equicontinuity) upgrade to uniform convergence over the compact interval by a
finite `δ`-net argument. -/
theorem tendstoUniformlyOn_of_convAt_zero (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {γs : ℕ → ℝ → M}
    (hγc : Continuous γ) (hγgeo : IsGeodesic (I := I) g γ)
    (hγsc : ∀ n, Continuous (γs n)) (hγsgeo : ∀ n, IsGeodesic (I := I) g (γs n))
    (h0 : ConvAt (I := I) γ γs 0) (T : ℝ) :
    TendstoUniformlyOn (fun n => γs n) γ atTop (Icc (-T) T) := by
  obtain ⟨C, hLipγs, hLipγ⟩ :=
    exists_lipschitz_of_convAt_zero g hg hγc hγgeo hγsc hγsgeo h0
  have hpos : ∀ t, Tendsto (fun n => γs n t) atTop (𝓝 (γ t)) :=
    fun t => tendsto_apply_of_convAt_zero g hγgeo hγc hγsgeo hγsc h0 t
  set L : ℝ := Real.sqrt C with hL
  have hLnn : 0 ≤ L := Real.sqrt_nonneg C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ : ℝ := ε / (3 * (L + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨tt, htt⟩ := (isCompact_Icc (a := -T) (b := T)).elim_nhds_subcover
    (fun x => ball x δ) (fun x _ => Metric.ball_mem_nhds x hδpos)
  have hnet : ∀ᶠ n in atTop, ∀ x ∈ tt, dist (γ x) (γs n x) < ε / 3 := by
    rw [eventually_all_finset]
    intro x _
    have hd0 : Tendsto (fun n => dist (γ x) (γs n x)) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := γ x)).dist (hpos x)
    exact hd0.eventually (Iio_mem_nhds (show (0 : ℝ) < ε / 3 by positivity))
  filter_upwards [hnet] with n hn
  intro z hz
  obtain ⟨x, hxtt, hzx⟩ := mem_iUnion₂.mp (htt.2 hz)
  have hzxlt : |z - x| < δ := by rw [← Real.dist_eq]; exact hzx
  have hL1 : (0 : ℝ) < 3 * (L + 1) := by positivity
  have hδeq : δ * (3 * (L + 1)) = ε := by rw [hδ]; exact div_mul_cancel₀ ε hL1.ne'
  have harith : L * |z - x| + ε / 3 + L * |x - z| < ε := by
    have hzx' : |z - x| ≤ δ := hzxlt.le
    have hxz' : |x - z| ≤ δ := by rw [abs_sub_comm]; exact hzxlt.le
    have h1 : L * |z - x| ≤ L * δ := mul_le_mul_of_nonneg_left hzx' hLnn
    have h2 : L * |x - z| ≤ L * δ := mul_le_mul_of_nonneg_left hxz' hLnn
    nlinarith [h1, h2, hδeq, hδpos, hLnn, hε]
  calc dist (γ z) (γs n z)
      ≤ dist (γ z) (γ x) + dist (γ x) (γs n x) + dist (γs n x) (γs n z) :=
        dist_triangle4 _ _ _ _
    _ ≤ L * |z - x| + ε / 3 + L * |x - z| := by
        have a1 : dist (γ z) (γ x) ≤ L * |z - x| := hLipγ z x
        have a2 : dist (γ x) (γs n x) ≤ ε / 3 := (hn x hxtt).le
        have a3 : dist (γs n x) (γs n z) ≤ L * |x - z| := hLipγs n x z
        linarith
    _ < ε := harith

end MorganTianLib

end

import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodContinuity
import OpenGALib.Riemannian.Geodesic.FlowReadback

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: assembly of `lem:dc-ch3-4-1` (do Carmo Ch. 3, §4)

`ConvexNeighborhood.lean` supplied the fibrewise (fixed-`(q,v)`) Leibniz calculus of the
squared radial distance `F(t) = |exp_p⁻¹(γ(t))|²_p`, and `ConvexNeighborhoodContinuity.lean`
packaged `∂²F/∂t²(0, q, v)` as the explicit algebraic form `secondDerivChartForm`, proved its
joint continuity in the moving base point, and — via degree-2 homogeneity — its strict
positivity `secondDerivChartForm g p finv a w > 0` for every base `a` in a neighborhood `V` of
`φ_p(p)` and every nonzero chart velocity `w` (`exists_secondDerivChartForm_pos_nhds_ne`).

This file performs the **assembly** that do Carmo's proof describes: it identifies the abstract
form `secondDerivChartForm g p finv a w` with the genuine second time-derivative
`deriv (deriv F) 0` of `F` *along the moving-base geodesic family*, and then combines the
tangency (`∂F/∂t(0) = 0`, the Gauss lemma) with the strict positivity through the
second-derivative test (`eventually_ge_of_deriv_deriv_pos`) to conclude that a geodesic tangent
to the geodesic sphere `S_r(p)` stays outside the open ball `B_r(p)` near its base point —
`lem:dc-ch3-4-1`.

The heart is the **second-order chain rule** for `u(s) = finv(x(s))`, where `x` is the chart
reading of the geodesic (`x(0) = a`, `x'(0) = w`, `x''(0) = (spray(a,w))₂`):
`u'(0) = Dfinv(a)(w)`, `u''(0) = D²finv(a)(w,w) + Dfinv(a)(x''(0))`,
so by the Leibniz calculus `deriv F 0 = 2⟨Dfinv(a)(w), finv(a)⟩` and
`deriv (deriv F) 0 = 2⟨u''(0), finv(a)⟩ + 2⟨Dfinv(a)(w), Dfinv(a)(w)⟩ = secondDerivChartForm`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The F-identity: `∂F/∂t(0)` and `∂²F/∂t²(0)` along a chart-read geodesic.**
Let `finv` be `C²` on an open set `S`, let `x : ℝ → E` be a curve differentiable near `0` with
values eventually in `S`, `x(0) = a ∈ S`, `x'(0) = w`, and second derivative
`HasDerivAt (deriv x) xacc 0` (so `x''(0) = xacc`). Then the squared radial distance
`F(s) = ⟨finv(x s), finv(x s)⟩_p` in the fixed chart Gram form at `p` satisfies

* `deriv F 0 = 2⟨Dfinv(a)(w), finv(a)⟩_p` (do Carmo's `∂F/∂t = 2⟨u', u⟩`, at `t = 0`), and
* `deriv (deriv F) 0 = 2⟨D²finv(a)(w,w) + Dfinv(a)(xacc), finv(a)⟩_p + 2⟨Dfinv(a)(w), Dfinv(a)(w)⟩_p`
  (do Carmo's `∂²F/∂t² = 2⟨u'', u⟩ + 2|u'|²`, at `t = 0`),

by the second-order chain rule `u''(0) = D²finv(a)(w,w) + Dfinv(a)(x''(0))` for
`u = finv ∘ x`. -/
theorem hasDerivAt_and_deriv_deriv_sqNormComp (g : RiemannianMetric I M) (p : M)
    {finv : E → E} {S : Set E} (hS : IsOpen S) (hfinv : ContDiffOn ℝ 2 finv S)
    {x : ℝ → E} {a w xacc : E} (ha : a ∈ S) (hx0 : x 0 = a) (hdx0 : deriv x 0 = w)
    (hxev : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt x (deriv x s) s)
    (hxmem : ∀ᶠ s in 𝓝 (0 : ℝ), x s ∈ S)
    (hx2 : HasDerivAt (deriv x) xacc 0) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
        (finv (x s)) (finv (x s)))
      (2 * chartMetricInner (I := I) g p (extChartAt I p p)
        (fderiv ℝ finv a w) (finv a)) 0
    ∧ deriv (deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
        (finv (x s)) (finv (x s)))) 0
      = 2 * chartMetricInner (I := I) g p (extChartAt I p p)
          ((fderiv ℝ (fderiv ℝ finv) a w) w + fderiv ℝ finv a xacc) (finv a)
        + 2 * chartMetricInner (I := I) g p (extChartAt I p p)
          (fderiv ℝ finv a w) (fderiv ℝ finv a w) := by
  classical
  set IP := extChartAt I p p with hIP
  -- `u = finv ∘ x`, `u' s = Dfinv(x s)(x'(s))`
  set u : ℝ → E := fun s => finv (x s) with hudef
  set u' : ℝ → E := fun s => fderiv ℝ finv (x s) (deriv x s) with hu'def
  set F : ℝ → ℝ := fun s => chartMetricInner (I := I) g p IP (u s) (u s) with hFdef
  -- `finv` has an `fderiv` at every point of `S`
  have hfinvFD : ∀ y ∈ S, HasFDerivAt finv (fderiv ℝ finv y) y := fun y hy =>
    ((hfinv.contDiffAt (hS.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt
  -- near `0`: `u` is differentiable with derivative `u' s`
  have hu_ev : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt u (u' s) s := by
    filter_upwards [hxev, hxmem] with s hxs hmems
    exact (hfinvFD (x s) hmems).comp_hasDerivAt s hxs
  -- near `0`: `deriv F s = 2⟨u' s, u s⟩`
  have hF_ev : ∀ᶠ s in 𝓝 (0 : ℝ),
      HasDerivAt F (2 * chartMetricInner (I := I) g p IP (u' s) (u s)) s := by
    filter_upwards [hu_ev] with s hus
    exact hasDerivAt_chartMetricInner_diag (I := I) g p IP hus
  -- values at `0`
  have hu0 : u 0 = finv a := by simp only [hudef, hx0]
  have hu'0 : u' 0 = fderiv ℝ finv a w := by simp only [hu'def, hx0, hdx0]
  -- first conclusion: `deriv F 0`
  have hF'0 : HasDerivAt F (2 * chartMetricInner (I := I) g p IP (fderiv ℝ finv a w) (finv a)) 0 := by
    have h := hF_ev.self_of_nhds
    rwa [hu'0, hu0] at h
  refine ⟨hF'0, ?_⟩
  -- second-order chain rule for `u'`
  have hxw0 : HasDerivAt x w 0 := by
    have h := hxev.self_of_nhds
    rwa [hdx0] at h
  -- `A = Dfinv` differentiable at `a`
  have hDcd : ContDiffOn ℝ 1 (fderiv ℝ finv) S := hfinv.fderiv_of_isOpen hS (by norm_num)
  have hAFD : HasFDerivAt (fderiv ℝ finv) (fderiv ℝ (fderiv ℝ finv) a) a :=
    ((hDcd.contDiffAt (hS.mem_nhds ha)).differentiableAt (by norm_num)).hasFDerivAt
  -- `B s = Dfinv(x s)` has derivative `D²finv(a)(w)` at `0`
  have hgFD : HasFDerivAt (fderiv ℝ finv) (fderiv ℝ (fderiv ℝ finv) a) (x 0) := by
    rw [hx0]; exact hAFD
  have hB : HasDerivAt (fun s => fderiv ℝ finv (x s))
      ((fderiv ℝ (fderiv ℝ finv) a) w) 0 :=
    hgFD.comp_hasDerivAt 0 hxw0
  -- `u' = B ⬝ deriv x` has derivative `u''(0)` at `0`
  have hu' : HasDerivAt u'
      ((fderiv ℝ (fderiv ℝ finv) a w) w + fderiv ℝ finv a xacc) 0 := by
    have h := hB.clm_apply hx2
    simp only [hdx0, hx0] at h
    exact h
  -- differentiate `deriv F =ᶠ (fun s => 2⟨u' s, u s⟩)` at `0`
  have hderivF_ev : deriv F =ᶠ[𝓝 (0 : ℝ)]
      (fun s => 2 * chartMetricInner (I := I) g p IP (u' s) (u s)) := by
    filter_upwards [hF_ev] with s hs using hs.deriv
  rw [hderivF_ev.deriv_eq]
  have hmain := hasDerivAt_deriv_chartMetricInner_diag (I := I) g p IP
    (u := u) (u' := u') hu_ev.self_of_nhds hu'
  rw [hmain.deriv, hu0, hu'0]
  ring

/-- **Math.** **The F-identity for the moving-base geodesic flow reading.** Let `Z` be a local
flow of the chart-`p` geodesic spray (from `exists_uniform_geodesic_flow` /
`exists_pairMap_hasStrictFDerivAt`), let `finv` be `C²` on an open `S ∋ y` (`y = φ_p(q)` the
chart position of the base point), and let `(y, T⁻¹ • w)` be an admissible initial condition
with chart velocity `w`. Along the geodesic reading
`x(s) = φ_p(γ(s))`, `γ(s) = φ_p⁻¹((Z(y, T⁻¹ • w)(sT))₁)`, the squared radial distance
`F(s) = ⟨finv(x s), finv(x s)⟩_p` has

* `HasDerivAt F (2⟨Dfinv(y)(w), finv(y)⟩_p) 0` (do Carmo's `∂F/∂t`), and
* `deriv (deriv F) 0 = secondDerivChartForm g p finv y w` (do Carmo's `∂²F/∂t²(0, q, v)`).

The chart reading `x` has `x(0) = y`, `x'(0) = w`, and `x''(0) = (spray(y, w))₂`
(`isGeodesicOn_uniform_flow_segment`), and is differentiable on the whole open window
(`isGeodesicOn_uniform_flow_segment_Ioo`); feeding these into the abstract second-order chain
rule `hasDerivAt_and_deriv_deriv_sqNormComp` identifies `deriv (deriv F) 0` with the algebraic
form `secondDerivChartForm` of `ConvexNeighborhoodContinuity.lean`. -/
theorem hasDerivAt_and_deriv_deriv_sqNorm_flowReading [T2Space M]
    (g : RiemannianMetric I M) (p : M) {r ε T : ℝ} {Z : E × E → ℝ → E × E}
    (hT : 0 < T) (hTε : T < ε)
    (hflow : ∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
      Z z 0 = z ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
        (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E)))
    {finv : E → E} {S : Set E} (hSopen : IsOpen S) (hfinv : ContDiffOn ℝ 2 finv S)
    {y w : E} (hyS : y ∈ S)
    (hmem : ((y, T⁻¹ • w) : E × E) ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r) :
    HasDerivAt (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
        (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
          ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
        (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
          ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s)))
      (2 * chartMetricInner (I := I) g p (extChartAt I p p)
        (fderiv ℝ finv y w) (finv y)) 0
    ∧ deriv (deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
        (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
          ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
        (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
          ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s)))) 0
      = secondDerivChartForm (I := I) g p finv y w := by
  classical
  set x : ℝ → E := fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
    ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1)) with hxdef
  -- base descent: `x 0 = γ`-reading, `x'(0) = w`, `x''(0) = (spray(y,w))₂`
  obtain ⟨_hγ0, _hcont, _hgeo, hchart, hvel, hacc⟩ :=
    isGeodesicOn_uniform_flow_segment (I := I) g p hT hTε hflow hmem
  -- window derivative facts, for eventual differentiability of `x`
  obtain ⟨_, _, _, _, _, hwindow⟩ :=
    isGeodesicOn_uniform_flow_segment_Ioo (I := I) g p hT hTε hflow hmem
  -- `x 0 = y`
  obtain ⟨h0, _, _⟩ := hflow _ hmem
  have hx0 : x 0 = y := by
    have h := (hchart 0 ⟨le_refl 0, zero_le_one⟩).2
    simp only [hxdef]
    rw [h, zero_mul, h0]
  -- `deriv x 0 = w`
  have hdx0 : deriv x 0 = w := hvel.deriv
  -- eventual differentiability of `x` near 0
  have hεpos : (0 : ℝ) < ε := hT.trans hTε
  have hεTpos : (0 : ℝ) < ε / T := div_pos hεpos hT
  have h0J : (0 : ℝ) ∈ Ioo (-(ε / T)) (ε / T) := ⟨neg_lt_zero.mpr hεTpos, hεTpos⟩
  have hxev : ∀ᶠ s in 𝓝 (0 : ℝ), HasDerivAt x (deriv x s) s := by
    filter_upwards [isOpen_Ioo.mem_nhds h0J] with s hs
    have hd := hwindow s hs
    rw [hd.deriv]; exact hd
  -- `x s ∈ S` eventually
  have hxmem : ∀ᶠ s in 𝓝 (0 : ℝ), x s ∈ S := by
    have hxcont : ContinuousAt x 0 := hvel.continuousAt
    filter_upwards [hxcont.preimage_mem_nhds (hSopen.mem_nhds (by rw [hx0]; exact hyS))]
      with s hs using hs
  -- apply the abstract F-identity, with `xacc = (spray(y,w))₂`
  obtain ⟨hF', hF''⟩ := hasDerivAt_and_deriv_deriv_sqNormComp (I := I) g p hSopen hfinv
    hyS hx0 hdx0 hxev hxmem hacc
  refine ⟨hF', ?_⟩
  rw [hF'']
  rfl

/-- **Math.** **do Carmo Ch. 3, §4, Lemma 4.1 — a geodesic tangent to a geodesic sphere stays
outside the ball.** For any `p ∈ M` there are a `C²` exponential inverse `finv`, an open
neighborhood `V` of `φ_p(p)` (do Carmo's `c`: the ball `exp_p(B_c(0))` reads into `V`), and a
local geodesic flow package `(r, ε, T, Z)`, such that: for every base position `y ∈ V` and every
nonzero chart velocity `w` with `(y, T⁻¹ • w)` admissible, the geodesic `γ` through
`q = φ_p⁻¹(y)` with chart velocity `w` — read radially as
`F(s) = |exp_p⁻¹(γ(s))|²_p = ⟨finv(x s), finv(x s)⟩_p`, `x(s) = φ_p(γ(s))` — that is **tangent**
to the geodesic sphere at `q` (`∂F/∂t(0) = 0`, the Gauss lemma) has a **strict minimum** of `F`
at `s = 0`: `F(0) ≤ F(s)` for all `s` near `0`, i.e. it stays outside the open ball
`{|exp_p⁻¹(·)|²_p < F(0)}` — do Carmo's `B_r(p)`.

The proof combines the F-identity `deriv (deriv F) 0 = secondDerivChartForm g p finv y w`
(`hasDerivAt_and_deriv_deriv_sqNorm_flowReading`), the strict positivity of `secondDerivChartForm`
on `V` for nonzero velocities (`exists_secondDerivChartForm_pos_nhds_ne`), and the
second-derivative test (`eventually_ge_of_deriv_deriv_pos`): with `∂F/∂t(0) = 0` and
`∂²F/∂t²(0) > 0`, `F` has a strict local minimum at `0`. -/
theorem exists_forall_geodesic_tangent_stays_outside_ball [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (V : Set E) (r ε T : ℝ) (Z : E × E → ℝ → E × E),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      ∀ (y w : E), y ∈ V → w ≠ 0 →
        ((y, T⁻¹ • w) : E × E) ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r →
        deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
            (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
              ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
            (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
              ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))) 0 = 0 →
        ∀ᶠ s in 𝓝 (0 : ℝ),
          chartMetricInner (I := I) g p (extChartAt I p p)
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) 0))
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) 0))
            ≤ chartMetricInner (I := I) g p (extChartAt I p p)
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s)) := by
  obtain ⟨finv, V, hVopen, hpV, hVsub, hf0, hfinvC2, hpos, _⟩ :=
    exists_secondDerivChartForm_pos_nhds_ne (I := I) g p
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, _, _⟩ :=
    exists_pairMap_hasStrictFDerivAt (I := I) g p
  refine ⟨finv, V, r, ε, T, Z, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hflow, ?_⟩
  intro y w hyV hwne hmem htang
  obtain ⟨hF', hF''⟩ :=
    hasDerivAt_and_deriv_deriv_sqNorm_flowReading (I := I) g p hT hTε hflow hVopen hfinvC2 hyV hmem
  have hF''pos : deriv (deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
      (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
      (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s)))) 0 > 0 := by
    rw [hF'']; exact hpos y hyV w hwne
  exact eventually_ge_of_deriv_deriv_pos hF''pos htang hF'.continuousAt

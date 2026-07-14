import OpenGALib.Riemannian.Exponential.ConvexNeighborhood
import OpenGALib.Riemannian.Exponential.C2LocalDiffeo
import OpenGALib.Riemannian.Exponential.TotallyNormal

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Convex neighborhoods: joint continuity of the second time-derivative in the base point

This file supplies the residual of `lem:dc-ch3-4-1` (do Carmo Ch. 3, §4, Lemma 4.1):
the joint continuity of `∂²F/∂t²(0, q, v)` in the moving base point `q`, where
`F(t, q, v) = |exp_p⁻¹(γ(t, q, v))|²_p` for the geodesic `γ(·, q, v)` through `q`
with velocity `v`.

The key structural observation is that the value `∂²F/∂t²(0, q, v)` is an **algebraic**
function of `(a, w) = (φ_p(q), w)` — the chart position of `q` and the chart velocity —
obtained from the fixed `C²` inverse chart map `finv = (φ_p ∘ exp_p)⁻¹` and the geodesic
spray, with **no time integration**:

* along the geodesic read in the chart at `p`, `x(s) = φ_p(γ(s))`, the geodesic ODE gives
  directly `x(0) = a`, `x'(0) = w`, and `x''(0) = (geodesicSprayCoord g p a w).2`
  (the velocity-component of the spray, `-Γ_a(w, w)`);
* `u(s) = finv(x(s))`, so by the second-order chain rule
  `u''(0) = D²finv(a)(w, w) + Dfinv(a)(x''(0))`;
* `F = |u|²_p` has, by the fibrewise Leibniz calculus of `ConvexNeighborhood.lean`,
  `∂²F/∂t²(0) = 2⟨u''(0), u(0)⟩_p + 2|u'(0)|²_p`.

We package the right-hand side as the explicit form `secondDerivChartForm`, prove it is
**jointly continuous** in `(a, w)` (from continuity of `finv`, `Dfinv`, `D²finv` and the
smooth spray), and — since at `q = p` the term `u(0) = finv(φ_p p) = 0` vanishes and
`Dfinv(φ_p p)` is a linear isomorphism — that it is **strictly positive** for `v ≠ 0` at
`q = p`. Continuity plus positivity at `p` propagate the strict minimum to a neighborhood,
which is exactly the missing step for `lem:dc-ch3-4-1`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

section ChartMetricInnerContinuous

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Each chart coordinate `v ↦ v^i` is continuous (it is a continuous linear
functional). -/
theorem Geodesic.continuous_chartCoord (i : Fin (Module.finrank ℝ E)) :
    Continuous (Geodesic.chartCoord (E := E) i) := by
  have h : (Geodesic.chartCoord (E := E) i)
      = fun v => Geodesic.chartCoordFunctional (E := E) i v :=
    funext fun v => (Geodesic.chartCoordFunctional_apply (E := E) i v).symm
  rw [h]
  exact (Geodesic.chartCoordFunctional (E := E) i).continuous

/-- **Math.** **Joint continuity of the fixed chart Gram inner product.** For a fixed base
point `y`, the bilinear form `(a, b) ↦ ⟨a, b⟩_y = chartMetricInner g α y a b` is jointly
continuous (a finite sum of products of continuous linear coordinates with constant
coefficients). -/
theorem continuous_chartMetricInner_pair (g : RiemannianMetric I M) (α : M) (y : E) :
    Continuous (fun z : E × E => chartMetricInner (I := I) g α y z.1 z.2) := by
  simp only [chartMetricInner_def]
  refine continuous_finset_sum _ (fun i _ => continuous_finset_sum _ (fun j _ => ?_))
  exact (continuous_const.mul
      ((Geodesic.continuous_chartCoord (E := E) i).comp continuous_fst)).mul
    ((Geodesic.continuous_chartCoord (E := E) j).comp continuous_snd)

/-- **Math.** Continuity of `z ↦ ⟨f z, h z⟩_y` for the fixed chart Gram inner product,
whenever `f` and `h` are continuous on `s`. -/
theorem continuousOn_chartMetricInner_comp {α : M} {y : E} (g : RiemannianMetric I M)
    {X : Type*} [TopologicalSpace X] {f h : X → E} {s : Set X}
    (hf : ContinuousOn f s) (hh : ContinuousOn h s) :
    ContinuousOn (fun z => chartMetricInner (I := I) g α y (f z) (h z)) s :=
  ((continuous_chartMetricInner_pair (I := I) g α y).comp_continuousOn
    (hf.prodMk hh)).congr (fun _ _ => rfl)

end ChartMetricInnerContinuous

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **The `t = 0` second time-derivative of the squared radial distance, as an
explicit algebraic form in `(a, w)`.** With `a = φ_p(q)` the chart position, `w` the chart
velocity, and `finv` the local inverse of `φ_p ∘ exp_p`, this is do Carmo's
`∂²F/∂t²(0, q, v) = 2⟨u''(0), u(0)⟩_p + 2|u'(0)|²_p`, where
`u(0) = finv(a)`, `u'(0) = Dfinv(a)(w)`,
`u''(0) = D²finv(a)(w, w) + Dfinv(a)(x''(0))` and
`x''(0) = (geodesicSprayCoord g p a w).2 = -Γ_a(w, w)` is the geodesic acceleration read in
the chart at `p`. -/
def secondDerivChartForm (g : RiemannianMetric I M) (p : M) (finv : E → E)
    (a w : E) : ℝ :=
  2 * chartMetricInner (I := I) g p (extChartAt I p p)
        ((fderiv ℝ (fderiv ℝ finv) a w) w
          + fderiv ℝ finv a (geodesicSprayCoord (I := I) g p a w).2)
        (finv a)
    + 2 * chartMetricInner (I := I) g p (extChartAt I p p)
        (fderiv ℝ finv a w) (fderiv ℝ finv a w)

/-- **Math.** **Degree-2 homogeneity of the second time-derivative form in the velocity.**
`secondDerivChartForm g p finv a (c • w) = c² · secondDerivChartForm g p finv a w`. This is
do Carmo's reduction to unit speed (the homogeneity Lemma 2.6): every building block scales —
`Dfinv(a)(c w) = c·Dfinv(a)(w)`, `D²finv(a)(c w)(c w) = c²·D²finv(a)(w)(w)`, and the geodesic
acceleration `x''(0) = (spray(a, c w))₂ = c²·(spray(a, w))₂`
(`geodesicSprayCoord_smul_velocity`) — and the chart Gram form is bilinear, so both summands
acquire a factor `c²`. -/
theorem secondDerivChartForm_smul_velocity (g : RiemannianMetric I M) (p : M)
    (finv : E → E) (a w : E) (c : ℝ) :
    secondDerivChartForm (I := I) g p finv a (c • w)
      = (c * c) * secondDerivChartForm (I := I) g p finv a w := by
  have hD2 : (fderiv ℝ (fderiv ℝ finv) a (c • w)) (c • w)
      = (c * c) • ((fderiv ℝ (fderiv ℝ finv) a w) w) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
  have hspray2 : (geodesicSprayCoord (I := I) g p a (c • w)).2
      = (c * c) • (geodesicSprayCoord (I := I) g p a w).2 := by
    rw [geodesicSprayCoord_smul_velocity]
  have hDspray : fderiv ℝ finv a (geodesicSprayCoord (I := I) g p a (c • w)).2
      = (c * c) • fderiv ℝ finv a (geodesicSprayCoord (I := I) g p a w).2 := by
    rw [hspray2, map_smul]
  have hu' : fderiv ℝ finv a (c • w) = c • fderiv ℝ finv a w := by
    rw [map_smul]
  unfold secondDerivChartForm
  rw [hD2, hDspray, ← smul_add, hu', chartMetricInner_smul_left,
    chartMetricInner_smul_left, chartMetricInner_smul_right]
  ring

/-- **Math.** **Joint continuity of `∂²F/∂t²(0, q, v)` in the moving base point.** If `finv`
is `C²` on an open set `S` contained in the chart target at `p`, then the explicit second
time-derivative form `secondDerivChartForm g p finv` is jointly continuous in `(a, w)` on
`S ×ˢ univ`. This is the residual joint-continuity step of `lem:dc-ch3-4-1`: continuity
follows from continuity of `finv`, its first two derivatives, and the smooth geodesic spray,
with no time integration. -/
theorem continuousOn_secondDerivChartForm (g : RiemannianMetric I M) (p : M)
    {finv : E → E} {S : Set E} (hS : IsOpen S)
    (hSsub : S ⊆ (extChartAt I p).target) (hfinv : ContDiffOn ℝ 2 finv S) :
    ContinuousOn (fun z : E × E => secondDerivChartForm (I := I) g p finv z.1 z.2)
      (S ×ˢ (univ : Set E)) := by
  -- continuity of finv, Dfinv, D²finv on S
  have hcfinv : ContinuousOn finv S := hfinv.continuousOn
  have hcD : ContinuousOn (fderiv ℝ finv) S :=
    hfinv.continuousOn_fderiv_of_isOpen hS (by norm_num)
  have hD1 : ContDiffOn ℝ 1 (fderiv ℝ finv) S :=
    hfinv.fderiv_of_isOpen hS (by norm_num)
  have hcD2 : ContinuousOn (fderiv ℝ (fderiv ℝ finv)) S :=
    hD1.continuousOn_fderiv_of_isOpen hS (by norm_num)
  -- the spray is smooth on the chart target × univ, hence continuous on S × univ
  have hspray : ContinuousOn
      (fun z : E × E => geodesicSprayCoord (I := I) g p z.1 z.2)
      (S ×ˢ (univ : Set E)) :=
    ((contDiffOn_geodesicSprayCoord_prod (I := I) g p).continuousOn).mono
      (prod_mono hSsub (subset_refl _))
  -- pointwise continuity building blocks on S × univ
  have hfst : ContinuousOn (fun z : E × E => z.1) (S ×ˢ (univ : Set E)) :=
    continuousOn_fst
  have hsnd : ContinuousOn (fun z : E × E => z.2) (S ×ˢ (univ : Set E)) :=
    continuousOn_snd
  have ha : ContinuousOn (fun z : E × E => finv z.1) (S ×ˢ (univ : Set E)) :=
    hcfinv.comp hfst (fun z hz => hz.1)
  have hDa : ContinuousOn (fun z : E × E => fderiv ℝ finv z.1) (S ×ˢ (univ : Set E)) :=
    hcD.comp hfst (fun z hz => hz.1)
  have hD2a : ContinuousOn
      (fun z : E × E => fderiv ℝ (fderiv ℝ finv) z.1) (S ×ˢ (univ : Set E)) :=
    hcD2.comp hfst (fun z hz => hz.1)
  -- u'(0) = Dfinv(a)(w)
  have hu' : ContinuousOn (fun z : E × E => fderiv ℝ finv z.1 z.2)
      (S ×ˢ (univ : Set E)) := hDa.clm_apply hsnd
  -- x''(0) = spray₂(a, w)
  have hx'' : ContinuousOn (fun z : E × E => (geodesicSprayCoord (I := I) g p z.1 z.2).2)
      (S ×ˢ (univ : Set E)) := hspray.snd
  -- D²finv(a)(w)(w)
  have hD2w : ContinuousOn
      (fun z : E × E => fderiv ℝ (fderiv ℝ finv) z.1 z.2)
      (S ×ˢ (univ : Set E)) := hD2a.clm_apply hsnd
  have hD2ww : ContinuousOn
      (fun z : E × E => (fderiv ℝ (fderiv ℝ finv) z.1 z.2) z.2)
      (S ×ˢ (univ : Set E)) := hD2w.clm_apply hsnd
  -- Dfinv(a)(x''(0))
  have hDx'' : ContinuousOn (fun z : E × E => fderiv ℝ finv z.1
      (geodesicSprayCoord (I := I) g p z.1 z.2).2) (S ×ˢ (univ : Set E)) :=
    hDa.clm_apply hx''
  -- u''(0)
  have hu'' : ContinuousOn (fun z : E × E =>
      (fderiv ℝ (fderiv ℝ finv) z.1 z.2) z.2
        + fderiv ℝ finv z.1 (geodesicSprayCoord (I := I) g p z.1 z.2).2)
      (S ×ˢ (univ : Set E)) := hD2ww.add hDx''
  -- assemble the two inner products via the generic bilinear-continuity helper
  have hterm1 := continuousOn_chartMetricInner_comp (I := I) (α := p)
    (y := extChartAt I p p) g hu'' ha
  have hterm2 := continuousOn_chartMetricInner_comp (I := I) (α := p)
    (y := extChartAt I p p) g hu' hu'
  refine ((hterm1.const_smul (2 : ℝ)).add (hterm2.const_smul (2 : ℝ))).congr ?_
  intro z _
  simp only [secondDerivChartForm, smul_eq_mul, Pi.add_apply]

/-- **Math.** **The second time-derivative is strictly positive at the center `q = p`.**
At the reference point `q = p` the geodesic through `p` with velocity `v ≠ 0` is the radial
ray, so `u(0) = finv(φ_p p) = 0` kills the `⟨u''(0), u(0)⟩` term and
`∂²F/∂t²(0, p, v) = 2|Dfinv(φ_p p)(w)|²_p`. Since `Dfinv(φ_p p)` is injective (the derivative
of the local inverse of the exponential chart reading is a linear isomorphism) and the chart
Gram form at `p` is positive definite, this is strictly positive. This is do Carmo's
strict-minimum seed `∂²F/∂t²(0, p, v) = 2|v|² = 2 > 0`. -/
theorem secondDerivChartForm_extChartAt_self_pos (g : RiemannianMetric I M) (p : M)
    (finv : E → E) (h0 : finv (extChartAt I p p) = 0)
    (hinj : Function.Injective ⇑(fderiv ℝ finv (extChartAt I p p)))
    {w : E} (hw : w ≠ 0) :
    0 < secondDerivChartForm (I := I) g p finv (extChartAt I p p) w := by
  have hDw : fderiv ℝ finv (extChartAt I p p) w ≠ 0 := by
    intro hc
    exact hw (hinj (hc.trans (map_zero _).symm))
  have hpos : 0 < chartMetricInner (I := I) g p (extChartAt I p p)
      (fderiv ℝ finv (extChartAt I p p) w) (fderiv ℝ finv (extChartAt I p p) w) :=
    chartMetricInner_extChartAt_self_pos (I := I) g p hDw
  unfold secondDerivChartForm
  rw [h0, chartMetricInner_zero_right]
  linarith

/-- **Math.** **Packaged `C²` exponential inverse with an invertible derivative at `p`.**
There is a `C²` local inverse `finv` of `φ_p ∘ exp_p`, defined on an open set `S` inside the
chart target and containing `φ_p(p)`, that sends `φ_p(p)` to `0` and whose derivative at
`φ_p(p)` is a linear isomorphism (in particular injective). The injectivity follows from the
inverse function theorem: `finv ∘ (φ_p ∘ exp_p) = id` near `0`, and `φ_p ∘ exp_p` has an
invertible strict derivative at `0`, so `D finv(φ_p p) = (D(φ_p∘exp_p)(0))⁻¹`. This packages
exactly the `finv` data consumed by `secondDerivChartForm` and its positivity/continuity. -/
theorem exists_c2_expMapInv_injDeriv (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (S : Set E),
      IsOpen S ∧ S ⊆ (extChartAt I p).target ∧ extChartAt I p p ∈ S ∧
      ContDiffOn ℝ 2 finv S ∧
      finv (extChartAt I p p) = 0 ∧
      Function.Injective ⇑(fderiv ℝ finv (extChartAt I p p)) ∧
      (∃ εL : ℝ, 0 < εL ∧ ∀ w : E, ‖w‖ < εL →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) := by
  obtain ⟨ε, hε, hdom, hsrc, hinjε, hopen_exp, hcd, hopen_f, finv, hfinvleft, hfinvC2⟩ :=
    exists_c2_local_diffeomorphism_expMap (I := I) g p
  set f : E → E :=
    fun w => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)) with hfdef
  have hf0 : f 0 = extChartAt I p p :=
    congrArg (fun m => extChartAt I p m) (expMap_zero (I := I) g p)
  refine ⟨finv, f '' ball (0 : E) ε, hopen_f, ?_, ?_, hfinvC2, ?_, ?_,
    ⟨ε, hε, fun w hw => hfinvleft w hw⟩⟩
  · -- S ⊆ chart target
    rintro y ⟨w, hw, rfl⟩
    have hsrcw : expMap (I := I) g p (w : TangentSpace I p) ∈ (extChartAt I p).source := by
      rw [extChartAt_source]
      exact hsrc w (mem_ball_zero_iff.mp hw)
    exact (extChartAt I p).map_source hsrcw
  · -- φ_p(p) ∈ S
    exact ⟨0, mem_ball_self hε, hf0⟩
  · -- finv(φ_p p) = 0
    have h := hfinvleft 0 (by simpa using hε)
    rw [← hf0]
    exact h
  · -- fderiv finv (φ_p p) injective
    obtain ⟨ρ, hρ, -, -, hequiv⟩ :=
      exists_hasStrictFDerivAt_equiv_extChartAt_expMap_ball (I := I) g p
    obtain ⟨D₀, hD₀⟩ := hequiv 0 (by simpa using hρ)
    have hfderiv : HasFDerivAt f (↑D₀ : E →L[ℝ] E) 0 := hD₀.hasFDerivAt
    have hf0mem : f 0 ∈ f '' ball (0 : E) ε := ⟨0, mem_ball_self hε, rfl⟩
    have hfinvdiff : HasFDerivAt finv (fderiv ℝ finv (f 0)) (f 0) :=
      ((hfinvC2.contDiffAt (hopen_f.mem_nhds hf0mem)).differentiableAt
        (by norm_num)).hasFDerivAt
    have hcompd : HasFDerivAt (finv ∘ f) ((fderiv ℝ finv (f 0)).comp ↑D₀) 0 :=
      hfinvdiff.comp 0 hfderiv
    have heq : (finv ∘ f) =ᶠ[𝓝 (0 : E)] id := by
      filter_upwards [ball_mem_nhds (0 : E) hε] with w hw
      simp only [Function.comp_apply, id_eq, hfdef]
      exact hfinvleft w (mem_ball_zero_iff.mp hw)
    have hidd : HasFDerivAt (finv ∘ f) (ContinuousLinearMap.id ℝ E) 0 :=
      (hasFDerivAt_id (0 : E)).congr_of_eventuallyEq heq
    have hcomp : (fderiv ℝ finv (f 0)).comp (↑D₀ : E →L[ℝ] E)
        = ContinuousLinearMap.id ℝ E := hcompd.unique hidd
    have hid : ∀ z, fderiv ℝ finv (f 0) (D₀ z) = z := fun z => by
      have h := ContinuousLinearMap.ext_iff.mp hcomp z
      simpa using h
    have hAeq : ∀ y, fderiv ℝ finv (f 0) y = D₀.symm y := fun y => by
      have := hid (D₀.symm y)
      rwa [D₀.apply_symm_apply] at this
    have hAinj : Function.Injective ⇑(fderiv ℝ finv (f 0)) := by
      have hcoe : ⇑(fderiv ℝ finv (f 0)) = ⇑D₀.symm := funext hAeq
      rw [hcoe]
      exact D₀.symm.injective
    rwa [hf0] at hAinj

/-- **Math.** **do Carmo's neighborhood with a strictly positive Hessian.** There is a `C²`
exponential inverse `finv` and an open neighborhood `V` of `φ_p(p)` inside the chart target,
on which the second time-derivative form is strictly positive for every Euclidean-unit chart
velocity: `∂²F/∂t²(0, q, v) > 0` for all `q` reading into `V` and all `‖w‖ = 1`. This is do
Carmo Ch. 3, §4, Lemma 4.1's "hence there is a neighborhood `V ⊂ W` of `p` with
`∂²F/∂t²(0, q, v) > 0` for all `q ∈ V`, `|v| = 1`" — the strict positivity at the center `p`
(`secondDerivChartForm_extChartAt_self_pos`) propagated to a neighborhood by joint continuity
(`continuousOn_secondDerivChartForm`) and compactness of the unit sphere (the tube lemma). -/
theorem exists_secondDerivChartForm_pos_nhds (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (V : Set E),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧ ContDiffOn ℝ 2 finv V ∧
      (∀ a ∈ V, ∀ w : E, ‖w‖ = 1 → 0 < secondDerivChartForm (I := I) g p finv a w) ∧
      (∃ εL : ℝ, 0 < εL ∧ ∀ w : E, ‖w‖ < εL →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) := by
  obtain ⟨finv, S, hSopen, hSsub, hpS, hfinvC2, hf0, hinj, hleftinv⟩ :=
    exists_c2_expMapInv_injDeriv (I := I) g p
  set a₀ : E := extChartAt I p p with ha₀
  set G : E × E → ℝ := fun z => secondDerivChartForm (I := I) g p finv z.1 z.2 with hGdef
  have hGcont : ContinuousOn G (S ×ˢ (univ : Set E)) :=
    continuousOn_secondDerivChartForm (I := I) g p hSopen hSsub hfinvC2
  have hNopen : IsOpen ((S ×ˢ (univ : Set E)) ∩ G ⁻¹' Set.Ioi (0 : ℝ)) :=
    hGcont.isOpen_inter_preimage (hSopen.prod isOpen_univ) isOpen_Ioi
  have hKcompact : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hsub : ({a₀} ×ˢ Metric.sphere (0 : E) 1) ⊆
      ((S ×ˢ (univ : Set E)) ∩ G ⁻¹' Set.Ioi (0 : ℝ)) := by
    rintro ⟨a, w⟩ ⟨ha, hw⟩
    rw [mem_singleton_iff] at ha
    subst ha
    have hwne : w ≠ 0 := by
      intro h
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at hw
      exact one_ne_zero hw.symm
    exact ⟨⟨hpS, mem_univ _⟩,
      secondDerivChartForm_extChartAt_self_pos (I := I) g p finv hf0 hinj hwne⟩
  obtain ⟨u, v, hu_open, hv_open, hau, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hKcompact hNopen hsub
  refine ⟨finv, u ∩ S, hu_open.inter hSopen,
    ⟨hau (mem_singleton_iff.mpr rfl), hpS⟩, inter_subset_right.trans hSsub, hf0,
    hfinvC2.mono inter_subset_right, ?_, hleftinv⟩
  intro a ha w hw
  have hmem : (a, w) ∈ (S ×ˢ (univ : Set E)) ∩ G ⁻¹' Set.Ioi (0 : ℝ) :=
    huv ⟨ha.1, hKv (mem_sphere_zero_iff_norm.mpr hw)⟩
  exact hmem.2

/-- **Math.** **Strict positivity of the second time-derivative form for every nonzero chart
velocity, near the center.** Combining the Euclidean-unit positivity
(`exists_secondDerivChartForm_pos_nhds`) with the degree-2 homogeneity
(`secondDerivChartForm_smul_velocity`), the form `∂²F/∂t²(0, q, v)` is strictly positive for
*every* nonzero chart velocity `w ≠ 0` at every base point reading into the neighborhood `V`:
writing `w = ‖w‖ • (‖w‖⁻¹ • w)` with `‖w‖⁻¹ • w` on the unit sphere, the homogeneity factor
`‖w‖² > 0`. This removes the unit-speed restriction — do Carmo's strict-minimum condition
holds for every base point of `V` and every nonzero geodesic velocity. -/
theorem exists_secondDerivChartForm_pos_nhds_ne (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (V : Set E),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧ ContDiffOn ℝ 2 finv V ∧
      (∀ a ∈ V, ∀ w : E, w ≠ 0 → 0 < secondDerivChartForm (I := I) g p finv a w) ∧
      (∃ εL : ℝ, 0 < εL ∧ ∀ w : E, ‖w‖ < εL →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) := by
  obtain ⟨finv, V, hVopen, hpV, hVsub, hf0, hfinvC2, hpos, hleftinv⟩ :=
    exists_secondDerivChartForm_pos_nhds (I := I) g p
  refine ⟨finv, V, hVopen, hpV, hVsub, hf0, hfinvC2, ?_, hleftinv⟩
  intro a ha w hw
  have hcpos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hwscale : w = ‖w‖ • (‖w‖⁻¹ • w) := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hcpos), one_smul]
  have hw₀norm : ‖(‖w‖⁻¹ • w)‖ = 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hcpos,
      inv_mul_cancel₀ (ne_of_gt hcpos)]
  rw [hwscale, secondDerivChartForm_smul_velocity]
  exact mul_pos (mul_pos hcpos hcpos) (hpos a ha _ hw₀norm)

end Exponential

end Riemannian

end

import MorganTianLib.Ch02.FlowIsometryBridges
import MorganTianLib.Ch02.FlowVariation
import MorganTianLib.Ch02.FlowContinuity
import MorganTianLib.Ch02.StrictFDerivC1

/-!
# Morgan–Tian Ch. 2 — the gradient flow is a local isometry

Blueprint `lem:parallel-gradient-flow`(4), local step. Under the Bochner
package the flow `θ` of the gradient field `(∇f)^*` preserves the metric,
locally in space and time: near every point `z` there are a time `δ > 0` and
a neighbourhood `V ∋ z` such that for every `|s| ≤ δ` and `x ∈ V` the flow
map `θ_s` is differentiable at `x` and its differential preserves the
Riemannian inner product.

The proof runs entirely in the chart at `z`:

* the chart representation `V̂` of the gradient field (and its negation, for
  backward time) is `C¹` on the chart target and satisfies the fixed-chart
  parallel identity (`ChartGradientParallel`, `FlowIsometryBridges`);
* its local flow is strictly differentiable in the initial condition, with
  derivative solving the variational equation (`FlowVariation`);
* by uniqueness of integral curves, `θ_s` agrees near `x` with the chart
  flow pushed through `φ⁻¹`, so `dθ_s = dφ⁻¹ ∘ D_s ∘ dφ`;
* the chart Gram product of variational solutions is constant in time
  (`chartMetricInner_variational_eq_left`), and the chart-derivative bridges
  identify the endpoints with the intrinsic inner products at `x` and `θ_s x`.

Main declarations:

* `metricPreserving_of_localFlowRep` — the core: a manifold map locally
  represented by a `C¹`-dependent chart flow of a parallel field is
  differentiable and metric-preserving at the centre.
* `exists_flowIsometryBoxAt` — the local isometry step for the gradient
  flow, both time directions.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Function Metric Riemannian Riemannian.Geodesic
open Riemannian.FlowDependence
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ### The core: metric preservation of a chart-flow representative -/

/-- **Math.** **The core metric-preservation step**: let `W` be a chart field
at `z` satisfying the parallel identity, with a uniform local flow `Z` that
is strictly differentiable in its initial condition (with variational
derivative `D`). If a manifold map `Θ` agrees near `x` with the time-`τ`
chart flow pushed through the chart inverse, then `Θ` is differentiable at
`x` and its differential preserves the Riemannian inner product:
`⟨dΘ(v), dΘ(w)⟩_{Θ(x)} = ⟨v, w⟩_x`. The differential factors as
`dφ⁻¹ ∘ D_τ ∘ dφ`, and the chart Gram product of variational solutions is
constant in time. Blueprint `lem:parallel-gradient-flow`(4). -/
theorem metricPreserving_of_localFlowRep
    (g : RiemannianMetric I M) (z : M) {W : E → E}
    (hpar : ∀ y ∈ (extChartAt I z).target, ∀ w : E,
      fderiv ℝ W y w
        = - Geodesic.chartChristoffelContraction (I := I) g z w (W y) y)
    {r ε T : ℝ} {Z : E → ℝ → E} {σ : E → C(Set.Icc (0:ℝ) T, E)} (hT : 0 < T)
    (hTε : T < ε)
    (hflow : ∀ ζ ∈ closedBall (extChartAt I z z) r, Z ζ 0 = ζ ∧
      (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z ζ) (W (Z ζ t)) (Icc (-ε) ε) t) ∧
      (∀ t ∈ Icc (-ε) ε, Z ζ t ∈ (extChartAt I z).target))
    (hσ_ball : ∀ ζ ∈ closedBall (extChartAt I z z) r,
      ∀ t : Set.Icc (0:ℝ) T, σ ζ t = Z ζ t.1)
    (hderiv : ∀ ζ ∈ ball (extChartAt I z z) r,
      ∃ (D : E →L[ℝ] C(Set.Icc (0:ℝ) T, E))
        (A₀ : C(Set.Icc (0:ℝ) T, E →L[ℝ] E)),
        (∀ t : Set.Icc (0:ℝ) T, A₀ t = fderiv ℝ W (σ ζ t)) ∧
        (∀ v : E, D v - intervalPrimitive hT.le (postcompCurve A₀ (D v))
          = ContinuousMap.const _ v) ∧
        HasStrictFDerivAt σ D ζ)
    {x : M} (hxsrc : x ∈ (chartAt H z).source)
    (hxball : extChartAt I z x ∈ ball (extChartAt I z z) r)
    {τ : ℝ} (hτ : τ ∈ Icc (0:ℝ) T) {Θ : M → M}
    (hΘ : Θ =ᶠ[𝓝 x]
      fun x' => (extChartAt I z).symm (Z (extChartAt I z x') τ)) :
    MDifferentiableAt I I Θ x ∧
    ∀ v w : TangentSpace I x,
      g.metricInner (Θ x) (mfderiv I I Θ x v) (mfderiv I I Θ x w)
        = g.metricInner x v w := by
  classical
  have hxc : extChartAt I z x ∈ closedBall (extChartAt I z z) r :=
    ball_subset_closedBall hxball
  have hIccsub : Icc (0:ℝ) T ⊆ Icc (-ε) ε := fun t ht =>
    ⟨le_trans (neg_nonpos.mpr (hT.le.trans hTε.le)) ht.1, ht.2.trans hTε.le⟩
  set τ' : Set.Icc (0:ℝ) T := ⟨τ, hτ⟩ with hτ'_def
  obtain ⟨D, A₀, hA₀, hD, hstrict⟩ := hderiv _ hxball
  -- membership of the trajectory in the chart target
  have hZmem : ∀ t ∈ Icc (0:ℝ) T,
      Z (extChartAt I z x) t ∈ (extChartAt I z).target := fun t ht =>
    (hflow _ hxc).2.2 t (hIccsub ht)
  have hZτmem : Z (extChartAt I z x) τ ∈ (extChartAt I z).target := hZmem τ hτ
  -- the time-`τ` flow map is differentiable at the chart image of `x`
  have hστ : HasStrictFDerivAt (fun ζ => σ ζ τ')
      ((ContinuousMap.evalCLM ℝ τ').comp D) (extChartAt I z x) :=
    (ContinuousMap.evalCLM ℝ τ').hasStrictFDerivAt.comp _ hstrict
  have hZτ_fd : HasFDerivAt (fun ζ => Z ζ τ)
      ((ContinuousMap.evalCLM ℝ τ').comp D) (extChartAt I z x) := by
    refine hστ.hasFDerivAt.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ball.mem_nhds hxball] with ζ hζ
    exact (hσ_ball ζ (ball_subset_closedBall hζ) τ').symm
  -- differentiability of the pushed-through composition, hence of `Θ`
  have hrange : Set.range (I : H → E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  have hmdφ : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I z) x :=
    mdifferentiableAt_extChartAt hxsrc
  have hmdZ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun ζ => Z ζ τ)
      (extChartAt I z x) :=
    mdifferentiableAt_iff_differentiableAt.mpr hZτ_fd.differentiableAt
  have hmdsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I z).symm
      (Z (extChartAt I z x) τ) := by
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact mdifferentiableWithinAt_extChartAt_symm hZτmem
  have hmdinner : MDifferentiableAt I 𝓘(ℝ, E)
      (fun x' => Z (extChartAt I z x') τ) x := hmdZ.comp x hmdφ
  have hmdcomp : MDifferentiableAt I I
      (fun x' => (extChartAt I z).symm (Z (extChartAt I z x') τ)) x :=
    hmdsymm.comp x hmdinner
  have hmdΘ : MDifferentiableAt I I Θ x := hmdcomp.congr_of_eventuallyEq hΘ
  refine ⟨hmdΘ, ?_⟩
  -- the differential factors through the chart
  have hmf : ∀ v : TangentSpace I x, mfderiv I I Θ x v
      = mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm (Z (extChartAt I z x) τ)
          (((ContinuousMap.evalCLM ℝ τ').comp D)
            (tangentCoordChange I x z x v)) := by
    intro v
    have h1 : mfderiv I I Θ x
        = mfderiv I I (fun x' => (extChartAt I z).symm
            (Z (extChartAt I z x') τ)) x := hΘ.mfderiv_eq
    have h2 : mfderiv I I (fun x' => (extChartAt I z).symm
          (Z (extChartAt I z x') τ)) x
        = (mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm
            (Z (extChartAt I z x) τ)).comp
          (mfderiv I 𝓘(ℝ, E) (fun x' => Z (extChartAt I z x') τ) x) :=
      mfderiv_comp x hmdsymm hmdinner
    have h3 : mfderiv I 𝓘(ℝ, E) (fun x' => Z (extChartAt I z x') τ) x
        = (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun ζ => Z ζ τ) (extChartAt I z x)).comp
          (mfderiv I 𝓘(ℝ, E) (extChartAt I z) x) := mfderiv_comp x hmdZ hmdφ
    have h4 : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun ζ => Z ζ τ) (extChartAt I z x)
        = (ContinuousMap.evalCLM ℝ τ').comp D := by
      rw [mfderiv_eq_fderiv]
      exact hZτ_fd.fderiv
    rw [h1, h2, h3, h4]
    show mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm (Z (extChartAt I z x) τ)
        (((ContinuousMap.evalCLM ℝ τ').comp D)
          ((mfderiv I 𝓘(ℝ, E) (extChartAt I z) x) v)) = _
    rw [mfderiv_extChartAt_apply_eq_tangentCoordChange hxsrc v]
  intro v w
  -- read the endpoint pairing through the chart
  have hb : (extChartAt I z).symm (Z (extChartAt I z x) τ)
      ∈ (chartAt H z).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I z).map_target hZτmem
  have hΘx : Θ x = (extChartAt I z).symm (Z (extChartAt I z x) τ) :=
    hΘ.self_of_nhds
  have hread : ∀ a : E, mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm
        (Z (extChartAt I z x) τ) a
      = (trivializationAt E (TangentSpace I) z).symm
          ((extChartAt I z).symm (Z (extChartAt I z x) τ)) a :=
    fun a => mfderiv_extChartAt_symm_apply_eq_trivializationAt_symm hZτmem a
  rw [hmf v, hmf w, hΘx, hread, hread,
    ← chartMetricInner_extChartAt_eq_metricInner (I := I) g z hb,
    (extChartAt I z).right_inv hZτmem]
  -- the variational solutions through the chart readings of `v` and `w`
  obtain ⟨dv, hdv_agree, hdv_deriv⟩ :=
    exists_extension_hasDerivAt_variational hT (hD (tangentCoordChange I x z x v))
  obtain ⟨dw, hdw_agree, hdw_deriv⟩ :=
    exists_extension_hasDerivAt_variational hT (hD (tangentCoordChange I x z x w))
  -- the flow line has genuine two-sided derivatives on `[0, T]`
  have hu_deriv : ∀ t ∈ Icc (0:ℝ) T,
      HasDerivAt (fun t' => Z (extChartAt I z x) t')
        (W (Z (extChartAt I z x) t)) t := by
    intro t ht
    have h := (hflow _ hxc).2.1 t (hIccsub ht)
    exact h.hasDerivAt (Icc_mem_nhds
      (lt_of_lt_of_le (neg_lt_zero.mpr (hT.trans_le hTε.le)) ht.1)
      (lt_of_le_of_lt ht.2 hTε))
  -- the extensions solve the variational equation along the flow line
  have hdv_var : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt dv
      (fderiv ℝ W (Z (extChartAt I z x) t) (dv t)) t := by
    intro t ht
    have h := hdv_deriv t ht
    rw [Set.projIcc_of_mem hT.le ht, hA₀ ⟨t, ht⟩,
      hσ_ball _ hxc ⟨t, ht⟩, ← hdv_agree ⟨t, ht⟩] at h
    simpa using h
  have hdw_var : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt dw
      (fderiv ℝ W (Z (extChartAt I z x) t) (dw t)) t := by
    intro t ht
    have h := hdw_deriv t ht
    rw [Set.projIcc_of_mem hT.le ht, hA₀ ⟨t, ht⟩,
      hσ_ball _ hxc ⟨t, ht⟩, ← hdw_agree ⟨t, ht⟩] at h
    simpa using h
  -- constancy of the chart Gram product along the variational pair
  have hconst := chartMetricInner_variational_eq_left (I := I) g z hpar
    hZmem hu_deriv hdv_var hdw_var hτ
  -- identify the two endpoints
  have hzero_mem : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_refl 0, hT.le⟩
  have hdv0 : dv 0 = tangentCoordChange I x z x v := by
    have h0 := congrFun (congrArg
      (fun (φ : C(Set.Icc (0:ℝ) T, E)) => (φ : _ → E))
      (hD (tangentCoordChange I x z x v))) ⟨0, hzero_mem⟩
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply,
      intervalPrimitive_apply] at h0
    rw [hdv_agree ⟨0, hzero_mem⟩]
    simpa using h0
  have hdw0 : dw 0 = tangentCoordChange I x z x w := by
    have h0 := congrFun (congrArg
      (fun (φ : C(Set.Icc (0:ℝ) T, E)) => (φ : _ → E))
      (hD (tangentCoordChange I x z x w))) ⟨0, hzero_mem⟩
    simp only [ContinuousMap.sub_apply, ContinuousMap.const_apply,
      intervalPrimitive_apply] at h0
    rw [hdw_agree ⟨0, hzero_mem⟩]
    simpa using h0
  have hdvτ : dv τ = ((ContinuousMap.evalCLM ℝ τ').comp D)
      (tangentCoordChange I x z x v) := hdv_agree τ'
  have hdwτ : dw τ = ((ContinuousMap.evalCLM ℝ τ').comp D)
      (tangentCoordChange I x z x w) := hdw_agree τ'
  have hZ0 : Z (extChartAt I z x) 0 = extChartAt I z x := (hflow _ hxc).1
  rw [← hdvτ, ← hdwτ, hconst, hZ0, hdv0, hdw0,
    chartMetricInner_tangentCoordChange (I := I) g hxsrc v w]

/-! ### The local isometry step for the gradient flow -/

/-- **Math.** **The gradient flow is a local isometry** (blueprint
`lem:parallel-gradient-flow`(4), local step): under the Bochner package,
near every point `z` there are `δ > 0` and an open `V ∋ z` such that for all
`|s| ≤ δ` and `x ∈ V` the flow map `θ_s` of the gradient field is **`C¹`** at
`x` with metric-preserving differential. The `C¹` regularity comes from the
strict differentiability of the chart flow at every point of the flow ball
(`FlowVariation`) via `contDiffOn_one_of_hasStrictFDerivAt`. Both time
directions are covered, by the flow of the chart field and of its negation. -/
theorem exists_flowIsometryBoxAt
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) (z : M) :
    ∃ (δ : ℝ) (V : Set M), 0 < δ ∧ IsOpen V ∧ z ∈ V ∧
      ∀ x ∈ V, ∀ s : ℝ, |s| ≤ δ →
        ContMDiffAt I I 1
          (smoothVectorFieldFlow (gradientField g f hf) hex s) x ∧
        ∀ v w : TangentSpace I x,
          g.metricInner (smoothVectorFieldFlow (gradientField g f hf) hex s x)
            (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s) x v)
            (mfderiv I I (smoothVectorFieldFlow (gradientField g f hf) hex s) x w)
          = g.metricInner x v w := by
  classical
  have hΩ : IsOpen (extChartAt I z).target := isOpen_extChartAt_target (I := I) z
  have hz₀ : extChartAt I z z ∈ (extChartAt I z).target := mem_extChartAt_target z
  -- the chart field of the gradient, its negation, and their `C¹` regularity
  have hV1 : ContDiffOn ℝ 1
      (fieldChartRep (I := I) z (gradientField g f hf)) (extChartAt I z).target :=
    (contDiffOn_fieldChartRep_gradientField g hf z).of_le (by exact_mod_cast le_top)
  have hV1neg : ContDiffOn ℝ 1
      (fun y => -(fieldChartRep (I := I) z (gradientField g f hf) y))
      (extChartAt I z).target := hV1.neg
  -- the two flow packages, forward and backward
  obtain ⟨rp, εp, Tp, Zp, σp, hTp, hrp, hεp, hTεp, hflowp, hZcp, hσbp, hderp⟩ :=
    exists_localFlow_hasStrictFDerivAt hΩ hz₀ hV1
  obtain ⟨rm, εm, Tm, Zm, σm, hTm, hrm, hεm, hTεm, hflowm, hZcm, hσbm, hderm⟩ :=
    exists_localFlow_hasStrictFDerivAt hΩ hz₀ hV1neg
  -- the parallel identities for the two fields
  have hparp : ∀ y ∈ (extChartAt I z).target, ∀ w : E,
      fderiv ℝ (fieldChartRep (I := I) z (gradientField g f hf)) y w
        = - Geodesic.chartChristoffelContraction (I := I) g z w
            (fieldChartRep (I := I) z (gradientField g f hf) y) y :=
    fun y hy w =>
      fderiv_fieldChartRep_gradientField_of_bochner g hLC hf hgrad hharm hric z hy w
  have hparm : ∀ y ∈ (extChartAt I z).target, ∀ w : E,
      fderiv ℝ (fun y' => -(fieldChartRep (I := I) z (gradientField g f hf) y')) y w
        = - Geodesic.chartChristoffelContraction (I := I) g z w
            ((fun y' => -(fieldChartRep (I := I) z (gradientField g f hf) y')) y) y :=
    fun y hy w =>
      fderiv_neg_fieldChartRep_gradientField_of_bochner g hLC hf hgrad hharm hric
        z hy w
  -- the uniform time and the flow-box neighbourhood
  set δ : ℝ := min Tp Tm with hδ_def
  have hδ : 0 < δ := lt_min hTp hTm
  set ρ : ℝ := min rp rm with hρ_def
  have hρ : 0 < ρ := lt_min hrp hrm
  set V : Set M := (extChartAt I z).source
    ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) ρ with hV_def
  have hVopen : IsOpen V := isOpen_extChartAt_preimage' z isOpen_ball
  refine ⟨δ, V, hδ, hVopen, ⟨mem_extChartAt_source z, mem_ball_self hρ⟩, ?_⟩
  intro x hx s hs
  have hxsrc : x ∈ (chartAt H z).source := by
    rw [← extChartAt_source (I := I)]
    exact hx.1
  have hxballp : extChartAt I z x ∈ ball (extChartAt I z z) rp :=
    ball_subset_ball (min_le_left _ _) hx.2
  have hxballm : extChartAt I z x ∈ ball (extChartAt I z z) rm :=
    ball_subset_ball (min_le_right _ _) hx.2
  -- regularity of the gradient section, for uniqueness of integral curves
  have hX1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q => (⟨q, gradientField g f hf q⟩ : TangentBundle I M)) := fun p =>
    ((gradientField g f hf).smooth p).of_le (by norm_num)
  rcases le_or_gt 0 s with hs0 | hs0
  · -- forward time: the flow of the chart field
    have hsT : s ∈ Icc (0:ℝ) Tp := ⟨hs0, le_trans (le_of_abs_le hs) (min_le_left _ _)⟩
    have hΘ : (smoothVectorFieldFlow (gradientField g f hf) hex s) =ᶠ[𝓝 x]
        fun x' => (extChartAt I z).symm (Zp (extChartAt I z x') s) := by
      filter_upwards [hVopen.mem_nhds hx] with x' hx'
      have hx'src : x' ∈ (extChartAt I z).source := hx'.1
      have hx'c : extChartAt I z x' ∈ closedBall (extChartAt I z z) rp :=
        ball_subset_closedBall (ball_subset_ball (min_le_left _ _) hx'.2)
      -- the pushed chart flow is an integral curve of the gradient field
      have hu : ∀ t ∈ Ioo (-εp) εp, HasDerivAt (Zp (extChartAt I z x'))
          (fieldChartRep (I := I) z (gradientField g f hf)
            (Zp (extChartAt I z x') t)) t := fun t ht =>
        ((hflowp _ hx'c).2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt
          (Icc_mem_nhds ht.1 ht.2)
      have hmemt : ∀ t ∈ Ioo (-εp) εp,
          Zp (extChartAt I z x') t ∈ (extChartAt I z).target := fun t ht =>
        (hflowp _ hx'c).2.2 t (Ioo_subset_Icc_self ht)
      have hIC : IsMIntegralCurveOn
          (fun t => (extChartAt I z).symm (Zp (extChartAt I z x') t))
          (fun q => gradientField g f hf q) (Ioo (-εp) εp) :=
        isMIntegralCurveOn_extChartAt_symm_comp (gradientField g f hf) z hmemt hu
      have hICθ : IsMIntegralCurveOn
          (fun t => smoothVectorFieldFlow (gradientField g f hf) hex t x')
          (fun q => gradientField g f hf q) (Ioo (-εp) εp) :=
        (isMIntegralCurve_smoothVectorFieldFlow _ hex x').isMIntegralCurveOn _
      have h0mem : (0:ℝ) ∈ Ioo (-εp) εp := ⟨neg_lt_zero.mpr hεp, hεp⟩
      have h0eq : smoothVectorFieldFlow (gradientField g f hf) hex 0 x'
          = (extChartAt I z).symm (Zp (extChartAt I z x') 0) := by
        rw [smoothVectorFieldFlow_zero, (hflowp _ hx'c).1,
          (extChartAt I z).left_inv hx'src]
      have heqOn := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        h0mem hX1 hICθ hIC h0eq
      exact heqOn ⟨lt_of_lt_of_le (neg_lt_neg (lt_of_le_of_lt hsT.2 hTεp))
          (neg_nonpos.mpr hs0 |>.trans hs0),
        lt_of_le_of_lt hsT.2 hTεp⟩
    obtain ⟨-, hmp⟩ := metricPreserving_of_localFlowRep g z hparp hTp hTεp hflowp
      hσbp hderp hxsrc hxballp hsT hΘ
    refine ⟨?_, hmp⟩
    -- `C¹` of the chart flow map on the whole flow ball, from its strict
    -- derivatives (`FlowVariation` + `contDiffOn_one_of_hasStrictFDerivAt`)
    have hstrictZ : ∀ ζ ∈ ball (extChartAt I z z) rp,
        ∃ D : E →L[ℝ] C(Set.Icc (0:ℝ) Tp, E), HasStrictFDerivAt σp D ζ := by
      intro ζ hζ
      obtain ⟨D, A₀, -, -, hstrict⟩ := hderp ζ hζ
      exact ⟨D, hstrict⟩
    choose! Dσ hDσ using hstrictZ
    set τ' : Set.Icc (0:ℝ) Tp := ⟨s, hsT⟩ with hτ'_def
    have hσC1 : ContDiffOn ℝ 1 ((ContinuousMap.evalCLM ℝ τ') ∘ σp)
        (ball (extChartAt I z z) rp) :=
      contDiffOn_one_of_hasStrictFDerivAt isOpen_ball fun ζ hζ =>
        ((ContinuousMap.evalCLM ℝ τ').hasStrictFDerivAt).comp ζ (hDσ ζ hζ)
    have hZC1 : ContDiffOn ℝ 1 (fun ζ => Zp ζ s)
        (ball (extChartAt I z z) rp) := by
      refine hσC1.congr fun ζ hζ => ?_
      show Zp ζ s = σp ζ τ'
      rw [hσbp ζ (ball_subset_closedBall hζ) τ']
    -- the flow point stays in the chart target
    have hZsmem : Zp (extChartAt I z x) s ∈ (extChartAt I z).target :=
      (hflowp _ (ball_subset_closedBall hxballp)).2.2 s
        ⟨le_trans (neg_nonpos.mpr hεp.le) hsT.1, hsT.2.trans hTεp.le⟩
    -- assemble the `C¹` manifold map through the chart
    have hφ : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I z) x :=
      contMDiffAt_extChartAt' hxsrc
    have hZm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun ζ => Zp ζ s)
        (extChartAt I z x) :=
      contMDiffAt_iff_contDiffAt.mpr
        (hZC1.contDiffAt (isOpen_ball.mem_nhds hxballp))
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I z).symm
        (Zp (extChartAt I z x) s) :=
      (contMDiffOn_extChartAt_symm z).contMDiffAt
        ((isOpen_extChartAt_target z).mem_nhds hZsmem)
    exact ((hsymm.comp x (hZm.comp x hφ)).congr_of_eventuallyEq hΘ)
  · -- backward time: the flow of the negated chart field, at time `-s`
    have hsT : -s ∈ Icc (0:ℝ) Tm :=
      ⟨neg_nonneg.mpr hs0.le,
        le_trans (neg_le_abs s) (le_trans hs (min_le_right _ _))⟩
    have hΘ : (smoothVectorFieldFlow (gradientField g f hf) hex s) =ᶠ[𝓝 x]
        fun x' => (extChartAt I z).symm (Zm (extChartAt I z x') (-s)) := by
      filter_upwards [hVopen.mem_nhds hx] with x' hx'
      have hx'src : x' ∈ (extChartAt I z).source := hx'.1
      have hx'c : extChartAt I z x' ∈ closedBall (extChartAt I z z) rm :=
        ball_subset_closedBall (ball_subset_ball (min_le_right _ _) hx'.2)
      -- the time-reversed chart flow solves the forward gradient ODE
      have hu : ∀ t ∈ Ioo (-εm) εm,
          HasDerivAt (fun t' => Zm (extChartAt I z x') (-t'))
            (fieldChartRep (I := I) z (gradientField g f hf)
              (Zm (extChartAt I z x') (-t))) t := by
        intro t ht
        have hmt : -t ∈ Ioo (-εm) εm := ⟨neg_lt_neg ht.2, by linarith [ht.1]⟩
        have hZd : HasDerivAt (Zm (extChartAt I z x'))
            (-(fieldChartRep (I := I) z (gradientField g f hf)
              (Zm (extChartAt I z x') (-t)))) (-t) :=
          ((hflowm _ hx'c).2.1 (-t) (Ioo_subset_Icc_self hmt)).hasDerivAt
            (Icc_mem_nhds hmt.1 hmt.2)
        have hcomp := hZd.scomp t (hasDerivAt_neg t)
        simpa using hcomp
      have hmemt : ∀ t ∈ Ioo (-εm) εm,
          Zm (extChartAt I z x') (-t) ∈ (extChartAt I z).target := fun t ht =>
        (hflowm _ hx'c).2.2 (-t)
          (Ioo_subset_Icc_self ⟨neg_lt_neg ht.2, by linarith [ht.1]⟩)
      have hIC : IsMIntegralCurveOn
          (fun t => (extChartAt I z).symm (Zm (extChartAt I z x') (-t)))
          (fun q => gradientField g f hf q) (Ioo (-εm) εm) :=
        isMIntegralCurveOn_extChartAt_symm_comp (gradientField g f hf) z hmemt hu
      have hICθ : IsMIntegralCurveOn
          (fun t => smoothVectorFieldFlow (gradientField g f hf) hex t x')
          (fun q => gradientField g f hf q) (Ioo (-εm) εm) :=
        (isMIntegralCurve_smoothVectorFieldFlow _ hex x').isMIntegralCurveOn _
      have h0mem : (0:ℝ) ∈ Ioo (-εm) εm := ⟨neg_lt_zero.mpr hεm, hεm⟩
      have h0eq : smoothVectorFieldFlow (gradientField g f hf) hex 0 x'
          = (extChartAt I z).symm (Zm (extChartAt I z x') (-0)) := by
        rw [smoothVectorFieldFlow_zero, neg_zero, (hflowm _ hx'c).1,
          (extChartAt I z).left_inv hx'src]
      have heqOn := isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
        h0mem hX1 hICθ hIC h0eq
      have hsmem : s ∈ Ioo (-εm) εm := by
        have habs : |s| < εm := lt_of_le_of_lt
          (le_trans hs (min_le_right _ _)) hTεm
        exact ⟨neg_lt_of_abs_lt habs, lt_of_abs_lt habs⟩
      exact heqOn hsmem
    obtain ⟨-, hmp⟩ := metricPreserving_of_localFlowRep g z hparm hTm hTεm hflowm
      hσbm hderm hxsrc hxballm hsT hΘ
    refine ⟨?_, hmp⟩
    -- `C¹` of the backward chart flow map on the whole flow ball
    have hstrictZ : ∀ ζ ∈ ball (extChartAt I z z) rm,
        ∃ D : E →L[ℝ] C(Set.Icc (0:ℝ) Tm, E), HasStrictFDerivAt σm D ζ := by
      intro ζ hζ
      obtain ⟨D, A₀, -, -, hstrict⟩ := hderm ζ hζ
      exact ⟨D, hstrict⟩
    choose! Dσ hDσ using hstrictZ
    set τ' : Set.Icc (0:ℝ) Tm := ⟨-s, hsT⟩ with hτ'_def
    have hσC1 : ContDiffOn ℝ 1 ((ContinuousMap.evalCLM ℝ τ') ∘ σm)
        (ball (extChartAt I z z) rm) :=
      contDiffOn_one_of_hasStrictFDerivAt isOpen_ball fun ζ hζ =>
        ((ContinuousMap.evalCLM ℝ τ').hasStrictFDerivAt).comp ζ (hDσ ζ hζ)
    have hZC1 : ContDiffOn ℝ 1 (fun ζ => Zm ζ (-s))
        (ball (extChartAt I z z) rm) := by
      refine hσC1.congr fun ζ hζ => ?_
      show Zm ζ (-s) = σm ζ τ'
      rw [hσbm ζ (ball_subset_closedBall hζ) τ']
    -- the flow point stays in the chart target
    have hZsmem : Zm (extChartAt I z x) (-s) ∈ (extChartAt I z).target :=
      (hflowm _ (ball_subset_closedBall hxballm)).2.2 (-s)
        ⟨le_trans (neg_nonpos.mpr hεm.le) hsT.1, hsT.2.trans hTεm.le⟩
    -- assemble the `C¹` manifold map through the chart
    have hφ : ContMDiffAt I 𝓘(ℝ, E) 1 (extChartAt I z) x :=
      contMDiffAt_extChartAt' hxsrc
    have hZm' : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (fun ζ => Zm ζ (-s))
        (extChartAt I z x) :=
      contMDiffAt_iff_contDiffAt.mpr
        (hZC1.contDiffAt (isOpen_ball.mem_nhds hxballm))
    have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I z).symm
        (Zm (extChartAt I z x) (-s)) :=
      (contMDiffOn_extChartAt_symm z).contMDiffAt
        ((isOpen_extChartAt_target z).mem_nhds hZsmem)
    exact ((hsymm.comp x (hZm'.comp x hφ)).congr_of_eventuallyEq hΘ)

end MorganTianLib

end

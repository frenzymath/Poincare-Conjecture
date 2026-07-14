import MorganTianLib.Ch02.FlowC1
import MorganTianLib.Ch02.FlowVariationJoint

/-!
# Morgan–Tian Ch. 2 — the gradient flow is jointly `C¹` in `(t, x)`

Blueprint `lem:parallel-gradient-flow`(2), joint regularity: under the Bochner
package (`|∇f|² ≡ c₁`, `Δf ≡ c₂`, `Ric(∇f,∇f) ≥ 0`), the flow
`θ : ℝ × M → M` of the gradient field `(∇f)^*` is **jointly `C¹`** on the
product manifold `ℝ × M`. This is the analytic gate for the sharp ℓ² product
formula of blueprint `prop:parallel-gradient-splitting` Step 4: the
tilted-competitor-path and level-projection arguments differentiate `θ` along
paths that move in time and space simultaneously.

The proof has two layers:

* **the one-sided joint flow box** (`exists_flowJointC1BoxAt`): in the chart at
  any `z`, the chart representation of the gradient field is `C¹`, so its local
  flow is jointly `C¹` on an open space-time box
  (`exists_localFlow_hasStrictFDerivAt_uncurry`); by uniqueness of integral
  curves the manifold flow agrees near `z` with the chart flow pushed through
  the chart inverse, for all times in the box, so `(s, x) ↦ θ_s(x)` is `C¹` at
  every `(s, x)` with `0 < s < δ` and `x` near `z`;
* **the backward-anchor gluing**
  (`contMDiffAt_smoothVectorFieldFlow_uncurry_of_bochner`): at `(t₀, x₀)`,
  cover the compact orbit arc `{θ_u(x₀) : |u| ≤ |t₀| + 1}` by finitely many
  joint boxes, take the uniform box time `δ₀ ≤ 1`, and write
  `θ_t(x) = θ_{t - (t₀ - a)}(θ_{t₀ - a}(x))` with anchor `a := δ₀ / 2`: the
  reparametrized time `t - (t₀ - a)` sits in the open interval `(0, δ₀)` for
  `t` near `t₀`, the anchor point `θ_{t₀ - a}(x₀)` lies on the arc, and
  `θ_{t₀ - a}` is `C¹` by the fixed-time regularity (`FlowC1`), so the joint
  box composes with a `C¹` map.

Main declarations:

* `exists_flowJointC1BoxAt` — the local one-sided joint `C¹` flow box.
* `contMDiffAt_smoothVectorFieldFlow_uncurry_of_bochner` — `θ` is jointly `C¹`
  at every point of `ℝ × M`.
* `contMDiff_smoothVectorFieldFlow_uncurry_of_bochner` — `θ` is `C¹` as a map
  `ℝ × M → M`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`, `prop:parallel-gradient-splitting`).
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
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **The one-sided joint `C¹` flow box**: around every `z ∈ M` there
are a time `δ > 0` and an open neighbourhood `V ∋ z` such that the gradient
flow `(s, x) ↦ θ_s(x)` is jointly `C¹` at every `(s, x)` with `0 < s < δ` and
`x ∈ V`. In the chart at `z` the flow is the local flow of the `C¹` chart
field, which is jointly `C¹` on an open space-time box
(`exists_localFlow_hasStrictFDerivAt_uncurry`); the identification is by
uniqueness of integral curves. Blueprint `lem:parallel-gradient-flow`(2),
joint local step. -/
theorem exists_flowJointC1BoxAt
    (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) (z : M) :
    ∃ (δ : ℝ) (V : Set M), 0 < δ ∧ IsOpen V ∧ z ∈ V ∧
      ∀ x ∈ V, ∀ s ∈ Ioo (0:ℝ) δ,
        ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
          (fun p : ℝ × M =>
            smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2) (s, x) := by
  classical
  have hΩ : IsOpen (extChartAt I z).target := isOpen_extChartAt_target (I := I) z
  have hz₀ : extChartAt I z z ∈ (extChartAt I z).target := mem_extChartAt_target z
  -- the chart field of the gradient and its `C¹` regularity
  have hV1 : ContDiffOn ℝ 1
      (fieldChartRep (I := I) z (gradientField g f hf)) (extChartAt I z).target :=
    (contDiffOn_fieldChartRep_gradientField g hf z).of_le (by exact_mod_cast le_top)
  -- the jointly `C¹` chart flow box
  obtain ⟨r, ε, T, Z, Dx, hr, hε, hT, hTε, hflow, hZcont, hDx, hDxcont, hjoint,
    hC1⟩ := exists_localFlow_hasStrictFDerivAt_uncurry hΩ hz₀ hV1
  set V : Set M := (extChartAt I z).source
    ∩ extChartAt I z ⁻¹' ball (extChartAt I z z) r with hV_def
  have hVopen : IsOpen V := isOpen_extChartAt_preimage' z isOpen_ball
  refine ⟨T, V, hT, hVopen, ⟨mem_extChartAt_source z, mem_ball_self hr⟩, ?_⟩
  intro x hx s hs
  have hxsrc : x ∈ (chartAt H z).source := by
    rw [← extChartAt_source (I := I)]
    exact hx.1
  have hxball : extChartAt I z x ∈ ball (extChartAt I z z) r := hx.2
  -- regularity of the gradient section, for uniqueness of integral curves
  have hX1 : ContMDiff I (I.prod 𝓘(ℝ, E)) 1
      (fun q => (⟨q, gradientField g f hf q⟩ : TangentBundle I M)) := fun p =>
    ((gradientField g f hf).smooth p).of_le (by norm_num)
  -- pointwise identification of the flow with the chart-flow readback
  have hid : ∀ x' ∈ V, ∀ s' ∈ Ioo (-ε) ε,
      smoothVectorFieldFlow (gradientField g f hf) hex s' x'
        = (extChartAt I z).symm (Z (extChartAt I z x') s') := by
    intro x' hx' s' hs'
    have hx'src : x' ∈ (extChartAt I z).source := hx'.1
    have hx'c : extChartAt I z x' ∈ closedBall (extChartAt I z z) r :=
      ball_subset_closedBall hx'.2
    -- the pushed chart flow is an integral curve of the gradient field
    have hu : ∀ t ∈ Ioo (-ε) ε, HasDerivAt (Z (extChartAt I z x'))
        (fieldChartRep (I := I) z (gradientField g f hf)
          (Z (extChartAt I z x') t)) t := fun t ht =>
      ((hflow _ hx'c).2.1 t (Ioo_subset_Icc_self ht)).hasDerivAt
        (Icc_mem_nhds ht.1 ht.2)
    have hmemt : ∀ t ∈ Ioo (-ε) ε,
        Z (extChartAt I z x') t ∈ (extChartAt I z).target := fun t ht =>
      (hflow _ hx'c).2.2 t (Ioo_subset_Icc_self ht)
    have hIC : IsMIntegralCurveOn
        (fun t => (extChartAt I z).symm (Z (extChartAt I z x') t))
        (fun q => gradientField g f hf q) (Ioo (-ε) ε) :=
      isMIntegralCurveOn_extChartAt_symm_comp (gradientField g f hf) z hmemt hu
    have hICθ : IsMIntegralCurveOn
        (fun t => smoothVectorFieldFlow (gradientField g f hf) hex t x')
        (fun q => gradientField g f hf q) (Ioo (-ε) ε) :=
      (isMIntegralCurve_smoothVectorFieldFlow _ hex x').isMIntegralCurveOn _
    have h0mem : (0:ℝ) ∈ Ioo (-ε) ε := ⟨neg_lt_zero.mpr hε, hε⟩
    have h0eq : smoothVectorFieldFlow (gradientField g f hf) hex 0 x'
        = (extChartAt I z).symm (Z (extChartAt I z x') 0) := by
      rw [smoothVectorFieldFlow_zero, (hflow _ hx'c).1,
        (extChartAt I z).left_inv hx'src]
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless
      h0mem hX1 hICθ hIC h0eq hs'
  -- the box point sits inside the product identification region
  have hsε : s ∈ Ioo (-ε) ε :=
    ⟨lt_of_lt_of_le (neg_lt_zero.mpr hε) hs.1.le, lt_trans hs.2 hTε⟩
  have hmemprod : (s, x) ∈ Ioo (-ε) ε ×ˢ V := ⟨hsε, hx⟩
  have hprod_open : IsOpen (Ioo (-ε) ε ×ˢ V) := isOpen_Ioo.prod hVopen
  -- eventual equality of the flow with the chart-flow readback near `(s, x)`
  have hΘev : (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2)
      =ᶠ[𝓝 (s, x)] fun p : ℝ × M =>
        (extChartAt I z).symm (Z (extChartAt I z p.2) p.1) := by
    filter_upwards [hprod_open.mem_nhds hmemprod] with p hp
    exact hid p.2 hp.2 p.1 hp.1
  -- `C¹` of the chart-flow readback at `(s, x)`
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) 1
      (fun p : ℝ × M => extChartAt I z p.2) (s, x) :=
    (contMDiffAt_extChartAt' hxsrc).comp (s, x) contMDiffAt_snd
  have hfst : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => p.1) (s, x) := contMDiffAt_fst
  have hpair : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E × ℝ) 1
      (fun p : ℝ × M => (extChartAt I z p.2, p.1)) (s, x) :=
    hφ.prodMk_space hfst
  have hZC : ContDiffAt ℝ 1 (fun q : E × ℝ => Z q.1 q.2)
      (extChartAt I z x, s) := by
    have h := hC1.contDiffAt ((isOpen_ball.prod isOpen_Ioo).mem_nhds
      (⟨hxball, hs⟩ : (extChartAt I z x, s) ∈ ball (extChartAt I z z) r ×ˢ Ioo 0 T))
    exact h
  have hZM : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, E) 1
      (fun p : ℝ × M => Z (extChartAt I z p.2) p.1) (s, x) :=
    hZC.comp_contMDiffAt (x := ((s, x) : ℝ × M)) hpair
  -- the flow point stays in the chart target
  have hsIcc : s ∈ Icc (-ε) ε := Ioo_subset_Icc_self hsε
  have hZsmem : Z (extChartAt I z x) s ∈ (extChartAt I z).target :=
    (hflow _ (ball_subset_closedBall hxball)).2.2 s hsIcc
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I 1 (extChartAt I z).symm
      (Z (extChartAt I z x) s) :=
    (contMDiffOn_extChartAt_symm z).contMDiffAt
      ((isOpen_extChartAt_target z).mem_nhds hZsmem)
  have hcomp : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M => (extChartAt I z).symm (Z (extChartAt I z p.2) p.1))
      (s, x) := hsymm.comp (s, x) hZM
  exact hcomp.congr_of_eventuallyEq hΘev

/-- **Math.** **The gradient flow is jointly `C¹` in `(t, x)` at every point**
(blueprint `lem:parallel-gradient-flow`(2), joint regularity): under the
Bochner package, the flow `θ : ℝ × M → M` of the gradient field is `C¹` at
every `(t₀, x₀)`. The compact orbit arc through `x₀` is covered by finitely
many one-sided joint boxes with uniform time `δ₀ ≤ 1`; the backward anchor
`a := δ₀/2` rewrites `θ_t(x) = θ_{t - (t₀ - a)}(θ_{t₀ - a}(x))`, whose
reparametrized time lies mid-box, and `θ_{t₀ - a}` is `C¹` by the fixed-time
regularity. -/
theorem contMDiffAt_smoothVectorFieldFlow_uncurry_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t₀ : ℝ) (x₀ : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2) (t₀, x₀) := by
  classical
  -- the compact orbit arc through `x₀`, with a one-step margin
  set K : Set M := (fun u => smoothVectorFieldFlow (gradientField g f hf) hex u x₀)
    '' Icc (-(|t₀| + 1)) (|t₀| + 1) with hK_def
  have hKcompact : IsCompact K :=
    isCompact_Icc.image (continuous_smoothVectorFieldFlow_apply _ hex x₀)
  -- a joint `C¹` flow box around every point of the arc
  choose! δ V hδ hVopen hVmem hVstep using fun y : M =>
    exists_flowJointC1BoxAt g hf hex y
  obtain ⟨T', hT'K, hKT'⟩ := hKcompact.elim_nhds_subcover V
    fun y _ => (hVopen y).mem_nhds (hVmem y)
  have hx₀K : x₀ ∈ K := ⟨0, ⟨neg_nonpos.mpr (by positivity), by positivity⟩,
    smoothVectorFieldFlow_zero _ hex x₀⟩
  have hT'ne : T'.Nonempty := by
    rcases Finset.eq_empty_or_nonempty T' with hT0 | hT0
    · exfalso
      subst hT0
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty,
        subset_empty_iff] at hKT'
      rw [hKT'] at hx₀K
      exact hx₀K
    · exact hT0
  -- the uniform box time over the finite subcover, capped at `1`
  set δ₀ : ℝ := min 1 (T'.inf' hT'ne δ) with hδ₀_def
  have hδ₀ : 0 < δ₀ :=
    lt_min one_pos ((Finset.lt_inf'_iff _).mpr fun y _ => hδ y)
  have hδ₀le : ∀ y ∈ T', δ₀ ≤ δ y := fun y hy =>
    le_trans (min_le_right _ _) (Finset.inf'_le _ hy)
  have hδ₀le1 : δ₀ ≤ 1 := min_le_left _ _
  -- the backward anchor and the anchored point on the arc
  set a : ℝ := δ₀ / 2 with ha_def
  have ha : 0 < a := by positivity
  have ha1 : a ≤ 1 := by
    rw [ha_def]
    linarith
  set w : M := smoothVectorFieldFlow (gradientField g f hf) hex (t₀ - a) x₀
    with hw_def
  have hwK : w ∈ K := by
    refine ⟨t₀ - a, ⟨?_, ?_⟩, rfl⟩
    · have := neg_abs_le t₀
      linarith
    · have := le_abs_self t₀
      linarith
  -- the box containing the anchored point
  obtain ⟨z, hzT', hwz⟩ := mem_iUnion₂.mp (hKT' hwK)
  have haδz : a ∈ Ioo (0:ℝ) (δ z) := by
    constructor
    · exact ha
    · have h1 : a < δ₀ := by
        rw [ha_def]
        linarith
      exact lt_of_lt_of_le h1 (hδ₀le z hzT')
  -- joint `C¹` of the flow at the anchored box point
  have hbox := hVstep z w hwz a haδz
  -- rewrite the anchor time to match the reparametrization
  have hbox' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2)
      (t₀ - (t₀ - a), w) := by
    rw [sub_sub_cancel]
    exact hbox
  -- the `C¹` reparametrization `(t, x) ↦ (t - (t₀ - a), θ_{t₀ - a}(x))`
  have hψ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex (t₀ - a) p.2)
      (t₀, x₀) :=
    ((contMDiff_smoothVectorFieldFlow_of_bochner g hLC hf hgrad hharm hric hex
      (t₀ - a)).contMDiffAt).comp (t₀, x₀) contMDiffAt_snd
  have htime : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1
      (fun p : ℝ × M => p.1 - (t₀ - a)) (t₀, x₀) :=
    contMDiffAt_fst.sub contMDiffAt_const
  have hΨ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) 1
      (fun p : ℝ × M => ((p.1 - (t₀ - a)),
        smoothVectorFieldFlow (gradientField g f hf) hex (t₀ - a) p.2))
      (t₀, x₀) := htime.prodMk hψ
  -- compose: the anchor of the box is the value of the reparametrization
  have hcomp := hbox'.comp (t₀, x₀) hΨ
  have hcomp' : ContMDiffAt (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex (p.1 - (t₀ - a))
          (smoothVectorFieldFlow (gradientField g f hf) hex (t₀ - a) p.2))
      (t₀, x₀) := hcomp
  -- the group law identifies the composite with the flow
  have hgroup : ∀ p : ℝ × M,
      smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2
        = smoothVectorFieldFlow (gradientField g f hf) hex (p.1 - (t₀ - a))
            (smoothVectorFieldFlow (gradientField g f hf) hex (t₀ - a) p.2) := by
    intro p
    rw [← smoothVectorFieldFlow_add _ hex (p.1 - (t₀ - a)) (t₀ - a) p.2,
      sub_add_cancel]
  exact hcomp'.congr_of_eventuallyEq (Filter.Eventually.of_forall hgroup)

/-- **Math.** **The gradient flow is jointly `C¹` as a map `ℝ × M → M`**
(blueprint `lem:parallel-gradient-flow`(2), joint regularity, global form):
under the Bochner package, `(t, x) ↦ θ_t(x)` is `C¹` on the product manifold
`ℝ × M`. -/
theorem contMDiff_smoothVectorFieldFlow_uncurry_of_bochner
    (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q)) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) I 1
      (fun p : ℝ × M =>
        smoothVectorFieldFlow (gradientField g f hf) hex p.1 p.2) :=
  fun p => (contMDiffAt_smoothVectorFieldFlow_uncurry_of_bochner g hLC hf hgrad
    hharm hric hex p.1 p.2).contMDiffWithinAt

end MorganTianLib

end

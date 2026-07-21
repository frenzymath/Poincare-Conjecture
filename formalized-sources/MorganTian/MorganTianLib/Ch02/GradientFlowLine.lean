import MorganTianLib.Ch02.FrameBridge

/-!
# Morgan–Tian Ch. 2 — flow lines of a parallel gradient field

Blueprint `lem:parallel-gradient-flow`(2)–(3), per-flow-line form. Let `f` be a
smooth function on a Riemannian manifold `(M, g)` with `|∇f|² ≡ c₁` and
`Δf ≡ c₂` constant and non-negative Ricci curvature along `∇f` — the Bochner
package under which the gradient field `(∇f)^*` restricts to a parallel field
along chart-regular curves (`isParallelAlong_gradientField_comp_of_bochner`).
Then along every continuous geodesic `γ` whose velocity at one time is
`(∇f)^*(γ t₁)`:

* `curveVelocity_eq_gradientField_of_bochner` — the **integral-curve
  identification** `γ'(t) = (∇f)^*(γ t)` for all `t`: both sides are parallel
  fields along `γ` (the velocity by the geodesic equation, the gradient field
  by Bochner), and they agree at `t₁`, so they agree everywhere
  (`IsParallelAlong.apply_eq`). In particular the geodesic through `x` with
  initial velocity `(∇f)^*(x)` is an integral curve of `(∇f)^*`.
* `metricInner_curveVelocity_self_of_bochner` — flow lines have constant
  speed: `|γ'(t)|² = c₁` for all `t`.
* `hasDerivAt_comp_of_bochner` / `comp_eq_add_mul_of_bochner` — blueprint
  part (3): `(f ∘ γ)'(t) = ⟨(∇f)^*, γ'⟩(γ t) = |∇f|²(γ t) = c₁`, hence
  `f (γ t) = f (γ 0) + c₁ · t`. For a Busemann-type function (`c₁ = 1`) this
  is `B(θ_t(x)) = B(x) + t`.

The chart-regularity inputs (`hmem`/`hvel`) demanded by the moving-foot
covariant-derivative machinery are discharged here once and for all:
chart membership near each time from continuity of `γ`
(`eventually_mem_chartAt_source`), the chart velocity from the
geodesic-equation data itself. The file also provides the moving-foot
**chain rule** `hasDerivAt_comp_chartLocalCurve` —
`(F ∘ γ)'(t₀) = dF_{γ t₀}(γ'(t₀))` for smooth `F : M → ℝ` and a curve with
chart velocity `v` at `t₀` — routed through mathlib's `HasMFDerivAt` via the
bridge `hasMFDerivAt_of_hasDerivAt_chartLocalCurve` (the chart-local curve at
the moving foot *is* `writtenInExtChartAt` for the source model `𝓘(ℝ, ℝ)`).

Continuity of the geodesic is a genuine hypothesis, not an omission: the
`Riemannian.Geodesic.IsGeodesic` predicate constrains only the chart-local
curves `s ↦ φ_{γ t}(γ s)`, whose smoothness does not force `γ` itself to be
continuous (off the chart source the chart map is junk-valued). The geodesics
produced by the DoCarmo flow are continuous, and the eventual
`lem:parallel-gradient-flow`(2) existence statement will supply this.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-! ### Chart regularity of continuous curves -/

/-- **Math.** A curve continuous at `t₀` eventually stays in the chart source
at its foot `γ t₀`: the `hmem` regularity input of the moving-foot
covariant-derivative machinery, discharged from continuity alone. -/
theorem eventually_mem_chartAt_source {γ : ℝ → M} {t₀ : ℝ}
    (h : ContinuousAt γ t₀) :
    ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source :=
  h.preimage_mem_nhds
    ((chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀)))

/-- **Math.** The chart velocity of a curve, read off the derivative data: if
the chart-local curve at `t₁` has derivative `v` at `t₁`, then the velocity
field of `γ` at `t₁` is `v` (as a tangent vector at `γ t₁`). -/
theorem curveVelocity_eq_of_hasDerivAt {γ : ℝ → M} {t₁ : ℝ} {v : E}
    (hv : HasDerivAt (chartLocalCurve (I := I) γ t₁) v t₁) :
    curveVelocity (I := I) γ t₁ = (v : TangentSpace I (γ t₁)) :=
  hv.deriv

/-! ### The moving-foot chain rule -/

/-- **Math.** The chart-local curve at the moving foot is the coordinate
representation of `γ` in the sense of `HasMFDerivAt`: a curve continuous at
`t₀` whose chart curve has derivative `v` at `t₀` is manifold-differentiable
at `t₀` with derivative `r ↦ r • v : T_{t₀}ℝ → T_{γ t₀}M`. -/
theorem hasMFDerivAt_of_hasDerivAt_chartLocalCurve {γ : ℝ → M} {t₀ : ℝ} {v : E}
    (hcont : ContinuousAt γ t₀)
    (hv : HasDerivAt (chartLocalCurve (I := I) γ t₀) v t₀) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight (v : TangentSpace I (γ t₀))) := by
  refine ⟨hcont, ?_⟩
  rw [(𝓘(ℝ, ℝ)).range_eq_univ, hasFDerivWithinAt_univ]
  have heq : writtenInExtChartAt 𝓘(ℝ, ℝ) I t₀ γ = chartLocalCurve (I := I) γ t₀ :=
    rfl
  rw [heq]
  exact hv.hasFDerivAt

/-- **Math.** **Chain rule at the moving foot**: for `F : M → ℝ` smooth and a
curve `γ` with chart velocity `v` at `t₀`,
`(F ∘ γ)'(t₀) = dF_{γ t₀}(v)` — the manifold differential of `F` applied to
the velocity, the coordinate-free form of `d/dt F(γ(t)) = ⟨∇F, γ'⟩`. -/
theorem hasDerivAt_comp_chartLocalCurve {F : M → ℝ}
    (hF : ContMDiff I 𝓘(ℝ, ℝ) ∞ F) {γ : ℝ → M} {t₀ : ℝ} {v : E}
    (hcont : ContinuousAt γ t₀)
    (hv : HasDerivAt (chartLocalCurve (I := I) γ t₀) v t₀) :
    HasDerivAt (fun s => F (γ s))
      (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀) (v : TangentSpace I (γ t₀))) t₀ := by
  have hγ := hasMFDerivAt_of_hasDerivAt_chartLocalCurve (I := I) hcont hv
  have hFd : HasMFDerivAt I 𝓘(ℝ, ℝ) F (γ t₀) (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀)) :=
    ((hF (γ t₀)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hcomp := hFd.comp t₀ hγ
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  refine hcomp.congr_mfderiv ?_
  ext
  exact (congrArg (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀)) (one_smul ℝ v)).trans
    (one_smul ℝ (mfderiv I 𝓘(ℝ, ℝ) F (γ t₀) v)).symm

/-! ### The velocity field of a continuous geodesic is parallel -/

/-- **Math.** Blueprint `lem:cov-deriv-along-curve`(4), global form: the
velocity field of a continuous geodesic is **parallel along the geodesic**,
`Dγ'/dt ≡ 0`. The chart-membership input comes from continuity, the
chart-curve differentiability from the geodesic-equation data itself. -/
theorem isParallelAlong_curveVelocity_of_isGeodesic (g : RiemannianMetric I M)
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) :
    IsParallelAlong (I := I) g γ (curveVelocity (I := I) γ) := by
  intro t
  obtain ⟨v, a, hv, hev, ha, heqn⟩ := hgeo t
  exact (hasGeodesicEquationAt_iff_hasCovDerivAlongAt_velocity_zero (I := I)
    (g := g) (eventually_mem_chartAt_source hcont.continuousAt)
    hev).mp (hgeo t)

/-! ### Flow lines of a Bochner-parallel gradient field -/

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2), integral-curve
identification: under the Bochner package (`|∇f|²` and `Δf` constant,
`Ric(∇f, ∇f) ≥ 0`), a continuous geodesic whose velocity at one time `t₁` is
the gradient `(∇f)^*(γ t₁)` has velocity `(∇f)^*(γ t)` at **every** time:
`γ' = (∇f)^* ∘ γ`, i.e. `γ` is an integral curve of the gradient field. Both
sides are parallel fields along `γ` — the velocity by the geodesic equation,
the gradient field by the Bochner vanishing `∇(∇f)^* ≡ 0` — and parallel
fields agreeing at one time agree everywhere. -/
theorem curveVelocity_eq_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (hinit : curveVelocity (I := I) γ t₁ = gradientField g f hf (γ t₁))
    (t : ℝ) :
    curveVelocity (I := I) γ t = gradientField g f hf (γ t) := by
  have hmem : ∀ s, ∀ᶠ u in 𝓝 s, γ u ∈ (chartAt H (γ s)).source := fun s =>
    eventually_mem_chartAt_source hcont.continuousAt
  have hvel : ∀ s, ∃ v : E, HasDerivAt (chartLocalCurve (I := I) γ s) v s := by
    intro s
    obtain ⟨v, a, hv, -, -, -⟩ := hgeo s
    exact ⟨v, hv⟩
  have hpar₂ := isParallelAlong_gradientField_comp_of_bochner (I := I) g hLC hf
    hgrad hharm hric hmem hvel
  have hpar₁ := isParallelAlong_curveVelocity_of_isGeodesic (I := I) g hgeo hcont
  exact hpar₁.apply_eq (I := I) hpar₂ hinit t

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2), constant speed: the
flow lines of a Bochner-parallel gradient field have squared speed
`|γ'(t)|² = |∇f|² = c₁` at every time. For a Busemann-type function
(`c₁ = 1`) the flow lines are unit-speed geodesics. -/
theorem metricInner_curveVelocity_self_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (hinit : curveVelocity (I := I) γ t₁ = gradientField g f hf (γ t₁))
    (t : ℝ) :
    g.metricInner (γ t) (curveVelocity (I := I) γ t)
      (curveVelocity (I := I) γ t) = c₁ := by
  rw [curveVelocity_eq_gradientField_of_bochner (I := I) g hLC hf hgrad hharm
    hric hgeo hcont hinit t]
  exact hgrad (γ t)

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(3), derivative form:
along a flow line of the Bochner-parallel gradient field,
`(f ∘ γ)'(t) = df(γ'(t)) = ⟨(∇f)^*, (∇f)^*⟩(γ t) = c₁` at every time. -/
theorem hasDerivAt_comp_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (hinit : curveVelocity (I := I) γ t₁ = gradientField g f hf (γ t₁))
    (t : ℝ) :
    HasDerivAt (fun s => f (γ s)) c₁ t := by
  obtain ⟨v, a, hv, -, -, -⟩ := hgeo t
  have hchain := hasDerivAt_comp_chartLocalCurve (I := I) hf
    hcont.continuousAt hv
  have hveq : curveVelocity (I := I) γ t = (v : TangentSpace I (γ t)) :=
    curveVelocity_eq_of_hasDerivAt (I := I) hv
  have hvgrad : (v : TangentSpace I (γ t)) = gradientField g f hf (γ t) :=
    hveq.symm.trans (curveVelocity_eq_gradientField_of_bochner (I := I) g hLC
      hf hgrad hharm hric hgeo hcont hinit t)
  have hval : mfderiv I 𝓘(ℝ, ℝ) f (γ t) (v : TangentSpace I (γ t)) = c₁ := by
    rw [← metricInner_gradientAt g f (γ t) (v : TangentSpace I (γ t)), hvgrad]
    exact hgrad (γ t)
  rw [hval] at hchain
  exact hchain

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(3): along a flow line of
the Bochner-parallel gradient field, `f` grows affinely,
`f (γ t) = f (γ 0) + c₁ · t`. For a Busemann-type function (`c₁ = 1`) this is
`B(θ_t(x)) = B(x) + t`: the flow of `(∇B)^*` translates the level sets of
`B`. -/
theorem comp_eq_add_mul_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (hinit : curveVelocity (I := I) γ t₁ = gradientField g f hf (γ t₁))
    (t : ℝ) :
    f (γ t) = f (γ 0) + c₁ * t := by
  have hder : ∀ u : ℝ, HasDerivAt (fun s => f (γ s) - c₁ * s) 0 u := by
    intro u
    have h₁ := hasDerivAt_comp_of_bochner (I := I) g hLC hf hgrad hharm hric
      hgeo hcont hinit u
    have h₂ : HasDerivAt (fun s : ℝ => c₁ * s) c₁ u := by
      simpa using (hasDerivAt_id u).const_mul c₁
    simpa using h₁.sub h₂
  have hconst := is_const_of_deriv_eq_zero
    (fun u => (hder u).differentiableAt) (fun u => (hder u).deriv) t 0
  have : f (γ t) - c₁ * t = f (γ 0) - c₁ * 0 := hconst
  linarith

/-! ### Flow lines as mathlib integral curves: uniqueness and the group law -/

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2): a Bochner flow line
is a **global integral curve** of the gradient field in the mathlib sense
(`IsMIntegralCurve`): at every time `t`, `γ` is manifold-differentiable with
`γ'(t) = (∇f)^*(γ t)`. Together with `isMIntegralCurve_smoothVectorField_eq`
this makes `γ` *the* maximal integral curve of `(∇f)^*` through its starting
point, defined on all of `ℝ`. -/
theorem isMIntegralCurve_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    {γ : ℝ → M} (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hcont : Continuous γ) {t₁ : ℝ}
    (hinit : curveVelocity (I := I) γ t₁ = gradientField g f hf (γ t₁)) :
    IsMIntegralCurve γ (fun x => gradientField g f hf x) := by
  intro t
  obtain ⟨v, a, hv, -, -, -⟩ := hgeo t
  have hvv : (v : TangentSpace I (γ t)) = gradientField g f hf (γ t) :=
    (curveVelocity_eq_of_hasDerivAt (I := I) hv).symm.trans
      (curveVelocity_eq_gradientField_of_bochner (I := I) g hLC hf hgrad hharm
        hric hgeo hcont hinit t)
  show HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
    ((1 : ℝ →L[ℝ] ℝ).smulRight (gradientField g f hf (γ t)))
  rw [← hvv]
  exact hasMFDerivAt_of_hasDerivAt_chartLocalCurve (I := I) hcont.continuousAt hv

/-- **Math.** **Global uniqueness of integral curves** of a smooth vector
field: two global integral curves through a common point coincide.
Mathlib's Picard–Lindelöf uniqueness (`isMIntegralCurve_eq_of_contMDiff`)
specialised to a `SmoothVectorField`, whose section is `C^∞`, hence `C^1`.
Blueprint: `lem:parallel-gradient-flow`(2) ("the maximal integral curve"). -/
theorem isMIntegralCurve_smoothVectorField_eq [T2Space M]
    (X : SmoothVectorField I M) {γ γ' : ℝ → M} {t₀ : ℝ}
    (hγ : IsMIntegralCurve γ (fun x => X x))
    (hγ' : IsMIntegralCurve γ' (fun x => X x)) (h : γ t₀ = γ' t₀) : γ = γ' :=
  isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless
    (fun p => (X.smooth p).of_le (by norm_num)) hγ hγ' h

/-- **Math.** The **group law along integral curves**: if `δ` and `γ` are
global integral curves of a smooth vector field and `δ` starts where `γ` is
at time `t₀`, then `δ s = γ (s + t₀)` for all `s`. Applied to the flow
`θ_t(x)` of the gradient field of a Busemann-type function this is
`θ_s(θ_{t₀}(x)) = θ_{s+t₀}(x)`, blueprint `lem:parallel-gradient-flow`(2). -/
theorem isMIntegralCurve_smoothVectorField_comp_add [T2Space M]
    (X : SmoothVectorField I M) {γ δ : ℝ → M} {t₀ : ℝ}
    (hγ : IsMIntegralCurve γ (fun x => X x))
    (hδ : IsMIntegralCurve δ (fun x => X x))
    (h : δ 0 = γ t₀) (s : ℝ) : δ s = γ (s + t₀) := by
  have hshift : IsMIntegralCurve (γ ∘ (· + t₀)) (fun x => X x) :=
    hγ.comp_add t₀
  have h0 : δ 0 = (γ ∘ (· + t₀)) 0 := by simpa using h
  exact congrFun (isMIntegralCurve_smoothVectorField_eq X hδ hshift h0) s

end MorganTianLib

end

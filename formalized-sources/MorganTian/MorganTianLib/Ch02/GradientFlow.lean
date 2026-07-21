import MorganTianLib.Ch02.GradientFlowLine

/-!
# Morgan–Tian Ch. 2 — the global flow of a parallel gradient field

Blueprint `lem:parallel-gradient-flow`(2)–(3), flow form. The previous file
(`GradientFlowLine`) shows that under the Bochner package a continuous
geodesic with gradient initial velocity is a global integral curve of the
gradient field `(∇f)^*`, that such curves are unique through each point, and
that they obey the group law. This file assembles the **flow** `θ` itself:

* `IsContGeodesicallyComplete` — geodesic completeness with continuous
  witnesses: through every `(p, v)` there is a *continuous* globally-defined
  geodesic with data `(p, v)`. This is do Carmo's `IsGeodesicallyComplete`
  (`Riemannian.Geodesic.IsGeodesicallyComplete`) strengthened by continuity
  of the produced geodesic — a mathematically inessential strengthening (the
  geodesics produced by the local flow are continuous), needed here because
  the chart-local `IsGeodesic` predicate does not constrain the curve off the
  chart sources. The Hopf–Rinow theorem (blueprint `thm:hopf-rinow`, still
  open in DoCarmo) is what will discharge this hypothesis from metric
  completeness.
* `exists_gradientFlowLine_of_bochner` — blueprint
  `lem:parallel-gradient-flow`(2), **existence**: on a geodesically complete
  manifold, through every point `x` there is a (continuous, global) flow line
  of the gradient field, along which `f` grows affinely (part (3)).
* `smoothVectorFieldFlow` — for any smooth vector field with a global
  integral curve through every point, *the* flow `θ : ℝ → M → M`, defined by
  choice and well-defined by uniqueness (`isMIntegralCurve_smoothVectorField_eq`),
  with `θ_0 = id` (`smoothVectorFieldFlow_zero`), the group law
  `θ_{s+t} = θ_s ∘ θ_t` (`smoothVectorFieldFlow_add`), and each `θ_t` a
  bijection of `M` with inverse `θ_{-t}` (`smoothVectorFieldFlow_bijective`) —
  the flow-of-`(∇B)^*` skeleton of blueprint `lem:parallel-gradient-flow`(2).
  Smoothness of `θ_t` (and hence the "diffeomorphism" refinement and part (4))
  requires smooth dependence of integral curves on initial conditions, not yet
  available at manifold level.
* `comp_smoothVectorFieldFlow_gradientField_of_bochner` — blueprint
  `lem:parallel-gradient-flow`(3) in flow form: `f (θ_t x) = f x + c₁ t`.

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

/-! ### The flow of a smooth vector field with global integral curves -/

section Flow

variable (X : SmoothVectorField I M)
  (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧ IsMIntegralCurve γ (fun q => X q))

/-- **Math.** The **flow** of a smooth vector field `X` that has a global
integral curve through every point: `θ t x` is the time-`t` value of the
integral curve of `X` through `x`. By global uniqueness of integral curves
(`isMIntegralCurve_smoothVectorField_eq`) this is well-defined — independent
of the chosen curve — and satisfies the flow identities below. -/
def smoothVectorFieldFlow (t : ℝ) (x : M) : M :=
  Classical.choose (hex x) t

/-- **Math.** The flow at time `0` is the identity: `θ_0 = id`. -/
theorem smoothVectorFieldFlow_zero (x : M) :
    smoothVectorFieldFlow X hex 0 x = x :=
  (Classical.choose_spec (hex x)).1

/-- **Math.** Each flow line `t ↦ θ_t x` is a global integral curve of `X`. -/
theorem isMIntegralCurve_smoothVectorFieldFlow (x : M) :
    IsMIntegralCurve (fun t => smoothVectorFieldFlow X hex t x)
      (fun q => X q) :=
  (Classical.choose_spec (hex x)).2

/-- **Math.** Flow lines are continuous (manifold-differentiability at every
time implies continuity). -/
theorem continuous_smoothVectorFieldFlow_apply (x : M) :
    Continuous fun t => smoothVectorFieldFlow X hex t x :=
  continuous_iff_continuousAt.2 fun t =>
    (isMIntegralCurve_smoothVectorFieldFlow X hex x t).continuousAt

/-- **Math.** The flow line through `x` is *the* integral curve through `x`:
any global integral curve `γ` of `X` with `γ 0 = x` computes the flow,
`θ_t x = γ t`. -/
theorem smoothVectorFieldFlow_eq_of_isMIntegralCurve [T2Space M] {γ : ℝ → M}
    {x : M} (hγ : IsMIntegralCurve γ (fun q => X q)) (h0 : γ 0 = x) (t : ℝ) :
    smoothVectorFieldFlow X hex t x = γ t :=
  congrFun
    (isMIntegralCurve_smoothVectorField_eq (I := I) X
      (isMIntegralCurve_smoothVectorFieldFlow X hex x) hγ (t₀ := 0)
      ((smoothVectorFieldFlow_zero X hex x).trans h0.symm)) t

/-- **Math.** The **group law** of the flow: `θ_{s+t} = θ_s ∘ θ_t`.
Blueprint `lem:parallel-gradient-flow`(2). -/
theorem smoothVectorFieldFlow_add [T2Space M] (s t : ℝ) (x : M) :
    smoothVectorFieldFlow X hex (s + t) x =
      smoothVectorFieldFlow X hex s (smoothVectorFieldFlow X hex t x) :=
  (isMIntegralCurve_smoothVectorField_comp_add (I := I) X
    (isMIntegralCurve_smoothVectorFieldFlow X hex x)
    (isMIntegralCurve_smoothVectorFieldFlow X hex
      (smoothVectorFieldFlow X hex t x))
    (smoothVectorFieldFlow_zero X hex _) s).symm

/-- **Math.** `θ_{-t}` inverts `θ_t` on the left (and, by symmetry in `t`,
on the right): `θ_{-t} (θ_t x) = x`. -/
theorem smoothVectorFieldFlow_neg_apply [T2Space M] (t : ℝ) (x : M) :
    smoothVectorFieldFlow X hex (-t) (smoothVectorFieldFlow X hex t x) = x := by
  rw [← smoothVectorFieldFlow_add X hex (-t) t x, neg_add_cancel]
  exact smoothVectorFieldFlow_zero X hex x

/-- **Math.** Each time-`t` flow map `θ_t` is a **bijection** of `M`, with
inverse `θ_{-t}`. Blueprint `lem:parallel-gradient-flow`(2) (the
"diffeomorphism" claim, at the level of bijectivity; smoothness of `θ_t`
awaits smooth dependence on initial conditions). -/
theorem smoothVectorFieldFlow_bijective [T2Space M] (t : ℝ) :
    Function.Bijective (smoothVectorFieldFlow X hex t) :=
  Function.bijective_iff_has_inverse.2
    ⟨smoothVectorFieldFlow X hex (-t),
      fun x => smoothVectorFieldFlow_neg_apply X hex t x,
      fun x => by
        simpa using smoothVectorFieldFlow_neg_apply X hex (-t) x⟩

end Flow

/-! ### Existence of flow lines under geodesic completeness -/

/-- **Math.** **Geodesic completeness with continuous witnesses**: through
every point `p` and tangent vector `v` there is a *continuous* curve
`γ : ℝ → M`, defined for all time, starting at `p` with chart velocity `v`
and satisfying the geodesic equation at every time. This strengthens
do Carmo's `Riemannian.Geodesic.IsGeodesicallyComplete` by the continuity of
the witness — mathematically inessential (geodesics produced by the local
geodesic flow are continuous) but not derivable from the chart-local
`IsGeodesic` predicate alone, which does not constrain the curve off the
chart sources. The Hopf–Rinow theorem (blueprint `thm:hopf-rinow`) produces
this from metric completeness. -/
def IsContGeodesicallyComplete (g : RiemannianMetric I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p), ∃ γ : ℝ → M, Continuous γ ∧ γ 0 = p ∧
    HasDerivAt (fun s => extChartAt I p (γ s)) v 0 ∧
    Riemannian.Geodesic.IsGeodesic (I := I) g γ

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(2), **existence of flow
lines**: on a geodesically complete manifold, under the Bochner package
(`|∇f|² ≡ c₁`, `Δf ≡ c₂`, `Ric(∇f, ∇f) ≥ 0`), through every point `x` there
is a continuous global integral curve `γ` of the gradient field `(∇f)^*` with
`γ 0 = x` — namely the geodesic with initial data `(x, (∇f)^*(x))` — and `f`
grows affinely along it: `f (γ t) = f x + c₁ t` (part (3)). -/
theorem exists_gradientFlowLine_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g) (x : M) :
    ∃ γ : ℝ → M, Continuous γ ∧ γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q) ∧
      ∀ t, f (γ t) = f x + c₁ * t := by
  obtain ⟨γ, hcont, h0, hv, hgeo⟩ := hcomp x (gradientField g f hf x)
  subst h0
  have hinit : curveVelocity (I := I) γ 0 = gradientField g f hf (γ 0) :=
    curveVelocity_eq_of_hasDerivAt (I := I) hv
  exact ⟨γ, hcont, rfl,
    isMIntegralCurve_gradientField_of_bochner (I := I) g hLC hf hgrad hharm
      hric hgeo hcont hinit,
    fun t => comp_eq_add_mul_of_bochner (I := I) g hLC hf hgrad hharm hric
      hgeo hcont hinit t⟩

/-- **Math.** The gradient field of a Bochner function on a geodesically
complete manifold has a global integral curve through every point — the
existence input for its flow `smoothVectorFieldFlow`. -/
theorem exists_isMIntegralCurve_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g) :
    ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q) := by
  intro x
  obtain ⟨γ, -, h0, hIC, -⟩ := exists_gradientFlowLine_of_bochner (I := I) g
    hLC hf hgrad hharm hric hcomp x
  exact ⟨γ, h0, hIC⟩

/-- **Math.** Blueprint `lem:parallel-gradient-flow`(3), flow form: along the
flow `θ` of the gradient field of a Bochner function,
`f (θ_t x) = f x + c₁ t`. For a Busemann-type function (`c₁ = 1`) this is
`B(θ_t(x)) = B(x) + t`: the flow translates the level sets of `B`. -/
theorem comp_smoothVectorFieldFlow_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (hcomp : IsContGeodesicallyComplete g)
    (hex : ∀ x : M, ∃ γ : ℝ → M, γ 0 = x ∧
      IsMIntegralCurve γ (fun q => gradientField g f hf q))
    (t : ℝ) (x : M) :
    f (smoothVectorFieldFlow (gradientField g f hf) hex t x) = f x + c₁ * t := by
  obtain ⟨γ, -, h0, hIC, hcomp_eq⟩ := exists_gradientFlowLine_of_bochner
    (I := I) g hLC hf hgrad hharm hric hcomp x
  rw [smoothVectorFieldFlow_eq_of_isMIntegralCurve _ hex hIC h0 t]
  exact hcomp_eq t

end MorganTianLib

end

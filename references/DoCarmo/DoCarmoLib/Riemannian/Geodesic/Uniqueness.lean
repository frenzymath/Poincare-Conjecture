import DoCarmoLib.Riemannian.Geodesic.Equation
import DoCarmoLib.Riemannian.Geodesic.Existence
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique


/-!
# Local uniqueness of geodesics via Picard-Lindelöf / Gronwall

For a smooth Riemannian metric `g` on a boundaryless smooth manifold `M`
modelled on a complete inner-product space `E`, two local integral curves
of the chart-fixed geodesic vector field that agree at a base time `t₀`
agree on a neighbourhood of `t₀`. This is a direct lift of Mathlib's

* `isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless`
  (`Mathlib/Geometry/Manifold/IntegralCurve/ExistUnique.lean`),

specialised to the chart-fixed geodesic vector field
`geodesicVectorFieldChart g α`, whose `C^∞`-smoothness on
`(chartAt H α).source` is recorded in
`DifferentialGeometry/Geometry/Geodesic/Equation.lean`.

We then transfer the result to base curves on `M` via projection, and
package the conclusion at the `IsGeodesicAt`-predicate level. The key
observation is that the predicate `IsGeodesicAt g γ t₀` already exposes a
lift `f : ℝ → TangentBundle I M` projecting to `γ`; uniqueness of `f` in
the chart-fixed vector field hence projects to uniqueness of `γ` on a
neighbourhood of `t₀`.

The natural matching condition for two geodesics is "same initial tangent
vector" — i.e. the lifts `f₁, f₂` agree at `t₀` as points of
`TangentBundle I M`. This encodes both `γ₁ t₀ = γ₂ t₀` and a matching of
velocity vectors in `T_{γ t₀} M`.

The chart basepoint `α` is fixed once and for all in the predicate
`IsGeodesicAt`; comparison of geodesics produced from *different* chart
basepoints is a separate question (it asks whether two different
chart-Christoffel ODEs share solutions through a common initial point —
true on the chart overlap, but the natural statement is at the level of
the moving-chart geodesic equation).
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


section ChartFixedUniqueness

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Uniqueness of integral curves of the chart-fixed geodesic vector
field.** Two `IsMIntegralCurveAt` witnesses `f₁, f₂` for the chart-fixed
geodesic vector field `geodesicVectorFieldChart g α` at `t₀` that agree
at `t₀` agree on a neighbourhood of `t₀`, provided the common base point
`(f₁ t₀).proj = (f₂ t₀).proj` lies in the chart-α source (so the vector
field is smooth there). -/
theorem isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
    {g : RiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : (f₁ t₀).proj ∈ (chartAt H α).source)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    f₁ =ᶠ[𝓝 t₀] f₂ := by
  have hsmooth_inf :
      ContMDiffAt I.tangent I.tangent.tangent ∞
        (fun p : TangentBundle I M =>
          (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (f₁ t₀) :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g α
      (p₀ := f₁ t₀) hα_src
  have hsmooth1 :
      ContMDiffAt I.tangent I.tangent.tangent 1
        (fun p : TangentBundle I M =>
          (⟨p, geodesicVectorFieldChart (I := I) g α p⟩ :
            TangentBundle I.tangent (TangentBundle I M)))
        (f₁ t₀) :=
    hsmooth_inf.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    isMIntegralCurveAt_eventuallyEq_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g α)
      (γ := f₁) (γ' := f₂) (t₀ := t₀)
      hsmooth1 hf₁ hf₂ h0

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Projected uniqueness.** Under the same hypotheses, the base curves
agree on a neighbourhood of `t₀`. -/
theorem projectCurve_eventuallyEq_of_isMIntegralCurveAt_geodesicVectorFieldChart
    {g : RiemannianMetric I M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : (f₁ t₀).proj ∈ (chartAt H α).source)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    projectCurve (I := I) f₁ =ᶠ[𝓝 t₀] projectCurve (I := I) f₂ := by
  have heq :=
    isMIntegralCurveAt_geodesicVectorFieldChart_eventuallyEq
      (I := I) (g := g) (α := α) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f₂) hα_src hf₁ hf₂ h0
  refine heq.mono ?_
  intro t ht
  simp [projectCurve, ht]

end ChartFixedUniqueness

section GeodesicUniqueness

variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Uniqueness of geodesics with a fixed chart basepoint.** If two
curves are local geodesics at `t₀` witnessed by the same chart basepoint
`α : M` and lifts `f₁, f₂` with `f₁ t₀ = f₂ t₀`, and the common starting
point lies in `(chartAt H α).source`, then the two base curves agree on a
neighbourhood of `t₀`. -/
theorem isGeodesicAt_eventuallyEq
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {α : M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hα_src : γ₁ t₀ ∈ (chartAt H α).source)
    (hproj₁ : ∀ t, (f₁ t).proj = γ₁ t)
    (hproj₂ : ∀ t, (f₂ t).proj = γ₂ t)
    (hf₁ : IsMIntegralCurveAt f₁ (geodesicVectorFieldChart (I := I) g α) t₀)
    (hf₂ : IsMIntegralCurveAt f₂ (geodesicVectorFieldChart (I := I) g α) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ := by
  have hα_src' : (f₁ t₀).proj ∈ (chartAt H α).source := by
    rw [hproj₁ t₀]; exact hα_src
  have hproj_eq :=
    projectCurve_eventuallyEq_of_isMIntegralCurveAt_geodesicVectorFieldChart
      (I := I) (g := g) (α := α) (t₀ := t₀)
      (f₁ := f₁) (f₂ := f₂) hα_src' hf₁ hf₂ h0
  refine hproj_eq.mono ?_
  intro t ht
  rw [projectCurve_apply, projectCurve_apply] at ht
  rw [← hproj₁ t, ← hproj₂ t]; exact ht

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Uniqueness of geodesics with matching initial data.** If the base
curves `γ₁, γ₂` are projections of integral curves `f₁, f₂` of the
chart-fixed geodesic vector field for the chart basepoint `γ₁ t₀`, and the
lifts agree at `t₀` (`f₁ t₀ = f₂ t₀`, which encodes matching initial point
*and* initial velocity), then `γ₁` and `γ₂` agree on a neighbourhood of
`t₀`.

Specialisation of `isGeodesicAt_eventuallyEq` with the chart basepoint
taken to be the common starting point `γ₁ t₀`; this choice automatically
places that point in the chart source, so no source-membership hypothesis
is needed. -/
theorem isGeodesicAt_eventuallyEq_of_lift_eq
    {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M} {t₀ : ℝ}
    {f₁ f₂ : ℝ → TangentBundle I M}
    (hproj₁ : ∀ t, (f₁ t).proj = γ₁ t)
    (hproj₂ : ∀ t, (f₂ t).proj = γ₂ t)
    (hf₁ : IsMIntegralCurveAt f₁
      (geodesicVectorFieldChart (I := I) g (γ₁ t₀)) t₀)
    (hf₂ : IsMIntegralCurveAt f₂
      (geodesicVectorFieldChart (I := I) g (γ₁ t₀)) t₀)
    (h0 : f₁ t₀ = f₂ t₀) :
    γ₁ =ᶠ[𝓝 t₀] γ₂ :=
  isGeodesicAt_eventuallyEq (I := I) (g := g) (γ₁ := γ₁) (γ₂ := γ₂)
    (α := γ₁ t₀) (t₀ := t₀) (f₁ := f₁) (f₂ := f₂)
    (mem_chart_source H (γ₁ t₀)) hproj₁ hproj₂ hf₁ hf₂ h0

end GeodesicUniqueness

end Geodesic
end Riemannian

end

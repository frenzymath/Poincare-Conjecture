/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Geodesic/Existence.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.Equation
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

set_option linter.unusedSectionVars false

/-!
# Local existence of geodesics via Picard-Lindelöf

For a smooth Riemannian metric `g` on a smooth manifold `M` (boundaryless,
modelled on a complete inner-product space `E`) and any initial datum
`(p : M, v : T_p M)`, there exists a curve `γ : ℝ → M` starting at `p`
that is the projection of a local integral curve of the chart-fixed
geodesic vector field `geodesicVectorFieldChart g p` on `T M`.

The construction proceeds in two steps:

1. **Picard-Lindelöf on the tangent bundle.** We feed
   `geodesicVectorFieldChart g p` into Mathlib's existence theorem
   `exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless`. The vector
   field is `C^∞` at `⟨p, v⟩ : TangentBundle I M` by
   `geodesicVectorFieldChart_contMDiffAt`; the tangent bundle is
   boundaryless because `(I.prod 𝓘(ℝ, E)).Boundaryless` is automatic
   from `[I.Boundaryless]`; `[CompleteSpace E]` is a hypothesis of the
   theorem. The output is a curve `f : ℝ → TangentBundle I M` with
   `f 0 = ⟨p, v⟩` and `IsMIntegralCurveAt f (gvfChart g p) 0`.

2. **Projection to `M`.** Set `γ t := (f t).proj`. Then `γ 0 = p` and
   `IsGeodesicAt g γ 0` packages the integral-curve property of `f` into
   the integral-curve geodesic predicate (with chart basepoint `α := p`).

The headline theorem `exists_geodesic_with_initial_velocity_at` returns `IsGeodesicAt g γ 0` —
the local geodesic predicate at `t = 0`. The chart-`γ(t)` second-derivative
form `HasGeodesicEquationAt g γ 0` is a separate downstream bridge once the
chart-derivative properties of the projection are recorded.
-/

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff

namespace PetersenLib
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]


/-- **Math.** **Picard-Lindelöf lift.** For a smooth Riemannian metric `g`, point
`p : M`, and tangent vector `v : T_p M`, on a boundaryless smooth manifold
modelled on a complete inner-product space, there exists a curve
`f : ℝ → TangentBundle I M` with `f 0 = ⟨p, v⟩` that is a local integral
curve of `geodesicVectorFieldChart g p` at `0`. -/
theorem exists_isMIntegralCurveAt_geodesicVectorFieldChart
    (g : RiemannianMetric I M) [I.Boundaryless] [CompleteSpace E]
    (p : M) (v : TangentSpace I p) :
    ∃ f : ℝ → TangentBundle I M,
      f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 := by
  classical
  have hp_src : p ∈ (chartAt H p).source := mem_chart_source H p
  have hsmooth : ContMDiffAt I.tangent I.tangent.tangent ∞
      (fun q : TangentBundle I M =>
        (⟨q, geodesicVectorFieldChart (I := I) g p q⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (⟨p, v⟩ : TangentBundle I M) :=
    geodesicVectorFieldChart_contMDiffAt (I := I) g p
      (p₀ := (⟨p, v⟩ : TangentBundle I M)) hp_src
  have hsmooth1 : ContMDiffAt I.tangent I.tangent.tangent 1
      (fun q : TangentBundle I M =>
        (⟨q, geodesicVectorFieldChart (I := I) g p q⟩ :
          TangentBundle I.tangent (TangentBundle I M)))
      (⟨p, v⟩ : TangentBundle I M) :=
    hsmooth.of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))
  exact
    exists_isMIntegralCurveAt_of_contMDiffAt_boundaryless
      (I := I.tangent) (M := TangentBundle I M)
      (v := geodesicVectorFieldChart (I := I) g p)
      (t₀ := (0 : ℝ)) (x₀ := (⟨p, v⟩ : TangentBundle I M)) hsmooth1

/-- **Math.** The base projection of a curve `f : ℝ → TangentBundle I M` to a curve
`γ : ℝ → M`, namely `γ t := (f t).proj`. -/
def projectCurve (f : ℝ → TangentBundle I M) : ℝ → M := fun t => (f t).proj

@[simp] lemma projectCurve_apply (f : ℝ → TangentBundle I M) (t : ℝ) :
    projectCurve (I := I) f t = (f t).proj := rfl

/-- **Math.** If the lifted curve starts at `⟨p, v⟩`, its projection starts at `p`. -/
lemma projectCurve_zero_of_lift {f : ℝ → TangentBundle I M} {p : M} {v : E}
    (hf0 : f 0 = (⟨p, v⟩ : TangentBundle I M)) :
    projectCurve (I := I) f 0 = p := by
  simp [projectCurve, hf0]

section ChartedPicardLindelof

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Local existence of geodesics with prescribed initial velocity.** For
a smooth Riemannian metric `g`, an initial point `p : M`, and an initial
velocity `v : T_p M`, there exists a curve `γ : ℝ → M` through `p`, together
with a lift `f : ℝ → TangentBundle I M`, such that

* `f 0 = ⟨p, v⟩` (the lift carries the prescribed initial data);
* `γ` is the base projection of `f`;
* `γ 0 = p`;
* `f` is a local integral curve of the chart-fixed geodesic vector field
  `geodesicVectorFieldChart g p` at `t = 0`;
* `IsGeodesicAt g γ 0` holds — `γ` is a local geodesic at the initial
  time, with chart basepoint `p`.

Here `IsGeodesicAt g γ 0` is the integral-curve form of the geodesic
predicate at `t = 0`; promoting it to a geodesic `IsGeodesic g γ` for all
times requires extending the integral curve to all of `ℝ`, which is a
separate downstream step. -/
theorem exists_geodesic_with_initial_velocity_at
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ∃ γ : ℝ → M, ∃ f : ℝ → TangentBundle I M,
      f 0 = (⟨p, v⟩ : TangentBundle I M) ∧
      γ = projectCurve (I := I) f ∧
      γ 0 = p ∧
      IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g p) 0 ∧
      IsGeodesicAt (I := I) g γ 0 := by
  obtain ⟨f, hf0, hf⟩ :=
    exists_isMIntegralCurveAt_geodesicVectorFieldChart (I := I) g p v
  refine ⟨projectCurve (I := I) f, f, hf0, rfl,
    projectCurve_zero_of_lift (I := I) hf0, hf, ?_⟩
  refine ⟨p, f, fun t => rfl, ?_, hf⟩
  have h0 : (f 0).proj = p := projectCurve_zero_of_lift (I := I) hf0
  rw [h0]; exact mem_chart_source H p

/-- **Math.** The manifold derivative of the lifted curve at `0`. -/
theorem hasMFDerivAt_lift_zero
    {g : RiemannianMetric I M} {f : ℝ → TangentBundle I M}
    (hf : IsMIntegralCurveAt f (geodesicVectorFieldChart (I := I) g
      (Bundle.TotalSpace.proj (f 0))) 0) :
    HasMFDerivAt 𝓘(ℝ) I.tangent f 0
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        (geodesicVectorFieldChart (I := I) g
          (Bundle.TotalSpace.proj (f 0)) (f 0)))) :=
  hf.hasMFDerivAt

end ChartedPicardLindelof

end Geodesic
end PetersenLib

end

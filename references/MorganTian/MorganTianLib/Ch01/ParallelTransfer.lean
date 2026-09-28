import MorganTianLib.Ch01.JacobiChartTransfer
import MorganTianLib.Ch01.ParallelFrame

/-!
# Poincaré Ch. 1, §1.3 — chart-change covariance of parallel transport

`IsParallelSolOn g α u V a b` is a *coordinate* expression of the intrinsic
condition `∇_{γ'} V = 0`: it says the chart-`α` reading of `V` solves the
first-order linear system `V' = −Γ_α(u̇, V)(u)`.  Being intrinsic, the
condition must not depend on the chart used to write it down.  This file
proves that, closing for parallel transport the same chart-coherence gap that
`JacobiChartTransfer` closed for the Jacobi pair system.

The point is that a parallel field along a long geodesic cannot be produced in
a single chart: the geodesic leaves every chart.  Gluing chart-local solutions
requires moving a certificate from one chart to an overlapping one, which is
exactly `IsParallelSolOn.transfer`.

Main results:

* `chartTransitionPackage` — the shared analytic package along a geodesic
  lying in two chart sources: the `β`-reading of any field along `γ` is
  eventually the transition derivative applied to its `α`-reading; that
  transition derivative is differentiable in time along the curve; and the
  `β`-chart velocity is the tangent coordinate change of the `α`-chart
  velocity.  (This is the first-order half of the package used by
  `IsJacobiFieldOn.transfer`, isolated so that both the second-order Jacobi
  system and the first-order parallel system can consume it.)
* `IsParallelSolOn.transfer` — **the chart-change theorem for parallel
  transport**: along a geodesic lying in the sources of the charts at `α` and
  at `β`, a chart-`α` parallel certificate for the intrinsic field `V` yields
  the chart-`β` certificate.

The mechanism is the same cancellation as in the Jacobi case, in its simplest
instance.  Writing `C(σ) = D(τ_{αβ})(u_α(σ))` for the transition derivative,
the `β`-reading is `V_β = C V_α`, so the product rule gives
`V_β' = C' V_α + C V_α'`.  The inhomogeneous second-derivative term `C' V_α`
is exactly what the Christoffel transformation law
(`Riemannian.chartChristoffelContraction_change`) contributes when `Γ_α` is
pushed to `Γ_β`, and the two cancel, leaving `V_β' = −Γ_β(u̇_β, V_β)(u_β)`.
No curvature term appears: parallel transport is first order.

Blueprint: `lem:parallel-frame`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1;
do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.6.
-/

open Set Riemannian Riemannian.Tensor Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-! ### The shared transition package along a geodesic -/

/-- **Math.** The analytic package underlying every chart-change theorem along
a geodesic `γ` whose piece `γ([a, b])` lies in the sources of the charts at
`α` and at `β`.  At each time `τ ∈ [a, b]`:

1. for **every** field `V` along `γ`, the chart-`β` reading of `V` agrees, near
   `τ`, with the transition derivative applied to its chart-`α` reading;
2. that transition derivative `σ ↦ D(τ_{αβ})(u_α(σ))` is differentiable in
   time along the curve, with derivative `D²(τ_{αβ})(u_α(τ))[u̇_α(τ)]`;
3. the chart-`β` velocity of the geodesic is the tangent coordinate change of
   its chart-`α` velocity;
4. at `τ` the transition derivative *is* the tangent coordinate change.

Blueprint: `lem:parallel-frame`, `lem:jacobi-field-coordinates`. -/
theorem chartTransitionPackage
    {g : RiemannianMetric I M} {γ : ℝ → M} {α β : M} {a b : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrcα : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H α).source)
    (hsrcβ : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H β).source)
    {τ : ℝ} (hτ : τ ∈ Icc a b) :
    (∀ V : ℝ → E, chartVectorRep (I := I) γ β V =ᶠ[𝓝 τ]
        fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α V σ)) ∧
      HasDerivAt (fun σ => fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)))
        (fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
          (extChartAt I α (γ τ))
          (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ ∧
      deriv (fun σ => extChartAt I β (γ σ)) τ
        = tangentCoordChange I α β (γ τ)
            (deriv (fun σ => extChartAt I α (γ σ)) τ) ∧
      fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
        = tangentCoordChange I α β (γ τ) := by
  classical
  have hxα := hsrcα τ hτ
  have hxβ := hsrcβ τ hτ
  have hcτ := hγc τ hτ
  have hyT : extChartAt I α (γ τ)
      ∈ chartTransitionSource (I := I) (M := M) α β :=
    extChartAt_mem_chartTransitionSource (I := I) hxα hxβ
  have hsymm : (extChartAt I α).symm (extChartAt I α (γ τ)) = γ τ :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hxα)
  -- the fixed-chart geodesic curve is two-sidedly differentiable at `τ`
  have hu : HasDerivAt (fun σ => extChartAt I α (γ σ))
      (deriv (fun σ => extChartAt I α (γ σ)) τ) τ := by
    have hev := (hgeo τ hτ).eventually_hasDerivAt_extChartAt hcτ hxα
    exact hev.self_of_nhds.differentiableAt.hasDerivAt
  -- first derivative of the transition map at the chart image
  have hTd : HasFDerivAt (chartTransition (I := I) α β)
      (tangentCoordChange I α β (γ τ)) (extChartAt I α (γ τ)) := by
    have h0 := hasFDerivAt_chartTransition (I := I) hyT
    rwa [hsymm] at h0
  -- eventual membership of the feet in both chart sources
  have hev_mem : ∀ᶠ σ in 𝓝 τ,
      γ σ ∈ (chartAt H α).source ∧ γ σ ∈ (chartAt H β).source := by
    have h₁ : γ ⁻¹' (chartAt H α).source ∈ 𝓝 τ :=
      hcτ.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hxα)
    have h₂ : γ ⁻¹' (chartAt H β).source ∈ 𝓝 τ :=
      hcτ.preimage_mem_nhds ((chartAt H β).open_source.mem_nhds hxβ)
    filter_upwards [h₁, h₂] with σ h1 h2
    exact ⟨h1, h2⟩
  -- eventual identification of the β-reading through the transition map
  have hrep : ∀ V : ℝ → E, chartVectorRep (I := I) γ β V =ᶠ[𝓝 τ]
      fun σ => fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α V σ) := by
    intro V
    filter_upwards [hev_mem] with σ hσ
    have hyσ : extChartAt I α (γ σ)
        ∈ chartTransitionSource (I := I) (M := M) α β :=
      extChartAt_mem_chartTransitionSource (I := I) hσ.1 hσ.2
    have hsymmσ : (extChartAt I α).symm (extChartAt I α (γ σ)) = γ σ :=
      (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hσ.1)
    have hfdσ : fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)) = tangentCoordChange I α β (γ σ) := by
      rw [fderiv_chartTransition (I := I) hyσ, hsymmσ]
    show chartVectorRep (I := I) γ β V σ
      = fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α V σ)
    rw [hfdσ, chartVectorRep_apply, chartVectorRep_apply]
    exact (tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) (γ σ),
        by rw [extChartAt_source]; exact hσ.1⟩,
        by rw [extChartAt_source]; exact hσ.2⟩).symm
  -- derivative of the transition-derivative along the curve
  have hC' : HasDerivAt (fun σ => fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
        (extChartAt I α (γ τ))
        (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ :=
    (hasFDerivAt_fderiv_chartTransition (I := I) hyT).comp_hasDerivAt τ hu
  -- derivative of the β-reading of the base geodesic
  have huβ : HasDerivAt (fun σ => extChartAt I β (γ σ))
      (tangentCoordChange I α β (γ τ)
        (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ := by
    have hcomp := hTd.comp_hasDerivAt τ hu
    have hcong : (fun σ => extChartAt I β (γ σ)) =ᶠ[𝓝 τ]
        fun σ => chartTransition (I := I) α β (extChartAt I α (γ σ)) := by
      filter_upwards [hev_mem] with σ hσ
      exact (chartTransition_extChartAt (I := I) hσ.1).symm
    exact hcomp.congr_of_eventuallyEq hcong
  exact ⟨hrep, hC', huβ.deriv, hTd.fderiv⟩

/-! ### The chart-change theorem for parallel transport -/

/-- **Math.** **Chart-change covariance of parallel transport** along a
geodesic.  If the piece `γ([a, b])` lies in the sources of the charts at `α`
and at `β`, then the chart-`α` parallel certificate for the intrinsic field
`V` transfers to the chart at `β`.

The chart readings are related by the curve-dependent tangent coordinate
change `C(σ) = tangentCoordChange I α β (γ σ)`, so `V_β = C V_α`.  The product
rule produces the second-derivative term `C'(τ)[V_α(τ)]` of the transition
map, which cancels exactly against the inhomogeneous term of the Christoffel
transformation law `Riemannian.chartChristoffelContraction_change`.  This is
the first-order (curvature-free) instance of `IsJacobiFieldOn.transfer`.

Blueprint: `lem:parallel-frame`. -/
theorem IsParallelSolOn.transfer
    {g : RiemannianMetric I M} {γ : ℝ → M} {V : ℝ → E} {α β : M} {a b : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrcα : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H α).source)
    (hsrcβ : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H β).source)
    (h : IsParallelSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α V) a b) :
    IsParallelSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β V) a b := by
  classical
  intro τ hτ
  obtain ⟨hrep, hC', hduβ, hfd⟩ :=
    chartTransitionPackage (I := I) hgeo hγc hsrcα hsrcβ hτ
  have hVrep := hrep V
  have hxα := hsrcα τ hτ
  have hxβ := hsrcβ τ hτ
  have hVτ : chartVectorRep (I := I) γ β V τ
      = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ) := hVrep.self_of_nhds
  -- product rule: `(C V_α)' = C' V_α + C V_α'`, with `V_α' = −Γ_α(u̇_α, V_α)`
  have hval := (hC'.hasDerivWithinAt.clm_apply (h τ hτ)).congr_of_eventuallyEq
    (hVrep.filter_mono nhdsWithin_le_nhds) hVrep.self_of_nhds
  -- the transformation law turns the right-hand side into `−Γ_β(u̇_β, V_β)`
  have heq : -Geodesic.chartChristoffelContraction (I := I) g β
        (deriv (fun σ => extChartAt I β (γ σ)) τ)
        (chartVectorRep (I := I) γ β V τ) (extChartAt I β (γ τ))
      = fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
          (extChartAt I α (γ τ))
          (deriv (fun σ => extChartAt I α (γ σ)) τ)
          (chartVectorRep (I := I) γ α V τ)
        + fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (-Geodesic.chartChristoffelContraction (I := I) g α
              (deriv (fun σ => extChartAt I α (γ σ)) τ)
              (chartVectorRep (I := I) γ α V τ)
              (extChartAt I α (γ τ))) := by
    rw [hfd, map_neg,
      chartChristoffelContraction_change (I := I) g β α hxβ hxα
        (deriv (fun σ => extChartAt I α (γ σ)) τ)
        (chartVectorRep (I := I) γ α V τ),
      hduβ, hVτ, hfd]
    abel
  rw [heq]
  exact hval

end MorganTianLib

end

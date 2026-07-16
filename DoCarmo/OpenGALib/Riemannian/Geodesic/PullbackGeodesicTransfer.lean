import OpenGALib.Riemannian.Connection.PullbackChristoffelLaw
import OpenGALib.Riemannian.Geodesic.EquationTransfer

/-!
# A local isometry reflects geodesics (the geodesic map-transfer)

For a smooth local diffeomorphism `f : M → M'` between manifolds modelled on the same model
space `E` and a metric `g'` on `M'`, the pulled-back metric `h = f^*g'` makes `f` a local
isometry. This file proves that `f` **reflects** geodesics: if `f ∘ γ` solves the `g'`-geodesic
ODE, then `γ` solves the `h`-geodesic ODE.

The mechanism is the Christoffel transformation law under `f`
(`chartChristoffelContraction_mapReading`, do Carmo Ch. 7 `lem:dc-ch7-3-4-rays-are-geodesics`):
writing `u` for the chart reading of `γ` and `W = F ∘ u` for the reading of `f ∘ γ`
(`F = ` chart reading of `f`), the chain rule gives `W' = A u'`, `W'' = D²F(u', u') + A u''` with
`A = dF`, and the transformation law `A(Γ^h(u', u')) = Γ^{g'}(A u', A u') + D²F(u', u')` makes the
geodesic operator transform by `A` alone: `A(u'' + Γ^h(u', u')) = W'' + Γ^{g'}(W', W') = 0`. Since
`f` is a local diffeomorphism, `A = dF` is injective, so `u'' + Γ^h(u', u') = 0`.

This is the map-analog of `SolvesGeodesicODEAt.transfer` (the chart-transition case).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace Geodesic

open Riemannian RiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [Bundle.RiemannianBundle (TangentSpace I : M → Type _)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'} [I'.Boundaryless]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **A local diffeomorphism reflects the geodesic ODE.** If the chart reading of `γ`
at its foot is differentiable near `t₀` with second derivative `a` there, `γ` is continuous at
`t₀`, and `f ∘ γ` solves the `g'`-geodesic ODE at `t₀`, then `γ` solves the geodesic ODE of the
pulled-back metric `f^*g'` at `t₀`. -/
theorem solvesGeodesicODEAt_of_comp {f : M → M'} (hf : IsLocalDiffeomorph I I' ∞ f)
    (g' : RiemannianMetric I' M') {γ : ℝ → M} {t₀ : ℝ} (hcont : ContinuousAt γ t₀)
    (hu_ev : ∀ᶠ τ in 𝓝 t₀,
      HasDerivAt (chartReading (I := I) (γ t₀) γ)
        (deriv (chartReading (I := I) (γ t₀) γ) τ) τ)
    (a : E) (ha : HasDerivAt (deriv (chartReading (I := I) (γ t₀) γ)) a t₀)
    (hcompsolve : SolvesGeodesicODEAt (I := I') g' (f (γ t₀)) (fun τ => f (γ τ)) t₀) :
    SolvesGeodesicODEAt (I := I)
      (pullbackOfSmoothImmersion g' f (dcSmoothImmersion_of_isLocalDiffeomorph hf)) (γ t₀) γ t₀ := by
  classical
  have himm := dcSmoothImmersion_of_isLocalDiffeomorph (I := I) (I' := I') hf
  obtain ⟨hWev, b, hWb, hWeq⟩ := hcompsolve
  set u : ℝ → E := chartReading (I := I) (γ t₀) γ with hu_def
  set W : ℝ → E := chartReading (I := I') (f (γ t₀)) (fun τ => f (γ τ)) with hW_def
  set F : E → E := mapReading (I := I) (I' := I') f (γ t₀) (f (γ t₀)) with hF_def
  -- membership near `t₀`
  have hmem : ∀ᶠ τ in 𝓝 t₀,
      γ τ ∈ (chartAt H (γ t₀)).source ∧ f (γ τ) ∈ (chartAt H' (f (γ t₀))).source := by
    have h1 : (chartAt H (γ t₀)).source ∈ 𝓝 (γ t₀) :=
      (chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀))
    have h2 : (chartAt H' (f (γ t₀))).source ∈ 𝓝 (f (γ t₀)) :=
      (chartAt H' (f (γ t₀))).open_source.mem_nhds (mem_chart_source H' (f (γ t₀)))
    have hfcont : ContinuousAt (fun τ => f (γ τ)) t₀ :=
      himm.1.continuous.continuousAt.comp hcont
    filter_upwards [hcont.preimage_mem_nhds h1, hfcont.preimage_mem_nhds h2] with τ hτ1 hτ2
    exact ⟨hτ1, hτ2⟩
  have hsrc : ∀ᶠ τ in 𝓝 t₀,
      u τ ∈ mapReadingSource (I := I) (I' := I') f (γ t₀) (f (γ t₀)) := by
    filter_upwards [hmem] with τ hτ
    have hτ1' : γ τ ∈ (extChartAt I (γ t₀)).source := by rw [extChartAt_source]; exact hτ.1
    refine ⟨(extChartAt I (γ t₀)).map_source hτ1', ?_⟩
    rw [mem_preimage, hu_def, chartReading_def, (extChartAt I (γ t₀)).left_inv hτ1',
      extChartAt_source]
    exact hτ.2
  have hw_eq : ∀ᶠ τ in 𝓝 t₀, W τ = F (u τ) := by
    filter_upwards [hmem] with τ hτ
    have hτ1' : γ τ ∈ (extChartAt I (γ t₀)).source := by rw [extChartAt_source]; exact hτ.1
    show extChartAt I' (f (γ t₀)) (f (γ τ))
      = extChartAt I' (f (γ t₀)) (f ((extChartAt I (γ t₀)).symm (extChartAt I (γ t₀) (γ τ))))
    rw [(extChartAt I (γ t₀)).left_inv hτ1']
  have ht₀src : u t₀ ∈ mapReadingSource (I := I) (I' := I') f (γ t₀) (f (γ t₀)) :=
    hsrc.self_of_nhds
  have hu' : HasDerivAt u (deriv u t₀) t₀ := hu_ev.self_of_nhds
  -- eventual differentiability of `W` with the chain-rule formula
  have hw_deriv : ∀ᶠ τ in 𝓝 t₀,
      HasDerivAt W (fderiv ℝ F (u τ) (deriv u τ)) τ := by
    filter_upwards [hu_ev, hsrc, hw_eq.eventually_nhds] with τ hτ hτsrc hτeq
    have hFF : HasFDerivAt F (fderiv ℝ F (u τ)) (u τ) := hasFDerivAt_mapReading himm hτsrc
    exact (hFF.comp_hasDerivAt τ hτ).congr_of_eventuallyEq hτeq
  have hw_deriv_eq : (fun τ => deriv W τ)
      =ᶠ[𝓝 t₀] fun τ => fderiv ℝ F (u τ) (deriv u τ) := by
    filter_upwards [hw_deriv] with τ hτ
    exact hτ.deriv
  -- second derivative of `W` at `t₀`
  have hc : HasDerivAt (fun τ => fderiv ℝ F (u τ))
      (fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀)) t₀ :=
    (hasFDerivAt_fderiv_mapReading himm ht₀src).comp_hasDerivAt t₀ hu'
  have hΦ : HasDerivAt (fun τ => fderiv ℝ F (u τ) (deriv u τ))
      (fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀)
        + fderiv ℝ F (u t₀) a) t₀ := hc.clm_apply ha
  have hw_snd : HasDerivAt (deriv W)
      (fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀)
        + fderiv ℝ F (u t₀) a) t₀ := hΦ.congr_of_eventuallyEq hw_deriv_eq
  have hw_v : deriv W t₀ = fderiv ℝ F (u t₀) (deriv u t₀) := hw_deriv_eq.self_of_nhds
  have hbval : b = fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀)
      + fderiv ℝ F (u t₀) a := hWb.unique hw_snd
  -- the transformation law at the foot
  have hlaw := chartChristoffelContraction_mapReading (I := I) (I' := I') hf g'
    (mem_chart_source H (γ t₀)) (mem_chart_source H' (f (γ t₀))) (deriv u t₀) (deriv u t₀)
  -- `hlaw : A (Γ^h(v,v)(u t₀)) = Γ^{g'}(A v, A v)(W t₀) + D²F(v,v)`
  have hut₀ : extChartAt I (γ t₀) (γ t₀) = u t₀ := rfl
  have hWt₀ : extChartAt I' (f (γ t₀)) (f (γ t₀)) = W t₀ := rfl
  rw [hut₀, hWt₀] at hlaw
  refine ⟨hu_ev, a, ha, ?_⟩
  -- goal: `a + Γ^h(deriv u t₀, deriv u t₀)(u t₀) = 0`; apply the injective `A = dF(u t₀)`
  apply injective_fderiv_mapReading (I := I) (I' := I') hf ht₀src
  rw [map_add, map_zero, hlaw]
  -- `A a + (Γ^{g'}(A v, A v)(W t₀) + D²F(v,v)) = 0`
  have hgoal : fderiv ℝ F (u t₀) a
      + (Geodesic.chartChristoffelContraction (I := I') g'
            (f (γ t₀)) (fderiv ℝ F (u t₀) (deriv u t₀)) (fderiv ℝ F (u t₀) (deriv u t₀)) (W t₀)
        + fderiv ℝ (fderiv ℝ F) (u t₀) (deriv u t₀) (deriv u t₀)) = 0 := by
    have hWeq' : b + Geodesic.chartChristoffelContraction (I := I') g'
        (f (γ t₀)) (deriv W t₀) (deriv W t₀) (W t₀) = 0 := hWeq
    rw [hw_v, hbval] at hWeq'
    rw [← hWeq']; abel
  exact hgoal

end Geodesic
end Riemannian

end

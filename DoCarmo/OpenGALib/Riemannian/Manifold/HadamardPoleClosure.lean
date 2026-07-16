import OpenGALib.Riemannian.Manifold.HadamardPoleRays
import OpenGALib.Riemannian.Geodesic.PullbackGeodesicTransfer
import OpenGALib.Riemannian.Exponential.GlobalExp

/-!
# The radial lines of `T_pN` are `exp_p^*g`-geodesics — closing the poles theorem

This file discharges the last analytic input of do Carmo's poles theorem
(`rem:dc-ch7-3-4`, `HadamardModel.expDiffeomorphOfPole`): for a pole `p` (where
`exp_p : T_pN → N` is a local diffeomorphism), the radial lines `s ↦ s • v` of `T_pN` are
geodesics of the pulled-back metric `(\exp_p)^*g`.

The proof is `exp_p ∘ rayCurve v = globalGeodesic g hg p v`, a genuine `g`-geodesic (radial
homogeneity `expMapGlobal_smul` + `isGeodesic_globalGeodesic`), fed through the geodesic
map-transfer (`solvesGeodesicODEAt_of_comp`, a local diffeomorphism reflects geodesics): since
`exp_p` is a local isometry for `(\exp_p)^*g`, the ray — being mapped to a `g`-geodesic — is an
`(\exp_p)^*g`-geodesic. This is `lem:dc-ch7-3-4-rays-are-geodesics`, formerly the sole
`\notready` residual of the poles remark.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace Riemannian
namespace HadamardModel

open Riemannian.Geodesic Riemannian.Exponential RiemannianMetric

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [Module.Finite ℝ F] [FiniteDimensional ℝ F] [NeZero (Module.finrank ℝ F)] [CompleteSpace F]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ F H} [I.Boundaryless]
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [CompleteSpace N]

/-- **Math.** do Carmo Ch. 7, `lem:dc-ch7-3-4-rays-are-geodesics`. **The radial lines of `T_pN`
are geodesics of the pulled-back metric.** For a pole `p` (i.e. `exp_p` a local diffeomorphism),
every ray `s ↦ s • v` of `T_pN` is a geodesic of `(\exp_p)^*g`. Proof: `exp_p` maps the ray to
`globalGeodesic g hg p v` (a genuine `g`-geodesic), and being a local diffeomorphism it reflects
geodesics (`solvesGeodesicODEAt_of_comp`). -/
theorem expMap_rays_are_geodesics (g : RiemannianMetric I N) (hg : g.IsRiemannianDist) (p : N)
    (hpole : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞
      (fun v : HadamardModel F => expMapGlobal g hg p (HadamardModel.toModel v))) :
    ∀ v : F,
      Geodesic.IsGeodesic (I := 𝓘(ℝ, F)) (HadamardModel.pullbackMetric g hpole)
        (rayCurve v) := by
  intro v t₀
  set f : HadamardModel F → N :=
    fun w => expMapGlobal g hg p (HadamardModel.toModel w) with hf_def
  -- `f ∘ rayCurve v = globalGeodesic g hg p v`, a `g`-geodesic
  have hcompeq : (fun τ => f (rayCurve v τ)) = globalGeodesic g hg p v := by
    funext τ; exact expMapGlobal_smul g hg p v τ
  have hcompsolve : SolvesGeodesicODEAt (I := I) g (f (rayCurve v t₀))
      (fun τ => f (rayCurve v τ)) t₀ := by
    have hgeo : Geodesic.IsGeodesic (I := I) g (fun τ => f (rayCurve v τ)) := by
      rw [hcompeq]; exact isGeodesic_globalGeodesic g hg p v
    exact hasGeodesicEquationAt_iff_solvesGeodesicODEAt.mp (hgeo t₀)
  -- the source chart reading of the ray is `fun τ => τ • v` (identity chart)
  have hu_eq : chartReading (I := 𝓘(ℝ, F)) (rayCurve v t₀) (rayCurve v) = fun τ => (τ : ℝ) • v := by
    funext τ
    show extChartAt 𝓘(ℝ, F) (rayCurve v t₀) (rayCurve v τ) = (τ : ℝ) • v
    rw [extChartAt_hadamard]; rfl
  have hu_ev : ∀ᶠ τ in 𝓝 t₀,
      HasDerivAt (chartReading (I := 𝓘(ℝ, F)) (rayCurve v t₀) (rayCurve v))
        (deriv (chartReading (I := 𝓘(ℝ, F)) (rayCurve v t₀) (rayCurve v)) τ) τ := by
    rw [hu_eq]
    refine Filter.Eventually.of_forall fun τ => ?_
    have hd : deriv (fun τ : ℝ => τ • v) τ = v := by
      simpa using ((hasDerivAt_id τ).smul_const v).deriv
    rw [hd]
    simpa using (hasDerivAt_id τ).smul_const v
  have ha : HasDerivAt
      (deriv (chartReading (I := 𝓘(ℝ, F)) (rayCurve v t₀) (rayCurve v))) 0 t₀ := by
    rw [hu_eq]
    have hderiv : deriv (fun τ : ℝ => τ • v) = fun _ => v := by
      funext τ; simpa using ((hasDerivAt_id τ).smul_const v).deriv
    rw [hderiv]
    exact hasDerivAt_const t₀ v
  have hcont : ContinuousAt (rayCurve v) t₀ := (continuous_rayCurve v).continuousAt
  letI : Bundle.RiemannianBundle (fun x : HadamardModel F => TangentSpace 𝓘(ℝ, F) x) :=
    HadamardModel.flatBundle F
  have hsolve := solvesGeodesicODEAt_of_comp (I := 𝓘(ℝ, F)) (I' := I) hpole g hcont hu_ev 0 ha
    hcompsolve
  exact hsolve.hasGeodesicEquationAt hcont (mem_chart_source F (rayCurve v t₀))

/-- **Math.** do Carmo Ch. 7, **Remark 3.4 (poles), fully discharged.** For a complete, simply
connected `N` with a pole `p`, the exponential map `exp_p : T_pN → N` is a diffeomorphism; in
particular `N ≃ ℝⁿ`. This is `expDiffeomorphOfPole` with its last analytic input `hrays` supplied
by `expMap_rays_are_geodesics` (via `hrays_of_rayGeodesic`). -/
def expDiffeomorphOfPole_of_pole [ConnectedSpace N] [SimplyConnectedSpace N]
    [LocPathConnectedSpace N] (g : RiemannianMetric I N) (hg : g.IsRiemannianDist) (p : N)
    (hpole : IsLocalDiffeomorph 𝓘(ℝ, F) I ∞
      (fun v : HadamardModel F => expMapGlobal g hg p (HadamardModel.toModel v))) :
    Diffeomorph 𝓘(ℝ, F) I (HadamardModel F) N ∞ :=
  diffeomorphOfPole_of_rayGeodesic g hpole (expMap_rays_are_geodesics g hg p hpole)

end HadamardModel
end Riemannian

end

import OpenGALib.Riemannian.Jacobi.FlowChainContDiff
import OpenGALib.Riemannian.Exponential.GlobalExp

/-!
# The exponential map is globally `C^∞`

This file discharges the sole remaining hypothesis of the Cartan–Hadamard theorem
(do Carmo Ch. 7): the global `C^∞` smoothness of the exponential map,
`ContMDiff 𝓘(ℝ,E) I ∞ (expMapGlobal g hg p)`. It is the capstone of the chart-chain
globalization of the geodesic-flow smoothness:

* `exists_geodesic_flow_step_contDiff` — the `C^∞` geodesic flow step at an arbitrary
  chart state (off the zero section);
* `exists_geodesic_flowstep_partition_contDiff` — the `C^∞` chart/flow-step partition of a
  compact geodesic;
* `exists_geodesic_contDiff_chain_nbhd` — the `C^∞` chart chain, computing nearby geodesic
  endpoints.

The final assembly is clean because `globalGeodesic g hg p w` is, *by construction*, the
geodesic whose chart-`p` velocity at time `0` is `w`
(`hasDerivAt_chartReading_globalGeodesic`). Hence the chain's initial-state map
`ι : w ↦ (φ_α(p), (φ_α ∘ γ_w)'(0))` is **affine**: its velocity component is the fixed
tangent coordinate change `w ↦ tangentCoordChange I p α p · w`
(`deriv_extChartAt_eq_tangentCoordChange`), so no differentiation of `exp` near the zero
section is needed. Composing the `C^∞` chain map `F₀` with `ι`, and reading off the terminal
chart, gives the chart-`ζ` reading `w ↦ φ_ζ(exp_p w)` as `C^∞` near every `v`; the manifold
inverse-chart bridge upgrades this to `ContMDiffAt`, and `ContMDiff` is pointwise.

Once passed as `hsmooth` to `Riemannian.Jacobi.hadamardDiffeomorphOfNonpos`, this closes
`thm:dc-ch7-3-1` (Cartan–Hadamard) and `lem:dc-ch7-3-2` unconditionally.

Blueprint: `thm:dc-ch7-3-1`, `lem:dc-ch7-3-2`.
Reference: do Carmo, *Riemannian Geometry*, Ch. 7, §3.
-/

open Set Filter Function
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Exponential

open Riemannian Riemannian.Geodesic Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [CompleteSpace E]

/-- **Math.** **The exponential map is globally `C^∞`** (do Carmo Ch. 7, the smoothness
input to the Cartan–Hadamard theorem). On a complete Riemannian manifold, the global
exponential map `expMapGlobal g hg p : T_pM → M` is `ContMDiff 𝓘(ℝ,E) I ∞`.

Fix `v`. The geodesic `γ = globalGeodesic v` has chart-`p` velocity `v` at time `0`, so the
`C^∞` chart chain (`exists_geodesic_contDiff_chain_nbhd`) applied to `γ` yields a map `F₀`,
`C^∞` at the initial chart state, that reads off the time-`1` endpoint of every nearby
geodesic. Feeding `γ_w = globalGeodesic w`, whose initial chart-`α` state is the *affine*
function `ι w = (φ_α(p), tangentCoordChange I p α p · w)`, gives
`φ_ζ(exp_p w) = (F₀ (ι w))₁` on a neighbourhood of `v`, hence the chart-`ζ` reading of
`exp_p` is `C^∞` at `v`; the inverse-chart bridge makes `exp_p` `ContMDiffAt` at `v`. -/
theorem contMDiff_expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] (p : M) :
    ContMDiff 𝓘(ℝ, E) I ∞ (fun w : E => expMapGlobal (I := I) g hg p w) := by
  intro v
  classical
  -- the geodesic `γ = globalGeodesic v`
  set γ : ℝ → M := globalGeodesic (I := I) g hg p v with hγdef
  have hγgeo : Geodesic.IsGeodesic (I := I) g γ := isGeodesic_globalGeodesic g hg p v
  have hγcont : Continuous γ := continuous_globalGeodesic g hg p v
  have hγ0 : γ 0 = p := globalGeodesic_zero g hg p v
  -- the `C^∞` chart chain applied to `γ` on `univ`
  obtain ⟨α, ζ, F₀, W₀, hα0, hζ1, hF₀cd, hF₀base, hW₀, hend⟩ :=
    exists_geodesic_contDiff_chain_nbhd (I := I) g (U := univ) isOpen_univ (subset_univ _)
      (fun t _ => hγgeo t) hγcont.continuousOn
  have hpα : p ∈ (chartAt H α).source := hγ0 ▸ hα0
  have hpp : p ∈ (chartAt H p).source := mem_chart_source H p
  -- the fixed chart-velocity change and the *affine* initial-state map `ι`
  set C : E →L[ℝ] E := tangentCoordChange I p α p with hCdef
  set ι : E → E × E := fun w => (extChartAt I α p, C w) with hιdef
  have hιcd : ContDiff ℝ ∞ ι := ContDiff.prodMk contDiff_const C.contDiff
  -- the chart-`α` state of `globalGeodesic w` at time `0` is `ι w`
  have hstate : ∀ w : E, (extChartAt I α (globalGeodesic (I := I) g hg p w 0),
      deriv (fun t => extChartAt I α (globalGeodesic (I := I) g hg p w t)) 0) = ι w := by
    intro w
    have h0 : globalGeodesic (I := I) g hg p w 0 = p := globalGeodesic_zero g hg p w
    -- chart-`p` velocity is `w` (by construction of `globalGeodesic`)
    have hvelp : deriv (fun t => extChartAt I p (globalGeodesic (I := I) g hg p w t)) 0 = w := by
      have h := (hasDerivAt_chartReading_globalGeodesic g hg p w).deriv
      simpa only [chartReading_def] using h
    -- chart-`α` velocity is `C w = tangentCoordChange I p α p w`
    have hvelα : deriv (fun t => extChartAt I α (globalGeodesic (I := I) g hg p w t)) 0
        = tangentCoordChange I p α p w := by
      rw [deriv_extChartAt_eq_tangentCoordChange (I := I)
        (fun t _ => isGeodesic_globalGeodesic g hg p w t) (mem_univ 0)
        (continuous_globalGeodesic g hg p w).continuousAt
        (by rw [h0]; exact hpp) (by rw [h0]; exact hpα), h0, hvelp]
    refine Prod.ext ?_ ?_
    · show extChartAt I α (globalGeodesic (I := I) g hg p w 0) = extChartAt I α p
      rw [h0]
    · show deriv (fun t => extChartAt I α (globalGeodesic (I := I) g hg p w t)) 0 = C w
      rw [hvelα, hCdef]
  -- `ι v` is the chain's initial state, where `F₀` is `C^∞`
  have hxv : ι v = (extChartAt I α (γ 0), deriv (fun s => extChartAt I α (γ s)) 0) :=
    (hstate v).symm
  have hF₀v : ContDiffAt ℝ ∞ F₀ (ι v) := by rw [hxv]; exact hF₀cd
  -- the chart reading `w ↦ (F₀ (ι w))₁` is `C^∞` at `v`
  have hreadcd : ContDiffAt ℝ ∞ (fun w => (F₀ (ι w)).1) v :=
    contDiffAt_fst.comp v (hF₀v.comp v hιcd.contDiffAt)
  -- the neighbourhood `T = ι⁻¹' W₀` of `v`
  set T : Set E := ι ⁻¹' W₀ with hTdef
  have hTnhds : T ∈ 𝓝 v := by
    refine (hιcd.continuous.continuousAt).preimage_mem_nhds ?_
    rw [hxv]; exact hW₀
  -- on `T`: the endpoint identity and terminal-chart membership
  have hkey : ∀ w ∈ T, extChartAt I ζ (expMapGlobal (I := I) g hg p w) = (F₀ (ι w)).1
      ∧ expMapGlobal (I := I) g hg p w ∈ (chartAt H ζ).source := by
    intro w hw
    obtain ⟨heq, hsrc⟩ := hend (ι w) hw (globalGeodesic (I := I) g hg p w)
      (continuous_globalGeodesic g hg p w) (isGeodesic_globalGeodesic g hg p w)
      (by rw [globalGeodesic_zero]; exact hpα) (hstate w)
    have hfst := congrArg Prod.fst heq
    exact ⟨hfst.symm, hsrc⟩
  -- the chart-`ζ` reading of `exp_p` is `C^∞` at `v`
  have hcda : ContDiffAt ℝ ∞
      (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) v := by
    refine hreadcd.congr_of_eventuallyEq ?_
    filter_upwards [hTnhds] with w hw using (hkey w hw).1
  -- manifold inverse-chart bridge
  have hζv : expMapGlobal (I := I) g hg p v ∈ (chartAt H ζ).source :=
    (hkey v (mem_of_mem_nhds hTnhds)).2
  have hfM : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞
      (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) v := hcda.contMDiffAt
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I ζ).symm
      (extChartAt I ζ (expMapGlobal (I := I) g hg p v)) := by
    refine (contMDiffOn_extChartAt_symm ζ).contMDiffAt ((isOpen_extChartAt_target ζ).mem_nhds ?_)
    exact PartialEquiv.map_source _ (by rw [extChartAt_source]; exact hζv)
  refine (hsymm.comp v hfM).congr_of_eventuallyEq ?_
  filter_upwards [hTnhds] with w hw
  show expMapGlobal (I := I) g hg p w
      = (extChartAt I ζ).symm (extChartAt I ζ (expMapGlobal (I := I) g hg p w))
  exact ((extChartAt I ζ).left_inv (by rw [extChartAt_source]; exact (hkey w hw).2)).symm

end Riemannian.Exponential

end

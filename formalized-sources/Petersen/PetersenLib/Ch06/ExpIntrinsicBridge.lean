import PetersenLib.Ch05.GeodesicCompleteness
import PetersenLib.Ch05.ExponentialMap
import PetersenLib.Riemannian.Exponential.RayGeodesic

/-!
# The chart-anchored and intrinsic exponential maps agree near the origin

This project carries **two** exponential maps, and nothing until now related them.

* `PetersenLib.expMap g p v` (`Ch05/ExponentialMap.lean`) is `Exponential.expMap`, the value at
  time `1` of the **maximal geodesic read in the single chart at `p`**
  (`geodesicVectorFieldChart g p`).  Its domain is therefore anchored to `(chartAt H p).source`:
  off that chart the defining vector field is *zero*
  (`Exponential.geodesicVectorFieldChart_eq_zero_of_notMem`, `Ch05/ExpChartConfinement.lean`), so
  `expMap` silently returns a junk value rather than the true `exp_p(v)`.
* `PetersenLib.geodesicMaximalCurve g p v 1` (`Ch05/GeodesicCompleteness.lean`) is the
  **intrinsic**, moving-foot maximal geodesic — the one `Ch05/UniformInjectivityRadiusDiffeo.lean`
  states its uniform results for, precisely because (as its docstring at
  `compactSet_uniformCInftyDiffeo` records) the chart-anchored domain "makes this statement
  false".

## Why the bridge matters

`chartAt H p` is an arbitrary per-point choice with no uniform size, so the `expMap` chart-escape
radius admits **no locally uniform lower bound** in `p`.  Any argument needing one `δ` good for
*every* basepoint along a curve — e.g. discharging the `hf` hypothesis of `secondVariationEnergy`
(Thm. 6.1.4) for the exponential variation `(s,t) ↦ exp_{c(t)}(sV(t))`, which is the gap between
this project and Bonnet–Synge (Lem. 6.3.1) — therefore **cannot** be run against `expMap`.  It
must be run against the intrinsic exponential, and this file is what lets the two pointwise
results already proved for `expMap` (`Ch06/ExpVariation.lean`) be carried across.

Note this corrects `Ch06/ExpVariation.lean`'s closing docstring, which frames the missing
ingredient as "a uniform normal radius along `c` — another chart cover, of the same shape as
Thm. 6.1.4's".  The uniform radius is not the obstruction; `expMap`'s chart anchoring is.

## The proof is short because the lever was already in the tree

`Exponential.exists_isGeodesicOn_expMap_ray` (`Riemannian/Exponential/RayGeodesic.lean`)
emits, for `‖u‖ < ρ`, exactly four conjuncts about the ray `t ↦ exp_p(t·u)`:
`γ 0 = p`, `HasDerivAt (φ_p ∘ γ) u 0`, `ContinuousOn γ (Ioo (-b) b)`, `IsGeodesicOn g γ (Ioo (-b) b)`.
Those are — modulo the order — precisely the four fields of
`IsGeodesicWithInitialOn g γ (Ioo (-b) b) 0 p u` (`Ch05/Geodesics.lean`).  So the ray *is* an
admissible witness for the intrinsic initial-value problem, and `geodesicMaximalCurve_eqOn`
identifies it with the intrinsic maximal geodesic on all of `Ioo (-b) b`.  Since the ray lemma
delivers `b > 1`, evaluating at `t = 1` is legal and gives the bridge.

This was available and unused: no lemma anywhere in `PetersenLib` (including `Vendored/`)
previously identified `expMap g p v` with `geodesicMaximalCurve g p v 1`.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]

/-- **Math.** **The chart-anchored exponential agrees with the intrinsic one near the origin.**
At every `p` there is a radius `ρ > 0` such that

$$\exp_p(u) = \gamma^{\max}_{p,u}(1) \qquad (\|u\| < \rho),$$

where the left side is `PetersenLib.expMap` (the chart-at-`p` reading) and the right side is the
intrinsic moving-foot maximal geodesic `PetersenLib.geodesicMaximalCurve`.

This is the *only* bridge between this project's two exponential encodings; see the module
docstring for why the distinction is load-bearing (the chart-anchored domain has no locally
uniform radius, so all uniform-in-basepoint results are stated intrinsically).

**Proof.**  `Exponential.exists_isGeodesicOn_expMap_ray` says that for `‖u‖ < ρ` the ray
`t ↦ exp_p(t·u)` starts at `p` with chart velocity `u`, and is continuous and geodesic on
`Ioo (-b) b` with `b > 1`.  Reassembled in the order `IsGeodesicWithInitialOn` wants, that is
literally a witness for the intrinsic initial-value problem with data `(p, u)` at time `0`; so
`geodesicMaximalCurve_eqOn` makes the intrinsic maximal geodesic agree with the ray throughout
`Ioo (-b) b`.  As `b > 1`, evaluate at `t = 1` and use `one_smul`. -/
theorem expMap_eq_geodesicMaximalCurve_of_small (g : RiemannianMetric I M) (p : M) :
    ∃ ρ > (0 : ℝ), ∀ u : E, ‖u‖ < ρ →
      expMap (I := I) g p (u : TangentSpace I p)
        = geodesicMaximalCurve (I := I) g p (u : TangentSpace I p) 1 := by
  obtain ⟨ρ, b, hρ, hb, -, hmain⟩ := Exponential.exists_isGeodesicOn_expMap_ray (I := I) g p
  have hb0 : (0 : ℝ) < b := lt_trans one_pos hb
  refine ⟨ρ, hρ, fun u hu => ?_⟩
  -- the ray lemma's four conjuncts, in its order: value, velocity, continuity, geodesic
  obtain ⟨h0, hd, hc, hgeo⟩ := hmain u hu
  -- `IsGeodesicWithInitialOn` wants them as: continuity, value, velocity, geodesic
  have hivp : IsGeodesicWithInitialOn (I := I) g
      (fun t : ℝ => expMap (I := I) g p ((t • u : E) : TangentSpace I p))
      (Ioo (-b) b) 0 p (u : TangentSpace I p) := ⟨hc, h0, hd, hgeo⟩
  have h0mem : (0 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb0⟩
  have h1mem : (1 : ℝ) ∈ Ioo (-b) b := ⟨by linarith, hb⟩
  have heq := geodesicMaximalCurve_eqOn (I := I) g isOpen_Ioo ordConnected_Ioo h0mem hivp h1mem
  simpa using heq.symm

end PetersenLib

end

import PetersenLib.Ch05.DistanceEDistBridge
import PetersenLib.Ch05.GaussLemma
import PetersenLib.Vendored.OpenGA.Exponential.NormalBallEDist

/-!
# Petersen Ch. 5, §5.5.2 — short geodesics are segments (the distance lower bound)

Toward Petersen Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`): near a
point `p`, the radial geodesic `t ↦ exp_p(tv)` realizes the Riemannian distance,
`d(p, exp_p v) = |v|_g`, and is therefore a segment.

This file lands the **substantive (lower-bound) half**,
`expMap_riemannianDistance_ge`:

  there is `ε > 0` with `B_ε(0) ⊂ T_pM` in the exponential domain and, for every
  `v` with `‖v‖ < ε`, `|v|_g = √(g_p(v, v)) ≤ d(p, exp_p v)` —

i.e. **no curve from `p` to `exp_p v` is shorter than the radial geodesic**.  This
is the geometrically substantive direction (the trivial competitor gives only the
reverse `≤`).

The proof composes two pieces, staying entirely at the `riemannianEDist` /
`pathELength` layer (no ambient metric-space structure is needed):

* the vendored do Carmo competitor bound
  `PetersenLib.Exponential.exists_le_pathELength` (do Carmo Ch. 3, Prop. 3.6): on a
  small ball, **every** `C¹` curve `σ` from `p` to `exp_p v` has
  `pathELength ≥ ofReal √(g_p(v, v))`.  Since `riemannianEDist` is the infimum of
  `pathELength` over `C¹` paths, this gives `ofReal √(g_p(v,v)) ≤ riemannianEDist p (exp_p v)`;
* the bridge `riemannianEDist_le_ofReal_riemannianDistance`
  (`Ch05/DistanceEDistBridge.lean`): `riemannianEDist p q ≤ ofReal (d(p, q))`.

Chaining, `ofReal √(g_p(v,v)) ≤ riemannianEDist p (exp_p v) ≤ ofReal (d(p, exp_p v))`,
whence `√(g_p(v,v)) ≤ d(p, exp_p v)`.

**The reverse (upper) bound `d(p, exp_p v) ≤ |v|_g` is not proved here** — it needs
the radial geodesic `t ↦ exp_p(tv)` to be a Petersen competitor, i.e. **`C^∞`**,
whereas only `C¹` (chart-level `C²`) regularity of the exponential map is available
at this layer.  That is the documented `C^∞`-ODE smooth-dependence gap of §5.2
(`GeodesicLocal.lean`); once it closes, the upper bound is the one-line radial
competitor and Thm 5.5.4 becomes unconditional.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory Metric
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]
  [T2Space M] [ConnectedSpace M]

/-- **Math.** Petersen Ch. 5, Theorem 5.5.4 (`thm:pet-ch5-short-geodesics-segments`),
**lower-bound half**: near `p` the exponential map does not decrease radial
distance.  There is `ε > 0` such that the model ball `B_ε(0) ⊂ T_pM` lies in the
exponential domain and, for every `v` with `‖v‖ < ε`,

`√(g_p(v, v)) ≤ d(p, exp_p v)` :

no piecewise-`C^∞` curve from `p` to `exp_p v` is shorter than the radial geodesic
of `g`-length `|v|_g`.  This is the geometrically substantive direction of "short
geodesics are segments"; the reverse (competitor) inequality needs the `C^∞`
regularity of the radial geodesic (the §5.2 ODE gap) and is not proved here. -/
theorem expMap_riemannianDistance_ge (g : RiemannianMetric I M) (p : M) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : E, ‖w‖ < ε → (w : TangentSpace I p) ∈ expDomain (I := I) g p) ∧
      ∀ v : E, ‖v‖ < ε →
        Real.sqrt (g.metricInner p v v)
          ≤ riemannianDistance (I := I) g p (expMap (I := I) g p (v : TangentSpace I p)) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨ε, c, hε, -, hdom, -, -, -, hlower, -, -, -⟩ :=
    Exponential.exists_le_pathELength (I := I) g p
  refine ⟨ε, hε, hdom, fun v hv => ?_⟩
  -- at the chart origin the chart-Gram pairing is the intrinsic inner product
  have hchart : chartMetricInner (I := I) g p (extChartAt I p p) v v
      = g.metricInner p v v := by
    rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g p (mem_chart_source H p) v v,
      trivializationAt_symm_self]
  -- lower bound on the mathlib edistance: every `C¹` competitor is at least as
  -- long as the radial geodesic, so their infimum `riemannianEDist` is too
  have hge : ENNReal.ofReal (Real.sqrt (g.metricInner p v v))
      ≤ Manifold.riemannianEDist I p (expMap (I := I) g p (v : TangentSpace I p)) := by
    by_contra hlt
    obtain ⟨σ, hσ0, hσ1, hσC1, hσlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (not_le.mp hlt)
    have hlow := hlower v hv σ hσC1 hσ0 hσ1
    rw [hchart] at hlow
    exact absurd hσlen (not_lt.mpr hlow)
  -- the bridge: `riemannianEDist ≤ ofReal (riemannianDistance)`
  have hbridge := riemannianEDist_le_ofReal_riemannianDistance (I := I) g p
    (expMap (I := I) g p (v : TangentSpace I p))
  exact (ENNReal.ofReal_le_ofReal_iff
    (riemannianDistance_nonneg (I := I) g p
      (expMap (I := I) g p (v : TangentSpace I p)))).mp (le_trans hge hbridge)

end PetersenLib

end

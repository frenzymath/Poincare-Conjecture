# Hopf–Rinow — build plan (do Carmo Ch. 7 §2, task LEHENG.7)

Goal: prove Hopf–Rinow (`../HopfRinow.lean`) faithful to **do Carmo,
*Riemannian Geometry*, Ch. 7** (geodesic-sphere + connectedness argument — NO
Morse / second variation / spray). The facade holds the statements; this file
tracks the upstream stack.

## STATUS 2026-07-14: COMPLETE — every theorem of the facade is proved, 0 sorry

Both remaining walls fell:

* **Wall 2 (corner rigidity + growth induction): DOWN.**
  `Exponential/CornerRigidity.lean` (do Carmo Ch. 3, Cor. 3.9 equality case),
  `Exponential/GrowthInduction.lean` (`exists_minimizing_geodesic_of_forall_geodesic`,
  `exists_minimizing_geodesic_unitInterval` — statement f) from geodesic
  completeness at one point), all 0-sorry.
* **f) ⟹ b) ⟹ c): DOWN.** `Exponential/ProperAssembly.lean`
  (`properSpace_of_forall_geodesic`, `completeSpace_of_forall_geodesic`):
  Bolzano–Weierstrass on the initial data of the minimizing geodesics, fed by
  **endpoint continuity of geodesics in their initial data** — the last
  analytic ingredient, proved in `Geodesic/EndpointContinuity.lean`
  (`exists_conv_step_eval`: flow-box step with moving evaluation times, via
  the κ-rescaled affine readback `IsGeodesic.eq_uniform_flow_readback_affine`
  and Lipschitz-in-data flow evaluation `tendsto_flow_eval`) and globalized
  by the clopen argument in `Geodesic/EndpointContinuityGlobal.lean`
  (`tendsto_geodesic_eval_of_tendsto_initialData`).
* The facade `../HopfRinow.lean` now proves `hopfRinow` (c ⟺ d),
  `complete_of_isGeodesicallyComplete` (d ⟹ c),
  `complete_of_geodesicallyComplete_at` (a ⟹ c),
  `exists_minimizing_geodesic` (f), and
  `isGeodesicallyComplete_of_compactSpace` (Cor. 2.9), all axiom-clean.

The historical plan below is kept for the record.

## Status (2026-07-11, run 0052)

**DONE — metric-distance layer (① of the old plan).** mathlib's
`Manifold.riemannianEDist` / `IsRiemannianManifold` framework is adopted as
the definition of do Carmo's `d(p,q)` (ch07 nodes 2.4–2.7 wired):

| Piece | Where |
|---|---|
| `edist ≤ pathELength` on C¹ paths, `eVariationOn ≤ pathELength` | `EVariationLePathELength.lean` (0 sorry) |
| `d` finite on connected `M`, `d > 0` for `p ≠ q`, `MetricSpace.ofRiemannianMetric` | `../../Metric/RiemannianDistance.lean` (0 sorry) |
| compatibility predicate `g.IsRiemannianDist` (edist = Riemannian distance of `g`) — the standing hypothesis of every Hopf–Rinow statement; without it the statements are FALSE | ibid. |
| Thm 2.8 b)⟺e) (proper ⟺ divergent compact exhaustion) | `../../../MetricGeometry/ProperExhaustion.lean` (0 sorry) |
| Thm 2.8 b)⟹c) | mathlib `complete_of_proper` |

**DONE — statement repair.** `IsGeodesicallyComplete` is now *intrinsic*
(`∀ (p,v), ∃ γ : ℝ → M` through it with `IsGeodesic g γ`, i.e.
`HasGeodesicEquationAt` at every time). The old
`maximalGeodesicInterval g p v = univ` form was NOT geodesic completeness:
`MaximalGeodesicWitness` anchors its integral curve at the chart of the
initial point for the whole interval (junk field outside), so it fails for,
e.g., the round circle. See `MaximalInterval.lean` docstring ("gluing across
chart changes … deferred").

## Remaining walls (the `sorry` frontiers in `../HopfRinow.lean`)

**Wall 1 — moving-chart geodesic theory: DOWN (run 0070).**
c)⟹d) (`isGeodesicallyComplete_of_complete`) is PROVED, axiom-clean.
The stack, all 0-sorry:

| Piece | Where |
|---|---|
| Christoffel change-of-chart law `A Γ^β(v,w) = Γ^α(Av,Aw) + D²τ(v,w)` | `Connection/ChartChristoffelChange.lean` (run 0052) |
| chart-independence of the geodesic equation (`SolvesGeodesicODEAt.transfer`, moving ⟺ any fixed chart) | `Geodesic/EquationTransfer.lean` |
| spray-flow solutions are intrinsic geodesics (`isGeodesicOn_sprayBase`), seed existence with prescribed velocity | `Geodesic/FlowGeodesic.lean`, `Geodesic/Completeness.lean` |
| intrinsic uniqueness on intervals (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`, Grönwall + clopen; needs `[T2Space M]` — false on the line with two origins) | `Geodesic/IntrinsicUniqueness.lean` |
| local Gram lower bound `‖w‖² ≤ c⟨w,w⟩_G` + pole-generalised speed bridge | `Geodesic/HopfRinow/GramBound.lean` |
| Cauchy endpoint limit, forward extension (Gram-bounded velocity + κ-rescaling into the uniform flow + uniqueness gluing), symmetric-interval sup gluing (`exists_global_geodesic`) | `Geodesic/Completeness.lean` |

The chart-anchored `maximalGeodesicInterval` framework was NOT needed:
`Completeness.lean` uses only the generic Picard–Lindelöf flow
(`exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt`) and the
intrinsic predicates.

**DONE (run 0052) — intrinsic constant speed + locally Lipschitz.**
`MetricBridge.lean` (0 sorry): (i) `chartMetricInner_extChartAt_eq_metricInner`
(chart Gram inner product = `g.metricInner` on trivialization readbacks),
`trivializationAt_symm_eq_tangentCoordChange`, and the fiber-(e)norm bridge
`enorm_tangent_eq_sqrt_metricInner` under `⟨g.toRiemannianMetric⟩`.
`ConstantSpeed.lean` (0 sorry): (ii) the velocity bridge
(`HasGeodesicEquationAt.hasMFDerivAt` / `mfderiv_apply_one`: moving-foot chart
derivative = `mfderiv γ t 1`), the first-order chart-change transfer
(`eventually_hasDerivAt_extChartAt`, via `tangentCoordChange` — NO Christoffel
law needed), **geodesics are C¹** (`IsGeodesicOn.contMDiffOn`), `speedSq`
constant (`IsGeodesicOn.speedSq_eq`), and **geodesics are locally Lipschitz**
(`IsGeodesicOn.edist_le` / `dist_le`, `d(γa,γb) ≤ √speedSq·(b−a)`, consuming
`edist_le_pathELength_of_cmdiff` under `g.IsRiemannianDist`). This is the
Cauchy-at-the-endpoint half of c)⟹d). Hypotheses: `IsGeodesicOn g γ s` +
`ContinuousOn γ s` on OPEN (pre)connected `s` — continuity of `γ` is NOT
implied by the junk-tolerant `HasGeodesicEquationAt` and must be carried.

What c)⟹d) still needs from Wall 1: intrinsic local existence/uniqueness →
maximal intrinsic geodesics on open intervals, and the uniform-time flow
(`exists_uniform_geodesic_flow`) to extend past the Cauchy limit point.

**Wall 2 — Ch. 3 §3 minimizing geodesics** (blocks d)⟹c)/f),
`exists_minimizing_geodesic`, `complete_of_geodesicallyComplete_at`).
Status after run 0070 (the C¹-dependence gap I-0086 was closed by LEHENG.3;
the chart-polar Gauss-lemma stack `Exponential/{GaussLemma,Minimizing,
LocalDiffeo,MinimizingPiecewise}.lean` landed):

*DONE — the metric normal ball and the step engine (0 sorry, axiom-clean):*

| Piece | Where |
|---|---|
| chart-length bridge (`pathELength` = chart integral of the Gram speed) | `HopfRinow/CurveReadback.lean` |
| metric normal ball: `d(p, exp_p v) = √⟨v,v⟩ₚ`, escape estimate, δ-sphere **first-crossing** (`δ + ℓ(σ|[T,1]) ≤ ℓ(σ)`), exposed Gram bound | `Exponential/NormalBallEDist.lean` (`exists_edist_expMap_ball`, `exists_le_pathELength`) |
| **sphere-minimum decomposition** `d(p,q) = δ + min_{x∈S_δ(p)} d(x,q)`, min attained, `d(p,x₀)=δ`, `‖z₀‖ ≤ √c·δ` | ibid. (`exists_normalSphere_min_edist`) |
| **exp rays are intrinsic geodesics** on `(-b,b) ⊃ [0,1]` (ray ODE + `SolvesGeodesicODEAt.hasGeodesicEquationAt`) | `Exponential/RayGeodesic.lean` (`exists_isGeodesicOn_expMap_ray`) |
| **the full geodesic-sphere step**: `∃ γ` geodesic on `[0,1]`, `γ 0 = p`, `d(p,γ 1)=δ`, `d(p,q)=δ+d(γ 1,q)` | `Exponential/MinimizingStep.lean` (`exists_minimizing_step`) |

*Statement repair (run 0070):* `IsGeodesicallyComplete` now demands
`Continuous γ` — `HasGeodesicEquationAt` is junk-tolerant and does not rule
out discontinuous witnesses by itself; `exists_global_geodesic` supplies
continuity, so c)⟹d) was unaffected.

*REMAINING for d)⟹c)/f) — the induction and its one wall:*

1. **Corner rigidity** (do Carmo Ch. 3, Cor. 3.9, the equality case): a
   broken curve (geodesic + radial segment) realizing the distance between
   its endpoints has no corner. Equality analysis in the Gauss radius
   comparison (`Minimizing.lean`); THE remaining mathematical wall.
2. **The growth induction** (`thm:dc-ch7-2-8` a⟹f): fix unit-speed geodesic
   `γ` through the first sphere-min direction; `A = {s ∈ [δ,r] :
   d(γ s, q) = r − s}` is closed (continuity `continuous_riemannianEDist_right`
   + `Continuous γ`), contains `δ` (base = `exists_minimizing_step`), and
   `sup A < r` is pushed forward by the step at `γ(sup A)` + corner rigidity
   + intrinsic uniqueness (`IsGeodesicOn.eqOn_of_deriv_chartReading_eq`).
   Bookkeeping: subsegment-minimizing, unit-speed reparametrization
   (`IsGeodesicOn.speedSq_eq` for constant speed).
3. f)⟹b (closed balls compact): needs continuity of `exp_p` on **large**
   compact balls of `expDomain` (currently only small-ball continuity via the
   chart; likely: flow continuity + compactness gluing).

## Hard-won non-goals (do NOT build — off the path)

Morse index / index form, spray cocycle, weak-to-strong minimizer
regularity. do Carmo's proof uses none of these. The snapshot
`openga-bg-buildable-*` (45-file `HopfRinow/`) over-built exactly these and
shipped false statements; we do NOT inherit it.

# Plan: closing `cor:dc-ch5-2-5` → `lem:dc-ch7-3-2` → `thm:dc-ch7-3-1` (K≤0 Hadamard)

## ✅ STATUS UPDATE run 0148 s0010: `cor:dc-ch5-2-5` + `prop:dc-ch5-3-5` LANDED (axiom-clean, lib green 3286)

The ENTIRE Poincaré `ExpDifferential` cone is ported into `OpenGALib/Riemannian/Jacobi/`
(18 files, all axiom-clean). `expDifferential_eq_jacobiField` (= `cor:dc-ch5-2-5`) and
`expDifferential_injective_iff_not_conjugate` (= `prop:dc-ch5-3-5`) are available.
Remaining path to `lem:dc-ch7-3-2` / `thm:dc-ch7-3-1` is in the memory
`ch5-cor25-exp-c3-blocker` (steps 1–5): move `IsConjugatePointAt` to `JacobiManifold`,
port `JacobiRescale` + the Sturm-free half of `ExpLocalDiffeo`, then the one genuinely-new
piece `K≤0 ⟹ ¬IsConjugatePointAt` (manifold→frame Jacobi bridge feeding the already-landed
`frameJacobi_ne_zero_of_nonpos`), then assemble. Everything below is the earlier (pre-completion) plan.

---

Status as of run 0148 s0008. The **entire** do Carmo Ch7 Hadamard machine is `\leanok`
EXCEPT the two headline nodes, both `\notready`:

- `lem:dc-ch7-3-2` (intrinsic): `K ≤ 0 ⟹ exp_p is a local diffeomorphism`.
- `thm:dc-ch7-3-1`: Hadamard (assembles `lem:dc-ch7-3-2` + the already-`\leanok`
  covering/pole/assembly infra).

The frame-coordinate energy convexity is DONE (`Riemannian.Jacobi.jacobiCoefOp_quadratic_nonpos`,
`frameJacobi_ne_zero_of_nonpos` = `lem:dc-ch7-3-2-no-conjugate`, `\leanok`). The SOLE
remaining gap is the exp-differential ↔ Jacobi identity `cor:dc-ch5-2-5`:

    d(exp_p)_v (Z) = Y_Z(1),   Y_Z the Jacobi field with Y_Z(0)=0, ∇Y_Z(0)=Z.

Once this lands, `lem:dc-ch7-3-2` follows: a nonzero `Z ∈ ker d(exp_p)_v` gives a
Jacobi field vanishing at 0 and at 1 with `∇Y(0)=Z≠0` — contradicting the energy
convexity. Then `thm:dc-ch7-3-1` assembles via the (already-`\leanok`)
`Riemannian.DCExpandsMetric.diffeomorphOfSimplyConnectedOfGeodesicCompleteAt` +
`expDiffeomorphOfPole_of_pole` infra.

## The route: port the Poincaré (Morgan–Tian §1.4) flow-chain funnel into `Riemannian.Jacobi`

The identity is the composition of one-chart geodesic-flow steps along the compact
geodesic `[0,1]`, each step's derivative being the Jacobi variational transport
(`IsJacobiFieldOn.variational_transport`, DONE). Reference tree:
`/home/axel/OpenGA-Horizon/Poincare/PoincareLib/Ch01/`. The port is **Sturm-free**:
the Sturm/comparison cone (ComparisonFunctions, ScalarComparison, VectorSturm,
SturmContinuation, CurvatureSectionalBound, PointwiseCurvature, CurvatureFrameBridge)
is needed only for Bishop–Gromov (two-sided |Rm|≤K). For K≤0 Hadamard we use the
energy argument already landed. The Sturm files appeared in a naive import-cone only
because Poincaré's *monolithic* `JacobiManifold` pulls them; DoCarmo's split-port
already excised that.

### Already ported (DoCarmo `OpenGALib/Riemannian/Jacobi/`, all green/axiom-clean)
Geodesics, JacobiEquationODE, ParallelFrame, FrameReduction, JacobiField,
ChartCurvatureVector, ChartCurvatureContraction, CovariantCurvatureAlong,
SurfaceCurvatureCommutation, JacobiNonpositiveCurvature, PairJacobiField (chart pair
system + existence/uniqueness/superposition), SprayLinearization
(`isJacobiFieldOn_of_variational`), FlowStep (`exists_geodesic_flow_step`,
`IsJacobiFieldOn.variational_transport`), FlowStateChart, JacobiManifold
(`IsJacobiFieldAlongOn`, `eqOn_zero`), JacobiRestriction (`.mono`).

### Remaining port chain (bottom-up; Poincaré file → DoCarmo `Riemannian.Jacobi.*`)
Namespace surgery `PoincareLib`→`Riemannian.Jacobi` is near-mechanical (FlowStep
ported ~line-for-line), BUT each file needs a handful of helper lemmas that DoCarmo's
split-port reorganized under different names. Order:

1. **JacobiChartTransfer** — ✅ DONE run 0148 s0010 (ledger `fbb1ae0e32`, axiom-clean, lib green 3270).
   `IsJacobiFieldOn.transfer` + `chartCurvature_coordChange` landed. The 3 reconciliation-gap helpers
   (`curvatureFormAt_chartFrame` general realization, `chartMetricInner_pos`, `chartMetricInner_neg_left`)
   are in the NEW file `ChartCurvatureNaturality.lean` — `curvatureFormAt_chartFrame` is proved from
   OpenGALib's own `curvatureOperatorAt_chartBasis_expansion` (`Connection.ChartCurvatureMovingPoint`) +
   `curvatureOperatorAt`/`curvatureFormAt` multilinearity (`curvatureFormAt_sum₄`) + `chartCurvature`
   christoffel-multilinearity (`chartCurvature_sum₃`/`chartCurvature_basis`), so NO port of the divergent
   Poincaré `CurvatureFrameBridge`/`FrameReduction` cone was needed. Both registered in OpenGALib.lean.
2. **StateTransition**, **JacobiExistence** (`IsJacobiFieldAlongOn` existence + algebra),
   **ChartPartition** ← JacobiManifold.
3. **FlowGluing** ← StateTransition, FlowStep, JacobiExistence.
4. **FlowStepManifold**, **FlowComposition**, **JunctionStep** ← FlowGluing.
5. **GeodesicTranslation** ← FlowStepManifold.
6. **GeodesicOfState**, **FlowStepManifoldAt** ← GeodesicTranslation/StateTransition.
7. **GlobalExp** (DoCarmo already has `Exponential.expMapGlobal`; adapt),
   **FlowStepManifoldBall** ← FlowStepManifoldAt, FlowStateChart.
8. **FlowStepPartition** ← FlowStepManifoldBall, ChartPartition.
9. **FlowChainAssembly** ← FlowStepPartition, JunctionStep, JacobiRestriction, FlowComposition.
10. **FlowChainNbhd** ← FlowChainAssembly, GeodesicOfState (`exists_geodesic_jacobiTransport_chain_nbhd`).
11. **ExpDifferential** ← FlowChainNbhd, GlobalExp, JacobiExistence
    (`hasFDerivAt_chartReading_expMapGlobal`, `expDifferential_eq_jacobiField` = `cor:dc-ch5-2-5`).
12. **ConjugateDifferential** ← ExpDifferential (`expDifferential_injective_iff_not_conjugate`).
13. **K≤0 `ExpLocalDiffeo` variant** — like Poincaré `ExpLocalDiffeo` but feeding the
    conjugate-point input from `frameJacobi_ne_zero_of_nonpos` (energy) instead of Sturm.
    Delivers `lem:dc-ch7-3-2`.

## Derived math for the JacobiChartTransfer reconciliation (`ChartCurvatureNaturality.lean`)

`chartCurvature g α y = christoffelCurvature (chartChristoffelBilin g α) y`, and DoCarmo
has NO existing bridge to the intrinsic curvature. Key facts derived this session
(SIGN is real — christoffelCurvature has `∂_i − ∂_j`, `chartCurvatureCoef` has `∂_j − ∂_i`):

- **Basis identity:** `chartCurvature g α y (eᵢ)(eⱼ)(eₖ) = − ∑ₗ chartCurvatureCoef g α i j k l y • eₗ`.
- The coefficient in `curvatureOperatorAt_chartBasis_expansion` is LITERALLY
  `chartCurvatureCoef g α i j k l (extChartAt I α q)`.
- **Realization** (`chartCurvature_realize`): with `⟪v⟫ := tangentCoordChange I α x x v`,
  `⟪chartCurvature g α (extChartAt I α x) v w z⟫ = − curvatureOperatorAt x ⟪v⟫ ⟪w⟫ ⟪z⟫`.
- **Naturality** (`chartCurvature_coordChange`): both charts realize the same intrinsic
  vector; `tangentCoordChange I β x x` is injective (left inverse), so
  `chartCurvature g β (φ_β x)(Cv)(Cw)(Cz) = C(chartCurvature g α (φ_α x) v w z)`, `C = tangentCoordChange I α β x`.

Proof ingredients: full multilinearity of `curvatureOperatorAt`
(`curvatureOperatorAt_add/smul_{left,middle,right}`, present) + ADD the middle/right
multilinearity of `chartCurvature` (only left exists) + `(finBasis).sum_repr` +
`fderiv_clm_apply` for the fderiv-of-CLM step in the basis identity.

## DEAD ENDS (do not retry)
- Proving `chartCurvature_coordChange` from the connection transformation law directly
  → needs the 2nd-derivative cancellation, as hard as `IsJacobiFieldOn.transfer`. The
  intrinsic-`curvatureOperatorAt` naturality route is far shorter.
- Metric-compatibility route to the ray-geodesic fact is CIRCULAR (see LEHENG.14 memory).

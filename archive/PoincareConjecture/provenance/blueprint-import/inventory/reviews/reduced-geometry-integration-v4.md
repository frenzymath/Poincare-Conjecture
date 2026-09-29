# Reduced geometry: integration acceptance

Accepted by the main integration reviewer on 29 September 2026 at draft
SHA-256 `0ec11f86d8bb7fac9e859f25304eb395f9e187bcc7dd77ee68bee39289bb3a2e`.
Production source: `751329327f4f582797bda8e6cffe7cdf7531cc1d`.
The extinction calibration preceded this decision. The completed correction
session handed its draft and review back at
`04914376881823cc3d53ceeb9cf28cac8e44add9`.

The main reviewer read the complete corrected chapter continuously, from the
action definition through the final limitations. The appended independent
review in `reduced-geometry-v4.json` records six concrete corrected findings,
their substantive producers and exact Morgan--Tian comparisons. Main review
reused that work and directly read these corrected producers:

- `ReducedGeometry/ReducedLength/Barrier/ZeroResidualBarrier.lean`: one
  adapted comparison action and endpoint inverse supply both first
  derivatives and the Laplacian; the Harnack identity cancels their residual.
- `ReducedGeometry/ReducedVolume/WeakInequality/Comparison/ChartWeakComparison.lean`
  and `SemiconcaveWeakComparison.lean`: the positive calibrated density,
  weighted divergence identity, uniform upper operator bound, smooth-test
  Green identity and upper integral limit give the stated weak sign.
- `Generalized/ReducedGeometry/SmallTime/Stability/SmallTimeCoverage.lean`:
  compact initial vectors have unique minimizing branches on an open source
  neighborhood, using curvature on the entire past slab. Stability then
  supplies the exact compact-capture conclusion.
- `Generalized/Noncollapse/Cylinder/LocalEstimates.lean`: the compact
  initial-metric ball has radius exp(-n)/8 after unit rescaling; the local
  derivative theorem applies on the final half-cylinder. Scalar contraction
  and rescaling yield A/r^3 on the actual horizontal metric.

Paths above are relative to `PoincareLib/Geometry/RicciFlow/`.
The continuous review checked the square-root coefficients, positive-start
correction, cut-locus nullness and inverse-branch stability, raw-weight versus
regular-domain indicator, pairing ODE and stationary Euclidean map, exact
carrier/gauge/rescaling identities, and both noncollapse arguments. No
unresolved internal mathematical finding remains at this digest.

The ancient-models outgoing interface was checked against digest
`0fa8edc89baec2d0a30b496999ebf57017c1adff76fc708a41c5da9c6b6b0670`.
Finite past slabs have uniform curvature bounds; choosing tau_max=tau_i+1
keeps each minimizer time interior. Harnack gives K>=-L, hence the stated
gradient and time bounds. The common spacetime regular locus has null
complement in every slice, so Lipschitz weak derivatives and Fubini apply.
The signed Laplacian inequality and exact density/volume rescaling match the
ancient chapter's energy argument. Its limiting potential is not identified
with reduced length from an unconstructed limiting basepoint.

Later arbitrary generalized uses of noncollapse still require the actual
cylinder, compact terminal ball, closed-cylinder curvature bound, stable
family and open source W, action bound l0, image volume at least V,
r^2<=tau0<=taubar and constants uniform over the tested region. Generalized
transport alone does not supply this configuration or full-slice capture.
The compact ordinary proof constructs its own configuration explicitly.

This accepts the chapter relative to its explicit predecessor results.
It does not accept unfinished consumers or the whole book. Final text
integration, source links and complete PDF/site inspection remain pending.
No Lean build, audit or comparator was run; production evidence is reused.

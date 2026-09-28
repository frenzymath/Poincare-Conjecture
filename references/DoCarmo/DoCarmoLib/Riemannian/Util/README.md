# `Riemannian/Util/` — engineering tax for the Riemannian layer

Per OpenGA's anchor-purity discipline, anchor files expose only
`**Math.**`-tagged declarations; `**Eng.**` and `**Mixed.**` plumbing lives
under `Util/`. The files are grouped by the downstream layer they support.

## Directories

| Theme | Directory | Files |
| --- | --- | --- |
| Chart Jacobian | [`Chart/`](./Chart/) | `ChartJacobianCLM.lean`, `ChartJacobianEntries.lean`, `FlatChartDerivs.lean` |
| Tangent / section glue | [`Tangent/`](./Tangent/) | `TangentHelpers.lean`, `TensorBundleCoercions.lean`, `MfderivApplySection.lean` |
| Metric inner / notation | [`Metric/`](./Metric/) | `MetricInnerSmoothness.lean`, `MetricNotation.lean`, `CotangentFunctional.lean` |
| Covariant derivative | [`CovDeriv/`](./CovDeriv/) | `CovDerivSmoothness.lean`, `CovDerivBridges.lean` |
| Operator simp lemmas | [`Simp/`](./Simp/) | `OperatorSimp.lean` |

`ChartJacobianSmooth.lean` was renamed to `Chart/ChartJacobianCLM.lean`
because it proves smoothness of continuous-linear-map-valued chart-Jacobian
composites. `ChartJacobianSmoothness.lean` was renamed to
`Chart/ChartJacobianEntries.lean` because it proves scalar matrix-entry
smoothness.

`ConnectionLaplacianSimp.lean` and `DivergenceSimp.lean` were merged into
`Simp/OperatorSimp.lean`. `CovDerivBridges.lean` remains a separate
post-`LeviCivita` bridge file: it imports `Connection.LeviCivita`, while
`Connection.LeviCivita` imports `CovDerivSmoothness.lean`; absorbing the bridge
lemmas into `CovDerivSmoothness.lean` would create an import cycle.

## Conventions

* Every declaration docstring starts with `**Math.**`, `**Eng.**`, or
  `**Mixed.**`.
* Util files may contain engineering declarations; sibling anchor folders keep
  the mathematical surface clean.
* Subdirectory names carry the grouping role. File names describe concrete
  content and avoid generic `Helpers` / `Base` / `Foundation` suffixes except
  where the historical API name is retained.

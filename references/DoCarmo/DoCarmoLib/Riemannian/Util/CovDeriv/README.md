# CovDeriv

Covariant-derivative utilities are split by import direction.
`CovDerivSmoothness.lean` is pre-`LeviCivita` scaffolding used to construct the
connection. `CovDerivBridges.lean` is post-`LeviCivita` simp glue for
`covDeriv` and `covDerivAt`, kept separate to avoid an import cycle.

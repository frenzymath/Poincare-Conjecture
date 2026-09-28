# Simply connected three-manifolds: orientability component

## Exact statement, not a supplied orientation certificate

`PoincareConjecture.simplyConnected_threeManifold_orientable` proves the
positive-transition criterion for the tangent bundle of **every simply
connected C1 three-manifold** modeled on real three-space. In particular it
applies to a smooth three-manifold. It does not require compactness, curvature,
a surgery flow, a spherical presentation, a trivial tangent bundle, or an
orientation cover as an extra hypothesis.

The target `HasPositiveOrientationAtlas Z` is explicitly defined in terms of
the determinant of the original vector-bundle coordinate changes. It means
there are continuous local signs `σ_i : U_i → Bool` with

```text
sign(σ_j(x)) det(coordChange(i,j,x)) sign(σ_i(x)) > 0
```

on every chart overlap. This is the usual orientation criterion for a real
finite-dimensional vector bundle. The implementation does not claim to
instantiate a pre-existing Mathlib `OrientableManifold` class; the pinned
library does not supply that interface. The precise, exposed determinant
criterion and its construction are the formalized conclusion.

The stronger companion
`simplyConnected_threeManifold_positiveTangentFrames` constructs **actual
continuous invertible changes of local tangent frames** for which every
transition determinant is positive. These frame changes square to the
identity. They are the identity or the negative identity of real three-space,
whose determinants are respectively `1` and `-1`.

The bundle is Mathlib's real `tangentBundleCore`, not a substitute bundle.
Its coordinate changes are derivatives of the original manifold chart
transitions, as defined by the pinned tangent-bundle implementation. Neither
the topology nor the original charted-space data is replaced by a convenient
already-oriented structure. The frame formulation supplies the standard
tangent-bundle meaning of the blueprint's word “orientable”.

## What is constructed and proved

`Topology/OrientationCover.lean` starts from a real vector-bundle core. It
proves that its transition determinants are nonzero and obey the determinant
cocycle law. Taking their signs gives coordinate changes on a **discrete
two-point fibre**, preserving its two choices for positive determinant and
interchanging them for negative determinant.

Continuity and the cocycle law for this new fibre bundle are proved from the
original coordinate changes. Its local trivializations then give a covering
map. The covering-map property is a theorem, not a replacement input.

The identity map of the simply connected base is lifted through that cover,
starting from a chosen point in one fibre. This constructs a continuous
section. Reading the section in each local trivialization gives compatible
orientation signs. `Geometry/Orientability.lean` applies this construction to
the actual tangent bundle and realizes the signs as local frame changes.

This is the classical orientation-double-cover argument, using Mathlib's
covering-space lifting theorem. It is a formalization contribution, not a
new discovery of orientability or a new proof of the Poincare theorem.

## Reproduce and audit

The primary package retains Lean `v4.32.1`, Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`, and its existing pinned Hatcher
reference dependency. From the primary package directory:

```sh
lake exe cache get
lake build
lake env leanchecker --verbose --fresh PoincareConjectureTests
```

The default root test module imports the new orientability regressions before
its namespace-wide transitive axiom audit. The audit admits only `propext`,
`Classical.choice`, and `Quot.sound`. The two new production modules and their
regression module compile without new warnings. The existing Hatcher
`unitCircleCov` definition-style warning remains an unchanged dependency
warning; it is not a proof gap.

Seven named regression theorems check negative-determinant sign reversal,
two reversals, two genuinely distinct lifts of every base point, the ordinary
real three-space model, and a real two-chart vector bundle whose transition
is the negative identity. The latter requires opposite local signs and
rejects assigning the same orientation sign to both charts.

Negative mutation tests additionally require rejection of an injected axiom,
a placeholder proof, removal of simple connectivity, and replacing every
orientation-fibre transition by the identity. Temporary invalid files are
kept outside the library import graph, under ignored `.lake/` directories.

`leanchecker --fresh` replays proof terms with Lean's own kernel, not a
separately implemented checker. No independent expert review or prize
verification is asserted by these local checks.

## Remaining Poincare obligations

This component discharges the orientability step only. General Ricci flow
with surgery, geometric finite extinction, connected-sum reconstruction and
the three-dimensional smoothability bridge remain separate obligations.
`TopologicalPoincareStatement` is still an unproved target, and the final
Poincare blueprint node remains `notready`. A larger import graph or a
successful build is not interpreted as closure of that target.

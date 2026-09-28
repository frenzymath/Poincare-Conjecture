# Topological endgame: statement correspondence and verification

## Completed mathematical scope

The completed results are the last factor-elimination steps of the primary
Poincare blueprint, plus the smooth quotient infrastructure needed to state
the spherical-factor conclusion faithfully. These are classical results and
new formalization work, not a new mathematical proof of the Poincare theorem.

| Blueprint node | Actual Lean result |
| --- | --- |
| `lem:trivial-free-product-factors` | `freeProduct_factor_subsingleton`, for Mathlib's indexed free product, with injectivity derived from its universal property. |
| `lem:sphere-bundle-fundamental-group` | `sphere2CircleFundamentalGroupEquiv` for the actual product `Sphere2 × Circle`; `twistedSphereFundamentalGroupEquiv` for the actual antipodal mapping torus. Both yield the infinite cyclic group at every basepoint. |
| `lem:simply-connected-spherical-space-form` | `sphere3QuotientDiffeomorph` and `diffeomorph_sphere3_of_finite_quotient`, with the canonical smooth quotient atlas and an actual diffeomorphism, not only a homeomorphism. |

## Smooth finite quotients

`Topology/FiniteQuotient.lean` constructs a quotient covering from a finite,
free, continuous action on a locally compact Hausdorff path-connected space.
The monodromy map from the fundamental group of the base onto the opposite
acting group is a theorem from path lifting. A simply connected base thus
forces the group to be trivial and the projection to be bijective. The source
need only be path connected; no sphere classification is used to prove it
simply connected.

`Geometry/SmoothQuotient.lean` fills the smoothness bridge not supplied by
the pinned Mathlib orbit-quotient charted-space instance. A local inverse
branch composed with the projection agrees near any source point with one
group translate. This proves smooth chart changes, a smooth projection, and
smooth local inverses. For a trivial group every translate is the identity,
so the sphere specialization derives all the needed smoothness from the
topological argument. The final bijective local diffeomorphism is a genuine
global diffeomorphism for the canonical quotient atlas.

The general `Topology/SimplyConnectedCover.lean` also treats connected covers
that are not presented as faithful group quotients. A surjective local
diffeomorphism from a compact path-connected Hausdorff manifold to a simply
connected Hausdorff manifold is a diffeomorphism: compactness supplies the
covering property and path lifting supplies injectivity.

## The two sphere-bundle models

`Topology/MappingTorus.lean` uses the actual cyclic action

```text
n · (x,t) = (φ^n(x), t+n),    n ∈ ℤ.
```

Freeness is proved from the real coordinate. Proper discontinuity is proved
for arbitrary compact sets by bounding the possible integer translations
between their compact real-coordinate images. The fundamental-group map
arises from this covering, not from a field claiming a desired isomorphism.
For simply connected fibre, the full fundamental group is `Multiplicative ℤ`.

`Topology/MappingTorusProduct.lean` proves the identity-monodromy quotient
is homeomorphic to `X × (ℝ/ℤ)`: its orbit relation equals the kernel of the
open quotient map `(x,t) ↦ (x,t mod ℤ)`. `Topology/SphereBundle.lean` specializes
to the real two-sphere, uses the actual additive-circle/unit-circle
homeomorphism, and treats antipodal monodromy separately.

The simple-connectivity proof for the two-sphere is **reused**, with its
original authorship, from `HatcherLib.Ch1.Sphere` at upstream commit
`bb91a091f0b968f8bbe8d861e025a88d82b161be`. It uses the stereographic open cover
and the proved surjective portion of van Kampen. It does not require the
reference project's still-unproved general van Kampen kernel computation.
The dependency is pinned to the Hatcher subdirectory, so this primary package
can also build as a standalone prize-evidence package.

## Nonvacuous regression examples

`PoincareConjectureTopologyTests.lean` constructs the actual antipodal action
of the two-element group on the standard three-sphere. The action laws,
freeness, continuity, and smoothness are proved. The new quotient-atlas and
local-diffeomorphism results are exercised on this nontrivial action, and
the quotient is proved not simply connected. A separate trivial action on
a point proves that freeness cannot be omitted from group triviality.

The tests also exercise a real identity covering, free products of trivial
and infinite cyclic factors, the actual mapping-torus period relation, a
round trip through the product fundamental-group isomorphism, and a nonempty
twisted model with nontrivial fundamental group.

The default test target checks transitive axiom dependencies for every
declaration in the production and test namespaces. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. This audits imported
reference proofs used by the results as well as the new proofs.

## Reproduction and dependency warning

From this package directory, with the pinned Lean toolchain:

```sh
lake exe cache get
lake build
lake env leanchecker --verbose --fresh PoincareConjectureTests
```

The Hatcher dependency has one pre-existing style warning at
`HatcherLib/Ch1/Circle.lean:38`: `unitCircleCov` is a proposition-valued `def`.
The reference source remains unmodified. This warning must be distinguished
from errors or new warnings in the submitted production/test files. Therefore
a global warnings-as-errors build of the enlarged dependency cone is not
claimed. Source compilation, namespace-wide axiom checks, and fresh kernel
replay are separate checks; Lean's own replay is not an independently
implemented checker or designated human review.

## Exact remaining boundary

`Topology/Statement.lean` records the full **topological** target with only
compactness, the Hausdorff property, a three-dimensional topological atlas,
and simple connectivity. It is a proposition definition, not a proof or
an axiom, and does not import Mathlib's Poincare `proof_wanted` placeholder.

These results do **not** construct the general surgery flow, derive the
geometric width inequality, reconstruct a connected sum from surgery, prove
the geometric connected-sum van Kampen isomorphism, prove the arbitrary
connected-sum identity with the three-sphere, or establish three-dimensional
smoothability. The factor-interface theorems leave their actual geometric
fundamental-group isomorphism explicit. No omitted premise is replaced with
a target-equivalent assumption, and no percentage completion is assigned.

The existing prize-intake PR for this work is
[TheJustinSunPrize/awards #438](https://github.com/TheJustinSunPrize/awards/pull/438).
The upstream mathematical PR and prize-intake package are two destinations
for the same contribution, not independent priority or payment claims.
No full Poincare closure, award eligibility, recipient confirmation, or
payment decision is claimed by these completed components.

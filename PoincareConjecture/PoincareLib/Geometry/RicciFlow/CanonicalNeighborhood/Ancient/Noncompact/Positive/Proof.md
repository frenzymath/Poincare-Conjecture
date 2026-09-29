# Positive-curvature strong capped tubes

## Informal description

Assume the frozen M26 predecessor services. There is a universal positive
threshold such that, for each positive epsilon below it, a positive constant
can be chosen before the manifold and solution so that every connected
noncompact three-dimensional ancient kappa-solution with strictly positive
sectional curvature at time zero has its whole time-zero slice represented
by a strong capped epsilon-tube with that constant and the actual flow
connection on the cap.

## Informal proof

Choose a point soul and use the universal soul-centered core estimates.
Choose a sufficiently fine surrounding neck outside the controlled soul
ball, oriented toward infinity. Recenter and calibrate two larger-accuracy
necks in this source neck: one has the original central sphere, and the
negative endpoint of the other is that same sphere. The compact complementary
side and a buffered outer collar supply the cap. Point-soul coordinates and
the smooth sphere-ball neighborhood theorem identify its compact side with
a ball. A smooth axial expansion absorbs the outer collar and supplies the
Euclidean cap model.
Uniform curvature, distance, and calibrated volume estimates supply the cap
bounds. Universal noncollapse supplies the scalar-radius ball lower bound,
and the M26 scalar derivative theorem supplies the two derivative estimates.
Use the singleton cap cover to choose a maximal outgoing neck chain. Its
frontier could meet only the core of the original cap, which lies in the open
cap-chain union, so the union is the whole connected slice. The outgoing
cylinder construction preserves the cap and constructs its attachment.
The chain avoids the closed core, hence every tube point retains a strong
neck. A common constant absorbs all cap estimates before the solution is
chosen. The proof uses the separately tracked smooth sphere-ball theorem.

## Proposed formal statements

```lean
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Statement

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

theorem positiveCurvatureStrongCappedTubes
    (P : M26CanonicalNeighborhoodPredecessors.{u}) :
    ∃ epsilonStar : ℝ, 0 < epsilonStar ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ epsilonStar →
        ∃ C : ℝ, 0 < C ∧
          ∀ {M : Type u} [TopologicalSpace M]
            [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
            [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
            [T2Space M] [T3Space M] [SecondCountableTopology M]
            [ConnectedSpace M],
            ∀ K : AncientKappaSolution 3 M,
              ¬ IsCompact (Set.univ : Set M) →
              M27PositiveSectionalCurvature K 0 →
              Nonempty (M26StrongCappedTube K 0 epsilon C) := by
  sorry

end PoincareMT
```

## Informal translation

Fix the canonical-neighborhood predecessor services. There is a positive
threshold such that for each positive epsilon at most that threshold there
is a positive constant C with the following property. Every connected,
second-countable Hausdorff T3 smooth three-manifold with its Borel measurable
structure, carrying a noncompact ancient kappa-solution whose sectional
curvatures at time zero are strictly positive, is the connected union of a
strong cap with parameters epsilon and C and an epsilon-tube attached along
one of its ends. Every point of the tube is the center of a strong evolving
epsilon-neck at time zero. The retained cap connection is the actual flow
connection at time zero. C is chosen before the manifold and solution.

## Alignment review

Accepted by independent native reviewer `review_positive_alignment`, using
only the informal description and the translation by
`translate_positive_statement`. The quantifier order, whole-slice coverage,
strict positivity, and actual cap connection agree. Imported geometric
definitions were supplied to the translator as formal declarations only.
This fixes the theorem type, which is unchanged in the completed assembly.
The candidate above records the original statement-checking artifact; its
placeholder proof has been replaced in `Producer.lean`.

The reviewed declaration (from `theorem` through `sorry`, including the final
newline) has SHA-256
`3a5fa286e153c51988c2b2ade3ddbf1efe4ca14fdd85ec47effe14e6732b0167`.
It was checked against the PR #514 node at graph head
`bafd300817a14eaea0eb9425f2f9cd8e96ebad08` and workspace base
`3d940536e`. The named `Positive.Producer` build passed; the sole diagnostic
is the visible admission.

## Checked Construction

`Regions/Selection.lean` proves curvature-scale separation without scalar
normalization, then selects a strong neck at a universal distance from the
same point soul supplied to the Core interface. The entire joining neck is
outside the original controlled ball. `Regions/Basic.lean` constructs its
compact and noncompact complementary sides, their exact overlap cover, a
compact core with nonempty interior, and a bounded candidate cap carrier.
Every point outside the interior core is the center of a strong evolving
neck, including the core boundary; `core_or_strong` retains this information
for the compact branch's pointwise consumers.

`Regions/Smooth.lean` orients the actual neck outward and builds a smooth
domain structure on the compact side. `Bounds/Intrinsic.lean` joins an
interior point to its nearest boundary point by a minimizing geodesic that
stays inside, then joins through the neck. The resulting intrinsic diameter
is less than nine times the selected outer radius in the soul scalar scale.
This is a path bound within the carrier, not just an ambient-distance bound.

`Bounds/Scalar.lean` obtains lower scalar bounds by reversing the existing
local upper estimate. `Bounds/Fields.lean` proves the scalar-ratio and volume
fields in the carrier's own supremum-curvature scale, the exact calibrated
core-radius equation, compact ball containment, and strict universal lower
ball volumes. Its derivative fields use
`uniformKappaScalarDerivativeBounds_of_services` and uniqueness of the derivative
within `Iic 0` to retain the actual Laplacian-plus-Ricci expression at zero.
`Bounds/Diameter.lean` converts the intrinsic bound to that same supremum
scale. `Bounds/Common.lean` combines these fields into one constant, with the
smallness threshold chosen before the radius and all constants before the
carrier and solution.

`Construction.lean` composes these constructions with the point-soul theorem
and an explicit `UniformSoulCenteredCoreConclusionOfServices` argument. Its axiom audit
uses only `propext`, `Classical.choice` and `Quot.sound`, as do the individual
region and bound producers.

## Cap And Attachment

`Collars/Recenter.lean` transports the actual cylinder comparison through an
affine change of coordinates and scalar normalization. `Collars/Placement.lean`
uses the intermediate value theorem to place the outgoing neck with its
negative endpoint at the original central sphere. `Collars/Boundary.lean`
proves the closure and frontier identities for buffered source slabs.
`Cap/Boundary.lean` applies them to the calibrated cap and end necks,
including the prescribed negative-end closure and nondegenerate local
defining functions.

`Regions/Euclidean.lean` transports the actual smooth domain and embedded
sphere into the point-soul Euclidean coordinates. `Regions/Ball.lean` applies
`Poincare.Manifold.SmoothDomain.exists_ball_neighborhood`. The resulting
ball parametrization gives the Euclidean cap model in `Regions/Model.lean`;
`Regions/Expansion.lean` uses an ambient smooth slice shift to extend the
model to the buffered cap carrier.

`Bounds/Buffered/Paths.lean` and `Diameter.lean` construct paths inside this
smaller carrier. `Fields.lean` proves every quantitative cap field there,
including calibrated balls at every point of the entire compact-side core.
The new diameter argument is intrinsic; it does not infer diameter
monotonicity under shrinking a carrier. Negative scalar powers transport the
volume estimate to the buffered carrier's own scalar supremum.

`Cap/Certificate.lean` assembles these fields into `CapCertificate` with the
flow connection definitionally. `Cap/Construction.lean` chooses the fine
source accuracy and common cap constant before the manifold and solution.
`End/Attachment.lean` constructs the actual outgoing tube and attachment
using the original cap, proves whole-slice coverage, and uses closed-core
avoidance to prove strong coverage at every tube point. The final conversion
in `Noncompact/Cap.lean` preserves the actual cap connection.

`Producer.lean` proves the exact reviewed universal target with no direct
admission. All Lean files under `Positive/` have no `sorry`, `admit`, new axiom
or unsafe proof. The read-only Core producer was subsequently completed at
workspace commit `3db8777b4e9df8afc150ed01ec362372ba95a3ed`, using the published
original-flow trichotomy; its audit now uses only standard axioms. The sole
remaining inherited admission is the smooth sphere-ball neighborhood theorem,
owned by the active `smooth-sphere-ball-neighborhoods` mission. It contributes
`sorryAx` to the cap model, cap certificate and public endpoint. No proof of
that filling theorem is claimed here.

## Verification

The analytic construction now takes `NoncompactKappaServices`, consisting of
the six scalar-derivative services and two-dimensional classification.
The Core producer uses the existing small-carrier compactness estimate and
the shared original-flow classification. Every original M26-parameter
declaration is retained with its original signature as an adapter.

`exists_coveredCappedTube_of_cap_threshold` exposes the actual static cap
identity and closed-core disjointness. Strongification retains both cores;
`positiveCurvatureStrongCappedTubes_of_services` keeps core-or-strong-neck
coverage on that same cap and with the same epsilon. The exact M27 adapter
applies `m27CappedEuclidean_of_covered_attachment` to the constructed
attachment. The candidate declarations and independent alignment are in
`notes/ricci-flow/positive-capped-tubes-services.md`.

The named `Positive.Check` target audits the exact public endpoint and each
geometric stage. Collar placement, boundary identities, buffered estimates
and outgoing attachment report only the three standard axioms. The ball
model, cap assembly and endpoint additionally report inherited `sorryAx`.
It also traverses the strengthened and exact M27 endpoint dependencies,
rejecting any direct admission except the tracked smooth-ball filling.
The final source is checked with the managed build and `make check` before
publication; the graph revision records the immutable source and evidence.

## References

Morgan--Tian, *Ricci Flow and the Poincare Conjecture* (2007),
Proposition 9.85 and Corollary 9.86, pp. 237-239, and the positive-curvature
case of Corollary 9.88, pp. 239-240. The source is archived at
`references/ricci-flow/morgan-tian/authoritative-archive/MT2007/`.
The outgoing-chain argument uses Proposition A.21 and Claims A.23-A.24,
pp. 510-513. The ball model uses Hatcher, *Notes on Basic 3-Manifold
Topology* (2014), Section 1.1, Theorem 1.1, printed pp. 1-5, through the
existing `smooth-sphere-ball-neighborhoods` dependency.

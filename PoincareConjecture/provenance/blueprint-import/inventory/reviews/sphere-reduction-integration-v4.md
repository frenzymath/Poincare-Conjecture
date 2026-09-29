# Sphere reduction: integration review

Reviewer: `session_fd894b3e2eb047718aa35f162d35c568`, 28 September 2026.
Production source: `751329327f4f582797bda8e6cffe7cdf7531cc1d`.
Calibration: extinction accepted at `77936e5090144b8475576678b32f2e215c009544`.
The author session has finished; the integration owner made the corrections
below. The exact reviewed draft digest is in `sphere-reduction-v4.json`.

## Findings and disposition

1. **Precise upstream topology statements were unlinked. Resolved locally.**
   The reciprocal end uses a chart whose image includes the entire oriented
   half-collar, a radial formula after every allowed width, and connectedness
   of both sides. A bare statement of smooth Schoenflies does not supply
   these clauses. The draft now links `lem:neck-cap-prescribed-collar` and
   `lem:neck-cap-sphere-isotopy`. The neck-cap draft now explains the positive
   normal derivative, time-space interpolation, compact velocity extension,
   preservation of the filled ball and full outer-collar gluing. The sphere
   reduction still states exactly the weaker monotone radial data it consumes;
   it recovers radial smoothness rather than assuming it.
2. **The neck-cap isotopy endpoint conventions differed from the source.
   Corrected.** `Sphere/Normalization.lean` gives `N_0=A` and `N_1 k=f`;
   `Sphere/CompactPlaneTransfer.lean` gives `J_0=k`, `J_1=id`.
   The formula `I_t=N_t J_(1-t)` is retained with these actual conventions.
   The two reversals in the old prose happened to yield the intended endpoints,
   but did not translate these source constructions. Added the cone derivative,
   supported identity-jet correction and Gram--Schmidt linear path.
3. **Nonemptiness and basepoint transport were too implicit. Corrected.**
   The factor simple-connectedness conclusion now assumes a nonempty connected
   factor, matching `IsConnected univ`. The ball-removal cover is explicitly
   the complement of the closed unit ball and the open radius-two chart.
   A path in that chart moves an interior basepoint to radius three halves.
   No connectedness of an entire intermediate side is imposed.
4. **Finite-history and same-flow interfaces. Passed.** The factor family is
   the bijective enumeration of actual event/non-survivor pairs. The accepted
   reconstruction theorem is now directly referenced. Recognition constructs
   maps for those exact pieces, and the endpoint composes a reduction of that
   exact time-zero carrier with its stored initial identification.

## Source review

The following paths are relative to `PoincareLib/Topology/Manifold/` unless
otherwise stated. These are proof mechanisms inspected, not a count-based
coverage certificate.

| Exposition | Inspected source and mathematical check |
| --- | --- |
| `lem:sphere-factor-retraction` | `Surgery/GroupEffects/ConnectedSum/{RemoveBall,Factors,Reconstruction}.lean`; arbitrary-basepoint retractions and ball-filling isomorphism, clopen initial groups and composition. Also read `PoincareLib/AlgebraicTopology/FundamentalGroup/VanKampen/General.lean`: adapted overlap paths and the conjugation correction yield an actual left inverse at every basepoint. |
| `thm:exact-sphere-factors` | `Surgery/SphereFactors/Assembly/{PieceSimplyConnected,SphereBundleExclusion}.lean`, `SphereFactors/SimplyConnected/KillingHopf.lean` and `SphereFactors/Main.lean`: local openness of the projection gives openness of the lifted compact range; constant positive curvature is normalized by multiplying the metric by its curvature constant; the covering becomes a diffeomorphism under target simple connectedness. |
| `lem:reciprocal-sphere-end` | `Surgery/Reduction/Assembly/{CanonicalPuncturedSphereEnd,SchoenfliesGlobalChart,SchoenfliesBallSide,SchoenfliesExteriorBall,SchoenfliesRadialCoordinate,SchoenfliesRadiusInverse,SchoenfliesCanonicalRadius}.lean`; the shift reaches the original boundary at minus one half, boundedness forces the sign, connected-side partitions prove the exact smaller-ball image, and inverse-chart norms recover radial regularity. |
| Radial splice | `Surgery/Reduction/Algebra/{ReciprocalRadiusExtension,PositiveRadiusSplice}.lean`: the linear slope is `h(a)/(2R)`, every term in the derivative estimate has the required sign, the linear germ resolves the origin, and the reciprocal divergence gives the full positive radial image. |
| `thm:binary-sphere-identity` | `Surgery/Reduction/Assembly/{CollarAbsorptionActualAssembly,CollarAbsorptionAssemblyMaps,CollarAbsorptionSphereCharts,CollarAbsorptionAssembly,SphereConnectedSum}.lean`: the inverse angular gluing is exact at radius at least two, cap radii separate the inverse cases, one smooth collar formula crosses radius two, and the two charts have the same radius-two inversion as standard stereographic charts. |
| `lem:sphere-union-step` | `Surgery/Reduction/Assembly/{ComponentBookkeeping,ComponentTargetRegion,StepPreservesSphereUnion,FiniteComponentFamily,FiniteInduction}.lean`: distinct selected indices, full ball-chart containment, clopen selected target, unchanged untouched components, disjoint finite cover and final connected extraction. |
| `thm:sphere-smooth-endpoint` | `Poincare/Smooth/Providers.lean` and `Poincare/Smooth.lean`: the provider retains the same global certificate definitionally, and the conditional endpoint is the composition of two actual diffeomorphisms. |

For the topology input correction, read
`NeckCap/SourceServices/Space/{SchoenfliesFromBall,BallCollarMatching,OrientedCollarCorrection,SphereCollarCorrection,SphereInterpolation}.lean`,
`NeckCap/SourceServices/Gluing/SchoenfliesService.lean`,
`NeckCap/SourceServices/Sphere/{Normalization,GermCorrection,OrthogonalPath,CompactPlaneTransfer,Reduction,Service}.lean`
and `Diffeomorph/EssentialSphere/Euclidean.lean`. The compact planar assembly
was traced through `NeckCap/SourceServices/Plane/Isotopy/CompactIsotopy.lean`.
Its moving-axis construction still needs the full neck-cap review; reading
that assembly does not discharge its substantial prerequisites.

## Readability and source comparison

Read the whole chapter continuously, separately from source lookup, and
reread the corrected statements and affected proofs. Definitions precede
recognition, the arbitrary gluing is retained, and the binary identity is
proved by formulas rather than asserted from diffeomorphism types. The
component proof does not assume connected intermediate carriers or a unique
prime decomposition. Empty finite families are allowed, and nonemptiness is
used at final extraction.

Directly inspected Morgan--Tian, *Ricci Flow and the Poincare Conjecture*,
Proposition 15.3 and Corollary 15.4, printed pp. 357--359 (local Clay PDF
pages 400--402). Corollary 15.4 treats its simply connected conclusion as
immediate after finite reconstruction. This chapter develops the formal
implementation's particular group, lifted-bundle and actual-collar arguments;
the citation alone is not their proof. The author also records the precise
standard covering and positive-spaceform locators. No novelty is inferred.

## Decision and limits

Accept the sphere-reduction chapter with its explicit predecessor results,
on the same basis as the extinction and finite-history chapter decisions.
This does not accept the entire neck-cap or filling-width chapters. The
compact planar moving-axis argument and ambient ball-filling branch remain
in the neck-cap source/readability queue. Changes to those input statements
reopen this decision. Rendering, actual-text source inventory and whole-book
mathematical coverage remain pending. No Lean build, axiom audit or comparator
was run; the unchanged production evidence is reused as directed.

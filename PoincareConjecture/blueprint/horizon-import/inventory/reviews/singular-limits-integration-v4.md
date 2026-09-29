# Singular Limits Integration Review

Status: accepted for chapter mathematics at corrected digest
`2c2986d59e8134e0b12be674a570f22b0b74527868d1cd9c6310f8e73f9d5ece`.
Main read the complete recovered draft at author digest
`baf2c53f6db63492eff353eb3ee54f95100e1197f5aa5b0ea83d24905672fa65`,
published in `9b43c56d8295bfa56c0f3daa64c8d14ea0d35ec2`, and its finite
independent source review. Production source pin:
`751329327f4f582797bda8e6cffe7cdf7531cc1d`.

## Main Corrections

- The finite-left-endpoint Harnack estimate uses the scalar bound on the
  included time-zero slice. Calling it a bound at the endpoint being
  constructed made the argument appear circular. The draft now separates
  compact-local endpoint construction from the later global bound.
- The compact separator in the horn limit is a closed ball. Read
  `Surgery/Singular/DeepHorn/Construction/LimitGeometry/Topology/LimitLine.lean`
  in full. The draft now proves separation by capturing an alleged avoiding
  path and compact endpoint neighborhoods, then transferring them through
  inverse confinement to contradict the original central sphere's
  separation. Joining unbounded components did not construct this separator.
- The attachment domain is relatively compact and open, with closure in
  a larger open domain; it is not a compact open set.
- The projective-plane product alternative is excluded by orientability
  of the retained open horn slab. Simple connectedness alone would not
  justify an arbitrary embedded subregion's fundamental group.
- The full-neck scalar estimate now points to
  `eq:neck-cap-full-scalar`. The positive-curvature neck-scale input points
  to the actual universal point-soul/nested-side/flux proof following
  `lem:ancient-terminal-cylinder` in the accepted ancient-models chapter;
  that argument is independent of a soliton equation.

## Completed Finite Source Checks

All paths below are relative to `PoincareLib/Geometry/RicciFlow/`; the
listed files were read in full.

- `Generalized/BoundedDistance/Tube/SourceGeometry/CriticalBall/`:
  `SourceCriticalBallInitialCapture`, `SourceCriticalBallPositiveEnd`,
  `SourceCriticalBallRecut`, and `SourceCriticalBallLimitVolume`;
  `Spacetime/NeckGeometry/{NeckCoverCompactness,NeckCoverEnd}` within the
  same bounded-distance tree. The finite-volume packing proof now explains
  compact containment of bounded-scalar centers without completeness and
  uniform divergence on the proper positive tail.
- `Generalized/BoundedDistance/Angles/Limits/SelectedEndRayChordLimits.lean`
  and `Cone/SourceGeometry/Coordinates/SourceChartConeObstruction.lean`
  within that tree: joint chord limit, unchanged intrinsic metric,
  closed a/64 and open a/128 domains, strict cone radial margins.
- `Surgery/Singular/RegularLimit/Canonical/Cap/Assembly/`:
  `SameCoreBounds` and `SameCorePersistence`;
  `Canonical/Neck/Static/{Recenter,FullDomainComparison}` and
  `Canonical/Cap/Core/Affine/TranslatedNormalization` within the same
  regular-limit tree. Main separated upper total cap volume from lower
  core-ball volume and added the actual scalar-ratio error calculation:
  translation preserves derivatives, scaling costs
  `2 c^2 bound + 6 (c-1)^2`, giving `(32+6 S^2) epsilon^2`.
- `Blowup/Construction/LongTime/FiniteSlab/RawFiniteScalarBound.lean`,
  `LongTime/BoundedFiniteContinuation.lean`, and
  `LongTime/CofinalExtraction/CofinalFiniteLimitClosure.lean` within
  `Blowup/Construction/`. Main replaced an unsupported identification of
  arbitrary finite limits by the actual uniform strict-prefix Harnack
  coefficients and diagonal extraction from original source cylinders.
- `Surgery/Singular/DeepHorn/Construction/LimitGeometry/Charts/InverseConfinement.lean`,
  `LimitGeometry/Topology/LimitLine.lean`,
  `AncientLimits/Continuation/Stages/StageStep.lean`,
  `AncientLimits/Continuation/Noncollapse/NoncollapseGluing.lean`, and
  `Selection/MonotoneSelection.lean` within the deep-horn construction.
  The actual inverse covers a source r-ball by an enlarged limit Cr-ball.
  The stage time step precedes radii, native attachment times stay in
  [-1/2,0], and same-clock uniqueness preserves pointwise noncollapse on
  the original sequence. The selector uses a least eligible dyadic index.

The accepted Ricci-flow construction supplies the analytic and compactness
inputs, with source cylinders and terminal endpoint work developed here.
The positive-curvature neck-scale proof and `thm:surface-ancient` are actual
accepted ancient-models inputs. The full-neck scalar estimate, local
certificates and confined sphere transport agree with accepted neck-cap
topology. The updated chapter preserves the same extensions and exact
height choices exported to surgery/global surgery.

This bounded source pass and the complete readability pass resolve the
chapter findings. The authoritative decision and digest are in
`singular-limits-v4.json`. Later consumers, milestone/source integration
and complete PDF/site inspection remain pending. No Lean build, audit or
comparator was run by integration; pinned production evidence is reused,
with an empty source-tree diff at this decision.

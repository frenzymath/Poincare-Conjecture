# Independent review of the extinction inputs

Root coordinator review, 2026-09-28, requested by the active integration
session in message 2434. This is a bounded source and mathematical-readability
review of the global-flow and filling-width interfaces needed by extinction.
Neither chapter is accepted. Extinction calibration failed in the integration
review and remains owned by `blueprint-v4-integration`.

## Pins and verification scope

- Workspace read: `00469eddc0a711a9dcce1b963bedbdb22bfd3488`.
- Original recovered global draft: commit
  `ff2b4d943486a00b38b98069a1cda848a4f93e73`.
- Original recovered filling draft: commit
  `393e6a8c2f0ba934d01cbf75c503391717c786f2`.
- Corrected global draft SHA-256:
  `9aea303f5b854c154750fff5561b51d137957a5912c2e4eaf2e9239693096a8a`.
- Corrected filling draft SHA-256:
  `1f6c8356501ae7c6f0dd1e7d4411f958a815b72d076fd26b68420c7d5e21b891`.
- Library, Roadmap and reference revisions are the current reads recorded
  in `finite-history-independent-v4.md`.
- Read-only Git comparison against
  `751329327f4f582797bda8e6cffe7cdf7531cc1d` found no changes in the reviewed
  extinction-global, ancestry, initial-class-adapter, comparison-calibration
  and local-topology-statement sources. Reused production verification is
  `references/ricci-flow/mapher/production-cleanup/verification.json`.
  No new Lean build or recursive audit was run for this review.

## Findings and corrections

1. **The common initial class was missing from the exposition.**
   The original filling interface promised a fixed label but did not construct
   it or prove the same initial width for all targets. The new
   `sec:filling-fixed-initial-class` supplies the literal initial component,
   finite target cover, pulled-back metric, selected-point transport of the
   integer generator, inverse loop-space identification, and the common
   equality `eq:filling-fixed-initial-width`. The choices precede every
   target-time quantifier.
2. **The strict flow calibration was missing.** The new
   `sec:global-comparison-calibration` chooses the minimum of all three
   thresholds before the schedule, then the explicit ceiling-indexed
   halved control before the flow. It proves positivity, monotonicity,
   epoch compatibility, and both strict surgery bounds. The actual accuracy
   loss is `10^14`, not `2`.
3. **False path assertion.** Corrected "basepoints on different components"
   to basepoints in the same connected smooth component. The path transporting
   the initial generator is inside the fixed initial carrier.
4. **Incorrect group-map quantifiers and kernel description.**
   `ConnectedSum/Reconstruction.lean` proves, for each piece point, existence
   of a parent point. The draft had quantified universally over both points,
   which is invalid for disconnected parents. The retained kernel is the
   factor map's kernel; no equality with the other summand subgroup is
   supplied. Corrected both claims.
5. **Epoch boundary direction.** `surgeryEpochEntry` is left-closed and
   right-open. Corrected the draft to use the new value at the boundary.
   Also repaired missing spacing-command backslashes and five equations
   whose tags referenced nonexistent labels. They now carry actual labels.
6. **Historical admission claim.** Removed the unsupported present-tense
   assertion that the epoch extension inherits an M13 admission. The actual
   endpoint supplies `generalizedParabolicRescaling_from_M12 3` in its
   predecessor record; the preserved production endpoint audit lists only
   the three standard axioms. Conditional theorem parameters and unresolved
   exposition review are not themselves mathematical admissions. The old
   author JSON still records this historical claim and must be superseded
   during shared metadata integration.

## Source reconstruction

The following proof bodies and definitions were read. Paths are relative
to `PoincareLib/`.

| Link | Evidence and mathematical mechanism |
| --- | --- |
| Actual final route | `Topology/Manifold/Poincare/Final/Providers.lean`, `m90SmoothEndpointInputs`: constructs all named theories and invokes `m71ExtinctionFromCalibratedTheories`, retaining its one flow, raw topology and extinction. It does not use `m72GlobalFlowWithRawTopology` to select a second flow. |
| Accuracy thresholds | `Geometry/RicciFlow/Extinction/Global/ComparisonProviders.lean`: minimum of the M38/M39/M40 thresholds; global bound `2 * minimum / terminalAccuracyFactor`; the local comparison homotopy is selected for the actual comparison map. `Surgery/Singular/Geometry.lean` defines the factor as `100000000000000`. |
| Explicit control | `Geometry/RicciFlow/Surgery/Global/ComparisonCalibration.lean`: `min (Delta (ceilNat (32*t))/2) (min 1 (R0^(-1/2)/2))`. The epoch index is bounded by the ceiling using `n+1 <= 2^n`. Height is bounded by `delta^2*r <= delta`, using `r <= 1` and `delta <= 1`. |
| Same-flow scalar and topology inputs | `Extinction/Global/PoincareInputs.lean` and `Assembly.lean` (under `Geometry/RicciFlow/`): ancestry is constructed on the actual core view of the global flow, scalar lower bounds come from that flow's pinching, and the returned local topology stays on it. |
| Common initial carrier | `Surgery/Ancestry/Finite/FiniteAncestry.lean`, `TraceComponents.lean`, and `Ancestry/Path.lean`: choose the initial component once; connectedness makes its range the whole initial slice. Every trace uses this identical record at zero and selected open component models at positive times. |
| Trace existence | `Ancestry/Finite/FiniteTrace.lean`, `EventTrace.lean`, `EventOverlap.lean`: finite-event induction; inverse ordinary transport for the regular step; a retained-interior point for the event step. The cap's connected local ball model meets a negative half-neck; boundary correspondence upgrades a boundary witness to an interior witness in the same child component. |
| Literal finite target cover | `Ancestry/InitialAnchor.lean`, `m56LiteralPathCover`: compactness first supplies finitely many terminal component ranges. Reselect each model's included basepoint, use its prescribed `path_for`, and prove equality of ranges because both components contain that point. No substitution of an unrelated path is used. |
| Initial topology and metric | `Extinction/Global/InitialClass.lean`: apply closed simply connected topology to the actual initial component, and restrict the actual time-zero metric via `m39ComponentMetric`. The M59 output is the same chosen system used by the width theories. |
| Nonzero class at the chosen point | `Extinction/Width/Path/InitialClassAdapters.lean`, `m67InitialClassFromM02AtSelectedPoint`: take the inverse image of integer one under the supplied third-homotopy isomorphism, transport it along a path from the topology theorem's point to the selected component point, and use inverse-path injectivity to retain nonzero. Transport trivial second homotopy the same way, then apply the inverse loop-space isomorphism. |
| Quantifier order and width identity | `Extinction/Global/Definitions.lean`, `ContinuationInputs.lean`, `InitialWidth.lean`, and `WidthInputs.lean`: the sole initial record precedes `target_cover`; each width application substitutes along `path_for_initial`; `m71WidthChoice_initial_width` has the same right-hand side for every target package. |
| Target chosen later | `Extinction/Global/NegativeTime.lean`: its observation time depends only on the fixed initial width. This review does not review the scalar-profile proof or claim it passes extinction calibration. |
| Reconstruction input | `Topology/Manifold/Poincare/Smooth/Providers.lean` and `Surgery/Reconstruction/Providers.lean`: the same flow, local topology and finite-extinction conclusion feed the finite-history input; chronology is constructed by `LocalTopology.lean`, as reviewed separately. |

The preceding mechanisms establish the two added interface subsections
relative to the explicitly named geometric and topological input theorems.
They do not establish all substantive proofs in the global or filling chapter.

## Source comparison

Read the retained Morgan--Tian Chapter 18 transcription, Claim 18.16,
Definition 18.17, Proposition 18.18 and the subsequent proof of Theorem 18.1,
pp. 430--432. The published proof first reaches a time when second homotopy
vanishes and bounds the finitely many starting components. The present route
specializes to the simply connected initial manifold at time zero, produces
its generator from closed-manifold topology, and fixes one initial width
for all targets. This is a specialization, not a claimed new theorem.
The unrestricted raw competitors in the class infimum agree with the
published distinction between family maximum and class infimum.

## Unresolved Acceptance Gates

- **Surgery threshold mismatch:** `drafts/surgery.tex`,
  `thm:surgery-local-topology`, currently assumes `2*epsilon <= epsilon0`.
  `Topology/Manifold/ConnectedSum/Surgery/LocalTheory.lean` actually assumes
  `terminalAccuracyFactor*epsilon <= epsilon0`. The new global subsection
  satisfies the stronger source hypothesis. Integration must correct the
  local statement and check other uses of that factor before acceptance.
- **Ancestry coverage:** the filling author's JSON assigns M56/M57 to
  surgery/finite-history, but finite-history reconstructs assemblies rather
  than proving ancestry transport. The new fixed-initial subsection covers
  the anchor and finite-cover mechanism. Integration must map M56 there
  and to the full event-trace account, and map M57 to the actual degree-one,
  homology, basepoint-path and nonzero-class transport proofs. This review
  does not certify that all of M57 is already adequately exposed.
- **Filling readability:** much of the original draft still prints
  `pi_2`, `C subset M_t`, arrows and whole formulas as ordinary text.
  Its quotient description also conflates a quotient space with the
  quotient map. These require mathematical notation and definition review.
- **Substantial proof depth:** full M59 cubical/free-class naturality,
  M60 filling continuity and minimal-sphere arguments, and global
  action-minimizer, canonical induction, volume/component counting and
  global-union constructions still need source/readability review. The
  phrase "compactly supported homology" in the free-class discussion
  needs reconciliation with the ordinary top-homology argument.
- **Calibration and rendering:** integration owns correction and review
  of extinction, incorporation of these inputs, the shared milestone and
  metadata records, and final PDF/site inspection. Local source/structure
  checks are not a TeX build or a completed mathematical review.

The added subsections were read continuously as mathematical arguments;
their bounded interface findings are resolved. Both complete chapters and
the book remain pending acceptance by the integration owner.
Static checks found balanced TeX environments, unique labels, and resolved
local `ref`/`eqref` targets in both corrected drafts; `git diff --check`
passed. These checks do not substitute for final PDF/site rendering.

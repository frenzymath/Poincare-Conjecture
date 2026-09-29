# Independent finite-history review

Reviewed 2026-09-28 by the root coordinator, independently of the chapter
author. This is a source and continuous-readability review of the finite
reconstruction argument. It does not accept the other chapters or discharge
the extinction calibration gate.

## Result and pins

The reverse-history argument passes this source review after the corrections
below, relative to the explicitly stated global-flow, empty-event and local
topology inputs. A separate continuous mathematical read found the corrected
argument understandable without Lean: it defines the event and factor sets,
constructs their chronology, describes every geometric operation used in
substitution, and proves the induction invariant. Final chapter acceptance
remains pending the calibration and cross-chapter checks listed below.

- Workspace inspected: `d83f7a020403603978084150c8458e6484e4cb81`.
- Reviewed draft SHA-256 after corrections:
  `0f3e4a306362786f6becc6c6d33f9017ae2e0b13c0f0992caef29de0e24f586b`.
- Current Roadmap read: `2912db8dd8d7db573079cd02f251b1276fda72db`, including
  `finite-surgery-history-reconstruction` and
  `m82-event-indexed-sphere-factor-ledger`.
- Current Library read: `806006e5715414b4ceb6897d00ea279e8722042e`.
  Its README/tree were inspected; the reconstruction source reviewed here
  is workspace source, not a claim about the Library snapshot.
- Reference mirror read: `5a9e2acd61c33320a2e6232e502d2189385f5157`,
  `CONTRIBUTING.md`, for authoring/metadata conventions only.
- Read-only Git comparison confirms the reviewed `ConnectedSum` and
  `Surgery/Reconstruction` source directories are unchanged from the
  published verification commit `751329327`. No new Lean verification is
  claimed. The redundant local builds started before reading operator
  direction 2418 were stopped; contract checks passed, but the builds had
  cache/permission errors and did not provide successful new verification.

## Corrections made

1. **Missing construction of chronology.** The opening previously treated
   predecessor and reference times as supplied data. Following
   `Reconstruction/LocalTopology.lean` exposes their producer: take the maximum
   of zero and all earlier surgery times, then the midpoint between the
   maximum of that predecessor and the event's stored lower time and the event
   time. The new `lem:finite-event-references` proves both surgery-free
   intervals, constructs the actual regular map, and transports the raw local
   conclusion in both nonempty and vanishing branches. This is a substantive
   dependency discovered beyond the author's declaration list.
2. **Implicit target transport.** The new `lem:finite-assembly-transport`
   treats a zero-operation assembly by transporting its initial partition;
   otherwise it postcomposes the last operation's region maps and collar.
   It does not introduce an extra connected-sum step for a diffeomorphism.
3. **Disconnected intermediate slices.** Replaced the claim that the later
   whole-slice assembly is inserted "as one component" by the precise
   disjoint-summand statement. The two sides of an operation may be
   disconnected, as required by the operation-lifting construction.
4. **Mathematical narrative.** Removed input-package/service narration and
   publication-review instructions from the chapter. Added explicit
   nonemptiness of local pieces, zero not being a surgery time, and the
   global nonnegative time domain. Simple connectedness is explicitly
   postponed to factor recognition.

## Source review

All paths below are relative to `PoincareLib/Topology/Manifold/`. They were
read as source, including proof bodies, rather than inferred from imports.

| Exposition | Source and mathematical check |
| --- | --- |
| Opening and event data | `ConnectedSum/Reconstruction.lean`: `M72EventTopologyData` and `M72LocalTopologyService` retain the actual M38 conclusion under the preterminal map, both reference inequalities, cap correspondence, empty-event rule and exact regular predecessor map. |
| Compatible references | `Surgery/Reconstruction/LocalTopology.lean`: `m72Predecessor`, `m72Reference`, the nonempty and vanishing constructors, and `m72LocalTopologyFromRaw`. The maximum is strictly below the event; the midpoint is strictly above both required lower times. |
| Assembly definition | `ConnectedSum/Basic.lean`: the punctured radius-one balls have radius-two coordinate neighborhoods; the negative/positive collar radii are respectively `1-s` and `1+s`. The central sphere is disjoint from both open regions. |
| Target transport | `ConnectedSum/Transport.lean`: `SmoothFiniteConnectedSumAssembly.nonempty_transportTarget` changes the initial union in the reflexive case and the last genuine operation otherwise. |
| Immediate successor | `Surgery/Reconstruction/Assembly/Successors.lean`: `m72ImmediateSuccessor` is minimal among all later surgery times, including those outside the bounded ledger. Both predecessor contradiction branches and the zero anchor are checked. |
| Survivor components | The same file: `m72SurvivorBeforeExtinction`, `m72DiffeomorphImageConnectedComponent`, and `m72SuccessorChoice`. The terminal empty-slice rule excludes survivors; the same regular map sends each complete component to its image component. |
| Split diffeomorphism | `Assembly/SliceDecomposition.lean` and `Assembly/DisjointUnionIdentification.lean` (under `Surgery/Reconstruction/`): the discarded open union has a zero-operation assembly; the survivor slice plus that union has the same pieces as the local initial carrier. Piecewise inverse maps paste on open regions. The target is the local initial carrier, not the incoming slice. |
| Appending and lifting | `Assembly/DisjointUnionSum.lean` and `Assembly/StepLift.lean`: each listed piece is nonempty, while a family may be empty. The extra manifold is included in the second side and second target region; the second punctured complement is the original punctured complement plus the entire extra summand. All collar identities are unchanged after inclusion. |
| Source composition | `Assembly/SourceTransport.lean`: `nonempty_compOperations` distinguishes a reflexive local chain from a genuine first operation, pulling back that first operation's source partition. |
| Substitution | `Assembly/Substitution.lean`: the family is exactly the later-tail family plus current non-survivors; it uses the split map, lifted chain and local operation chain just reviewed. No arbitrary reclassification of factors occurs. |
| Index invariant | `Assembly/HistoryIndices.lean`: terminal, successor and first-tail equivalences preserve the literal carriers. Successor minimality proves surjectivity of the tail partition and strict order proves disjointness of its two branches. |
| Reverse induction and endpoint | `Assembly/ReverseInduction.lean`, `Assembly/FirstEvent.lean` and `Assembly/Assembly.lean`: the same whole-slice invariant is propagated; the least event has predecessor zero; the chosen initial identification transports connectedness. Survivor witnesses are also retained separately. |

Basic finite-order facts, local smooth pasting and connected-component
maximality are ordinary background used with their hypotheses displayed.
Finite-index encodings and total inverse functions off the relevant regions
are implementation details. Neither classification of discarded pieces nor
existence of collared local surgery reconstructions is treated as bookkeeping.

## Source comparison and M82

Read Morgan--Tian, Proposition 15.3, pp. 357--358, and Corollary 15.4,
pp. 358--359, in the retained transcription
`references/ricci-flow/morgan-tian/transcriptions/chapters/Ch15_ControlledRicciFlows.tex`,
the proposition `surgerytoptype` and corollary `Tgood0good`, including their
proofs. The published argument reverses finitely many surgery times, adjoining
sphere bundles and positive spaceforms and performing connected sums. The
workspace specializes to one extinct flow and constructs the exact factor
indices and smooth operations. No novelty or general geometrization claim
is made for this specialization.

Read `ConnectedSum/PrimeFactorLedger.lean` and
`ConnectedSum/PrimeFactorLedger/Basic.lean` at historical workspace
`e130ac11dab52f2020b596dd4fe0b8e9a44c3fd5`. The M82 constructor literally
uses the M72 index function, pieces and assembly, and the supplied M73 sphere
maps. Its type requires equality of the source-index function but not
equality of its assembly or sphere maps to the supplied witnesses; the
constructor chooses those actual witnesses. The current source has pruned
the adapter. Recommended milestone disposition: historical auxiliary
adapter, unused as a separate current endpoint dependency, with its
mathematical content incorporated at `sec:m82-factor-ledger` and
`eq:m82-ledger`. This is justified by reading its statement and proof,
not merely by absence of its name.

## Remaining integration gates

- `blueprint-v4-integration` must finish extinction calibration before
  accepting this chapter. This independent pass is review evidence, not
  an assertion that calibration has passed.
- Check the earlier global-flow and local-surgery statements supply the
  raw local reconstruction on the same flow, regular identifications,
  local finiteness, nonnegative full time domain and zero-not-surgery.
  The formerly missing reference-time construction is now proved here.
- Connect the actual empty surgery event from extinction, not just an
  arbitrary empty observation time. No continuity across surgery is used.
- Wire the exact indexed factor family to sphere recognition and record
  the M82 disposition in the shared milestone register. The optional ledger
  section states a downstream consequence; the M72 induction does not
  depend on that consequence.
- Validate metadata integration and the final PDF/site. On this host
  `pdflatex`, `bibtex` and `pdftotext` are absent; no visual check is claimed.

The source and readability findings internal to this chapter are resolved
by the accompanying edits. Cross-chapter acceptance and final rendering
remain owned by `blueprint-v4-integration`.

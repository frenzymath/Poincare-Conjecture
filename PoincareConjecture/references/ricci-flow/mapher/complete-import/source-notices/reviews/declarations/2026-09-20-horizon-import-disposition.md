---
document_status: SNAPSHOT
updated: 2026-09-20
status: HISTORICAL_DISPOSITION_SUPERSEDED_BY_RELAND_VALIDATION
scope: HORIZON_IMPORT_METADATA_ONLY
base_commit: d1c6d06a2005a91f18f080e9ce9367e6a759b745
---

# Horizon Import Disposition

The compiled-proof status below is historical. PR 32 re-landed the repaired
eight-entry payload after its full aggregate and axiom checks passed; see
[the current compiled review](2026-09-20-horizon-reland-validation.md).
Its [attribution reconciliation](../../references/2026-09-20-horizon-reland-attribution.md)
preserves the independent semantic and reuse holds below. The original
scope hashes continue to identify the original payload, not the re-landed
files.

## Historical Disposition

PR 19, `f6c284d9e2cf67903b7dcdaf909f8b23370d4906`, delivers the M06,
M16-M20 and M24 proof entries with one shared Horizon library. The
coordinator records those seven proofs as `IN_PROGRESS`, replacing the
importer's `CLOSED` flags pending current aggregate build and axiom evidence.
Their accepted public contracts, prior review rounds, skeleton completions,
dependency records and ownership assignments are unchanged. This disposition
does not grant independent semantic acceptance to any imported helper.

## Evidence Boundaries

The [importer account](2026-09-20-horizon-chain-port.md) and
[library provenance note](../../PoincareMT/Proofs/Horizon/PROVENANCE.md)
preserve the author's donor, reproducibility and donor-side M20 axiom claims
as claims. They are not independent reviews. `SOURCE_COMMIT` in
`tools/port_horizon_chain.py` is an attribution label; the generator does not
authenticate a supplied tree against it. `--check` compares the supplied
tree's rendered output and layout registration. The coordinator has no
matching donor tree for that comparison and has not run it.

The separate [donor evidence audit](../../references/2026-09-20-horizon-reuse-verification.md)
records recovered source and license evidence for 73 identified files.
It does not recover the original Horizon snapshot or complete the reuse
chain. Prominent Horizon-to-PoincareMT modification notices in modified
generated files remain an explicit remediation hold, together with missing
historical attribution links and independent adaptation reviews. No Lean
source notices are edited while the lead validates the fixed source tree.

The project lead reports a leased two-worker full Horizon build at
`5f909b72fbd1c7adc6ea3db95050026e3b652e2b`. Its completed result and the
seven closure checks in `PoincareMT/Audit/HorizonChain.lean` are still
pending here. This task starts no Lean or Lake process. The interrupted
older coordinator build supplies no aggregate success receipt. A later
successful build and foundational-axiom check may support the proof axis;
they cannot replace provenance, independent helper semantics or the actual
declaration/dependency review.

## Layout Disposition

The coordinator adopts the existing catalog of 3,718 Horizon Lean files and
`PoincareMT/Audit/HorizonChain.lean` as shared library files for layout only.
The existing seventeen size exceptions have matching delivered SHA-256
hashes and exact line counts, including one file with exactly 1,000 lines.
They retain those counts and hashes and now cite this disposition.

Keeping the delivered module boundaries makes the imported payload traceable
while donor evidence is recovered. This is an exception for the recorded
bytes only, not approval of arbitrary later generated content. The generator
uses the same review pointer and limited reason as the register; changing a
file or its exception requires a new coordinator disposition. No Lean file,
audit guard, package pin, theorem type or proof body changes in this task.

The [scope record](2026-09-20-horizon-import-disposition-scope.json) pins the
shared payload manifest, all seven entries, the audit file and the seventeen
exception hashes/counts. Its permitted blueprint differences are exactly
the seven proof flags and the exceptions' `reason`/`review` fields. The
shared file list itself is unchanged. M13's proof and review records,
all foreign holds and all completion records are preserved.

## Remaining Work

1. Recover the donor tree and verify the claimed revision, imported-file
   correspondence and author/license notices in the separate source ledger.
   Retained upstream licenses must be matched to the actual reused files;
   the present label or importer account does not complete that ledger.
   Resolve the modification-notice and attribution holds above in a later
   coordinator-owned source change with its own validation scope.
2. Receive the lead's complete build and seven axiom-check receipts with
   exact source scope. Capture actual types, bodies, generated declarations
   and direct dependencies before reconciling the declaration register.
   The existing register has no inventory of the Horizon helper modules;
   it remains unchanged by this metadata task.
3. Independently review the imported helper statements and mathematical
   derivations, then their elaborated semantics. Preserve every earlier
   UNREVIEWED or OUTDATED foreign state until its own review is completed.
4. Resolve the M19/M20 shared-file ownership boundary before independent
   owner edits. M19 imports Horizon `Soliton.TwoDimensional`, which imports
   `Soliton.Flow.Applications.Classification`; that file imports
   `Soliton.ThreeDimensional.Models` and
   `Soliton.ThreeDimensional.Compact.Homothety` and defines both surface and
   three-dimensional helpers. Capture actual declaration dependencies and
   assess a split of the shared module. This is a file/ownership question;
   the import path alone does not establish logical circularity or an M19
   theorem dependency on the final M20 theorem. No dependency edge is
   invented or removed here.
5. Confirm M17's handover from its previous Zhiyuan assignment before
   further owner work. The Horizon delivery does not authorize a silent
   reassignment. The latest Axel M21/M22/M23/M25, Zhiyuan M13/M14/M15/M62
   and Leheng assignments remain unchanged.

## Skeleton Receipts

The milestone table's M22, M47, M60 and M61 contract/review cells now follow
their published receipts: [M22](../../docs/progress/2026-09-20-m22-archive-completion.md),
[M47](../../docs/progress/2026-09-20-m47-publication.md),
[M60](../../docs/progress/2026-09-20-m60-archive-completion.md) and
[M61](../../docs/progress/2026-09-20-m61-archive-completion.md).
This corrects a stale table; it performs no new milestone review.
Cumulative completed skeleton IDs remain **M01-M83, M90 (84)**.
M84-M89 remain retired, and imported-proof acceptance is separate.

## Metadata Validation

Blueprint and layout checks pass after normal regeneration of both views:
90 milestones, 397 candidate edges, 68 source nodes, 6,987 source files,
84 numbered entries and 2,872 owned helpers. Structured comparison against
the base permits exactly seven proof-field changes and 34 exception
`reason`/`review` changes. All 3,718 shared source hashes, seven proof-entry
hashes, the audit hash and seventeen exception hashes/counts are unchanged.

The milestone table changes exactly the twelve specified cells and preserves
all three assignment lines. Generator AST comparison permits only its
docstring, size-review metadata, help and printed messages; rendering and
file-write/delete logic are unchanged. Its help check, sixteen local links
and whitespace checks pass. The production Lean files, declaration register
and dependency pins have no differences from the base. These are metadata
checks only; the compiled, semantic and provenance holds above remain open.

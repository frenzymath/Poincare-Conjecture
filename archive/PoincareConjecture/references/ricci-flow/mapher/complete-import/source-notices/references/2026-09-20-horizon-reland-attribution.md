---
document_status: SNAPSHOT
updated: 2026-09-20
inspection_commit: 1d7baec54a653d72bd1fabd2d4f25aa78e0ec671
reviewer: AGENT /root/original_source_acquisition
scope: POST_MERGE_HEADER_ARCHIVE_AND_IMPORT_TARGET_RECONCILIATION
status: FACTUAL_RECONCILIATION_ONLY_EXISTING_HOLDS_PRESERVED
---

# Horizon Attribution After Re-Landing

PR 32 re-landed the Horizon ports of M06, M16-M21 and M24. This record
reconciles their source notices after deduplication at commit
`1d7baec54a653d72bd1fabd2d4f25aa78e0ec671`. The inspected Horizon tree,
deduplication map and source archives are unchanged from the PR 33 commit
`d306f791d8dea2b741c9dcb4fd84121713292ca8`. No Lean source, proof status,
license decision or historical source manifest is changed by this record.

The [measured inventory](2026-09-20-horizon-reland-attribution.json) records
every mapped current path and hash, its historical inspection hash, actual
implementation imports, implementation hashes and literal notice evidence.
It also records exact archive checks. Import relationships and byte equality
are evidence of file disposition, not acceptance of adapted mathematics.

## Historical And Current Counts

The original [donor audit](2026-09-20-horizon-reuse-verification.md) inspected
commit `ce01e7bd61ec451ebd7dadda8709d0c5993cd697`.

| Notice or source family | Original inspection | Current Horizon |
| --- | ---: | ---: |
| `All rights reserved` | 11 | 7 |
| DifferentialGeometry contributor notices | 61 | 35 |
| ClassificationOfSurfaces contributor notices | 8 | 8 |

The original eleven rights-reserved notices comprise seven Classification
files, three Archon Horizon files with AxelWorkspace references, and one
A Tucker/Mathlib file. Each also includes an Apache release or adaptation
notice. The additional Classification file, `Topology/Plane/Meshes/PolygonalDomains.lean`,
does not contain the rights-reserved phrase. Thus the historical bounded
scope is 73 files, not 72. The copyright phrase alone is neither a complete
license statement nor grounds for inferring permission or a prohibition.

The seven current rights-reserved paths, relative to
`PoincareMT/Proofs/Horizon/`, are:

- `Topology/Plane/Jordan/Arcs.lean`
- `Topology/Plane/Jordan/Basic.lean`
- `Topology/Plane/Jordan/Brouwer.lean`
- `Topology/Plane/Jordan/Counting.lean`
- `Topology/Plane/Meshes/Basic.lean`
- `Topology/Plane/Meshes/Subdivision/Fine.lean`
- `Topology/Plane/Meshes/Subdivision/Lines.lean`

The full current tree contains 3,721 Lean files. Literal searches also find
`AxelWorkspace` in 111 files and `Apache-2.0` in 155 files. Those overlapping
keyword counts are not additional completed source audits or a license for
the entire tree.

## File Disposition

All 73 historical mapped paths still exist:

- 43 have exactly the original inspected bytes: 35 DifferentialGeometry
  files and all eight Classification files.
- 30 now contain imports and comments only: 26 DifferentialGeometry files,
  three AxelWorkspace-attributed files and the Mathlib-attributed file.
  Their actual imports identify 33 existing implementation files, 24 under
  `Proofs/M05` and nine under `Proofs/M07`. The count includes the extra
  implementation modules created by earlier file splits. These implementation
  files retain their source notices.

The three outputs in the [ODE supplement](2026-09-20-horizon-ode-verification.md)
are separate from that 73-file scope and are also import-only bridges:

| Horizon path suffix | Existing implementation |
| --- | --- |
| `Analysis/ODE/Jacobi/Basic.lean` | `PoincareMT/Proofs/M07/Analysis/ODE/Jacobi/Basic.lean` |
| `Analysis/ODE/Linear.lean` | `PoincareMT/Proofs/M05/Analysis/ODE/Linear.lean` |
| `Geometry/Riemannian/Connection/AlongCurve/Manifold.lean` | `PoincareMT/Proofs/M07/Geometry/Riemannian/Connection/AlongCurve/Manifold.lean` |

The [deduplication map](../docs/progress/2026-09-20-horizon-duplicate-modules.json)
provides the wider module comparison. This record verifies only the bounded
notice and ODE mappings, not all mathematical deduplication decisions.
Earlier source-only reviews remain available for the
[eight-file scope](../reviews/declarations/2026-09-20-horizon-bounded-source-review.md),
[two ODE files](../reviews/declarations/2026-09-20-horizon-ode-source-review.md)
and [parallel transport](../reviews/declarations/2026-09-20-horizon-manifold-transport-source-review.md).
Their recorded hashes and limitations remain historical evidence; none is
automatically promoted to review of the current elaborated declarations.

## Archive And Provenance Position

Every one of the 82 file records in canonical source entry
`HorizonProofSources20260920` and all six in `HorizonODEProofSources20260920`
matches its recorded byte count and SHA-256. This includes all 79 originally
archived source/license/NOTICE files and the three supplemental donor sources.
The historical reuse manifests are preserved exactly:

- `supporting/HorizonProofSources/reuse-manifest.json`:
  `6f88a6fa533b04adf4096ca254e8bbbc006d7e22e5ac434d27ec6eaa86db01f9`.
- `supporting/HorizonProofSources/ode-reuse-manifest.json`:
  `8c641bc82b6797e10f266be8b3d72d95c7a0ff0b5adcd4f28ca5b58204fb0199`.

The retained donor license and NOTICE evidence remains source-specific.
Classification's revision is a verified comparison, not a recovered
historical Horizon donor pin. The same historical-pin distinction remains
for the Mathlib adaptation and the Linear ODE comparison.

The current [PROVENANCE.md](../PoincareMT/Proofs/Horizon/PROVENANCE.md) is the
original seven-port importer account. It omits M21 and the later implementation
bridges. Its claimed input commit
`a1096626d6e26fc0b5c134fe20899e46600575fb` is still unavailable as a Git object
in this repository. This check performs no new remote acquisition and makes
no claim about availability elsewhere. The importer narrative supplies
neither authenticated input/output reproduction nor a project-wide license.
It is preserved rather than relabeled as verified provenance.

These historical header targets remain absent:

- `references/topology/classification-of-surfaces/README.md`
- `references/ricci-flow/chow-liao-qin-2026/LICENSE.Apache-2.0.txt`
- `references/ricci-flow/chow-liao-qin-2026/interior-hessian-reuse.md`
- `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`

The canonical archives provide the separately verified donor evidence; they
do not reconstruct missing historical review documents. Source links and
prominent modification notices still need reconciliation where applicable.
Original copyright, license and NOTICE material must remain attached to
its source when files move or become shared implementations.

No declaration status, mathematical review hold, source-provenance hold or
public-distribution decision changes here. The project-wide license remains
unselected. A successful build and this file inventory do not settle the
remaining independent adaptation or semantic reviews.

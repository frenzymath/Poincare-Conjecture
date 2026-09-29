# Source modifications and attribution

This file records source-level reuse where a Lean file is adapted from an
external development. It complements each file's local notice. A source
reference is evidence for review, not an automatic copyright decision: before
adding an attribution, verify the cited revision, license, authorship, and the
substantive changes.

## DeGiorgi Sobolev approximation

- **Local file:** `PoincareLib/Analysis/Elliptic/Regularity/Sobolev/Weak/Approximation.lean`
- **Source:** `DifferentialGeometry/External/DeGiorgi/SobolevSpace/Approximation.lean`
- **Repository/revision:** `qinz1yang/differential-geometry`, v0.1.2,
  commit `1b535dd102b94cc42b107cca27059687888f08b3`
- **Upstream provenance:** the file derives from Julia Kempe and Scott
  Armstrong's DeGiorgi project. Preserve the upstream notice:
  `Copyright 2026 Scott Armstrong and Julia Kempe`.
- **Changes here:** import paths were moved into `PoincareLib`, the namespace
  was moved from `DeGiorgi` to `Poincare.Analysis.Sobolev.Weak`, and the local
  style-warning cleanup was retained. The theorem bodies otherwise match the
  cited source at the token level.
- **License:** Apache-2.0, subject to the source project's license and notice.

## Whole-tree audit, 2026-09-29

The [audit](provenance/2026-09-29/README.md) compared **23,564 active Lean files**
against **18,888 files** from pinned revisions of DifferentialGeometry, DeGiorgi,
TauCeti, ClassificationOfSurfaces, and Mathlib. It searched code without requiring
existing citations or matching filenames. The 80% token-coverage rule, including
local fragments, yielded **455 candidate pairs in 109 local files**.

All candidates have recorded review dispositions in the
[file-by-file ledger](provenance/2026-09-29/reviewed-files.json).
One additional explicitly attributed adaptation, `Topology/Plane/Meshes/PolygonalDomains.lean`,
was reviewed despite falling below the detector threshold. The ledger records
source paths, comparison commits, source hashes, notices, modifications, and
the disposition of every candidate. Comparison commits identify inspected
snapshots; they do not establish the date or exact revision of initial copying.

Missing copyright notices were added to **36 files**. Existing notices were
preserved, and all 110 reviewed files have local provenance and modification
notices. Nine files retain Scott Armstrong and Julia Kempe's DeGiorgi notice,
including substantial fragments incorporated through DifferentialGeometry.
The two partial Mathlib adaptations retain Yizheng Zhu's and Sebastien Gouezel's
respective source notices. TauCeti files retain their individual notices, which
distinguish Lean FRO, LLC from The Tau Ceti contributors.

The DeGiorgi match in `Sobolev/Iterated/Basic.lean` consists of scattered common
weak-derivative proof idioms (longest continuous match: 38 tokens); it did not
justify an additional DeGiorgi attribution. Its substantial DifferentialGeometry
adaptation is separately recorded. Related matches and duplicate upstream trees
are recorded without treating each as a distinct author.

This audit changes Lean comments only. It does not change declarations, imports,
proofs, or mathematical attribution based merely on similarity. Retained source
licenses and the DifferentialGeometry NOTICE are under
[`provenance/2026-09-29/licenses/`](provenance/2026-09-29/licenses/).

## Detection workflow

Use [`scripts/scan_external_reuse.py`](../scripts/scan_external_reuse.py) and the
[reproduction instructions](provenance/2026-09-29/README.md). This replaces the
earlier citation-only workflow in `scripts/detect_provenance.py` for whole-tree
audits. The old helper cannot discover uncited reuse.

The scanner proposes candidates; source inspection determines which notices
to retain. It is a textual heuristic, not a semantic proof comparator, and its
threshold and sampled prefilter can miss short or heavily rewritten adaptations.

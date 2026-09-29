---
document_status: SNAPSHOT
updated: 2026-09-20
reviewer: AGENT /root/original_source_acquisition
scope: HORIZON_THIRD_PARTY_NOTICE_AND_SOURCE_PROVENANCE
status: DONOR_EVIDENCE_VERIFIED_REUSE_CHAIN_REVIEW_PENDING
---

# Horizon Donor Evidence

This record audits the source at commit
`ce01e7bd61ec451ebd7dadda8709d0c5993cd697`, inspected in the isolated publication
checkout. It does not accept any mathematical declaration, change a milestone
status, select a license for original project material, or authorize public
redistribution. Existing proof and provenance holds remain open.

The reported count of 72 notice-bearing files is reproducible, but their
attribution needs correction. All 11 files containing `All rights reserved`
also contain an Apache-2.0 release or adaptation notice. Seven of those files
are attributed to ClassificationOfSurfaces, three to Archon Horizon with
AxelWorkspace source references, and one to A Tucker/Mathlib. There are 61
additional DifferentialGeometry-noticed files. A further file,
`Topology/Plane/Meshes/PolygonalDomains.lean`, records adaptation from
ClassificationOfSurfaces without the rights-reserved phrase. The complete
bounded scope therefore contains 73 files.

The copyright phrase alone neither proves a prohibition on reuse nor supplies
permission. This audit checks actual donor source and license evidence; it
does not infer a license from a project name.

| Family | Local files | Donor evidence | Remaining limitation |
| --- | ---: | --- | --- |
| DifferentialGeometry | 61 | Exact header revision, 61 available donor files, Apache license and NOTICE | Full adaptations and semantics remain unreviewed |
| ClassificationOfSurfaces | 8 | Eight source comparison files and Apache license at a verified public revision | Historical Horizon donor pin is unknown |
| AxelWorkspace | 3 | Four exact donor files and Apache license in retained local Git | Full adaptations and semantics remain unreviewed |
| Mathlib | 1 | Named source declaration and license at the pinned dependency | Historical adaptation pin is not recorded |

The machine-readable [reuse manifest](supporting/HorizonProofSources/reuse-manifest.json)
lists every local path and SHA-256, source path and SHA-256, revision, license
evidence, embedded original-hash check and review limitation. The donor source
files are reference evidence only. They are not Lean build inputs or an
external package dependency.

## Verified Donors

The DifferentialGeometry headers name revision
`1b535dd102b94cc42b107cca27059687888f08b3`. The
[official repository](https://github.com/qinz1yang/differential-geometry/tree/1b535dd102b94cc42b107cca27059687888f08b3)
serves that exact revision and all 61 cited source files. All 26 embedded
original-file SHA-256 claims match: 23 ODE files and three index-form files.
The other 35 files name a revision and source path but supply no original
hash; their actual donor hashes are now recorded. This establishes source
identity evidence, not equivalence of the adapted proof bodies.

Its preserved `LICENSE` is 11,357 bytes, SHA-256
`c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4`.
Its preserved `NOTICE` is 74 bytes, SHA-256
`0daec4551bae719f24ed46a4abb73df4d01b26b3e74de06b12bb828efb859ee3`.
Both are available under the exact donor revision, not inferred from the
current default branch or another project's license.

For ClassificationOfSurfaces, the
[verified comparison revision](https://github.com/mccorvie/classification-of-surfaces/tree/e3c7230fe78d7b056a415d9ecae6f77887046b32)
is `e3c7230fe78d7b056a415d9ecae6f77887046b32`. Its complete tree has no `NOTICE`
file. The Apache license is 11,357 bytes, SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`.
This revision is not asserted to be the original historical donor pin.

The source correspondence is concrete. Excluding imports and blank lines,
`Arcs`, `Counting` and `FineSubdivision` differ only in namespace scaffolding.
`LineSubdivision` additionally changes a Lean option; `Brouwer` changes the
namespace, one open qualifier and documentation. `JordanCurve/Main` has
additional documentation and qualified-name changes. `PlaneComplex` has
substantive local adaptations and omissions. `PolygonalDomains` explicitly
cites `PolygonalPolyhedron` as the argument it extends and is substantially
rewritten; a full adaptation review remains necessary. None of these
comparisons establishes mathematical acceptance.

The AxelWorkspace donor is the existing read-only repository at revision
`f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e`, whose recorded origin is
`AxelDlv00/workspace-poincare-conjecture`. Its four cited originals are
`ChartVariation.lean`, `SecondVariationPrep.lean`, `ChartPartitionSlack.lean`
and `ChartPartitionCorner.lean` in
`formalized-sources/riemannian/MorganTian/MorganTianLib/Geometry/`.
All four embedded hashes match the retained Git bytes. Its root Apache
license is 11,358 bytes, SHA-256
`cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`.
The pinned tree contains no `NOTICE` file. This recovery uses local Git
objects; it does not claim a newly verified network download of that snapshot.

The Mathlib adaptation names
`Mathlib.Analysis.Calculus.FDeriv.Partial.isLittleO_sub_sub_fderiv`.
The source and Apache license are preserved from the actual pinned dependency
`0df444a360eaa60ab8c11dca51a86af692955474`. The license has the same bytes and
hash as the surface-project license above. The source file retains A Tucker's
copyright. This is a verified dependency comparison revision, not a claim
that the historical adapter recorded its original revision.

## Unresolved Provenance

The generator names Horizon snapshot
`a1096626d6e26fc0b5c134fe20899e46600575fb`, but that object and its input tree
were not recovered in the inspected repository or the known local source
repositories. The string in `tools/port_horizon_chain.py` is a claim, not a
verified source archive. The generator rewrites imports and selected names;
its complete input/output correspondence cannot be rerun without that tree.
This audit does not establish a license grant for unexamined Horizon-authored
additions.

The imported files refer to absent historical records:

- `references/topology/classification-of-surfaces/README.md`;
- `references/ricci-flow/chow-liao-qin-2026/LICENSE.Apache-2.0.txt` and
  `interior-hessian-reuse.md`;
- `references/analysis/axel-workspace/LICENSE.Apache-2.0.txt`.

The newly archived donor evidence resolves the identified donor-file and
license-text availability gaps. It does not reconstruct those missing
historical adaptation reviews. The source manifest's statuses explicitly
retain that distinction.

## Bounded Remediation

For distribution of Apache-covered derivative files, Section 4 calls for a
license copy, preservation of applicable attribution, prominent modification
notices in modified files, and preservation of applicable upstream NOTICE
content. These obligations are stated by the
[Apache license itself](https://www.apache.org/licenses/LICENSE-2.0).
They do not require selecting a new license for all original project material.

The coordinator can integrate this package by registering the files from
`supporting/HorizonProofSources/canonical-entry.json`, then adding that JSON
file's own hash record to the canonical manifest. The proposed entry cannot
contain its own digest. The existing canonical manifest and foreign edits
were not changed during preparation.

The remaining bounded work is to reconcile the missing historical donor
records, record the Horizon-to-PoincareMT modifications prominently in the
generated files and generator, and point the retained notices to available
license evidence. In particular, namespace-only modifications still need
modification attribution. Retain original notices, even when they include
`All rights reserved`. Keep independent semantic and adaptation review
pending; neither a license nor a successful build clears those gates.

## Reproduction

`recover_evidence.py` records exact upstream bytes from pinned raw URLs or
existing pinned local Git objects. It executes no archived code, imports no
external Lean package, and refuses to overwrite different evidence bytes.
The URLs and acquisition times are recorded per payload. A repeat acquisition
must use a separate output snapshot because metadata timestamps are historical.

Validation checks every archived byte count and hash, all 73 current source
hashes at the inspection revision, all embedded donor hashes, and exact scope
counts. No Lean or Lake invocation is part of this source/notice audit.

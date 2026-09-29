---
date: 2026-09-20
status: ARCHIVED_VERIFIED_SOURCE_SPECIFIC_REVIEW_LIMITS
inspection_commit: 0406fd431cc5a684b44e93f16d971982c86351e2
---

# Additional Horizon ODE Donor Evidence

Three additional donor files, totaling 80,828 bytes, were recovered unchanged
from the existing read-only Git repository
`/home/ubuntu/workspace-poincare-conjecture`, commit
`f1cdb30cabdc8781d2d3dec86d3d99ab1820f30e`. No donor code was executed or
added as a project dependency. The supplemental source entry is
`HorizonODEProofSources20260920`; it preserves the earlier 73-file archive
as a separate historical record.

The [reuse manifest](supporting/HorizonProofSources/ode-reuse-manifest.json)
records exact paths, original bytes, SHA-256, retrieval method, current output
hashes and acceptance limits. The [recovery script](supporting/HorizonProofSources/recover_ode_evidence.py)
verifies all expected hashes and refuses to replace different existing bytes.
The [registration record](supporting/HorizonProofSources/ode-canonical-entry.json)
is included in the canonical manifest with its own hash added separately.

All three source paths begin with `formalized-sources/riemannian/`:

| Source Suffix | Bytes | Correspondence |
| --- | ---: | --- |
| `MorganTian/MorganTianLib/Ch01/JacobiODE.lean` | 22,679 | Exact current Jacobi header revision, path and hash. |
| `DoCarmo/DoCarmoLib/Riemannian/Geodesic/LinearODE.lean` | 18,567 | Verified comparison source; historical attribution is unknown. |
| `DoCarmo/DoCarmoLib/Riemannian/Variation/ArbitraryParallelTransport.lean` | 39,582 | Exact current AlongCurve/Manifold header revision, path suffix and hash. |

Independent source acquisition review by `/root/original_source_acquisition`
and coordinator verification agree on all three identities. The separately
archived [Apache-2.0 license](supporting/HorizonProofSources/AxelWorkspace/LICENSE)
matches the root `LICENSE` blob at this commit, SHA-256
`cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30`.
This preserves donor terms and selects no license for original project work.
The full Horizon modification-notice and provenance review remains open.

The [ODE source review](../reviews/declarations/2026-09-20-horizon-ode-source-review.md)
covers 19 Linear and 13 Jacobi declarations. The Linear comparison is exact
apart from the namespace and the two added `solOf_add`/`solOf_smul` theorems.
The Jacobi adaptation retains the selected quantitative arguments. Neither
source review grants post-elaboration acceptance. AlongCurve/Manifold has
source identity evidence only, with its adaptation and semantics still pending.

The earlier literal AxelWorkspace census is not a complete provenance audit.
This supplement resolves two additional census entries and the separate
unattributed Linear comparison; it does not establish mappings for the other
145 entries. The original Horizon snapshot `a1096626` remains unavailable.
In particular, the absent `weak-parabolic-regularity-sources.json` mapping
must not be reconstructed from coincident basenames without further evidence.

Validation uses `python3 tools/check_sources.py`, exact Git-blob comparisons,
structured manifest checks and source-review scope hashes. No Lean build
was run for this archive checkpoint; the lead owns the active repair build.

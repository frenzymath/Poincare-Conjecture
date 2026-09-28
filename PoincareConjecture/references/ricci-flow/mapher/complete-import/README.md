# Complete Public Poincare Import

This directory records the verified full import at workspace
`a71c2ef35f0ff06f34eb555982c03d3e6d92c624`. Its module counts, file mappings,
root registry, and compiled index describe that historical recovery revision.
The later [production cleanup](../production-cleanup/README.md) records which
modules remain active, with removal hashes and independent reduced-tree checks.

This directory records the subject-library integration under Horizon run 12,
mission `import-complete-mapher-poincare-20260928` revision 5. The primary source
is the directly fetched public repository `LehengChen/PoincareConjecture` at
`60de1a94ca7038d04ed123b490a3229f8aa5fa75`. Historical import provenance remains
`Mapher06/Poincare-MorganTian` at `a27691488baa6c690f50afc23376abb51abd2f9c`,
obtained through the project's `external-mapher` mirror. Both contain the same
completed controlled blowup construction and coupled bounded-distance changes.

## Source Identity

- [Public-source comparison](public-source-provenance.json) records both pins,
  the identical `PoincareMT` tree `99298b4e9ac964cb84d5b5c2851144d7fa2a8ccc`
  (27,237 tracked files), and identical root, package, toolchain, and comparator
  blobs. The public snapshot adds `LICENSE`, changes `.gitignore` and `README.md`,
  and omits 3,343 historical review, reference, and tooling files. These
  differences require no re-import of the unchanged production tree.
- Historical Mapher Git tree: `d48915c68b01e8a86196034199563a0ad7ba4b54`.
- Historical retrieved archive SHA-256:
  `728899b02154a374f2f2fb345505cea5b4c2864f10ef0007007e0b33c619035e`.
- [Source archive manifest](source-archive-manifest.json): all 30,590 tracked
  files, exact SHA-256, Git blob SHA-1, modes, and byte lengths. Every file was
  independently compared with its pinned Git blob, including all 27,574 Lean
  files. The large source archive remains in the source cache rather than
  being copied into the production repository.
- [Inventory](inventory-analysis.json) and [inventory notes](inventory-notes.md):
  the initial source classification, historical provenance matches, competing
  destinations, and subsequent assigned batches. Snapshot counts in the notes
  describe intermediate integration states.
- [Current reconciliation](reconciliation.json): the integration owner's
  consolidated source-to-destination disposition. Batch manifests below retain
  the detailed transformations and hashes supporting that reconciliation.

Reproduce the source identity comparison from checkouts at the two exact pins:

```sh
node references/ricci-flow/mapher/complete-import/compare-public-source.mjs \
  PUBLIC_CHECKOUT MAPHER_CHECKOUT OUTPUT_JSON
```

## Public Endpoints And Subjects

The public import is `PoincareLib.Topology.Manifold.Poincare`. It exports
`PoincareMT.smoothPoincareSkeleton` and
`PoincareMT.topologicalPoincareSkeleton`, preserving the source universe,
hypotheses, and proof terms. [Endpoint evidence](endpoints.json) records exact
declaration comparisons. Its faithful export is distinct from the final
recursive admission check, whose passing integrated result is retained in
[verification results](verification/results.json).

All paths below are relative to `PoincareLib/`.

| Subject | Main module trees |
| --- | --- |
| Differential and integral analysis | `Analysis/Calculus/`, `Analysis/ODE/`, `MeasureTheory/` |
| Metric and connection geometry | `Geometry/Riemannian/`, `Geometry/Manifold/` |
| Local Ricci flow and curvature estimates | `Geometry/RicciFlow/Local/`, `Geometry/RicciFlow/Curvature/`, `Geometry/RicciFlow/Pinching/`, `Geometry/RicciFlow/Harnack/` |
| Reduced geometry and spacetime | `Geometry/RicciFlow/ReducedGeometry/`, `Geometry/Spacetime/`, `Geometry/RicciFlow/Generalized/` |
| Ancient solutions and limits | `Geometry/RicciFlow/AncientKappa/`, `Geometry/RicciFlow/Soliton/`, `Geometry/RicciFlow/Compactness/`, `Geometry/RicciFlow/Blowup/` |
| Canonical neighborhoods and surgery | `Geometry/RicciFlow/CanonicalNeighborhood/`, `Geometry/RicciFlow/Surgery/` |
| Area, loops, width, and extinction | `Geometry/RicciFlow/Area/`, `Geometry/CurveShortening/`, `Geometry/RicciFlow/Extinction/`, `Topology/Homotopy/` |
| Homology, triangulation, and manifold topology | `AlgebraicTopology/`, `Topology/CWComplex/`, `Topology/Manifold/` |
| Smoothing and final assembly | `Topology/Manifold/Smoothing/`, `Topology/Manifold/Poincare/` |

Detailed batch maps are [bounded-distance](bounded-distance-update.json),
[controlled blowup](blowup-map.json), [annulus comparison](annulus-update.json),
[neck and cap](neck-cap-map.json), [deep horn](deep-horn-map.json),
[regular limit](regular-limit-root-map.json),
[standard cap and canonical induction](standard-cap-canonical-map.json),
[other surgery modules](misc-surgery-map.json),
[foundations](foundational-map.json),
[definition splits](definition-splits-map.json), and
[smoothing refactors](smoothing-refactor-map.json).
[Subject path renames](subject-path-renames.json) replace numbered production
paths while retaining their original locations as provenance.
[Superseding transformations](superseding-transformations-map.json) record
later provider-name and verification-import repairs without overwriting the
historical batch hashes.

The [Schoenflies consolidation review](schoenflies-consolidation-review.md) and
[historical preparation plan](schoenflies-consolidation-plan.json) identify the
pre-existing 357-module M38 namespace port. The
[applied consolidation map](schoenflies-consolidation-map.json) records its
retirement in favor of ordinary subject modules and the three updated
consumers. The old M62 dependency no longer requires that port. Regenerated
registration covers 28,377 active modules and 1,175 roots without import
cycles. The three changed consumers passed a focused managed build (12,710
jobs, exit 0); the final integrated build and endpoint audits also passed.

[Compilation repairs](compatibility-repairs-map.json) record canonical names,
scoped elaboration settings, and compatibility fixes required by the combined
library. [Root name-collision repairs](collision-repairs-map.json) distinguish
compiler-confirmed conflicts from repeated theorem names that Lean permits.
Reusing the coordinate definition through a facade reduces the final root
count to 1,174 while retaining 28,377 active modules; no mathematical premise
or source construction was substituted.

The [focused frenzymath comparison](frenzymath-99148d28-focused-comparison.md)
records the additional public snapshot requested by the operator. The relevant
proofs have unchanged text after recorded namespace and comment normalization;
no integration fix or source repin follows from that comparison.

The [M76 visibility scan](m76-visibility-scan.json) compares every one of the
6,252 mapped source modules against the public pin and now reports no public
source declaration remaining private in its corresponding workspace module.
The [earlier scan](m76-visibility-scan-before-provider-repair.json) preserves
the three additional mismatches and exact source/target hashes that led to
the provider repairs in the smoothing map. Their declaration suffixes matched
after removing `private`. This is a deterministic visibility comparison, not
a Lean build or an admission audit. Reproduce it without compilation:

```sh
node references/ricci-flow/mapher/complete-import/scan-m76-visibility.mjs \
  PINNED_PUBLIC_CHECKOUT
```

## Package Comparison

Source and workspace both use `leanprover/lean4:v4.33.1`. All nine shared
packages have identical URLs and revisions:

| Package | Revision |
| --- | --- |
| mathlib | `0df444a360eaa60ab8c11dca51a86af692955474` |
| plausible | `b7eb3304aeae834b12dda98993a37f6a41f6f0bb` |
| LeanSearchClient | `5f4d51b81cbd3f6b32b156bfad9056621a040404` |
| importGraph | `16f02aa7642864af59f1ff0e384a015994db9118` |
| proofwidgets | `4be2e3d5087eeb272cf5a8853b8f9dd025ef5957` |
| aesop | `3448c0bcc5ce01b2d1546e483ec3620e32df3d0e` |
| Qq | `92c15be17b7caf78c2ad767ec40f89052d908d81` |
| batteries | `4488d40d070b9700d4d5a6aa342f0d40c31b2a2d` |
| Cli | `6130a47896ce867c6a4a55373441e59e565bad0f` |

The source additionally pins `lean4export` at
`15f6055e299ad5b89345e533cc2192f4cc00f659` and `Comparator` at
`3927ad383f208ae977c340a91c48ac9b497d2097`. They support the separate
`Challenge` and `Solution` environments rooted in `comparator/`; the workspace
production package directly requires mathlib. The original
[Lake file](source-notices/lakefile.lean),
[package manifest](source-notices/lake-manifest.json), and
[toolchain](source-notices/lean-toolchain) are preserved byte-for-byte.
The archive manifest records the full structured package comparison.

## Authorship And Notices

The primary public snapshot supplies the exact
[Apache-2.0 LICENSE](source-notices/public-snapshot/LICENSE), preserved alongside
its [README](source-notices/public-snapshot/README.md); their hashes are in the
public-source comparison. The older Mapher
[licensing record](source-notices/docs/licensing.md), which says no license had
been selected, is retained as historical evidence and does not describe the
current primary-source license. Individual imported files retain their source
headers, copyright notices, donor identities, and adaptation notes.

`source-notices/` preserves the source README, licensing and attribution
records, the donor LICENSE and NOTICE files, and the two archived literature
deposit licenses. Its 18 historical files and their exact hashes are listed in
the archive manifest; the two public-snapshot notices are recorded separately.
The upstream records distinguish original project material,
DifferentialGeometry and other donor material, import-only bridges, and
historical attribution questions. Their retained statements are provenance,
not a new legal or semantic certification by this integration.

## Integration And Verification Policy

Equivalent existing subject modules are reused, including Horizon-origin
proofs returned through Mapher. Source import-only facades map to the existing
implementations. New production helpers remain in scope even when neither
endpoint imports them. Mechanical imports preserve declaration bodies except
recorded module, namespace, identifier, and compatibility adaptations.

Source audits, experiments, tooling, and superseded duplicate constructions
are classified individually. Retired material belongs under `archive/`,
outside package roots, with original locations and hashes. The
[controlled-construction retirement record](controlled-retirement.json)
preserves the disposition of the earlier active construction. Historical
accepted contracts and earlier import evidence retain their original pins.
The [verification archive map](verification-map.json) records 318 workspace
inspection files moved intact out of the production tree, their mathematical
import replacements, and the excluded source inspection module. These files
contain diagnostic commands, private audit tooling, or an empty historical
placeholder; they supply no named mathematical declarations. Twenty-three
mixed modules with diagnostic commands also supply mathematical declarations
and remain in production unchanged.

Verification **passed for the integrated revision**. The full `PoincareLib`
build completed 37,084 jobs, including the aggregate root, with exit 0
(2,317.58 seconds). `make check` passed its frozen-contract checks, full build,
and recursive endpoint audit. The final audit took 10.674 seconds and reported
exactly `propext`, `Classical.choice`, and `Quot.sound` for both original
universe-general public endpoints, with no admission or extra supplier argument.
[Verification results](verification/results.json) retain exact commands,
compressed logs and hashes, focused compilation results, and source-manifest
hashes. Source inventories and historical builds are separate evidence.
Under the operator's 2026-09-28 storage constraint, run 12 must not execute the
comparator, Nanoda, or comparator environment exports, including through
`make check` or wrapper scripts. Use focused managed Lake builds, `lake env lean`,
LSP, and scoped endpoint axiom checks; check disk headroom, reuse dependencies,
and use the assigned disk-backed `TMPDIR`. The final `make check` invocation
must retain these restrictions.

The upstream comparator folder, pinned configuration, separate Mathlib-only
Challenge and integrated Solution, permitted-axiom list, and enabled Nanoda
check remain available for external execution; see
[the comparator instructions](../../../../comparator/README.md).
Comparator verification is **not performed for this integrated revision** and
is not a run 12 completion blocker under revision 5. Historical tooling checks
do not establish endpoint comparison success. Challenge admissions remain
outside production; the admission-free mathematical endpoint requirements and
recursive axiom checks above remain mandatory.
The endpoint check is `scripts/check_poincare_endpoints.lean`. Final publication
and mission completion remain the integration owner's responsibility.

The focused repository target builds the public endpoint and then checks its
recursive axioms. The full target checks frozen contracts, builds the library,
and runs the same endpoint audit. Neither target invokes the comparator,
Nanoda, or an environment exporter:

```sh
LAKE_ARTIFACT_CACHE=false make endpoint-axioms \
  LEAN_BUILD="python3 \"$HORIZON_BUILD_HELPER\" --local --json --timeout 7200" \
  LEAN_CHECK="python3 \"$HORIZON_BUILD_HELPER\" --local --json --lean"

LAKE_ARTIFACT_CACHE=false make check \
  LEAN_BUILD="python3 \"$HORIZON_BUILD_HELPER\" --local --json --timeout 7200" \
  LEAN_CHECK="python3 \"$HORIZON_BUILD_HELPER\" --local --json --lean"
```

These reproduction commands use the same managed build route as the retained
passing results. Artifact-cache reads were disabled after an empty cached
object was preserved and rebuilt; shared cache files were not modified.

## Compiled Declaration Index

The [compiled index summary](compiled-declarations-summary.json) accounts for
all 28,377 active submodules and 120,515 compiler-reported source declarations.
Its compressed index occupies 6,077,565 bytes and is tied to the retained
successful build evidence and exact source hashes.

`index-compiled-declarations.mjs` runs **after the final integrated build
passes**, with the retained successful build result supplied explicitly:

```sh
node references/ricci-flow/mapher/complete-import/index-compiled-declarations.mjs \
  --after-successful-build --build-evidence PATH_TO_SUCCESSFUL_BUILD_RESULT
```

It traverses `production-roots.json`, checks its root hash and full active
module coverage, and reads each compiled `.ilean` JSON object. The resulting
`compiled-declarations.jsonl.gz` has one sorted record per active production
submodule: source SHA-256, compiler-metadata SHA-256, metadata version, compiler
import tuples, and sorted declaration names with their unmodified source-range
arrays. `compiled-declarations-summary.json` records counts, compressed and
uncompressed hashes, toolchain, generator versions, and the build-evidence
hash. The generated index is metadata from the successful integrated build,
not a comparator environment export.

The generator rejects missing artifacts, unsupported metadata schemas,
compiler/source import mismatches, incomplete coverage, and source changes
during generation. It does not rerun Lean or repeat admission audits. This is
an index of compiler-reported source declarations, including their proof source
ranges, not an exhaustive listing of synthesized kernel auxiliaries or an
independent proof that the build succeeded. Build evidence is retained by hash;
the caller is responsible for supplying the actual successful final result.
The package aggregator itself has no mathematical declarations and is covered
by its root hash rather than an extra index record.

`test-compiled-declaration-index.mjs` exercises generation and rejection paths
using temporary synthetic metadata. Those fixtures do not constitute Lean
proof evidence and do not create a production declaration index.

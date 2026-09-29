# Schoenflies Namespace Port Consolidation

The initial read-only review used workspace base
`6a6637f3732aa69ca351a3bc31844a626222eddb`. The 357-file namespace port was
already tracked at this base and came from the earlier final-assembly import;
this migration did not create it. The integration owner has now applied the
consolidation recorded in [schoenflies-consolidation-map.json](schoenflies-consolidation-map.json):
357 duplicate active modules were retired and three consumers now use the
ordinary subject implementation. Production registration has been regenerated
with 28,377 modules, 1,175 roots and no import cycles. The focused managed
build of all three changed consumers passed (12,710 jobs, exit 0, 63.334 s).
The integrated build and final endpoint audits remain pending; the initial plan is historical
preparation evidence, not the current applied-state manifest.

## Current Dependency Evidence

The upstream `PoincareMT/Proofs/M38/SchoenfliesPort` headers explain that the
port removed an old transitive M62 import. The ordinary subject implementation
now uses `Geometry.Manifold.Circle.FlatCharts`. Its `Schoenflies.Neighborhood`
closure has 1,164 PoincareLib modules and reaches neither curve shortening nor
surgery events. Replacing every port import by its ordinary counterpart and
removing the port nodes yields 28,377 active modules and zero import cycles.
The old dependency reason no longer requires a second active construction.

All 357 files have existing ordinary counterparts. The special
`FlatCircleCharts.lean` maps to `Geometry/Manifold/Circle/FlatCharts.lean`;
the remaining 356 map by removing `Topology/Manifold/Surgery/Event/Schoenflies/`.
The plan records exact source, destination and proposed reused-file hashes.
321 pairs are identical after import, comment, namespace and command-scope
normalization; 328 pairs agree also ignoring whitespace. All 2,534 source
declaration names have counterparts after removing the namespace prefix.
These lexical counts are review aids, not new Lean evidence.

The other 29 module pairs use existing equivalent proofs: qualified versus
field-notation applications, explicit versus inferred arguments, tactic
layout or proof-script variants, unused binder names, reordered declarations,
and extra scope opens. Their public headers agree after whitespace and unused
binder normalization. Two private helpers differ from `Finite` plus a local
`Fintype.ofFinite` to a `Fintype` hypothesis:

- `.../Closing/Ends/Family/ActualAnnuli.lean`: `exists_common_strict_upper_bound`.
- `.../Iteration/Core/OneCritical/SaddleEnds/ResolutionCircles.lean`:
  `index_two_component_family`.

The ordinary proofs give the source propositions by installing
`Fintype.ofFinite`; no new public premise or supplier is needed. Do not claim
byte-identical proof terms for these nonidentical pairs. Preserve the source
proofs at the public pin and the old destination at its existing Git commit.

## Exact External APIs

Only three production modules outside the port imported it or named its
namespace. Each calls one theorem; the complete theorem header agrees exactly
after whitespace normalization, with the same surrounding universe/variables.
No new alias is needed for any in-repository caller.

| Consumer under `Topology/Manifold/Surgery/Event/` | Ordinary theorem | Header SHA-256 |
| --- | --- | --- |
| `Capped/CappedTubeIncident.lean` | `PoincareMT.CapTubeAttachment.exists_absorption_threshold` | `500c4a9898d5e742885ef65f383e3b444b929985769b5f2057a3e0004caf710c` |
| `Cylinder/CylinderSphereFilling.lean` | `Poincare.exists_ambient_map_of_euclidean_sphere_collar` | `816ab3ba11310f77ead8f2adaf5ba4d89d6e08c9d9abcd2f16370f365cf9360c` |
| `Collared/CollaredChartFilling.lean` | `Poincare.Manifold.Schoenflies.ball_neighborhood_of_compact_collar_side` | `1b795a00a846599f4ef9dcd077af404ec3709d3d76b31708e3390f49189f33d7` |

The cylinder caller imports `Diffeomorph.EssentialSphere.Extension`; the called
theorem is supplied transitively by `EssentialSphere.Euclidean`. Retain that
import boundary during the mechanical replacement.

## Historical Reproduction

[inspect-schoenflies-consolidation.mjs](inspect-schoenflies-consolidation.mjs) produced
[schoenflies-consolidation-plan.json](schoenflies-consolidation-plan.json) without
source edits. The matching
[apply-schoenflies-consolidation.mjs](apply-schoenflies-consolidation.mjs) defaults
to a dry run. It verifies all 357 port hashes, all 357 reused-target hashes,
all three consumer hashes, and every pinned public source hash before any
mutation. The temporary pending-map candidate was removed after application;
the applied map linked above is authoritative.

The commands below reproduce the migration from its exact historical
pre-consolidation state. The guarded applier is not intended to run again on
the already consolidated production tree:

```sh
node references/ricci-flow/mapher/complete-import/apply-schoenflies-consolidation.mjs \
  --source=PINNED_PUBLIC_CHECKOUT --apply
node references/ricci-flow/mapher/complete-import/register-production.mjs --apply
node references/ricci-flow/mapher/complete-import/reconcile-inventory.mjs \
  PINNED_HISTORICAL_CHECKOUT
```

Pass the existing checkout at the reviewed public pin to `--source`; use the
existing historical Mapher checkout for reconciliation. Both source locations
are configurable, and no new checkout is required. The apply step writes one new
mapping overlay, changes exactly the three consumer imports/qualifications,
and removes the 357 duplicate active files. It preserves the ordinary
constructions, unrelated source repairs, old per-file manifests, and source
hash/archive records. The root generator registers all remaining modules;
reconciliation must again report zero unresolved entries. No large source
snapshot or comparator operation is needed.

The three changed consumers passed the focused managed build recorded in
`schoenflies-consolidation-build-final.log`. The remaining verification is
the integrated library build and final endpoint audits.
Integration owner: current session owner; metadata/consolidation preparation
owner: `provenance_reconcile`. No final build or axiom result is claimed here.
No external blocker is asserted.

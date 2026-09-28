# Production Endpoint Closure

This separate cleanup follows the verified complete import at
[`a71c2ef35f`](/api/v2/forge/web/poincare-conjecture/workspace-poincare-conjecture/commit/a71c2ef35f0ff06f34eb555982c03d3e6d92c624).
That published Git commit preserves every removed source and its original
verification evidence. The import source pin, contracts, dependency revisions,
endpoint statements, universes, and concrete endpoint proofs are unchanged.

## Scope

The [removal manifest](removal-manifest.json) compares source imports with the
successful build's compiler-recorded imports. Starting at the common public
module for both endpoints reaches 23,554 source modules. Only the package entry
point `PoincareLib.lean` remains outside that closure, forwarding one import to
`PoincareLib.Topology.Manifold.Poincare`.

| Physical source metric | Verified import | Reduced library |
| --- | ---: | ---: |
| Lean files, including package entry point | 28,378 | 23,555 |
| Lines under identical counting rules | 3,684,691 | 3,060,326 |
| Compiler-reported source declarations | 120,515 | 102,503 |

The change removes 4,823 complete modules, 18,010 declarations in those
modules, two unused helper theorems, two repeated import lines, and the old
package import list. The net reduction is 624,365 physical lines.

[Retained-file edits](retained-edits.json) identify the two plain helper
theorems and the repeated imports. Neither theorem had registration attributes
or a reference use in any of the 23,554 retained modules' compiler metadata.
The remaining endpoint provider and width aliases are consumed by final
assembly and stay intact. Unique imports of retained modules are unchanged.
The closure therefore preserves imported instances, simp extensions, notation,
macros, and elaborators. This is not a claim that every declaration within
every retained module occurs in the final proof term; no such blanket pruning
was performed.

## Archive And Links

Every removed path has its original SHA-256 and recovery-commit locator in the
manifest. No second compilable historical source tree is retained. The
[application record](application.json) records same-filesystem quarantine of
36,487 local build artifacts, outside the Lean search path. Shared cache
inodes and retained artifacts were not modified.

The two scoped audits of historical helper declarations import removed
modules. Their exact texts are preserved as noncompilable provenance in
[`archive/`](archive/), with [hashes and original paths](archived-audits.json).
Their passing results belong to the recovery commit. Current endpoint checks,
package tooling, and comparator source/configuration remain available.

The [source-link review](link-review/README.md) found all affected graph and
blueprint URLs already pinned to historical commits; no graph repinning was
necessary. The blueprint coordinator owns its seven historical dependency
records and will distinguish their old source route when updating its baseline.
The complete-import inventories remain records of the recovery revision;
this manifest records their later production disposition.

## Validation

The reduced library passed `make check`: 32,261 jobs in 52.319 seconds,
followed by the endpoint audit in 9.418 seconds, both with exit 0.
[Verification evidence](verification.json) retains the compressed logs and
hashes. The [post-build source check](source-validation.json) confirms all
4,823 removed modules remain unavailable, all retained imports agree, and the
compiled source-declaration count is 102,503. The integrated Solution wrapper
also passed a managed Lean check; this does not execute the comparator.
The direct supplier check `scripts/check_import_graph_suppliers.lean` passed
in 6.019 seconds for M30, its concrete milestone provider, the M32 provider,
and the smooth ball-neighborhood theorem, each with exactly the three standard
axioms. Its log distinguishes the current constructions from historical
admitted graph records without reinterpreting those older records.
`verify.mjs` checks every
removed source and compiled module is unavailable through Lean's effective
search path, retained source hashes and compiler imports agree with the
reviewed closure, and the two retired helper declarations are absent from
rebuilt metadata. Run it before and after the managed build:

```sh
node references/ricci-flow/mapher/production-cleanup/verify.mjs --before-build

env -u LEAN_PATH -u LEAN_SRC_PATH \
  LAKE_ARTIFACT_CACHE=false LAKE_RESTORE_ARTIFACTS=false \
  make check \
  LEAN_BUILD="python3 \"$HORIZON_BUILD_HELPER\" --local --json --timeout 7200" \
  LEAN_CHECK="python3 \"$HORIZON_BUILD_HELPER\" --local --json --timeout 3600 --lean"

node references/ricci-flow/mapher/production-cleanup/verify.mjs
```

The current endpoint check requires exactly `propext`, `Classical.choice`, and
`Quot.sound` for both universe-general endpoints. Comparator, Nanoda, and
environment-export verification are **not performed**, as required by the
run 12 operator storage constraint. Pinned dependencies and their existing
artifacts are reused. Retained modules use the successful compiled outputs
whose source and import hashes match the published recovery evidence.

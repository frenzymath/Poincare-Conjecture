# Verification and build cost

## Routine CI

Pushes and pull requests run source scans and tooling tests, with no Lean
compilation. Pages generates documentation separately. Standard GitHub-hosted
runner execution is free for public repositories; larger runners and storage
have separate billing rules. See GitHub's
[billing documentation](https://docs.github.com/en/billing/concepts/product-billing/github-actions).
The lightweight policy limits routine runtime and storage regardless of the
eventual proof's size. It does not certify compilation.

## Comparator evidence

Comparator checks a solution against a trusted challenge, restricts permitted
axioms and replays exported proof terms. The challenge and its definitions
still require mathematical review. See the upstream
[trust assumptions](https://github.com/leanprover/comparator#readme).

The **Comparator verification** workflow is manual and uses a dedicated
self-hosted Linux runner labeled `lean-verification`. There is no automatic
PR execution on that runner. Provision it with the pinned Lean toolchain,
Landrun and Nanoda, a functioning user systemd manager, and sufficient disk
and memory. Use an isolated account without unrelated credentials.

The primary proof import must supply these inputs before this workflow can run:

- `PoincareConjecture/Comparator/config.json`, its Challenge and Solution modules.
- Pinned Comparator and lean4export dependencies in the project's Lake manifest.
- Exactly `propext`, `Classical.choice`, and `Quot.sound` as permitted axioms,
  nonempty theorem targets, and `enable_nanoda: true`.

The draft import supplies these targets and pins. A local comparator run passed
at commit `1876d7dc2c85325a3f62ce9776af98f910c5db04`: both Nanoda and Lean's
default kernel accepted the solution, and the driver exited successfully after
6h 55m. The source stayed clean and unchanged throughout the run. See the
[integration evidence](../archive/PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md)
for the report, compressed logs, tool hashes and execution details. This is a
local result, not a CI attestation or a claim about later unchecked proof changes.
Historical Horizon build and recursive endpoint axiom evidence is retained in
`archive/PoincareConjecture/references/ricci-flow/mapher/production-cleanup/`;
it is not a comparator result or a build of the final PR revision.
The workflow builds the pinned verification tools with the reviewed
[`nanoda-before-parse.patch`](../PoincareConjecture/Comparator/nanoda-before-parse.patch),
then invokes comparator. This execution-order patch avoids retaining both
kernels' proof representations concurrently. It preserves statement comparison,
axiom validation, both kernel checks, and all success conditions. Source and
patch hashes are recorded in `Comparator/provenance.json`.

For a local run, start from a clean checkout of the intended commit. Build
the pinned tools in the primary Lean project:

```bash
cd PoincareConjecture
make comparator-build
cd ..
export COMPARATOR_LANDRUN=/absolute/path/to/landrun
export COMPARATOR_NANODA=/absolute/path/to/nanoda_bin
export COMPARATOR_LEAN4EXPORT="$PWD/PoincareConjecture/.lake/packages/lean4export/.lake/build/bin/lean4export"
python3 scripts/verify_comparator.py --output .verification/comparator
```

The script records commit and tree hashes, configuration, input hashes,
executable hashes, timestamps, the actual command, exit status and complete
combined output. It rejects dirty source trees and checks that the source and
commit remain unchanged. Failures are recorded as failures; missing prerequisites
stop before a verification claim is produced.

The Actions workflow publishes logs and the report. Successful runs also
produce a provenance-attested archive, downloadable from the workflow run.
Check its GitHub provenance with:

```bash
gh attestation verify comparator-evidence.tar.gz --repo frenzymath/Poincare-Conjecture
```

An attestation establishes the workflow origin and digest of the archive. It
does not independently verify mathematics or eliminate trust in the runner.
A local report is a reproducibility record, not an authenticated CI result.
Independent rerunning of comparator at the same commit is stronger evidence.

Record the exact successful workflow URL and commit in a release, and attach
the evidence archive there for durable access before Actions artifacts expire
(30 days here). Do not display a success badge for a newer, unchecked commit.

# Local integration verification

Comparator passed for commit `1876d7dc2c85325a3f62ce9776af98f910c5db04`
(tree `c3a35b96ee5326be1cdbfe2e2421d85bd45375bc`). Both public smooth and
topological targets were checked, with Nanoda enabled, no definition holes,
and only `propext`, `Classical.choice`, and `Quot.sound` permitted.

The source stayed clean and unchanged throughout the run. On 2026-09-28 UTC,
the driver reported all three required messages and exited with code zero:

```text
Nanoda kernel accepts the solution
Lean default kernel accepts the solution
Your solution is okay!
```

Service runtime was 6h 55m 24.756s. Systemd reported a 44.7G memory peak
(swap: 4.9G); the unit had a 52 GiB memory cap. Verification ran on the local
host, not on run12 workers.

## Evidence and reproduction

- `verification.json`: exact commit, tree, configuration, command, timestamps,
  executable hashes, unchanged-source check, success markers and log digest.
- `comparator.log.gz`: complete combined output. Its uncompressed SHA-256 is
  `ac882c6f2bdf0ad3be2d79108b0eeb097540b1bacf07aeca0fb5bb8ad640b639`.
- `execution-context.json`: resource limit, underlying tools and cache adapter.
- `provenance.json` and `nanoda-before-parse.patch`: pinned upstream inputs and
  the reviewed execution-order change. Nanoda runs before environment parsing
  to reduce peak memory. Statement comparison, axiom validation, both kernels
  and all success conditions remain enabled.
- `landrun-cache-adapter.sh`: forwards three Lake cache variables through the
  stock Landrun sandbox; all supplied sandbox restrictions remain intact.
  Its absolute paths describe this host and must be adapted on another host.
- `comparator-build.log.gz`: successful verifier build and exact statement
  preflight at the verified revision.
- `make-check.log.gz`: successful fresh library build (32,266 jobs) and both
  recursive endpoint axiom audits at `516badd1`. The production proof tree was
  unchanged at the comparator revision: `5945c0ab3033f4e90e6f97c0548c75ebc2c4d88d`.

Follow the repository's [verification instructions](../../../../../site/verification.md)
to rerun. These files are local reproducibility evidence, not authenticated CI
attestations. Later documentation/evidence commits are not themselves the tested
revision. Public statement fidelity and blueprint links still require review;
source statistics and website readiness labels are not kernel verification.

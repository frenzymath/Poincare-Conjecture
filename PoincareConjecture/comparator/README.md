# Isolated endpoint comparator

## Run 12 Storage Restriction

The operator's 2026-09-28 storage constraint, mission
`import-complete-mapher-poincare-20260928` revision 5, prohibits running the
comparator, Nanoda, or comparator environment exports on Horizon workers,
including through `make check` or wrapper scripts. The commands below are
preserved for external execution. Comparator verification is **not performed
for the integrated revision** and is not a run 12 completion blocker. Focused
managed Lean builds and recursive endpoint axiom checks remain required.
The permitted-axiom list, isolation, and enabled Nanoda check are unchanged.

This imports `comparator/` from
[LehengChen/PoincareConjecture at 60de1a94](https://github.com/LehengChen/PoincareConjecture/tree/60de1a94ca7038d04ed123b490a3229f8aa5fa75/comparator).
Challenge and `comparator.json` are byte-for-byte copies. Solution changes only
its import to `PoincareLib.Topology.Manifold.Poincare`; both proofs still apply
the corresponding `PoincareMT` skeleton declaration, polymorphically in `u`.
Exact revisions, file hashes and the additional external-tool pins are in
[`provenance.json`](provenance.json).

Reuse the accepted
[statement and definition-boundary review](../reviews/contracts/comparator-challenge-20260928.md).
Challenge imports only Mathlib and intentionally admits its two target proofs.
Challenge and Solution are separate Lake libraries and exported environments:
never import both into one Lean module. Only `propext`, `Classical.choice`, and
`Quot.sound` are permitted; there are no definition holes, and Nanoda is enabled.

## Prepare

Use the repository's Lean 4.33.1 toolchain and locked Lake dependencies. From
the workspace root, with Git, Python 3, Go >= 1.24 and recent Rust/Cargo:

```sh
make comparator-build
make comparator-setup
bash comparator/run.sh --preflight
```

`comparator-build` compiles only Challenge, Comparator and lean4export. Under
Horizon, use the managed build helper:

```sh
make comparator-build LEAN_BUILD="python3 $HORIZON_BUILD_HELPER --json"
```

`comparator-setup` builds pinned Landrun and Nanoda sources under the ignored
`.lake/comparator-tools/`, using the upstream dependency locks. It does not
install a compiler or change system packages. The preflight checks the
executables and starts Landrun in a restricted user systemd unit; it does not
check either endpoint. The GitHub workflow builds only these isolated tools
and Challenge; workflow success is not endpoint acceptance.

## Verify The Integrated Solution

On Linux with Landlock and a working user systemd manager, as an unprivileged
user, run from the integrated production revision:

```sh
make comparator
```

The runner invokes the pinned comparator through `lake env` in a user systemd
unit with `RestrictAddressFamilies=~AF_UNIX`, as required by the pinned
[Comparator documentation](https://github.com/leanprover/comparator/blob/3927ad383f208ae977c340a91c48ac9b497d2097/README.md).
The comparator builds and exports Challenge and Solution separately, compares
the statements and their referenced definitions, audits recursive axioms, and
replays the solution in Lean and Nanoda. Success must include
`Nanoda kernel accepts the solution` and `Your solution is okay!`, with exit 0.
Failures are propagated; the runner has no option to disable Nanoda or replace
Landrun with an unsandboxed shim.

Existing trusted binaries can be selected with absolute paths in
`COMPARATOR_LANDRUN`, `COMPARATOR_NANODA`, and `COMPARATOR_LEAN4EXPORT`.
Default paths point to the binaries prepared above. Supply trusted source,
dependencies, and artifacts according to the upstream comparator assumptions.

## Validation Boundary

On 2026-09-28, against workspace base `11767a3a` plus this additive tooling:

- Managed `Challenge @Comparator/comparator @lean4export/lean4export` build
  passed on Lean 4.33.1, with exactly the two intentional Challenge admissions.
  The first successful build's artifact upload failed (`invalid Lake staging
  output`); the subsequent local check passed without that cache error.
- `make check LEAN_BUILD="python3 $HORIZON_BUILD_HELPER --json"
  LEAN_TARGETS="Challenge @Comparator/comparator @lean4export/lean4export"`
  passed, including all 12 frozen contract hashes. Plain `make check` retains
  its full default library build and was deliberately not run on the old
  production tree.
- The pinned Landrun and Nanoda binaries built with Go 1.24.0 and Rust 1.98.1;
  `bash comparator/run.sh --preflight` passed on Linux 7.0.0.
- The pinned Comparator's `tests/projects/simple_match` fixture was copied to
  a fresh temporary Lake package on Lean 4.33.1, with `enable_nanoda` changed
  to `true`. The same restricted systemd invocation successfully built and
  exported its separate environments, accepted the fixture in Nanoda and Lean,
  and printed `Your solution is okay!` (exit 0). This was the upstream natural
  number commutativity fixture, not the production Poincare Solution.

These are historical tooling checks performed before the storage restriction;
they do not certify either integrated Poincare endpoint. Final production
compilation and recursive endpoint audits remain with mission
`import-complete-mapher-poincare-20260928` and its active integration owner.
Endpoint comparison remains available for an external runner and is recorded
as not performed, rather than passed, for this integrated revision.

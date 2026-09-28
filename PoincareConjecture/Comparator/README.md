# Comparator

The layout, Challenge and config.json come from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture/tree/99148d28f5607a908b90c3aa1908b0c5529df9d4/Comparator).
Challenge and configuration are byte-for-byte copies. Statements.lean reproduces
the public definitions in the PoincareConjecture namespace using only Mathlib.
This separate module prevents proof-library instances from changing statement
elaboration. Solution imports these definitions and
PoincareLib.Topology.Manifold.Poincare, then applies the PoincareMT endpoint
proofs. No hypothesis or conclusion is changed.

Challenge imports only Mathlib and intentionally admits its two targets.
Challenge and Solution must be compiled separately. The configuration permits
only propext, Classical.choice and Quot.sound, has no definition holes, and
requires Nanoda. Exact source hashes and tool pins are in provenance.json.
The comparator build also checks exact identity of the elaborated statement
definitions and theorem types before the full proof export and kernel replay.

From the primary package directory:

```sh
make comparator-build
make comparator-setup
bash Comparator/run.sh --preflight
make comparator
```

Tool setup needs Git, Go >= 1.24 and Rust/Cargo. Execution needs Linux with
Landlock, a working user systemd manager, sufficient disk space and a
disk-backed TMPDIR. The stock Nanoda executable is built from the same upstream
revision documented by the public snapshot; no checks are disabled.

The pinned comparator driver receives the small, hash-checked
`nanoda-before-parse.patch` during `make comparator-build`. It runs Nanoda before
parsing the exported Lean environments. The original order exceeded a 52 GiB
memory limit by retaining both kernels' proof representations simultaneously.
Statement comparison, permitted-axiom validation, both kernel checks, and the
conditions for success are unchanged. `provenance.json` records both driver
hashes and the patch hash; `prepare.py` refuses to patch an unknown source.

For commit-bound logs and executable hashes, use the repository-level
[verification runner](../../site/verification.md). Success requires
`Nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`,
`Your solution is okay!`, and exit code zero.

Historical Horizon build and axiom evidence is not comparator evidence.
The earlier restriction against heavy verification on run12 workers remains;
the operator has authorized local verification on the host separately.

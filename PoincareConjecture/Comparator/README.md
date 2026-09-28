# Comparator

The layout, Challenge and config.json come from
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture/tree/99148d28f5607a908b90c3aa1908b0c5529df9d4/Comparator).
Challenge and configuration are byte-for-byte copies. The solution imports
PoincareLib.Topology.Manifold.Poincare, reproduces the unchanged public
definitions in the PoincareConjecture namespace, and applies the imported
PoincareMT endpoint proofs. No hypothesis or conclusion is changed.

Challenge imports only Mathlib and intentionally admits its two targets.
Challenge and Solution must be compiled separately. The configuration permits
only propext, Classical.choice and Quot.sound, has no definition holes, and
requires Nanoda. Exact source hashes and tool pins are in provenance.json.

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

For commit-bound logs and executable hashes, use the repository-level
[verification runner](../../site/verification.md). Success requires
`Nanoda kernel accepts the solution`, `Lean default kernel accepts the solution`,
`Your solution is okay!`, and exit code zero.

Historical Horizon build and axiom evidence is not comparator evidence.
The earlier restriction against heavy verification on run12 workers remains;
the operator has authorized local verification on the host separately.

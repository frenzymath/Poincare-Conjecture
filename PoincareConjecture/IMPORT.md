# Subject-organized Poincare library import

This draft imports the reduced `PoincareLib` from Horizon workspace commit
`e4f267f2dd99872fc1162af7b8ebe098a434872e`. Its 23,555 Lean files (including
the package entry point) are copied byte-for-byte: 3,060,326 physical lines,
2,795,006 nonblank lines, and 2,522,977 code lines excluding comments.
These counts include the supporting library, not external Mathlib.

The upstream source is `LehengChen/PoincareConjecture` at
`60de1a94ca7038d04ed123b490a3229f8aa5fa75`, with historical Mapher provenance
and subject reorganization recorded in
[complete-import](references/ricci-flow/mapher/complete-import/README.md).
Source licenses and notices are retained under that directory's `source-notices/`.
The separate unhyphenated `frenzymath/PoincareConjecture` snapshot is discussed
in the retained comparison record; it is not this PR's destination repository.

The public module `PoincareLib.Topology.Manifold.Poincare` exports
`PoincareMT.smoothPoincareSkeleton` and
`PoincareMT.topologicalPoincareSkeleton`. The existing `PoincareConjecture`
root now forwards the imported library. Existing blueprint and reference-book
blueprints remain in place; matching their nodes to these declarations remains
review work and their existing readiness labels are not upgraded by this import.

The primary package adopts the imported Lean toolchain and Mathlib pin so the
proof sources retain their verified dependency context. Its previous package
options are scoped to the existing `PoincareConjecture` target. Reference books
are blueprint-only and no longer contain Lean packages.

## Verification boundary

Horizon recorded a successful reduced-library build and recursive endpoint
checks requiring exactly `propext`, `Classical.choice`, and `Quot.sound`.
The [cleanup evidence](references/ricci-flow/mapher/production-cleanup/README.md)
contains commands, source hashes and compressed logs. Historical paths and
Horizon API links in those records refer to the original workspace. These
records do not assert a fresh build of this relocated package.

Before marking the PR ready, build this exact branch and run its endpoint audit:

```sh
cd PoincareConjecture
make check
```

Then execute the repository's manual comparator workflow or the instructions
in [verification](../site/verification.md) on an external verification host with
sufficient disk space and disk-backed `TMPDIR`. No comparator, Nanoda or
environment export was run during initial draft preparation or on run12 workers.
Local host verification of the updated comparator is tracked separately.

Routine CI scans the package but explicitly excludes historical `references/`,
frozen `contracts/`, and `Comparator/Challenge.lean`. The challenge deliberately
contains two admissions and is checked separately from the production Solution.
The source report lists these exclusions and still scans Solution and all
production library sources. It does not certify compilation or proof fidelity.

# Focused comparison with the frenzymath public snapshot

Date: 2026-09-28. Scope: run 12 integration follow-up to operator message
2385 and the public-reference addition reviewed in roadmap PR 879.

The production import remains pinned to
`LehengChen/PoincareConjecture@60de1a94ca7038d04ed123b490a3229f8aa5fa75`.
The additional public reference is
`frenzymath/PoincareConjecture@99148d28f5607a908b90c3aa1908b0c5529df9d4`.
The latter was fetched directly from
`https://github.com/frenzymath/PoincareConjecture.git` into the existing source
Git repository, without creating another checkout or modifying its worktree.
Disk headroom was 50 GiB before the comparison.

## Relationship and limits

The new revision has two commits in its visible history: initial commit
`23b2f1e99` followed by `99148d28f` ("style: remove excess blank lines (#1)").
It is a separately packaged snapshot, not an identified descendant of the
current source pin. Its Lean package prefix is `PoincareConjecture`, replacing
`PoincareMT`; its `NOTICE` records adaptations to paths, namespaces, imports,
interfaces, organization, and comments. This focused comparison does not
assert that the complete source trees are equivalent.

Repository tree objects:

- Current primary source: `8f08c17a1ae9b24903090c8df02a94f7e14fe083`.
- Additional public snapshot: `50db3d818f5c8c44d7943abae5475d2bf92044b7`.

The new `lakefile.toml` retains the existing pinned Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, lean4export
`15f6055e299ad5b89345e533cc2192f4cc00f659`, and Comparator
`3927ad383f208ae977c340a91c48ac9b497d2097` dependencies.
`lean-toolchain` remains `leanprover/lean4:v4.33.1`.
These configuration observations are not execution evidence.

## Integration failures checked

For the following three suffixes, the old path begins with `PoincareMT/` and
the new path begins with `PoincareConjecture/`:

| Source suffix | Result |
| --- | --- |
| `Proofs/M35/Uniqueness/Heat/WeakTimeDerivative.lean` | Same declarations and proof text; no new heartbeat option. |
| `Proofs/M47/TerminalCurvatureNullCoverBound.lean` | Same declarations and proof text; no new synthesis budget. |
| `Proofs/M76/Triangulation/HamiltonIndexOneMeridianBand.lean` | Same declarations and proof text, including its private helpers; no duplicate-helper repair. |

Equality here means byte equality after removing nested Lean block comments
and line comments, replacing `PoincareConjecture` with `PoincareMT`, and
collapsing whitespace. Comment removal respected quoted strings. This is a
source comparison, not a Lean proof or a claim that arbitrary whitespace
rewrites preserve Lean syntax. Direct inspection confirmed namespace/import
renaming and removed comments in these three files.

Exact SHA-256 hashes of the unmodified source blobs:

| File | Primary source | Additional public snapshot |
| --- | --- | --- |
| `WeakTimeDerivative.lean` | `792fb79628b1112be9009e4eecbde4639a8d7cdf13071e877c3afc15d94a8abd` | `6d2a56eb89e3938333c8a58968e845e7a4cdb13dd337f5586581c222ab7baad5` |
| `TerminalCurvatureNullCoverBound.lean` | `8e89c9031faa131723158a2ba8dd52894d84f20463e5aca08fcb0b4bc7d9f558` | `72b5290e516466433048b979e9819ae6d8eec51aa9e2bdcd72adfabd0aaf324f` |
| `HamiltonIndexOneMeridianBand.lean` | `12f1928da3aec44388042469372136c115a5a0d1cde18bff3826fb7cc76dbbda` | `195a0d6c13ba1dfd5d5890c7c6ac5bfc83c6fa1471ce4bc37d87d15007e2e4dc` |

`OriginalDoubleArcTubeBlocks.lean` is absent from both public source trees.
A scoped `git grep` of each revision's `Proofs/M76` tree also found no
`exists_original_signed_tube_blocks` declaration. The failing module is the
existing Horizon consumer at
`PoincareLib/Topology/Manifold/Smoothing/Dehn/DoubleArc/OriginalDoubleArcTubeBlocks.lean`;
this comparison supplies no replacement proof or argument repair for it.

## Consequence

No fix for the four investigated integration failures was available to import
from this revision. The integration owner retains the current production
pin, source mapping, and subject hierarchy, and repairs the evidenced local
compatibility failures with the existing build evidence.

No Lean build, comparator, Nanoda check, or environment export was run for
this comparison. Comparator verification was not performed under the run 12
storage constraint. No source, package configuration, contract, or existing
provenance map was changed by this comparison.

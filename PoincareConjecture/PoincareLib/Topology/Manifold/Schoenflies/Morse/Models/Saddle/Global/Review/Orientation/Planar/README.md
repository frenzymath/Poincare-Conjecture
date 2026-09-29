# Reflected planar transport

This directory constructs the isolated four-model planar proposal from the
original terminal inputs. `Selection.lean` selects a complete baseline family
for the original or reflected input. `Ends`, `Flattening`, `Geometry`, `Sets`,
and `Data` transport its labelled geometric data back. `Transport` and `Family`
transport the smooth supported planar family and its protected square. The
candidate planar leaf applies this constructed family without extra hypotheses.
The accepted `Global/TerminalData.lean`, `Global/Leaves.lean`, and existing cap
proof are unchanged.

The focused check is:

```text
python3 "$HORIZON_BUILD_HELPER" \
  PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Checks --json
```

It passed on 2026-09-24 (4701 jobs). Recursive `#print axioms` audits of the
selection, end transport, reflected geometry/data, family producer, and candidate
planar leaf report only `propext`, `Classical.choice`, and `Quot.sound`.

`Assembly.lean` preserves the exact ball-neighborhood statement but remains
conditional on the separately owned candidate cap leaf, whose recursive audit
still contains `sorryAx`. No accepted consumer has been migrated. The proof and
proposed consumer change are described in the source directory's
`saddle-orientation-migration.md`.

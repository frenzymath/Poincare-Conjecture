# Cleanup source-link review

Result: no graph link repin is required for the 4,823 removed module paths.
No graph changes are proposed.
No API write, source edit, or blueprint edit was performed.

Inputs inspected:

- Current fetched roadmap main `d1fb36a710e780e3868508e0a8e81b0f1fbe8452`.
- `references/ricci-flow/mapher/production-cleanup/removal-manifest.json`, recovery
  commit `a71c2ef35f0ff06f34eb555982c03d3e6d92c624`.
- Live pending PRs 882 (twelve graph nodes) and 883 (objective).
- Current `blueprint-publication` source, inventories and source-link config.

The deterministic `scan-links.mjs` reproduces `link-report.json` when run from
the workspace with the existing fetched roadmap checkout as its first argument.
It reads that checkout and the two PRs,
and writes only into this directory. The report lists exact matching paths,
documents, lines and link targets.

Graph results:

- 186 affected source-link occurrences on main are already commit-pinned;
  preserve each original pin.
- All 34 bare-path occurrences on main belong to historical metadata with
  recorded commit/revision fields or surrounding pinned implementation
  evidence. These are source identifiers, not live branch links.
- PR 882 contains seven affected pinned source-link occurrences; its three
  additional bare occurrences are the display text of those pinned links.
  Preserve the verified import commit in that PR even after pruning.
- PR 883 has no source link to a removed module. No objective amendment is
  needed for link survival.
- No metadata, statement, label, dependency edge or accepted evidence requires
  alteration for this bounded link-maintenance task.

## Blueprint coordinator handoff

There is no unpinned affected blueprint URL. `provenance.json:62` and
`hgraph/config.yaml:17` use the historical source base
`6a6637f3732aa69ca351a3bc31844a626222eddb`; preserve it rather than repinning old
mathematical evidence to the cleanup revision.

`graph-review.json` has four affected historical pinned URLs: the nonseparating
local-region construction (line 108, embedded node document) at `133b8b19...`,
and M37/M41/M42 source URIs at lines 203/213/223, pinned to `11767a3a...`. Its
three `canonical_file` fields (lines 198/208/218) are paired with those URIs and
need no change.

`inventory/dependencies.json` explicitly records its own
`workspace_revision: 6a6637f3732aa69ca351a3bc31844a626222eddb`. Seven dependency
records refer to six removed paths:

| Declaration | File field line |
| --- | --- |
| `PoincareMT.ConnectedNeckCapCover.exists_compatible_local_region_threshold` | 63652 |
| `PoincareMT.DeepHorn.hornSelectionEpsilonThreshold` | 64568 |
| `PoincareMT.DeepHorn.hornSelectionTheoryOfUniformContainedNecks` | 65022 |
| `PoincareMT.DeepHorn.uniformContainedNecks` | 65743 |
| `PoincareMT.NeckCapRegionCompatible.globalConclusion` | 91463 |
| `PoincareMT.NeckOnlyCover.exists_correctedA19Conclusion` | 91768 |
| `PoincareMT.NeckOnlyCover.exists_correctedA20Conclusion` | 92037 |

These are historical source-backed dependency records, not evidence that the
declarations remain in the current endpoint closure. If the coordinator later
updates the blueprint's source baseline or inventory, it must distinguish the
historical accepted route from the new endpoint route. Do not mechanically
change these source pins or remove their narratives during cleanup. Blueprint
ownership remains exclusively with its coordinator.

# Horizon blueprint snapshot

The active blueprint imports all 18 chapters from `blueprint-publication/drafts/`
in Horizon workspace `poincare-conjecture/workspace-poincare-conjecture`, commit
`fbdf7e1493ed0566f4e74a287819fb3b0f765284`. The mathematical chapter text,
bibliography and macros are preserved; [manifest.json](manifest.json) records
their upstream hashes and the chapter sequence. One metadata correction turns
`\uses{ch:foundations-v4}` into a normal chapter cross-reference: chapters are
not statement nodes in hgraph. One trailing space in global-surgery is removed.
The checker reverses these recorded edits before comparing upstream digests.
The integration preface is authored here.

At this snapshot, 17 chapters were accepted by Horizon's main-agent review;
`smoothing` and whole-book publication acceptance remain pending. Importing this
snapshot into a draft PR does not upgrade those reviews. The retained
[status report](inventory/v4-publication-status.json),
[chapter reviews](inventory/reviews/), and
[outstanding issues](reconstruction/outstanding-issues-v4.md) describe that boundary.
The report's `integrated_source_checked: false` describes the upstream snapshot,
whose own content entry point still contained the old six chapters. This PR's
entry point integrates the 18 drafts, with consistency checks performed locally.
The upstream status checkpoint also predates the final global-surgery correction;
that chapter's newer acceptance record matches the imported text. The local
checker validates all 17 accepted chapter hashes against their individual reviews.

The active `../../blueprint/` directory contains only the current TeX chapters,
entry point, macros and bibliography. The former six-chapter blueprint and its
obsolete reviews were removed from the working tree; they remain in Git history
at `e84e9c3f`. Map generation lives in the repository's `scripts/` and `site/`
directories. This provenance directory is not part of the document sources.

The source report records 237 Lean names, including three historical adapters
removed during production cleanup. Their treatment is explicit in
[v4-source-resolutions.json](inventory/v4-source-resolutions.json).
These adapters are not restored to the proof library or counted as current
verified declarations. Source report URLs beginning `/api/v2/forge/` are original
Horizon provenance, not public website links. Active site links are generated
from the current local Lean sources.

Only `PoincareConjecture` has Lean source discovery.
All 16 reference projects use `lean: []`; their source views, formalization
controls and percentages are hidden. All projects set `site.progress: false`.
The main blueprint's Source links view records annotation coverage separately
from the revision-pinned build and Comparator evidence in its Verification tab.

Run the integration checks and build the site from the repository root:

```sh
python scripts/check_blueprint_import.py
python scripts/build_site.py --out _site
```

Neither command compiles Lean or reruns Comparator. The completed proof's
revision-pinned verification evidence is retained separately under
`PoincareConjecture/references/ricci-flow/mapher/integration-verification/`.
See [VALIDATION.md](VALIDATION.md) for the integration and browser checks.

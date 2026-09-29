# Integration validation

Validated on 2026-09-29 against the imported Horizon snapshot
`fbdf7e1493ed0566f4e74a287819fb3b0f765284`.

- All 29 Python tooling tests pass, including chapter/source linkage, review
  digests, provenance records, and map generation from a staged project root.
- The integration checker resolves 18 chapters, 179 statement nodes, and 234
  current Lean names. It reports no unresolved chapter references or citations.
  The three historical Lean names are explicitly excluded from current source
  checks, as recorded in the upstream cleanup resolutions.
- All 17 accepted chapters match their individual review digests after reversing
  the recorded metadata and trailing-space corrections. Smoothing and whole-book publication
  acceptance remain pending. The older global-surgery checkpoint hash is
  superseded by its matching individual acceptance record.
- The full static website build succeeds. The main project produces 179
  blueprint nodes; every reference project produces zero Lean declarations.
- Playwright checks at 1440 x 1000 and 390 x 1000 load all 18 main chapters
  without runtime or KaTeX errors. All 16 reference projects hide formalization
  percentages, Lean controls, status squares, badges, and chapter-progress
  summaries. Their chapter disclosures retain an accessible label and navigation.
  The main project retains its progress display and the regenerated map loads.
- Hgraph reports 95 linked statement nodes and 84 without current attached Lean
  targets (53% linkage). This is not an estimate of proof completion or a new
  verification result. The three historical adapters are among the unlinked
  nodes; many other nodes are explanatory statements without Lean annotations.

The full-tree source parser also reports existing duplicate Lean names and
unattached helper declarations. Some reference blueprints retain unresolved
background dependency annotations. The new main blueprint has no unresolved
statement dependency after its recorded chapter-reference correction.

No Lean source or proof was changed. No Lean build, endpoint audit or Comparator
run was performed for this blueprint and website integration. The earlier
revision-pinned proof verification evidence remains separate.

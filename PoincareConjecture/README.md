# Poincare-Conjecture

This is the repository's complete Lean 4 formalization of the Poincare conjecture.
Its blueprint follows
the dependency architecture of the Poincare conjecture rather than reproducing
the chapter order of a particular source.

The projects under `../references/` collect book and article blueprints with
their mathematical dependency graphs. They provide blueprint-only references;
completing those books is not an objective of this formalization.

## Status

The [subject-organized proof library](IMPORT.md) has passed a full Lean build
and endpoint axiom audits at `516badd1`. Comparator accepted both public targets
at `1876d7dc`, checked by Nanoda and Lean's default kernel. The recursive axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
See the [verification evidence](../archive/PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md)
for the exact revisions, verifier configuration, and logs, and the
[FrenzyMath announcement](https://frenzymath.com/news/poincare-formalization/)
for the project's background.

The [main blueprint](blueprint/content.tex) explains the implemented proof in
18 chapters, from Ricci flow and surgery to finite extinction, reconstruction,
and compatible smoothing. Its named mathematical nodes link to current Lean
declarations and record their prerequisites. Run
`python scripts/check_blueprint_import.py` from the repository root to check
these links, citations, and graph connections.

The [snapshot record](../archive/PoincareConjecture/provenance/blueprint-import/README.md)
preserves the original Horizon import at `fbdf7e1493ed`, including its hashes
and review decisions. Those historical reviews and the recorded kernel checks
are distinct from validation of the revised exposition. All 16 reference
projects remain blueprint-only.

## Build

```bash
lake exe cache get
lake build
```

Graph synchronization and local website preview are documented in the root
`CONTRIBUTING.md`.

## Blueprint map

The project-local `Blueprint map` tab is generated from the live hgraph nodes
and `uses` edges during the site build:

```bash
python3 scripts/build_site.py --out _site
```

Run this command from the repository root. The map is generated in temporary
storage from the same current chapters as the built-in dependency graph.

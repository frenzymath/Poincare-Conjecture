# Frozen milestone contracts

This directory preserves the exact reviewed M05, M06, M07, and M12 Lean source from
Mapher06/Poincare-MorganTian at commit
`b2c3c64781fee22edfd683a224d4f8d280e2e9ce`.

- `definitions/` contains the definitions used to state each result.
- `statements/` contains the associated conclusion structures.
- `milestones/` contains the `by sorry` theorem entry for each milestone.
- `manifest.json` records the original paths and SHA-256 hashes.

These snapshots are excluded from the package build because their imports refer
to the source repository's module hierarchy. They are immutable targets, not a
template for `PoincareLib`. Run `python3 scripts/check_frozen_contracts.py` to
verify them. Proof work belongs in semantic library modules; a contract change
requires a separate reviewed update of both the files and the manifest.

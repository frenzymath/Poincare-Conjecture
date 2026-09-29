# Historical records

This directory retains the import, attribution, and verification records for
the published Poincare proof. The active Lean library and blueprint are in
[`PoincareConjecture/`](../PoincareConjecture/); book and article blueprints are
in [`references/`](../references/).

- [Verification runs](PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md)
  record the build and independent-kernel checks at their exact revisions.
- [Source attribution](PoincareConjecture/provenance/2026-09-29/README.md)
  retains reuse decisions, copyright notices, and verbatim source licenses.
- [Blueprint import](PoincareConjecture/provenance/blueprint-import/README.md)
  records the original extracted draft and its reviews. The live blueprint has
  since evolved; snapshot hashes describe that import, not its current text.
- [Frozen contracts](PoincareConjecture/contracts/README.md) preserve the
  historical milestone interfaces. `make -C PoincareConjecture contracts`
  checks their recorded hashes.

Archived scripts, source snapshots, and logs describe the original workspace
and are not production modules. Their historical paths and commands are kept
as evidence, so they should not be run as current development instructions.
The original relative layout is retained to preserve links within the records.

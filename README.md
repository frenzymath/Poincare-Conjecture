<h1 align="center">Poincare Conjecture</h1>
<p align="center">
  Frenzymath - PKU@AI4Math
</p>

<div align="center">

[![Website: Live](https://img.shields.io/badge/Website-Live-0969da?style=flat-square)](https://frenzymath.github.io/Poincare-Conjecture/)
[![Project board: Worklist](https://img.shields.io/badge/Project-Worklist-2da44e?style=flat-square)](https://github.com/orgs/frenzymath/projects/1)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow?style=flat-square)](LICENSE)
[![Lean: v4.33.1](https://img.shields.io/badge/Lean-v4.33.1-6f42c1?style=flat-square)](https://github.com/leanprover/lean4/tree/v4.33.1)
[![Mathlib: 0df444a](https://img.shields.io/badge/Mathlib-0df444a-0969da?style=flat-square)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)
</div>

<p align="center">
  A custom Lean 4 formalization of the Poincare conjecture,<br>
  with a custom proof blueprint and annotated blueprints of mathematical references.
</p>

> [!IMPORTANT]
> This is an active, incomplete formalization. The website distinguishes verified Lean declarations from statements still in progress.

This draft adds the [subject-organized Poincare library](PoincareConjecture/IMPORT.md).
Its historical Horizon build and endpoint audits passed; a fresh build and
comparator verification of this repository revision remain pending. Existing
blueprint readiness labels have not been upgraded by the import.

## The conjecture

> [!NOTE]
> **Poincare conjecture.** Let $M$ be a closed, connected topological $3$-manifold. If $\pi_1(M)=0$, then $M \cong S^3$.

The primary [`PoincareConjecture`](PoincareConjecture/) project is organized by
the mathematical dependency structure of the proof, independently of any one
book's chapter order. Blueprints following individual books and articles are
collected under [`references/`](references/) as blueprint-only reading material.

## Repository structure

```text
PoincareConjecture/     primary custom blueprint and Lean library
references/            book and article blueprints, without Lean packages
config.yaml            hgraph workspace and website manifest
site/                  authored website content, graph settings, reviews and assets
```

## Project and references

The [primary project](https://frenzymath.github.io/Poincare-Conjecture/#/PoincareConjecture)
contains the proof library and blueprint. The [reference blueprints](references/)
cover Ricci flow, three-manifolds, Riemannian geometry, algebraic topology, and
PDEs. They provide mathematical background and are not separate formalization
projects.

## Contributing

Contributions are welcome through [issues](https://github.com/frenzymath/Poincare-Conjecture/issues) and focused [pull requests](https://github.com/frenzymath/Poincare-Conjecture/pulls). Build instructions, local website preview, and the review/comment workflow are documented in [CONTRIBUTING.md](CONTRIBUTING.md).

Automatic CI reports Lean source statistics and admissions without compiling the
proof. Full builds and comparator verification are explicit workflows; their
evidence and trust assumptions are described in [Verification](site/verification.md).
Generated graph directories and website output are never committed.

Active work is coordinated on the [Poincare Conjecture Formalization Library project board](https://github.com/orgs/frenzymath/projects/1).

## Provenance

See [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture)
for the companion proof repository and comparator statement. This repository
organizes the proof library by mathematical subject and adds the blueprint.
Exact import revisions, adaptations, and retained source notices are recorded
in [the import provenance](PoincareConjecture/IMPORT.md).

Licensed under [Apache 2.0](LICENSE).

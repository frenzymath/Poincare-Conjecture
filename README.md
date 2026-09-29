<h1 align="center">Poincare Conjecture</h1>
<p align="center">
  Frenzymath - PKU@AI4Math
</p>

<div align="center">

[![Website: Live](https://img.shields.io/badge/Website-Live-0969da?style=flat-square)](https://frenzymath.github.io/Poincare-Conjecture/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow?style=flat-square)](LICENSE)
[![Lean: v4.33.1](https://img.shields.io/badge/Lean-v4.33.1-6f42c1?style=flat-square)](https://github.com/leanprover/lean4/tree/v4.33.1)
[![Mathlib: 0df444a](https://img.shields.io/badge/Mathlib-0df444a-0969da?style=flat-square)](https://github.com/leanprover-community/mathlib4/tree/0df444a360eaa60ab8c11dca51a86af692955474)
</div>

<p align="center">
  A complete Lean 4 formalization of the Poincare conjecture,<br>
  with a proof blueprint and blueprint-only mathematical references.
</p>

The formalization has passed a full Lean build and Comparator verification.
Comparator accepted both public targets at commit `1876d7dc`, with checks by
Nanoda and Lean's default kernel. See the
[verification evidence](PoincareConjecture/references/ricci-flow/mapher/integration-verification/README.md)
for the exact revisions, verifier configuration, and logs.

Read the [FrenzyMath announcement](https://frenzymath.com/news/poincare-formalization/)
for the project's background and results.

## The conjecture

> [!NOTE]
> **Poincare conjecture.** Let $M$ be a closed, connected topological $3$-manifold. If $\pi_1(M)=0$, then $M \cong S^3$.

The primary [`PoincareConjecture`](PoincareConjecture/) project is organized by
the mathematical dependency structure of the proof, independently of any one
book's chapter order. Its [18-chapter Horizon blueprint](PoincareConjecture/blueprint/content.tex)
explains the implemented proof; the snapshot retains its outstanding editorial
review status. Blueprints following individual books and articles are
collected under [`references/`](references/) as blueprint-only reading material.

## Repository structure

```text
PoincareConjecture/     primary custom blueprint and Lean library
references/            book and article blueprints, without Lean packages
config.yaml            hgraph workspace and website manifest
site/                  authored website content, graph settings, reviews and assets
```

## Discussion

[Issues](https://github.com/frenzymath/Poincare-Conjecture/issues) |
[Pull requests](https://github.com/frenzymath/Poincare-Conjecture/pulls) |
[Lean Zulip](https://leanprover.zulipchat.com/)

Build and website instructions are in [CONTRIBUTING.md](CONTRIBUTING.md).

## Provenance

See [frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture)
for the companion proof repository and comparator statement. This repository
organizes the proof library by mathematical subject and adds the blueprint.
Exact import revisions, adaptations, and retained source notices are recorded
in [the import provenance](PoincareConjecture/IMPORT.md) and
[MODIFICATIONS.md](PoincareConjecture/MODIFICATIONS.md).
The [whole-tree external-source audit](PoincareConjecture/provenance/2026-09-29/README.md)
records reviewed similarity matches, restored notices, and upstream licenses.

Licensed under [Apache 2.0](LICENSE).

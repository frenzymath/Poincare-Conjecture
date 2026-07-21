<h1 align="center">Poincare Conjecture</h1>
<p align="center">
  Frenzymath - PKU@AI4Math
</p>

<div align="center">

[![Website: Live](https://img.shields.io/badge/Website-Live-0969da?style=flat-square)](https://frenzymath.github.io/Poincare-Conjecture/)
[![Project board: Worklist](https://img.shields.io/badge/Project-Worklist-2da44e?style=flat-square)](https://github.com/orgs/frenzymath/projects/1)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow?style=flat-square)](LICENSE)
[![Lean: v4.30.0](https://img.shields.io/badge/Lean-v4.30.0-6f42c1?style=flat-square)](https://github.com/leanprover/lean4/tree/v4.30.0)
[![Mathlib: c5ea003](https://img.shields.io/badge/Mathlib-c5ea003-0969da?style=flat-square)](https://github.com/leanprover-community/mathlib4/tree/c5ea00351c28e24afc9f0f84379aa41082b1188f)
</div>

<p align="center">
  A custom Lean 4 formalization of the Poincare conjecture,<br>
  supported by source-faithful formalizations of its mathematical references.
</p>

> [!IMPORTANT]
> This is an active, incomplete formalization. The website distinguishes verified Lean declarations from statements still in progress.

## The conjecture

> [!NOTE]
> **Poincare conjecture.** Let $M$ be a closed, connected topological $3$-manifold. If $\pi_1(M)=0$, then $M \cong S^3$.

The primary [`PoincareConjecture`](PoincareConjecture/) project is organized by
the mathematical dependency structure of the proof, independently of any one
book's chapter order. Formalizations following individual books and articles
are maintained as supporting source projects under
[`formalized-sources/`](formalized-sources/).

## Repository structure

```text
PoincareConjecture/    primary custom blueprint and Lean library
formalized-sources/    book- and article-based reference projects
shared/                book-independent Lean infrastructure
config.yaml            hgraph workspace and website manifest
site/                  authored website content and assets
```

## Formalization projects

| Project | Role |
|---|---|
| [PoincareConjecture](https://frenzymath.github.io/Poincare-Conjecture/#/PoincareConjecture) | Primary custom proof architecture |
| [Morgan-Tian](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/MorganTian) | Ricci flow and the Poincare conjecture |
| [Kleiner-Lott](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/KleinerLott) | Notes on Perelman's papers |
| [Cao-Zhu](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/CaoZhu) | Hamilton-Perelman proof and geometrization |
| [Chow et al.](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/ChowEtAl) | Ricci flow techniques and applications, Parts II-IV |
| [Chow-Knopf](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/ChowKnopf) | Introduction to Ricci flow |
| [Topping](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/Topping) | Lectures on Ricci flow |
| [do Carmo](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/DoCarmo) | Riemannian geometry |
| [Petersen](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/Petersen) | Riemannian geometry |
| [Lee, Riemannian Manifolds](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/LeeRiemannian) | Riemannian geometry |
| [Lee, Smooth Manifolds](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/LeeSmooth) | Smooth-manifold foundations |
| [Cheeger-Gromov-Taylor](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/CheegerGromovTaylor) | Kernel estimates on complete Riemannian manifolds |
| [Hatcher](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/Hatcher) | Algebraic topology |
| [Evans](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/Evans) | Partial differential equations |
| [Gilbarg-Trudinger](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/GilbargTrudinger) | Second-order elliptic partial differential equations |
| [Han-Lin](https://frenzymath.github.io/Poincare-Conjecture/#/formalized-sources/HanLinLectureNotes) | Elliptic differential equations |

## Contributing

Contributions are welcome through [issues](https://github.com/frenzymath/Poincare-Conjecture/issues) and focused [pull requests](https://github.com/frenzymath/Poincare-Conjecture/pulls). Build instructions, local website preview, and the hgraph review/comment workflow are documented in [CONTRIBUTING.md](CONTRIBUTING.md).

Active work is coordinated on the [Poincare Conjecture Formalization Library project board](https://github.com/orgs/frenzymath/projects/1).

## Provenance

This is an independent formalization. A limited part of the Riemannian
geometry infrastructure was originally derived from
[OpenGA](https://github.com/MathNetwork/OpenGA) and has since been substantially
extended and rewritten. The project is built on
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/c5ea00351c28e24afc9f0f84379aa41082b1188f).

Licensed under [Apache 2.0](LICENSE).

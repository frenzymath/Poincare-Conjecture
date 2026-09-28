<h1 align="center">Poincare Conjecture</h1>
<p align="center">
  Frenzymath - PKU@AI4Math
</p>

<div align="center">

[![Website: Live](https://img.shields.io/badge/Website-Live-0969da?style=flat-square)](https://frenzymath.github.io/Poincare-Conjecture/)
[![Project board: Worklist](https://img.shields.io/badge/Project-Worklist-2da44e?style=flat-square)](https://github.com/orgs/frenzymath/projects/1)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache%202.0-yellow?style=flat-square)](LICENSE)
[![Lean: v4.32.1](https://img.shields.io/badge/Lean-v4.32.1-6f42c1?style=flat-square)](https://github.com/leanprover/lean4/tree/v4.32.1)
[![Mathlib: 520045a](https://img.shields.io/badge/Mathlib-520045a-0969da?style=flat-square)](https://github.com/leanprover-community/mathlib4/tree/520045ab14e26149ee970e2e617ca04b09bde5d6)
</div>

<p align="center">
  A custom Lean 4 formalization of the Poincare conjecture,<br>
  with a custom proof blueprint and annotated blueprints of mathematical references.
</p>

> [!IMPORTANT]
> This is an active, incomplete formalization. The website distinguishes verified Lean declarations from statements still in progress.

## The conjecture

> [!NOTE]
> **Poincare conjecture.** Let $M$ be a closed, connected topological $3$-manifold. If $\pi_1(M)=0$, then $M \cong S^3$.

The primary [`PoincareConjecture`](PoincareConjecture/) project is organized by
the mathematical dependency structure of the proof, independently of any one
book's chapter order. Blueprints following individual books and articles are
collected under [`references/`](references/), together with their earlier Lean
developments. These references are not separate formalization objectives for
the primary proof.

## Repository structure

```text
PoincareConjecture/     primary custom blueprint and Lean library
references/            book and article blueprints with retained Lean developments
references/shared/     shared Lean infrastructure used by the reference packages
config.yaml            hgraph workspace and website manifest
site/                  authored website content, graph settings, reviews and assets
```

## Primary project and references

| Project | Role |
|---|---|
| [PoincareConjecture](https://frenzymath.github.io/Poincare-Conjecture/#/PoincareConjecture) | Primary custom proof architecture |
| [Morgan-Tian](https://frenzymath.github.io/Poincare-Conjecture/#/references/MorganTian) | Ricci flow and the Poincare conjecture |
| [Kleiner-Lott](https://frenzymath.github.io/Poincare-Conjecture/#/references/KleinerLott) | Notes on Perelman's papers |
| [Cao-Zhu](https://frenzymath.github.io/Poincare-Conjecture/#/references/CaoZhu) | Hamilton-Perelman proof and geometrization |
| [Chow et al.](https://frenzymath.github.io/Poincare-Conjecture/#/references/ChowEtAl) | Ricci flow techniques and applications, Parts II-IV |
| [Chow-Knopf](https://frenzymath.github.io/Poincare-Conjecture/#/references/ChowKnopf) | Introduction to Ricci flow |
| [Topping](https://frenzymath.github.io/Poincare-Conjecture/#/references/Topping) | Lectures on Ricci flow |
| [do Carmo](https://frenzymath.github.io/Poincare-Conjecture/#/references/DoCarmo) | Riemannian geometry |
| [Petersen](https://frenzymath.github.io/Poincare-Conjecture/#/references/Petersen) | Riemannian geometry |
| [Lee, Riemannian Manifolds](https://frenzymath.github.io/Poincare-Conjecture/#/references/LeeRiemannian) | Riemannian geometry |
| [Lee, Smooth Manifolds](https://frenzymath.github.io/Poincare-Conjecture/#/references/LeeSmooth) | Smooth-manifold foundations |
| [Cheeger-Gromov-Taylor](https://frenzymath.github.io/Poincare-Conjecture/#/references/CheegerGromovTaylor) | Kernel estimates on complete Riemannian manifolds |
| [Hatcher](https://frenzymath.github.io/Poincare-Conjecture/#/references/Hatcher) | Algebraic topology |
| [Thurston](https://frenzymath.github.io/Poincare-Conjecture/#/references/Thurston) | Three-manifold topology and hyperbolic geometry |
| [Evans](https://frenzymath.github.io/Poincare-Conjecture/#/references/Evans) | Partial differential equations |
| [Gilbarg-Trudinger](https://frenzymath.github.io/Poincare-Conjecture/#/references/GilbargTrudinger) | Second-order elliptic partial differential equations |
| [Han-Lin](https://frenzymath.github.io/Poincare-Conjecture/#/references/HanLinLectureNotes) | Elliptic differential equations |

## Current review milestones

- **Hopf-Rinow (do Carmo, Chapter 7, Section 2).** The path-regularity gap raised
  in [issue #6](https://github.com/frenzymath/Poincare-Conjecture/issues/6) is
  closed: `piecewiseRiemannianEDist_eq_riemannianEDist` identifies do Carmo's
  finite piecewise-smooth infimum with Mathlib's `riemannianEDist`.
- **Cartan-Hadamard (do Carmo, Chapter 7, Section 3).** The theorem is fully
  formalized without project axioms or `sorry`. The construction
  `hadamardDiffeomorphOfNonpos_complete` is a global smooth diffeomorphism and
  its underlying map is definitionally the exponential map, so mathematical
  and Lean review can start.
- **Cross-reference status.** Cartan-Hadamard is also complete in the
  Lee-Riemannian development. Petersen Section 6.2 remains open, which is why
  the workspace-wide milestone remains active.

## Contributing

Contributions are welcome through [issues](https://github.com/frenzymath/Poincare-Conjecture/issues) and focused [pull requests](https://github.com/frenzymath/Poincare-Conjecture/pulls). Build instructions, local website preview, and the review/comment workflow are documented in [CONTRIBUTING.md](CONTRIBUTING.md).

Automatic CI reports Lean source statistics and admissions without compiling the
proof. Full builds and comparator verification are explicit workflows; their
evidence and trust assumptions are described in [Verification](site/verification.md).
Generated graph directories and website output are never committed.

Active work is coordinated on the [Poincare Conjecture Formalization Library project board](https://github.com/orgs/frenzymath/projects/1).

## Provenance

This is an independent formalization. A limited part of the Riemannian
geometry infrastructure was originally derived from
[OpenGA](https://github.com/MathNetwork/OpenGA) and has since been substantially
extended and rewritten. The project is built on
[Mathlib](https://github.com/leanprover-community/mathlib4/tree/520045ab14e26149ee970e2e617ca04b09bde5d6).

Licensed under [Apache 2.0](LICENSE).

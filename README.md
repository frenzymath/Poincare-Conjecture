<h1 align="center">Poincaré Conjecture</h1>
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
  A Lean 4 formalization of the Poincaré conjecture,<br>
  following Morgan–Tian and built on a shared foundation in Riemannian geometry.
</p>

<p align="center">
  <strong><a href="https://frenzymath.github.io/Poincare-Conjecture/">Explore the formalization on the website →</a></strong>
</p>

> [!IMPORTANT]
> This is an active, incomplete formalization. The website distinguishes verified Lean declarations from statements still in progress or awaiting formalization.

> [!WARNING]
> **Beta version.** This repository is public for development and transparency, but its contents are preliminary and do not yet constitute an official release.

## The conjecture

> [!NOTE]
> **Poincaré conjecture.** Let $M$ be a closed, connected topological $3$-manifold. If $\pi_1(M)=0$, then $M \cong S^3$.

Henri Poincaré posed the problem in 1904 while laying the foundations of three-dimensional topology. In 1982, Richard Hamilton introduced Ricci flow and proposed using it to deform a manifold toward a geometrically understandable form. Grigori Perelman's 2002–2003 preprints supplied the decisive ideas, entropy, noncollapsing, and control of singularities, needed to complete Hamilton's program. The detailed account by Morgan and Tian is the principal proof track followed here.

## Projects

| Track | Purpose |
|---|---|
| [Morgan–Tian](https://frenzymath.github.io/Poincare-Conjecture/MorganTian/dashboard.html) | Ricci flow and the Poincaré conjecture |
| [do Carmo](https://frenzymath.github.io/Poincare-Conjecture/DoCarmo/dashboard.html) | Shared Riemannian geometry foundation |
| [Petersen](https://frenzymath.github.io/Poincare-Conjecture/Petersen/dashboard.html) | Riemannian geometry |
| [Lee — Riemannian Manifolds](https://frenzymath.github.io/Poincare-Conjecture/LeeRiemannian/dashboard.html) | Complementary Riemannian geometry |
| [Lee — Smooth Manifolds](https://frenzymath.github.io/Poincare-Conjecture/LeeSmooth/dashboard.html) | Prerequisite smooth-manifolds volume (GTM 218); imported and audited, substantially incomplete |
| [Hatcher](https://frenzymath.github.io/Poincare-Conjecture/Hatcher/dashboard.html) | Algebraic topology |
| [Evans](https://frenzymath.github.io/Poincare-Conjecture/Evans/dashboard.html) | Partial differential equations |

The principal proof track follows J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* ([arXiv:math/0607607](https://arxiv.org/abs/math/0607607)). The supporting tracks formalize the geometry, topology, and analysis needed along the way.

## Preview locally

The project website is generated with [hgraph](https://github.com/AxelDlv00/hgraph). After [installing hgraph](https://github.com/AxelDlv00/hgraph#install), rebuild and serve the site from the repository root:

```bash
bash scripts/build-site.sh
python3 -m http.server 8000 --directory docs --bind 127.0.0.1
```

Open <http://127.0.0.1:8000/> to explore the blueprints, dependency graphs, and formalization progress locally before submitting a pull request.

## Contributing

Contributions are welcome through [issues](https://github.com/frenzymath/Poincare-Conjecture/issues) and focused [pull requests](https://github.com/frenzymath/Poincare-Conjecture/pulls). See the [contribution guide](CONTRIBUTING.md) to get started.

Work in progress is coordinated on the [**Poincaré Conjecture Formalization Library** project board](https://github.com/orgs/frenzymath/projects/1). The two views are complementary: the [website](https://frenzymath.github.io/Poincare-Conjecture/) is the map of *all* the mathematics, while the board is the live worklist of what contributors are actively claiming, grouped by theorem milestone (e.g. Bonnet–Myers, Hopf–Rinow, Cartan–Hadamard). To claim a task, open a sub-issue for the specific lemma or definition, assign yourself, add the relevant `book:` label(s), and move the card to *In Progress*.

Licensed under [Apache 2.0](LICENSE).

## Provenance

This is an independent formalization of the Poincaré conjecture, following Morgan and Tian's *Ricci Flow and the Poincaré Conjecture*. The Lean development uses `DoCarmoLib` for foundational Riemannian geometry. A limited part of that infrastructure was originally derived from [OpenGA](https://github.com/MathNetwork/OpenGA) and has since been substantially extended and rewritten.

The project is built on [Mathlib (c5ea003)](https://github.com/leanprover-community/mathlib4/tree/c5ea00351c28e24afc9f0f84379aa41082b1188f).

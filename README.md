<h1 align="center">Poincaré Conjecture</h1>

[![Project site](https://img.shields.io/badge/website-project%20site-0969da?style=flat-square&logo=githubpages&logoColor=white)](https://frenzymath.github.io/Poincare-Conjecture/)
[![License: Apache 2.0](https://img.shields.io/badge/license-Apache%202.0-blue?style=flat-square)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4-6f42c1?style=flat-square)](https://lean-lang.org/)
[![Powered by mathlib](https://img.shields.io/badge/powered%20by-mathlib-d73a49?style=flat-square)](https://github.com/leanprover-community/mathlib4)

<p align="center">
  A Lean 4 formalization of the Poincaré conjecture,<br>
  following Morgan–Tian and built on a shared foundation in Riemannian geometry.
</p>

<p align="center">
  <strong><a href="https://frenzymath.github.io/Poincare-Conjecture/">Explore the formalization on the website →</a></strong>
</p>

> [!IMPORTANT]
> This is an active, incomplete formalization. The website distinguishes verified Lean declarations from statements still in progress or awaiting formalization.

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
| [Lee](https://frenzymath.github.io/Poincare-Conjecture/Lee/dashboard.html) | Complementary Riemannian geometry |
| [Hatcher](https://frenzymath.github.io/Poincare-Conjecture/Hatcher/dashboard.html) | Algebraic topology |
| [Evans](https://frenzymath.github.io/Poincare-Conjecture/Evans/dashboard.html) | Partial differential equations |

The principal proof track follows J. W. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture* ([arXiv:math/0607607](https://arxiv.org/abs/math/0607607)). The supporting tracks formalize the geometry, topology, and analysis needed along the way.

## Contributing

Contributions are welcome through [issues](https://github.com/frenzymath/Poincare-Conjecture/issues) and focused [pull requests](https://github.com/frenzymath/Poincare-Conjecture/pulls). See the [contribution guide](CONTRIBUTING.md) to get started.

Licensed under [Apache 2.0](LICENSE).

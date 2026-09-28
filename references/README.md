# References

These blueprints follow individual books or articles and serve as mathematical
references for the custom proof in `PoincareConjecture/`. Completing every book
is not an objective of the primary formalization.

Earlier Lean developments, Lake packages, declaration links, and reviews are
retained for now. Their common Lean infrastructure lives in `shared/` here.
The website still exposes their existing Lean status during this transition;
it should not be read as a completion measure for the primary proof.

After importing the primary proof and checking its dependency closure, the
reference packages can become blueprint-only projects. That later step should
remove unused Lean packages and build targets, adjust declaration links and
status displays, and exclude references from formalization progress totals.

Subject grouping is maintained in the root `config.yaml` manifest rather than
encoded in this directory tree. Keeping every source project at the same depth
also keeps cross-project Lake paths stable. Package and Lean module names are
unchanged by the directory move.

| Project | Source area |
|---|---|
| `MorganTian` | Ricci flow and the Poincare conjecture |
| `KleinerLott` | Perelman's papers and geometrization |
| `CaoZhu` | Hamilton-Perelman proof and geometrization |
| `ChowEtAl` | Ricci flow techniques and applications, Parts II-IV |
| `ChowKnopf` | Introduction to Ricci flow |
| `Topping` | Lectures on Ricci flow |
| `DoCarmo` | Riemannian geometry |
| `Petersen` | Riemannian geometry |
| `LeeRiemannian` | Riemannian geometry |
| `LeeSmooth` | Smooth manifolds |
| `CheegerGromovTaylor` | Kernel estimates on complete Riemannian manifolds |
| `Hatcher` | Algebraic topology |
| `Thurston` | Three-manifold topology and hyperbolic geometry |
| `Evans` | Partial differential equations |
| `GilbargTrudinger` | Second-order elliptic partial differential equations |
| `HanLinLectureNotes` | Elliptic differential equations |

Build and hgraph instructions are centralized in the repository root
`CONTRIBUTING.md`.

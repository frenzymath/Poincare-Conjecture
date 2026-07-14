# Poincaré Conjecture

A Lean 4 formalization effort around the **Poincaré Conjecture**: a machine-checked
blueprint for the proof (after Morgan–Tian), built on a shared, formally verified
foundation of Riemannian geometry.

The repository is a small monorepo of **symmetrically structured projects** on top of
one **shared foundation library**, so there is a single source of truth for the
geometry and no divergent copies to keep in sync.

## Architecture

```
DoCarmo/  ──(OpenGALib)──►  Petersen/      require OpenGALib from "../DoCarmo"
                      └──►  MorganTian/    require OpenGALib from "../DoCarmo"
```

- **`DoCarmo/`** — the shared **foundation**. Its `OpenGALib` is the machine-verified
  Riemannian-geometry library (the *Riemannian Geometry Challenge*, developed following
  do Carmo). Everything else depends on it. Upstream: <https://github.com/MathNetwork/OpenGA>.
- **`Petersen/`**, **`MorganTian/`** — **consumer** blueprint projects, each with its own
  library that depends on the single shared `OpenGALib` via a local-path dependency.

### Formalized projects (blueprint + Lean)

| Project | Role | Source | Library |
|---|---|---|---|
| [`DoCarmo/`](DoCarmo) | foundation | M. P. do Carmo, *Riemannian Geometry* | `OpenGALib` (shared) |
| [`Petersen/`](Petersen) | consumer | P. Petersen, *Riemannian Geometry* (GTM 171) | `PetersenLib` → `OpenGALib` |
| [`MorganTian/`](MorganTian) | consumer | Morgan–Tian, *Ricci Flow & the Poincaré Conjecture* ([arXiv:math/0607607](https://arxiv.org/abs/math/0607607)) | `MorganTianLib` → `OpenGALib` |

### Blueprint-only projects (formalization pending)

Machine-checked blueprints for the remaining background, awaiting Lean formalization.

| Project | Topic | Source |
|---|---|---|
| [`Lee/`](Lee) | Riemannian geometry | J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed. (GTM 176) |
| [`Hatcher/`](Hatcher) | Algebraic topology | A. Hatcher, *Algebraic Topology* |
| [`Evans/`](Evans) | Analysis — PDEs & 2nd-order elliptic theory | L. C. Evans, *Partial Differential Equations* (GSM 19) |

## Project layout

Every project directory has the same shape:

```
<Project>/
├── blueprint/src/          LaTeX blueprint (content.tex, chapters/ChNN_*.tex, refs.bib)
├── <Lib>/                  Lean 4 source (library root)
├── <Lib>.lean              library root module
├── lakefile.lean           Lake build config
├── lake-manifest.json
├── lean-toolchain          pinned Lean version (identical across projects)
├── hgraph/config.yaml      blueprint ↔ Lean dependency-graph config
└── README.md
```

The blueprint's `\lean{...}` anchors name the Lean declarations that discharge each
statement, keeping the informal proof and the formal code in lock-step.

Blueprint-only projects have just `blueprint/src/`, `hgraph/config.yaml`, and `README.md`
(no Lean library or lakefile yet); the rest lands when their formalization begins.

## Building

The foundation builds first; consumers pick it up via the local path dependency.

```bash
cd DoCarmo && lake exe cache get && lake build     # shared foundation
cd ../MorganTian && lake build                     # consumer (finds OpenGALib at ../DoCarmo)
cd ../Petersen   && lake build
```

All projects pin the same Lean toolchain and mathlib revision.

## Contributing

Contributions go through **pull requests** — `main` is protected and takes no direct
pushes. Open an issue to discuss scope, then submit a focused PR against the relevant
project. CI runs `lake build`; a PR must be green before review. Review covers two
dimensions, tracked per PR:

- **Mathematics** — correctness and fidelity of the blueprint statement to its source.
- **Lean** — validity of the formal code discharging it.

After cloning, enable the repository's git hooks:

```bash
git config core.hooksPath .githooks
```

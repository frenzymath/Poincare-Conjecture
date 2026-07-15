# Contributing

Thank you for helping formalize the Poincaré conjecture and its mathematical foundations. Contributions to the blueprints, Lean libraries, documentation, review, and project website are welcome.

## Before you start

- Check the [open issues](https://github.com/frenzymath/Poincare-Conjecture/issues) for related work.
- For a substantial change, open an issue first so its scope and mathematical source can be agreed upon.
- Keep each pull request focused on one project or one coherent piece of infrastructure.

Enable the repository's commit hook once after cloning:

```bash
git config core.hooksPath .githooks
```

## Blueprints

Blueprint contributions should follow the cited source faithfully and preserve the distinction between the source mathematics and any added dependency metadata.

- Give theorem-like statements stable, descriptive labels.
- Record mathematical dependencies with `\uses{...}`.
- Use `\lean{...}` to name the corresponding Lean declaration.
- Add `\leanok` only when the declaration has been checked and fully proves the stated result.
- Include a precise source reference when adding or changing mathematical content.

Do not edit generated files in `docs/` or project-level `dashboard.html` files by hand. After changing a blueprint, regenerate the site with [hgraph](https://github.com/AxelDlv00/hgraph) installed:

```bash
bash scripts/build-site.sh
```

## Lean

Shared Riemannian geometry belongs in `DoCarmo/OpenGALib`; `MorganTian` and `Petersen` depend on that single foundation. Prefer extending the shared library to duplicating a general result in a consumer project.

Build the project you changed before opening a pull request:

```bash
cd DoCarmo       # or MorganTian / Petersen
lake exe cache get
lake build
```

Changes to `DoCarmo/OpenGALib` should also be checked against both consumers:

```bash
cd MorganTian && lake build
cd ../Petersen && lake build
```

Avoid changing the pinned Lean toolchain or mathlib revision unless that upgrade is the purpose of the pull request.

## Pull requests

A pull request should explain:

- what mathematical or technical gap it addresses;
- which source or blueprint statement it follows;
- how the change was validated; and
- any remaining `sorry`, assumptions, or follow-up work.

Reviews consider both mathematical fidelity and the correctness of the Lean implementation. By contributing, you agree that your contribution is licensed under the repository's [Apache 2.0 License](LICENSE).

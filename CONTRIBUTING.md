# Contributing

Contributions to the primary proof, reference-source projects, shared Lean
infrastructure, blueprints, and mathematical reviews are welcome.

## Repository roles

- `PoincareConjecture/` is the primary custom formalization. Organize it by
  proof dependency, not by the chapter structure of a reference.
- `formalized-sources/` contains projects that follow particular books or
  articles. Preserve the source's mathematical organization and cite it
  precisely.
- `shared/` contains only book-independent infrastructure and mathlib gaps.

Keep each pull request focused on one project or one coherent infrastructure
change. For substantial work, check the
[project board](https://github.com/orgs/frenzymath/projects/1) and open an issue
before starting.

## Git hooks

Enable the repository hooks once after cloning:

```bash
git config core.hooksPath .githooks
```

The hooks remove unwanted generated attribution from commit messages and block
publishing history that still contains it.

## Lean

Build the project you changed from its own package directory:

```bash
cd PoincareConjecture
lake exe cache get
lake build
```

For a reference project, use its path under `formalized-sources/`:

```bash
cd formalized-sources/DoCarmo
lake exe cache get
lake build
```

All packages use the pinned toolchain and mathlib revision recorded in their
Lake files. Do not change those pins unless an upgrade is the purpose of the
pull request.

## Blueprints

- Give theorem-like statements stable, descriptive labels.
- Record mathematical dependencies with `\uses{...}`.
- Use `\lean{...}` for the corresponding Lean declaration.
- Add `\leanok` only after the declaration has been checked and fully proves
  the blueprint statement.
- Include precise source metadata in source-based projects.

The generated hgraph records and static website are build artifacts. Do not
commit `_site/`, `docs/`, or the directly generated Markdown files under
`hgraph/nodes/` and `hgraph/edges/`.

## hgraph and website

GitHub Actions installs the pinned hgraph revision, synchronizes every project,
builds the static site, and deploys it. Ordinary Lean and blueprint
contributors do not need to install hgraph.

Local hgraph is useful when changing graph metadata, previewing the website, or
writing a review. Install it using the upstream instructions, then synchronize
the project you are working on:

```bash
hgraph --root PoincareConjecture sync
hgraph serve --manifest config.yaml
```

For a reference project, pass its full root, for example
`--root formalized-sources/MorganTian`. From the repository root, bare
`hgraph sync` synchronizes every project listed in `config.yaml`.

## Reviews and comments

Reviews and comments are authored hgraph attachments. They live below a stable
node identifier and are intentionally tracked:

```text
<project>/hgraph/nodes/<node-id>/review-1.md
<project>/hgraph/nodes/<node-id>/comment-1.md
```

Run a local project sync before reviewing so the target nodes exist. Reviews
created through `hgraph serve` can be committed in a pull request. The CI sync
reconstructs the derived nodes around those attachments without overwriting
them, and the deployed site includes the merged feedback.

Alternatively, authenticated contributors can publish local feedback for
discussion without committing it first:

```bash
hgraph --root <project> review send --dry-run
hgraph --root <project> review send
```

Feedback sent through an issue appears in the repository-backed website only
after its attachment file is merged.

## Pull requests

A pull request should explain the mathematical or technical gap, its source,
the validation performed, and any remaining `sorry` or assumptions. CI builds
every Lean package and reconstructs the complete hgraph workspace from the
checked-out repository files.

By contributing, you agree that your contribution is licensed under the
repository's [Apache 2.0 License](LICENSE).

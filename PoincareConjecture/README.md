# PoincareConjecture

This is the repository's primary formalization project. Its blueprint follows
the dependency architecture of the Poincare conjecture rather than reproducing
the chapter order of a particular source.

The projects under `../formalized-sources/` remain faithful reference
formalizations of books and articles. Results from those projects may inform
or support this development, but they do not define its organization.

## Build

```bash
lake exe cache get
lake build
```

Graph synchronization and local website preview are documented in the root
`CONTRIBUTING.md`.

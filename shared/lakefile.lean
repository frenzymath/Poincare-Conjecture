import Lake
open Lake DSL

/-
Workspace-shared Lean infrastructure.

Scope is deliberately narrow: only material that belongs to **no book** — gaps
in mathlib (general algebra, metric geometry, topology) and workspace tooling
(the docstring/naming linters). Nothing here is anchored by any project's
blueprint.

Riemannian-geometry infrastructure does **not** live here. Each book project
formalizes its own, in the form its book needs; that duplication is intended,
because a book project should be a faithful, self-contained formalization
rather than a consumer of another book's engineering.
-/
package Shared where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib Shared where
  roots := #[`Shared]
  globs := #[.andSubmodules `Shared]

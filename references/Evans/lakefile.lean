import Lake
open Lake DSL

package EvansLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

@[default_target]
lean_lib EvansLib where
  roots := #[`EvansLib]
  globs := #[.andSubmodules `EvansLib]

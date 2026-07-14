import Lake
open Lake DSL

package OpenGALib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "5fc0241932dd6d465bc5549308cc39011772293a"

@[default_target]
lean_lib OpenGALib where
  roots := #[`OpenGALib]
  globs := #[.andSubmodules `OpenGALib]

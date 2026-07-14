import Lake
open Lake DSL

package PetersenLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "5fc0241932dd6d465bc5549308cc39011772293a"

require OpenGALib from "../DoCarmo"

@[default_target]
lean_lib PetersenLib where
  roots := #[`PetersenLib]
  globs := #[.andSubmodules `PetersenLib]

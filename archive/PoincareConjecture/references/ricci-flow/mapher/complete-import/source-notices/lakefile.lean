import Lake

open Lake DSL

package poincareMT where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`weak.linter.mathlibStandardSet, true⟩,
    ⟨`weak.linter.style.header, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "0df444a360eaa60ab8c11dca51a86af692955474"

-- Verification tools, compiled with this project's unchanged Lean toolchain.
require lean4export from git
  "https://github.com/leanprover/lean4export" @
  "15f6055e299ad5b89345e533cc2192f4cc00f659"

require Comparator from git
  "https://github.com/leanprover/comparator" @
  "3927ad383f208ae977c340a91c48ac9b497d2097"

@[default_target]
lean_lib PoincareMT where
  globs := #[`PoincareMT, `PoincareMT.+]

-- Separate environment: Challenge deliberately redeclares the endpoint names.
lean_lib Challenge where
  srcDir := "comparator"

lean_lib Solution where
  srcDir := "comparator"

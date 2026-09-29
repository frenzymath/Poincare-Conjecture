import Lake

open Lake DSL

package «poincare» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
    "0df444a360eaa60ab8c11dca51a86af692955474"

@[default_target]
lean_lib PoincareLib

@[default_target]
lean_lib PoincareConjecture where
  leanOptions := #[⟨`pp.unicode.fun, true⟩, ⟨`autoImplicit, false⟩]

require lean4export from git
  "https://github.com/leanprover/lean4export" @
    "15f6055e299ad5b89345e533cc2192f4cc00f659"

require Comparator from git
  "https://github.com/leanprover/comparator" @
    "3927ad383f208ae977c340a91c48ac9b497d2097"

-- Challenge and Solution redeclare names and must remain separate environments.
lean_lib Challenge where
  srcDir := "Comparator"

lean_lib Statements where
  srcDir := "Comparator"

lean_lib Solution where
  srcDir := "Comparator"

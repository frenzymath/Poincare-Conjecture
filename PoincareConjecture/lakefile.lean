import Lake
open Lake DSL

package PoincareConjecture where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

-- Reuse the already formalized sphere fundamental-group calculation from the
-- reference project. Pin the source subdirectory so this package also builds
-- independently of the surrounding monorepo (e.g. in the prize evidence package).
require HatcherLib from git
  "https://github.com/frenzymath/Poincare-Conjecture.git"
    @ "bb91a091f0b968f8bbe8d861e025a88d82b161be" / "formalized-sources/Hatcher"

@[default_target]
lean_lib PoincareConjecture where
  roots := #[`PoincareConjecture]
  globs := #[.andSubmodules `PoincareConjecture]

@[default_target]
lean_lib PoincareConjectureTests where
  roots := #[`PoincareConjectureTests, `PoincareConjectureTopologyTests,
    `PoincareConjectureOrientabilityTests]

import Lake
open Lake DSL

package MorganTianLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "5fc0241932dd6d465bc5549308cc39011772293a"

-- Shared Riemannian-geometry infrastructure (Levi-Civita, geodesics,
-- exponential map, curvature) maintained in the DoCarmo project; same
-- mathlib pin and toolchain.
require OpenGALib from "../OpenGA"

@[default_target]
lean_lib MorganTianLib where
  roots := #[`MorganTianLib]
  globs := #[.andSubmodules `MorganTianLib]

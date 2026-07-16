import Lake
open Lake DSL

package MorganTianLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- mathlib v4.30.0 (final) makes defeq checks respect transparency, which
    -- breaks the `TangentSpace I x = E` defeq abuse; mathlib itself opts out
    -- the same way. Inherited via the OpenGALib dependency.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

-- Shared Riemannian-geometry infrastructure (Levi-Civita, geodesics,
-- exponential map, curvature) maintained in the DoCarmo project; same
-- mathlib pin and toolchain.
require OpenGALib from "../DoCarmo"

@[default_target]
lean_lib MorganTianLib where
  roots := #[`MorganTianLib]
  globs := #[.andSubmodules `MorganTianLib]

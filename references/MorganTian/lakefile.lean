import Lake
open Lake DSL

package MorganTianLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Transparency-respecting defeq checks break the `TangentSpace I x = E`
    -- defeq abuse; mathlib itself opts out the same way. Inherited via the
    -- DoCarmoLib dependency.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

-- Shared Riemannian-geometry infrastructure (Levi-Civita, geodesics,
-- exponential map, curvature) maintained in the DoCarmo project; same
-- mathlib pin and toolchain.
require DoCarmoLib from "../DoCarmo"

@[default_target]
lean_lib MorganTianLib where
  roots := #[`MorganTianLib]
  globs := #[.andSubmodules `MorganTianLib]

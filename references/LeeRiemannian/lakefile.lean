import Lake
open Lake DSL

package LeeLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Transparency-respecting defeq checks break the `TangentSpace I x = E`
    -- defeq abuse; mathlib itself opts out the same way.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

-- Shared Riemannian-geometry infrastructure, including the axiom-clean
-- Hopf-Rinow theorem. The package uses the same toolchain and mathlib pin.
require DoCarmoLib from "../DoCarmo"

-- The Chapter 11 conjugate-point comparison uses the Sturm comparison
-- developed in the Morgan--Tian project, over the same DoCarmo backend.
require MorganTianLib from "../MorganTian"

@[default_target]
lean_lib LeeLib where
  roots := #[`LeeLib]
  globs := #[.andSubmodules `LeeLib]

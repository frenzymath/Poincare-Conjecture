import Lake
open Lake DSL

package LeeLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- mathlib v4.30.0 (final) makes defeq checks respect transparency, which
    -- breaks the `TangentSpace I x = E` defeq abuse; mathlib itself opts out
    -- the same way.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

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

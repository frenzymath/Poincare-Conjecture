import Lake
open Lake DSL

package PetersenLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- mathlib v4.30.0 (final) makes defeq checks respect transparency, which
    -- breaks the `TangentSpace I x = E` defeq abuse; mathlib itself opts out
    -- the same way. Needed by the vendored OpenGA manifold code.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

@[default_target]
lean_lib PetersenLib where
  roots := #[`PetersenLib]
  globs := #[.andSubmodules `PetersenLib]

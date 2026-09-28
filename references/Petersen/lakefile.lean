import Lake
open Lake DSL

package PetersenLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Transparency-respecting defeq checks break the `TangentSpace I x = E`
    -- defeq abuse; mathlib itself opts out the same way. Needed by the vendored
    -- OpenGA manifold code.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

@[default_target]
lean_lib PetersenLib where
  roots := #[`PetersenLib]
  globs := #[.andSubmodules `PetersenLib]

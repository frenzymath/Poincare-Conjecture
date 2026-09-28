import Lake
open Lake DSL

package GilbargTrudinger where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require DoCarmoLib from "../DoCarmo"

@[default_target]
lean_lib GilbargTrudinger where
  roots := #[`GilbargTrudinger]
  globs := #[.andSubmodules `GilbargTrudinger]

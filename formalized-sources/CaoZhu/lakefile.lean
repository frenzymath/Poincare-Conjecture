import Lake
open Lake DSL

package CaoZhuLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require DoCarmoLib from "../DoCarmo"

@[default_target]
lean_lib CaoZhuLib where
  roots := #[`CaoZhuLib]
  globs := #[.andSubmodules `CaoZhuLib]

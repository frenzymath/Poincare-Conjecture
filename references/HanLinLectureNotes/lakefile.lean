import Lake
open Lake DSL

package HanLinLectureNotes where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require DoCarmoLib from "../DoCarmo"

@[default_target]
lean_lib HanLinLectureNotes where
  roots := #[`HanLinLectureNotes]
  globs := #[.andSubmodules `HanLinLectureNotes]

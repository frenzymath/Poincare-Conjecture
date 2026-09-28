import Lake
open Lake DSL

package DoCarmoLib where
  lintDriver := "batteries/runLinter"
  testDriver := "DoCarmoLibTest"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- Transparency-respecting defeq checks break the `TangentSpace I x = E`
    -- defeq abuse; mathlib itself opts out the same way. Needed here for the
    -- Riemannian tangent-space instances.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    -- some tangent-space instance searches (e.g. bilinear forms on T_xM) exceed
    -- the default budget after the newer typeclass changes.
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

-- Workspace-shared, book-agnostic infrastructure (mathlib gaps + linters).
-- Riemannian material deliberately does NOT live there: this project owns its
-- own, in the form do Carmo's exposition needs.
require Shared from ".." / "shared"

@[default_target]
lean_lib DoCarmoLib where
  roots := #[`DoCarmoLib]
  globs := #[.andSubmodules `DoCarmoLib]

lean_lib DoCarmoLibTest where
  globs := #[.submodules `DoCarmoLibTest]

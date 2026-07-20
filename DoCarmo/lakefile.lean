import Lake
open Lake DSL

package DoCarmoLib where
  lintDriver := "batteries/runLinter"
  testDriver := "DoCarmoLibTest"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    -- mathlib v4.30.0 (final) makes defeq checks respect transparency, which
    -- breaks the `TangentSpace I x = E` defeq abuse; mathlib itself opts out the
    -- same way. Needed here for the Riemannian tangent-space instances.
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    -- some tangent-space instance searches (e.g. bilinear forms on T_xM) exceed
    -- the default budget after the v4.30.0 typeclass changes.
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

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

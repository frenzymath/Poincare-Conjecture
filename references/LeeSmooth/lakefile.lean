import Lake
open Lake DSL

package LeeSmoothLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩,
    ⟨`backward.isDefEq.respectTransparency, false⟩,
    ⟨`synthInstance.maxHeartbeats, (400000 : Nat)⟩
  ]

-- All workspace projects share the same mathlib release and package checkout.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "520045ab14e26149ee970e2e617ca04b09bde5d6"

-- `globs` is required: without it Lake builds only the root module, and since the
-- root imports no item module, `lake build` would succeed while compiling nothing.
-- That is exactly the defect described in UPSTREAM_LEAN_AUDIT.md.
@[default_target]
lean_lib LeeSmoothLib where
  roots := #[`LeeSmoothLib]
  globs := #[.andSubmodules `LeeSmoothLib]

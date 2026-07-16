import Lake
open Lake DSL

package LeeSmoothLib where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, (3 : Nat)⟩
  ]

-- NOTE: this project pins mathlib at v4.30.0 (c5ea0035), NOT the workspace-wide
-- rev 5fc0241 used by DoCarmo/LeeRiemannian/Petersen/Poincare/Evans/Hatcher.
-- The imported Lean was written against a mathlib 946 commits newer than the
-- workspace pin and does not compile against it. Consequently LeeSmooth must
-- keep its own mathlib checkout under `.lake/packages/` rather than sharing the
-- symlinked one at `DoCarmo/.lake/packages/mathlib`. See UPSTREAM_LEAN_AUDIT.md.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
    @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

-- `globs` is required: without it Lake builds only the root module, and since the
-- root imports no item module, `lake build` would succeed while compiling nothing.
-- That is exactly the defect described in UPSTREAM_LEAN_AUDIT.md.
@[default_target]
lean_lib LeeSmoothLib where
  roots := #[`LeeSmoothLib]
  globs := #[.andSubmodules `LeeSmoothLib]

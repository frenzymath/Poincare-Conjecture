import Mathlib

/-!
# LeeSmoothLib

Lean formalization of John M. Lee, *Introduction to Smooth Manifolds*
(2nd ed., GTM 218). Imported from `frenzymath/ALLBOOKS` (`SmoothManifoldsLee`,
commit `cdd0f105`); see `UPSTREAM_LEAN_AUDIT.md`.

One module per book item, at `LeeSmoothLib/Ch<NN>/Sec<NN>_<MM>/<Item>.lean`, so
that each blueprint node maps to exactly one Lean module.

## Why this root module imports no item module

Unlike the other projects in this workspace (whose root module imports every
submodule), this root cannot: two upstream item modules declare the same name,
so importing both fails —

```
import LeeSmoothLib.Ch01.Sec01_05.Proposition_1_40 failed, environment already
contains 'connectedComponent_connectedSpace' from LeeSmoothLib.Ch01.Sec01.Proposition_1_11
```

The item modules are therefore built via `globs := #[.andSubmodules \`LeeSmoothLib]`
in `lakefile.lean`, which compiles them all without importing them into one
environment. Do **not** "fix" this by deleting the glob: without it `lake build`
compiles only this file and reports success while verifying nothing.
-/

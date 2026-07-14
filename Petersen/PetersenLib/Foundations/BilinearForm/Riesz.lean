import OpenGALib.Algebraic.BilinearForm.Riesz

/-!
# Riesz extraction — algebraic core

This module previously carried a verbatim vendored copy of the shared
OpenGALib Riesz core.  It now re-exports the live shared definition so
there is a single `BilinearForm.toDual` / `BilinearForm.riesz` (and
friends) in the environment, avoiding a duplicate-definition collision
when both Petersen and OpenGALib appear in the same import graph.

All names (`BilinearForm.toDual`, `BilinearForm.toDualEquiv`,
`BilinearForm.riesz`, `BilinearForm.IsPosDef.nondegenerate`, and the
`toDual_*` / `riesz_*` / `inner_eq_iff_eq` lemmas) are provided unchanged
by the imported module.
-/

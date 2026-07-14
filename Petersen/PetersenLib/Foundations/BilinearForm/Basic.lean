import OpenGALib.Algebraic.BilinearForm.Basic

/-!
# Bilinear forms — algebraic core (field-generic)

This module previously carried a verbatim vendored copy of the shared
OpenGALib bilinear-form core.  It now re-exports the live shared
definition so there is a single `BilinearForm.inner` (and friends) in the
environment, avoiding a duplicate-definition collision when both Petersen
and OpenGALib appear in the same import graph.

All names (`BilinearForm.Form`, `BilinearForm.inner`, `BilinearForm.IsSymm`,
`BilinearForm.IsPosDef`, and the `inner_*` lemmas) are provided unchanged by
the imported module.
-/

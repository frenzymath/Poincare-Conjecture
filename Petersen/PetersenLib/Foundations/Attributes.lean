import OpenGALib.Util.Attributes

/-!
# Simp attributes — declarations

This module previously registered a minimal vendored subset of the shared
OpenGALib simp attributes.  It now re-exports the live shared declarations
so the `metric_simp` (and `riem_simp`) attributes are registered exactly
once, avoiding a duplicate-registration collision when both Petersen and
OpenGALib appear in the same import graph.
-/

import Mathlib.Tactic.Common

/-!
# Simp attributes — declarations

Pure attribute registration, intentionally without imports of lemmas
that consume the attributes. Vendored (minimal subset) from the shared
OpenGALib core (`OpenGALib/Util/Attributes.lean`, identical in the
openga and DoCarmo projects).
-/

/-- Simp set for `metricInner` algebra normalisation: bilinearity, sign
rules, zero / neg / sub / self_nonneg. Tagged on the lemmas in
`Foundations/RiemannianMetric.lean`; downstream proofs can invoke
`simp only [metric_simp]` for routine inner-product calculations. -/
register_simp_attr metric_simp

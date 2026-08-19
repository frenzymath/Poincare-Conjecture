import PetersenLib.Ch06.ExpCovering
import PetersenLib.Ch06.SpaceFormConjugate

/-!
# Petersen Ch. 6, §6.2 — the formalizable Cartan–Hadamard core

The full Hadamard–Cartan theorem also needs the construction of a universal smooth
cover and the bridge from the sectional-curvature Jacobi estimate to global
nonsingularity of `exp_p`.  Those constructions are not present in the current
library.  This file records the two conclusions which are available without
silently assuming that missing bridge:

* the topological covering-map conclusion from the explicit hypotheses of
  `exp_nonsingular_isCoveringMap`; and
* the finite-dimensional fact that the source tangent model is linearly
  (continuously) equivalent to Euclidean space.

The conditional core is named `cartanHadamard_coveringCore` to make its scope
explicit, rather than retaining the headline name for a partial result.  Its
hypotheses are the concrete local-homeomorphism, closed-map, and finite
fibre data; no universal-cover or diffeomorphism conclusion is hidden in an
assumption.  The analytic nonpositive-curvature input is exposed separately by
`injectivityRadius_nonpositiveCurvature_modelCore` below.
-/

open Set

noncomputable section

namespace PetersenLib

/-- **Math.** Conditional core of Petersen Theorem 6.2.2 (Hadamard–Cartan).

If the exponential-map candidate has the local-homeomorphism, closed-map, and
finite-fibre properties supplied by the pullback-metric argument, it is a covering
map.  Its finite-dimensional source is continuously linearly equivalent to the
Euclidean model of the same dimension.  The omitted universal-cover construction
and the curvature-to-nonsingularity bridge are deliberately not encoded as an
assumed conclusion.
-/
theorem cartanHadamard_coveringCore
    {V X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [TopologicalSpace X] [T2Space X]
    (exp_p : V → X)
    (hlocal : IsLocalHomeomorph exp_p)
    (hclosed : IsClosedMap exp_p)
    (hfinite : ∀ x : X, (exp_p ⁻¹' {x}).Finite) :
    IsCoveringMap exp_p ∧
      Nonempty (V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := by
  refine ⟨exp_nonsingular_isCoveringMap exp_p hlocal hclosed hfinite, ?_⟩
  exact ⟨toEuclidean⟩

/-- **Math.** Analytic no-conjugate-point core used in Petersen's nonpositive
curvature injectivity-radius remark.  For `K ≤ 0`, the model Jacobi coefficient
`sn_K` never vanishes at a positive time.

The intrinsic statement about the injectivity radius and shortest geodesic loops
also requires the global cut-locus/compactness bridge; this theorem records the
part that is proved by the space-form Jacobi equation.
-/
theorem injectivityRadius_nonpositiveCurvature_modelCore {K : ℝ} (hK : K ≤ 0) {t : ℝ}
    (ht : 0 < t) : snFunction K t ≠ 0 :=
  snFunction_ne_zero_of_nonpos hK ht

end PetersenLib

end

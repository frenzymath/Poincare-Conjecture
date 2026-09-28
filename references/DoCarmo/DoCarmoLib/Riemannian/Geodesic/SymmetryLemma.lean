import DoCarmoLib.Riemannian.Geodesic.Equation
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Symmetry lemma (do Carmo Ch. 3, Lemma 3.4) — chart-coordinate core

The covariant second derivative of a `C²` chart-coordinate surface is symmetric.
This is the coordinate engine of do Carmo's symmetry lemma `D/∂s (∂f/∂t) =
D/∂t (∂f/∂s)`: it packages Schwarz (`second_derivative_symmetric`, mixed partials
commute) with the symmetry of the Christoffel contraction
(`chartChristoffelContraction_symm`, `Γᵏᵢⱼ = Γᵏⱼᵢ`).

It is the most upstream gap on the Gauss-lemma → Hopf–Rinow chain (do Carmo Ch. 3
§3): with it the elementary Gauss-lemma proof proceeds with no Jacobi fields.
-/

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

-- the chart machinery pulls in `Module.Finite ℝ E` which this thin lemma never names

namespace Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Symmetry lemma (do Carmo Ch. 3, Lemma 3.4), chart-coordinate form.**
For a `C²` chart-coordinate surface `c : ℝ² → E` with derivative `Dc` (everywhere)
and second derivative `D2c` at `x`, the covariant second derivative
`D2c v w + Γ(Dc v, Dc w)` is symmetric in `v, w`. This is the coordinate core of
`D/∂s (∂f/∂t) = D/∂t (∂f/∂s)` — Schwarz on the leading term, Christoffel symmetry
on the connection term. -/
theorem covariant_sndFDeriv_symm (g : RiemannianMetric I M) (α : M)
    {c : (ℝ × ℝ) → E} {Dc : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] E)}
    {D2c : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E} {x : ℝ × ℝ}
    (hc : ∀ y, HasFDerivAt c (Dc y) y) (hc2 : HasFDerivAt Dc D2c x)
    (v w : ℝ × ℝ) :
    D2c v w + chartChristoffelContraction (I := I) g α (Dc x v) (Dc x w) (c x)
      = D2c w v + chartChristoffelContraction (I := I) g α (Dc x w) (Dc x v) (c x) := by
  rw [second_derivative_symmetric hc hc2 v w, chartChristoffelContraction_symm]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Symmetry lemma (do Carmo Ch. 3, Lemma 3.4), local chart-coordinate
form.** The same covariant-second-derivative symmetry with the first-derivative
hypothesis required only *near* `x` — the form needed for a surface (such as
`(t,s) ↦ φ_p(exp_p(t·v(s)))`) that is only defined and `C²` on an open set. -/
theorem covariant_sndFDeriv_symm_of_eventually (g : RiemannianMetric I M) (α : M)
    {c : (ℝ × ℝ) → E} {Dc : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] E)}
    {D2c : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E} {x : ℝ × ℝ}
    (hc : ∀ᶠ y in nhds x, HasFDerivAt c (Dc y) y) (hc2 : HasFDerivAt Dc D2c x)
    (v w : ℝ × ℝ) :
    D2c v w + chartChristoffelContraction (I := I) g α (Dc x v) (Dc x w) (c x)
      = D2c w v + chartChristoffelContraction (I := I) g α (Dc x w) (Dc x v) (c x) := by
  rw [second_derivative_symmetric_of_eventually hc hc2 v w,
    chartChristoffelContraction_symm]

end Riemannian.Geodesic

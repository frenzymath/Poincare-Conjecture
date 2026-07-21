import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.31 (parallel vector fields have constant length)

Exercise 2.5.31: let `X` be a parallel vector field on `(M, g)` (`∇X = 0`).  Show
`X` has constant length, that it generates parallel distributions, and that
locally `(U, g) = (V × I, g|_V + dt²)`.

The formalized declaration `exercise2_5_31` establishes the **constant-length**
part: for a parallel field `X` the squared length `q ↦ g(X, X)(q)` has vanishing
differential at every point, i.e. `X` has (locally) constant length.  The proof is
Petersen's: metric compatibility gives
`D_v g(X, X) = g(∇_v X, X) + g(X, ∇_v X)`, and both connection terms vanish because
`∇_v X = 0`.

The remaining conclusions — that `X` generates orthogonally complementary parallel
distributions and the resulting local product-metric splitting
`(U, g) = (V × I, g|_V + dt²)` — depend on the Frobenius integrability theorem and
the product-metric construction of Exercise 2.5.30, which are not available in this
development.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.31.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section
namespace PetersenLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §2.5, Exercise 2.5.31 (constant-length part): a **parallel**
vector field `X` (`∇_v X = 0` for every direction `v`) has constant length — the
differential of the squared length `q ↦ g(X, X)(q)` vanishes at every point.

Petersen's proof: differentiate `g(X, X)` along `v` using metric compatibility,
`D_v g(X, X) = g(∇_v X, X) + g(X, ∇_v X)`; both terms drop since `∇_v X = 0`. -/
theorem exercise2_5_31 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hpar : ∀ (p : M) (v : TangentSpace I p), D.cov p v X = 0) (p : M) :
    mfderiv I 𝓘(ℝ, ℝ) (fun q => g.metricInner q (X q) (X q)) p = 0 := by
  ext v
  have hcompat := D.metric_compat hX hX p v
  rw [hpar p v] at hcompat
  simp only [g.metricInner_zero_left, g.metricInner_zero_right, add_zero] at hcompat
  simpa [dirTangent] using hcompat

end PetersenLib

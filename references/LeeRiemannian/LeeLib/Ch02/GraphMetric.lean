/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": metrics in graph coordinates.

Lee's Example 2.19.  If `U ⊆ ℝⁿ` is open and `f : U → ℝ` is smooth, its graph
`Γ(f) = {(x, f(x))} ⊆ ℝⁿ⁺¹` is an embedded `n`-dimensional submanifold, with the
global graph parametrization `X(u) = (u, f(u))`.  In graph coordinates the metric
induced on `Γ(f)` by the Euclidean metric of `ℝⁿ⁺¹` is

  `X^* ḡ = (du¹)² + ⋯ + (duⁿ)² + df²`,

that is, `(X^* ḡ)_u(v, w) = ⟨v, w⟩ + df_u(v)·df_u(w)` (`graphMetric`).

We work with a general real inner-product space `E` in the role of `ℝⁿ`, and
realise the ambient `ℝⁿ⁺¹ = ℝⁿ × ℝ` as the `L²`-product `WithLp 2 (E × ℝ)`, whose
inner product is exactly `⟨(a,s),(b,t)⟩ = ⟨a,b⟩ + s·t`.  Following Lee's §2.3, the
induced metric is the pullback `X^* ḡ` of the Euclidean metric along `X`, so this
is `pullbackForm` of `euclideanMetric`.  Because `X` is defined on all of `E`
(the case `U = ℝⁿ` of Lee's `U ⊆ ℝⁿ`) the computation is global; all the content
is the Jacobian `dX_u(v) = (v, df_u(v))` and the split of the `L²`-product inner
product into its two blocks.

This construction is not in the shared DoCarmoLib/PetersenLib developments; it is
the graph-coordinate companion of `LeeLib.Ch02.SurfaceOfRevolution` (Lee 2.20).
-/
import LeeLib.Ch02.PullbackMetric
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section

open Manifold
open scoped ContDiff Manifold Topology RealInnerProductSpace

namespace LeeLib.Ch02

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The graph parametrization** `X(u) = (u, f(u))` of Lee's Example 2.19, valued
in the `L²`-product `ℝⁿ⁺¹ = ℝⁿ × ℝ` realised as `WithLp 2 (E × ℝ)`. -/
def graphMap (f : E → ℝ) (u : E) : WithLp 2 (E × ℝ) := WithLp.toLp 2 (u, f u)

/-- **The Jacobian of the graph parametrization**: `dX_u(v) = (v, df_u(v))`. -/
def graphJacobian (f : E → ℝ) (p : E) : E →L[ℝ] WithLp 2 (E × ℝ) :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm : (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ)).comp
    ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ f p))

theorem hasFDerivAt_graphMap {f : E → ℝ} (hf : Differentiable ℝ f) (p : E) :
    HasFDerivAt (graphMap f) (graphJacobian f p) p := by
  have h1 : HasFDerivAt (fun u : E => (u, f u))
      ((ContinuousLinearMap.id ℝ E).prod (fderiv ℝ f p)) p :=
    (hasFDerivAt_id p).prodMk (hf p).hasFDerivAt
  exact (((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm :
    (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ)).hasFDerivAt).comp p h1

/-- **Lee's Example 2.19: the induced metric in graph coordinates.**  The metric
induced from `(dx¹)² + ⋯ + (dxⁿ⁺¹)²` by the graph parametrization
`X(u) = (u, f(u))` is `(du¹)² + ⋯ + (duⁿ)² + df²`, i.e.
`(X^* ḡ)_u(v, w) = ⟨v, w⟩ + df_u(v)·df_u(w)`. -/
theorem graphMetric {f : E → ℝ} (hf : Differentiable ℝ f) (p : E)
    (v w : TangentSpace 𝓘(ℝ, E) p) :
    pullbackForm (euclideanMetric (WithLp 2 (E × ℝ))) (graphMap f) p v w =
      inner ℝ (show E from v) (show E from w) +
        fderiv ℝ f p (show E from v) * fderiv ℝ f p (show E from w) := by
  rw [pullbackForm_apply, euclideanMetric_inner]
  have hmf : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, WithLp 2 (E × ℝ)) (graphMap f) p = graphJacobian f p := by
    rw [mfderiv_eq_fderiv]
    exact (hasFDerivAt_graphMap hf p).fderiv
  rw [hmf]
  show @inner ℝ _ _ (graphJacobian f p v) (graphJacobian f p w) = _
  simp only [graphJacobian, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
    WithLp.prod_inner_apply]
  have hinner : ∀ a b : ℝ, (inner ℝ a b : ℝ) = b * a := fun _ _ => rfl
  rw [hinner]
  ring

end LeeLib.Ch02

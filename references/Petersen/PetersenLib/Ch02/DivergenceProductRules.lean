import PetersenLib.Ch02.CovariantAdjoint
import PetersenLib.Ch02.ExercisesProductRule

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.27 (divergence/Laplacian product rules)

Exercise 2.5.27 collects the calculus of the divergence and Laplacian on an
oriented Riemannian manifold.  The formalized declarations establish the two
**algebraic** parts, which hold pointwise without integration:

* `exercise2_5_27` — part (2), the divergence product rule
  `div(f X) = g(∇f, X) + f · div X`;
* `exercise2_5_27_laplacian_product` — part (3), the Laplacian product rule
  `Δ(f₁ f₂) = (Δf₁) f₂ + 2 g(∇f₁, ∇f₂) + f₁ Δf₂`.

The remaining parts — (1) `∫_M Δf · vol = 0` for compactly supported `f`, (4)
Green's formula, and (5) the (weak and strong) maximum principle — require the
divergence theorem / Stokes' theorem on compact support, which is not available
in the manifold-integration API and is deferred.

Both formalized identities are stated against a positively oriented **orthonormal
frame** `E₁, …, E_n` near `x` (orthonormal for `g`, normalized to
`vol(E₁, …, E_n) = 1` on a neighbourhood of `x`) — the standing frame hypothesis
of the divergence and its adjoint (`divergence_trace_formula`,
`divergence_eq_neg_adjoint_dualForm`).  The proofs are Petersen's: writing the
divergence as the covariant trace `div X = Σᵢ g(∇_{Eᵢ}X, Eᵢ)`, both rules follow
from the Leibniz rule of the connection and the orthonormal expansion of the
gradient.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.27.
-/

open Bundle Set Function Finset Module
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section
namespace PetersenLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] [T2Space M]
  [hm : HasMetric I M]

/-! ## Orthonormal Parseval pairing -/

omit [FiniteDimensional ℝ E] [InnerProductSpace ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Parseval pairing against a `g`-orthonormal tuple at `x`:
`g(a, b) = Σᵢ g(b, vᵢ) · g(a, vᵢ)`.  Immediate from the orthonormal expansion
`b = Σᵢ g(b, vᵢ) · vᵢ` and bilinearity. -/
theorem metricInner_orthonormal_pairing {x : M}
    {v : Fin (Module.finrank ℝ E) → TangentSpace I x}
    (h : ∀ i j, hm.metric.metricInner x (v i) (v j) = if i = j then 1 else 0)
    (a b : TangentSpace I x) :
    hm.metric.metricInner x a b
      = ∑ i, hm.metric.metricInner x b (v i) * hm.metric.metricInner x a (v i) := by
  conv_lhs => rw [metricInner_orthonormal_expansion h b]
  simp only [hasMetric_metricInner_eq_inner, inner_sum, real_inner_smul_right]

/-! ## The divergence as a covariant trace -/

/-- **Math.** Against a positively oriented orthonormal frame `E₁, …, E_n` near
`x`, the divergence is the covariant trace `div X = Σᵢ g(∇_{Eᵢ}X, Eᵢ)`.  Combines
the trace formula `div X = Σᵢ ½(L_X g)(Eᵢ, Eᵢ)` with the pairing identity
`g(∇_{Eᵢ}X, Eᵢ) = ½(L_X g)(Eᵢ, Eᵢ)`. -/
theorem divergenceLieDerivative_eq_sum_covariant
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o X x
      = ∑ i, hm.metric.metricInner x (D.cov x (Efr i x) X) (Efr i x) := by
  rw [divergence_trace_formula o X hEs hU horth hvol]
  exact Finset.sum_congr rfl fun i _ =>
    (RiemannianConnection.metricInner_cov_self_eq_half_lie D hX (hEs i) x).symm

/-- **Math.** Additivity of the divergence: `div(A + B) = div A + div B`.  The
covariant trace is additive in the field through the connection's `add_field`. -/
theorem divergenceLieDerivative_add
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {A B : Π x : M, TangentSpace I x}
    (hA : IsSmoothVectorField A) (hB : IsSmoothVectorField B)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o (fun q => A q + B q) x
      = divergenceLieDerivative o A x + divergenceLieDerivative o B x := by
  have hAB : IsSmoothVectorField (fun q => A q + B q) := ContMDiff.add_section hA hB
  rw [divergenceLieDerivative_eq_sum_covariant o D hAB hEs hU horth hvol,
      divergenceLieDerivative_eq_sum_covariant o D hA hEs hU horth hvol,
      divergenceLieDerivative_eq_sum_covariant o D hB hEs hU horth hvol,
      ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [D.add_field x (Efr i x) hA hB, hm.metric.metricInner_add_left]

/-! ## Exercise 2.5.27 part (2): divergence product rule -/

/-- **Math.** Petersen §2.5, Exercise 2.5.27 (2): the **divergence product rule**
`div(f X) = g(∇f, X) + f · div X`, against an orthonormal frame near `x`.

Petersen's proof: `div(f X) = Σᵢ g(∇_{Eᵢ}(f X), Eᵢ)`; the Leibniz rule
`∇_{Eᵢ}(f X) = (E_i f)·X + f·∇_{Eᵢ}X` splits each summand into
`(E_i f)·g(X, Eᵢ) + f·g(∇_{Eᵢ}X, Eᵢ)`; summing, the second block is `f·div X` and
the first is `g(∇f, X)` by the Parseval expansion of the gradient. -/
theorem exercise2_5_27
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    divergenceLieDerivative o (fun q => f q • X q) x
      = hm.metric.metricInner x (gradient hm.metric f x) (X x)
        + f x * divergenceLieDerivative o X x := by
  have hfX : IsSmoothVectorField (fun q => f q • X q) := isSmoothVectorField_smul hf hX
  rw [divergenceLieDerivative_eq_sum_covariant o D hfX hEs hU horth hvol,
      divergenceLieDerivative_eq_sum_covariant o D hX hEs hU horth hvol]
  have key : ∀ i, hm.metric.metricInner x
        (D.cov x (Efr i x) (fun q => f q • X q)) (Efr i x)
      = dirTangent f (Efr i x) * hm.metric.metricInner x (X x) (Efr i x)
        + f x * hm.metric.metricInner x (D.cov x (Efr i x) X) (Efr i x) := by
    intro i
    rw [D.leibniz x (Efr i x) hf hX, hm.metric.metricInner_add_left,
      hm.metric.metricInner_smul_left, hm.metric.metricInner_smul_left]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, ← Finset.mul_sum]
  congr 1
  rw [metricInner_orthonormal_pairing (v := fun i => Efr i x)
    (horth x (mem_of_mem_nhds hU)) (gradient hm.metric f x) (X x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dirTangent_eq_directionalDerivative,
    directionalDerivative_eq_metricInner_gradient hm.metric]
  ring

/-! ## Exercise 2.5.27 part (3): Laplacian product rule -/

/-- **Math.** Petersen §2.5, Exercise 2.5.27 (3): the **Laplacian product rule**
`Δ(f₁ f₂) = (Δf₁) f₂ + 2 g(∇f₁, ∇f₂) + f₁ Δf₂`, against an orthonormal frame
near `x`.  Expanding `∇(f₁ f₂) = f₂·∇f₁ + f₁·∇f₂` (gradient product rule), then
applying additivity of the divergence and the divergence product rule (part (2))
to each term, the cross terms combine into `2 g(∇f₁, ∇f₂)` by symmetry of `g`. -/
theorem exercise2_5_27_laplacian_product [I.Boundaryless] [CompleteSpace E]
    (o : ∀ x : M, Orientation ℝ (TangentSpace I x) (Fin (Module.finrank ℝ E)))
    (D : RiemannianConnection I hm.metric)
    {f₁ f₂ : M → ℝ} (hf₁ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₁)
    (hf₂ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f₂)
    {Efr : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then 1 else 0)
    (hvol : ∀ y ∈ U, volumeOperator o Efr y = 1) :
    laplacian o (fun p => f₁ p * f₂ p) x
      = laplacian o f₁ x * f₂ x
        + 2 * hm.metric.metricInner x (gradient hm.metric f₁ x) (gradient hm.metric f₂ x)
        + f₁ x * laplacian o f₂ x := by
  have hf₁d : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) f₁ x := fun x => (hf₁ x).mdifferentiableAt (by decide)
  have hf₂d : ∀ x, MDifferentiableAt I 𝓘(ℝ, ℝ) f₂ x := fun x => (hf₂ x).mdifferentiableAt (by decide)
  have hg₁ : IsSmoothVectorField (gradient hm.metric f₁) := gradient_isSmoothVectorField hm.metric hf₁
  have hg₂ : IsSmoothVectorField (gradient hm.metric f₂) := gradient_isSmoothVectorField hm.metric hf₂
  have hs₁ : IsSmoothVectorField (fun q => f₂ q • gradient hm.metric f₁ q) :=
    isSmoothVectorField_smul hf₂ hg₁
  have hs₂ : IsSmoothVectorField (fun q => f₁ q • gradient hm.metric f₂ q) :=
    isSmoothVectorField_smul hf₁ hg₂
  rw [laplacian_apply, gradient_mul hf₁d hf₂d hm.metric,
    divergenceLieDerivative_add o D hs₁ hs₂ hEs hU horth hvol,
    exercise2_5_27 o D hf₂ hg₁ hEs hU horth hvol,
    exercise2_5_27 o D hf₁ hg₂ hEs hU horth hvol,
    ← laplacian_apply, ← laplacian_apply,
    hm.metric.metricInner_comm x (gradient hm.metric f₂ x) (gradient hm.metric f₁ x)]
  ring

end PetersenLib

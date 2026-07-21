/-
Chapter 4, "Connections", Problem 4-10: parallel vector fields and reparametrization.

Lee's Problem 4-10: if `Y` is parallel along a curve `γ`, then it is parallel along
every reparametrization of `γ`.  Read in a chart (via the covariant derivative along
a curve `covariantDerivAlongChart` of `LeeLib.Ch04.ParallelTransport`), a
reparametrization by `φ : ℝ → ℝ` sends the coordinate data `(u, c, V)` to
`(u ∘ φ, c ∘ φ, V ∘ φ)`, and the covariant derivative along the reparametrized curve
is the chain-rule rescaling of the original:

  `D_s (V ∘ φ)(s) = φ'(s) • (D_t V)(φ(s))`   (`covariantDerivAlongChart_comp`).

This is immediate from the chain rule `(V ∘ φ)'(s) = φ'(s) • V'(φ(s))`,
`(u ∘ φ)'(s) = φ'(s) • u'(φ(s))`, and the homogeneity of the chart Christoffel
contraction in its direction slot (`chartGamma_smul_left`).  In particular, if `V` is
parallel along `(u, c)` then `V ∘ φ` is parallel along `(u ∘ φ, c ∘ φ)`
(`isParallelAlongChart_comp`).  (Note this is the statement for a fixed field `V`
reparametrized to `V ∘ φ`; it is *not* the same as geodesic-preservation, whose
reparametrized velocity is `φ' • (γ' ∘ φ)` rather than `γ' ∘ φ`, so geodesics are
preserved only under affine reparametrizations.)
-/
import LeeLib.Ch04.ParallelTransport

namespace LeeLib.Ch04

open Bundle Module
open scoped Manifold ContDiff Topology
open Set

set_option linter.unusedSectionVars false

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [Fintype ι]
  {e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)}
  [MemTrivializationAtlas e] {b : Basis ι ℝ E}

/-- **The covariant derivative along a curve under reparametrization** (chain rule).
Reparametrizing the chart data `(u, c, V)` by `φ : ℝ → ℝ` rescales the covariant
derivative along the curve by the reparametrization speed:
`D_s (V ∘ φ)(s) = φ'(s) • (D_t V)(φ(s))`.  The two chain-rule terms
`(V ∘ φ)'` and `(u ∘ φ)'` each pick up a factor `φ'(s)`, and the `Γ`-term factor is
pulled out by homogeneity of the Christoffel contraction in the direction slot. -/
theorem covariantDerivAlongChart_comp (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (V : ℝ → E) (φ : ℝ → ℝ) (s : ℝ)
    (hφ : DifferentiableAt ℝ φ s) (hu : DifferentiableAt ℝ u (φ s))
    (hV : DifferentiableAt ℝ V (φ s)) :
    covariantDerivAlongChart cov e b (u ∘ φ) (c ∘ φ) (V ∘ φ) s
      = deriv φ s • covariantDerivAlongChart cov e b u c V (φ s) := by
  have hVφ : deriv (V ∘ φ) s = deriv φ s • deriv V (φ s) :=
    (hV.hasDerivAt.scomp s hφ.hasDerivAt).deriv
  have huφ : deriv (u ∘ φ) s = deriv φ s • deriv u (φ s) :=
    (hu.hasDerivAt.scomp s hφ.hasDerivAt).deriv
  simp only [covariantDerivAlongChart_def, Function.comp_apply, hVφ, huφ,
    chartGamma_smul_left, smul_add]

/-- **Lee's Problem 4-10**: a parallel vector field stays parallel under
reparametrization.  If `V` is parallel along the chart curve `(u, c)`
(`D_t V ≡ 0`), then the reparametrized field `V ∘ φ` is parallel along the
reparametrized curve `(u ∘ φ, c ∘ φ)`, for any (everywhere differentiable)
reparametrization `φ : ℝ → ℝ`.  Immediate from `covariantDerivAlongChart_comp`:
`D_s (V ∘ φ) = φ' • (D_t V) ∘ φ = φ' • 0 = 0`. -/
theorem isParallelAlongChart_comp (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (V : ℝ → E) (φ : ℝ → ℝ)
    (hφ : ∀ s, DifferentiableAt ℝ φ s) (hu : ∀ t, DifferentiableAt ℝ u t)
    (hV : ∀ t, DifferentiableAt ℝ V t)
    (hpar : IsParallelAlongChart cov e b u c V) :
    IsParallelAlongChart cov e b (u ∘ φ) (c ∘ φ) (V ∘ φ) := by
  intro s
  rw [covariantDerivAlongChart_comp cov u c V φ s (hφ s) (hu (φ s)) (hV (φ s)),
    hpar (φ s), smul_zero]

end

end LeeLib.Ch04

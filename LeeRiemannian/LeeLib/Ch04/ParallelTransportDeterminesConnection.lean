import LeeLib.Ch04.ParallelTransport
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach

namespace LeeLib.Ch04

open Bundle Module
open scoped Manifold ContDiff Topology NNReal
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

/-- **Operator-norm bound for left-composition.** Left-composition by a fixed continuous
linear map `g : E →L[ℝ] E`, encoded as `ContinuousLinearMap.compL ℝ E E E g`, has operator
norm at most `‖g‖`. -/
theorem nnnorm_compL_apply_le (g : E →L[ℝ] E) :
    ‖ContinuousLinearMap.compL ℝ E E E g‖₊ ≤ ‖g‖₊ := by
  rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
  calc ‖ContinuousLinearMap.compL ℝ E E E g‖
      ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖g‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm g
    _ ≤ 1 * ‖g‖ := by gcongr; exact ContinuousLinearMap.norm_compL_le ℝ E E E
    _ = ‖g‖ := one_mul _

/-- **Coefficient of the fundamental-solution (matrix) ODE.** Working in the Banach algebra
`F = E →L[ℝ] E`, Lee's parallelism ODE `V̇ = −Γ(u̇, V)(c)` becomes the linear matrix ODE
`Φ̇(t) = 𝔸(t) Φ(t)` whose coefficient `𝔸(t) : F →L[ℝ] F` is left-composition by
`A(t) = −chartGammaRight cov e b (u̇ t) (c t)`.  Concretely
`𝔸(t) Ψ = A(t) ∘L Ψ = (compL ℝ E E E) (A t) Ψ`. -/
def chartMatrixCoeff (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (u : ℝ → E) (c : ℝ → M) (t : ℝ) :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  ContinuousLinearMap.compL ℝ E E E (-chartGammaRight cov e b (deriv u t) (c t))

theorem chartMatrixCoeff_apply (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (t : ℝ) (Ψ : E →L[ℝ] E) :
    chartMatrixCoeff cov e b u c t Ψ = (-chartGammaRight cov e b (deriv u t) (c t)) ∘L Ψ := by
  rw [chartMatrixCoeff, ContinuousLinearMap.compL_apply]

/-- The matrix-ODE coefficient is continuous on any set on which the parallel-transport
coefficient `chartGammaRight` is continuous (left-composition `compL` is a continuous linear
map). -/
theorem continuousOn_chartMatrixCoeff (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {s : Set ℝ}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) s) :
    ContinuousOn (chartMatrixCoeff cov e b u c) s :=
  (ContinuousLinearMap.compL ℝ E E E).continuous.comp_continuousOn hcont.neg

/-- The matrix-ODE coefficient inherits the operator-norm bound `K` of the
parallel-transport coefficient `chartGammaRight` (left-composition is norm-nonincreasing). -/
theorem nnnorm_chartMatrixCoeff_le (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} {K : ℝ≥0}
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) :
    ∀ t ∈ Icc t₀ t₁, ‖chartMatrixCoeff cov e b u c t‖₊ ≤ K := fun t ht => by
  refine le_trans (nnnorm_compL_apply_le _) ?_
  rw [nnnorm_neg]
  exact hK t ht

/-- **The fundamental solution `Φ` of Lee's parallel-transport ODE, in a chart.** In the
Banach algebra `F = E →L[ℝ] E`, `Φ` is the unique solution of the matrix ODE
`Φ̇(t) = 𝔸(t) Φ(t) = A(t) ∘L Φ(t)` on `[t₀, t₁]` with `Φ(t₀) = 1` (the identity map).  Its
columns are the parallel fields: `t ↦ Φ(t) w` is the parallel transport of `w ∈ E` starting
from `t₀` (`chartFundamentalSolution_parallel`).  Built from the global linear-ODE engine
`solOf` applied over `F`, which is a `CompleteSpace` because `E` is. -/
def chartFundamentalSolution (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : ℝ≥0}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) : ℝ → (E →L[ℝ] E) :=
  solOf (A := chartMatrixCoeff cov e b u c) ht
    (continuousOn_chartMatrixCoeff cov u c hcont) (nnnorm_chartMatrixCoeff_le cov u c hK)
    (1 : E →L[ℝ] E)

/-- The fundamental solution is the identity at the initial time `t₀`. -/
theorem chartFundamentalSolution_left (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : ℝ≥0}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) :
    chartFundamentalSolution cov u c ht hcont hK t₀ = 1 :=
  solOf_left _ _ _ _

/-- The fundamental solution solves the matrix ODE `Φ̇(t) = 𝔸(t) Φ(t)` on `[t₀, t₁]`. -/
theorem chartFundamentalSolution_isSolOn (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : ℝ≥0}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) :
    IsSolOn (chartMatrixCoeff cov e b u c) t₀ t₁ (chartFundamentalSolution cov u c ht hcont hK) :=
  solOf_isSolOn _ _ _ _

/-- **The columns of the fundamental solution are parallel fields.** For any `w ∈ E`, the
curve `t ↦ Φ(t) w` solves Lee's parallelism ODE `V̇(t) = −Γ(u̇ t, V t)(c t)` on `[t₀, t₁]`;
with `Φ(t₀) w = w` this exhibits `Φ(t) w` as the parallel transport of `w` from `t₀` to `t`. -/
theorem chartFundamentalSolution_parallel (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : ℝ≥0}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) (w : E) :
    ∀ t ∈ Icc t₀ t₁,
      HasDerivWithinAt (fun t => chartFundamentalSolution cov u c ht hcont hK t w)
        (-chartGamma cov e b (deriv u t) (chartFundamentalSolution cov u c ht hcont hK t w) (c t))
        (Icc t₀ t₁) t := by
  intro t ht'
  have hsol := chartFundamentalSolution_isSolOn cov u c ht hcont hK t ht'
  have h := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp_hasDerivWithinAt t hsol
  simp only [ContinuousLinearMap.apply_apply, chartMatrixCoeff_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, chartGammaRight_apply] at h
  exact h

/-- **Derivative of the inverse fundamental solution applied to a vector field.** Core
computation behind Lee's Theorem 4.34.  If `Φ` is a fundamental solution normalized at `t₀`
(`Φ t₀ = 1`) with `Φ̇(t₀) = −chartGammaRight cov e b (u̇ t₀)(c t₀)` (the value forced by the
matrix ODE at `t₀`, since `Φ(t₀) = 1`), and `V` is differentiable at `t₀`, then the "transport
back to `t₀`" field `W(t) = Φ(t)⁻¹ V(t)` has derivative Lee's covariant derivative
`D_t V(t₀)` at `t₀`.  The proof differentiates `t ↦ Ring.inverse (Φ t)` at the unit
`Φ t₀ = 1` (via `hasFDerivAt_ringInverse`, whose derivative there is `H ↦ −H`) and applies the
product rule `HasDerivAt.clm_apply`. -/
theorem hasDerivAt_ringInverse_apply
    (cov : Connection I E (TangentSpace I : M → Type _)) (u : ℝ → E) (c : ℝ → M)
    {t₀ : ℝ} {Φ : ℝ → (E →L[ℝ] E)} {V : ℝ → E}
    (hΦ0 : Φ t₀ = 1)
    (hΦ : HasDerivAt Φ (-chartGammaRight cov e b (deriv u t₀) (c t₀)) t₀)
    (hV : DifferentiableAt ℝ V t₀) :
    HasDerivAt (fun t => Ring.inverse (Φ t) (V t))
      (covariantDerivAlongChart cov e b u c V t₀) t₀ := by
  letI : NormedRing (E →L[ℝ] E) := ContinuousLinearMap.toNormedRing
  letI : NormedAlgebra ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedAlgebra
  have hinv := hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (E →L[ℝ] E)ˣ)
  rw [Units.val_one, ← hΦ0] at hinv
  have hΨ := hinv.comp_hasDerivAt t₀ hΦ
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one,
    Units.val_one, one_mul, mul_one, neg_neg] at hΨ
  have hW := hΨ.clm_apply hV.hasDerivAt
  simp only [Function.comp_apply, hΦ0, Ring.inverse_one, ContinuousLinearMap.one_apply,
    chartGammaRight_apply] at hW
  rw [covariantDerivAlongChart_def, add_comm]
  exact hW

/-- **The fundamental solution is invertible at every time.** Each value `Φ(t)` of the chart
fundamental solution is a unit of `E →L[ℝ] E` (a linear isomorphism): if `Φ(t) w = 0` then the
parallel field `τ ↦ Φ(τ) w`, which equals `w` at `t₀`, agrees with the zero field on `[t₀, t]`
by backward Grönwall uniqueness (`IsSolOn.eqOn_of_right`), forcing `w = 0`; an injective
endomorphism of a finite-dimensional space is bijective, hence a unit
(`ContinuousLinearMap.isUnit_iff_bijective`).  Invertibility of `Φ(t)` is what lets us transport
`V(t)` *back* to `t₀` via `Ring.inverse (Φ t)`. -/
theorem isUnit_chartFundamentalSolution (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : ℝ≥0}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K)
    {t : ℝ} (htmem : t ∈ Icc t₀ t₁) :
    IsUnit (chartFundamentalSolution cov u c ht hcont hK t) := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  set Φ := chartFundamentalSolution cov u c ht hcont hK with hΦdef
  set A_E : ℝ → E →L[ℝ] E := fun τ => -chartGammaRight cov e b (deriv u τ) (c τ) with hA_E
  have hsub : Icc t₀ t ⊆ Icc t₀ t₁ := Icc_subset_Icc le_rfl htmem.2
  have hinj : Function.Injective ⇑(Φ t) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have hpar := chartFundamentalSolution_parallel cov u c ht hcont hK w
    have hs₁ : IsSolOn A_E t₀ t (fun τ => Φ τ w) := by
      intro τ hτ
      have hd := (hpar τ (hsub hτ)).mono hsub
      show HasDerivWithinAt (fun τ => Φ τ w) (A_E τ (Φ τ w)) (Icc t₀ t) τ
      rw [hA_E]
      simpa only [ContinuousLinearMap.neg_apply, chartGammaRight_apply] using hd
    have hs₂ : IsSolOn A_E t₀ t (0 : ℝ → E) := by
      intro τ hτ
      simpa only [Pi.zero_apply, map_zero] using hasDerivWithinAt_const τ (Icc t₀ t) (0 : E)
    have hKA : ∀ τ ∈ Icc t₀ t, ‖A_E τ‖₊ ≤ K := fun τ hτ => by
      rw [hA_E]; simpa only [nnnorm_neg] using hK τ (hsub hτ)
    have hend : (fun τ => Φ τ w) t = (0 : ℝ → E) t := by simpa using hw
    have heq := IsSolOn.eqOn_of_right hKA hs₁ hs₂ hend
    have h0 := heq (left_mem_Icc.mpr htmem.1)
    have hΦ0 : Φ t₀ = 1 := chartFundamentalSolution_left cov u c ht hcont hK
    simpa only [hΦ0, ContinuousLinearMap.one_apply, Pi.zero_apply] using h0
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (Φ t).toLinearMap)).mp hinj⟩

end

end LeeLib.Ch04

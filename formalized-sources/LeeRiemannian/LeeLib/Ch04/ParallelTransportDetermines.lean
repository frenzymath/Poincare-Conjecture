/-
Chapter 4, "Connections": **parallel transport along piecewise-smooth curves**
(Lee, Corollary 4.33), in chart coordinates.

Building on `LeeLib.Ch04.ParallelTransport` (single-chart existence/uniqueness of
parallel transport, via the global linear-ODE engine of `LeeLib.Ch04.LinearODE`)
this file glues the chart-local segments into a piecewise-smooth transport:

* Piecewise gluing at the abstract linear-ODE level (`exists_isSolOn_pieces`): given
  a partition `a 0 ≤ a 1 ≤ … ≤ a k` and a coefficient `A : ℝ → (E →L[ℝ] E)` that is
  continuous and operator-norm bounded on *each* segment `[a i, a (i+1)]` (but possibly
  discontinuous at the breakpoints), for any initial value there is a solution of
  `V̇ = A(t) V` on the whole interval `[a 0, a k]`, obtained by concatenating the
  per-segment solutions.

* `exists_isPiecewiseParallelAlongChart_Icc` / `isPiecewiseParallelAlongChart_eqOn_Icc`
  — Lee's Corollary 4.33: parallel transport along a *piecewise-smooth* curve exists
  (by concatenating chart-local parallel fields, each solving Lee's parallelism ODE
  `V̇ = −Γ(u̇, V)(c)`) and is unique (by propagating the per-segment Grönwall uniqueness
  `isParallelAlongChart_eqOn_Icc` across the breakpoints).

The follow-up "parallel transport *determines* the connection" (Thm 4.34 / Cor 4.35)
— the difference-quotient limit `D_t V(t₀) = limₜ (P_{t t₀} V(t) − V(t₀))/(t − t₀)` —
is left for a later file; it needs the fundamental-solution `Ψ` of the matrix ODE
`Ψ̇ = −Γ(u̇, ·)(c) ∘ Ψ` and its local invertibility.
-/
import LeeLib.Ch04.ParallelTransport
import Mathlib.Analysis.Calculus.FDeriv.Mul

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

/-! ## Piecewise gluing at the linear-ODE level (Lee, Corollary 4.33)

A partition `a 0 ≤ a 1 ≤ … ≤ a k` with a coefficient continuous and bounded on each
segment (but possibly jumping at breakpoints) still admits a global solution of
`V̇ = A(t) V` on `[a 0, a k]`, obtained by concatenating the per-segment solutions. -/

/-- Monotonicity of a partition from its consecutive-step inequalities: if
`a j ≤ a (j+1)` for every `j < k`, then `a i ≤ a j` whenever `i ≤ j ≤ k`. -/
private theorem partition_le_of_le {a : ℕ → ℝ} {k : ℕ} (h : ∀ j, j < k → a j ≤ a (j + 1)) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ k → a i ≤ a j := by
  intro i j hij
  induction hij with
  | refl => intro _; exact le_rfl
  | @step m _ ih =>
      intro hmk
      exact (ih (Nat.le_of_succ_le hmk)).trans (h m hmk)

/-- **Piecewise existence for a linear ODE** (the analytic core of Lee's Corollary 4.33).
Given a partition `a 0 ≤ … ≤ a k` and a coefficient `A : ℝ → (E →L[ℝ] E)` that is continuous
and (per segment) operator-norm bounded on each `[a i, a (i+1)]`, for any initial value `x₀`
there is a curve `V` with `V (a 0) = x₀` solving `V̇ = A(t) V` on the whole interval
`[a 0, a k]`.  Proof: solve each segment with the single-interval engine
`exists_hasDerivWithinAt_Icc` and glue consecutive segments with
`exists_hasDerivWithinAt_glue`, inducting on the number of segments. -/
theorem exists_isSolOn_pieces {a : ℕ → ℝ} (A : ℝ → E →L[ℝ] E) (x₀ : E) :
    ∀ {k : ℕ}, (∀ i, i < k → a i ≤ a (i + 1)) →
      (∀ i, i < k → ContinuousOn A (Icc (a i) (a (i + 1)))) →
      (∀ i, i < k → ∃ K : ℝ≥0, ∀ t ∈ Icc (a i) (a (i + 1)), ‖A t‖₊ ≤ K) →
      ∃ V : ℝ → E, V (a 0) = x₀ ∧ IsSolOn A (a 0) (a k) V := by
  intro k
  induction k with
  | zero =>
    intro _ _ _
    refine ⟨fun _ => x₀, rfl, fun t _ => ?_⟩
    exact HasFDerivWithinAt.of_subsingleton (by rw [Set.Icc_self]; exact Set.subsingleton_singleton)
  | succ n ih =>
    intro hmono hcont hbound
    obtain ⟨V₁, hV₁0, hV₁sol⟩ := ih (fun i hi => hmono i (Nat.lt_succ_of_lt hi))
      (fun i hi => hcont i (Nat.lt_succ_of_lt hi)) (fun i hi => hbound i (Nat.lt_succ_of_lt hi))
    obtain ⟨K, hK⟩ := hbound n (Nat.lt_succ_self n)
    obtain ⟨V₂, hV₂0, hV₂sol⟩ := exists_hasDerivWithinAt_Icc (hmono n (Nat.lt_succ_self n)) A
      (V₁ (a n)) (hcont n (Nat.lt_succ_self n)) hK
    have ha0n : a 0 ≤ a n := partition_le_of_le hmono (Nat.zero_le n) (Nat.le_succ n)
    obtain ⟨V, hVa, hVd⟩ := exists_hasDerivWithinAt_glue ha0n (hmono n (Nat.lt_succ_self n)) A
      hV₁sol hV₂sol hV₂0
    exact ⟨V, hVa.trans hV₁0, hVd⟩

/-- **Parallel transport along a piecewise-smooth curve** (Lee, Corollary 4.33), existence.
For a partition `a 0 ≤ … ≤ a k` of the parameter interval and a curve that on each segment
`[a i, a (i+1)]` is continuous into the chart domain with `C¹` coordinate velocity, and a
`C¹` connection on the chart, any initial vector `V₀` extends to a coordinate vector field `V`
with `V (a 0) = V₀` that is parallel along each smooth segment (`D_t V = 0`, i.e. Lee's
parallelism ODE `V̇ = −Γ(u̇, V)(c)`).  The field is obtained by concatenating the chart-local
parallel fields of each segment (`exists_isSolOn_pieces`). -/
theorem exists_isPiecewiseParallelAlongChart_Icc
    (cov : Connection I E (TangentSpace I : M → Type _)) (u : ℝ → E) (c : ℝ → M)
    {a : ℕ → ℝ} {k : ℕ} (hmono : ∀ i, i < k → a i ≤ a (i + 1))
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet)
    (hc : ∀ i, i < k → ContinuousOn c (Icc (a i) (a (i + 1))))
    (hcmem : ∀ i, i < k → MapsTo c (Icc (a i) (a (i + 1))) e.baseSet)
    (hu : ∀ i, i < k → ContinuousOn (deriv u) (Icc (a i) (a (i + 1)))) (V₀ : E) :
    ∃ V : ℝ → E, V (a 0) = V₀ ∧
      ∀ i, i < k → ∀ t ∈ Icc (a i) (a (i + 1)),
        HasDerivWithinAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) (Icc (a i) (a (i + 1))) t := by
  set A : ℝ → E →L[ℝ] E := fun t => -chartGammaRight cov e b (deriv u t) (c t) with hA
  have hcontA : ∀ i, i < k → ContinuousOn A (Icc (a i) (a (i + 1))) := fun i hi =>
    (continuousOn_chartGammaRight cov u c hcov (hc i hi) (hcmem i hi) (hu i hi)).neg
  have hbound : ∀ i, i < k → ∃ K : ℝ≥0, ∀ t ∈ Icc (a i) (a (i + 1)), ‖A t‖₊ ≤ K := fun i hi => by
    obtain ⟨K, hK⟩ := exists_nnnorm_chartGammaRight_bound (b := b) cov u c (hmono i hi) hcov
      (hc i hi) (hcmem i hi) (hu i hi)
    exact ⟨K, fun t ht => by rw [hA]; simpa using hK t ht⟩
  obtain ⟨V, hV0, hVsol⟩ := exists_isSolOn_pieces A V₀ hmono hcontA hbound
  refine ⟨V, hV0, fun i hi t ht => ?_⟩
  have hsub : Icc (a i) (a (i + 1)) ⊆ Icc (a 0) (a k) :=
    Icc_subset_Icc (partition_le_of_le hmono (Nat.zero_le i) (le_of_lt hi))
      (partition_le_of_le hmono hi le_rfl)
  have hd := (hVsol t (hsub ht)).mono hsub
  rw [hA] at hd
  simpa only [ContinuousLinearMap.neg_apply, chartGammaRight_apply] using hd

/-- **Uniqueness of parallel transport along a piecewise-smooth curve** (Lee, Corollary 4.33).
Two coordinate vector fields that are parallel along each smooth segment `[a i, a (i+1)]`
(Lee's parallelism ODE) and agree at the initial parameter `a 0` agree on *every* segment.
Proof: forward Grönwall uniqueness (`isParallelAlongChart_eqOn_Icc`) on each segment,
inducting on the segment index to propagate agreement across the breakpoints. -/
theorem isPiecewiseParallelAlongChart_eqOn_Icc
    (cov : Connection I E (TangentSpace I : M → Type _)) (u : ℝ → E) (c : ℝ → M)
    {a : ℕ → ℝ} {k : ℕ} (hmono : ∀ i, i < k → a i ≤ a (i + 1))
    (hbound : ∀ i, i < k →
      ∃ K : ℝ≥0, ∀ t ∈ Icc (a i) (a (i + 1)), ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K)
    {V W : ℝ → E}
    (hV : ∀ i, i < k → ∀ t ∈ Icc (a i) (a (i + 1)),
      HasDerivWithinAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) (Icc (a i) (a (i + 1))) t)
    (hW : ∀ i, i < k → ∀ t ∈ Icc (a i) (a (i + 1)),
      HasDerivWithinAt W (-chartGamma cov e b (deriv u t) (W t) (c t)) (Icc (a i) (a (i + 1))) t)
    (ha : V (a 0) = W (a 0)) :
    ∀ i, i < k → EqOn V W (Icc (a i) (a (i + 1))) := by
  have hnode : ∀ i, i ≤ k → V (a i) = W (a i) := by
    intro i
    induction i with
    | zero => intro _; exact ha
    | succ n ihn =>
      intro hik
      have hn : n < k := hik
      obtain ⟨K, hK⟩ := hbound n hn
      have heq := isParallelAlongChart_eqOn_Icc cov u c hK (hV n hn) (hW n hn)
        (ihn (Nat.le_of_succ_le hik))
      exact heq ⟨hmono n hn, le_rfl⟩
  intro i hi
  obtain ⟨K, hK⟩ := hbound i hi
  exact isParallelAlongChart_eqOn_Icc cov u c hK (hV i hi) (hW i hi) (hnode i (le_of_lt hi))

end

end LeeLib.Ch04

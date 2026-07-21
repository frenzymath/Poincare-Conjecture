/-
Chapter 4, "Connections", §"Parallel Transport": the chart-local existence,
uniqueness, and linear-isomorphism structure of parallel transport, for an
abstract connection `∇` in `TM`.

Lee (Theorem 4.32) reduces parallel transport to a first-order **linear** ODE:
in a chart, a vector field `V` along a curve `γ` is parallel (`D_t V = 0`) iff its
frame components satisfy Lee's equation (4.19)

  `V̇^k(t) = − V^j(t) γ̇^i(t) Γ^k_{ij}(γ(t))`,

a linear system `V̇ = −Γ(γ̇, V)(γ)` in the coordinate vector `V(t) ∈ E`.  The
existence and uniqueness of parallel transport on the *whole* parameter interval
(Lee's key improvement over generic ODE short-time theory) is exactly the global
linear-ODE theory of `LeeLib.Ch04.LinearODE` (Theorem 4.31), and the resulting
endpoint map is a linear isomorphism.

This file packages that content for the connection's chart Christoffel contraction
`chartGamma` (built from the chart connection coefficients `chartConnectionCoeff`
of `LeeLib.Ch04.ChartConnection`):

* `chartGamma cov e b v w y = ∑_k (∑_{i,j} Γ^k_{ij}(y) vⁱ wʲ) b_k` — the bilinear
  Christoffel contraction, read in the trivialization frame `e.localFrame b`.
* `chartGamma_add_right` / `chartGamma_smul_right` (and the left versions) — its
  bilinearity; `chartGammaRight cov e b v y : E →L[ℝ] E` — the ODE coefficient CLM.
* `covariantDerivAlongChart` / `IsParallelAlongChart` — Lee's `D_t V` and the
  parallelism predicate `D_t V = 0`, in chart coordinates.
* `isParallelAlongChart_iff_hasDerivAt` — the solved ODE form `V̇ = −Γ(u̇, V)(u)`.
* `exists_isParallelAlongChart_Icc` / `isParallelAlongChart_eqOn_Icc` — existence
  (via `exists_hasDerivWithinAt_Icc`) and uniqueness (via
  `IsSolOn.eqOn_of_left`) on any compact interval, Lee's single-chart
  case of Theorem 4.32.
* `chartParallelTransport cov e b u c hab hcont hK : E ≃ₗ[ℝ] E` — the parallel
  transport map `P^γ_{t₀t₁}` read in the chart, a linear isomorphism (via
  `flowMap` and `flowMap_injective`).
* `continuousOn_chartGammaRight` / `exists_nnnorm_chartGammaRight_bound` — the ODE
  coefficient is continuous and (on a compact interval) bounded when the connection
  is `C¹` on the chart and the curve is `C¹` there, so
  `exists_isParallelAlongChart_Icc_of_contMDiff` supplies parallel transport with the
  `hcont`/`hK` hypotheses discharged automatically.
-/
import LeeLib.Ch04.ChartConnection
import LeeLib.Ch04.LinearODE
import Mathlib.Analysis.ODE.Gronwall

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

/-- **Chart Christoffel contraction** of a connection `∇` in `TM`, read in the
trivialization frame `(∂_i) = e.localFrame b`.  For coordinate vectors `v, w : E`
(frame components `vⁱ = b.repr v i`) and a base point `y : M`, this is Lee's
bilinear contraction
`Γ(v, w)(y) = ∑_k (∑_{i,j} Γ^k_{ij}(y) vⁱ wʲ) b_k`,
the right-hand-side data of Lee's parallel-transport equation (4.19) and geodesic
equation (4.16). -/
def chartGamma (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (v w : E) (y : M) : E :=
  ∑ k, (∑ i, ∑ j, chartConnectionCoeff cov e b i j k y * b.repr v i * b.repr w j) • b k

theorem chartGamma_def (cov : Connection I E (TangentSpace I : M → Type _))
    (v w : E) (y : M) :
    chartGamma cov e b v w y
      = ∑ k, (∑ i, ∑ j, chartConnectionCoeff cov e b i j k y * b.repr v i * b.repr w j) • b k :=
  rfl

/-- The chart Christoffel contraction is additive in its second (vector-field) slot. -/
theorem chartGamma_add_right (cov : Connection I E (TangentSpace I : M → Type _))
    (v w w' : E) (y : M) :
    chartGamma cov e b v (w + w') y = chartGamma cov e b v w y + chartGamma cov e b v w' y := by
  simp only [chartGamma_def, map_add, Finsupp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The chart Christoffel contraction is homogeneous in its second (vector-field) slot. -/
theorem chartGamma_smul_right (cov : Connection I E (TangentSpace I : M → Type _))
    (v : E) (a : ℝ) (w : E) (y : M) :
    chartGamma cov e b v (a • w) y = a • chartGamma cov e b v w y := by
  simp only [chartGamma_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The chart Christoffel contraction is additive in its first (direction) slot. -/
theorem chartGamma_add_left (cov : Connection I E (TangentSpace I : M → Type _))
    (v v' w : E) (y : M) :
    chartGamma cov e b (v + v') w y = chartGamma cov e b v w y + chartGamma cov e b v' w y := by
  simp only [chartGamma_def, map_add, Finsupp.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← add_smul]
  congr 1
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The chart Christoffel contraction is homogeneous in its first (direction) slot. -/
theorem chartGamma_smul_left (cov : Connection I E (TangentSpace I : M → Type _))
    (a : ℝ) (v w : E) (y : M) :
    chartGamma cov e b (a • v) w y = a • chartGamma cov e b v w y := by
  simp only [chartGamma_def, map_smul, Finsupp.smul_apply, smul_eq_mul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul]
  congr 1
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The coefficient of Lee's parallel-transport ODE**, as a continuous linear map.
For a fixed direction `v` and base point `y`, the map `w ↦ Γ(v, w)(y)` is linear
(`chartGamma_add_right` / `chartGamma_smul_right`), hence continuous since `E` is
finite-dimensional.  Lee's parallelism equation (4.19) is `V̇ = −chartGammaRight (γ̇) (γ) V`. -/
def chartGammaRight (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (v : E) (y : M) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => chartGamma cov e b v w y
      map_add' := fun w w' => chartGamma_add_right cov v w w' y
      map_smul' := fun a w => by
        rw [RingHom.id_apply]; exact chartGamma_smul_right cov v a w y }

@[simp] theorem chartGammaRight_apply (cov : Connection I E (TangentSpace I : M → Type _))
    (v : E) (y : M) (w : E) :
    chartGammaRight cov e b v y w = chartGamma cov e b v w y := rfl

/-- The right-hand side of Lee's parallel-transport ODE is globally Lipschitz in the
vector-field slot, with the operator norm of `chartGammaRight` as an explicit constant.
This is the uniform bound that Grönwall's inequality turns into uniqueness. -/
theorem lipschitzWith_neg_chartGamma (cov : Connection I E (TangentSpace I : M → Type _))
    (v : E) (y : M) :
    LipschitzWith ‖chartGammaRight cov e b v y‖₊ (fun w => -chartGamma cov e b v w y) := by
  have h := (chartGammaRight cov e b v y).lipschitz.neg
  simpa only [chartGammaRight_apply] using h

/-- **CLM decomposition of the parallel-transport coefficient**: the ODE coefficient
`chartGammaRight cov e b v y` is a finite sum of the *fixed* rank-one continuous linear
maps `(∂_j)^* ↦ ∂_k` weighted by the scalar coefficients `Γ^k_{ij}(y) vⁱ`.  This exhibits
its dependence on `(v, y)` through continuous scalars only, which yields continuity of the
coefficient along a curve (`continuousOn_chartGammaRight`). -/
theorem chartGammaRight_eq_sum (cov : Connection I E (TangentSpace I : M → Type _))
    (v : E) (y : M) :
    chartGammaRight cov e b v y
      = ∑ k, ∑ i, ∑ j, (chartConnectionCoeff cov e b i j k y * b.repr v i)
          • ((b.coord j).toContinuousLinearMap.smulRight (b k)) := by
  ext w
  simp only [chartGammaRight_apply, chartGamma_def, ContinuousLinearMap.coe_sum',
    Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, LinearMap.coe_toContinuousLinearMap',
    Basis.coord_apply, Finset.sum_smul, smul_smul]

/-- **Continuity of the parallel-transport coefficient along a curve.**  If the connection
is `C¹` on the chart domain `e.baseSet` (`hcov`), the base curve `c` is continuous into
`e.baseSet`, and the coordinate velocity `u̇` is continuous, then the ODE coefficient
`t ↦ chartGammaRight cov e b (u̇ t) (c t)` is continuous.  (The chart Christoffel symbols
`Γ^k_{ij}` are continuous on `e.baseSet` by `chartConnectionCoeff_contMDiffOn`; the
coefficient is a finite sum of these scalars times fixed rank-one maps, via
`chartGammaRight_eq_sum`.)  This discharges the `hcont` hypothesis of the parallel-transport
theorems in the presence of a `C¹` connection and a `C¹` curve staying in one chart. -/
theorem continuousOn_chartGammaRight (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {s : Set ℝ}
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet)
    (hc : ContinuousOn c s) (hcmem : MapsTo c s e.baseSet)
    (hu : ContinuousOn (deriv u) s) :
    ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) s := by
  simp only [chartGammaRight_eq_sum]
  refine continuousOn_finsetSum _ fun k _ => continuousOn_finsetSum _ fun i _ =>
    continuousOn_finsetSum _ fun j _ => ?_
  refine ContinuousOn.smul (ContinuousOn.mul ?_ ?_) continuousOn_const
  · exact ((chartConnectionCoeff_contMDiffOn cov hcov i j k).continuousOn).comp hc hcmem
  · have : (fun t => b.repr (deriv u t) i) = fun t => (b.coord i) (deriv u t) := by
      funext t; rw [Basis.coord_apply]
    rw [this]
    exact (b.coord i).continuous_of_finiteDimensional.comp_continuousOn hu

/-- **Operator-norm bound for the parallel-transport coefficient on a compact interval.**
Continuity of the coefficient (`continuousOn_chartGammaRight`) on the compact interval
`[t₀, t₁]` yields a uniform operator-norm bound `K`, discharging the `hK` hypothesis of the
parallel-transport theorems from the `C¹` connection and a `C¹` curve staying in one chart. -/
theorem exists_nnnorm_chartGammaRight_bound (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet)
    (hc : ContinuousOn c (Icc t₀ t₁)) (hcmem : MapsTo c (Icc t₀ t₁) e.baseSet)
    (hu : ContinuousOn (deriv u) (Icc t₀ t₁)) :
    ∃ K : NNReal, ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K := by
  have hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁) :=
    continuousOn_chartGammaRight cov u c hcov hc hcmem hu
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨Real.toNNReal C, fun t htmem => ?_⟩
  have h0 : (0 : ℝ) ≤ C := le_trans (norm_nonneg _) (hC t₀ ⟨le_rfl, ht⟩)
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal C h0]
  exact hC t htmem

/-- **Lee's covariant derivative along a curve, in chart coordinates** (Theorem 4.24,
equation (4.15)).  For a coordinate curve `u : ℝ → E` (the chart image of a curve `γ`)
staying over the base curve `c : ℝ → M`, and a coordinate vector field `V : ℝ → E` along
it, `D_t V = V̇ + Γ(u̇, V)(c)`. -/
def covariantDerivAlongChart (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (u : ℝ → E) (c : ℝ → M) (V : ℝ → E) (t : ℝ) : E :=
  deriv V t + chartGamma cov e b (deriv u t) (V t) (c t)

@[simp] theorem covariantDerivAlongChart_def (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (V : ℝ → E) (t : ℝ) :
    covariantDerivAlongChart cov e b u c V t
      = deriv V t + chartGamma cov e b (deriv u t) (V t) (c t) := rfl

/-- **Lee's Theorem 4.24 (i)**: the covariant derivative along a curve is additive in the
vector field, `D_t (V + W) = D_t V + D_t W`, at points where `V` and `W` are differentiable. -/
theorem covariantDerivAlongChart_add (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (V W : ℝ → E) {t : ℝ}
    (hV : DifferentiableAt ℝ V t) (hW : DifferentiableAt ℝ W t) :
    covariantDerivAlongChart cov e b u c (V + W) t
      = covariantDerivAlongChart cov e b u c V t + covariantDerivAlongChart cov e b u c W t := by
  simp only [covariantDerivAlongChart_def, Pi.add_apply, deriv_add hV hW, chartGamma_add_right]
  abel

/-- **Lee's Theorem 4.24 (ii)**: the product rule for the covariant derivative along a curve,
`D_t (f • V) = ḟ • V + f • D_t V`, for a scalar `f : ℝ → ℝ` differentiable along the curve. -/
theorem covariantDerivAlongChart_smul (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (f : ℝ → ℝ) (V : ℝ → E) {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hV : DifferentiableAt ℝ V t) :
    covariantDerivAlongChart cov e b u c (f • V) t
      = deriv f t • V t + f t • covariantDerivAlongChart cov e b u c V t := by
  simp only [covariantDerivAlongChart_def, Pi.smul_apply', deriv_smul hf hV,
    chartGamma_smul_right, smul_add]
  abel

/-- **Parallel field along a curve, in chart coordinates** (Lee's `D_t V = 0`). -/
def IsParallelAlongChart (cov : Connection I E (TangentSpace I : M → Type _))
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] (b : Basis ι ℝ E) (u : ℝ → E) (c : ℝ → M) (V : ℝ → E) : Prop :=
  ∀ t, covariantDerivAlongChart cov e b u c V t = 0

/-- **Lee's parallel-transport equation (4.19)**, solved form: `V` is parallel along the
curve iff it solves the first-order linear system `V̇(t) = −Γ(u̇(t), V(t))(c(t))`. -/
theorem isParallelAlongChart_iff_hasDerivAt (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) (V : ℝ → E) (hV : ∀ t, DifferentiableAt ℝ V t) :
    IsParallelAlongChart cov e b u c V ↔
      ∀ t, HasDerivAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) t := by
  constructor
  · intro h t
    have hd : deriv V t = -chartGamma cov e b (deriv u t) (V t) (c t) :=
      eq_neg_iff_add_eq_zero.mpr (h t)
    rw [← hd]; exact (hV t).hasDerivAt
  · intro h t
    simp only [covariantDerivAlongChart_def]
    rw [(h t).deriv]; abel

/-- **Existence of parallel transport** (Lee, Theorem 4.32, single-chart case).  On any
compact interval `[t₀, t₁]`, for any initial vector `V₀` there is a coordinate vector
field `V` along the curve with `V t₀ = V₀` solving Lee's parallelism ODE `V̇ = −Γ(u̇, V)(c)`.
Because the ODE is linear, the solution exists on *all* of `[t₀, t₁]` (via the global
linear-ODE engine `exists_hasDerivWithinAt_Icc`), not merely for a short time. -/
theorem exists_isParallelAlongChart_Icc (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (V₀ : E) {K : NNReal}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) :
    ∃ V : ℝ → E, V t₀ = V₀ ∧
      ∀ t ∈ Icc t₀ t₁,
        HasDerivWithinAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) (Icc t₀ t₁) t := by
  set A : ℝ → E →L[ℝ] E := fun t => -chartGammaRight cov e b (deriv u t) (c t) with hA
  obtain ⟨V, hV0, hVd⟩ := exists_hasDerivWithinAt_Icc ht A V₀ hcont.neg
    (fun t ht => by rw [hA]; simpa using hK t ht)
  refine ⟨V, hV0, fun t ht => ?_⟩
  have := hVd t ht
  rwa [hA, ContinuousLinearMap.neg_apply, chartGammaRight_apply] at this

/-- **Existence of parallel transport from connection smoothness** (Lee, Theorem 4.32,
single-chart case, fully discharged form).  For a `C¹` connection on the chart domain, a base
curve `c` continuous into the chart, and a `C¹` coordinate velocity `u̇`, there is a parallel
field with any prescribed initial value on `[t₀, t₁]`; the continuity/boundedness of the ODE
coefficient (`hcont`/`hK`) are supplied automatically by `continuousOn_chartGammaRight` and
`exists_nnnorm_chartGammaRight_bound`. -/
theorem exists_isParallelAlongChart_Icc_of_contMDiff
    (cov : Connection I E (TangentSpace I : M → Type _)) (u : ℝ → E) (c : ℝ → M)
    {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) (V₀ : E)
    (hcov : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet)
    (hc : ContinuousOn c (Icc t₀ t₁)) (hcmem : MapsTo c (Icc t₀ t₁) e.baseSet)
    (hu : ContinuousOn (deriv u) (Icc t₀ t₁)) :
    ∃ V : ℝ → E, V t₀ = V₀ ∧
      ∀ t ∈ Icc t₀ t₁,
        HasDerivWithinAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) (Icc t₀ t₁) t := by
  obtain ⟨K, hK⟩ := exists_nnnorm_chartGammaRight_bound (b := b) cov u c ht hcov hc hcmem hu
  have hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁) :=
    continuousOn_chartGammaRight cov u c hcov hc hcmem hu
  exact exists_isParallelAlongChart_Icc cov u c ht V₀ hcont hK

/-- **Uniqueness of parallel transport** (Lee, Theorem 4.32, single-chart case).  Two
solutions of Lee's parallelism ODE on `[t₀, t₁]` that agree at the left endpoint `t₀`
agree on all of `[t₀, t₁]` (forward Grönwall uniqueness, `IsSolOn.eqOn_of_left`). -/
theorem isParallelAlongChart_eqOn_Icc (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K)
    {V W : ℝ → E}
    (hVd : ∀ t ∈ Icc t₀ t₁,
      HasDerivWithinAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) (Icc t₀ t₁) t)
    (hWd : ∀ t ∈ Icc t₀ t₁,
      HasDerivWithinAt W (-chartGamma cov e b (deriv u t) (W t) (c t)) (Icc t₀ t₁) t)
    (ha : V t₀ = W t₀) :
    EqOn V W (Icc t₀ t₁) := by
  set A : ℝ → E →L[ℝ] E := fun t => -chartGammaRight cov e b (deriv u t) (c t) with hA
  have hKA : ∀ t ∈ Icc t₀ t₁, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  have hval : ∀ (t : ℝ) (w : E), A t w = -chartGamma cov e b (deriv u t) w (c t) := fun t w => by
    rw [hA]; simp only [ContinuousLinearMap.neg_apply, chartGammaRight_apply]
  have hVsol : IsSolOn A t₀ t₁ V := fun t ht => by rw [hval]; exact hVd t ht
  have hWsol : IsSolOn A t₀ t₁ W := fun t ht => by rw [hval]; exact hWd t ht
  exact IsSolOn.eqOn_of_left hKA hVsol hWsol ha

/-- **The parallel transport map** `P^γ_{t₀t₁}` read in the chart (Lee, equation (4.22)):
the linear isomorphism `V₀ ↦ V(t₁)` sending an initial vector at time `t₀` to the value at
time `t₁` of the unique parallel field along the curve with that initial value.  Linearity
and injectivity come from the linear-ODE flow (`flowMap`, `flowMap_injective`);
an injective endomorphism of a finite-dimensional space is an isomorphism, giving Lee's
statement that `P^γ_{t₀t₁}` is invertible with inverse `P^γ_{t₁t₀}`. -/
def chartParallelTransport (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : NNReal}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) :
    E ≃ₗ[ℝ] E := by
  set A : ℝ → E →L[ℝ] E := fun t => -chartGammaRight cov e b (deriv u t) (c t) with hA
  have hcontA : ContinuousOn A (Icc t₀ t₁) := hcont.neg
  have hKA : ∀ t ∈ Icc t₀ t₁, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  exact LinearEquiv.ofInjectiveEndo (flowMap ht hcontA hKA)
    (flowMap_injective ht hcontA hKA)

/-- The parallel transport `P^γ_{t₀t₁} V₀` (Lee, equation (4.22)) is realised by a genuine
parallel field: there is a coordinate vector field `V` along the curve with `V t₀ = V₀`,
`V t₁ = P^γ_{t₀t₁} V₀`, solving Lee's parallelism ODE on `[t₀, t₁]`. -/
theorem exists_chartParallelTransport_spec (cov : Connection I E (TangentSpace I : M → Type _))
    (u : ℝ → E) (c : ℝ → M) {t₀ t₁ : ℝ} (ht : t₀ ≤ t₁) {K : NNReal}
    (hcont : ContinuousOn (fun t => chartGammaRight cov e b (deriv u t) (c t)) (Icc t₀ t₁))
    (hK : ∀ t ∈ Icc t₀ t₁, ‖chartGammaRight cov e b (deriv u t) (c t)‖₊ ≤ K) (V₀ : E) :
    ∃ V : ℝ → E, V t₀ = V₀ ∧ V t₁ = chartParallelTransport cov u c ht hcont hK V₀ ∧
      ∀ t ∈ Icc t₀ t₁,
        HasDerivWithinAt V (-chartGamma cov e b (deriv u t) (V t) (c t)) (Icc t₀ t₁) t := by
  set A : ℝ → E →L[ℝ] E := fun t => -chartGammaRight cov e b (deriv u t) (c t) with hA
  have hcontA : ContinuousOn A (Icc t₀ t₁) := hcont.neg
  have hKA : ∀ t ∈ Icc t₀ t₁, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  have hval : ∀ (t : ℝ) (w : E), A t w = -chartGamma cov e b (deriv u t) w (c t) := fun t w => by
    rw [hA]; simp only [ContinuousLinearMap.neg_apply, chartGammaRight_apply]
  refine ⟨solOf ht hcontA hKA V₀, solOf_left ht hcontA hKA V₀, rfl,
    fun t htmem => ?_⟩
  have h := solOf_isSolOn ht hcontA hKA V₀ t htmem
  rwa [hval] at h

end

end LeeLib.Ch04

import OpenGALib.Riemannian.Geodesic.CovariantDerivative
import OpenGALib.Riemannian.Geodesic.HopfRinow.MetricBridge
import OpenGALib.Riemannian.Exponential.ConvexNeighborhood
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Parallel orthonormal frame along a curve (do Carmo Ch. 5, `def:dc-ch5-2-1`)

do Carmo's derivation of the Jacobi equation and, later, of the no-conjugate-point
lemma `lem:dc-ch7-3-2` is carried out in a **parallel orthonormal frame**
`e₁(t),…,eₙ(t)` along the geodesic `γ`: fields that are parallel (`DeᵢDt = 0`) and
orthonormal (`⟨eᵢ(t), eⱼ(t)⟩ = δᵢⱼ`) at every `t`.  In such a frame the covariant
derivative `D/dt` becomes ordinary differentiation of components, the metric is the
standard inner product, and `J = Σ fᵢ eᵢ` turns the Jacobi equation into the
second-order linear system `f'' + A(t) f = 0` handled abstractly in
`OpenGALib/Riemannian/Jacobi/JacobiEquationODE.lean`.

This file constructs that frame, read in the chart at `α` along the coordinate
curve `u : ℝ → E`:

* `Riemannian.Jacobi.chartMetricInner_const_of_parallelSol` — **parallel transport
  is an isometry** (do Carmo Ch. 2, Cor. 3.3 / `lem:dc-ch2-3-1-coord`, in usable
  *constant* form): two coordinate fields solving the parallel-transport ODE on
  `[a,b]` have constant chart inner product.  Upgrades the `deriv = 0` statement
  `hasDerivAt_chartMetricInner_eq_zero_of_isParallelCoord` to the integrated fact.
* `Riemannian.Jacobi.exists_parallelOrthoFrame` — given an orthonormal frame at the
  initial point, parallel transport it to a **parallel orthonormal frame** along
  `u` (do Carmo's `e₁(t),…,eₙ(t)`).
* `Riemannian.Jacobi.exists_chartOrthonormalBasis` — existence of the initial
  orthonormal frame for the (positive-definite, symmetric) chart inner product.
-/

open Set Bundle
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** `chartMetricInner g α y a b = 0` when the left slot is `0` (linearity
in the first argument). -/
theorem chartMetricInner_zero_left (g : RiemannianMetric I M) (α : M) (y b : E) :
    chartMetricInner (I := I) g α y 0 b = 0 := by
  simp [chartMetricInner_def]

/-- **Math.** `chartMetricInner g α y a b = 0` when the right slot is `0` (linearity
in the second argument). -/
theorem chartMetricInner_zero_right (g : RiemannianMetric I M) (α : M) (y a : E) :
    chartMetricInner (I := I) g α y a 0 = 0 := by
  simp [chartMetricInner_def]

/-- **Math.** The chart inner product is additive over a finite sum in the left slot. -/
theorem chartMetricInner_sum_left {ι : Type*} (g : RiemannianMetric I M) (α : M) (y : E)
    (s : Finset ι) (a : ι → E) (b : E) :
    chartMetricInner (I := I) g α y (∑ k ∈ s, a k) b
      = ∑ k ∈ s, chartMetricInner (I := I) g α y (a k) b := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, chartMetricInner_add_left, ih]

/-- **Math.** do Carmo Ch. 2, Cor. 3.3 / `lem:dc-ch2-3-1-coord`, integrated form:
**parallel transport is an isometry.**  If `V` and `W` solve the parallel-transport
ODE `V̇ = −Γ(u̇, V)(u)` on `[a,b]` (in the chart at `α`, with the curve `u` staying
in the chart domain), then the chart inner product `⟨V(t), W(t)⟩` is **constant** on
`[a,b]`, equal to its value `⟨V(a), W(a)⟩` at the left endpoint.  This upgrades the
pointwise `d/dt⟨V,W⟩ = 0` statement to the global constancy needed to transport an
orthonormal frame. -/
theorem chartMetricInner_const_of_parallelSol (g : RiemannianMetric I M) (α : M)
    (u V W : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc a b, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hV : ∀ t ∈ Icc a b, HasDerivWithinAt V
      (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t)) (Icc a b) t)
    (hW : ∀ t ∈ Icc a b, HasDerivWithinAt W
      (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (W t) (u t)) (Icc a b) t)
    {t : ℝ} (ht : t ∈ Icc a b) :
    chartMetricInner (I := I) g α (u t) (V t) (W t)
      = chartMetricInner (I := I) g α (u a) (V a) (W a) := by
  classical
  set φ : ℝ → ℝ := fun s => chartMetricInner (I := I) g α (u s) (V s) (W s) with hφ
  -- `V`, `W` are continuous on `[a,b]`.
  have hVc : ContinuousOn V (Icc a b) := fun s hs => (hV s hs).continuousWithinAt
  have hWc : ContinuousOn W (Icc a b) := fun s hs => (hW s hs).continuousWithinAt
  -- `φ` is continuous on `[a,b]`.
  have hφc : ContinuousOn φ (Icc a b) := by
    rw [hφ]
    have hfun : (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
        = fun s => ∑ i, ∑ j, chartGramOnE (I := I) g α i j (u s)
            * Geodesic.chartCoord (E := E) i (V s) * Geodesic.chartCoord (E := E) j (W s) := by
      funext s; rw [chartMetricInner_def]
    rw [hfun]
    apply continuousOn_finset_sum
    intro i _
    apply continuousOn_finset_sum
    intro j _
    have hG' : ContinuousOn (fun s => chartGramOnE (I := I) g α i j (u s)) (Icc a b) := by
      intro s hs
      exact ((hG s hs i j).continuousAt.comp_continuousWithinAt
        (hu s hs).continuousAt.continuousWithinAt)
    have hVi : ContinuousOn (fun s => Geodesic.chartCoord (E := E) i (V s)) (Icc a b) :=
      (Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hVc
    have hWj : ContinuousOn (fun s => Geodesic.chartCoord (E := E) j (W s)) (Icc a b) :=
      (Geodesic.chartCoordFunctional (E := E) j).continuous.comp_continuousOn hWc
    exact (hG'.mul hVi).mul hWj
  -- On the interior, `φ' = 0`.
  have hderiv : ∀ s ∈ interior (Icc a b), HasDerivWithinAt φ 0 (interior (Icc a b)) s := by
    intro s hs
    rw [interior_Icc] at hs
    have hnhds : Icc a b ∈ 𝓝 s := Icc_mem_nhds hs.1 hs.2
    have hsmem : s ∈ Icc a b := ⟨hs.1.le, hs.2.le⟩
    -- Full derivatives at the interior point.
    have hVd : HasDerivAt V
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u s) (V s) (u s)) s :=
      (hV s hsmem).hasDerivAt hnhds
    have hWd : HasDerivAt W
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u s) (W s) (u s)) s :=
      (hW s hsmem).hasDerivAt hnhds
    -- Both covariant derivatives vanish (parallelism).
    have hcV : covariantDerivCoord (I := I) g α u V s = 0 := by
      rw [covariantDerivCoord_def, hVd.deriv]; abel
    have hcW : covariantDerivCoord (I := I) g α u W s = 0 := by
      rw [covariantDerivCoord_def, hWd.deriv]; abel
    have hmain := hasDerivAt_chartMetricInner_along (I := I) g α u V W
      (hu s hsmem) hVd.differentiableAt hWd.differentiableAt (hG s hsmem) (hbase s hsmem)
    have hval : chartMetricInner (I := I) g α (u s) (covariantDerivCoord (I := I) g α u V s) (W s)
        + chartMetricInner (I := I) g α (u s) (V s) (covariantDerivCoord (I := I) g α u W s) = 0 := by
      rw [hcV, hcW, chartMetricInner_zero_left, chartMetricInner_zero_right, add_zero]
    rw [hval] at hmain
    exact (hmain.hasDerivWithinAt).mono interior_subset
  -- `φ` is both monotone and antitone (derivative `≥ 0` and `≤ 0`), hence constant.
  have hmono : MonotoneOn φ (Icc a b) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b) hφc hderiv
      (fun s _ => le_refl 0)
  have hanti : AntitoneOn φ (Icc a b) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b) hφc hderiv
      (fun s _ => le_refl 0)
  have haq : a ∈ Icc a b := ⟨le_rfl, hab⟩
  exact le_antisymm (hanti haq ht ht.1) (hmono haq ht ht.1)

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: **existence of a parallel
orthonormal frame along a curve.**  Given an orthonormal family `e₀ : ι → E` for the
chart inner product at the initial point `u a`, parallel transport produces fields
`e i : ℝ → E` (`i : ι`) that are

* parallel along `u` (each solves the parallel-transport ODE `ėᵢ = −Γ(u̇, eᵢ)(u)`),
* start at the given frame, `e i a = e₀ i`, and
* stay **orthonormal** at every time: `⟨e i(t), e j(t)⟩ = δᵢⱼ` for all `t ∈ [a,b]`.

The orthonormality is the content of `chartMetricInner_const_of_parallelSol`
(parallel transport is an isometry): each pairing `⟨e i(t), e j(t)⟩` is constant, so
it keeps its initial value `⟨e₀ i, e₀ j⟩ = δᵢⱼ`.  This is do Carmo's
`e₁(t),…,eₙ(t)`. -/
theorem exists_parallelOrthoFrame {ι : Type*} [DecidableEq ι] (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0}
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc a b, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Icc a b))
    (hK : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    (e₀ : ι → E)
    (horth : ∀ i j, chartMetricInner (I := I) g α (u a) (e₀ i) (e₀ j)
      = if i = j then (1 : ℝ) else 0) :
    ∃ e : ι → ℝ → E,
      (∀ i, e i a = e₀ i) ∧
      (∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (e i)
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (e i t) (u t))
        (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = if i = j then (1 : ℝ) else 0) := by
  classical
  have H : ∀ i : ι, ∃ V : ℝ → E, V a = e₀ i ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt V
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
        (Icc a b) t := fun i => exists_isParallelCoord_Icc g α u hab (e₀ i) hcont hK
  choose e he0 heODE using H
  refine ⟨e, he0, heODE, fun t ht i j => ?_⟩
  rw [chartMetricInner_const_of_parallelSol g α u (e i) (e j) hab hu hG hbase
    (heODE i) (heODE j) ht, he0 i, he0 j, horth i j]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1` / `cor:dc-ch5-3-10`: an **orthonormal
frame is a basis at each point.**  A finite family `e : ι → E` that is orthonormal for
the chart inner product `⟨·,·⟩ = chartMetricInner g α y` is linearly independent (over
`ℝ`): pairing `∑ cᵢ eᵢ = 0` with `eⱼ` gives `cⱼ = ⟨∑ cᵢ eᵢ, eⱼ⟩ = 0`.  Combined with
`exists_parallelOrthoFrame`, at each time `t` the transported frame `{e i(t)}` is a
basis of the model space, so `J(t) = ∑ᵢ fᵢ(t) e i(t)` is well defined. -/
theorem linearIndependent_of_chartMetricInner_orthonormal {ι : Type*} [Fintype ι]
    [DecidableEq ι] (g : RiemannianMetric I M) (α : M) (y : E) (e : ι → E)
    (horth : ∀ i j, chartMetricInner (I := I) g α y (e i) (e j) = if i = j then (1 : ℝ) else 0) :
    LinearIndependent ℝ e := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have hkey : chartMetricInner (I := I) g α y (∑ i, c i • e i) (e j) = c j := by
    rw [chartMetricInner_sum_left]
    simp only [chartMetricInner_smul_left, horth, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j]
    simp
  rw [hc, chartMetricInner_zero_left] at hkey
  exact hkey.symm

-- the following instances are used only by `exists_chartOrthonormalBasis_self` and
-- `exists_parallelOrthoFrame_self` (they are what the pole positive-definiteness
-- lemma requires); kept below the purely-algebraic frame lemmas above so those stay
-- free of the pole hypotheses.
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: **existence of an orthonormal frame for
the chart inner product at the pole.**  The chart inner product
`chartMetricInner g α (extChartAt I α α)` at the center `α` is a symmetric
positive-definite bilinear form on the model space `E`, so it admits an orthonormal
basis `e₁,…,eₙ` (`n = dim M`): `⟨eᵢ, eⱼ⟩ = δᵢⱼ`.  Feeding this to
`exists_parallelOrthoFrame` discharges the orthonormal-start hypothesis, giving do
Carmo's parallel orthonormal frame with no input frame required.  Proof: diagonalize
the symmetric form (`LinearMap.BilinForm.exists_orthogonal_basis`) and normalize each
basis vector by `1/√⟨vᵢ,vᵢ⟩`, using positive-definiteness at the pole
(`chartMetricInner_extChartAt_self_pos`). -/
theorem exists_chartOrthonormalBasis_self (g : RiemannianMetric I M) (α : M) :
    ∃ e : Fin (Module.finrank ℝ E) → E,
      ∀ i j, chartMetricInner (I := I) g α (extChartAt I α α) (e i) (e j)
        = if i = j then (1 : ℝ) else 0 := by
  classical
  -- Package the pole chart inner product as a bilinear form on `E`.
  set B : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (chartMetricInner (I := I) g α (extChartAt I α α))
      (chartMetricInner_add_left (I := I) g α (extChartAt I α α))
      (fun s a b => by simp only [chartMetricInner_smul_left, smul_eq_mul])
      (chartMetricInner_add_right (I := I) g α (extChartAt I α α))
      (fun s a b => by simp only [chartMetricInner_smul_right, smul_eq_mul]) with hB
  have hBapp : ∀ a b, B a b = chartMetricInner (I := I) g α (extChartAt I α α) a b := by
    intro a b; rw [hB]; rfl
  -- Diagonalize: an orthogonal basis for the symmetric form `B`.
  obtain ⟨v, hv⟩ : ∃ v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, B.IsOrthoᵢ v := by
    apply LinearMap.BilinForm.exists_orthogonal_basis
    exact ⟨fun x y => by
      simp only [hBapp]; exact chartMetricInner_symm (I := I) g α _ x y⟩
  rw [LinearMap.isOrthoᵢ_def] at hv
  -- Diagonal values are strictly positive (pole positive-definiteness).
  have hc : ∀ i, 0 < chartMetricInner (I := I) g α (extChartAt I α α) (v i) (v i) := fun i =>
    Riemannian.Exponential.chartMetricInner_extChartAt_self_pos (I := I) g α (v.ne_zero i)
  -- Normalize each basis vector.
  refine ⟨fun i =>
      (Real.sqrt (chartMetricInner (I := I) g α (extChartAt I α α) (v i) (v i)))⁻¹ • v i, ?_⟩
  intro i j
  rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hsq : Real.sqrt (chartMetricInner (I := I) g α (extChartAt I α α) (v i) (v i))
        * Real.sqrt (chartMetricInner (I := I) g α (extChartAt I α α) (v i) (v i))
        = chartMetricInner (I := I) g α (extChartAt I α α) (v i) (v i) :=
      Real.mul_self_sqrt (hc i).le
    rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ (hc i).ne']
  · rw [if_neg hij]
    have hoff := hv i j hij
    rw [hBapp] at hoff
    rw [hoff, mul_zero, mul_zero]

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: **a parallel orthonormal frame exists
along the geodesic, with no input frame required.**  When the coordinate curve `u`
starts at the chart center (`u a = extChartAt I α α`, e.g. `α = γ(0)`), the pole
orthonormal basis (`exists_chartOrthonormalBasis_self`) supplies the initial frame, and
`exists_parallelOrthoFrame` transports it: there are `n = dim M` coordinate fields
`e i : ℝ → E` that are parallel along `u` and orthonormal at every `t ∈ [a,b]`.  This is
do Carmo's ``let `e₁(t),…,eₙ(t)` be parallel, orthonormal fields along `γ`.'' -/
theorem exists_parallelOrthoFrame_self (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0} (hstart : u a = extChartAt I α α)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc a b, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Icc a b))
    (hK : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K) :
    ∃ e : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (e i)
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (e i t) (u t))
        (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = if i = j then (1 : ℝ) else 0) := by
  obtain ⟨e₀, horth₀⟩ := exists_chartOrthonormalBasis_self (I := I) g α
  obtain ⟨e, _, heODE, heorth⟩ := exists_parallelOrthoFrame g α u hab hu hG hbase hcont hK e₀
    (fun i j => by rw [hstart]; exact horth₀ i j)
  exact ⟨e, heODE, heorth⟩

end Riemannian.Jacobi

import DoCarmoLib.Riemannian.Jacobi.JacobiCurvatureSmooth
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureVector
import DoCarmoLib.Riemannian.Jacobi.ParallelFrame
import DoCarmoLib.Riemannian.Jacobi.JacobiManifold
import DoCarmoLib.Riemannian.Exponential.MovingBaseGauss
import DoCarmoLib.Riemannian.Geodesic.ODESmoothness

/-!
# `C^∞` smoothness of the parallel orthonormal frame along a smooth curve

do Carmo, *Riemannian Geometry*, Ch. 5, §2.  The fourth-order Taylor expansion of
`|J(t)|²` (do Carmo Prop. 2.7, analytic core `norm_sq_jacobi_isLittleO_local`) needs the
Jacobi coefficient data `f, A` along a geodesic to be `C^∞`, not merely `C¹`.
`ParallelFrame.lean` builds the parallel orthonormal frame `e₁,…,eₙ` along a curve `u`,
but only with `HasDerivWithinAt`/`C¹` regularity (the `Riemannian.LinearODE` engine produces
`C¹` solutions from continuous coefficients).

This file supplies the `C^∞` upgrade.  Along a curve `u : ℝ → E` that is `C^∞` on an open
time set and stays in the chart interior, the parallel-transport ODE
`ė_i = −Γ(u̇, e_i)(u) = B(t) e_i` has a `C^∞` operator coefficient
`B(t) = −chartChristoffelContractionRight(u̇(t), u(t))`, so the `C^∞` bootstrap for linear
ODEs (`contDiffOn_infty_of_hasDerivAt_clm_apply`) upgrades each frame field `e_i` to `C^∞`.

Reusable outputs:

* `contDiffOn_infty_chartChristoffelContractionRight` — the frame ODE coefficient `B(t)` is
  `C^∞` in `t` (mirrors `contDiffOn_infty_chartCurvatureOp`).
* `exists_chartOrthonormalBasis_at` — an orthonormal frame for the chart inner product at an
  *arbitrary* interior chart point (the moving-base analogue of
  `exists_chartOrthonormalBasis_self`); lets the parallel frame start off the pole, so that
  `t = 0` is an *interior* time and the two-sided Taylor expansion applies.
* `exists_contDiffOn_parallelOrthoFrame` — a parallel orthonormal frame along `u`, orthonormal
  on the closed interval and `C^∞` on its interior.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The frame ODE coefficient as a smooth operator field -/

/-- **Math.** The parallel-transport coefficient `w ↦ Γ(v, w)(y)` is the partial application
of the Christoffel bilinear map: `chartChristoffelContractionRight g α v y = Γ(y)(v, ·)`. -/
theorem chartChristoffelContractionRight_eq_chartChristoffelBilin
    (g : RiemannianMetric I M) (α : M) (v y : E) :
    chartChristoffelContractionRight (I := I) g α v y
      = chartChristoffelBilin (I := I) g α y v := by
  ext w
  rw [chartChristoffelContractionRight_apply, chartChristoffelBilin_apply]

/-- **Math.** **`C^∞` smoothness of the parallel-transport ODE coefficient.**  Along a curve `u`
that is `C^∞` on an open time set `s` and stays in the chart interior, the operator field
`t ↦ chartChristoffelContractionRight(u̇(t), u(t))` (the coefficient `A(t)` of the parallel
system `V̇ = −A(t)V`) is `C^∞` in `t`.  Both the Christoffel bilinear map (smooth on the chart
interior, `contDiffOn_chartChristoffelBilin`) and the velocity `u̇` are `C^∞`, and evaluation of
a smooth operator field on a smooth vector is smooth (`ContDiffOn.clm_apply`). -/
theorem contDiffOn_infty_chartChristoffelContractionRight
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {s : Set ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I α).target) :
    ContDiffOn ℝ ∞
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) s := by
  have hu' : ContDiffOn ℝ ∞ (deriv u) s := by
    have h : ContDiffOn ℝ ∞ (derivWithin u s) s := hu.derivWithin hs.uniqueDiffOn (by simp)
    rwa [contDiffOn_congr (fun x hx => (derivWithin_of_isOpen hs hx))] at h
  have hbilin : ContDiffOn ℝ ∞ (fun t => chartChristoffelBilin (I := I) g α (u t)) s :=
    (contDiffOn_chartChristoffelBilin (I := I) g α).comp hu hmem
  have hres := hbilin.clm_apply hu'
  refine hres.congr (fun t _ => ?_)
  rw [chartChristoffelContractionRight_eq_chartChristoffelBilin]

/-! ### Orthonormal frame at an arbitrary interior chart point -/

variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **Orthonormal frame for the chart inner product at an arbitrary interior point.**
For `y` in the chart target, the chart inner product `chartMetricInner g α y` is a symmetric
positive-definite bilinear form on `E`, so it admits an orthonormal basis
(`⟨e_i, e_j⟩ = δ_{ij}`).  This is the moving-base analogue of
`exists_chartOrthonormalBasis_self`: diagonalize the symmetric form
(`LinearMap.BilinForm.exists_orthogonal_basis`) and normalize each vector using
positive-definiteness at `y` (`chartMetricInner_self_pos_of_mem_target`). -/
theorem exists_chartOrthonormalBasis_at (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target) :
    ∃ e : Fin (Module.finrank ℝ E) → E,
      ∀ i j, chartMetricInner (I := I) g α y (e i) (e j) = if i = j then (1 : ℝ) else 0 := by
  classical
  set B : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (chartMetricInner (I := I) g α y)
      (chartMetricInner_add_left (I := I) g α y)
      (fun s a b => by simp only [chartMetricInner_smul_left, smul_eq_mul])
      (chartMetricInner_add_right (I := I) g α y)
      (fun s a b => by simp only [chartMetricInner_smul_right, smul_eq_mul]) with hB
  have hBapp : ∀ a b, B a b = chartMetricInner (I := I) g α y a b := by
    intro a b; rw [hB]; rfl
  obtain ⟨v, hv⟩ : ∃ v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, B.IsOrthoᵢ v := by
    apply LinearMap.BilinForm.exists_orthogonal_basis
    exact ⟨fun x y => by
      simp only [hBapp]; exact chartMetricInner_symm (I := I) g α _ x y⟩
  rw [LinearMap.isOrthoᵢ_def] at hv
  have hc : ∀ i, 0 < chartMetricInner (I := I) g α y (v i) (v i) := fun i =>
    chartMetricInner_self_pos_of_mem_target (I := I) g α hy (v.ne_zero i)
  refine ⟨fun i =>
      (Real.sqrt (chartMetricInner (I := I) g α y (v i) (v i)))⁻¹ • v i, ?_⟩
  intro i j
  rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    have hsq : Real.sqrt (chartMetricInner (I := I) g α y (v i) (v i))
        * Real.sqrt (chartMetricInner (I := I) g α y (v i) (v i))
        = chartMetricInner (I := I) g α y (v i) (v i) :=
      Real.mul_self_sqrt (hc i).le
    rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ (hc i).ne']
  · rw [if_neg hij]
    have hoff := hv i j hij
    rw [hBapp] at hoff
    rw [hoff, mul_zero, mul_zero]

/-! ### The `C^∞` parallel orthonormal frame -/

/-- **Math.** **do Carmo Ch. 5, `def:dc-ch5-2-1`, `C^∞` form.**  Along a curve `u` that is
`C^∞` on an open time set `s` and stays in the chart interior, and a closed subinterval
`[a, b] ⊆ s`, there is a parallel orthonormal frame `e₁,…,eₙ` along `u` that is orthonormal at
every `t ∈ [a, b]` and, crucially, **`C^∞` on the interior `(a, b)`**.  The frame is transported
from an orthonormal basis at `u(a)` (`exists_chartOrthonormalBasis_at`); orthonormality is
preserved by parallel transport, and the `C^∞` regularity is the linear-ODE bootstrap
(`contDiffOn_infty_of_hasDerivAt_clm_apply`) applied to the parallel system
`ė_i = −Γ(u̇, e_i)(u)` whose coefficient is `C^∞`
(`contDiffOn_infty_chartChristoffelContractionRight`). -/
theorem exists_contDiffOn_parallelOrthoFrame (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {s : Set ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ ∞ u s)
    (hmem : ∀ t ∈ s, u t ∈ interior (extChartAt I α).target)
    {a b : ℝ} (hab : a ≤ b) (hIccs : Icc a b ⊆ s) :
    ∃ e : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ t ∈ Icc a b, ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = if i = j then (1 : ℝ) else 0) ∧
      (∀ i, ContinuousOn (e i) (Icc a b)) ∧
      (∀ i, ContDiffOn ℝ ∞ (e i) (Ioo a b)) ∧
      (∀ i, ∀ t ∈ Ioo a b, HasDerivAt (e i)
        (-(chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (e i t)) t) := by
  classical
  -- membership of `u t` in the target (interior ⊆ target)
  have hmemT : ∀ t ∈ Icc a b, u t ∈ (extChartAt I α).target := fun t ht =>
    interior_subset (hmem t (hIccs ht))
  -- differentiability of `u` on `[a, b]`
  have hu_diff : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t := fun t ht =>
    (hu.contDiffAt (hs.mem_nhds (hIccs ht))).differentiableAt (by norm_num)
  -- Gram differentiability at interior points
  have hG : ∀ t ∈ Icc a b, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t) := fun t ht i j =>
    differentiableAt_chartGramOnE (I := I) g α (hmemT t ht) i j
  -- base-set membership of the chart foot
  have hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    intro t ht
    have hfoot : (extChartAt I α).symm (u t) ∈ (chartAt H α).source := by
      have h := (extChartAt I α).map_target (hmemT t ht)
      rwa [extChartAt_source] at h
    rw [TangentBundle.trivializationAt_baseSet]; exact hfoot
  -- the coefficient field is `C^∞`, hence continuous and bounded on `[a, b]`
  have hcoefCD : ContDiffOn ℝ ∞
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) s :=
    contDiffOn_infty_chartChristoffelContractionRight g α u hs hu hmem
  have hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
      (Icc a b) := (hcoefCD.continuousOn).mono hIccs
  -- also need the same in the `chartChristoffelContractionRight`-name form used by
  -- `exists_parallelOrthoFrame` (it is literally the same function)
  obtain ⟨C, hC⟩ := (isCompact_Icc).exists_bound_of_continuousOn hcont
  set K : ℝ≥0 := Real.toNNReal C with hKdef
  have hKbound : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K := by
    intro t ht
    rw [hKdef, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal C (le_trans (norm_nonneg _) (hC t ht))]
    exact hC t ht
  -- orthonormal starting frame at `u a`
  obtain ⟨e₀, he₀⟩ := exists_chartOrthonormalBasis_at (I := I) g α (hmemT a ⟨le_rfl, hab⟩)
  -- build the parallel orthonormal frame on `[a, b]`
  obtain ⟨e, _he0, heODE, heorth⟩ :=
    exists_parallelOrthoFrame (I := I) g α u hab hu_diff hG hbase hcont hKbound e₀ he₀
  refine ⟨e, heorth, fun i t ht => (heODE i t ht).continuousWithinAt, ?_, ?_⟩
  · -- `C^∞` on the interior via the ODE bootstrap
    intro i
    have hB : ContDiffOn ℝ ∞
        (fun t => -(chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)))
        (Ioo a b) :=
      (hcoefCD.neg).mono (subset_trans Ioo_subset_Icc_self hIccs)
    refine contDiffOn_infty_of_hasDerivAt_clm_apply isOpen_Ioo hB (fun t ht => ?_)
    have hd := (heODE i t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    simp only [ContinuousLinearMap.neg_apply,
      chartChristoffelContractionRight_apply]
    exact hd
  · -- the two-sided ODE at interior points
    intro i t ht
    have hd := (heODE i t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    simpa only [ContinuousLinearMap.neg_apply,
      chartChristoffelContractionRight_apply] using hd

end Riemannian.Jacobi

end

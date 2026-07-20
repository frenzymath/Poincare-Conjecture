import DoCarmoLib.Riemannian.Jacobi.ParallelFrame
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureNaturality
import DoCarmoLib.Riemannian.Jacobi.FrameReduction
import DoCarmoLib.Riemannian.Jacobi.PairJacobiField

/-!
# Velocity-seeded parallel orthonormal frame (do Carmo Ch. 8, `cor:dc-ch8-2-2`)

E. Cartan's theorem (do Carmo Ch. 8, `thm:dc-ch8-2-1`, and its constant-curvature
corollaries `cor:dc-ch8-2-2`/`cor:dc-ch8-2-3`) is proved in a **parallel orthonormal
frame along the geodesic `γ` whose distinguished vector is the velocity**: do Carmo's
`e₁,…,e_{n-1}, e_n = γ'`.  The generic parallel orthonormal frame
(`exists_parallelOrthoFrame_self`) is built from an *arbitrary* orthonormal basis at the
initial point and gives no control over whether one of its members is the velocity.

This file supplies that control.  Two ingredients:

* **`exists_chartOrthonormalBasis_containing_unit`** — an algebraic extension lemma: a
  chart-unit vector `v` (`⟨v, v⟩_y = 1`) extends to a chart-orthonormal basis of the model
  space with `v` as one of its members.  The construction is a Householder reflection
  `R x = x − (2⟨w, x⟩/⟨w, w⟩) w`, `w = f₀ − v`, applied to a generic orthonormal basis `f`
  (`exists_chartOrthonormalBasis_of_mem_baseSet`): a reflection preserves the (symmetric)
  chart inner product (`chartMetricInner_householderReflection`), and this particular one
  sends `f₀` to `v`, so `R ∘ f` is orthonormal with `(R ∘ f) 0 = v`.

* **`exists_velocitySeededParallelOrthoFrame`** — feeding that seeded basis to
  `exists_parallelOrthoFrame` produces a parallel orthonormal frame `e` with
  `e n₀ a = γ'(a)`; and since the geodesic velocity `γ'` is itself a chart-parallel field
  (the chart geodesic equation `u'' = −Γ(u', u')(u)` is the parallel-transport ODE with
  `V = u'`), forward uniqueness of parallel fields (`isParallelSol_eqOn_Icc`) forces
  `e n₀ t = γ'(t) = u'(t)` for **all** `t ∈ [a, b]`.

Blueprint: `lem:dc-ch8-2-1-velocity-frame`, feeding `cor:dc-ch8-2-2`, `cor:dc-ch8-2-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, Theorem 2.1 and Corollaries 2.2–2.3.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The Householder reflection preserves the chart inner product -/

/-- **Math.** **A Householder reflection is a chart isometry.**  For a vector `w` with
`⟨w, w⟩_y ≠ 0`, the reflection `R x = x − (2⟨w, x⟩_y / ⟨w, w⟩_y) w` across the hyperplane
`⟨w, ·⟩_y = 0` preserves the (symmetric) chart inner product: `⟨R x, R x'⟩_y = ⟨x, x'⟩_y`.
Standard bilinear expansion using symmetry `⟨x, w⟩_y = ⟨w, x⟩_y`. -/
theorem chartMetricInner_householderReflection (g : RiemannianMetric I M) (α : M) (y w : E)
    (hw : chartMetricInner (I := I) g α y w w ≠ 0) (x x' : E) :
    chartMetricInner (I := I) g α y
        (x + (-(2 * chartMetricInner (I := I) g α y w x
              / chartMetricInner (I := I) g α y w w)) • w)
        (x' + (-(2 * chartMetricInner (I := I) g α y w x'
              / chartMetricInner (I := I) g α y w w)) • w)
      = chartMetricInner (I := I) g α y x x' := by
  simp only [chartMetricInner_add_left, chartMetricInner_add_right,
    chartMetricInner_smul_left, chartMetricInner_smul_right]
  rw [chartMetricInner_symm (I := I) g α y x w]
  field_simp
  ring

/-- **Math.** **Orthonormal expansion in a chart-orthonormal frame.**  A chart-orthonormal
family `e : Fin n → E` (`n = dim M`) is a basis of the model space, and every vector expands
as `v = Σᵢ ⟨v, eᵢ⟩_y eᵢ` with the chart inner products as coordinates.  This turns a field of
tangent vectors read in the frame into its scalar coefficient functions
`yᵢ(t) = ⟨J(t), eᵢ(t)⟩` — the passage do Carmo uses to write `J = Σ yᵢ eᵢ`.  Proof: the
family is linearly independent (`linearIndependent_of_chartMetricInner_orthonormal`) with
`Fintype.card (Fin n) = n = dim M`, hence a basis; pairing `v = Σ (repr v i) eᵢ` with `eⱼ`
and using orthonormality identifies `repr v j = ⟨v, eⱼ⟩`. -/
theorem eq_sum_chartMetricInner_smul_of_orthonormal (g : RiemannianMetric I M) (α : M) (y : E)
    (e : Fin (Module.finrank ℝ E) → E)
    (horth : ∀ i j, chartMetricInner (I := I) g α y (e i) (e j)
      = if i = j then (1 : ℝ) else 0)
    (v : E) :
    v = ∑ i, chartMetricInner (I := I) g α y v (e i) • e i := by
  classical
  have hli : LinearIndependent ℝ e :=
    linearIndependent_of_chartMetricInner_orthonormal (I := I) g α y e horth
  set B : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hli (by simp) with hB
  have hBe : ∀ i, B i = e i := fun i => by rw [hB, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- the chart pairing `⟨v, eⱼ⟩` is the repr coordinate of `v` along `eⱼ`
  have hrepr : ∀ j, chartMetricInner (I := I) g α y v (e j) = B.repr v j := by
    intro j
    conv_lhs => rw [← B.sum_repr v]
    rw [chartMetricInner_sum_left]
    simp only [chartMetricInner_smul_left, hBe, horth, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ j (B.repr v)]
    simp
  conv_lhs => rw [← B.sum_repr v]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hBe, ← hrepr i]

/-! ### Extend a chart-unit vector to a chart-orthonormal basis -/

/-- **Math.** **A chart-orthonormal basis of the model space at a base-set point.**  At any
`y` whose base point lies in the trivialization base set, the chart inner product
`chartMetricInner g α y` is symmetric and positive-definite (`chartMetricInner_pos`), hence
admits an orthonormal basis `e₁,…,eₙ` (`⟨eᵢ, eⱼ⟩_y = δᵢⱼ`).  Same diagonalize-and-normalize
proof as `exists_chartOrthonormalBasis_self`, but at a general base-set point rather than the
pole. -/
theorem exists_chartOrthonormalBasis_of_mem_baseSet (g : RiemannianMetric I M) (α : M) {y : E}
    (hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ e : Fin (Module.finrank ℝ E) → E,
      ∀ i j, chartMetricInner (I := I) g α y (e i) (e j)
        = if i = j then (1 : ℝ) else 0 := by
  classical
  set B : LinearMap.BilinForm ℝ E :=
    LinearMap.mk₂ ℝ (chartMetricInner (I := I) g α y)
      (chartMetricInner_add_left (I := I) g α y)
      (fun s a b => by simp only [chartMetricInner_smul_left, smul_eq_mul])
      (chartMetricInner_add_right (I := I) g α y)
      (fun s a b => by simp only [chartMetricInner_smul_right, smul_eq_mul]) with hB
  have hBapp : ∀ a b, B a b = chartMetricInner (I := I) g α y a b := fun a b => by rw [hB]; rfl
  obtain ⟨v, hv⟩ : ∃ v : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E, B.IsOrthoᵢ v := by
    apply LinearMap.BilinForm.exists_orthogonal_basis
    exact ⟨fun x z => by simp only [hBapp]; exact chartMetricInner_symm (I := I) g α _ x z⟩
  rw [LinearMap.isOrthoᵢ_def] at hv
  have hc : ∀ i, 0 < chartMetricInner (I := I) g α y (v i) (v i) := fun i =>
    chartMetricInner_pos (I := I) g α hbase (v.ne_zero i)
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

/-- **Math.** **Extend a chart-unit vector to a chart-orthonormal basis.**  If `v` is a
chart-unit vector at a base-set point `y` (`⟨v, v⟩_y = 1`), there is a chart-orthonormal
basis `e₁,…,eₙ` of the model space and an index `n₀` with `e_{n₀} = v`.  Take a generic
chart-orthonormal basis `f` (`exists_chartOrthonormalBasis_of_mem_baseSet`); if `f 0 = v`
we are done, otherwise the Householder reflection `R` with `w = f 0 − v` fixes the
inner product and sends `f 0` to `v`, so `R ∘ f` is orthonormal with `(R ∘ f) 0 = v`. -/
theorem exists_chartOrthonormalBasis_containing_unit (g : RiemannianMetric I M) (α : M) {y v : E}
    (hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hv : chartMetricInner (I := I) g α y v v = 1) :
    ∃ (e : Fin (Module.finrank ℝ E) → E) (n₀ : Fin (Module.finrank ℝ E)),
      e n₀ = v ∧
      ∀ i j, chartMetricInner (I := I) g α y (e i) (e j)
        = if i = j then (1 : ℝ) else 0 := by
  classical
  -- bilinearity in a subtracted slot (no dedicated `sub` lemma exists)
  have hsubL : ∀ a b c : E, chartMetricInner (I := I) g α y (a - b) c
      = chartMetricInner (I := I) g α y a c - chartMetricInner (I := I) g α y b c := by
    intro a b c
    rw [sub_eq_add_neg, chartMetricInner_add_left, ← neg_one_smul ℝ b,
      chartMetricInner_smul_left]; ring
  have hsubR : ∀ a b c : E, chartMetricInner (I := I) g α y a (b - c)
      = chartMetricInner (I := I) g α y a b - chartMetricInner (I := I) g α y a c := by
    intro a b c
    rw [sub_eq_add_neg, chartMetricInner_add_right, ← neg_one_smul ℝ c,
      chartMetricInner_smul_right]; ring
  obtain ⟨f, hf⟩ := exists_chartOrthonormalBasis_of_mem_baseSet (I := I) g α hbase
  have hf00 : chartMetricInner (I := I) g α y (f 0) (f 0) = 1 := by
    rw [hf 0 0, if_pos rfl]
  by_cases hfv : f 0 = v
  · exact ⟨f, 0, hfv, hf⟩
  · -- Householder reflection swapping `f 0 ↦ v`
    set w : E := f 0 - v with hw
    have hwne : w ≠ 0 := sub_ne_zero.mpr hfv
    have hswpos : 0 < chartMetricInner (I := I) g α y w w :=
      chartMetricInner_pos (I := I) g α hbase hwne
    have hsw : chartMetricInner (I := I) g α y w w ≠ 0 := hswpos.ne'
    set R : E → E := fun x =>
      x + (-(2 * chartMetricInner (I := I) g α y w x
            / chartMetricInner (I := I) g α y w w)) • w with hR
    -- the two chart pairings of `w = f 0 − v`
    have hwf0 : chartMetricInner (I := I) g α y w (f 0)
        = 1 - chartMetricInner (I := I) g α y v (f 0) := by
      rw [hw, hsubL, hf00]
    have hww : chartMetricInner (I := I) g α y w w
        = 2 - 2 * chartMetricInner (I := I) g α y v (f 0) := by
      rw [hw, hsubR, hsubL, hsubL, hf00, hv, chartMetricInner_symm (I := I) g α y (f 0) v]
      ring
    -- `R (f 0) = v`: the reflection coefficient at `f 0` is `1`.
    have hden : (2 : ℝ) - 2 * chartMetricInner (I := I) g α y v (f 0) ≠ 0 := by
      rw [← hww]; exact hsw
    have hcoef : 2 * chartMetricInner (I := I) g α y w (f 0)
        / chartMetricInner (I := I) g α y w w = 1 := by
      rw [hwf0, hww, div_eq_one_iff_eq hden]; ring
    have hRf0 : R (f 0) = v := by
      simp only [hR]
      rw [hcoef, neg_smul, one_smul, hw]
      abel
    refine ⟨fun i => R (f i), 0, hRf0, ?_⟩
    intro i j
    show chartMetricInner (I := I) g α y (R (f i)) (R (f j)) = _
    simp only [hR]
    rw [chartMetricInner_householderReflection (I := I) g α y w hsw (f i) (f j)]
    exact hf i j

/-! ### The velocity-seeded parallel orthonormal frame -/

/-- **Math.** **A parallel orthonormal frame along the geodesic whose distinguished vector
is the velocity** (do Carmo's `e₁,…,e_{n-1}, e_n = γ'`).  Along a coordinate curve `u`
that solves the chart geodesic ODE `u'' = −Γ(u', u')(u)` (hypothesis `hgeo`, i.e. `u' = γ'`
is chart-parallel) and whose initial velocity `u'(a)` is a chart-unit vector (`hunit`),
there is a parallel orthonormal frame `e : Fin n → ℝ → E` and a distinguished index `n₀`
such that

* each `e i` is parallel along `u` (solves `ėᵢ = −Γ(u', eᵢ)(u)`),
* `{e i(t)}` is chart-orthonormal at every `t ∈ [a, b]`, and
* **`e n₀(t) = u'(t)` for all `t ∈ [a, b]`** — the distinguished frame vector *is* the velocity.

Construction: extend `u'(a)` to a chart-orthonormal basis `e₀` with `e₀ n₀ = u'(a)`
(`exists_chartOrthonormalBasis_containing_unit`), parallel-transport it
(`exists_parallelOrthoFrame`), and note that both `e n₀` and `u'` solve the same
parallel-transport ODE with the same value at `a`, so forward uniqueness
(`isParallelSol_eqOn_Icc`) forces them equal on `[a, b]`.

Blueprint: `lem:dc-ch8-2-1-velocity-frame`. -/
theorem exists_velocitySeededParallelOrthoFrame (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0}
    (hunit : chartMetricInner (I := I) g α (u a) (deriv u a) (deriv u a) = 1)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc a b, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Icc a b))
    (hK : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    (hgeo : ∀ t ∈ Icc a b, HasDerivWithinAt (deriv u)
      (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (deriv u t) (u t))
      (Icc a b) t) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (n₀ : Fin (Module.finrank ℝ E)),
      (∀ i, ∀ t ∈ Icc a b, HasDerivWithinAt (e i)
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (e i t) (u t))
        (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = if i = j then (1 : ℝ) else 0) ∧
      (∀ t ∈ Icc a b, e n₀ t = deriv u t) := by
  classical
  have hbase_a : (extChartAt I α).symm (u a) ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    hbase a (left_mem_Icc.mpr hab)
  -- extend the unit velocity to a chart-orthonormal basis
  obtain ⟨e₀, n₀, he₀n₀, horth₀⟩ :=
    exists_chartOrthonormalBasis_containing_unit (I := I) g α hbase_a hunit
  -- parallel-transport that seeded basis
  obtain ⟨e, he0, heODE, heorth⟩ :=
    exists_parallelOrthoFrame (I := I) g α u hab hu hG hbase hcont hK e₀ horth₀
  refine ⟨e, n₀, heODE, heorth, ?_⟩
  -- `e n₀` and `u'` are parallel fields with the same value at `a`, hence equal on `[a, b]`
  have hstart : e n₀ a = deriv u a := by rw [he0 n₀, he₀n₀]
  exact fun t ht => isParallelSol_eqOn_Icc (I := I) g α u hK (heODE n₀) hgeo hstart ht

/-! ### The second-order chart Jacobi equation from the pair system -/

/-- **Math.** **The chart Jacobi field solves the second-order Jacobi equation.**  A chart
Jacobi field `(J, DJ)` along `u` (do Carmo's `∇J = DJ`, `∇DJ = −ℛ(J, u̇)u̇`, `IsJacobiFieldOn`)
satisfies the second-order equation
`D²J/dt² + ℛ(J, u̇)u̇ = 0` at interior times, i.e.

  `∇(∇J) t + chartCurvatureEndo(u̇)(J t) = 0`.

This is the form consumed by the frame transfer `jacobiFrameTransfer`/
`jacobiFrameTransfer_isConstantCurvature`: the first covariant derivative `∇J` equals `DJ`
on a neighborhood (`covariantDerivCoord_fst`), so its own covariant derivative is `∇DJ`
(`covariantDerivCoord_congr_of_eventuallyEq`), which is `−ℛ(J, u̇)u̇`
(`covariantDerivCoord_snd`); and `ℛ(J, u̇)u̇ = chartCurvatureEndo(u̇)(J)`. -/
theorem IsJacobiFieldOn.chartJacobiEquation {g : RiemannianMetric I M} {α : M}
    {u J DJ : ℝ → E} {a b : ℝ} (h : IsJacobiFieldOn (I := I) g α u J DJ a b) {t : ℝ}
    (ht : t ∈ Ioo a b) :
    covariantDerivCoord (I := I) g α u (fun r => covariantDerivCoord (I := I) g α u J r) t
      + chartCurvatureEndo (I := I) g α (u t) (deriv u t) (J t) = 0 := by
  have hev : (fun r => covariantDerivCoord (I := I) g α u J r) =ᶠ[𝓝 t] DJ := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
    exact h.covariantDerivCoord_fst hr
  rw [covariantDerivCoord_congr_of_eventuallyEq (I := I) g α u hev,
    h.covariantDerivCoord_snd ht, chartCurvatureEndo_apply]
  abel

end Riemannian.Jacobi

end

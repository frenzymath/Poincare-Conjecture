import MorganTianLib.Ch01.JacobiField
import MorganTianLib.Ch01.ParallelFrame
import MorganTianLib.Ch01.VectorSturm
import OpenGALib.Riemannian.TensorBundle.MusicalIso

/-!
# Poincaré Ch. 1 — Jacobi fields in a parallel orthonormal frame

The bridge between the **chart-level Jacobi pair system**
(`MorganTianLib.Ch01.JacobiField`) and the **frame-independent Sturm
comparison** (`MorganTianLib.Ch01.VectorSturm`): expressing a Jacobi field in a
parallel orthonormal frame along the curve turns the time-dependent chart
Gram inner product into the fixed Euclidean one, so the vector-valued Sturm
comparison applies verbatim to the frame-coordinate curve.

* algebra of the chart Gram inner product `chartMetricInner`:
  `chartMetricInner_smul_left/right`, `chartMetricInner_comm`,
  `chartMetricInner_pos` (positive definiteness over the trivialization base
  set, via `chartGramMatrix_posDef`);
* `exists_chartMetricInner_orthonormal` — a basis of `E` orthonormal for the
  chart Gram inner product at a fixed chart point (diagonalize the symmetric
  bilinear form, normalize by positivity);
* `chartMetricInner_parseval` — for a `chartMetricInner`-orthonormal family
  `e` and any `x z : E`,
  `∑ i ⟨x, e i⟩⟨z, e i⟩ = ⟨x, z⟩` (expansion in the frame);
* `jacobi_frame_sturm_comparison` — **the frame reduction**: a Jacobi field
  `(J, ∇J)` along `u` on `[0, T]` with `J(0) = 0`, whose curvature term
  satisfies `⟨ℛ(J, u̇)u̇, J⟩ ≤ K ⟨J, J⟩` along the curve (`K ≥ 0`,
  `√K · T < π`), obeys
  `√⟨∇J(0), ∇J(0)⟩ · s_K(t) ≤ √⟨J(t), J(t)⟩` on `(0, T]`;
* `jacobi_ne_zero_of_curvature_le` — with `∇J(0) ≠ 0` the field has **no
  zero on `(0, T]`**: the chart-local core of Morgan–Tian's "no conjugate
  points below `π/√K`" (blueprint `lem:conjugate-sturm`).

Blueprint: `lem:jacobi-frame-reduction`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.5.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Algebra of the chart Gram inner product -/

/-- **Math.** The chart Gram inner product is homogeneous in its first
vector argument. -/
theorem chartMetricInner_smul_left (g : RiemannianMetric I M) (α : M)
    (y : E) (c : ℝ) (a b : E) :
    chartMetricInner (I := I) g α y (c • a) b
      = c * chartMetricInner (I := I) g α y a b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Math.** The chart Gram inner product is homogeneous in its second
vector argument. -/
theorem chartMetricInner_smul_right (g : RiemannianMetric I M) (α : M)
    (y : E) (c : ℝ) (a b : E) :
    chartMetricInner (I := I) g α y a (c • b)
      = c * chartMetricInner (I := I) g α y a b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Math.** The chart Gram inner product vanishes on the zero vector
(first slot). -/
theorem chartMetricInner_zero_left (g : RiemannianMetric I M) (α : M)
    (y b : E) :
    chartMetricInner (I := I) g α y 0 b = 0 := by
  simp [chartMetricInner_def, Geodesic.chartCoord_def]

/-- **Math.** The chart Gram inner product vanishes on the zero vector
(second slot). -/
theorem chartMetricInner_zero_right (g : RiemannianMetric I M) (α : M)
    (y a : E) :
    chartMetricInner (I := I) g α y a 0 = 0 := by
  simp [chartMetricInner_def, Geodesic.chartCoord_def]

/-- **Math.** The chart Gram inner product is negated with its first
argument. -/
theorem chartMetricInner_neg_left (g : RiemannianMetric I M) (α : M)
    (y a b : E) :
    chartMetricInner (I := I) g α y (-a) b
      = -chartMetricInner (I := I) g α y a b := by
  have h := chartMetricInner_smul_left (I := I) g α y (-1) a b
  simp only [neg_one_smul, neg_one_mul] at h
  exact h

/-- **Math.** **Symmetry** of the chart Gram inner product, from the symmetry
of the Gram matrix. -/
theorem chartMetricInner_comm (g : RiemannianMetric I M) (α : M)
    (y a b : E) :
    chartMetricInner (I := I) g α y a b = chartMetricInner (I := I) g α y b a := by
  simp only [chartMetricInner_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [chartGramOnE_symm]
  ring

/-- **Math.** The chart Gram inner product is additive over finite sums in
its first argument. -/
theorem chartMetricInner_sum_left {ι : Type*} (g : RiemannianMetric I M) (α : M)
    (y : E) (s : Finset ι) (f : ι → E) (b : E) :
    chartMetricInner (I := I) g α y (∑ k ∈ s, f k) b
      = ∑ k ∈ s, chartMetricInner (I := I) g α y (f k) b := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, chartMetricInner_zero_left]
  | cons k s hk ih =>
      rw [Finset.sum_cons, chartMetricInner_add_left, ih, Finset.sum_cons]

/-- **Math.** The chart Gram inner product is additive over finite sums in
its second argument. -/
theorem chartMetricInner_sum_right {ι : Type*} (g : RiemannianMetric I M) (α : M)
    (y : E) (s : Finset ι) (a : E) (f : ι → E) :
    chartMetricInner (I := I) g α y a (∑ k ∈ s, f k)
      = ∑ k ∈ s, chartMetricInner (I := I) g α y a (f k) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.sum_empty, chartMetricInner_zero_right]
  | cons k s hk ih =>
      rw [Finset.sum_cons, chartMetricInner_add_right, ih, Finset.sum_cons]

/-- **Math.** **Positive definiteness** of the chart Gram inner product over
the trivialization base set: `⟨a, a⟩_y > 0` for `a ≠ 0`. Inherited from the
positive definiteness of the Gram matrix (`chartGramMatrix_posDef`). -/
theorem chartMetricInner_pos (g : RiemannianMetric I M) (α : M) {y : E}
    (hbase : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {a : E} (ha : a ≠ 0) :
    0 < chartMetricInner (I := I) g α y a a := by
  classical
  have hpd := Tensor.chartGramMatrix_posDef (I := I) g α hbase
  set c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => Geodesic.chartCoord (E := E) i a with hc
  have hcne : c ≠ 0 := by
    intro h0
    apply ha
    have hsum := (Module.finBasis ℝ E).sum_repr a
    rw [← hsum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hci : c i = 0 := by rw [h0]; rfl
    rw [hc] at hci
    simp only [Geodesic.chartCoord_def] at hci
    rw [hci, zero_smul]
  have hpos := hpd.dotProduct_mulVec_pos hcne
  calc (0 : ℝ)
      < star c ⬝ᵥ (Tensor.chartGramMatrix (I := I) g α
          ((extChartAt I α).symm y)).mulVec c := hpos
    _ = chartMetricInner (I := I) g α y a a := by
        simp only [chartMetricInner_def, chartGramOnE_def, dotProduct,
          Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hc]
        ring

/-- **Math.** A vector with vanishing chart Gram square norm over the
trivialization base set is zero. -/
theorem eq_zero_of_chartMetricInner_self_eq_zero (g : RiemannianMetric I M)
    (α : M) {y : E}
    (hbase : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {a : E} (h : chartMetricInner (I := I) g α y a a = 0) :
    a = 0 := by
  by_contra ha
  exact absurd h (ne_of_gt (chartMetricInner_pos (I := I) g α hbase ha))

/-! ### A `chartMetricInner`-orthonormal basis -/

/-- **Math.** At a chart point over the trivialization base set there is a
family of vectors of `E`, indexed by `Fin (dim E)`, **orthonormal for the
chart Gram inner product**: diagonalize the symmetric bilinear form
`⟨·,·⟩_y` (`LinearMap.BilinForm.exists_orthogonal_basis`) and normalize each
diagonal entry, which is positive by `chartMetricInner_pos`. -/
theorem exists_chartMetricInner_orthonormal (g : RiemannianMetric I M) (α : M)
    {y : E}
    (hbase : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∃ e₀ : Fin (Module.finrank ℝ E) → E, ∀ i j,
      chartMetricInner (I := I) g α y (e₀ i) (e₀ j)
        = if i = j then 1 else 0 := by
  classical
  -- package the chart Gram inner product as a bilinear form
  set B : LinearMap.BilinForm ℝ E := LinearMap.mk₂ ℝ
    (fun a b => chartMetricInner (I := I) g α y a b)
    (fun a a' b => chartMetricInner_add_left (I := I) g α y a a' b)
    (fun c a b => chartMetricInner_smul_left (I := I) g α y c a b)
    (fun a b b' => chartMetricInner_add_right (I := I) g α y a b b')
    (fun c a b => chartMetricInner_smul_right (I := I) g α y c a b) with hB
  have hBapply : ∀ a b : E, B a b = chartMetricInner (I := I) g α y a b :=
    fun a b => rfl
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (B := B)
    ⟨fun a b => by
      simp only [hBapply]
      exact chartMetricInner_comm (I := I) g α y a b⟩
  have hpos : ∀ i, 0 < B (v i) (v i) := fun i =>
    chartMetricInner_pos (I := I) g α hbase (v.ne_zero i)
  refine ⟨fun i => (Real.sqrt (B (v i) (v i)))⁻¹ • v i, fun i j => ?_⟩
  rw [chartMetricInner_smul_left, chartMetricInner_smul_right]
  rcases eq_or_ne i j with rfl | hij
  · rw [if_pos rfl, ← hBapply]
    have hd := hpos i
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hd.le]
    exact inv_mul_cancel₀ (ne_of_gt hd)
  · rw [if_neg hij]
    have h0 : B (v i) (v j) = 0 := hv hij
    rw [← hBapply, h0, mul_zero, mul_zero]

/-! ### Expansion in an orthonormal family (Parseval) -/

/-- **Math.** **Parseval expansion** in a `chartMetricInner`-orthonormal
family: for any `x z : E`,
`∑ i ⟨x, e i⟩_y ⟨z, e i⟩_y = ⟨x, z⟩_y`. An orthonormal family of
`dim E` vectors is automatically a basis; expand both arguments. -/
theorem chartMetricInner_parseval (g : RiemannianMetric I M) (α : M) {y : E}
    {e : Fin (Module.finrank ℝ E) → E}
    (horth : ∀ i j, chartMetricInner (I := I) g α y (e i) (e j)
      = if i = j then 1 else 0)
    (x z : E) :
    ∑ i, chartMetricInner (I := I) g α y x (e i)
        * chartMetricInner (I := I) g α y z (e i)
      = chartMetricInner (I := I) g α y x z := by
  classical
  -- linear independence of the orthonormal family
  have hli : LinearIndependent ℝ e := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have hc' := congrArg
      (fun w => chartMetricInner (I := I) g α y w (e j)) hc
    simp only [chartMetricInner_sum_left, chartMetricInner_smul_left,
      chartMetricInner_zero_left, horth] at hc'
    simpa [Finset.sum_ite_eq'] using hc'
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ E := by
    simp
  let bas : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbas : ∀ i, bas i = e i := fun i => by
    simp [bas, coe_basisOfLinearIndependentOfCardEqFinrank]
  -- coefficient formula: ⟨w, e j⟩ = repr w j
  have hcoeff : ∀ (w : E) (j : Fin (Module.finrank ℝ E)),
      chartMetricInner (I := I) g α y w (e j) = bas.repr w j := by
    intro w j
    conv_lhs => rw [← bas.sum_repr w]
    rw [chartMetricInner_sum_left]
    have : ∀ i, chartMetricInner (I := I) g α y (bas.repr w i • bas i) (e j)
        = bas.repr w i * (if i = j then 1 else 0) := by
      intro i
      rw [chartMetricInner_smul_left, hbas, horth]
    simp only [this, mul_ite, mul_one, mul_zero]
    simp [Finset.sum_ite_eq']
  -- expand z in the basis on the right-hand side
  have hz : chartMetricInner (I := I) g α y x z
      = ∑ j, bas.repr z j * chartMetricInner (I := I) g α y x (e j) := by
    conv_lhs => rw [← bas.sum_repr z]
    rw [chartMetricInner_sum_right]
    exact Finset.sum_congr rfl fun j _ => by
      rw [chartMetricInner_smul_right, hbas]
  rw [hz]
  exact Finset.sum_congr rfl fun j _ => by rw [hcoeff z j]; ring

/-! ### Continuity of the chart Gram inner product along curves -/

/-- **Math.** The chart Gram inner product of two continuous fields along a
continuous curve is continuous (in time), the Gram coefficients being
differentiable along the curve. -/
theorem continuousOn_chartMetricInner_comp {g : RiemannianMetric I M} {α : M}
    {u X Y : ℝ → E} {s : Set ℝ}
    (hu : ContinuousOn u s) (hX : ContinuousOn X s) (hY : ContinuousOn Y s)
    (hG : ∀ t ∈ s, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t)) :
    ContinuousOn (fun t => chartMetricInner (I := I) g α (u t) (X t) (Y t)) s := by
  simp only [chartMetricInner_def]
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · exact fun t ht => ((hG t ht i j).continuousAt).comp_continuousWithinAt (hu t ht)
  · have := (Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hX
    simpa [Function.comp_def, Geodesic.chartCoordFunctional_apply] using this
  · have := (Geodesic.chartCoordFunctional (E := E) j).continuous.comp_continuousOn hY
    simpa [Function.comp_def, Geodesic.chartCoordFunctional_apply] using this

/-! ### The frame reduction -/

/-- **Math.** **Frame reduction and Sturm comparison for chart Jacobi
fields.** Let `(J, ∇J)` be a Jacobi field along the coordinate curve `u` on
`[0, T]` with `J(0) = 0`, and suppose the curvature term satisfies the bound
`⟨ℛ(J, u̇)u̇, J⟩ ≤ K ⟨J, J⟩` along the curve (as follows, for a unit-speed
geodesic, from an upper sectional curvature bound `K ≥ 0`), with
`√K · T < π`. Then

`√⟨∇J(0), ∇J(0)⟩_{u(0)} · s_K(t) ≤ √⟨J(t), J(t)⟩_{u(t)}` for `t ∈ (0, T]`.

Expressing `J` in a parallel `⟨·,·⟩`-orthonormal frame along `u`
(`exists_parallelFrame_Icc`) turns the time-dependent chart Gram inner
product into the fixed Euclidean one (`chartMetricInner_parseval`), and the
covariant pair system into a genuine second-order ODE for the coordinate
curve; the vector-valued Sturm comparison (`vector_sturm_comparison`)
applies to that curve.

Blueprint: `lem:jacobi-frame-reduction`. -/
theorem jacobi_frame_sturm_comparison
    {g : RiemannianMetric I M} {α : M} {u J DJ : ℝ → E} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hπ : Real.sqrt K * T < Real.pi)
    (hJac : IsJacobiFieldOn (I := I) g α u J DJ 0 T)
    (hu : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc 0 T, (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hΓcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
      (Icc 0 T))
    (hcurv : ∀ t ∈ Ioo 0 T,
      chartMetricInner (I := I) g α (u t)
        (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t)) (J t)
        ≤ K * chartMetricInner (I := I) g α (u t) (J t) (J t))
    (hJ0 : J 0 = 0) :
    ∀ t ∈ Ioc 0 T,
      Real.sqrt (chartMetricInner (I := I) g α (u 0) (DJ 0) (DJ 0)) * sinK K t
        ≤ Real.sqrt (chartMetricInner (I := I) g α (u t) (J t) (J t)) := by
  classical
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  -- a parallel frame with `chartMetricInner`-orthonormal initial values
  obtain ⟨e₀, he₀⟩ := exists_chartMetricInner_orthonormal (I := I) g α (hbase 0 h0T)
  obtain ⟨KΓ, hKΓ⟩ : ∃ KΓ : ℝ≥0, ∀ t ∈ Icc (0 : ℝ) T,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ KΓ := by
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hΓcont
    refine ⟨C.toNNReal, fun t ht => ?_⟩
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact (hC t ht).trans (le_max_left _ _)
  obtain ⟨e, he_init, he_par⟩ :=
    exists_parallelFrame_Icc (I := I) g α u hT.le hΓcont hKΓ e₀
  -- the frame stays orthonormal
  have horthT : ∀ t ∈ Icc 0 T, ∀ i j,
      chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = if i = j then 1 else 0 := by
    intro t ht i j
    rw [chartMetricInner_parallelFrame_eq he_par hu hG hbase i j t ht,
      he_init i, he_init j]
    exact he₀ i j
  -- frame coordinates, in Euclidean space
  set σ : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    (EuclideanSpace.equiv (Fin (Module.finrank ℝ E)) ℝ).symm with hσ
  set V : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun t => σ (fun i => chartMetricInner (I := I) g α (u t) (J t) (e i t)) with hV
  set V' : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun t => σ (fun i => chartMetricInner (I := I) g α (u t) (DJ t) (e i t)) with hV'
  set V'' : ℝ → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    fun t => σ (fun i => -chartMetricInner (I := I) g α (u t)
      (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))
      (e i t)) with hV''
  have hVapply : ∀ t i, V t i = chartMetricInner (I := I) g α (u t) (J t) (e i t) :=
    fun t i => rfl
  -- squared Euclidean norm of frame coordinates = chart Gram square norm
  have hframe_normsq : ∀ (X : ℝ → E), ∀ t ∈ Icc 0 T,
      ‖σ (fun i => chartMetricInner (I := I) g α (u t) (X t) (e i t))‖ ^ 2
        = chartMetricInner (I := I) g α (u t) (X t) (X t) := by
    intro X t ht
    rw [EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    rw [← chartMetricInner_parseval (I := I) g α (horthT t ht) (X t) (X t)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
    have : σ (fun i => chartMetricInner (I := I) g α (u t) (X t) (e i t)) i
        = chartMetricInner (I := I) g α (u t) (X t) (e i t) := rfl
    rw [this, sq]
  have hnormsq : ∀ t ∈ Icc 0 T,
      ‖V t‖ ^ 2 = chartMetricInner (I := I) g α (u t) (J t) (J t) :=
    fun t ht => hframe_normsq J t ht
  have hnorm : ∀ t ∈ Icc 0 T,
      ‖V t‖ = Real.sqrt (chartMetricInner (I := I) g α (u t) (J t) (J t)) := by
    intro t ht
    rw [← hnormsq t ht, Real.sqrt_sq (norm_nonneg _)]
  -- interior differentiability of J and DJ
  have hJd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ J t := fun t ht =>
    ((hJac.hasDerivWithinAt_fst t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).differentiableAt
  have hDJd : ∀ t ∈ Ioo 0 T, DifferentiableAt ℝ DJ t := fun t ht =>
    ((hJac.hasDerivWithinAt_snd t (Ioo_subset_Icc_self ht)).hasDerivAt
      (Icc_mem_nhds ht.1 ht.2)).differentiableAt
  -- the frame-coordinate curve solves the second-order system: V ' = V'
  have hd1 : ∀ t ∈ Ioo 0 T, HasDerivAt V (V' t) t := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have hcomp : ∀ i, HasDerivAt
        (fun s => chartMetricInner (I := I) g α (u s) (J s) (e i s))
        (chartMetricInner (I := I) g α (u t) (DJ t) (e i t)) t := by
      intro i
      have h := hasDerivAt_chartMetricInner_along (I := I) g α u J (e i)
        (hu t htI) (hJd t ht) ((he_par i).differentiableAt ht)
        (hG t htI) (hbase t htI)
      rwa [hJac.covariantDerivCoord_fst ht,
        (he_par i).covariantDerivCoord_eq_zero ht,
        chartMetricInner_zero_right, add_zero] at h
    exact σ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.2 hcomp)
  -- ... and V' ' = V''
  have hd2 : ∀ t ∈ Ioo 0 T, HasDerivAt V' (V'' t) t := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have hcomp : ∀ i, HasDerivAt
        (fun s => chartMetricInner (I := I) g α (u s) (DJ s) (e i s))
        (-chartMetricInner (I := I) g α (u t)
          (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))
          (e i t)) t := by
      intro i
      have h := hasDerivAt_chartMetricInner_along (I := I) g α u DJ (e i)
        (hu t htI) (hDJd t ht) ((he_par i).differentiableAt ht)
        (hG t htI) (hbase t htI)
      rwa [hJac.covariantDerivCoord_snd ht,
        (he_par i).covariantDerivCoord_eq_zero ht,
        chartMetricInner_zero_right, add_zero, chartMetricInner_neg_left] at h
    exact σ.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_pi.2 hcomp)
  -- continuity of the coordinate curves on [0, T]
  have huc : ContinuousOn u (Icc 0 T) :=
    fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hVc : ContinuousOn V (Icc 0 T) := by
    refine σ.continuous.comp_continuousOn (continuousOn_pi.2 fun i => ?_)
    exact continuousOn_chartMetricInner_comp (I := I) huc
      hJac.continuousOn_fst (he_par i).continuousOn hG
  have hV'c : ContinuousOn V' (Icc 0 T) := by
    refine σ.continuous.comp_continuousOn (continuousOn_pi.2 fun i => ?_)
    exact continuousOn_chartMetricInner_comp (I := I) huc
      hJac.continuousOn_snd (he_par i).continuousOn hG
  -- the curvature inequality in Euclidean coordinates
  have hjac : ∀ t ∈ Ioo 0 T, -(K * ‖V t‖ ^ 2) ≤ inner ℝ (V'' t) (V t) := by
    intro t ht
    have htI := Ioo_subset_Icc_self ht
    have hip : inner ℝ (V'' t) (V t)
        = -chartMetricInner (I := I) g α (u t)
            (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))
            (J t) := by
      have hpars := chartMetricInner_parseval (I := I) g α (horthT t htI)
        (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t)) (J t)
      rw [PiLp.inner_apply, ← hpars, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : V'' t i = -chartMetricInner (I := I) g α (u t)
          (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))
          (e i t) := rfl
      have h2 : V t i = chartMetricInner (I := I) g α (u t) (J t) (e i t) := rfl
      rw [h1, h2]
      exact (RCLike.inner_apply _ _).trans
        (by rw [starRingEnd_apply, star_trivial]; ring)
    rw [hip, hnormsq t htI]
    exact neg_le_neg (hcurv t ht)
  -- V vanishes at 0
  have hV0 : V 0 = 0 := by
    have hz : (fun i => chartMetricInner (I := I) g α (u 0) (J 0) (e i 0))
        = fun _ => (0 : ℝ) := funext fun i => by
      rw [hJ0, chartMetricInner_zero_left]
    rw [hV]
    simp only [hz]
    exact map_zero σ
  -- boundedness of ‖V'‖ near 0⁺
  have hIooT : Ioo (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := by
    rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
    exact self_mem_nhdsWithin
  have hbdd : ∀ᶠ t in 𝓝[>] (0 : ℝ), ‖V' t‖ ≤ ‖V' 0‖ + 1 := by
    have h2 : Tendsto (fun t => ‖V' t‖) (𝓝[Icc 0 T] (0 : ℝ)) (𝓝 ‖V' 0‖) :=
      ((hV'c 0 h0T).norm : ContinuousWithinAt (fun t => ‖V' t‖) (Icc 0 T) 0)
    have h3 : ∀ᶠ t in 𝓝[Icc 0 T] (0 : ℝ), ‖V' t‖ ≤ ‖V' 0‖ + 1 :=
      h2.eventually (eventually_le_nhds (lt_add_one _))
    have hle : 𝓝[Ioo (0 : ℝ) T] (0 : ℝ) ≤ 𝓝[Icc 0 T] (0 : ℝ) :=
      nhdsWithin_mono _ Ioo_subset_Icc_self
    rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
    exact hle h3
  -- the slope at 0⁺ is ‖V'(0)‖ (mean value inequality on [δ, t], δ → 0⁺)
  have hslope : Tendsto (fun t => ‖V t‖ / t) (𝓝[>] (0 : ℝ)) (𝓝 ‖V' 0‖) := by
    rw [Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    have h2 : ContinuousWithinAt V' (Icc 0 T) 0 := hV'c 0 h0T
    rw [Metric.continuousWithinAt_iff] at h2
    obtain ⟨η, hη, hnear⟩ := h2 (ε / 2) (half_pos hε)
    refine ⟨min η T, lt_min hη hT, fun {t} ht hdist => ?_⟩
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0] at hdist
    have htη : t < η := lt_of_lt_of_le hdist (min_le_left _ _)
    have htT : t < T := lt_of_lt_of_le hdist (min_le_right _ _)
    -- mean value estimate: ‖V t − t • V'(0)‖ ≤ (ε/2) t
    have key : ‖V t - t • V' 0‖ ≤ ε / 2 * t := by
      have hmvt : ∀ δ, 0 < δ → δ ≤ t →
          ‖(V t - t • V' 0) - (V δ - δ • V' 0)‖ ≤ ε / 2 * (t - δ) := by
        intro δ hδ hδt
        have hsub : Icc δ t ⊆ Ioo 0 T := fun s hs =>
          ⟨lt_of_lt_of_le hδ hs.1, lt_of_le_of_lt hs.2 htT⟩
        have hf : ∀ x ∈ Icc δ t, HasDerivWithinAt (fun s => V s - s • V' 0)
            (V' x - V' 0) (Icc δ t) x := by
          intro x hx
          have hDx : HasDerivAt (fun s => V s - s • V' 0) (V' x - V' 0) x := by
            have hsm : HasDerivAt (fun s : ℝ => s • V' 0) ((1 : ℝ) • V' 0) x :=
              (hasDerivAt_id x).smul_const (V' 0)
            rw [one_smul] at hsm
            exact (hd1 x (hsub hx)).sub hsm
          exact hDx.hasDerivWithinAt
        have hbound : ∀ x ∈ Ico δ t, ‖V' x - V' 0‖ ≤ ε / 2 := by
          intro x hx
          have hx0 : 0 < x := lt_of_lt_of_le hδ hx.1
          have hxI : x ∈ Icc (0 : ℝ) T := ⟨hx0.le, (hx.2.le.trans htT.le)⟩
          have hxd : dist x 0 < η := by
            rw [Real.dist_eq, sub_zero, abs_of_pos hx0]
            exact hx.2.trans htη
          have := hnear hxI hxd
          rw [dist_eq_norm] at this
          exact this.le
        have := norm_image_sub_le_of_norm_deriv_le_segment' hf hbound t
          (right_mem_Icc.2 hδt)
        calc ‖(V t - t • V' 0) - (V δ - δ • V' 0)‖
            = ‖(fun s => V s - s • V' 0) t - (fun s => V s - s • V' 0) δ‖ := rfl
          _ ≤ ε / 2 * (t - δ) := this
      -- pass to the limit δ → 0⁺
      have hlim : Tendsto (fun δ => ‖(V t - t • V' 0) - (V δ - δ • V' 0)‖)
          (𝓝[>] (0 : ℝ)) (𝓝 ‖V t - t • V' 0‖) := by
        have hVten : Tendsto V (𝓝[>] (0 : ℝ)) (𝓝 (V 0)) := by
          have := (hVc 0 h0T : ContinuousWithinAt V (Icc 0 T) 0)
          have hle : 𝓝[Ioo (0 : ℝ) T] (0 : ℝ) ≤ 𝓝[Icc 0 T] (0 : ℝ) :=
            nhdsWithin_mono _ Ioo_subset_Icc_self
          rw [← nhdsWithin_Ioo_eq_nhdsGT hT]
          exact this.mono_left hle
        rw [hV0] at hVten
        have hsm : Tendsto (fun δ : ℝ => δ • V' 0) (𝓝[>] (0 : ℝ))
            (𝓝 ((0 : ℝ) • V' 0)) :=
          (tendsto_id.smul_const (V' 0)).mono_left nhdsWithin_le_nhds
        rw [zero_smul] at hsm
        have hsub : Tendsto (fun δ => V δ - δ • V' 0) (𝓝[>] (0 : ℝ)) (𝓝 (0 - 0)) :=
          hVten.sub hsm
        rw [sub_zero] at hsub
        have h8 : Tendsto (fun δ => (V t - t • V' 0) - (V δ - δ • V' 0))
            (𝓝[>] (0 : ℝ)) (𝓝 ((V t - t • V' 0) - 0)) :=
          tendsto_const_nhds.sub hsub
        rw [sub_zero] at h8
        exact h8.norm
      have hlim2 : Tendsto (fun δ : ℝ => ε / 2 * (t - δ)) (𝓝[>] (0 : ℝ))
          (𝓝 (ε / 2 * (t - 0))) :=
        (tendsto_const_nhds.mul (tendsto_const_nhds.sub tendsto_id)).mono_left
          nhdsWithin_le_nhds
      rw [sub_zero] at hlim2
      have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
          ‖(V t - t • V' 0) - (V δ - δ • V' 0)‖ ≤ ε / 2 * (t - δ) := by
        have hmem : Ioo (0 : ℝ) t ∈ 𝓝[>] (0 : ℝ) := by
          rw [← nhdsWithin_Ioo_eq_nhdsGT ht0]
          exact self_mem_nhdsWithin
        filter_upwards [hmem] with δ hδ
        exact hmvt δ hδ.1 hδ.2.le
      exact le_of_tendsto_of_tendsto hlim hlim2 hev
    -- conclude the ε-estimate for the slope
    have habs : |‖V t‖ / t - ‖V' 0‖| ≤ ε / 2 := by
      have hinv : ‖V t‖ / t = ‖t⁻¹ • V t‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0),
          inv_mul_eq_div]
      rw [hinv]
      have h5 : |‖t⁻¹ • V t‖ - ‖V' 0‖| ≤ ‖t⁻¹ • V t - V' 0‖ :=
        abs_norm_sub_norm_le _ _
      have h6 : t⁻¹ • V t - V' 0 = t⁻¹ • (V t - t • V' 0) := by
        rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt ht0), one_smul]
      have h7 : ‖t⁻¹ • (V t - t • V' 0)‖ ≤ ε / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 ht0)]
        calc t⁻¹ * ‖V t - t • V' 0‖ ≤ t⁻¹ * (ε / 2 * t) := by
              exact mul_le_mul_of_nonneg_left key (inv_pos.2 ht0).le
          _ = ε / 2 := by field_simp
      calc |‖t⁻¹ • V t‖ - ‖V' 0‖| ≤ ‖t⁻¹ • V t - V' 0‖ := h5
        _ = ‖t⁻¹ • (V t - t • V' 0)‖ := by rw [h6]
        _ ≤ ε / 2 := h7
    rw [Real.dist_eq]
    exact lt_of_le_of_lt habs (half_lt_self hε)
  -- apply the vector-valued Sturm comparison
  have hVs := vector_sturm_comparison hK hπ hVc hd1 hd2 hjac hbdd hslope
  -- identify the slope constant with the chart Gram norm of DJ(0)
  have hc : ‖V' 0‖ = Real.sqrt (chartMetricInner (I := I) g α (u 0) (DJ 0) (DJ 0)) := by
    have h1 : ‖V' 0‖ ^ 2 = chartMetricInner (I := I) g α (u 0) (DJ 0) (DJ 0) :=
      hframe_normsq DJ 0 h0T
    rw [← h1, Real.sqrt_sq (norm_nonneg _)]
  intro t ht
  have := hVs t ht
  rw [hc] at this
  rw [← hnorm t (Ioc_subset_Icc_self ht)]
  exact this

/-- **Math.** **No zero below `π/√K`**: a Jacobi field along `u` on `[0, T]`
with `J(0) = 0` and `∇J(0) ≠ 0`, under the curvature bound
`⟨ℛ(J, u̇)u̇, J⟩ ≤ K ⟨J, J⟩` with `K ≥ 0` and `√K · T < π`, does not vanish
on `(0, T]`. This is the chart-local analytic core of Morgan–Tian's
"minimal geodesics have no conjugate point before `π/√K`"
(blueprint `lem:conjugate-sturm`).

Blueprint: `lem:jacobi-frame-reduction`. -/
theorem jacobi_ne_zero_of_curvature_le
    {g : RiemannianMetric I M} {α : M} {u J DJ : ℝ → E} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hπ : Real.sqrt K * T < Real.pi)
    (hJac : IsJacobiFieldOn (I := I) g α u J DJ 0 T)
    (hu : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ u t)
    (hG : ∀ t ∈ Icc 0 T, ∀ i j,
      DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc 0 T, (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hΓcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t))
      (Icc 0 T))
    (hcurv : ∀ t ∈ Ioo 0 T,
      chartMetricInner (I := I) g α (u t)
        (chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t)) (J t)
        ≤ K * chartMetricInner (I := I) g α (u t) (J t) (J t))
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 ≠ 0) :
    ∀ t ∈ Ioc 0 T, J t ≠ 0 := by
  intro t ht hJt
  have hcomp := jacobi_frame_sturm_comparison (I := I) hT hK hπ hJac hu hG hbase
    hΓcont hcurv hJ0 t ht
  rw [hJt, chartMetricInner_zero_left, Real.sqrt_zero] at hcomp
  have hDJpos : 0 < chartMetricInner (I := I) g α (u 0) (DJ 0) (DJ 0) :=
    chartMetricInner_pos (I := I) g α (hbase 0 ⟨le_rfl, hT.le⟩) hDJ0
  have hsin : 0 < sinK K t := by
    refine sinK_pos K t hK ht.1 ?_
    calc Real.sqrt K * t ≤ Real.sqrt K * T :=
          mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)
      _ < Real.pi := hπ
  have : 0 < Real.sqrt (chartMetricInner (I := I) g α (u 0) (DJ 0) (DJ 0)) * sinK K t :=
    mul_pos (Real.sqrt_pos.2 hDJpos) hsin
  exact absurd (lt_of_lt_of_le this hcomp) (lt_irrefl 0)

end MorganTianLib

end

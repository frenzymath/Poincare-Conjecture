import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureVector
import DoCarmoLib.Riemannian.Jacobi.ChartCurvatureContraction
import DoCarmoLib.Riemannian.Jacobi.ParallelFrame
import DoCarmoLib.Riemannian.Connection.ChartCurvatureMovingPoint
import DoCarmoLib.Riemannian.Exponential.GaussLemma
import DoCarmoLib.Riemannian.TensorBundle.MusicalIso

/-!
# The manifold ↔ chart curvature bridge, and positive-definiteness of the chart Gram form

This file supplies the last reconciliation helpers needed for the chart-change
covariance of the Jacobi pair system (`JacobiChartTransfer.lean`,
`lem:jacobi-field-coordinates`).  The headline result is the **general-vector,
moving-base-point** curvature bridge

`curvatureFormAt g p (F v)(F w)(F z)(F t) = − ⟨ℛ_chart(φp)(v, w)z, t⟩_{G(φp)}`,

where `F x = ∑_a x^a X_a(p)` realizes chart coordinates on the chart frame at
`p`, `ℛ_chart = chartCurvature g α` is the coordinate curvature (Morgan–Tian
sign) and the pairing is the chart Gram inner product.  The sign is the do
Carmo ↔ Morgan–Tian convention flip.

Where the Poincaré (Morgan–Tian §1.4) development derived the basis case inline
from a `q`-centred smooth frame, we instead use DoCarmoLib's own frame-free
moving-point expansion `curvatureOperatorAt_chartBasis_expansion`
(`Connection.ChartCurvatureMovingPoint`), so no reconciliation with the
Poincaré `FrameReduction`/`CurvatureFrameBridge` cone is needed.  The
multilinear extension is carried by `curvatureOperatorAt`'s own additivity /
homogeneity, avoiding the `curvatureForm`-tensor slot machinery.

Also collected here: positive-definiteness (`chartMetricInner_pos`) and
negation (`chartMetricInner_neg_left`) of the chart Gram inner product, ported
from the Poincaré `FrameReduction`, feeding the definiteness argument of
`chartCurvature_coordChange`.

Blueprint: `lem:jacobi-field-coordinates` (`cor:dc-ch5-2-5` route).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2–1.4.
-/

open Set Manifold Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Negation and positive-definiteness of the chart Gram inner product -/

/-- **Math.** The chart Gram inner product is negated with its first argument. -/
theorem chartMetricInner_neg_left (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricInner (I := I) g α y (-a) b
      = -chartMetricInner (I := I) g α y a b := by
  have h := chartMetricInner_smul_left (I := I) g α y (-1) a b
  simp only [neg_one_smul, neg_one_mul] at h
  exact h

/-- **Math.** **Positive definiteness** of the chart Gram inner product over the
trivialization base set: `⟨a, a⟩_y > 0` for `a ≠ 0`.  Inherited from the
positive definiteness of the Gram matrix (`chartGramMatrix_posDef`). -/
theorem chartMetricInner_pos (g : RiemannianMetric I M) (α : M) {y : E}
    (hbase : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {a : E} (ha : a ≠ 0) :
    0 < chartMetricInner (I := I) g α y a a := by
  classical
  have hpd := chartGramMatrix_posDef (I := I) g α hbase
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
      < star c ⬝ᵥ (chartGramMatrix (I := I) g α
          ((extChartAt I α).symm y)).mulVec c := hpos
    _ = chartMetricInner (I := I) g α y a a := by
        simp only [chartMetricInner_def, chartGramOnE_def, dotProduct,
          Matrix.mulVec, Pi.star_apply, star_trivial, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hc]
        ring

/-! ### Bilinearity helpers for the metric pairing -/

/-- **Math.** The metric pairing of a finite linear combination, left slot. -/
theorem metricInner_finsetSum_smul_left (g : RiemannianMetric I M) (p : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I p) (w : TangentSpace I p) :
    g.metricInner p (∑ a ∈ s, c a • v a) w
      = ∑ a ∈ s, c a * g.metricInner p (v a) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g.metricInner_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, g.metricInner_add_left, g.metricInner_smul_left, ih,
      Finset.sum_insert ha]

/-- **Math.** The metric pairing of a finite linear combination, right slot. -/
theorem metricInner_finsetSum_smul_right (g : RiemannianMetric I M) (p : M) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (v : TangentSpace I p) (w : ι → TangentSpace I p) :
    g.metricInner p v (∑ a ∈ s, c a • w a)
      = ∑ a ∈ s, c a * g.metricInner p v (w a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [g.metricInner_zero_right]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, g.metricInner_add_right, g.metricInner_smul_right, ih,
      Finset.sum_insert ha]

/-- **Math.** The chart Gram pairing of two basis vectors is the Gram entry:
`⟨e_m, e_l⟩_{G(y)} = G_{ml}(y)`. -/
theorem chartMetricInner_basis (g : RiemannianMetric I M) (α : M) (y : E)
    (m l : Fin (Module.finrank ℝ E)) :
    chartMetricInner (I := I) g α y (Module.finBasis ℝ E m) (Module.finBasis ℝ E l)
      = chartGramOnE (I := I) g α m l y := by
  classical
  rw [chartMetricInner_def]
  have hδ : ∀ a b : Fin (Module.finrank ℝ E),
      Geodesic.chartCoord (E := E) a (Module.finBasis ℝ E b)
        = if b = a then (1 : ℝ) else 0 := by
    intro a b
    rw [Geodesic.chartCoord_def, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [hδ, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

/-! ### The chart Christoffel contraction on basis vectors -/

/-- **Math.** The Christoffel contraction on chart basis vectors is the
Christoffel symbol: `Γ_y(e_i, e_j) = ∑_k Γ^k_{ij}(y) e_k`. -/
theorem chartChristoffelBilin_basis (g : RiemannianMetric I M) (α : M)
    (y : E) (i j : Fin (Module.finrank ℝ E)) :
    chartChristoffelBilin (I := I) g α y (Module.finBasis ℝ E i)
        (Module.finBasis ℝ E j)
      = ∑ k, chartChristoffel (I := I) g α i j k y • Module.finBasis ℝ E k := by
  classical
  rw [chartChristoffelBilin_apply, Geodesic.chartChristoffelContraction_def]
  have hδ : ∀ a b : Fin (Module.finrank ℝ E),
      Geodesic.chartCoord (E := E) a (Module.finBasis ℝ E b)
        = if b = a then (1 : ℝ) else 0 := by
    intro a b
    rw [Geodesic.chartCoord_def, Module.Basis.repr_self, Finsupp.single_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp only [hδ, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Math.** Derivative of the Christoffel contraction in the chart point,
evaluated on basis vectors: `(∂_dΓ)_y(e_i, e_j) = ∑_k (∂_dΓ^k_{ij})(y) e_k`
for `y` interior to the chart target. -/
theorem fderiv_chartChristoffelBilin_basis (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ interior (extChartAt I α).target) (d : E)
    (i j : Fin (Module.finrank ℝ E)) :
    fderiv ℝ (chartChristoffelBilin (I := I) g α) y d (Module.finBasis ℝ E i)
        (Module.finBasis ℝ E j)
      = ∑ k, (fderiv ℝ (chartChristoffel (I := I) g α i j k) y d)
          • Module.finBasis ℝ E k := by
  classical
  have hγdiff : ∀ a b k, HasFDerivAt (chartChristoffel (I := I) g α a b k)
      (fderiv ℝ (chartChristoffel (I := I) g α a b k) y) y := by
    intro a b k
    have h := ((chartChristoffel_contDiffOn_interior (I := I) g α a b k).contDiffAt
      (isOpen_interior.mem_nhds hy)).differentiableAt (by norm_num)
    exact h.hasFDerivAt
  have hD : HasFDerivAt (chartChristoffelBilin (I := I) g α)
      (∑ a, ∑ b, ∑ k,
        ((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E)
            (Geodesic.chartCoordFunctional (E := E) a)).comp
          (ContinuousLinearMap.smulRightL ℝ E E
            (Geodesic.chartCoordFunctional (E := E) b))).comp
        ((fderiv ℝ (chartChristoffel (I := I) g α a b k) y).smulRight
          (Module.finBasis ℝ E k))) y := by
    unfold chartChristoffelBilin
    exact HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ =>
      HasFDerivAt.fun_sum fun k _ => HasFDerivAt.comp
        (g := ⇑((ContinuousLinearMap.smulRightL ℝ E (E →L[ℝ] E)
            (Geodesic.chartCoordFunctional (E := E) a)).comp
          (ContinuousLinearMap.smulRightL ℝ E E
            (Geodesic.chartCoordFunctional (E := E) b))))
        (f := fun x => chartChristoffel (I := I) g α a b k x • Module.finBasis ℝ E k)
        y (ContinuousLinearMap.hasFDerivAt _)
        ((hγdiff a b k).smul_const (Module.finBasis ℝ E k))
  rw [hD.fderiv]
  have hδ : ∀ a b : Fin (Module.finrank ℝ E),
      Geodesic.chartCoordFunctional (E := E) a (Module.finBasis ℝ E b)
        = if b = a then (1 : ℝ) else 0 := by
    intro a b
    rw [Geodesic.chartCoordFunctional_apply, Geodesic.chartCoord_def,
      Module.Basis.repr_self, Finsupp.single_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRightL_apply_apply, hδ, ite_smul, one_smul, zero_smul,
    apply_ite (fun f : E →L[ℝ] E => f (Module.finBasis ℝ E j)),
    ContinuousLinearMap.zero_apply, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1600000 in
/-- **Math.** **The chart curvature in Christoffel components** — the classical
formula
`ℛ(e_i, e_j)e_k = ∑_m (∂_iΓ^m_{jk} − ∂_jΓ^m_{ik}
+ ∑_r (Γ^r_{jk}Γ^m_{ir} − Γ^r_{ik}Γ^m_{jr})) e_m`
in Morgan–Tian's convention, for `y` interior to the chart target. -/
theorem chartCurvature_basis (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ interior (extChartAt I α).target)
    (i j k : Fin (Module.finrank ℝ E)) :
    chartCurvature (I := I) g α y (Module.finBasis ℝ E i) (Module.finBasis ℝ E j)
        (Module.finBasis ℝ E k)
      = ∑ m, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) y
            - partialDeriv (E := E) j (chartChristoffel (I := I) g α i k m) y
            + ∑ r, (chartChristoffel (I := I) g α j k r y
                      * chartChristoffel (I := I) g α i r m y
                  - chartChristoffel (I := I) g α i k r y
                      * chartChristoffel (I := I) g α j r m y))
          • Module.finBasis ℝ E m := by
  rw [chartCurvature_def, christoffelCurvature]
  rw [fderiv_chartChristoffelBilin_basis (I := I) g α hy _ j k,
    fderiv_chartChristoffelBilin_basis (I := I) g α hy _ i k,
    chartChristoffelBilin_basis (I := I) g α y j k,
    chartChristoffelBilin_basis (I := I) g α y i k, map_sum, map_sum]
  simp only [map_smul, chartChristoffelBilin_basis (I := I) g α y i,
    chartChristoffelBilin_basis (I := I) g α y j, partialDeriv]
  refine (Module.finBasis ℝ E).ext_elem fun m₀ => ?_
  simp only [map_add, map_sub, map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.coe_add, Finsupp.coe_sub,
    Finsupp.coe_finset_sum, Pi.add_apply, Pi.sub_apply, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.finset_sum_apply, Finsupp.single_apply]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, mul_zero,
    mul_one, smul_eq_mul]
  rw [Finset.sum_sub_distrib]
  ring

/-! ### Multilinearity of the chart curvature in its three slots -/

/-- **Math.** Additivity of the chart curvature in its first slot. -/
theorem chartCurvature_add_fst (g : RiemannianMetric I M) (α : M) (y w z : E)
    (v₁ v₂ : E) :
    chartCurvature (I := I) g α y (v₁ + v₂) w z
      = chartCurvature (I := I) g α y v₁ w z + chartCurvature (I := I) g α y v₂ w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its first slot. -/
theorem chartCurvature_smul_fst (g : RiemannianMetric I M) (α : M) (y w z : E)
    (c : ℝ) (v : E) :
    chartCurvature (I := I) g α y (c • v) w z
      = c • chartCurvature (I := I) g α y v w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

/-- **Math.** Additivity of the chart curvature in its second slot. -/
theorem chartCurvature_add_middle (g : RiemannianMetric I M) (α : M) (y v z : E)
    (w₁ w₂ : E) :
    chartCurvature (I := I) g α y v (w₁ + w₂) z
      = chartCurvature (I := I) g α y v w₁ z + chartCurvature (I := I) g α y v w₂ z := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its second slot. -/
theorem chartCurvature_smul_middle (g : RiemannianMetric I M) (α : M) (y v z : E)
    (c : ℝ) (w : E) :
    chartCurvature (I := I) g α y v (c • w) z
      = c • chartCurvature (I := I) g α y v w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

/-- **Math.** Additivity of the chart curvature in its third slot. -/
theorem chartCurvature_add_right (g : RiemannianMetric I M) (α : M) (y v w : E)
    (z₁ z₂ : E) :
    chartCurvature (I := I) g α y v w (z₁ + z₂)
      = chartCurvature (I := I) g α y v w z₁ + chartCurvature (I := I) g α y v w z₂ := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its third slot. -/
theorem chartCurvature_smul_right (g : RiemannianMetric I M) (α : M) (y v w : E)
    (c : ℝ) (z : E) :
    chartCurvature (I := I) g α y v w (c • z)
      = c • chartCurvature (I := I) g α y v w z := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Math.** The chart curvature of finite linear combinations expands
multilinearly over all three slots. -/
theorem chartCurvature_sum₃ (g : RiemannianMetric I M) (α : M) (y : E)
    {ι : Type*} (s : Finset ι) (cv cw cz : ι → ℝ) (e : ι → E) :
    chartCurvature (I := I) g α y (∑ a ∈ s, cv a • e a) (∑ b ∈ s, cw b • e b)
        (∑ c ∈ s, cz c • e c)
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, (cv a * cw b * cz c)
          • chartCurvature (I := I) g α y (e a) (e b) (e c) := by
  classical
  have hzero : ∀ w z : E, chartCurvature (I := I) g α y 0 w z = 0 := by
    intro w z
    simp [chartCurvature_def, christoffelCurvature]
  have hzero₂ : ∀ v z : E, chartCurvature (I := I) g α y v 0 z = 0 := by
    intro v z
    simp [chartCurvature_def, christoffelCurvature]
  have hzero₃ : ∀ v w : E, chartCurvature (I := I) g α y v w 0 = 0 := by
    intro v w
    simp [chartCurvature_def, christoffelCurvature]
  have h₁ : ∀ (t : Finset ι) (w z : E),
      chartCurvature (I := I) g α y (∑ a ∈ t, cv a • e a) w z
        = ∑ a ∈ t, cv a • chartCurvature (I := I) g α y (e a) w z := by
    intro t w z
    induction t using Finset.induction_on with
    | empty => simpa using hzero w z
    | @insert a t' ha ih =>
      rw [Finset.sum_insert ha, chartCurvature_add_fst (I := I) g α,
        chartCurvature_smul_fst (I := I) g α, ih, Finset.sum_insert ha]
  have h₂ : ∀ (t : Finset ι) (v z : E),
      chartCurvature (I := I) g α y v (∑ b ∈ t, cw b • e b) z
        = ∑ b ∈ t, cw b • chartCurvature (I := I) g α y v (e b) z := by
    intro t v z
    induction t using Finset.induction_on with
    | empty => simpa using hzero₂ v z
    | @insert b t' hb ih =>
      rw [Finset.sum_insert hb, chartCurvature_add_middle (I := I) g α,
        chartCurvature_smul_middle (I := I) g α, ih, Finset.sum_insert hb]
  have h₃ : ∀ (t : Finset ι) (v w : E),
      chartCurvature (I := I) g α y v w (∑ c ∈ t, cz c • e c)
        = ∑ c ∈ t, cz c • chartCurvature (I := I) g α y v w (e c) := by
    intro t v w
    induction t using Finset.induction_on with
    | empty => simpa using hzero₃ v w
    | @insert c t' hc ih =>
      rw [Finset.sum_insert hc, chartCurvature_add_right (I := I) g α,
        chartCurvature_smul_right (I := I) g α, ih, Finset.sum_insert hc]
  rw [h₁ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h₂ s, Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h₃ s, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_smul, smul_smul]

/-! ### Multilinear expansion of the pointwise curvature form -/

section Curvature

variable [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- **Math.** `curvatureFormAt` is the metric-lowered pointwise curvature
operator (definitional). -/
theorem curvatureFormAt_eq_metricInner (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (x y z t : TangentSpace I p) :
    nabla.curvatureFormAt g p x y z t
      = g.metricInner p (nabla.curvatureOperatorAt p x y z) t := rfl

/-- **Math.** Additivity of `curvatureFormAt` in its first slot. -/
theorem curvatureFormAt_add_fst (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v₁ v₂ w z t : TangentSpace I p) :
    nabla.curvatureFormAt g p (v₁ + v₂) w z t
      = nabla.curvatureFormAt g p v₁ w z t + nabla.curvatureFormAt g p v₂ w z t := by
  simp only [curvatureFormAt_eq_metricInner, nabla.curvatureOperatorAt_add_left,
    g.metricInner_add_left]

/-- **Math.** Homogeneity of `curvatureFormAt` in its first slot. -/
theorem curvatureFormAt_smul_fst (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (c : ℝ) (v w z t : TangentSpace I p) :
    nabla.curvatureFormAt g p (c • v) w z t = c * nabla.curvatureFormAt g p v w z t := by
  simp only [curvatureFormAt_eq_metricInner, nabla.curvatureOperatorAt_smul_left,
    g.metricInner_smul_left, smul_eq_mul]

/-- **Math.** Additivity of `curvatureFormAt` in its second slot. -/
theorem curvatureFormAt_add_snd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w₁ w₂ z t : TangentSpace I p) :
    nabla.curvatureFormAt g p v (w₁ + w₂) z t
      = nabla.curvatureFormAt g p v w₁ z t + nabla.curvatureFormAt g p v w₂ z t := by
  simp only [curvatureFormAt_eq_metricInner, nabla.curvatureOperatorAt_add_middle,
    g.metricInner_add_left]

/-- **Math.** Homogeneity of `curvatureFormAt` in its second slot. -/
theorem curvatureFormAt_smul_snd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (c : ℝ) (v w z t : TangentSpace I p) :
    nabla.curvatureFormAt g p v (c • w) z t = c * nabla.curvatureFormAt g p v w z t := by
  simp only [curvatureFormAt_eq_metricInner, nabla.curvatureOperatorAt_smul_middle,
    g.metricInner_smul_left, smul_eq_mul]

/-- **Math.** Additivity of `curvatureFormAt` in its third slot. -/
theorem curvatureFormAt_add_trd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z₁ z₂ t : TangentSpace I p) :
    nabla.curvatureFormAt g p v w (z₁ + z₂) t
      = nabla.curvatureFormAt g p v w z₁ t + nabla.curvatureFormAt g p v w z₂ t := by
  simp only [curvatureFormAt_eq_metricInner, nabla.curvatureOperatorAt_add_right,
    g.metricInner_add_left]

/-- **Math.** Homogeneity of `curvatureFormAt` in its third slot. -/
theorem curvatureFormAt_smul_trd (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (c : ℝ) (v w z t : TangentSpace I p) :
    nabla.curvatureFormAt g p v w (c • z) t = c * nabla.curvatureFormAt g p v w z t := by
  simp only [curvatureFormAt_eq_metricInner, nabla.curvatureOperatorAt_smul_right,
    g.metricInner_smul_left, smul_eq_mul]

/-- **Math.** Additivity of `curvatureFormAt` in its fourth slot. -/
theorem curvatureFormAt_add_fth (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (v w z t₁ t₂ : TangentSpace I p) :
    nabla.curvatureFormAt g p v w z (t₁ + t₂)
      = nabla.curvatureFormAt g p v w z t₁ + nabla.curvatureFormAt g p v w z t₂ := by
  simp only [curvatureFormAt_eq_metricInner, g.metricInner_add_right]

/-- **Math.** Homogeneity of `curvatureFormAt` in its fourth slot. -/
theorem curvatureFormAt_smul_fth (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) (c : ℝ) (v w z t : TangentSpace I p) :
    nabla.curvatureFormAt g p v w z (c • t) = c * nabla.curvatureFormAt g p v w z t := by
  simp only [curvatureFormAt_eq_metricInner, g.metricInner_smul_right, smul_eq_mul]

/-- **Math.** The pointwise curvature form of four finite linear combinations
expands quadrilinearly. -/
theorem curvatureFormAt_sum₄ (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (p : M) {ι : Type*} (s : Finset ι)
    (cv cw cz ct : ι → ℝ) (e : ι → TangentSpace I p) :
    nabla.curvatureFormAt g p (∑ a ∈ s, cv a • e a) (∑ b ∈ s, cw b • e b)
        (∑ c ∈ s, cz c • e c) (∑ d ∈ s, ct d • e d)
      = ∑ a ∈ s, ∑ b ∈ s, ∑ c ∈ s, ∑ d ∈ s, cv a * cw b * cz c * ct d
          * nabla.curvatureFormAt g p (e a) (e b) (e c) (e d) := by
  classical
  have hzero₁ : ∀ w z t, nabla.curvatureFormAt g p 0 w z t = 0 := by
    intro w z t
    have h := curvatureFormAt_smul_fst g nabla p 0 0 w z t
    simpa using h
  have hzero₂ : ∀ v z t, nabla.curvatureFormAt g p v 0 z t = 0 := by
    intro v z t
    have h := curvatureFormAt_smul_snd g nabla p 0 v 0 z t
    simpa using h
  have hzero₃ : ∀ v w t, nabla.curvatureFormAt g p v w 0 t = 0 := by
    intro v w t
    have h := curvatureFormAt_smul_trd g nabla p 0 v w 0 t
    simpa using h
  have hzero₄ : ∀ v w z, nabla.curvatureFormAt g p v w z 0 = 0 := by
    intro v w z
    have h := curvatureFormAt_smul_fth g nabla p 0 v w z 0
    simpa using h
  have h₁ : ∀ (u : Finset ι) (w z t : TangentSpace I p),
      nabla.curvatureFormAt g p (∑ a ∈ u, cv a • e a) w z t
        = ∑ a ∈ u, cv a * nabla.curvatureFormAt g p (e a) w z t := by
    intro u w z t
    induction u using Finset.induction_on with
    | empty => simpa using hzero₁ w z t
    | @insert a u' ha ih =>
      rw [Finset.sum_insert ha, curvatureFormAt_add_fst,
        curvatureFormAt_smul_fst, ih, Finset.sum_insert ha]
  have h₂ : ∀ (u : Finset ι) (v z t : TangentSpace I p),
      nabla.curvatureFormAt g p v (∑ b ∈ u, cw b • e b) z t
        = ∑ b ∈ u, cw b * nabla.curvatureFormAt g p v (e b) z t := by
    intro u v z t
    induction u using Finset.induction_on with
    | empty => simpa using hzero₂ v z t
    | @insert b u' hb ih =>
      rw [Finset.sum_insert hb, curvatureFormAt_add_snd,
        curvatureFormAt_smul_snd, ih, Finset.sum_insert hb]
  have h₃ : ∀ (u : Finset ι) (v w t : TangentSpace I p),
      nabla.curvatureFormAt g p v w (∑ c ∈ u, cz c • e c) t
        = ∑ c ∈ u, cz c * nabla.curvatureFormAt g p v w (e c) t := by
    intro u v w t
    induction u using Finset.induction_on with
    | empty => simpa using hzero₃ v w t
    | @insert c u' hc ih =>
      rw [Finset.sum_insert hc, curvatureFormAt_add_trd,
        curvatureFormAt_smul_trd, ih, Finset.sum_insert hc]
  have h₄ : ∀ (u : Finset ι) (v w z : TangentSpace I p),
      nabla.curvatureFormAt g p v w z (∑ d ∈ u, ct d • e d)
        = ∑ d ∈ u, ct d * nabla.curvatureFormAt g p v w z (e d) := by
    intro u v w z
    induction u using Finset.induction_on with
    | empty => simpa using hzero₄ v w z
    | @insert d u' hd ih =>
      rw [Finset.sum_insert hd, curvatureFormAt_add_fth,
        curvatureFormAt_smul_fth, ih, Finset.sum_insert hd]
  rw [h₁ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [h₂ s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h₃ s, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h₄ s, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

/-! ### The manifold ↔ chart curvature bridge -/

/-- **Math.** The metric pairing of two chart-frame basis vectors at a chart
point is the chart Gram entry. -/
theorem metricInner_chartBasisVecFiber (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source) (m l : Fin (Module.finrank ℝ E)) :
    g.metricInner p (chartBasisVecFiber (I := I) α m p) (chartBasisVecFiber (I := I) α l p)
      = chartGramOnE (I := I) g α m l (extChartAt I α p) := by
  have hpe : (extChartAt I α).symm (extChartAt I α p) = p :=
    (extChartAt I α).left_inv (by rwa [extChartAt_source])
  rw [chartGramOnE_def, hpe, chartGramMatrix_apply, RiemannianMetric.metricInner_apply]

/-- **Math.** **The manifold ↔ chart curvature bridge (general realization).**
For `p` in the chart at `α` with image `y = φ(p)` and coordinate vectors
`v, w, z, t : E`, the pointwise curvature `(0,4)`-form of the Levi-Civita
connection evaluated on the chart-frame realizations `F(x) = ∑_a x^a X_a(p)`
is the chart Gram pairing of the Christoffel-formula curvature (Morgan–Tian
sign): `ℛ(F v, F w, F z, F t)(p) = −⟨ℛ_chart(y)(v, w)z, t⟩_{G(y)}`.

The basis case is the metric-lowered avatar of the frame-free moving-point
operator expansion `curvatureOperatorAt_chartBasis_expansion`; the sign is the
do Carmo ↔ Morgan–Tian convention flip. -/
theorem curvatureFormAt_chartFrame (g : RiemannianMetric I M) {α p : M}
    (hp : p ∈ (chartAt H α).source) (v w z t : E) :
    g.leviCivitaConnection.curvatureFormAt g p
        (∑ a, Geodesic.chartCoord (E := E) a v • chartBasisVecFiber (I := I) α a p)
        (∑ b, Geodesic.chartCoord (E := E) b w • chartBasisVecFiber (I := I) α b p)
        (∑ c, Geodesic.chartCoord (E := E) c z • chartBasisVecFiber (I := I) α c p)
        (∑ d, Geodesic.chartCoord (E := E) d t • chartBasisVecFiber (I := I) α d p)
      = - chartMetricInner (I := I) g α (extChartAt I α p)
          (chartCurvature (I := I) g α (extChartAt I α p) v w z) t := by
  classical
  have hy_int : extChartAt I α p ∈ interior (extChartAt I α).target := by
    rw [(isOpen_extChartAt_target (I := I) α).interior_eq]
    exact (extChartAt I α).map_source (by rwa [extChartAt_source])
  -- basis 4-tuple case at the moving point `p`
  have hframe_form : ∀ i j k l : Fin (Module.finrank ℝ E),
      g.leviCivitaConnection.curvatureFormAt g p
          (chartBasisVecFiber (I := I) α i p) (chartBasisVecFiber (I := I) α j p)
          (chartBasisVecFiber (I := I) α k p) (chartBasisVecFiber (I := I) α l p)
        = - chartMetricInner (I := I) g α (extChartAt I α p)
            (chartCurvature (I := I) g α (extChartAt I α p)
              (Module.finBasis ℝ E i) (Module.finBasis ℝ E j) (Module.finBasis ℝ E k))
            (Module.finBasis ℝ E l) := by
    intro i j k l
    rw [curvatureFormAt_eq_metricInner,
      curvatureOperatorAt_chartBasis_expansion (I := I) g α i j k hp,
      metricInner_finsetSum_smul_left,
      chartCurvature_basis (I := I) g α hy_int i j k,
      chartMetricInner_sum_left]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [metricInner_chartBasisVecFiber (I := I) g hp m l,
      chartMetricInner_smul_left, chartMetricInner_basis, ← neg_mul]
    congr 1
    have hcancel :
        (∑ s, (chartChristoffel (I := I) g α i k s (extChartAt I α p)
              * chartChristoffel (I := I) g α j s m (extChartAt I α p)
            - chartChristoffel (I := I) g α j k s (extChartAt I α p)
              * chartChristoffel (I := I) g α i s m (extChartAt I α p)))
          + (∑ r, (chartChristoffel (I := I) g α j k r (extChartAt I α p)
                * chartChristoffel (I := I) g α i r m (extChartAt I α p)
              - chartChristoffel (I := I) g α i k r (extChartAt I α p)
                * chartChristoffel (I := I) g α j r m (extChartAt I α p))) = 0 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_eq_zero fun x _ => by ring
    linarith [hcancel]
  -- quadrilinear expansion on both sides
  rw [curvatureFormAt_sum₄ g g.leviCivitaConnection p Finset.univ
      (fun a => Geodesic.chartCoord (E := E) a v)
      (fun b => Geodesic.chartCoord (E := E) b w)
      (fun c => Geodesic.chartCoord (E := E) c z)
      (fun d => Geodesic.chartCoord (E := E) d t)
      (fun a => chartBasisVecFiber (I := I) α a p)]
  conv_rhs =>
    rw [show v = ∑ a, Geodesic.chartCoord (E := E) a v • Module.finBasis ℝ E a from
          by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr],
        show w = ∑ b, Geodesic.chartCoord (E := E) b w • Module.finBasis ℝ E b from
          by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr],
        show z = ∑ c, Geodesic.chartCoord (E := E) c z • Module.finBasis ℝ E c from
          by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]]
  rw [chartCurvature_sum₃ (I := I) g α (extChartAt I α p) Finset.univ]
  conv_rhs =>
    rw [show t = ∑ d, Geodesic.chartCoord (E := E) d t • Module.finBasis ℝ E d from
          by simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]]
  rw [chartMetricInner_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [chartMetricInner_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [chartMetricInner_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [chartMetricInner_sum_right, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [chartMetricInner_smul_left, chartMetricInner_smul_right, hframe_form a b c d]
  ring

end Curvature

end Riemannian.Jacobi

end

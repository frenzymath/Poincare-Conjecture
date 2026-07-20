/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Jacobi/ChartCurvatureNaturality.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Jacobi.ChartCurvatureVector
import PetersenLib.Riemannian.Jacobi.SurfaceCurvatureCommutation

/-!
# Naturality of the chart curvature: basis values, multilinearity, slot reindexing

Two chart-level presentations of the same Morgan–Tian curvature live in the vendored
Jacobi cone and must be reconciled before either can talk to Petersen's Ch. 3 tensor:

* `chartCurvature g α y X Y Z` (`Riemannian/Jacobi/ChartCurvatureVector.lean`) —
  `ℛ(X,Y)Z` built as `christoffelCurvature` of the bilinear-map-valued Christoffel field
  `chartChristoffelBilin`, i.e. by differentiating `Γ` *as a map* `E → E →L[ℝ] E →L[ℝ] E`;
* `chartCurvatureContraction2 g α X Y Z y`
  (`Riemannian/Jacobi/SurfaceCurvatureCommutation.lean`) — `ℛ(X,Y)Z` built by
  contracting the scalar coefficient `chartCurvatureCoef` `Rˡ_{ijk}` against the
  components of `X, Y, Z`.

They are the same curvature, but only after a **slot swap**: this file proves
`chartCurvatureContraction2 g α X Y Z y = chartCurvature g α y Y X Z` on the chart
interior (`chartCurvatureContraction2_eq_chartCurvature`). That swap is a genuine trap —
feeding the two presentations the same slot order gives the *negated* curvature.

## Contents

* `chartChristoffelBilin_basis`, `fderiv_chartChristoffelBilin_basis` — the Christoffel
  contraction and its chart-point derivative read on the model basis: `Γ_y(e_i, e_j) =
  ∑_k Γ^k_{ij}(y) e_k` and its `∂_d`.
* `chartCurvature_basis` — the **classical Christoffel formula** for `chartCurvature` on
  basis vectors, `ℛ(e_i, e_j)e_k = ∑_m (∂_iΓ^m_{jk} − ∂_jΓ^m_{ik} + ∑_r (Γ^r_{jk}Γ^m_{ir}
  − Γ^r_{ik}Γ^m_{jr})) e_m`, valid at `y` interior to the chart target.
* `chartCurvature_add_*` / `chartCurvature_smul_*`, `chartCurvature_sum₃` — trilinearity,
  inherited from `christoffelCurvature`'s own linearity, no tensor-slot machinery.
* `chartCurvatureContraction2_eq_chartCurvature` — the reindexing above.

## Failure memory: what this cone can and cannot do

Composed with Ch. 6's `chartCurvatureContraction2_eq_neg_curvatureTensorAt`, the last
theorem yields `chartCurvature_eq_curvatureTensorAt`
(`PetersenLib/Ch06/CurvatureChartBridge.lean`), identifying `chartCurvature` with Ch. 3's
`curvatureTensorAt` — **on the diagonal only**, i.e. at `y = extChartAt I p p`, the centre
of the chart at `p`. That restriction is inherited from Ch. 3: `curvatureTensor_coordinates`
is diagonal-only by its own docstring, and it is the only coordinate expansion Petersen has.

This diagonal bridge **provably cannot close Jacobi-field existence/uniqueness**, and the
next agent should not spend a session rediscovering that. `Jacobi.IsJacobiFieldOn`'s ODE
evaluates `chartCurvature g α (u t) …` at a **moving** chart point `u t = φ_α(c t)`, in
**one fixed chart** `α` across a whole interval; the diagonal bridge fires only where the
evaluation point is the chart centre, i.e. at a single `t`. Re-centring the chart along the
curve (`α := c t`) does not rescue it: the ODE engine needs one chart on a whole window, not
a family of one-point statements. Closing that gap needs a genuinely new moving-point
coordinate expansion of Ch. 3's curvature (`curvatureTensor_coordinates_movingPoint`), which
Petersen does not have; that is ~1–1.5 sessions of new work, inside an existence/uniqueness
node that is ~3–4 sessions total.

Accordingly **this file closes no blueprint node**. It is infrastructure banked toward a
node that is still several sessions out.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2–1.4.
-/

open Set
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace PetersenLib.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

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
/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the general chart curvature contraction
`chartCurvatureContraction2 g α X Y Z y = ℛ_chart(X, Y)Z` and the chart curvature vector
`chartCurvature g α y Y X Z` are the *same* Riemann curvature in Morgan–Tian's convention,
differing only in the Lean-level presentation of the coefficient (via `chartCurvatureCoef`
vs. `christoffelCurvature`); they agree once the first two slots are swapped:
`chartCurvatureContraction2 g α X Y Z y = chartCurvature g α y Y X Z`, on the chart interior. -/
theorem chartCurvatureContraction2_eq_chartCurvature (g : RiemannianMetric I M) (α : M)
    (X Y Z : E) {y : E} (hy : y ∈ interior (extChartAt I α).target) :
    chartCurvatureContraction2 (I := I) g α X Y Z y = chartCurvature (I := I) g α y Y X Z := by
  classical
  have hY : Y = ∑ a, Geodesic.chartCoord (E := E) a Y • Module.finBasis ℝ E a := by
    simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]
  have hX : X = ∑ b, Geodesic.chartCoord (E := E) b X • Module.finBasis ℝ E b := by
    simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]
  have hZ : Z = ∑ c, Geodesic.chartCoord (E := E) c Z • Module.finBasis ℝ E c := by
    simp [Geodesic.chartCoord_def, Module.Basis.sum_repr]
  rw [chartCurvatureContraction2]
  conv_rhs => rw [hY, hX, hZ]
  rw [chartCurvature_sum₃ (I := I) g α y Finset.univ
      (fun a => Geodesic.chartCoord (E := E) a Y) (fun b => Geodesic.chartCoord (E := E) b X)
      (fun c => Geodesic.chartCoord (E := E) c Z) (fun i => Module.finBasis ℝ E i)]
  simp_rw [chartCurvature_basis (I := I) g α hy]
  -- both sides are `∑ (index) coeff • finBasis (index)`; compare basis coordinates
  refine (Module.finBasis ℝ E).ext_elem fun m => ?_
  simp only [map_sum, map_smul, Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_one,
    Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, mul_ite, mul_zero]
  -- scalar identity: `∑ᵢⱼₖ coef₂(i,j,k,m)·Xⁱ·Yʲ·Zᵏ = ∑ₐᵦᵧ coef(a,b,c,m)·Yᵃ·Xᵇ·Zᶜ`
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold chartCurvatureCoef
  ring

end PetersenLib.Jacobi

end

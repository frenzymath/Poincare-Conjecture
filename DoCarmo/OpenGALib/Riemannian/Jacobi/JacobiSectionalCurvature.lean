import OpenGALib.Riemannian.Jacobi.JacobiVelocityPairing
import OpenGALib.Riemannian.Jacobi.SurfaceCurvatureCommutation
import OpenGALib.Riemannian.Manifold.DoCarmoCh4SectionalPair

/-!
# do Carmo Ch. 5, §2, Corollary 2.9 — the Jacobi coefficient is the sectional curvature

The Taylor expansion of `|J(t)|²` (do Carmo Prop. 2.7, Cor. 2.10) carries the coefficient
`⟨R(v, w)v, w⟩`, read in the fixed chart at `p` as
`chartMetricInner g p (u t₀) (chartCurvatureOp g p u t₀ w) w`.  Corollary 2.9 identifies this
number with the **sectional curvature** `K(p, σ)` of the plane `σ = span{v, w}` when
`|v| = |w| = 1` and `⟨v, w⟩ = 0` (do Carmo's `v` is arc-length, `w` is a unit normal).

## The bridge

The chart curvature operator is the `(γ', ·, γ')` specialization of the chart curvature
contraction, `chartCurvatureOp g p u t w = ℛ_chart(u̇, w)u̇`, which — up to the Morgan–Tian
reindexing of its first two slots — is `chartCurvature g p (u t) w u̇ u̇`
(`chartCurvatureOp_eq_chartCurvature`).  The manifold ↔ chart curvature bridge
`curvatureFormAt_chartFrame` then turns the chart Gram pairing into the pointwise `(0,4)`
curvature form of the frame realizations `F v, F w ∈ T_qM`:

  `chartMetricInner g p (u t₀) (chartCurvatureOp g p u t₀ w) w
      = -curvatureFormAt g q (F w)(F v)(F v)(F w)`   (`chartMetricInner_chartCurvatureOp_eq_neg_curvatureFormAt`).

Antisymmetry in the first pair rewrites this as `curvatureFormAt g q (F v)(F w)(F v)(F w)`; since
the pointwise form is an algebraic curvature form, dividing by `wedgeSq (F v)(F w) = 1` (from
orthonormality) gives the sectional curvature:

  `chartMetricInner g p (u t₀) (chartCurvatureOp g p u t₀ w) w
      = sectionalCurvature (curvatureFormAt g q) (F v)(F w)`   (`chartMetricInner_chartCurvatureOp_eq_sectionalCurvature`).

Blueprint: `cor:dc-ch5-2-9`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Corollary 2.9.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The chart curvature operator as the chart curvature vector -/

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

/-- **Math.** The Jacobi-equation curvature operator as the chart curvature vector:
`chartCurvatureOp g α u t w = chartCurvature g α (u t) w u̇ u̇` (`u̇ = deriv u t`), on the
chart interior.  Combines `chartCurvatureOp_eq_contraction2` with the reindexing
`chartCurvatureContraction2_eq_chartCurvature`. -/
theorem chartCurvatureOp_eq_chartCurvature (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (t : ℝ) (w : E) (hy : u t ∈ interior (extChartAt I α).target) :
    chartCurvatureOp (I := I) g α u t w
      = chartCurvature (I := I) g α (u t) w (deriv u t) (deriv u t) := by
  rw [chartCurvatureOp_eq_contraction2,
    chartCurvatureContraction2_eq_chartCurvature (I := I) g α (deriv u t) w (deriv u t) hy]

/-! ### The chart Gram pairing of frame realizations is the intrinsic inner product -/

/-- **Math.** The intrinsic inner product of the chart-frame realizations
`F a = ∑ᵢ aⁱ · X_i(q)` of two coordinate vectors `a, b : E` at a point `q` in the chart at
`p` is the chart Gram inner product read at `y = φ(q)`:
`⟨F a, F b⟩_g = chartMetricInner g p (φ q) a b`.  Bilinear expansion over the chart frame
`X_i = chartBasisVecFiber p i`, whose Gram matrix is `chartGramOnE` (`metricInner_chartBasisVecFiber`). -/
theorem metricInner_chartFrameRealize (g : RiemannianMetric I M) {p q : M}
    (hq : q ∈ (chartAt H p).source) (a b : E) :
    g.metricInner q
        (∑ i, Geodesic.chartCoord (E := E) i a • chartBasisVecFiber (I := I) p i q)
        (∑ j, Geodesic.chartCoord (E := E) j b • chartBasisVecFiber (I := I) p j q)
      = chartMetricInner (I := I) g p (extChartAt I p q) a b := by
  classical
  rw [metricInner_finsetSum_smul_left, chartMetricInner_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [metricInner_finsetSum_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [metricInner_chartBasisVecFiber (I := I) g hq i j]
  ring

/-! ### The raw bridge: the chart Jacobi coefficient is the pointwise curvature form -/

/-- **Math.** **do Carmo Ch. 5, the analytic content of Cor. 2.9 (raw bridge).**  The Jacobi
coefficient `⟨R(v, w)v, w⟩` read in the fixed chart at `p` is (minus, by the do Carmo ↔
Morgan–Tian convention flip) the pointwise curvature `(0,4)` form of the frame realizations
`F v, F w ∈ T_qM` of the coordinate vectors `v = u̇`, `w`:

  `chartMetricInner g p (u t₀) (chartCurvatureOp g p u t₀ w) w
      = -curvatureFormAt g q (F w)(F v)(F v)(F w)`,

where `q` is the manifold point with `u t₀ = φ(q)` and `F a = ∑ᵢ aⁱ · X_i(q)`.  The chart
operator is `chartCurvature g p (u t₀) w u̇ u̇` (`chartCurvatureOp_eq_chartCurvature`); the
manifold ↔ chart bridge `curvatureFormAt_chartFrame` supplies the sign-flipped form. -/
theorem chartMetricInner_chartCurvatureOp_eq_neg_curvatureFormAt (g : RiemannianMetric I M)
    (p : M) (u : ℝ → E) (t₀ : ℝ) (w : E) {q : M} (hq : q ∈ (chartAt H p).source)
    (hu : u t₀ = extChartAt I p q) :
    chartMetricInner (I := I) g p (u t₀) (chartCurvatureOp (I := I) g p u t₀ w) w
      = - g.leviCivitaConnection.curvatureFormAt g q
          (∑ a, Geodesic.chartCoord (E := E) a w • chartBasisVecFiber (I := I) p a q)
          (∑ b, Geodesic.chartCoord (E := E) b (deriv u t₀) • chartBasisVecFiber (I := I) p b q)
          (∑ c, Geodesic.chartCoord (E := E) c (deriv u t₀) • chartBasisVecFiber (I := I) p c q)
          (∑ d, Geodesic.chartCoord (E := E) d w • chartBasisVecFiber (I := I) p d q) := by
  have hy_int : u t₀ ∈ interior (extChartAt I p).target := by
    rw [hu, (isOpen_extChartAt_target (I := I) p).interior_eq]
    exact (extChartAt I p).map_source (by rwa [extChartAt_source])
  rw [chartCurvatureOp_eq_chartCurvature (I := I) g p u t₀ w hy_int, hu]
  have hbridge := curvatureFormAt_chartFrame (I := I) g hq w (deriv u t₀) (deriv u t₀) w
  linarith [hbridge]

/-! ### Antisymmetry of the pointwise curvature form in the first pair (metric-lowered) -/

/-- **Math.** do Carmo Ch. 4, Prop. 2.5 (b), read pointwise and metric-lowered: the pointwise
curvature `(0,4)` form is antisymmetric in its **first pair**,
`⟨R(x, y)z, t⟩ = -⟨R(y, x)z, t⟩`.  Lifted from the field-level antisymmetry
`curvature_antisymm_left` through `curvatureOperatorAt_eq`, so it needs no `RiemannianBundle`
instance (the inner product is `g.metricInner`, not the fibre `inner`). -/
theorem curvatureFormAt_antisymm_fst (g : RiemannianMetric I M) (p : M)
    (x y z t : TangentSpace I p) :
    g.leviCivitaConnection.curvatureFormAt g p x y z t
      = - g.leviCivitaConnection.curvatureFormAt g p y x z t := by
  have hop : g.leviCivitaConnection.curvatureOperatorAt p x y z
      = -(g.leviCivitaConnection.curvatureOperatorAt p y x z) := by
    rw [g.leviCivitaConnection.curvatureOperatorAt_eq p
        (AffineConnection.extendField_apply p x) (AffineConnection.extendField_apply p y)
        (AffineConnection.extendField_apply p z),
      g.leviCivitaConnection.curvatureOperatorAt_eq p
        (AffineConnection.extendField_apply p y) (AffineConnection.extendField_apply p x)
        (AffineConnection.extendField_apply p z)]
    exact g.leviCivitaConnection.curvature_antisymm_left _ _ _ p
  rw [curvatureFormAt_eq_metricInner, curvatureFormAt_eq_metricInner, hop, g.metricInner_neg_left]

/-! ### The intrinsic curvature-form reading of the Jacobi coefficient -/

/-- **Math.** **do Carmo Ch. 5, the core of Cor. 2.9.**  The Jacobi coefficient
`⟨R(v, w)v, w⟩` read in the fixed chart at `p` is the pointwise **curvature `(0,4)` form**
of the frame realizations `F v, F w ∈ T_qM` of the coordinate vectors `v = u̇`, `w`:

  `chartMetricInner g p (u t₀) (chartCurvatureOp g p u t₀ w) w = ⟨R(F v, F w)F v, F w⟩_g`,

where `q` is the manifold point with `u t₀ = φ(q)` and `F a = ∑ᵢ aⁱ · X_i(q)`.  The raw
bridge gives `-⟨R(F w, F v)F v, F w⟩`; antisymmetry in the first pair
(`curvatureFormAt_antisymm_fst`) removes the sign, matching do Carmo's intrinsic
`⟨R(v, w)v, w⟩`.  This is the substantive content of Cor. 2.9 (the sectional-curvature
identification is then division by `wedgeSq (F v)(F w)`). -/
theorem chartMetricInner_chartCurvatureOp_eq_curvatureFormAt (g : RiemannianMetric I M) (p : M)
    (u : ℝ → E) (t₀ : ℝ) (w : E) {q : M} (hq : q ∈ (chartAt H p).source)
    (hu : u t₀ = extChartAt I p q) :
    chartMetricInner (I := I) g p (u t₀) (chartCurvatureOp (I := I) g p u t₀ w) w
      = g.leviCivitaConnection.curvatureFormAt g q
          (∑ a, Geodesic.chartCoord (E := E) a (deriv u t₀) • chartBasisVecFiber (I := I) p a q)
          (∑ b, Geodesic.chartCoord (E := E) b w • chartBasisVecFiber (I := I) p b q)
          (∑ c, Geodesic.chartCoord (E := E) c (deriv u t₀) • chartBasisVecFiber (I := I) p c q)
          (∑ d, Geodesic.chartCoord (E := E) d w • chartBasisVecFiber (I := I) p d q) := by
  rw [chartMetricInner_chartCurvatureOp_eq_neg_curvatureFormAt (I := I) g p u t₀ w hq hu,
    curvatureFormAt_antisymm_fst (I := I) g q
      (∑ a, Geodesic.chartCoord (E := E) a w • chartBasisVecFiber (I := I) p a q)
      (∑ b, Geodesic.chartCoord (E := E) b (deriv u t₀) • chartBasisVecFiber (I := I) p b q)
      (∑ c, Geodesic.chartCoord (E := E) c (deriv u t₀) • chartBasisVecFiber (I := I) p c q)
      (∑ d, Geodesic.chartCoord (E := E) d w • chartBasisVecFiber (I := I) p d q)]
  ring

/-! ### Corollary 2.9 -/

/-- **Math.** **do Carmo Ch. 5, Corollary 2.9.**  If `γ` is parametrized by arc length
(`|v| = 1`, `v = γ'(0)`) and `w` is a unit vector orthogonal to `v` (`|w| = 1`, `⟨v, w⟩ = 0`),
then the Jacobi coefficient `⟨R(v, w)v, w⟩` read in the fixed chart at `p` is the **sectional
curvature** `K(p, σ)` of the plane `σ = span{v, w}`:

  `chartMetricInner g p (u t₀) (chartCurvatureOp g p u t₀ w) w
      = ⟨R(F v, F w)F v, F w⟩_g / (⟨F v, F v⟩⟨F w, F w⟩ - ⟨F v, F w⟩²)`,

the right side being exactly the intrinsic sectional curvature `sectionalCurvature
(curvatureFormAt g q) (F v)(F w)` written out with the Riemannian inner product `g.metricInner`
(spelled explicitly to avoid the `RiemannianBundle` fibre-`inner` typeclass on `TangentSpace`,
which clashes with the model space's own inner product).  `F v, F w ∈ T_qM` are the frame
realizations of the coordinate vectors `v = u̇`, `w`; `q` is the manifold point with
`u t₀ = φ(q)`.  The orthonormality hypotheses (`|v| = |w| = 1`, `⟨v, w⟩ = 0`), stated in the
chart Gram form, transfer to the intrinsic inner product of the realizations
(`metricInner_chartFrameRealize`) and force the wedge denominator to `1`, so the sectional
curvature equals the curvature-form numerator `⟨R(F v, F w)F v, F w⟩_g`
(`chartMetricInner_chartCurvatureOp_eq_curvatureFormAt`).  Together with Cor. 2.10 this is
do Carmo's `|J(t)| = t - (1/6) K(p, σ) t³ + o(t³)`. -/
theorem chartMetricInner_chartCurvatureOp_eq_sectionalCurvature (g : RiemannianMetric I M) (p : M)
    (u : ℝ → E) (t₀ : ℝ) (w : E) {q : M} (Fv Fw : TangentSpace I q)
    (hq : q ∈ (chartAt H p).source) (hu : u t₀ = extChartAt I p q)
    (hFv : Fv = ∑ a, Geodesic.chartCoord (E := E) a (deriv u t₀) • chartBasisVecFiber (I := I) p a q)
    (hFw : Fw = ∑ b, Geodesic.chartCoord (E := E) b w • chartBasisVecFiber (I := I) p b q)
    (hv1 : chartMetricInner (I := I) g p (u t₀) (deriv u t₀) (deriv u t₀) = 1)
    (hw1 : chartMetricInner (I := I) g p (u t₀) w w = 1)
    (hvw : chartMetricInner (I := I) g p (u t₀) (deriv u t₀) w = 0) :
    chartMetricInner (I := I) g p (u t₀) (chartCurvatureOp (I := I) g p u t₀ w) w
      = g.leviCivitaConnection.curvatureFormAt g q Fv Fw Fv Fw
          / (g.metricInner q Fv Fv * g.metricInner q Fw Fw
              - g.metricInner q Fv Fw * g.metricInner q Fv Fw) := by
  have hnum := chartMetricInner_chartCurvatureOp_eq_curvatureFormAt (I := I) g p u t₀ w hq hu
  rw [← hFv, ← hFw] at hnum
  have hvv : g.metricInner q Fv Fv = 1 := by
    rw [hFv, metricInner_chartFrameRealize (I := I) g hq (deriv u t₀) (deriv u t₀), ← hu, hv1]
  have hww : g.metricInner q Fw Fw = 1 := by
    rw [hFw, metricInner_chartFrameRealize (I := I) g hq w w, ← hu, hw1]
  have hvw' : g.metricInner q Fv Fw = 0 := by
    rw [hFv, hFw, metricInner_chartFrameRealize (I := I) g hq (deriv u t₀) w, ← hu, hvw]
  rw [hnum, hvv, hww, hvw']; norm_num

end Riemannian.Jacobi

end

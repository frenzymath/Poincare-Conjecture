import OpenGALib.Riemannian.Jacobi.JacobiField
import OpenGALib.Riemannian.Jacobi.JacobiNonpositiveCurvature
import OpenGALib.Riemannian.Connection.ChartChristoffelSmooth

/-!
# The coordinate curvature contraction and the intrinsic Jacobi field for the real curvature
(do Carmo Ch. 5, `def:dc-ch5-2-1`)

The Jacobi-field machinery of `OpenGALib/Riemannian/Jacobi/` (`ParallelFrame`,
`FrameReduction`, `JacobiEquationODE`, `JacobiField`) produces the intrinsic Jacobi
field `J = Σᵢ fᵢ eᵢ` along a geodesic for an **abstract** continuous chart-curvature
operator field `R : ℝ → E →L[ℝ] E`.  do Carmo's field is the *specific* curvature
contraction `R(γ', ·)γ'`, whose reading in the fixed chart at `α = γ(0)` is the
coordinate curvature coefficient

  `Rˡ_{ijk}(y) = ∂ⱼΓˡ_{ik} − ∂ᵢΓˡ_{jk} + Σₛ(Γˢ_{ik}Γˡ_{js} − Γˢ_{jk}Γˡ_{is})`

(the same coefficient as `curvatureOperatorAt_chartBasis_expansion`,
`Connection/ChartCurvatureMovingPoint.lean`, so that
`R(∂ᵢ,∂ⱼ)∂ₖ = Σₗ Rˡ_{ijk} ∂ₗ`).  This file:

* defines `chartCurvatureCoef` (the coefficient `Rˡ_{ijk}`) and proves it is `C^∞` on
  the chart interior, using the Christoffel smoothness of
  `Connection/ChartChristoffelSmooth.lean`;
* packages the curvature contraction `w ↦ R(γ', w)γ'` read in the chart as a
  continuous-linear operator field `chartCurvatureOp g α u t : E →L[ℝ] E`, and proves
  it is **continuous in `t`** along a `C¹` curve `u` staying in the chart interior — the
  analytic input `ContinuousOn R` required by `exists_jacobiField_frame`;
* assembles the **intrinsic existence/uniqueness of the Jacobi field for the real
  curvature** (`exists_jacobiField`, `jacobiField_eqOn`), instantiating the abstract `R`
  of `JacobiField.lean` with `chartCurvatureOp` and producing the parallel orthonormal
  frame internally (`exists_parallelOrthoFrame_self`).  This closes the remaining step
  of do Carmo's Jacobi-field definition `def:dc-ch5-2-1` (the "instantiate `R` with the
  real `w ↦ R(γ', w)γ'`" step), and, downstream, feeds `def:dc-ch5-3-1` (conjugate
  points) and `lem:dc-ch7-3-2`.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The coordinate curvature coefficient `Rˡ_{ijk}` -/

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the **coordinate curvature
coefficient** `Rˡ_{ijk}(y)` of the fixed chart at `α`,

  `Rˡ_{ijk} = ∂ⱼΓˡ_{ik} − ∂ᵢΓˡ_{jk} + Σₛ(Γˢ_{ik}Γˡ_{js} − Γˢ_{jk}Γˡ_{is})`,

so that `R(∂ᵢ,∂ⱼ)∂ₖ|_q = Σₗ Rˡ_{ijk}(extChartAt α q) ∂ₗ|_q`
(`curvatureOperatorAt_chartBasis_expansion`). -/
def chartCurvatureCoef (g : RiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y
    - partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l) y
    + ∑ s, (chartChristoffel (I := I) g α i k s y * chartChristoffel (I := I) g α j s l y
          - chartChristoffel (I := I) g α j k s y * chartChristoffel (I := I) g α i s l y)

/-- **Math.** **Smoothness of the coordinate curvature coefficient.** `Rˡ_{ijk}` is
`C^∞` on the interior of the chart target, being a polynomial in the (`C^∞`) Christoffel
symbols and their first partial derivatives. -/
theorem chartCurvatureCoef_contDiffOn (g : RiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartCurvatureCoef (I := I) g α i j k l)
      (interior (extChartAt I α).target) := by
  classical
  have hΓ : ∀ p q r : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α p q r)
        (interior (extChartAt I α).target) := fun p q r =>
    chartChristoffel_contDiffOn_interior g α p q r
  have hpartial : ∀ a p q r : Fin (Module.finrank ℝ E),
      ContDiffOn ℝ ∞ (partialDeriv (E := E) a (chartChristoffel (I := I) g α p q r))
        (interior (extChartAt I α).target) := by
    intro a p q r
    unfold partialDeriv
    have hfderiv : ContDiffOn ℝ ∞ (fderiv ℝ (chartChristoffel (I := I) g α p q r))
        (interior (extChartAt I α).target) :=
      (hΓ p q r).fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
    exact hfderiv.clm_apply contDiffOn_const
  unfold chartCurvatureCoef
  refine ((hpartial j i k l).sub (hpartial i j k l)).add ?_
  refine ContDiffOn.sum (fun s _ => ?_)
  exact ((hΓ i k s).mul (hΓ j s l)).sub ((hΓ j k s).mul (hΓ i s l))

/-! ## The chart curvature contraction as a continuous operator field -/

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1`: the **curvature contraction**
`w ↦ R(γ', w)γ'` read in the fixed chart at `α`, as a continuous-linear operator field
in `t` along the coordinate curve `u` (with velocity `u̇ = deriv u`):

  `(R(t) w)ˡ = Σ_{i,j,k} Rˡ_{ijk}(u t) · u̇ⁱ · wʲ · u̇ᵏ`.

Linear in `w` (the middle slot), continuous in `t`; instantiating the abstract `R` of
`JacobiField.lean`. -/
def chartCurvatureOp (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (t : ℝ) : E →L[ℝ] E :=
  ∑ l, ∑ j,
    (∑ i, ∑ k, chartCurvatureCoef (I := I) g α i j k l (u t)
        * Geodesic.chartCoord (E := E) i (deriv u t)
        * Geodesic.chartCoord (E := E) k (deriv u t)) •
      (Geodesic.chartCoordFunctional (E := E) j).smulRight (Module.finBasis ℝ E l)

/-- **Math.** **Continuity of the chart curvature operator.** Along a curve `u` whose
value stays in the chart interior and whose velocity `deriv u` is continuous, the
curvature contraction `chartCurvatureOp g α u` is continuous in `t`.  This supplies the
`ContinuousOn R` hypothesis of `exists_jacobiField_frame` for the real curvature. -/
theorem continuousOn_chartCurvatureOp (g : RiemannianMetric I M) (α : M) (u : ℝ → E) {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) :
    ContinuousOn (chartCurvatureOp (I := I) g α u) (Icc a b) := by
  refine continuousOn_finset_sum _ fun l _ => continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.smul ?_ continuousOn_const
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun k _ => ?_
  have hcoef : ContinuousOn (fun t => chartCurvatureCoef (I := I) g α i j k l (u t)) (Icc a b) :=
    (chartCurvatureCoef_contDiffOn g α i j k l).continuousOn.comp hu hmem
  have hui : ContinuousOn (fun t => Geodesic.chartCoord (E := E) i (deriv u t)) (Icc a b) := by
    have := (Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hu'
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  have huk : ContinuousOn (fun t => Geodesic.chartCoord (E := E) k (deriv u t)) (Icc a b) := by
    have := (Geodesic.chartCoordFunctional (E := E) k).continuous.comp_continuousOn hu'
    simpa only [Geodesic.chartCoordFunctional_apply] using this
  exact (hcoef.mul hui).mul huk

/-- **Math.** Application of the chart curvature operator: `(R(t) w)` expands over the
chart-model basis `∂ₗ` with the do Carmo coefficients. -/
theorem chartCurvatureOp_apply (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (t : ℝ) (w : E) :
    chartCurvatureOp (I := I) g α u t w
      = ∑ l, (∑ j, (∑ i, ∑ k, chartCurvatureCoef (I := I) g α i j k l (u t)
            * Geodesic.chartCoord (E := E) i (deriv u t)
            * Geodesic.chartCoord (E := E) k (deriv u t))
          * Geodesic.chartCoord (E := E) j w) • Module.finBasis ℝ E l := by
  classical
  simp only [chartCurvatureOp, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Geodesic.chartCoordFunctional_apply, smul_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]

/-! ## Negative semidefiniteness of the Jacobi coefficient under nonpositive curvature -/

/-- **Math.** The chart inner product is additive over a finite sum in the **right**
slot. -/
theorem chartMetricInner_sum_right {ι : Type*} (g : RiemannianMetric I M) (α : M) (y : E)
    (a : E) (s : Finset ι) (b : ι → E) :
    chartMetricInner (I := I) g α y a (∑ k ∈ s, b k)
      = ∑ k ∈ s, chartMetricInner (I := I) g α y a (b k) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx, chartMetricInner_add_right, ih]

/-- **Math.** do Carmo Ch. 5 / Ch. 7, `lem:dc-ch7-3-2`: the **quadratic-form bridge**.
The quadratic form `Σᵢⱼ aᵢⱼ cᵢ cⱼ` of the Jacobi coefficient `aᵢⱼ = ⟨R(eᵢ), eⱼ⟩` is the
intrinsic curvature form of the field `J = Σᵢ cᵢ eᵢ`:

  `Σᵢⱼ aᵢⱼ cᵢ cⱼ = ⟨R(J), J⟩`.

Pure bilinearity of the chart inner product and linearity of `R`. -/
theorem sum_jacobiCoef_quadratic {ι : Type*} [Fintype ι] (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) (R : ℝ → E →L[ℝ] E) (e : ι → ℝ → E) (t : ℝ) (c : ι → ℝ) :
    ∑ i, ∑ j, jacobiCoef (I := I) g α u R e i j t * c i * c j
      = chartMetricInner (I := I) g α (u t)
          (R t (∑ i, c i • e i t)) (∑ j, c j • e j t) := by
  classical
  rw [chartMetricInner_map_frameCombination_left g α (u t) (R t) c (fun i => e i t)
    (∑ j, c j • e j t)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartMetricInner_sum_right g α (u t) (R t (e i t)) Finset.univ (fun j => c j • e j t),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chartMetricInner_smul_right, jacobiCoef]
  ring

/-- **Math.** do Carmo Ch. 7, `lem:dc-ch7-3-2` (the curvature side).  Under **nonpositive
sectional curvature** read in the chart — `⟨R(γ', w)γ', w⟩ ≤ 0` for every `w`
(`chartMetricInner (chartCurvatureOp …) ≤ 0`) — the Jacobi coefficient operator
`A(t) = jacobiCoefOp` is **negative semidefinite** in the Euclidean coefficient inner
product:

  `⟪A(t) c, c⟫ = Σⱼ (A(t) c)ⱼ cⱼ = Σᵢⱼ aᵢⱼ cᵢ cⱼ = ⟨R(J), J⟩ ≤ 0`,   `J = Σᵢ cᵢ eᵢ`.

This is exactly the hypothesis `∀ x, ⟪A(t) x, x⟫ ≤ 0` consumed by the no-conjugate-point
energy argument (`IsJacobiPairOn.ne_zero_of_nonpos_curv`, `JacobiNonpositiveCurvature`). -/
theorem jacobiCoefOp_quadratic_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (e : ι → ℝ → E) (t : ℝ)
    (hK : ∀ w : E, chartMetricInner (I := I) g α (u t)
      (chartCurvatureOp (I := I) g α u t w) w ≤ 0)
    (c : ι → ℝ) :
    ∑ j, jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e t c j * c j ≤ 0 := by
  classical
  have hexpand : ∑ j, jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e t c j * c j
      = ∑ i, ∑ j, jacobiCoef (I := I) g α u (chartCurvatureOp (I := I) g α u) e i j t * c i * c j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jacobiCoefOp_apply, Finset.sum_mul]
  rw [hexpand, sum_jacobiCoef_quadratic]
  exact hK (∑ i, c i • e i t)

/-- **Math.** do Carmo Ch. 7, `lem:dc-ch7-3-2` (**no conjugate points when `K ≤ 0`**).
Let `J = Σᵢ Fᵢ eᵢ` be a Jacobi field in a parallel orthonormal frame along the geodesic
curve `u`, with `J(0) = 0` and nonzero initial velocity (`V(0) ≠ 0`).  If the sectional
curvature is nonpositive — `⟨R(γ', w)γ', w⟩ ≤ 0` for every `w` and `t`
(`chartMetricInner (chartCurvatureOp …) ≤ 0`) — then `J(t) ≠ 0` for every `t ∈ (0, b]`:
no point of `γ` is conjugate to `γ(0)`.

The energy argument of `JacobiNonpositiveCurvature` is applied to the components read as
a Euclidean vector: negative semidefiniteness of the coefficient
(`jacobiCoefOp_quadratic_nonpos`) is exactly its `⟪A t x, x⟫ ≤ 0` hypothesis, and the
orthonormal frame identifies `J(t) = 0` with the vanishing of the components. -/
theorem frameJacobi_ne_zero_of_nonpos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (e : ι → ℝ → E) {b : ℝ}
    {F V : ℝ → ι → ℝ}
    (hFV : IsJacobiPairOn (jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e) 0 b F V)
    (hK : ∀ t : ℝ, ∀ w : E, chartMetricInner (I := I) g α (u t)
      (chartCurvatureOp (I := I) g α u t w) w ≤ 0)
    (horth : ∀ t ∈ Icc (0 : ℝ) b, ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
      = if i = j then (1 : ℝ) else 0)
    (hF0 : F 0 = 0) (hV0 : V 0 ≠ 0) :
    ∀ t ∈ Ioc (0 : ℝ) b, (∑ i, F t i • e i t) ≠ 0 := by
  classical
  set A := jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e with hAdef
  set φ : (ι → ℝ) ≃L[ℝ] EuclideanSpace ℝ ι :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => ℝ)).symm with hφ
  set A' : ℝ → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
    fun t => (φ.toContinuousLinearMap.comp (A t)).comp φ.symm.toContinuousLinearMap with hA'
  set F' : ℝ → EuclideanSpace ℝ ι := fun t => φ (F t) with hF'
  set V' : ℝ → EuclideanSpace ℝ ι := fun t => φ (V t) with hV'
  -- the transferred pair solves the Jacobi ODE over the Euclidean coefficient space
  have hF'V' : IsJacobiPairOn A' 0 b F' V' := by
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · simpa [hF', hV', Function.comp] using
        φ.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (hFV.1 t ht)
    · have h := φ.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t (hFV.2 t ht)
      have hEq : φ (-(A t) (F t)) = -(A' t) (F' t) := by
        simp only [hA', hF', ContinuousLinearMap.comp_apply,
          ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply, map_neg]
      simpa [hV', hEq, Function.comp] using h
  -- negative semidefiniteness of the transferred coefficient
  have hInner : ∀ (a c : ι → ℝ), inner ℝ (φ a) (φ c) = ∑ i, a i * c i := by
    intro a c
    rw [PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hφ, PiLp.coe_symm_continuousLinearEquiv, WithLp.ofLp_toLp]
    simp [inner, mul_comm]
  have hA'nonpos : ∀ t : ℝ, ∀ x : EuclideanSpace ℝ ι, inner ℝ (A' t x) x ≤ 0 := by
    intro t x
    have hx : x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
    have hval : (A' t) x = φ (A t (φ.symm x)) := by
      simp only [hA', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hval]
    conv_lhs => rw [show x = φ (φ.symm x) from hx]
    rw [hInner]
    have := jacobiCoefOp_quadratic_nonpos (I := I) g α u e t (hK t) (φ.symm x)
    simpa [hAdef] using this
  -- apply the abstract no-conjugate-point energy argument
  have hF'0 : F' 0 = 0 := by simp [hF', hF0]
  have hV'0 : V' 0 ≠ 0 := by
    simp only [hV', ne_eq, map_eq_zero_iff _ φ.injective]; exact hV0
  have hne := IsJacobiPairOn.ne_zero_of_nonpos_curv hF'V' hA'nonpos hF'0 hV'0
  intro t ht
  have hFt : F t ≠ 0 := by
    intro hFt0
    exact hne t ht (by simp [hF', hFt0])
  -- orthonormal frame is linearly independent, so `Σ Fᵢ eᵢ = 0 ⟹ F = 0`
  intro hsum
  have hli : LinearIndependent ℝ (fun i => e i t) :=
    linearIndependent_of_chartMetricInner_orthonormal g α (u t) (fun i => e i t)
      (horth t (Ioc_subset_Icc_self ht))
  have hzero := (Fintype.linearIndependent_iff.mp hli) (F t) hsum
  exact hFt (funext hzero)

/-! ## Existence and uniqueness of the intrinsic Jacobi field for the real curvature -/

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1` (**closing the definition**).  Along a
`C¹` coordinate curve `u` of a geodesic `γ` starting at the chart center
(`u a = extChartAt I α α`, `α = γ(0)`) and staying in the chart interior, for **the real
curvature contraction** `R(γ', ·)γ'` read in the chart (`chartCurvatureOp`), every
initial pair `(J₀, w₀)` determines a Jacobi field `J(t) = Σᵢ fᵢ(t) eᵢ(t)` in a parallel
orthonormal frame `e` (produced internally by `exists_parallelOrthoFrame_self`):

* the frame is orthonormal at every `t`;
* `J(a) = J₀`;
* the components have initial (within-interval) velocity `⟨w₀, eᵢ(a)⟩`, so `DJ/dt(a) = w₀`;
* `J` satisfies the **intrinsic Jacobi equation** `D²J/dt² + R(γ', J)γ' = 0` on `(a,b)`.

This is do Carmo's *"given the initial conditions `J(0)`, `DJ/dt(0)`, there exists a
`C^∞` solution defined on `[0,a]`,"* now with `R` instantiated as the genuine curvature
contraction rather than an abstract operator field — the remaining step to close
`def:dc-ch5-2-1`.  Uniqueness is `jacobiField_eqOn`. -/
theorem exists_jacobiField [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : RiemannianMetric I M) (α : M) (u : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hstart : u a = extChartAt I α α)
    (hudiff : ∀ t ∈ Icc a b, DifferentiableAt ℝ u t)
    (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target)
    (hGdiff : ∀ t ∈ Icc a b, ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : ∀ t ∈ Icc a b,
      (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hΓcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Icc a b))
    {K : ℝ≥0}
    (hΓbound : ∀ t ∈ Icc a b,
      ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    (J₀ w₀ : E) :
    ∃ (e : Fin (Module.finrank ℝ E) → ℝ → E) (f : Fin (Module.finrank ℝ E) → ℝ → ℝ),
      (∀ t ∈ Icc a b, ∀ i j, chartMetricInner (I := I) g α (u t) (e i t) (e j t)
        = if i = j then (1 : ℝ) else 0) ∧
      (∑ i, f i a • e i a = J₀) ∧
      (∀ i, HasDerivWithinAt (f i)
        (chartMetricInner (I := I) g α (u a) w₀ (e i a)) (Icc a b) a) ∧
      (∀ t ∈ Ioo a b,
        covariantDerivCoord (I := I) g α u
            (fun r => covariantDerivCoord (I := I) g α u (fun s => ∑ i, f i s • e i s) r) t
          + chartCurvatureOp (I := I) g α u t (∑ i, f i t • e i t) = 0) := by
  have hu : ContinuousOn u (Icc a b) := fun t ht => (hudiff t ht).continuousAt.continuousWithinAt
  obtain ⟨e, heODE, heorth⟩ :=
    exists_parallelOrthoFrame_self g α u hab hstart hudiff hGdiff hbase hΓcont hΓbound
  have hR : ContinuousOn (chartCurvatureOp (I := I) g α u) (Icc a b) :=
    continuousOn_chartCurvatureOp g α u hu hu' hmem
  have hG : ∀ p q, ContinuousOn (fun t => chartGramOnE (I := I) g α p q (u t)) (Icc a b) :=
    fun p q => (chartGramOnE_contDiffOn g α p q).continuousOn.comp hu
      (fun t ht => interior_subset (hmem t ht))
  obtain ⟨f, hJ0, hvel, hjac⟩ :=
    exists_jacobiField_frame g α u (chartCurvatureOp (I := I) g α u) e hab hR hG heODE heorth J₀ w₀
  exact ⟨e, f, heorth, hJ0, hvel, hjac⟩

/-- **Math.** do Carmo Ch. 5, `def:dc-ch5-2-1` (**uniqueness**).  For the real curvature
contraction `chartCurvatureOp`, two Jacobi fields `J = Σᵢ Fᵢ eᵢ` and `J' = Σᵢ Gᵢ eᵢ`
along the same parallel orthonormal frame, whose components solve the scalar Jacobi
system and share initial position and velocity, agree on `[a,b]`: *"a Jacobi field is
determined by its initial conditions `J(0)`, `DJ/dt(0)`."* -/
theorem jacobiField_eqOn (g : RiemannianMetric I M) (α : M) (u : ℝ → E) {a b : ℝ}
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (he : ∀ i, ContinuousOn (e i) (Icc a b))
    {F V G W : ℝ → Fin (Module.finrank ℝ E) → ℝ}
    (hFV : IsJacobiPairOn (jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e) a b F V)
    (hGW : IsJacobiPairOn (jacobiCoefOp (I := I) g α u (chartCurvatureOp (I := I) g α u) e) a b G W)
    (h0 : F a = G a) (h0' : V a = W a) :
    Set.EqOn (fun t => ∑ i, F t i • e i t) (fun t => ∑ i, G t i • e i t) (Icc a b) :=
  jacobiField_frame_eqOn g α u (chartCurvatureOp (I := I) g α u) e
    (continuousOn_chartCurvatureOp g α u hu hu' hmem) he
    (fun p q => (chartGramOnE_contDiffOn g α p q).continuousOn.comp hu
      (fun t ht => interior_subset (hmem t ht)))
    hFV hGW h0 h0'

end Riemannian.Jacobi

end

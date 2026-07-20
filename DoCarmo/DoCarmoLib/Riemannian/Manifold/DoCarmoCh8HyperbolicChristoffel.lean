import DoCarmoLib.Riemannian.Connection.ChartChristoffel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh8HyperbolicManifold

/-!
# Chart Christoffel symbols of the hyperbolic metric (do Carmo Ch. 8 §3)

This file identifies the **abstract chart Christoffel symbols**
`chartChristoffel (hyperbolicMetric e)` — keyed to `Module.finBasis ℝ E` — with a
closed form, the missing bridge for `prop:dc-ch8-3-const-curv` (identified in the
Ground orientation as THE remaining blocker: matching the abstract chart basis to
the coordinate basis).

The half-space `Hⁿ = {xₑ > 0}` is an open subset of `E = EuclideanSpace ℝ (Fin n)`,
so its tangent bundle is canonically trivial (`EuclideanOpens`) and the chart
frame vector is literally the abstract basis vector,
`chartBasisVecFiber α i x = (Module.finBasis ℝ E) i`. Hence the chart Gram matrix
is the constant Gram matrix `Bᵢⱼ = ⟪finBasisᵢ, finBasisⱼ⟫` of the abstract basis,
scaled by the conformal factor `φ(x) = 1/xₑ²`:

* `hyperbolic_chartBasisVecFiber` — `∂ᵢ = finBasisᵢ` on the opens manifold;
* `hyperbolic_chartGramMatrix` — `Gᵢⱼ(x) = (1/xₑ²)·Bᵢⱼ`, the conformal metric in
  the abstract chart frame (do Carmo's `gᵢⱼ = δᵢⱼ/F²`, with `δ` replaced by the
  constant abstract-basis Gram `B` since `finBasis` need not be orthonormal).

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix RealInnerProductSpace

namespace Riemannian.Hyperbolic

open Riemannian Riemannian.Tensor

variable {n : ℕ} [NeZero n]

/-- Abbreviation: `E = EuclideanSpace ℝ (Fin n)`, the ambient space of `Hⁿ`. -/
local notation "E" => EuclideanSpace ℝ (Fin n)

/-- **Eng.** `finrank ℝ (EuclideanSpace ℝ (Fin n)) = n ≠ 0`, the instance needed
by the chart-Gram/Christoffel machinery. -/
instance instNeZeroFinrankEuclidean :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) := by
  rw [finrank_euclideanSpace_fin]; exact ‹NeZero n›

/-- **Math.** The constant Gram matrix `Bᵢⱼ = ⟪finBasisᵢ, finBasisⱼ⟫` of the abstract chart
basis `Module.finBasis ℝ E`. Since `finBasis` is an arbitrary chosen basis (not
the orthonormal coordinate basis), `B` is a general constant symmetric
positive-definite matrix, not `δ`. -/
def finBasisGram (i j : Fin (Module.finrank ℝ E)) : ℝ :=
  @inner ℝ E _ ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)

/-- **Math.** On the opens manifold `Hⁿ ⊆ E`, the chart frame vector is literally
the abstract basis vector: `chartBasisVecFiber α i x = (Module.finBasis ℝ E) i`
(the tangent bundle of an open subset of `E` is canonically trivial). -/
theorem hyperbolic_chartBasisVecFiber (e : Fin n) (α x : ↥(upperHalfSpace e))
    (i : Fin (Module.finrank ℝ E)) :
    chartBasisVecFiber (I := 𝓘(ℝ, E)) α i x = (Module.finBasis ℝ E) i := by
  rw [chartBasisVecFiber]
  exact trivializationAt_symm_opens α x ((Module.finBasis ℝ E) i)

/-- **Math.** do Carmo Ch. 8 §3, eq. (1) in the abstract chart frame: the chart
Gram matrix of the hyperbolic metric is the conformal rescaling of the constant
abstract-basis Gram matrix, `Gᵢⱼ(x) = (1/xₑ²)·Bᵢⱼ`. -/
theorem hyperbolic_chartGramMatrix (e : Fin n) (α x : ↥(upperHalfSpace e))
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α x i j
      = ((x.val e) ^ 2)⁻¹ * finBasisGram (n := n) i j := by
  rw [chartGramMatrix_apply, hyperbolic_chartBasisVecFiber, hyperbolic_chartBasisVecFiber]
  show (hyperbolicMetric e).metricInner x ((Module.finBasis ℝ E) i)
      ((Module.finBasis ℝ E) j) = _
  rw [hyperbolicMetric_apply]
  rfl

/-- **Math.** The constant Gram matrix `Bᵢⱼ = ⟪finBasisᵢ, finBasisⱼ⟫` as a matrix. -/
def finBasisGramMatrix :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of (finBasisGram (n := n))

/-- **Math.** Matrix form of `hyperbolic_chartGramMatrix`: the chart Gram matrix
of the hyperbolic metric is the conformal scalar multiple `Gᵢⱼ = φ·Bᵢⱼ` of the
constant abstract-basis Gram matrix, `φ = 1/xₑ²`. -/
theorem hyperbolic_chartGramMatrix_eq (e : Fin n) (α x : ↥(upperHalfSpace e)) :
    chartGramMatrix (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α x
      = ((x.val e) ^ 2)⁻¹ • finBasisGramMatrix (n := n) := by
  ext i j
  rw [hyperbolic_chartGramMatrix]
  simp only [Matrix.smul_apply, finBasisGramMatrix, Matrix.of_apply, smul_eq_mul]

/-- **Math.** The constant abstract-basis Gram matrix is invertible (positive
definite Gram matrix of a basis): its determinant is a unit. Witnessed by the
positive-definiteness of the chart Gram matrix at the basepoint. -/
theorem finBasisGramMatrix_det_isUnit (e : Fin n) (α : ↥(upperHalfSpace e)) :
    IsUnit (finBasisGramMatrix (n := n)).det := by
  have hxpos : (0 : ℝ) < α.val e := coord_pos e α
  have hφ : ((α.val e) ^ 2)⁻¹ ≠ 0 := by positivity
  have hbase : (α : ↥(upperHalfSpace e))
      ∈ (trivializationAt (EuclideanSpace ℝ (Fin n))
        (TangentSpace 𝓘(ℝ, E)) α).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' α
  have hpos := chartGramMatrix_posDef (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α hbase
  have hdet_pos : 0 < (chartGramMatrix (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α α).det :=
    hpos.det_pos
  rw [hyperbolic_chartGramMatrix_eq, Matrix.det_smul] at hdet_pos
  have hne : (finBasisGramMatrix (n := n)).det ≠ 0 := by
    intro h
    rw [h, mul_zero] at hdet_pos
    exact lt_irrefl _ hdet_pos
  exact isUnit_iff_ne_zero.mpr hne

/-- **Math.** Inverse Gram matrix of the hyperbolic metric in the abstract chart
frame: `Gᵏˡ(x) = xₑ²·Bᵏˡ`, the conformal scalar `1/φ = xₑ²` times the inverse of
the constant abstract-basis Gram matrix. -/
theorem hyperbolic_chartInvGramMatrix (e : Fin n) (α x : ↥(upperHalfSpace e)) :
    chartInvGramMatrix (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α x
      = (x.val e) ^ 2 • (finBasisGramMatrix (n := n))⁻¹ := by
  have hxpos : (0 : ℝ) < x.val e := coord_pos e x
  have hxne : ((x.val e) ^ 2 : ℝ) ≠ 0 := by positivity
  have hunit := finBasisGramMatrix_det_isUnit (n := n) e α
  rw [chartInvGramMatrix]
  apply Matrix.inv_eq_right_inv
  rw [hyperbolic_chartGramMatrix_eq, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_nonsing_inv _ hunit, smul_smul, inv_mul_cancel₀ hxne, one_smul]

/-! ## Partial derivatives of the hyperbolic chart Gram matrix -/

/-- **Math.** On the chart target the chart Gram function is the explicit ambient
formula `Gₗⱼ(y) = (1/yₑ²)·Bₗⱼ` (the chart coordinate `y` is the point itself, the
chart being the inclusion of the open half-space). -/
theorem hyperbolic_chartGramOnE_of_mem_target (e : Fin n) (α : ↥(upperHalfSpace e))
    (l j : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    chartGramOnE (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α l j y
      = ((y e) ^ 2)⁻¹ * finBasisGram (n := n) l j := by
  have hri : (extChartAt 𝓘(ℝ, E) α) ((extChartAt 𝓘(ℝ, E) α).symm y) = y :=
    (extChartAt 𝓘(ℝ, E) α).right_inv hy
  rw [extChartAt_opens_coe] at hri
  rw [chartGramOnE, hyperbolic_chartGramMatrix, hri]

/-! ## The chart Christoffel symbols of the hyperbolic metric (closed form) -/

/-- **Math.** The `i`-th abstract-chart-frame partial derivative of the hyperbolic
chart Gram function `G_{lj}(y) = (yₑ²)⁻¹ B_{lj}` is
`∂ᵢ G_{lj} = B_{lj}·(-2 (yₑ)⁻³ (finBasisᵢ)ₑ)` — the derivative of the conformal
factor `(yₑ²)⁻¹` along `finBasisᵢ`, times the constant Gram entry `B_{lj}`. -/
theorem hyperbolic_partialDeriv_chartGramOnE (e : Fin n) (α : ↥(upperHalfSpace e))
    (l j i : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    partialDeriv i (chartGramOnE (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α l j) y
      = finBasisGram (n := n) l j
          * (-2 * ((y e) ^ 3)⁻¹ * (((Module.finBasis ℝ E) i) e)) := by
  have hval : ((extChartAt 𝓘(ℝ, E) α).symm y).val = y := by
    have h := (extChartAt 𝓘(ℝ, E) α).right_inv hy
    rwa [extChartAt_opens_coe] at h
  have hye : y e ≠ 0 := by
    have hpos := coord_pos e ((extChartAt 𝓘(ℝ, E) α).symm y)
    rw [hval] at hpos
    exact ne_of_gt hpos
  have heq : chartGramOnE (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α l j
      =ᶠ[𝓝 y] fun z => ((z e) ^ 2)⁻¹ * finBasisGram (n := n) l j := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) α).mem_nhds hy] with z hz
    exact hyperbolic_chartGramOnE_of_mem_target (n := n) e α l j hz
  have hproj : HasFDerivAt (fun z : E => z e) (EuclideanSpace.proj (𝕜 := ℝ) e) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt
  have hsq : HasDerivAt (fun t : ℝ => (t ^ 2)⁻¹) (-2 * ((y e) ^ 3)⁻¹) (y e) := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y e) (y e) := by
      simpa using hasDerivAt_pow 2 (y e)
    have h2 := h1.inv (pow_ne_zero 2 hye)
    convert h2 using 1
    field_simp
  have hcf := hsq.comp_hasFDerivAt y hproj
  have hprod : HasFDerivAt (fun z : E => ((z e) ^ 2)⁻¹ * finBasisGram (n := n) l j) _ y :=
    hcf.mul_const (finBasisGram (n := n) l j)
  have hpe : (EuclideanSpace.proj (𝕜 := ℝ) e) ((Module.finBasis ℝ E) i)
      = (((Module.finBasis ℝ E) i) e) := rfl
  rw [partialDeriv, heq.fderiv_eq, hprod.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hpe]

/-- **Math.** do Carmo Ch. 8 §3 (Christoffel symbols of `Hⁿ`). Closed form of the
abstract chart Christoffel symbols of the hyperbolic metric, computed from the
Koszul formula `Γᵏᵢⱼ = ½ Σₗ Gᵏˡ(∂ᵢG_{lj}+∂ⱼG_{li}−∂ₗG_{ij})` with the closed-form
chart Gram `G_{ij}=(yₑ²)⁻¹B_{ij}`, `Gᵏˡ=yₑ²B^{kl}`:

`Γᵏᵢⱼ(y) = -fᵢ δᵏⱼ - fⱼ δᵏᵢ + Dᵏ B_{ij}`,

with `fᵢ = cᵢ/yₑ`, `cᵢ = (finBasisᵢ)ₑ`, `Dᵏ = (Σₗ Bᵏˡ cₗ)/yₑ`, and `B` the
constant abstract-basis Gram matrix. This is do Carmo's displayed
`Γᵏᵢⱼ = -δⱼₖfᵢ - δₖᵢfⱼ + δᵢⱼfₖ` with `δ ⤳ B` (the abstract chart basis is not
orthonormal, so `δ` becomes the general constant Gram `B`), the two Kronecker
terms coming from `Σₗ Bᵏˡ B_{lj} = δᵏⱼ` and the `Bᵢⱼ` term from `Σₗ Bᵏˡ cₗ`. -/
theorem hyperbolic_chartChristoffel (e : Fin n) (α : ↥(upperHalfSpace e))
    (i j k : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    chartChristoffel (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i j k y
      = -((((Module.finBasis ℝ E) i) e) / y e) * (if k = j then (1 : ℝ) else 0)
        - ((((Module.finBasis ℝ E) j) e) / y e) * (if k = i then (1 : ℝ) else 0)
        + ((∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (((Module.finBasis ℝ E) l) e))
              / y e)
            * finBasisGram (n := n) i j := by
  classical
  have hval : ((extChartAt 𝓘(ℝ, E) α).symm y).val = y := by
    have h := (extChartAt 𝓘(ℝ, E) α).right_inv hy
    rwa [extChartAt_opens_coe] at h
  have hye : y e ≠ 0 := by
    have hpos := coord_pos e ((extChartAt 𝓘(ℝ, E) α).symm y)
    rw [hval] at hpos
    exact ne_of_gt hpos
  have hunit := finBasisGramMatrix_det_isUnit (n := n) e α
  -- inverse Gram in coordinates: `Gᵏˡ(y) = yₑ² Bᵏˡ`
  have hInv : ∀ k' l' : Fin (Module.finrank ℝ E),
      chartInvGramMatrix (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α
          ((extChartAt 𝓘(ℝ, E) α).symm y) k' l'
        = (y e) ^ 2 * (finBasisGramMatrix (n := n))⁻¹ k' l' := by
    intro k' l'
    rw [hyperbolic_chartInvGramMatrix (n := n) e α ((extChartAt 𝓘(ℝ, E) α).symm y)]
    simp only [Matrix.smul_apply, smul_eq_mul, hval]
  -- inverse-Gram/Gram contraction: `Σₗ Bᵏˡ B_{la} = δᵏₐ`
  have hcontract : ∀ a : Fin (Module.finrank ℝ E),
      ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * finBasisGram (n := n) l a
        = (if k = a then (1 : ℝ) else 0) := by
    intro a
    have hmul : ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * finBasisGram (n := n) l a
        = ((finBasisGramMatrix (n := n))⁻¹ * finBasisGramMatrix (n := n)) k a := by
      rw [Matrix.mul_apply]
      rfl
    rw [hmul, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
  -- each Koszul summand in factored form
  have key : ∀ l : Fin (Module.finrank ℝ E),
      (1 / 2 : ℝ) * (chartInvGramMatrix (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α
          ((extChartAt 𝓘(ℝ, E) α).symm y) k l
        * (partialDeriv i
              (chartGramOnE (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α l j) y
          + partialDeriv j
              (chartGramOnE (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α l i) y
          - partialDeriv l
              (chartGramOnE (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i j) y))
      = -(y e)⁻¹ * ((finBasisGramMatrix (n := n))⁻¹ k l *
          (finBasisGram (n := n) l j * (((Module.finBasis ℝ E) i) e)
            + finBasisGram (n := n) l i * (((Module.finBasis ℝ E) j) e)
            - finBasisGram (n := n) i j * (((Module.finBasis ℝ E) l) e))) := by
    intro l
    rw [hInv k l,
      hyperbolic_partialDeriv_chartGramOnE (n := n) e α l j i hy,
      hyperbolic_partialDeriv_chartGramOnE (n := n) e α l i j hy,
      hyperbolic_partialDeriv_chartGramOnE (n := n) e α i j l hy]
    field_simp
    ring
  rw [chartChristoffel_def, Finset.mul_sum, Finset.sum_congr rfl (fun l _ => key l),
    ← Finset.mul_sum]
  -- factor helper: pull a constant out of an inverse-Gram/Gram contraction
  have factor : ∀ (a : Fin (Module.finrank ℝ E)) (cc : ℝ),
      ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (finBasisGram (n := n) l a * cc)
        = cc * (if k = a then (1 : ℝ) else 0) := by
    intro a cc
    rw [← hcontract a, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have factor3 : ∑ l, (finBasisGramMatrix (n := n))⁻¹ k l *
        (finBasisGram (n := n) i j * (((Module.finBasis ℝ E) l) e))
      = finBasisGram (n := n) i j
          * (∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (((Module.finBasis ℝ E) l) e)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [show (∑ l, (finBasisGramMatrix (n := n))⁻¹ k l *
          (finBasisGram (n := n) l j * (((Module.finBasis ℝ E) i) e)
            + finBasisGram (n := n) l i * (((Module.finBasis ℝ E) j) e)
            - finBasisGram (n := n) i j * (((Module.finBasis ℝ E) l) e)))
        = (((Module.finBasis ℝ E) i) e) * (if k = j then (1 : ℝ) else 0)
          + (((Module.finBasis ℝ E) j) e) * (if k = i then (1 : ℝ) else 0)
          - finBasisGram (n := n) i j
              * (∑ l, (finBasisGramMatrix (n := n))⁻¹ k l * (((Module.finBasis ℝ E) l) e))
        from by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [factor j (((Module.finBasis ℝ E) i) e), factor i (((Module.finBasis ℝ E) j) e),
        factor3]]
  field_simp
  ring

/-- **Math.** do Carmo Ch. 8 §3 (derivative of the Christoffel symbols of `Hⁿ`).
Since the closed-form chart Christoffel symbol factors as
`Γˡᵢₖ(y) = Kˡᵢₖ · (yₑ)⁻¹` with `Kˡᵢₖ = -cᵢ δˡₖ - cₖ δˡᵢ + (∑ₛ Bˡˢcₛ) B_{ik}` a
constant (`cᵢ = (finBasisᵢ)ₑ`), its `m`-th abstract-chart-frame partial derivative
is `∂ₘΓˡᵢₖ = Kˡᵢₖ · (-cₘ (yₑ)⁻²)` — differentiating only the `(yₑ)⁻¹` factor.
This is the `∂Γ` input to the chart-frame curvature expansion
`lem:dc-ch8-3-chart-curvature`. -/
theorem hyperbolic_partialDeriv_chartChristoffel (e : Fin n) (α : ↥(upperHalfSpace e))
    (i k l m : Fin (Module.finrank ℝ E)) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℝ, E) α).target) :
    partialDeriv m (chartChristoffel (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i k l) y
      = (-(((Module.finBasis ℝ E) i) e) * (if l = k then (1 : ℝ) else 0)
          - (((Module.finBasis ℝ E) k) e) * (if l = i then (1 : ℝ) else 0)
          + (∑ s, (finBasisGramMatrix (n := n))⁻¹ l s * (((Module.finBasis ℝ E) s) e))
              * finBasisGram (n := n) i k)
        * (-(((Module.finBasis ℝ E) m) e) * ((y e) ^ 2)⁻¹) := by
  have hval : ((extChartAt 𝓘(ℝ, E) α).symm y).val = y := by
    have h := (extChartAt 𝓘(ℝ, E) α).right_inv hy
    rwa [extChartAt_opens_coe] at h
  have hye : y e ≠ 0 := by
    have hpos := coord_pos e ((extChartAt 𝓘(ℝ, E) α).symm y)
    rw [hval] at hpos
    exact ne_of_gt hpos
  set K : ℝ := -(((Module.finBasis ℝ E) i) e) * (if l = k then (1 : ℝ) else 0)
      - (((Module.finBasis ℝ E) k) e) * (if l = i then (1 : ℝ) else 0)
      + (∑ s, (finBasisGramMatrix (n := n))⁻¹ l s * (((Module.finBasis ℝ E) s) e))
          * finBasisGram (n := n) i k with hKdef
  have heqK : chartChristoffel (I := 𝓘(ℝ, E)) (hyperbolicMetric e) α i k l
      =ᶠ[𝓝 y] fun z => K * (z e)⁻¹ := by
    filter_upwards [(isOpen_extChartAt_target (I := 𝓘(ℝ, E)) α).mem_nhds hy] with z hz
    rw [hyperbolic_chartChristoffel (n := n) e α i k l hz, hKdef]
    ring
  have hproj : HasFDerivAt (fun z : E => z e) (EuclideanSpace.proj (𝕜 := ℝ) e) y :=
    (EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt
  have hgD : HasDerivAt (fun t : ℝ => K * t⁻¹) (K * (-((y e) ^ 2)⁻¹)) (y e) :=
    (hasDerivAt_inv hye).const_mul K
  have hcf := hgD.comp_hasFDerivAt y hproj
  have hpe : (EuclideanSpace.proj (𝕜 := ℝ) e) ((Module.finBasis ℝ E) m)
      = (((Module.finBasis ℝ E) m) e) := rfl
  have hfun : (fun z : E => K * (z e)⁻¹)
      = (fun t : ℝ => K * t⁻¹) ∘ (fun z : E => z e) := rfl
  rw [partialDeriv, heqK.fderiv_eq, hfun, hcf.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hpe]
  ring

/-- **Math.** The inverse-Gram/coordinate identity `∑ᵢⱼ Bⁱʲ cᵢ cⱼ = 1`, where
`cᵢ = (finBasisᵢ)ₑ` is the `e`-th coordinate of the `i`-th abstract basis vector
and `Bⁱʲ = (B⁻¹)ᵢⱼ` is the inverse of the constant abstract-basis Gram matrix.
Geometrically, `cᵢ = ⟪finBasisᵢ, wₑ⟫` for the standard unit vector
`wₑ = EuclideanSpace.single e 1`, and the contraction reconstructs
`⟪wₑ, wₑ⟫ = 1`. This is the single nontrivial input `|dσ|²_{g₀}=1` of the §3
conformal curvature cancellation `T = ½φg₀` behind `prop:dc-ch8-3-const-curv`. -/
theorem finBasis_inv_gram_coord (e : Fin n)
    (hunit : IsUnit (finBasisGramMatrix (n := n)).det) :
    ∑ i, ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j
        * (((Module.finBasis ℝ E) i) e) * (((Module.finBasis ℝ E) j) e) = 1 := by
  classical
  set b := Module.finBasis ℝ E with hb
  set w : E := EuclideanSpace.single e (1 : ℝ) with hw
  have hcoord : ∀ x : E, @inner ℝ E _ x w = x e := by
    intro x
    have h1 : @inner ℝ E _ x w = (1 : ℝ) * (starRingEnd ℝ) (x e) := by
      rw [hw]; exact EuclideanSpace.inner_single_right e 1 x
    rw [h1]; simp
  have hrepr : ∑ i, (b.repr w i) • b i = w := b.sum_repr w
  have hgram : ∀ i j, finBasisGram (n := n) i j = @inner ℝ E _ (b i) (b j) := by
    intro i j; rw [finBasisGram, hb]
  -- coordinate of `b i` as a Gram-weighted sum of the repr coords of `w`
  have hcB : ∀ i, (b i) e = ∑ j, finBasisGram (n := n) i j * (b.repr w j) := by
    intro i
    rw [← hcoord (b i)]
    conv_lhs => rw [← hrepr]
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [real_inner_smul_right, hgram i j]; ring
  -- inverse-Gram/Gram contraction `∑ⱼ Bⁱʲ B_{jk} = δᵢₖ`
  have hBinvB : ∀ i k, ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * finBasisGram (n := n) j k
      = (if i = k then (1 : ℝ) else 0) := by
    intro i k
    have hmul : ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * finBasisGram (n := n) j k
        = ((finBasisGramMatrix (n := n))⁻¹ * finBasisGramMatrix (n := n)) i k := by
      rw [Matrix.mul_apply]; rfl
    rw [hmul, Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply]
  -- `B⁻¹` applied to the coordinate vector recovers the repr coords
  have hinvca : ∀ i, ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * ((b j) e) = b.repr w i := by
    intro i
    calc ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * ((b j) e)
        = ∑ j, ∑ k, (finBasisGramMatrix (n := n))⁻¹ i j
              * finBasisGram (n := n) j k * (b.repr w k) := by
          apply Finset.sum_congr rfl; intro j _
          rw [hcB j, Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
      _ = ∑ k, ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j
              * finBasisGram (n := n) j k * (b.repr w k) := Finset.sum_comm
      _ = ∑ k, (∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * finBasisGram (n := n) j k)
              * (b.repr w k) := by
          apply Finset.sum_congr rfl; intro k _; rw [← Finset.sum_mul]
      _ = ∑ k, (if i = k then (1 : ℝ) else 0) * (b.repr w k) := by
          apply Finset.sum_congr rfl; intro k _; rw [hBinvB i k]
      _ = b.repr w i := by simp [Finset.sum_ite_eq]
  -- `⟪w,w⟫ = ∑ᵢ (repr wᵢ)·(b i)ₑ` and `⟪w,w⟫ = 1`
  have hww_sum : @inner ℝ E _ w w = ∑ i, (b.repr w i) * ((b i) e) := by
    nth_rewrite 1 [← hrepr]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_smul_left, hcoord (b i)]
  have hww1 : @inner ℝ E _ w w = 1 := by
    have h1 : @inner ℝ E _ w w
        = (1 : ℝ) * (starRingEnd ℝ) ((EuclideanSpace.single e (1 : ℝ)) e) := by
      rw [hw]; exact EuclideanSpace.inner_single_right e 1 (EuclideanSpace.single e 1)
    rw [h1]; simp
  calc ∑ i, ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * ((b i) e) * ((b j) e)
      = ∑ i, ((b i) e) * ∑ j, (finBasisGramMatrix (n := n))⁻¹ i j * ((b j) e) := by
        apply Finset.sum_congr rfl; intro i _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ i, ((b i) e) * (b.repr w i) := by
        apply Finset.sum_congr rfl; intro i _; rw [hinvca i]
    _ = ∑ i, (b.repr w i) * ((b i) e) := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ = @inner ℝ E _ w w := hww_sum.symm
    _ = 1 := hww1

end Riemannian.Hyperbolic

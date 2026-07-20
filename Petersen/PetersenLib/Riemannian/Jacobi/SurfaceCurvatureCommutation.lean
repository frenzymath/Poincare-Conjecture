/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Jacobi/SurfaceCurvatureCommutation.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Jacobi.ChartCurvatureCoef
import PetersenLib.Riemannian.Geodesic.CovariantDerivative
import PetersenLib.Riemannian.Geodesic.SymmetryLemma
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Curvature on a parametrized surface (do Carmo Ch. 4, `lem:dc-ch4-4-1`)

do Carmo's Lemma 4.1 of Chapter 4 states that for a parametrized surface
`f : A ⊆ ℝ² → M` and a vector field `V = V(s,t)` along `f`,
$$
\frac{D}{\partial t}\frac{D}{\partial s}V - \frac{D}{\partial s}\frac{D}{\partial t}V
  = R\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)V .
$$
This is the identity that turns the geodesic condition `D/∂t ∂f/∂t = 0` into the
Jacobi equation (do Carmo Ch. 5, `def:dc-ch5-2-1`), and is the sole greenfield
blocker on the exponential↔Jacobi bridge `cor:dc-ch5-2-5` feeding the Hadamard
theorem `thm:dc-ch7-3-1`.

We formalize it entirely **in a fixed chart at `α`**, reusing the coordinate
covariant derivative `covariantDerivCoord` along a curve and the coordinate
curvature coefficient `chartCurvatureCoef` (`Rˡ_{ijk}`).  A parametrized surface is
a `C²` map `f : ℝ × ℝ → E` (the chart reading `φ_α ∘ f`), a field is a `C²` map
`V : ℝ × ℝ → E`; the two covariant derivatives are the two coordinate covariant
derivatives applied to the slice curves.

## Main results (this file)

* `chartCurvatureContraction2` — the general coordinate curvature contraction
  `R(X, Y)Z = Σ_l (Σ_{ijk} Rˡ_{ijk}(y) Xⁱ Yʲ Zᵏ) ∂_l`, the right-hand side of the
  commutation identity; linear in each slot, antisymmetric in `(X, Y)`.
* `surface_covariant_commutator` — do Carmo Ch. 4 Lemma 4.1 = Petersen Lemma 6.1.2:
  `D/∂t D/∂s V − D/∂s D/∂t V = R(∂f/∂s, ∂f/∂t)V`.
-/

open Set
open scoped Manifold Topology ContDiff NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The general coordinate curvature contraction `R(X, Y)Z` -/

/-- **Math.** do Carmo Ch. 4, `lem:dc-ch4-4-1` (right-hand side).  The **coordinate
curvature contraction** `R(X, Y)Z` of three vectors `X, Y, Z : E` read in the fixed
chart at `α` and based at `y`:
$$
\big(R(X, Y)Z\big)^l = \sum_{i,j,k} R^l{}_{ijk}(y)\, X^i\, Y^j\, Z^k ,
$$
with `Rˡ_{ijk} = chartCurvatureCoef` the coordinate curvature coefficient
(`R(∂_i, ∂_j)∂_k = Σ_l Rˡ_{ijk} ∂_l`).  Multilinear in `(X, Y, Z)`; antisymmetric in
`(X, Y)`.  The Jacobi-equation operator `w ↦ R(γ', w)γ'` is the specialization
`X = Z = γ'`, `Y = w`. -/
def chartCurvatureContraction2 (g : RiemannianMetric I M) (α : M) (X Y Z : E) (y : E) : E :=
  ∑ l, (∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α i j k l y
      * Geodesic.chartCoord (E := E) i X
      * Geodesic.chartCoord (E := E) j Y
      * Geodesic.chartCoord (E := E) k Z) • Module.finBasis ℝ E l

/-! ### Antisymmetry of the curvature coefficient in `(i, j)` -/

/-- **Math.** The coordinate curvature coefficient is **antisymmetric** in its first
two indices, `Rˡ_{ijk} = − Rˡ_{jik}`, directly from its definition
(`∂_jΓ_{ik} − ∂_iΓ_{jk}` flips sign and the quadratic term flips sign). -/
theorem chartCurvatureCoef_antisymm (g : RiemannianMetric I M) (α : M)
    (i j k l : Fin (Module.finrank ℝ E)) (y : E) :
    chartCurvatureCoef (I := I) g α i j k l y
      = - chartCurvatureCoef (I := I) g α j i k l y := by
  classical
  have hsum : ∑ s, (chartChristoffel (I := I) g α j k s y * chartChristoffel (I := I) g α i s l y
        - chartChristoffel (I := I) g α i k s y * chartChristoffel (I := I) g α j s l y)
      = - ∑ s, (chartChristoffel (I := I) g α i k s y * chartChristoffel (I := I) g α j s l y
        - chartChristoffel (I := I) g α j k s y * chartChristoffel (I := I) g α i s l y) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]; ring
  simp only [chartCurvatureCoef]
  rw [hsum]; ring

/-! ### Multilinearity of the curvature contraction -/

@[simp] theorem chartCurvatureContraction2_zero_left (g : RiemannianMetric I M) (α : M)
    (Y Z y : E) : chartCurvatureContraction2 (I := I) g α 0 Y Z y = 0 := by
  simp only [chartCurvatureContraction2, Geodesic.chartCoord_zero]
  refine Finset.sum_eq_zero fun l _ => ?_
  have : (∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α i j k l y * (0 : ℝ)
      * Geodesic.chartCoord (E := E) j Y * Geodesic.chartCoord (E := E) k Z) = 0 := by
    simp
  rw [this, zero_smul]

/-- **Math.** `R(X, Y)Z` is **additive** in its third slot `Z`. -/
theorem chartCurvatureContraction2_add_right (g : RiemannianMetric I M) (α : M)
    (X Y Z Z' y : E) :
    chartCurvatureContraction2 (I := I) g α X Y (Z + Z') y
      = chartCurvatureContraction2 (I := I) g α X Y Z y
        + chartCurvatureContraction2 (I := I) g α X Y Z' y := by
  classical
  simp only [chartCurvatureContraction2, Geodesic.chartCoord_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← add_smul]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Math.** `R(X, Y)Z` is **homogeneous** in its third slot `Z`. -/
theorem chartCurvatureContraction2_smul_right (g : RiemannianMetric I M) (α : M)
    (a : ℝ) (X Y Z y : E) :
    chartCurvatureContraction2 (I := I) g α X Y (a • Z) y
      = a • chartCurvatureContraction2 (I := I) g α X Y Z y := by
  classical
  simp only [chartCurvatureContraction2, Geodesic.chartCoord_smul]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Math.** do Carmo Ch. 4, `lem:dc-ch4-4-1`.  The curvature contraction is
**antisymmetric in its first two vector slots**: `R(X, Y)Z = − R(Y, X)Z`, from the
antisymmetry `Rˡ_{ijk} = − Rˡ_{jik}` of the coordinate coefficient
(`chartCurvatureCoef_antisymm`).  In particular `R(X, X)Z = 0`. -/
theorem chartCurvatureContraction2_antisymm_left (g : RiemannianMetric I M) (α : M)
    (X Y Z y : E) :
    chartCurvatureContraction2 (I := I) g α X Y Z y
      = - chartCurvatureContraction2 (I := I) g α Y X Z y := by
  classical
  refine eq_neg_of_add_eq_zero_left ?_
  simp only [chartCurvatureContraction2]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [← add_smul]
  -- reindex the `Y X` sum (swap `i, j`), then cancel by the coefficient antisymmetry
  have hswap :
      (∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α i j k l y
          * Geodesic.chartCoord (E := E) i Y
          * Geodesic.chartCoord (E := E) j X
          * Geodesic.chartCoord (E := E) k Z)
        = ∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α j i k l y
          * Geodesic.chartCoord (E := E) i X
          * Geodesic.chartCoord (E := E) j Y
          * Geodesic.chartCoord (E := E) k Z := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => by ring
  have hzero :
      (∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α i j k l y
          * Geodesic.chartCoord (E := E) i X
          * Geodesic.chartCoord (E := E) j Y
          * Geodesic.chartCoord (E := E) k Z)
        + (∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α i j k l y
          * Geodesic.chartCoord (E := E) i Y
          * Geodesic.chartCoord (E := E) j X
          * Geodesic.chartCoord (E := E) k Z) = 0 := by
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [chartCurvatureCoef_antisymm (I := I) g α i j k l y]
    ring
  rw [hzero, zero_smul]

/-- **Math.** The directional derivative of a chart function expands over the chart
basis: `Df(y)(δ) = Σ_m (∂_m f)(y) · δ^m`, relating the base-directional derivative
`fderiv` to the coordinate partial derivatives `partialDeriv`.  This turns
`baseDerivChristoffelContraction` into the coordinate curvature coefficients. -/
theorem fderiv_eq_sum_partialDeriv (f : E → ℝ) (y δ : E) :
    fderiv ℝ f y δ
      = ∑ m, partialDeriv (E := E) m f y * Geodesic.chartCoord (E := E) m δ := by
  classical
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr δ]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul]
  simp only [partialDeriv, Geodesic.chartCoord_def, smul_eq_mul]
  ring

/-! ## The base-derivative of the Christoffel contraction along a curve

The analytic heart of the surface curvature-commutation lemma: the derivative of
`τ ↦ Γ(a τ, b τ)(c τ)` splits, by the chain and product rules, into the derivative
in each vector slot plus the **base-directional derivative** of the Christoffel
symbols along the moving base point `c`. -/

/-- **Math.** The **base-directional derivative** of the Christoffel contraction: the
directional derivative of `y ↦ Γ(a, b)(y)` at `y` in the direction `δ`,
$$
\text{baseDerivΓ}(a, b, δ)(y)
  = \sum_k \Big(\sum_{i,j} \big(D\Gamma^k{}_{ij}\big)(y)(δ)\, a^i\, b^j\Big) \partial_k,
$$
holding the vector slots `a, b` fixed and differentiating only the Christoffel
symbols with respect to the base point. -/
def baseDerivChristoffelContraction (g : RiemannianMetric I M) (α : M) (a b δ y : E) : E :=
  ∑ k, (∑ i, ∑ j, fderiv ℝ (chartChristoffel (I := I) g α i j k) y δ
      * Geodesic.chartCoord (E := E) i a
      * Geodesic.chartCoord (E := E) j b) • Module.finBasis ℝ E k

/-- **Math.** do Carmo Ch. 4, `lem:dc-ch4-4-1` (analytic core).  The **derivative of
the Christoffel contraction along a curve**.  For curves `a, b, c : ℝ → E`
differentiable at `t`, with `c t` in the chart interior (so the Christoffel symbols
are differentiable there), the composite `τ ↦ Γ(a τ, b τ)(c τ)` is differentiable and
$$
\frac{d}{dτ}\,\Gamma(a, b)(c)
  = \Gamma(a', b)(c) + \Gamma(a, b')(c) + \text{baseDerivΓ}(a, b, c')(c) ,
$$
the sum of the two vector-slot derivatives and the base-directional derivative.
This is the reusable Leibniz/chain rule for covariant differentiation of a field
along a parametrized surface. -/
theorem hasDerivAt_chartChristoffelContraction_along [I.Boundaryless]
    (g : RiemannianMetric I M) (α : M) (a b c : ℝ → E) (a' b' c' : E) {t : ℝ}
    (ha : HasDerivAt a a' t) (hb : HasDerivAt b b' t) (hc : HasDerivAt c c' t)
    (hcmem : c t ∈ interior (extChartAt I α).target) :
    HasDerivAt (fun τ => Geodesic.chartChristoffelContraction (I := I) g α (a τ) (b τ) (c τ))
      (Geodesic.chartChristoffelContraction (I := I) g α a' (b t) (c t)
        + Geodesic.chartChristoffelContraction (I := I) g α (a t) b' (c t)
        + baseDerivChristoffelContraction (I := I) g α (a t) (b t) c' (c t)) t := by
  classical
  -- differentiability of the Christoffel symbols at the (interior) base point `c t`
  have hΓdiff : ∀ i j k, DifferentiableAt ℝ (chartChristoffel (I := I) g α i j k) (c t) :=
    fun i j k => ((chartChristoffel_contDiffOn_interior g α i j k).differentiableOn
      (by norm_num)).differentiableAt (isOpen_interior.mem_nhds hcmem)
  -- chain rule for the Christoffel symbols along `c`
  have h1 : ∀ i j k, HasDerivAt (fun τ => chartChristoffel (I := I) g α i j k (c τ))
      (fderiv ℝ (chartChristoffel (I := I) g α i j k) (c t) c') t :=
    fun i j k => (hΓdiff i j k).hasFDerivAt.comp_hasDerivAt t hc
  -- linear-functional derivatives of the vector slots
  have h2 : ∀ i, HasDerivAt (fun τ => Geodesic.chartCoord (E := E) i (a τ))
      (Geodesic.chartCoord (E := E) i a') t := fun i => by
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) i).hasFDerivAt.comp_hasDerivAt t ha
  have h3 : ∀ j, HasDerivAt (fun τ => Geodesic.chartCoord (E := E) j (b τ))
      (Geodesic.chartCoord (E := E) j b') t := fun j => by
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) j).hasFDerivAt.comp_hasDerivAt t hb
  -- rewrite the contraction as its coordinate sum
  have hrw : (fun τ => Geodesic.chartChristoffelContraction (I := I) g α (a τ) (b τ) (c τ))
      = fun τ => ∑ k, (∑ i, ∑ j, chartChristoffel (I := I) g α i j k (c τ)
          * Geodesic.chartCoord (E := E) i (a τ)
          * Geodesic.chartCoord (E := E) j (b τ)) • Module.finBasis ℝ E k := by
    funext τ; rw [Geodesic.chartChristoffelContraction_def]
  rw [hrw]
  -- identify the clean three-term derivative with the raw product-rule sum
  have hval : Geodesic.chartChristoffelContraction (I := I) g α a' (b t) (c t)
        + Geodesic.chartChristoffelContraction (I := I) g α (a t) b' (c t)
        + baseDerivChristoffelContraction (I := I) g α (a t) (b t) c' (c t)
      = ∑ k, (∑ i, ∑ j, ((fderiv ℝ (chartChristoffel (I := I) g α i j k) (c t) c'
              * Geodesic.chartCoord (E := E) i (a t)
              + chartChristoffel (I := I) g α i j k (c t) * Geodesic.chartCoord (E := E) i a')
            * Geodesic.chartCoord (E := E) j (b t)
          + chartChristoffel (I := I) g α i j k (c t) * Geodesic.chartCoord (E := E) i (a t)
              * Geodesic.chartCoord (E := E) j b')) • Module.finBasis ℝ E k := by
    simp only [Geodesic.chartChristoffelContraction_def, baseDerivChristoffelContraction]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul, ← add_smul]
    congr 1
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hval]
  apply HasDerivAt.fun_sum
  intro k _
  have hSk : HasDerivAt
      (fun τ => ∑ i, ∑ j, chartChristoffel (I := I) g α i j k (c τ)
          * Geodesic.chartCoord (E := E) i (a τ) * Geodesic.chartCoord (E := E) j (b τ))
      (∑ i, ∑ j, ((fderiv ℝ (chartChristoffel (I := I) g α i j k) (c t) c'
              * Geodesic.chartCoord (E := E) i (a t)
              + chartChristoffel (I := I) g α i j k (c t) * Geodesic.chartCoord (E := E) i a')
            * Geodesic.chartCoord (E := E) j (b t)
          + chartChristoffel (I := I) g α i j k (c t) * Geodesic.chartCoord (E := E) i (a t)
              * Geodesic.chartCoord (E := E) j b')) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    exact ((h1 i j k).mul (h2 i)).mul (h3 j)
  exact hSk.smul_const (Module.finBasis ℝ E k)

/-! ## The collection lemma: curvature emerges from the commutator

Pure index algebra (no analysis).  The four terms produced by differentiating the
covariant derivatives along the surface — the two base-directional derivatives of the
Christoffel symbols and the two nested Christoffel contractions — collect exactly into
the coordinate curvature contraction `R(X, Y)V`. -/

/-- **Math.** **Reindexing of a base-derivative term.**  For fixed output index `l`,
the base-directional derivative coefficient `∑ᵢⱼ (D_δΓˡ_{ij}) aⁱ bʲ` expands via
`fderiv_eq_sum_partialDeriv` into a triple coordinate sum. -/
theorem baseDeriv_coef_expand (g : RiemannianMetric I M) (α : M)
    (a b δ : E) (l : Fin (Module.finrank ℝ E)) (y : E) :
    (∑ i, ∑ j, fderiv ℝ (chartChristoffel (I := I) g α i j l) y δ
        * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b)
      = ∑ i, ∑ j, ∑ m, partialDeriv (E := E) m (chartChristoffel (I := I) g α i j l) y
          * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b
          * Geodesic.chartCoord (E := E) m δ := by
  classical
  simp only [fderiv_eq_sum_partialDeriv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Math.** The chart coordinate of a basis expansion recovers the coefficient:
`(∑ₖ fₖ eₖ)ʲ = fⱼ`. -/
theorem chartCoord_sum_smul_finBasis (f : Fin (Module.finrank ℝ E) → ℝ)
    (j : Fin (Module.finrank ℝ E)) :
    Geodesic.chartCoord (E := E) j (∑ k, f k • Module.finBasis ℝ E k) = f j := by
  classical
  rw [← Geodesic.chartCoordFunctional_apply, map_sum]
  have hb : ∀ k, Geodesic.chartCoordFunctional (E := E) j (Module.finBasis ℝ E k)
      = (if k = j then (1 : ℝ) else 0) := by
    intro k
    rw [Geodesic.chartCoordFunctional_apply, Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  simp only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ j]
  simp only [Finset.mem_univ, if_true]

/-- **Math.** do Carmo Ch. 4, `lem:dc-ch4-4-1` (**algebraic collection step**).  The
commutator of covariant derivatives collects into the coordinate curvature contraction:
$$
\text{baseDerivΓ}(X, V, Y) - \text{baseDerivΓ}(Y, V, X)
  + \Gamma\big(Y, \Gamma(X, V)\big) - \Gamma\big(X, \Gamma(Y, V)\big)
  = R(X, Y)V ,
$$
the coordinate form of `∇_Y∇_X V − ∇_X∇_Y V = R(X, Y)V` (the `[X, Y] = 0` case for
coordinate fields, since here `X, Y` are frozen vectors).  Pure index algebra: the four
terms reindex onto the four terms of the coordinate curvature coefficient
`chartCurvatureCoef`. -/
theorem chartCurvatureContraction2_eq_commutator (g : RiemannianMetric I M) (α : M)
    (X Y V y : E) :
    baseDerivChristoffelContraction (I := I) g α X V Y y
      - baseDerivChristoffelContraction (I := I) g α Y V X y
      + Geodesic.chartChristoffelContraction (I := I) g α Y
          (Geodesic.chartChristoffelContraction (I := I) g α X V y) y
      - Geodesic.chartChristoffelContraction (I := I) g α X
          (Geodesic.chartChristoffelContraction (I := I) g α Y V y) y
      = chartCurvatureContraction2 (I := I) g α X Y V y := by
  classical
  simp only [chartCurvatureContraction2, baseDerivChristoffelContraction,
    Geodesic.chartChristoffelContraction_def, chartCoord_sum_smul_finBasis]
  -- merge the four basis sums into a single `∑ l, (·) • e_l`
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp only [← sub_smul, ← add_smul]
  congr 1
  -- scalar coefficient identity per output index `l`: reindex each of the four terms
  -- onto the canonical `∑ᵢⱼₖ (·) Xⁱ Yʲ Vᵏ` layout, then match `chartCurvatureCoef`.
  -- canonical-layout targets
  set S1 : ℝ := ∑ i, ∑ j, ∑ k, partialDeriv (E := E) j (chartChristoffel (I := I) g α i k l) y
    * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j Y
    * Geodesic.chartCoord (E := E) k V with hS1
  set S2 : ℝ := ∑ i, ∑ j, ∑ k, partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l) y
    * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j Y
    * Geodesic.chartCoord (E := E) k V with hS2
  set S3 : ℝ := ∑ i, ∑ j, ∑ k, (∑ s, chartChristoffel (I := I) g α i k s y
      * chartChristoffel (I := I) g α j s l y)
    * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j Y
    * Geodesic.chartCoord (E := E) k V with hS3
  set S4 : ℝ := ∑ i, ∑ j, ∑ k, (∑ s, chartChristoffel (I := I) g α j k s y
      * chartChristoffel (I := I) g α i s l y)
    * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j Y
    * Geodesic.chartCoord (E := E) k V with hS4
  have hcA : (∑ i, ∑ j, (fderiv ℝ (chartChristoffel (I := I) g α i j l) y) Y
      * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j V) = S1 := by
    rw [hS1, baseDeriv_coef_expand]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hcB : (∑ i, ∑ j, (fderiv ℝ (chartChristoffel (I := I) g α i j l) y) X
      * Geodesic.chartCoord (E := E) i Y * Geodesic.chartCoord (E := E) j V) = S2 := by
    rw [hS2, baseDeriv_coef_expand]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => ?_
    ring
  have hcC : (∑ x, ∑ x_1, chartChristoffel (I := I) g α x x_1 l y
      * Geodesic.chartCoord (E := E) x Y
      * ∑ i, ∑ j, chartChristoffel (I := I) g α i j x_1 y
          * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j V) = S3 := by
    rw [hS3]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => Finset.sum_comm))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hcD : (∑ x, ∑ x_1, chartChristoffel (I := I) g α x x_1 l y
      * Geodesic.chartCoord (E := E) x X
      * ∑ i, ∑ j, chartChristoffel (I := I) g α i j x_1 y
          * Geodesic.chartCoord (E := E) i Y * Geodesic.chartCoord (E := E) j V) = S4 := by
    rw [hS4]
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) => Finset.sum_comm)]
    rw [Finset.sum_congr rfl (fun x (_ : x ∈ Finset.univ) =>
      Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => Finset.sum_comm))]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hRHS : (∑ i, ∑ j, ∑ k, chartCurvatureCoef (I := I) g α i j k l y
      * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j Y
      * Geodesic.chartCoord (E := E) k V) = S1 - S2 + S3 - S4 := by
    rw [hS1, hS2, hS3, hS4]
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun k _ => ?_
    simp only [chartCurvatureCoef, Finset.sum_sub_distrib]
    ring
  rw [hcA, hcB, hcC, hcD, hRHS]

/-! ## Slice derivatives and mixed partials of a parametrized surface

The building blocks that interface the one-variable crux lemma
`hasDerivAt_chartChristoffelContraction_along` with the two-variable surface `f`:
its slice curves `σ ↦ f(σ, τ)` / `τ ↦ f(σ, τ)`, and the equality of the two mixed
partials (Schwarz). -/

section SurfaceDerivatives

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Math.** Derivative of the first slice of a surface: `∂/∂σ f(σ, τ) = Df·(1,0)`. -/
theorem hasDerivAt_comp_fst {F : ℝ × ℝ → G} {DF : (ℝ × ℝ) →L[ℝ] G} {s τ : ℝ}
    (h : HasFDerivAt F DF (s, τ)) :
    HasDerivAt (fun σ => F (σ, τ)) (DF (1, 0)) s := by
  have hc : HasDerivAt (fun σ => (σ, τ)) ((1 : ℝ), (0 : ℝ)) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s τ)
  exact HasFDerivAt.comp_hasDerivAt (hl := h) (hf := hc)

/-- **Math.** Derivative of the second slice of a surface: `∂/∂τ f(σ, τ) = Df·(0,1)`. -/
theorem hasDerivAt_comp_snd {F : ℝ × ℝ → G} {DF : (ℝ × ℝ) →L[ℝ] G} {s τ : ℝ}
    (h : HasFDerivAt F DF (s, τ)) :
    HasDerivAt (fun σ => F (s, σ)) (DF (0, 1)) τ := by
  have hc : HasDerivAt (fun σ => (s, σ)) ((0 : ℝ), (1 : ℝ)) τ :=
    (hasDerivAt_const τ s).prodMk (hasDerivAt_id τ)
  exact HasFDerivAt.comp_hasDerivAt (hl := h) (hf := hc)

/-- **Math.** The mixed partial `∂/∂τ (∂/∂σ f)|_{σ=s₀} = D²f·(0,1)·(1,0)`. -/
theorem hasDerivAt_mixed_fst_snd {F : ℝ × ℝ → G} {DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G)}
    {D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] G} {s₀ t₀ : ℝ}
    (hF : ∀ p, HasFDerivAt F (DF p) p) (hF2 : HasFDerivAt DF D2F (s₀, t₀)) :
    HasDerivAt (fun τ => deriv (fun σ => F (σ, τ)) s₀) (D2F (0, 1) (1, 0)) t₀ := by
  have hfun : (fun τ => deriv (fun σ => F (σ, τ)) s₀) = fun τ => DF (s₀, τ) (1, 0) := by
    funext τ; exact (hasDerivAt_comp_fst (hF (s₀, τ))).deriv
  rw [hfun]
  have hDF : HasDerivAt (fun τ => DF (s₀, τ)) (D2F (0, 1)) t₀ := hasDerivAt_comp_snd hF2
  exact HasFDerivAt.comp_hasDerivAt
    (hl := (ContinuousLinearMap.apply ℝ G ((1, 0) : ℝ × ℝ)).hasFDerivAt) (hf := hDF)

/-- **Math.** The mixed partial `∂/∂σ (∂/∂τ f)|_{τ=t₀} = D²f·(1,0)·(0,1)`. -/
theorem hasDerivAt_mixed_snd_fst {F : ℝ × ℝ → G} {DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G)}
    {D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] G} {s₀ t₀ : ℝ}
    (hF : ∀ p, HasFDerivAt F (DF p) p) (hF2 : HasFDerivAt DF D2F (s₀, t₀)) :
    HasDerivAt (fun σ => deriv (fun τ => F (σ, τ)) t₀) (D2F (1, 0) (0, 1)) s₀ := by
  have hfun : (fun σ => deriv (fun τ => F (σ, τ)) t₀) = fun σ => DF (σ, t₀) (0, 1) := by
    funext σ; exact (hasDerivAt_comp_snd (hF (σ, t₀))).deriv
  rw [hfun]
  have hDF : HasDerivAt (fun σ => DF (σ, t₀)) (D2F (1, 0)) s₀ := hasDerivAt_comp_fst hF2
  exact HasFDerivAt.comp_hasDerivAt
    (hl := (ContinuousLinearMap.apply ℝ G ((0, 1) : ℝ × ℝ)).hasFDerivAt) (hf := hDF)

/-- **Math.** **Schwarz / Clairaut** for a surface: the two mixed partials agree,
`∂τ∂σ f = ∂σ∂τ f`, from `second_derivative_symmetric`. -/
theorem mixed_partial_symm {F : ℝ × ℝ → G} {DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G)}
    {D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] G} {s₀ t₀ : ℝ}
    (hF : ∀ p, HasFDerivAt F (DF p) p) (hF2 : HasFDerivAt DF D2F (s₀, t₀)) :
    D2F (0, 1) (1, 0) = D2F (1, 0) (0, 1) :=
  second_derivative_symmetric hF hF2 (0, 1) (1, 0)

/-! ### Localized (`eventually`) versions of the mixed partials

The parametrized surfaces coming from the exponential map are only `C²` on a ball in
`E`, not on all of `ℝ²`; the `∀ p, HasFDerivAt f (Df p) p` hypothesis above is then
undischargeable.  The following variants require differentiability only on a
neighbourhood of the base point `(s₀, t₀)`, exactly what such local surfaces supply.
This mirrors `second_derivative_symmetric_of_eventually` / do Carmo's local surfaces. -/

/-- **Math.** The mixed partial `∂/∂τ (∂/∂σ f)|_{σ=s₀} = D²f·(0,1)·(1,0)`, requiring
differentiability of `f` only on a neighbourhood of `(s₀, t₀)`. -/
theorem hasDerivAt_mixed_fst_snd_of_eventually {F : ℝ × ℝ → G}
    {DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G)} {D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] G} {s₀ t₀ : ℝ}
    (hF : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt F (DF p) p) (hF2 : HasFDerivAt DF D2F (s₀, t₀)) :
    HasDerivAt (fun τ => deriv (fun σ => F (σ, τ)) s₀) (D2F (0, 1) (1, 0)) t₀ := by
  have hev : ∀ᶠ τ in nhds t₀, HasFDerivAt F (DF (s₀, τ)) (s₀, τ) := by
    have hcont : ContinuousAt (fun τ : ℝ => ((s₀, τ) : ℝ × ℝ)) t₀ :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact hcont.eventually hF
  have heq : (fun τ => deriv (fun σ => F (σ, τ)) s₀) =ᶠ[nhds t₀] fun τ => DF (s₀, τ) (1, 0) := by
    filter_upwards [hev] with τ hτ using (hasDerivAt_comp_fst hτ).deriv
  have hDF : HasDerivAt (fun τ => DF (s₀, τ)) (D2F (0, 1)) t₀ := hasDerivAt_comp_snd hF2
  have hbase : HasDerivAt (fun τ => DF (s₀, τ) (1, 0)) (D2F (0, 1) (1, 0)) t₀ :=
    HasFDerivAt.comp_hasDerivAt
      (hl := (ContinuousLinearMap.apply ℝ G ((1, 0) : ℝ × ℝ)).hasFDerivAt) (hf := hDF)
  exact hbase.congr_of_eventuallyEq heq

/-- **Math.** The mixed partial `∂/∂σ (∂/∂τ f)|_{τ=t₀} = D²f·(1,0)·(0,1)`, requiring
differentiability of `f` only on a neighbourhood of `(s₀, t₀)`. -/
theorem hasDerivAt_mixed_snd_fst_of_eventually {F : ℝ × ℝ → G}
    {DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G)} {D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] G} {s₀ t₀ : ℝ}
    (hF : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt F (DF p) p) (hF2 : HasFDerivAt DF D2F (s₀, t₀)) :
    HasDerivAt (fun σ => deriv (fun τ => F (σ, τ)) t₀) (D2F (1, 0) (0, 1)) s₀ := by
  have hev : ∀ᶠ σ in nhds s₀, HasFDerivAt F (DF (σ, t₀)) (σ, t₀) := by
    have hcont : ContinuousAt (fun σ : ℝ => ((σ, t₀) : ℝ × ℝ)) s₀ :=
      (continuous_id.prodMk continuous_const).continuousAt
    exact hcont.eventually hF
  have heq : (fun σ => deriv (fun τ => F (σ, τ)) t₀) =ᶠ[nhds s₀] fun σ => DF (σ, t₀) (0, 1) := by
    filter_upwards [hev] with σ hσ using (hasDerivAt_comp_snd hσ).deriv
  have hDF : HasDerivAt (fun σ => DF (σ, t₀)) (D2F (1, 0)) s₀ := hasDerivAt_comp_fst hF2
  have hbase : HasDerivAt (fun σ => DF (σ, t₀) (0, 1)) (D2F (1, 0) (0, 1)) s₀ :=
    HasFDerivAt.comp_hasDerivAt
      (hl := (ContinuousLinearMap.apply ℝ G ((0, 1) : ℝ × ℝ)).hasFDerivAt) (hf := hDF)
  exact hbase.congr_of_eventuallyEq heq

/-- **Math.** **Schwarz / Clairaut** for a surface, localized: the two mixed partials
agree, requiring differentiability of `f` only on a neighbourhood of `(s₀, t₀)`. -/
theorem mixed_partial_symm_of_eventually {F : ℝ × ℝ → G} {DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] G)}
    {D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] G} {s₀ t₀ : ℝ}
    (hF : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt F (DF p) p) (hF2 : HasFDerivAt DF D2F (s₀, t₀)) :
    D2F (0, 1) (1, 0) = D2F (1, 0) (0, 1) :=
  second_derivative_symmetric_of_eventually hF hF2 (0, 1) (1, 0)

end SurfaceDerivatives

/-! ## The two covariant derivatives along a parametrized surface -/

/-- **Math.** do Carmo Ch. 4: the covariant derivative `D/∂s V` of a field `V` along a
parametrized surface `f` (chart readings), at `p = (s, t)`: the coordinate covariant
derivative of the `s`-slice `σ ↦ V(σ, t)` along the `s`-slice `σ ↦ f(σ, t)`. -/
def surfaceCovariantDerivS (g : RiemannianMetric I M) (α : M) (f V : ℝ × ℝ → E)
    (p : ℝ × ℝ) : E :=
  covariantDerivCoord (I := I) g α (fun σ => f (σ, p.2)) (fun σ => V (σ, p.2)) p.1

/-- **Math.** do Carmo Ch. 4: the covariant derivative `D/∂t V` of a field `V` along a
parametrized surface `f`, at `p = (s, t)`. -/
def surfaceCovariantDerivT (g : RiemannianMetric I M) (α : M) (f V : ℝ × ℝ → E)
    (p : ℝ × ℝ) : E :=
  covariantDerivCoord (I := I) g α (fun τ => f (p.1, τ)) (fun τ => V (p.1, τ)) p.2

/-- **Math.** do Carmo Ch. 4, `lem:dc-ch4-4-1` (**surface curvature commutation**).
For a `C²` parametrized surface `f : ℝ² → M` and a `C²` field `V` along it (read in the
fixed chart at `α`), the covariant derivatives commute up to curvature:
$$
\frac{D}{\partial t}\frac{D}{\partial s}V - \frac{D}{\partial s}\frac{D}{\partial t}V
  = R\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)V .
$$
This is the identity that turns the geodesic condition into the Jacobi equation. -/
theorem surface_covariant_commutator_of_eventually [I.Boundaryless]
    (g : RiemannianMetric I M) (α : M) (f V : ℝ × ℝ → E)
    (Df DV : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E))
    (D2f D2V : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E) (s₀ t₀ : ℝ)
    (hf : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt f (Df p) p) (hf2 : HasFDerivAt Df D2f (s₀, t₀))
    (hV : ∀ᶠ p in nhds (s₀, t₀), HasFDerivAt V (DV p) p) (hV2 : HasFDerivAt DV D2V (s₀, t₀))
    (hmem : f (s₀, t₀) ∈ interior (extChartAt I α).target) :
    surfaceCovariantDerivT (I := I) g α f (surfaceCovariantDerivS (I := I) g α f V) (s₀, t₀)
      - surfaceCovariantDerivS (I := I) g α f (surfaceCovariantDerivT (I := I) g α f V) (s₀, t₀)
    = chartCurvatureContraction2 (I := I) g α
        (Df (s₀, t₀) (1, 0)) (Df (s₀, t₀) (0, 1)) (V (s₀, t₀)) (f (s₀, t₀)) := by
  classical
  -- the τ-derivative at t₀ of the field `τ ↦ (D/∂s V)(s₀, τ)`
  have key_s : HasDerivAt (fun τ => surfaceCovariantDerivS (I := I) g α f V (s₀, τ))
      (D2V (0, 1) (1, 0)
        + (Geodesic.chartChristoffelContraction (I := I) g α (D2f (0, 1) (1, 0))
              (V (s₀, t₀)) (f (s₀, t₀))
          + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
              (DV (s₀, t₀) (0, 1)) (f (s₀, t₀))
          + baseDerivChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
              (V (s₀, t₀)) (Df (s₀, t₀) (0, 1)) (f (s₀, t₀)))) t₀ := by
    simp only [surfaceCovariantDerivS, covariantDerivCoord_def]
    have hVs := hasDerivAt_mixed_fst_snd_of_eventually hV hV2
    have ha := hasDerivAt_mixed_fst_snd_of_eventually hf hf2
    have hb := hasDerivAt_comp_snd hV.self_of_nhds
    have hc := hasDerivAt_comp_snd hf.self_of_nhds
    have hval_a : deriv (fun σ => f (σ, t₀)) s₀ = Df (s₀, t₀) (1, 0) :=
      (hasDerivAt_comp_fst hf.self_of_nhds).deriv
    have hΓ := hasDerivAt_chartChristoffelContraction_along g α
      (fun τ => deriv (fun σ => f (σ, τ)) s₀) (fun τ => V (s₀, τ)) (fun τ => f (s₀, τ))
      (D2f (0, 1) (1, 0)) (DV (s₀, t₀) (0, 1)) (Df (s₀, t₀) (0, 1)) ha hb hc hmem
    simp only [hval_a] at hΓ
    exact hVs.add hΓ
  -- the σ-derivative at s₀ of the field `σ ↦ (D/∂t V)(σ, t₀)`
  have key_t : HasDerivAt (fun σ => surfaceCovariantDerivT (I := I) g α f V (σ, t₀))
      (D2V (1, 0) (0, 1)
        + (Geodesic.chartChristoffelContraction (I := I) g α (D2f (1, 0) (0, 1))
              (V (s₀, t₀)) (f (s₀, t₀))
          + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
              (DV (s₀, t₀) (1, 0)) (f (s₀, t₀))
          + baseDerivChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
              (V (s₀, t₀)) (Df (s₀, t₀) (1, 0)) (f (s₀, t₀)))) s₀ := by
    simp only [surfaceCovariantDerivT, covariantDerivCoord_def]
    have hVt := hasDerivAt_mixed_snd_fst_of_eventually hV hV2
    have ha := hasDerivAt_mixed_snd_fst_of_eventually hf hf2
    have hb := hasDerivAt_comp_fst hV.self_of_nhds
    have hc := hasDerivAt_comp_fst hf.self_of_nhds
    have hval_a : deriv (fun τ => f (s₀, τ)) t₀ = Df (s₀, t₀) (0, 1) :=
      (hasDerivAt_comp_snd hf.self_of_nhds).deriv
    have hΓ := hasDerivAt_chartChristoffelContraction_along g α
      (fun σ => deriv (fun τ => f (σ, τ)) t₀) (fun σ => V (σ, t₀)) (fun σ => f (σ, t₀))
      (D2f (1, 0) (0, 1)) (DV (s₀, t₀) (1, 0)) (Df (s₀, t₀) (1, 0)) ha hb hc hmem
    simp only [hval_a] at hΓ
    exact hVt.add hΓ
  -- slice-derivative values at the base point
  have hVs0 : deriv (fun σ => V (σ, t₀)) s₀ = DV (s₀, t₀) (1, 0) :=
    (hasDerivAt_comp_fst hV.self_of_nhds).deriv
  have hfs0 : deriv (fun σ => f (σ, t₀)) s₀ = Df (s₀, t₀) (1, 0) :=
    (hasDerivAt_comp_fst hf.self_of_nhds).deriv
  have hVt0 : deriv (fun τ => V (s₀, τ)) t₀ = DV (s₀, t₀) (0, 1) :=
    (hasDerivAt_comp_snd hV.self_of_nhds).deriv
  have hft0 : deriv (fun τ => f (s₀, τ)) t₀ = Df (s₀, t₀) (0, 1) :=
    (hasDerivAt_comp_snd hf.self_of_nhds).deriv
  -- the values of `D/∂s V` and `D/∂t V` at the base point
  have hSval : surfaceCovariantDerivS (I := I) g α f V (s₀, t₀)
      = DV (s₀, t₀) (1, 0)
        + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
            (V (s₀, t₀)) (f (s₀, t₀)) := by
    simp only [surfaceCovariantDerivS, covariantDerivCoord_def, hVs0, hfs0]
  have hTval : surfaceCovariantDerivT (I := I) g α f V (s₀, t₀)
      = DV (s₀, t₀) (0, 1)
        + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
            (V (s₀, t₀)) (f (s₀, t₀)) := by
    simp only [surfaceCovariantDerivT, covariantDerivCoord_def, hVt0, hft0]
  -- expand the two iterated covariant derivatives at the base point
  have hTS : surfaceCovariantDerivT (I := I) g α f (surfaceCovariantDerivS (I := I) g α f V) (s₀, t₀)
      = (D2V (0, 1) (1, 0)
          + (Geodesic.chartChristoffelContraction (I := I) g α (D2f (0, 1) (1, 0))
                (V (s₀, t₀)) (f (s₀, t₀))
            + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
                (DV (s₀, t₀) (0, 1)) (f (s₀, t₀))
            + baseDerivChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
                (V (s₀, t₀)) (Df (s₀, t₀) (0, 1)) (f (s₀, t₀))))
        + (Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
              (DV (s₀, t₀) (1, 0)) (f (s₀, t₀))
          + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
              (Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
                (V (s₀, t₀)) (f (s₀, t₀))) (f (s₀, t₀))) := by
    simp only [surfaceCovariantDerivT, covariantDerivCoord_def]
    rw [key_s.deriv, hft0, hSval, Geodesic.chartChristoffelContraction_add_right]
  have hST : surfaceCovariantDerivS (I := I) g α f (surfaceCovariantDerivT (I := I) g α f V) (s₀, t₀)
      = (D2V (1, 0) (0, 1)
          + (Geodesic.chartChristoffelContraction (I := I) g α (D2f (1, 0) (0, 1))
                (V (s₀, t₀)) (f (s₀, t₀))
            + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
                (DV (s₀, t₀) (1, 0)) (f (s₀, t₀))
            + baseDerivChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
                (V (s₀, t₀)) (Df (s₀, t₀) (1, 0)) (f (s₀, t₀))))
        + (Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
              (DV (s₀, t₀) (0, 1)) (f (s₀, t₀))
          + Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (1, 0))
              (Geodesic.chartChristoffelContraction (I := I) g α (Df (s₀, t₀) (0, 1))
                (V (s₀, t₀)) (f (s₀, t₀))) (f (s₀, t₀))) := by
    simp only [surfaceCovariantDerivS, covariantDerivCoord_def]
    rw [key_t.deriv, hfs0, hTval, Geodesic.chartChristoffelContraction_add_right]
  -- Schwarz kills the mixed-second-derivative and the repeated connection terms;
  -- the residue is exactly the connection commutator, which collects into the curvature.
  rw [hTS, hST, ← mixed_partial_symm_of_eventually hV hV2, ← mixed_partial_symm_of_eventually hf hf2,
    ← chartCurvatureContraction2_eq_commutator g α (Df (s₀, t₀) (1, 0)) (Df (s₀, t₀) (0, 1))
      (V (s₀, t₀)) (f (s₀, t₀))]
  abel

/-- **Math.** do Carmo Ch. 4, `lem:dc-ch4-4-1` (**surface curvature commutation**).
For a `C²` parametrized surface `f : ℝ² → M` and a `C²` field `V` along it (read in the
fixed chart at `α`), the covariant derivatives commute up to curvature:
$$
\frac{D}{\partial t}\frac{D}{\partial s}V - \frac{D}{\partial s}\frac{D}{\partial t}V
  = R\Big(\frac{\partial f}{\partial s}, \frac{\partial f}{\partial t}\Big)V .
$$
This is the identity that turns the geodesic condition into the Jacobi equation.  It is
the `∀ p` (globally-`C²`) specialization of `surface_covariant_commutator_of_eventually`. -/
theorem surface_covariant_commutator [I.Boundaryless]
    (g : RiemannianMetric I M) (α : M) (f V : ℝ × ℝ → E)
    (Df DV : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E))
    (D2f D2V : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E) (s₀ t₀ : ℝ)
    (hf : ∀ p, HasFDerivAt f (Df p) p) (hf2 : HasFDerivAt Df D2f (s₀, t₀))
    (hV : ∀ p, HasFDerivAt V (DV p) p) (hV2 : HasFDerivAt DV D2V (s₀, t₀))
    (hmem : f (s₀, t₀) ∈ interior (extChartAt I α).target) :
    surfaceCovariantDerivT (I := I) g α f (surfaceCovariantDerivS (I := I) g α f V) (s₀, t₀)
      - surfaceCovariantDerivS (I := I) g α f (surfaceCovariantDerivT (I := I) g α f V) (s₀, t₀)
    = chartCurvatureContraction2 (I := I) g α
        (Df (s₀, t₀) (1, 0)) (Df (s₀, t₀) (0, 1)) (V (s₀, t₀)) (f (s₀, t₀)) :=
  surface_covariant_commutator_of_eventually (I := I) g α f V Df DV D2f D2V s₀ t₀
    (Filter.Eventually.of_forall hf) hf2 (Filter.Eventually.of_forall hV) hV2 hmem

end PetersenLib.Jacobi

end

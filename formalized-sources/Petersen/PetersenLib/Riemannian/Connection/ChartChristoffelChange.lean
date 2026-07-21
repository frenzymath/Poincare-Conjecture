/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Connection/ChartChristoffelChange.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Geodesic.HopfRinow.MetricBridge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Change-of-chart transformation law for the chart Christoffel symbols

The chart Christoffel symbols `chartChristoffel g α` (`Connection/ChartChristoffel.lean`)
are computed from the metric Gram matrix in the chart at a basepoint `α`. This file
proves the classical **inhomogeneous transformation law** relating the symbols of two
basepoints `α, β` at a common foot `x`:

`A x (Γ^β(v, w)) = Γ^α(A x v, A x w) + D²τ(v, w)`,

where `A x = tangentCoordChange I β α x` is the derivative of the chart transition
`τ = extChartAt I α ∘ (extChartAt I β).symm` and `D²τ` its second derivative at the
`β`-chart image of `x` (`chartChristoffelContraction_change`). This is the identity that
makes the geodesic equation `γ'' = −Γ(γ', γ')` chart-independent: it is the toll gate
for rebasing chart-anchored geodesic witnesses, intrinsic local uniqueness, and the
maximal-geodesic gluing needed by Hopf–Rinow c) ⟹ d) (do Carmo Ch. 7, Thm. 2.8; inbox
I-0100).

The proof follows the classical route, organised around the **contraction identity**
`chartGram_christoffel_contraction` (`Σ_m G_{am} Γ^m_{ki} = ½(∂_k G_{ai} + ∂_i G_{ak}
− ∂_a G_{ki})`) which characterises the symbols through the invertible Gram matrix:

1. the zeroth-order Gram change law `G^β = Aᵀ(G^α∘τ)A` (`chartGramMatrix_change`,
   `Geodesic/HopfRinow/MetricBridge.lean`) is upgraded to an identity of functions on
   the open overlap `chartTransitionCCSource β α` in `β`-chart coordinates
   (`chartGramOnE_chartTransitionCC`);
2. differentiating it (product/chain rule; the derivative of `A` brings in the second
   derivative of the transition `τ`) expresses `∂G^β` through `∂G^α`, `A`, and `D²τ`
   (`partialDeriv_chartGramOnE_chartTransitionCC`);
3. substituting into the `β`-contraction identity, the `D²τ` cross-terms cancel by the
   symmetry of `D²τ` (Schwarz) and of `G^α`, and the `∂G^α` combination reassembles
   into the `α`-contraction identity (`sum_gram_mul_christoffel_transition`);
4. comparing with the direct expansion of `G^β` (`sum_gram_mul_christoffel_expand`)
   and cancelling the invertible `A` and `G^α` yields the index-level law
   (`sum_transitionDeriv_mul_chartChristoffel`), whence the bilinear form.

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 (the connection in coordinates);
Lee, *Riemannian Manifolds*, Ch. 5 (transformation law for the Christoffel symbols).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chart-coordinate helpers

The coordinate functional `Geodesic.chartCoordFunctional` and the directional
derivative expansion `fderiv_apply_eq_sum_partialDeriv` are provided by
`Geodesic/CovariantDerivative.lean`. -/

/-- **Math.** The chart coordinates of a basis vector are Kronecker deltas. -/
lemma chartCoord_finBasis (a b : Fin (Module.finrank ℝ E)) :
    Geodesic.chartCoord (E := E) a ((Module.finBasis ℝ E) b)
      = if b = a then (1 : ℝ) else 0 := by
  rw [Geodesic.chartCoord_def, Module.Basis.repr_self, Finsupp.single_apply]

/-- **Math.** Expansion of a continuous linear map through the chart basis, in
coordinates: `(f v)^a = Σ_k v^k (f e_k)^a`. -/
lemma chartCoord_clm_eq_sum (f : E →L[ℝ] E) (a : Fin (Module.finrank ℝ E)) (v : E) :
    Geodesic.chartCoord (E := E) a (f v)
      = ∑ k, Geodesic.chartCoord (E := E) k v
          * Geodesic.chartCoord (E := E) a (f ((Module.finBasis ℝ E) k)) := by
  have hfv : f v = ∑ k, (Module.finBasis ℝ E).repr v k • f ((Module.finBasis ℝ E) k) := by
    conv_lhs => rw [← Module.Basis.sum_repr (Module.finBasis ℝ E) v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul]
  rw [← Geodesic.chartCoordFunctional_apply, hfv, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Geodesic.chartCoordFunctional_apply]
  rfl

/-! ## The chart transition map and its derivatives -/

section Transition

variable [I.Boundaryless]

/-- **Math.** The chart transition map from `β`-chart coordinates to `α`-chart
coordinates, as a bare function `E → E` (junk outside the overlap). On the overlap
`chartTransitionCCSource β α` its derivative is `tangentCoordChange I β α` at the
moving foot. The argument order matches `tangentCoordChange I β α`. -/
def chartTransitionCC (β α : M) : E → E :=
  extChartAt I α ∘ (extChartAt I β).symm

@[simp] lemma chartTransitionCC_def (β α : M) (y : E) :
    chartTransitionCC (I := I) β α y = extChartAt I α ((extChartAt I β).symm y) := rfl

/-- **Math.** The overlap of the charts at `β` and `α`, read in `β`-chart
coordinates: the source of the transition `chartTransitionCC β α`. -/
def chartTransitionCCSource (β α : M) : Set E :=
  ((extChartAt I β).symm.trans (extChartAt I α)).source

lemma chartTransitionCCSource_eq (β α : M) :
    chartTransitionCCSource (I := I) (M := M) β α
      = (extChartAt I β).target
          ∩ (extChartAt I β).symm ⁻¹' (chartAt H α).source := by
  unfold chartTransitionCCSource
  rw [PartialEquiv.trans_source, PartialEquiv.symm_source, extChartAt_source]

/-- **Math.** The chart overlap is open in `β`-chart coordinates (boundaryless). -/
lemma isOpen_chartTransitionCCSource (β α : M) :
    IsOpen (chartTransitionCCSource (I := I) (M := M) β α) := by
  rw [chartTransitionCCSource_eq]
  exact ContinuousOn.isOpen_inter_preimage (continuousOn_extChartAt_symm β)
    (isOpen_extChartAt_target β) (chartAt H α).open_source

/-- **Math.** On the overlap, the foot `(extChartAt I β).symm y` lies in the chart
source at `β`. -/
lemma extChartAt_symm_mem_chartAt_source_left {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    (extChartAt I β).symm y ∈ (chartAt H β).source := by
  rw [chartTransitionCCSource_eq] at hy
  have := (extChartAt I β).map_target hy.1
  rwa [extChartAt_source] at this

/-- **Math.** On the overlap, the foot `(extChartAt I β).symm y` lies in the chart
source at `α`. -/
lemma extChartAt_symm_mem_chartAt_source_right {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    (extChartAt I β).symm y ∈ (chartAt H α).source := by
  rw [chartTransitionCCSource_eq] at hy
  exact hy.2

/-- **Math.** On the overlap, the `β`-chart reading of the foot is `y` itself. -/
lemma extChartAt_extChartAt_symm_of_mem {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    extChartAt I β ((extChartAt I β).symm y) = y := by
  rw [chartTransitionCCSource_eq] at hy
  exact (extChartAt I β).right_inv hy.1

/-- **Math.** On the overlap, the transition image lies in the `α`-chart target. -/
lemma chartTransitionCC_mem_target {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    chartTransitionCC (I := I) β α y ∈ (extChartAt I α).target := by
  refine (extChartAt I α).map_source ?_
  rw [extChartAt_source]
  exact extChartAt_symm_mem_chartAt_source_right (I := I) hy

/-- **Math.** On the overlap, pulling the transition image back through the `α`-chart
recovers the common foot. -/
lemma extChartAt_symm_chartTransitionCC {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    (extChartAt I α).symm (chartTransitionCC (I := I) β α y)
      = (extChartAt I β).symm y := by
  refine (extChartAt I α).left_inv ?_
  rw [extChartAt_source]
  exact extChartAt_symm_mem_chartAt_source_right (I := I) hy

/-- **Math.** Entry point from a manifold point: if `x` lies in both chart sources,
its `β`-chart image lies in the overlap. -/
lemma extChartAt_mem_chartTransitionCCSource {β α : M} {x : M}
    (hxβ : x ∈ (chartAt H β).source) (hxα : x ∈ (chartAt H α).source) :
    extChartAt I β x ∈ chartTransitionCCSource (I := I) (M := M) β α := by
  have hxβ' : x ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hxβ
  rw [chartTransitionCCSource_eq]
  refine ⟨(extChartAt I β).map_source hxβ', ?_⟩
  rw [mem_preimage, (extChartAt I β).left_inv hxβ']
  exact hxα

/-- **Math.** At the `β`-chart image of a common point `x`, the transition reads off
the `α`-chart image of `x`. -/
lemma chartTransitionCC_extChartAt {β α : M} {x : M}
    (hxβ : x ∈ (chartAt H β).source) :
    chartTransitionCC (I := I) β α (extChartAt I β x) = extChartAt I α x := by
  have hxβ' : x ∈ (extChartAt I β).source := by rw [extChartAt_source]; exact hxβ
  rw [chartTransitionCC_def, (extChartAt I β).left_inv hxβ']

/-- **Math.** The transition map is `C^∞` on the overlap. -/
lemma contDiffOn_chartTransitionCC (β α : M) :
    ContDiffOn ℝ ∞ (chartTransitionCC (I := I) β α)
      (chartTransitionCCSource (I := I) (M := M) β α) :=
  contDiffOn_ext_coord_change (I := I) α β

/-- **Math.** The transition map is `C^∞` at each point of the (open) overlap. -/
lemma contDiffAt_chartTransitionCC {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    ContDiffAt ℝ ∞ (chartTransitionCC (I := I) β α) y :=
  (contDiffOn_chartTransitionCC (I := I) β α).contDiffAt
    ((isOpen_chartTransitionCCSource (I := I) β α).mem_nhds hy)

/-- **Math.** On the overlap, the transition map differentiates to the tangent
coordinate change at the moving foot. -/
lemma hasFDerivAt_chartTransitionCC {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    HasFDerivAt (chartTransitionCC (I := I) β α)
      (tangentCoordChange I β α ((extChartAt I β).symm y)) y := by
  have hβ : (extChartAt I β).symm y ∈ (extChartAt I β).source := by
    rw [extChartAt_source]; exact extChartAt_symm_mem_chartAt_source_left (I := I) hy
  have hα : (extChartAt I β).symm y ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact extChartAt_symm_mem_chartAt_source_right (I := I) hy
  have hw := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hβ, hα⟩
  rw [I.range_eq_univ] at hw
  rw [extChartAt_extChartAt_symm_of_mem (I := I) hy] at hw
  exact hasFDerivWithinAt_univ.mp hw

/-- **Math.** The full-space `fderiv` of the transition on the overlap is the
tangent coordinate change at the moving foot. -/
lemma fderiv_chartTransitionCC {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    fderiv ℝ (chartTransitionCC (I := I) β α) y
      = tangentCoordChange I β α ((extChartAt I β).symm y) :=
  (hasFDerivAt_chartTransitionCC (I := I) hy).fderiv

/-- **Math.** `A^a_i(y)`: the matrix entry of the transition derivative at `y`, in
the chart basis — classically `∂x^a/∂y^i` for the transition `x = τ(y)` from
`β`-coordinates `y` to `α`-coordinates `x`. -/
def transitionDeriv (β α : M) (a i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  Geodesic.chartCoord (E := E) a
    (fderiv ℝ (chartTransitionCC (I := I) β α) y ((Module.finBasis ℝ E) i))

@[simp] lemma transitionDeriv_def (β α : M) (a i : Fin (Module.finrank ℝ E)) (y : E) :
    transitionDeriv (I := I) β α a i y
      = Geodesic.chartCoord (E := E) a
          (fderiv ℝ (chartTransitionCC (I := I) β α) y ((Module.finBasis ℝ E) i)) := rfl

/-- **Math.** `B^a_{ki}(y)`: the second-derivative coefficient of the transition —
classically `∂²x^a/∂y^k∂y^i`. -/
def transitionSndDeriv (β α : M) (a k i : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  Geodesic.chartCoord (E := E) a
    (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y ((Module.finBasis ℝ E) k)
      ((Module.finBasis ℝ E) i))

@[simp] lemma transitionSndDeriv_def (β α : M)
    (a k i : Fin (Module.finrank ℝ E)) (y : E) :
    transitionSndDeriv (I := I) β α a k i y
      = Geodesic.chartCoord (E := E) a
          (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y
            ((Module.finBasis ℝ E) k) ((Module.finBasis ℝ E) i)) := rfl

/-- **Math.** **Schwarz symmetry** of the transition second derivative in the two
differentiation directions: `∂²x^a/∂y^k∂y^i = ∂²x^a/∂y^i∂y^k` on the overlap. -/
lemma transitionSndDeriv_symm {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (a k i : Fin (Module.finrank ℝ E)) :
    transitionSndDeriv (I := I) β α a k i y
      = transitionSndDeriv (I := I) β α a i k y := by
  have hsymm : IsSymmSndFDerivAt ℝ (chartTransitionCC (I := I) β α) y := by
    refine (contDiffAt_chartTransitionCC (I := I) hy).isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.2 le_top
  rw [transitionSndDeriv_def, transitionSndDeriv_def, hsymm.eq]

/-- **Math.** The moving transition derivative `y ↦ Dτ(y)` is differentiable on the
overlap (as a map into continuous linear maps), with derivative the second
derivative of the transition. -/
lemma hasFDerivAt_fderiv_chartTransitionCC {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α) :
    HasFDerivAt (fderiv ℝ (chartTransitionCC (I := I) β α))
      (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ (chartTransitionCC (I := I) β α)) y := by
    refine (contDiffAt_chartTransitionCC (I := I) hy).fderiv_right ?_
    exact WithTop.coe_le_coe.2 le_top
  exact (h1.differentiableAt one_ne_zero).hasFDerivAt

/-- **Math.** The matrix-entry function `A^a_i` is differentiable on the overlap,
with partial derivatives the second-derivative coefficients `B^a_{ki}`. -/
lemma hasFDerivAt_transitionDeriv {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (a i : Fin (Module.finrank ℝ E)) :
    HasFDerivAt (transitionDeriv (I := I) β α a i)
      ((Geodesic.chartCoordFunctional (E := E) a).comp
        ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).comp
          (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y))) y := by
  have h2 := hasFDerivAt_fderiv_chartTransitionCC (I := I) hy
  have h3 := ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).hasFDerivAt.comp
    y h2)
  exact (Geodesic.chartCoordFunctional (E := E) a).hasFDerivAt.comp y h3

end Transition

/-! ## Step 1: the Gram change law at the `E`-level -/

section GramChange

variable [I.Boundaryless]

/-- **Math.** **The Gram change law through the transition map** (`E`-level form of
`chartGramMatrix_change`): on the overlap, the `β`-chart Gram entry is the
`α`-chart Gram entry at the transition image, conjugated by the transition
derivative: `G^β_{ij}(y) = Σ_{ab} G^α_{ab}(τ y) A^a_i(y) A^b_j(y)`. -/
theorem chartGramOnE_chartTransitionCC (g : RiemannianMetric I M) (α β : M) {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (I := I) g β i j y
      = ∑ a, ∑ b,
          chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α y)
            * transitionDeriv (I := I) β α a i y
            * transitionDeriv (I := I) β α b j y := by
  have hxβ := extChartAt_symm_mem_chartAt_source_left (I := I) hy
  have hxα := extChartAt_symm_mem_chartAt_source_right (I := I) hy
  have hchange := chartGramMatrix_change (I := I) g α β hxα hxβ i j
  rw [chartGramOnE_def, hchange]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [chartGramOnE_def, extChartAt_symm_chartTransitionCC (I := I) hy,
    transitionDeriv_def, transitionDeriv_def,
    fderiv_chartTransitionCC (I := I) hy]

/-- **Math.** **Derivative of the Gram change law** (the first-order layer): on the
overlap,
`∂_k G^β_{ij} = Σ_{ab} [(Σ_c ∂_c G^α_{ab}(τ y) A^c_k) A^a_i A^b_j
+ G^α_{ab}(τ y) (B^a_{ki} A^b_j + A^a_i B^b_{kj})]`.
Product rule on `chartGramOnE_chartTransitionCC`; the derivative of the moving
transition derivative brings in the second derivative of the transition. -/
theorem partialDeriv_chartGramOnE_chartTransitionCC (g : RiemannianMetric I M)
    (α β : M) {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (k i j : Fin (Module.finrank ℝ E)) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g β i j) y
      = ∑ a, ∑ b,
          ((∑ c, partialDeriv (E := E) c (chartGramOnE (I := I) g α a b)
                (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α c k y)
            * transitionDeriv (I := I) β α a i y
            * transitionDeriv (I := I) β α b j y
          + chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α y)
            * (transitionSndDeriv (I := I) β α a k i y
                * transitionDeriv (I := I) β α b j y
              + transitionDeriv (I := I) β α a i y
                * transitionSndDeriv (I := I) β α b k j y)) := by
  classical
  have heq : chartGramOnE (I := I) g β i j =ᶠ[𝓝 y]
      (fun z => ∑ a, ∑ b,
        chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α z)
          * transitionDeriv (I := I) β α a i z
          * transitionDeriv (I := I) β α b j z) := by
    filter_upwards [(isOpen_chartTransitionCCSource (I := I) β α).mem_nhds hy] with z hz
    exact chartGramOnE_chartTransitionCC (I := I) g α β hz i j
  have hτ : HasFDerivAt (chartTransitionCC (I := I) β α)
      (fderiv ℝ (chartTransitionCC (I := I) β α) y) y :=
    (hasFDerivAt_chartTransitionCC (I := I) hy).differentiableAt.hasFDerivAt
  have hG : ∀ a b : Fin (Module.finrank ℝ E),
      HasFDerivAt (chartGramOnE (I := I) g α a b)
        (fderiv ℝ (chartGramOnE (I := I) g α a b) (chartTransitionCC (I := I) β α y))
        (chartTransitionCC (I := I) β α y) := fun a b => by
    have hcd : ContDiffAt ℝ ∞ (chartGramOnE (I := I) g α a b)
        (chartTransitionCC (I := I) β α y) :=
      (chartGramOnE_contDiffOn (I := I) g α a b).contDiffAt
        ((isOpen_extChartAt_target (I := I) α).mem_nhds
          (chartTransitionCC_mem_target (I := I) hy))
    exact (hcd.differentiableAt (by simp)).hasFDerivAt
  have hcomp : ∀ a b : Fin (Module.finrank ℝ E),
      HasFDerivAt
        (fun z => chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α z))
        ((fderiv ℝ (chartGramOnE (I := I) g α a b)
            (chartTransitionCC (I := I) β α y)).comp
          (fderiv ℝ (chartTransitionCC (I := I) β α) y)) y :=
    fun a b => (hG a b).comp y hτ
  have hF : HasFDerivAt
      (fun z => ∑ a, ∑ b,
        chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α z)
          * transitionDeriv (I := I) β α a i z
          * transitionDeriv (I := I) β α b j z)
      (∑ a, ∑ b,
        ((chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α y)
            * transitionDeriv (I := I) β α a i y)
          • ((Geodesic.chartCoordFunctional (E := E) b).comp
              ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) j)).comp
                (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y)))
        + transitionDeriv (I := I) β α b j y
          • (chartGramOnE (I := I) g α a b (chartTransitionCC (I := I) β α y)
              • ((Geodesic.chartCoordFunctional (E := E) a).comp
                  ((ContinuousLinearMap.apply ℝ E ((Module.finBasis ℝ E) i)).comp
                    (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y)))
            + transitionDeriv (I := I) β α a i y
              • ((fderiv ℝ (chartGramOnE (I := I) g α a b)
                    (chartTransitionCC (I := I) β α y)).comp
                  (fderiv ℝ (chartTransitionCC (I := I) β α) y))))) y := by
    exact HasFDerivAt.fun_sum fun a _ => HasFDerivAt.fun_sum fun b _ =>
      ((hcomp a b).fun_mul (hasFDerivAt_transitionDeriv (I := I) hy a i)).fun_mul
        (hasFDerivAt_transitionDeriv (I := I) hy b j)
  have hpd : partialDeriv (E := E) k (chartGramOnE (I := I) g β i j) y
      = fderiv ℝ (chartGramOnE (I := I) g β i j) y ((Module.finBasis ℝ E) k) := rfl
  rw [hpd, heq.fderiv_eq, hF.fderiv]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have hsum : fderiv ℝ (chartGramOnE (I := I) g α a b) (chartTransitionCC (I := I) β α y)
      (fderiv ℝ (chartTransitionCC (I := I) β α) y ((Module.finBasis ℝ E) k))
      = ∑ c, partialDeriv (E := E) c (chartGramOnE (I := I) g α a b)
            (chartTransitionCC (I := I) β α y)
          * Geodesic.chartCoord (E := E) c
              (fderiv ℝ (chartTransitionCC (I := I) β α) y ((Module.finBasis ℝ E) k)) := by
    rw [fderiv_apply_eq_sum_partialDeriv]
    exact Finset.sum_congr rfl fun c _ => mul_comm _ _
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    Geodesic.chartCoordFunctional_apply, smul_eq_mul, transitionDeriv_def,
    transitionSndDeriv_def]
  rw [hsum]
  ring

end GramChange

/-! ## Steps 2–3: the contraction identity transported through the transition -/

section Contraction

variable [I.Boundaryless]

/-- **Math.** Cancellation of the (invertible) transition derivative: a covector
that annihilates every column `A e_a` of the transition derivative vanishes. -/
lemma eq_zero_of_forall_sum_mul_transitionDeriv {β α : M} {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (u : Fin (Module.finrank ℝ E) → ℝ)
    (h : ∀ a, ∑ p, u p * transitionDeriv (I := I) β α p a y = 0) :
    ∀ p, u p = 0 := by
  classical
  set x_y := (extChartAt I β).symm y with hxy_def
  have hβsrc : x_y ∈ (extChartAt I β).source := by
    rw [extChartAt_source]; exact extChartAt_symm_mem_chartAt_source_left (I := I) hy
  have hαsrc : x_y ∈ (extChartAt I α).source := by
    rw [extChartAt_source]; exact extChartAt_symm_mem_chartAt_source_right (I := I) hy
  have hderiv : fderiv ℝ (chartTransitionCC (I := I) β α) y
      = tangentCoordChange I β α x_y := fderiv_chartTransitionCC (I := I) hy
  have hAlt : ∀ a, ∑ p, u p * Geodesic.chartCoord (E := E) p
      (tangentCoordChange I β α x_y ((Module.finBasis ℝ E) a)) = 0 := by
    intro a
    have ha := h a
    simp only [transitionDeriv_def, hderiv] at ha
    exact ha
  have hlin : ∀ v : E, ∑ p, u p * Geodesic.chartCoord (E := E) p
      (tangentCoordChange I β α x_y v) = 0 := by
    intro v
    have hexpand : ∀ p, Geodesic.chartCoord (E := E) p (tangentCoordChange I β α x_y v)
        = ∑ k, Geodesic.chartCoord (E := E) k v *
            Geodesic.chartCoord (E := E) p
              (tangentCoordChange I β α x_y ((Module.finBasis ℝ E) k)) :=
      fun p => chartCoord_clm_eq_sum (tangentCoordChange I β α x_y) p v
    simp only [hexpand, Finset.mul_sum]
    rw [Finset.sum_comm]
    have step : ∀ k : Fin (Module.finrank ℝ E),
        (∑ p, u p * (Geodesic.chartCoord (E := E) k v *
            Geodesic.chartCoord (E := E) p
              (tangentCoordChange I β α x_y ((Module.finBasis ℝ E) k))))
          = Geodesic.chartCoord (E := E) k v *
              ∑ p, u p * Geodesic.chartCoord (E := E) p
                (tangentCoordChange I β α x_y ((Module.finBasis ℝ E) k)) := by
      intro k
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring
    simp only [step, hAlt]
    simp
  intro p₀
  have hv2 := hlin (tangentCoordChange I α β x_y ((Module.finBasis ℝ E) p₀))
  have hcomp : tangentCoordChange I β α x_y
      (tangentCoordChange I α β x_y ((Module.finBasis ℝ E) p₀))
      = (Module.finBasis ℝ E) p₀ := by
    rw [tangentCoordChange_comp (I := I) (h := ⟨⟨hαsrc, hβsrc⟩, hαsrc⟩)]
    exact tangentCoordChange_self (I := I) hαsrc
  rw [hcomp] at hv2
  have hite : ∀ p, Geodesic.chartCoord (E := E) p ((Module.finBasis ℝ E) p₀)
      = if p₀ = p then (1 : ℝ) else 0 := fun p => chartCoord_finBasis p p₀
  simp only [hite, mul_ite, mul_one, mul_zero] at hv2
  simpa [Fintype.sum_ite_eq] using hv2

/-- **Math.** Cancellation of the (invertible) Gram matrix: a vector annihilated by
every row of `G^α` at a foot in the chart source vanishes. -/
lemma eq_zero_of_forall_sum_chartGramOnE_mul (g : RiemannianMetric I M) {α : M}
    {y' : E}
    (hy' : (extChartAt I α).symm y'
      ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (w : Fin (Module.finrank ℝ E) → ℝ)
    (h : ∀ p, ∑ q, chartGramOnE (I := I) g α p q y' * w q = 0) :
    ∀ q, w q = 0 := by
  classical
  set x' := (extChartAt I α).symm y' with hx'_def
  have hinv := chartInvGramMatrix_mul_chartGramMatrix (I := I) g α hy'
  intro q₀
  have hite : ∀ q, (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) q₀ q
      = if q₀ = q then (1 : ℝ) else 0 := fun q => Matrix.one_apply
  have hstart : w q₀
      = ∑ q, (chartInvGramMatrix (I := I) g α x' * chartGramMatrix (I := I) g α x') q₀ q
          * w q := by
    have e1 : ∀ q, (chartInvGramMatrix (I := I) g α x' * chartGramMatrix (I := I) g α x') q₀ q
        * w q = if q₀ = q then w q else 0 := by
      intro q
      rw [hinv, hite q]
      by_cases hc : q₀ = q <;> simp [hc]
    simp only [e1]
    exact (Fintype.sum_ite_eq q₀ w).symm
  rw [hstart]
  have hexpand : ∀ q, (chartInvGramMatrix (I := I) g α x' * chartGramMatrix (I := I) g α x') q₀ q
      = ∑ p, chartInvGramMatrix (I := I) g α x' q₀ p
          * chartGramMatrix (I := I) g α x' p q := fun q => Matrix.mul_apply
  simp only [hexpand, Finset.sum_mul]
  rw [Finset.sum_comm]
  have step : ∀ p : Fin (Module.finrank ℝ E),
      (∑ q, chartInvGramMatrix (I := I) g α x' q₀ p * chartGramMatrix (I := I) g α x' p q
          * w q)
        = chartInvGramMatrix (I := I) g α x' q₀ p
            * ∑ q, chartGramOnE (I := I) g α p q y' * w q := by
    intro p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [chartGramOnE_def]
    ring
  simp only [step, h]
  simp

/-- **Math.** **The transported contraction identity** — the heart of the classical
computation. Substituting the differentiated Gram change law into the
`β`-contraction identity `Σ_m G^β_{am} Γ^{β,m}_{ki} = ½(∂_k G^β_{ai} + ∂_i G^β_{ak}
− ∂_a G^β_{ki})`, the second-derivative cross-terms cancel in pairs (Schwarz
symmetry of `B` and symmetry of `G^α`), and the `∂G^α` combination reassembles by
the `α`-contraction identity:
`Σ_m G^β_{am} Γ^{β,m}_{ki} = Σ_p A^p_a Σ_q G^α_{pq}(τ y)
(Σ_{cd} Γ^{α,q}_{cd}(τ y) A^c_k A^d_i + B^q_{ki})`. -/
theorem sum_gram_mul_christoffel_transition (g : RiemannianMetric I M)
    (α β : M) {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (a k i : Fin (Module.finrank ℝ E)) :
    ∑ m, chartGramOnE (I := I) g β a m y * chartChristoffel (I := I) g β k i m y
      = ∑ p, transitionDeriv (I := I) β α p a y
          * (∑ q, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
              * ((∑ c, ∑ d,
                    chartChristoffel (I := I) g α c d q
                        (chartTransitionCC (I := I) β α y)
                      * transitionDeriv (I := I) β α c k y
                      * transitionDeriv (I := I) β α d i y)
                + transitionSndDeriv (I := I) β α q k i y)) := by
  classical
  have hfootβ : (extChartAt I β).symm y
      ∈ (trivializationAt E (TangentSpace I) β).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact extChartAt_symm_mem_chartAt_source_left (I := I) hy
  have hfootα : (extChartAt I α).symm (chartTransitionCC (I := I) β α y)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source,
      extChartAt_symm_chartTransitionCC (I := I) hy]
    exact extChartAt_symm_mem_chartAt_source_right (I := I) hy
  have key : ∀ (n : ℕ) (G : Fin n → Fin n → ℝ)
      (dG : Fin n → Fin n → Fin n → ℝ)
      (A : Fin n → Fin n → ℝ) (B : Fin n → Fin n → Fin n → ℝ)
      (Γ : Fin n → Fin n → Fin n → ℝ) (a k i : Fin n),
      (∀ p q, G p q = G q p) →
      (∀ p x z, B p x z = B p z x) →
      (∀ p c d, (∑ q, G p q * Γ c d q)
        = (1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d)) →
      (1 / 2 : ℝ) * ((∑ p, ∑ q, ((∑ c, dG c p q * A c k) * A p a * A q i
            + G p q * (B p k a * A q i + A p a * B q k i)))
        + (∑ p, ∑ q, ((∑ c, dG c p q * A c i) * A p a * A q k
            + G p q * (B p i a * A q k + A p a * B q i k)))
        - (∑ p, ∑ q, ((∑ c, dG c p q * A c a) * A p k * A q i
            + G p q * (B p a k * A q i + A p k * B q a i))))
      = ∑ p, A p a * (∑ q, G p q * ((∑ c, ∑ d, Γ c d q * A c k * A d i)
          + B q k i)) := by
    intro n G dG A B Γ a k i hG hB hΓ
    have comm3 : ∀ (F : Fin n → Fin n → Fin n → ℝ),
        (∑ x, ∑ y, ∑ z, F x y z) = ∑ z, ∑ x, ∑ y, F x y z := by
      intro F
      have h1 : (∑ x, ∑ y, ∑ z, F x y z) = ∑ x, ∑ z, ∑ y, F x y z :=
        Finset.sum_congr rfl fun x _ => by rw [Finset.sum_comm]
      rw [h1, Finset.sum_comm]
    have hT1 : (∑ p, ∑ q, ((∑ c, dG c p q * A c k) * A p a * A q i
          + G p q * (B p k a * A q i + A p a * B q k i)))
        = (∑ p, ∑ q, ∑ c, dG c p q * A c k * A p a * A q i)
          + ((∑ p, ∑ q, G p q * (B p k a * A q i))
            + ∑ p, ∑ q, G p q * (A p a * B q k i)) := by
      simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib]
    have hT2 : (∑ p, ∑ q, ((∑ c, dG c p q * A c i) * A p a * A q k
          + G p q * (B p i a * A q k + A p a * B q i k)))
        = (∑ p, ∑ q, ∑ c, dG c p q * A c i * A p a * A q k)
          + ((∑ p, ∑ q, G p q * (B p i a * A q k))
            + ∑ p, ∑ q, G p q * (A p a * B q i k)) := by
      simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib]
    have hT3 : (∑ p, ∑ q, ((∑ c, dG c p q * A c a) * A p k * A q i
          + G p q * (B p a k * A q i + A p k * B q a i)))
        = (∑ p, ∑ q, ∑ c, dG c p q * A c a * A p k * A q i)
          + ((∑ p, ∑ q, G p q * (B p a k * A q i))
            + ∑ p, ∑ q, G p q * (A p k * B q a i)) := by
      simp only [Finset.sum_mul, mul_add, Finset.sum_add_distrib]
    have hS15 : (∑ p, ∑ q, G p q * (B p k a * A q i))
        = ∑ p, ∑ q, G p q * (B p a k * A q i) :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
        rw [hB p k a]
    have hS42 : (∑ p, ∑ q, G p q * (A p a * B q i k))
        = ∑ p, ∑ q, G p q * (A p a * B q k i) :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
        rw [hB q i k]
    have hS36 : (∑ p, ∑ q, G p q * (B p i a * A q k))
        = ∑ p, ∑ q, G p q * (A p k * B q a i) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
        rw [hG q p, hB q i a]; ring
    have hD1 : (∑ p, ∑ q, ∑ c, dG c p q * A c k * A p a * A q i)
        = ∑ p, ∑ c, ∑ d, dG c p d * (A p a * A c k * A d i) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by
        ring
    have hD2 : (∑ p, ∑ q, ∑ c, dG c p q * A c i * A p a * A q k)
        = ∑ p, ∑ c, ∑ d, dG d p c * (A p a * A c k * A d i) :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ =>
        Finset.sum_congr rfl fun d _ => by ring
    have hD3 : (∑ p, ∑ q, ∑ c, dG c p q * A c a * A p k * A q i)
        = ∑ p, ∑ c, ∑ d, dG p c d * (A p a * A c k * A d i) :=
      (comm3 fun x y z => dG z x y * A z a * A x k * A y i).trans
        (Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun c _ =>
          Finset.sum_congr rfl fun d _ => by ring)
    have hE : (∑ p, ∑ c, ∑ d, ((1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d))
          * (A p a * A c k * A d i))
        = (1 / 2 : ℝ) * ((∑ p, ∑ c, ∑ d, dG c p d * (A p a * A c k * A d i))
            + (∑ p, ∑ c, ∑ d, dG d p c * (A p a * A c k * A d i))
            - ∑ p, ∑ c, ∑ d, dG p c d * (A p a * A c k * A d i)) := by
      simp only [show ∀ x y z w : ℝ, ((1 / 2 : ℝ) * (x + y - z)) * w
          = (1 / 2 : ℝ) * (x * w) + (1 / 2 : ℝ) * (y * w) - (1 / 2 : ℝ) * (z * w)
          from fun x y z w => by ring,
        Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      ring
    have h1 : ∀ p, A p a * (∑ q, G p q * ((∑ c, ∑ d, Γ c d q * A c k * A d i)
          + B q k i))
        = (∑ c, ∑ d, ((1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d))
            * (A p a * A c k * A d i))
          + ∑ q, G p q * (A p a * B q k i) := by
      intro p
      simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
      congr 1
      · refine (comm3 fun x y z =>
          A p a * (G p z * (Γ x y z * A x k * A y i))).symm.trans ?_
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        rw [← hΓ p c d, Finset.sum_mul]
        exact Finset.sum_congr rfl fun q _ => by ring
      · exact Finset.sum_congr rfl fun q _ => by ring
    have hR : (∑ p, A p a * (∑ q, G p q * ((∑ c, ∑ d, Γ c d q * A c k * A d i)
          + B q k i)))
        = (∑ p, ∑ c, ∑ d, ((1 / 2 : ℝ) * (dG c p d + dG d p c - dG p c d))
            * (A p a * A c k * A d i))
          + ∑ p, ∑ q, G p q * (A p a * B q k i) := by
      rw [Finset.sum_congr rfl fun p _ => h1 p]
      exact Finset.sum_add_distrib
    rw [hT1, hT2, hT3, hR, hE, hD1, hD2, hD3, hS15, hS36, hS42]
    ring
  rw [chartGram_christoffel_contraction (I := I) g β a k i y hfootβ,
    partialDeriv_chartGramOnE_chartTransitionCC (I := I) g α β hy k a i,
    partialDeriv_chartGramOnE_chartTransitionCC (I := I) g α β hy i a k,
    partialDeriv_chartGramOnE_chartTransitionCC (I := I) g α β hy a k i]
  exact key (Module.finrank ℝ E)
    (fun p q => chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y))
    (fun c p q => partialDeriv (E := E) c (chartGramOnE (I := I) g α p q)
      (chartTransitionCC (I := I) β α y))
    (fun p x => transitionDeriv (I := I) β α p x y)
    (fun p x z => transitionSndDeriv (I := I) β α p x z y)
    (fun c d q => chartChristoffel (I := I) g α c d q
      (chartTransitionCC (I := I) β α y))
    a k i
    (fun p q => chartGramOnE_symm (I := I) g α p q _)
    (fun p x z => transitionSndDeriv_symm (I := I) hy p x z)
    (fun p c d => chartGram_christoffel_contraction (I := I) g α p c d
      (chartTransitionCC (I := I) β α y) hfootα)

/-- **Math.** Direct expansion of the same contraction through the Gram change law:
`Σ_m G^β_{am} Γ^{β,m}_{ki} = Σ_p A^p_a Σ_q G^α_{pq}(τ y) (Σ_m A^q_m Γ^{β,m}_{ki})`. -/
theorem sum_gram_mul_christoffel_expand (g : RiemannianMetric I M)
    (α β : M) {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (a k i : Fin (Module.finrank ℝ E)) :
    ∑ m, chartGramOnE (I := I) g β a m y * chartChristoffel (I := I) g β k i m y
      = ∑ p, transitionDeriv (I := I) β α p a y
          * (∑ q, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
              * (∑ m, transitionDeriv (I := I) β α q m y
                  * chartChristoffel (I := I) g β k i m y)) := by
  classical
  have hG : ∀ m, chartGramOnE (I := I) g β a m y
      = ∑ p, ∑ q, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
          * transitionDeriv (I := I) β α p a y * transitionDeriv (I := I) β α q m y :=
    fun m => chartGramOnE_chartTransitionCC (I := I) g α β hy a m
  have hLHS : ∑ m, chartGramOnE (I := I) g β a m y * chartChristoffel (I := I) g β k i m y
      = ∑ p, ∑ q, ∑ m, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
          * transitionDeriv (I := I) β α p a y * transitionDeriv (I := I) β α q m y
          * chartChristoffel (I := I) g β k i m y := by
    calc ∑ m, chartGramOnE (I := I) g β a m y * chartChristoffel (I := I) g β k i m y
        = ∑ m, (∑ p, ∑ q, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α p a y * transitionDeriv (I := I) β α q m y)
            * chartChristoffel (I := I) g β k i m y :=
          Finset.sum_congr rfl fun m _ => by rw [hG m]
      _ = ∑ m, ∑ p, ∑ q, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α p a y * transitionDeriv (I := I) β α q m y
              * chartChristoffel (I := I) g β k i m y := by
          simp_rw [Finset.sum_mul]
      _ = ∑ p, ∑ q, ∑ m, chartGramOnE (I := I) g α p q (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α p a y * transitionDeriv (I := I) β α q m y
              * chartChristoffel (I := I) g β k i m y := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [Finset.sum_comm]
  rw [hLHS]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun m _ => ?_
  ring

/-- **Math.** **Change-of-chart law for the chart Christoffel symbols, index form.**
On the overlap, `Σ_m A^q_m Γ^{β,m}_{ki} = Σ_{cd} Γ^{α,q}_{cd}(τ y) A^c_k A^d_i
+ B^q_{ki}` — the classical inhomogeneous transformation law, with the second
derivative of the transition as inhomogeneity. -/
theorem sum_transitionDeriv_mul_chartChristoffel (g : RiemannianMetric I M)
    (α β : M) {y : E}
    (hy : y ∈ chartTransitionCCSource (I := I) (M := M) β α)
    (k i q : Fin (Module.finrank ℝ E)) :
    ∑ m, transitionDeriv (I := I) β α q m y
        * chartChristoffel (I := I) g β k i m y
      = (∑ c, ∑ d,
          chartChristoffel (I := I) g α c d q (chartTransitionCC (I := I) β α y)
            * transitionDeriv (I := I) β α c k y
            * transitionDeriv (I := I) β α d i y)
        + transitionSndDeriv (I := I) β α q k i y := by
  classical
  set W : Fin (Module.finrank ℝ E) → ℝ := fun q' =>
      (∑ m, transitionDeriv (I := I) β α q' m y * chartChristoffel (I := I) g β k i m y)
        - ((∑ c, ∑ d, chartChristoffel (I := I) g α c d q' (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α c k y * transitionDeriv (I := I) β α d i y)
            + transitionSndDeriv (I := I) β α q' k i y) with hW_def
  set U : Fin (Module.finrank ℝ E) → ℝ := fun p =>
      ∑ q', chartGramOnE (I := I) g α p q' (chartTransitionCC (I := I) β α y) * W q'
    with hU_def
  have hzero' : ∀ a, ∑ p, transitionDeriv (I := I) β α p a y * U p = 0 := by
    intro a
    have hexp := sum_gram_mul_christoffel_expand (I := I) g α β hy a k i
    have htra := sum_gram_mul_christoffel_transition (I := I) g α β hy a k i
    have key : ∑ p, transitionDeriv (I := I) β α p a y * U p
        = (∑ p, transitionDeriv (I := I) β α p a y
              * (∑ q', chartGramOnE (I := I) g α p q'
                  (chartTransitionCC (I := I) β α y)
                  * (∑ m, transitionDeriv (I := I) β α q' m y
                      * chartChristoffel (I := I) g β k i m y)))
          - (∑ p, transitionDeriv (I := I) β α p a y
              * (∑ q', chartGramOnE (I := I) g α p q'
                  (chartTransitionCC (I := I) β α y)
                  * ((∑ c, ∑ d,
                        chartChristoffel (I := I) g α c d q'
                            (chartTransitionCC (I := I) β α y)
                          * transitionDeriv (I := I) β α c k y
                          * transitionDeriv (I := I) β α d i y)
                    + transitionSndDeriv (I := I) β α q' k i y))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← mul_sub]
      congr 1
      simp only [hU_def, hW_def]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q' _ => ?_
      rw [← mul_sub]
    rw [key, ← hexp, ← htra, sub_self]
  have hzero : ∀ a, ∑ p, U p * transitionDeriv (I := I) β α p a y = 0 := by
    intro a
    rw [← hzero' a]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have hU0 : ∀ p, U p = 0 :=
    eq_zero_of_forall_sum_mul_transitionDeriv (I := I) (β := β) (α := α) hy U hzero
  have hτy : (extChartAt I α).symm (chartTransitionCC (I := I) β α y)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, extChartAt_symm_chartTransitionCC (I := I) hy]
    exact extChartAt_symm_mem_chartAt_source_right (I := I) hy
  have hW0 : ∀ q', W q' = 0 :=
    eq_zero_of_forall_sum_chartGramOnE_mul (I := I) g (α := α)
      (y' := chartTransitionCC (I := I) β α y) hτy W hU0
  have := hW0 q
  simp only [hW_def] at this
  exact sub_eq_zero.mp this

end Contraction

/-! ## Step 4: the bilinear transformation law -/

section Bilinear

variable [I.Boundaryless]

/-- **Math.** **Change-of-chart transformation law for the Christoffel contraction**
(the toll-gate identity for chart-independence of the geodesic equation, inbox
I-0100): at a common foot `x` of the charts at `β` and `α`, with
`A = tangentCoordChange I β α x` the derivative of the transition
`τ = chartTransitionCC β α` and `D²τ` its second derivative at the `β`-chart image
of `x`,

`A (Γ^β(v, w)(φ_β x)) = Γ^α(A v, A w)(φ_α x) + D²τ(v, w)`.

Equivalently: the second-order geodesic operator `γ'' + Γ(γ', γ')` transforms by
`A` alone, so the geodesic equation holds in the chart at `β` iff it holds in the
chart at `α` (chain rule). -/
theorem chartChristoffelContraction_change (g : RiemannianMetric I M)
    (α β : M) {x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source)
    (v w : E) :
    tangentCoordChange I β α x
        (Geodesic.chartChristoffelContraction (I := I) g β v w (extChartAt I β x))
      = Geodesic.chartChristoffelContraction (I := I) g α
          (tangentCoordChange I β α x v) (tangentCoordChange I β α x w)
          (extChartAt I α x)
        + fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) (extChartAt I β x)
            v w := by
  have hy : extChartAt I β x ∈ chartTransitionCCSource (I := I) (M := M) β α :=
    extChartAt_mem_chartTransitionCCSource (I := I) hxβ hxα
  have hxsymm : (extChartAt I β).symm (extChartAt I β x) = x :=
    (extChartAt I β).left_inv (by rw [extChartAt_source]; exact hxβ)
  have hτx : chartTransitionCC (I := I) β α (extChartAt I β x) = extChartAt I α x :=
    chartTransitionCC_extChartAt (I := I) hxβ
  have hAx : fderiv ℝ (chartTransitionCC (I := I) β α) (extChartAt I β x)
      = tangentCoordChange I β α x := by
    rw [fderiv_chartTransitionCC (I := I) hy, hxsymm]
  set y := extChartAt I β x with hy_def
  have sum4_swap_outer : ∀ (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
      (∑ c, ∑ d, ∑ k, ∑ i, f c d k i) = ∑ k, ∑ i, ∑ c, ∑ d, f c d k i := by
    intro f
    have key : (∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          f z.1 z.2.1 z.2.2.1 z.2.2.2)
        = ∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          f z.2.2.1 z.2.2.2 z.1 z.2.1 :=
      Fintype.sum_bijective (fun z => (z.2.2.1, z.2.2.2, z.1, z.2.1))
        (Function.Involutive.bijective (fun _ => rfl)) _ _ (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using key
  have sum3_rotate : ∀ (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      Fin (Module.finrank ℝ E) → ℝ),
      (∑ m, ∑ k, ∑ i, f m k i) = ∑ k, ∑ i, ∑ m, f m k i := by
    intro f
    have hbij : Function.Bijective
        (fun z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
            Fin (Module.finrank ℝ E) => (z.2.1, z.2.2, z.1)) :=
      (Equiv.mk (fun z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E) => (z.2.1, z.2.2, z.1))
        (fun z => (z.2.2, z.1, z.2.1)) (fun _ => rfl) (fun _ => rfl)).bijective
    have key : (∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), f z.1 z.2.1 z.2.2)
        = ∑ z : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
          Fin (Module.finrank ℝ E), f z.2.2 z.1 z.2.1 :=
      Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
    simpa only [Fintype.sum_prod_type] using key
  refine (Module.finBasis ℝ E).ext_elem fun p => ?_
  rw [← Geodesic.chartCoord_def, ← Geodesic.chartCoord_def, Geodesic.chartCoord_add]
  have hLHS : Geodesic.chartCoord (E := E) p
      (tangentCoordChange I β α x
        (Geodesic.chartChristoffelContraction (I := I) g β v w y))
      = (∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
          (∑ c, ∑ d, chartChristoffel (I := I) g α c d p (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α c k y * transitionDeriv (I := I) β α d i y))
        + ∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
            transitionSndDeriv (I := I) β α p k i y := by
    rw [← hAx, chartCoord_clm_eq_sum]
    simp only [chartCoord_chartChristoffelContraction, ← transitionDeriv_def, Finset.sum_mul]
    rw [sum3_rotate]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsub := sum_transitionDeriv_mul_chartChristoffel g α β hy k i p
    calc ∑ m, chartChristoffel (I := I) g β k i m y * Geodesic.chartCoord (E := E) k v
          * Geodesic.chartCoord (E := E) i w * transitionDeriv (I := I) β α p m y
        = Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w
            * ∑ m, transitionDeriv (I := I) β α p m y * chartChristoffel (I := I) g β k i m y := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
      _ = Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w
            * ((∑ c, ∑ d, chartChristoffel (I := I) g α c d p (chartTransitionCC (I := I) β α y)
                  * transitionDeriv (I := I) β α c k y * transitionDeriv (I := I) β α d i y)
              + transitionSndDeriv (I := I) β α p k i y) := by rw [hsub]
      _ = _ := by ring
  have hR1 : Geodesic.chartCoord (E := E) p
      (Geodesic.chartChristoffelContraction (I := I) g α
        (tangentCoordChange I β α x v) (tangentCoordChange I β α x w) (extChartAt I α x))
      = ∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
          (∑ c, ∑ d, chartChristoffel (I := I) g α c d p (chartTransitionCC (I := I) β α y)
              * transitionDeriv (I := I) β α c k y * transitionDeriv (I := I) β α d i y) := by
    rw [← hτx, chartCoord_chartChristoffelContraction]
    have hcv : ∀ c, Geodesic.chartCoord (E := E) c (tangentCoordChange I β α x v)
        = ∑ k, Geodesic.chartCoord (E := E) k v * transitionDeriv (I := I) β α c k y := by
      intro c
      rw [← hAx, chartCoord_clm_eq_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← transitionDeriv_def]
    have hcw : ∀ d, Geodesic.chartCoord (E := E) d (tangentCoordChange I β α x w)
        = ∑ i, Geodesic.chartCoord (E := E) i w * transitionDeriv (I := I) β α d i y := by
      intro d
      rw [← hAx, chartCoord_clm_eq_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← transitionDeriv_def]
    simp only [hcv, hcw, Finset.mul_sum, Finset.sum_mul]
    rw [sum4_swap_outer, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    ring
  have hR2 : Geodesic.chartCoord (E := E) p
      (((fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y) v) w)
      = ∑ k, ∑ i, Geodesic.chartCoord (E := E) k v * Geodesic.chartCoord (E := E) i w *
          transitionSndDeriv (I := I) β α p k i y := by
    have hgv : ∀ v', (((fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y) v') w)
        = ((ContinuousLinearMap.apply ℝ E w).comp
            (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y)) v' := fun v' => rfl
    rw [hgv, chartCoord_clm_eq_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hgv2 : Geodesic.chartCoord (E := E) p
        (((ContinuousLinearMap.apply ℝ E w).comp
            (fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y)) ((Module.finBasis ℝ E) k))
        = Geodesic.chartCoord (E := E) p
            (((fderiv ℝ (fderiv ℝ (chartTransitionCC (I := I) β α)) y) ((Module.finBasis ℝ E) k)) w) :=
      rfl
    rw [hgv2, chartCoord_clm_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← transitionSndDeriv_def]
    ring
  rw [hLHS, hR1, hR2]

end Bilinear

end PetersenLib

end

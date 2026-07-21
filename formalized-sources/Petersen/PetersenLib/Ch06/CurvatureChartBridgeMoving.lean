import PetersenLib.Ch03.CurvatureCoordinates
import PetersenLib.Ch06.ChartConnectionBridge
import PetersenLib.Ch06.CurvatureChartBridge

/-!
# Petersen Ch. 6, §6.1 — the coordinate ↔ abstract curvature bridge **off the diagonal**

`Ch06/CurvatureChartBridge.lean` identifies the vendored coordinate curvature with Ch. 3's
Koszul `curvatureTensorAt`, but only *at the centre of its own chart*: the chart is at `p`
and the coefficient is read at `extChartAt I p p`.  Its docstring records that this is fatal
for the Jacobi equation, whose ODE evaluates `chartCurvature g α (u t) …` at a **moving**
chart point in **one fixed** chart `α` across a whole interval.

This file removes the restriction.  Contrary to the note at
`Ch06/CurvatureChartBridge.lean:281` ("the missing ingredient is a moving-point coordinate
expansion of `curvatureTensor` that Petersen does not have"), every input to the diagonal
proof is *already* moving-point:

* `mfderiv_chartChristoffel_eq_partialDeriv` (`Ch03/CurvatureCoordinates.lean`) takes the
  chart centre `p` and the evaluation point `q ∈ (chartAt H p).source` independently;
* `exists_chartFrame_leviCivita_christoffel_nhds` (`Ch06/ChartConnectionBridge.lean`)
  delivers `∇_{Z_i}Z_j = Σ_m Γ^m_{ij}(φ_α q) • Z_m q` for **all** `q` in an open `U`, in an
  **arbitrary** chart `α`;
* `curvatureTensorAt_sum₃`, `curvatureTensorAt_apply`, `connection_local_openSet`,
  `mlieBracket_chartBasisVecFiber_eq_zero` are all general.

Diagonality entered Ch. 3 only through two *cosmetic* steps — `chartFrameField_apply_self`
and `christoffelSymbols_metric_formula`, the latter converting the abstract
`christoffelSymbolsSecondKind` into `chartChristoffel` at the centre.  Both **disappear**
here: staying inside `chartChristoffel g α · (extChartAt I α x)` throughout means the
abstract Christoffel symbols never appear, and the sign reconciliation that
`Ch06/CurvatureChartBridge.lean:206-217` needs `christoffelSymbols_metric_formula` for
becomes a bare `ring`.

## The transport

`chartCurvatureContraction2` and `chartCurvature` consume and return **raw `E`**: a reading
of a tangent vector at `x` in the chart at `α`.  Ch. 3's `curvatureTensorAt … x` consumes
and returns `TangentSpace I x`, i.e. a reading in the chart at `x`.  The dictionary between
them is `Φ := tangentCoordChange I α x x : E →L[ℝ] E`, which sends the model basis vector
`e_i` to the chart frame vector `∂_i|_x = chartBasisVecFiber α i x`
(`chartBasisVecFiber_eq_tangentCoordChange`).  On the diagonal `α = x` it is the identity
(`tangentCoordChange_self`), which is exactly how the old statement got away with omitting
it.

## Results

* `chartBasisVecFiber_eq_tangentCoordChange`, `sum_chartCoord_smul_chartBasisVecFiber` — the
  transport `Φ` and the chart-frame expansion of an arbitrary reading.
* `leviCivita_cov_cov_chartFrame_of_mem` — the moving-point double covariant derivative.
* `curvatureTensorAt_chartBasis_of_mem` — **the moving-point coordinate formula for `R`**,
  written purely in `chartChristoffel g α`.
* `chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem` — **the off-diagonal
  bridge**.
* `chartCurvature_eq_curvatureTensorAt_of_mem` — the same in vector form.
* `chartCurvature_coordChange` — **naturality of the chart curvature under a change of
  chart**, a corollary rather than (as one might expect) an input.

Reference: Petersen, *Riemannian Geometry* (GTM 171, 3rd ed.), §6.1.
-/

open Set Filter Bundle Manifold Function
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The transport `Φ = tangentCoordChange I α x x` -/

namespace Tensor

/-- **Math.** **The chart frame is the transported model basis.**  For `x` in the chart at
`α`, the frame vector `∂_i|_x` is the model basis vector `e_i` read through the tangent
coordinate change from the chart at `α` to the chart at `x`:
`∂_i|_x = tangentCoordChange I α x x e_i`.

This is the off-diagonal form of `Tensor.chartBasisVecFiber_self`, which is the case
`α = x` (where `tangentCoordChange_self` collapses the transport to the identity). -/
theorem chartBasisVecFiber_eq_tangentCoordChange (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (i : Fin (Module.finrank ℝ E)) :
    (chartBasisVecFiber (I := I) α i x : E)
      = tangentCoordChange I α x x ((Module.finBasis ℝ E) i) := by
  rw [chartBasisVecFiber,
    show (trivializationAt E (TangentSpace I) α).symm x ((Module.finBasis ℝ E) i)
        = (trivializationAt E (TangentSpace I) α).symmL ℝ x ((Module.finBasis ℝ E) i) from rfl,
    TangentBundle.symmL_trivializationAt_eq_core hx]
  rfl

end Tensor

/-- **Math.** **The chart-frame expansion of an arbitrary `α`-reading.**  A vector `v : E`,
read as a tangent vector at `x` through the chart at `α`, expands over the chart frame with
its plain model-basis coordinates: `∑_a v^a ∂_a|_x = Φ v`, where `Φ = tangentCoordChange I α x x`.

Immediate from linearity of `Φ` and `Basis.sum_repr`; the diagonal case `α = x` is
`sum_chartCoord_smul_chartBasisVecFiber_self`. -/
theorem sum_chartCoord_smul_chartBasisVecFiber (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source) (v : E) :
    ∑ a, Geodesic.chartCoord (E := E) a v • (chartBasisVecFiber (I := I) α a x : E)
      = tangentCoordChange I α x x v := by
  classical
  conv_rhs => rw [← (Module.finBasis ℝ E).sum_repr v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Tensor.chartBasisVecFiber_eq_tangentCoordChange (I := I) α hx a,
    Geodesic.chartCoord_def]

/-! ### The moving-point double covariant derivative

From here the full `Ch03/CurvaturePointwise.lean` instance bundle is in force. -/

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Eng.** The moving-point double covariant derivative of a chart frame:
`∇_{∂_i}∇_{∂_j}∂_k |_x = Σ_l (∂_i Γ^l_{jk} + Σ_s Γ^s_{jk} Γ^l_{is})(φ_α x) ∂_l |_x`,
for `x` **anywhere** in the chart at `α`.

This is `Ch03/CurvatureCoordinates.lean`'s `leviCivita_cov_cov_chartFrameField` with the
chart centre and the evaluation point decoupled.  Two changes make that possible: the
canonical frame `chartFrameField x` is replaced by the *hypothesised* frame `Z` of
`exists_chartFrame_leviCivita_christoffel_nhds` (which realises the chart frame of an
arbitrary `α` on a whole open `U`), and — crucially — the abstract
`christoffelSymbolsSecondKind` never appears, so `christoffelSymbols_metric_formula`, whose
use at `Ch03/CurvatureCoordinates.lean:502` is the *sole* source of diagonality, is not
needed. -/
private theorem leviCivita_cov_cov_chartFrame_of_mem (g : RiemannianMetric I M) {α x : M}
    (Z : Fin (Module.finrank ℝ E) → SmoothVectorField I M) {U : Set M}
    (hUopen : IsOpen U) (hxU : x ∈ U) (hUsub : U ⊆ (chartAt H α).source)
    (hZframe : ∀ a, ∀ q ∈ U, Z a q = chartBasisVecFiber (I := I) α a q)
    (hZchr : ∀ i j, ∀ q ∈ U, (g.leviCivita).cov q (Z i q) (Z j)
      = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α q) • Z m q)
    (i j k : Fin (Module.finrank ℝ E)) :
    (g.leviCivita).toAffineConnection.cov x (chartBasisVecFiber (I := I) α i x)
        ((g.leviCivita).toAffineConnection.covField (Z j) (Z k))
      = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
              (extChartAt I α x)
            + ∑ s, chartChristoffel (I := I) g α j k s (extChartAt I α x)
                * chartChristoffel (I := I) g α i s l (extChartAt I α x))
          • chartBasisVecFiber (I := I) α l x := by
  classical
  have hxsrc : x ∈ (chartAt H α).source := hUsub hxU
  -- the moving Christoffel coefficient functions, in the fixed chart at `α`
  set Γ : Fin (Module.finrank ℝ E) → M → ℝ :=
    fun m y => chartChristoffel (I := I) g α j k m (extChartAt I α y) with hΓ
  have hΓsmooth : ∀ m, ContMDiffOn I 𝓘(ℝ) ∞ (Γ m) (chartAt H α).source := by
    intro m
    have hΓE : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞ (chartChristoffel (I := I) g α j k m)
        (interior (extChartAt I α).target) :=
      (chartChristoffel_contDiffOn_interior (I := I) g α j k m).contMDiffOn
    have hsub : (chartAt H α).source ⊆
        extChartAt I α ⁻¹' (interior (extChartAt I α).target) := by
      intro q hq
      exact extChartAt_target_subset_interior_of_boundaryless (I := I) α
        ((extChartAt I α).map_source (by rwa [extChartAt_source]))
    exact hΓE.comp (contMDiffOn_extChartAt (I := I) (x := α) (n := ∞)) hsub
  choose γ hγsmooth hγev using fun m =>
    exists_contMDiff_eventuallyEq (I := I) ((chartAt H α).open_source) (hΓsmooth m) hxsrc
  -- an open neighbourhood of `x` inside `U` on which every `γ` agrees with its `Γ`
  obtain ⟨V, hV, hVopen, hxV⟩ := eventually_nhds_iff.mp
    ((eventually_all.mpr fun m => hγev m).and (hUopen.eventually_mem hxU))
  have hVU : ∀ q ∈ V, q ∈ U := fun q hq => (hV q hq).2
  have hVγ : ∀ m, ∀ q ∈ V, γ m q = Γ m q := fun m q hq => (hV q hq).1 m
  -- smoothness bookkeeping
  have hterm : ∀ m, IsSmoothVectorField (fun q => γ m q • ⇑(Z m) q) := fun m => by
    simpa using (SmoothVectorField.smul (γ m) (hγsmooth m) (Z m)).smooth
  have hW : IsSmoothVectorField (fun q => ∑ m, γ m q • ⇑(Z m) q) :=
    isSmoothVectorField_finsetSum Finset.univ _ hterm
  have hcovjk : IsSmoothVectorField
      ((g.leviCivita).toAffineConnection.covField (Z j) (Z k)) :=
    (g.leviCivita).smooth_cov (Z j).smooth (Z k).smooth
  -- `∇_{∂_j}∂_k = Σ_m γ_m • Z_m` on `V`
  have hEqOn : Set.EqOn ((g.leviCivita).toAffineConnection.covField (Z j) (Z k))
      (fun q => ∑ m, γ m q • ⇑(Z m) q) V := by
    intro q hq
    show (g.leviCivita).cov q (⇑(Z j) q) (⇑(Z k)) = _
    rw [hZchr j k q (hVU q hq)]
    exact Finset.sum_congr rfl fun m _ => by rw [hVγ m q hq]
  have hloc := connection_local_openSet (g.leviCivita).toAffineConnection
    (chartBasisVecFiber (I := I) α i x) hcovjk hW hVopen hxV hEqOn
  rw [hloc, AffineConnection.cov_finsetSum_smul_field _ x _ Finset.univ γ _
    hγsmooth (fun m => (Z m).smooth)]
  have hstep : ∀ m : Fin (Module.finrank ℝ E),
      dirTangent (γ m) (chartBasisVecFiber (I := I) α i x) • ⇑(Z m) x
        + γ m x • (g.leviCivita).toAffineConnection.cov x
            (chartBasisVecFiber (I := I) α i x) (⇑(Z m))
      = partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m)
            (extChartAt I α x) • chartBasisVecFiber (I := I) α m x
        + chartChristoffel (I := I) g α j k m (extChartAt I α x) •
            ∑ l, chartChristoffel (I := I) g α i m l (extChartAt I α x) •
              chartBasisVecFiber (I := I) α l x := by
    intro m
    have hd : dirTangent (γ m) (chartBasisVecFiber (I := I) α i x)
        = partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m)
            (extChartAt I α x) := by
      show mfderiv I 𝓘(ℝ) (γ m) x (chartBasisVecFiber (I := I) α i x) = _
      rw [(hγev m).mfderiv_eq]
      exact mfderiv_chartChristoffel_eq_partialDeriv (I := I) g α j k m i hxsrc
    have hval : γ m x = chartChristoffel (I := I) g α j k m (extChartAt I α x) :=
      (hγev m).self_of_nhds
    have hcov : (g.leviCivita).toAffineConnection.cov x
          (chartBasisVecFiber (I := I) α i x) (⇑(Z m))
        = ∑ l, chartChristoffel (I := I) g α i m l (extChartAt I α x) •
            chartBasisVecFiber (I := I) α l x := by
      have h := hZchr i m x hxU
      rw [hZframe i x hxU] at h
      rw [h]
      exact Finset.sum_congr rfl fun l _ => by rw [hZframe l x hxU]
    rw [hd, hval, hcov, hZframe m x hxU]
  rw [Finset.sum_congr rfl fun m _ => hstep m]
  calc ∑ m, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m)
            (extChartAt I α x) • chartBasisVecFiber (I := I) α m x
          + chartChristoffel (I := I) g α j k m (extChartAt I α x) •
              ∑ l, chartChristoffel (I := I) g α i m l (extChartAt I α x) •
                chartBasisVecFiber (I := I) α l x)
      = ∑ m, partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m)
            (extChartAt I α x) • chartBasisVecFiber (I := I) α m x
        + ∑ m, ∑ l, (chartChristoffel (I := I) g α j k m (extChartAt I α x) *
              chartChristoffel (I := I) g α i m l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
        rw [Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun l _ => smul_smul ..
    _ = ∑ l, partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
            (extChartAt I α x) • chartBasisVecFiber (I := I) α l x
        + ∑ l, (∑ s, chartChristoffel (I := I) g α j k s (extChartAt I α x) *
              chartChristoffel (I := I) g α i s l (extChartAt I α x)) •
            chartBasisVecFiber (I := I) α l x := by
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => (Finset.sum_smul).symm
    _ = ∑ l, (partialDeriv (E := E) i (chartChristoffel (I := I) g α j k l)
            (extChartAt I α x)
          + ∑ s, chartChristoffel (I := I) g α j k s (extChartAt I α x) *
              chartChristoffel (I := I) g α i s l (extChartAt I α x))
          • chartBasisVecFiber (I := I) α l x := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => (add_smul ..).symm

/-! ### The moving-point coordinate formula for `R` -/

/-- **Math.** **The curvature tensor in local coordinates, at a moving point** (Petersen
§3.1.6 off the diagonal).  For `x` **anywhere** in the chart at `α`, Ch. 3's abstract
curvature tensor applied to the chart frame of `α` at `x` is the *negative* of do Carmo's
coordinate curvature coefficient, read at the chart image of `x`:
`R(∂_i, ∂_j)∂_k |_x = Σ_l (− Rˡ_{ijk}(φ_α x)) ∂_l |_x`.

This is the off-diagonal `curvatureTensorAt_chartBasis_eq_neg_chartCurvatureCoef`
(`Ch06/CurvatureChartBridge.lean`), and it is *cheaper* than the diagonal one: because both
sides are already written in `chartChristoffel g α`, the sign reconciliation is a bare
`ring`, with no appeal to `christoffelSymbols_metric_formula` — which is precisely the step
that pinned the old statement to the chart centre. -/
theorem curvatureTensorAt_chartBasis_of_mem (g : RiemannianMetric I M) {α x : M}
    (hx : x ∈ (chartAt H α).source) (i j k : Fin (Module.finrank ℝ E)) :
    curvatureTensorAt (g.leviCivita).toAffineConnection x
        (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)
        (chartBasisVecFiber (I := I) α k x)
      = ∑ l, (-(Jacobi.chartCurvatureCoef (I := I) g α i j k l (extChartAt I α x)))
          • chartBasisVecFiber (I := I) α l x := by
  classical
  obtain ⟨Z, U, hUopen, hxU, hUsub, hZframe, hZchr⟩ :=
    exists_chartFrame_leviCivita_christoffel_nhds (I := I) g hx
  have hgerm : ∀ a, (⇑(Z a) : Π q : M, TangentSpace I q)
      =ᶠ[nhds x] fun q => chartBasisVecFiber (I := I) α a q := fun a =>
    eventually_of_mem (hUopen.mem_nhds hxU) fun q hq => hZframe a q hq
  -- pass from the pointwise tensor to the global frame fields
  have hA : curvatureTensorAt (g.leviCivita).toAffineConnection x
      (chartBasisVecFiber (I := I) α i x) (chartBasisVecFiber (I := I) α j x)
      (chartBasisVecFiber (I := I) α k x)
      = curvatureTensor (g.leviCivita).toAffineConnection (⇑(Z i)) (⇑(Z j)) (⇑(Z k)) x := by
    rw [← hZframe i x hxU, ← hZframe j x hxU, ← hZframe k x hxU]
    exact curvatureTensorAt_apply _ (Z i).smooth (Z j).smooth (Z k).smooth x
  rw [hA, curvatureTensor_apply]
  -- the bracket term vanishes: `[∂_i, ∂_j]|_x = 0`
  have hbr0 : lieDerivativeVectorField I (⇑(Z i)) (⇑(Z j)) x = 0 := by
    rw [lieDerivativeVectorField_eq_mlieBracket,
      Filter.EventuallyEq.mlieBracket_vectorField_eq (hgerm i) (hgerm j)]
    exact mlieBracket_chartBasisVecFiber_eq_zero (I := I) α i j hx
  rw [hbr0, AffineConnection.cov_zero_direction, sub_zero, hZframe i x hxU, hZframe j x hxU,
    leviCivita_cov_cov_chartFrame_of_mem (I := I) g Z hUopen hxU hUsub hZframe hZchr i j k,
    leviCivita_cov_cov_chartFrame_of_mem (I := I) g Z hUopen hxU hUsub hZframe hZchr j i k,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← sub_smul]
  congr 1
  simp only [Jacobi.chartCurvatureCoef]
  rw [Finset.sum_sub_distrib]
  ring

/-! ### The off-diagonal bridge -/

/-- **Math.** **The bridge, off the diagonal** (Petersen §6.1 / do Carmo Ch. 4).  For `x`
**anywhere** in the chart at `α`, the vendored coordinate curvature contraction of three
`α`-readings `X, Y, Z : E`, evaluated at the chart image `φ_α x`, transports to the
*negative* of Ch. 3's abstract curvature tensor at `x` applied to the transported readings:
`Φ(R_chart(X, Y)Z) = − R(ΦX, ΦY)ΦZ`, with `Φ = tangentCoordChange I α x x`.

The transport `Φ` is unavoidable and is what the diagonal statement
`chartCurvatureContraction2_eq_neg_curvatureTensorAt` silently omits: there `α = x` and
`tangentCoordChange_self` makes `Φ = id`.  Since `chartCurvatureContraction2` returns a raw
`E` read in the chart at `α`, while `curvatureTensorAt … x` returns a `TangentSpace I x`
read in the chart at `x`, the two live in different copies of `E` unless `α = x`.

Proof: expand `ΦX, ΦY, ΦZ` over the chart frame at `x`
(`sum_chartCoord_smul_chartBasisVecFiber`), apply trilinearity (`curvatureTensorAt_sum₃`),
and compare coefficients with `curvatureTensorAt_chartBasis_of_mem`. -/
theorem chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem (g : RiemannianMetric I M)
    {α x : M} (hx : x ∈ (chartAt H α).source) (X Y Z : E) :
    (tangentCoordChange I α x x
        (Jacobi.chartCurvatureContraction2 (I := I) g α X Y Z (extChartAt I α x)) :
          TangentSpace I x)
      = -curvatureTensorAt (g.leviCivita).toAffineConnection x
          (tangentCoordChange I α x x X) (tangentCoordChange I α x x Y)
          (tangentCoordChange I α x x Z) := by
  classical
  -- transport the coordinate side onto the chart frame at `x`
  have hLHS : (tangentCoordChange I α x x
      (Jacobi.chartCurvatureContraction2 (I := I) g α X Y Z (extChartAt I α x)) : E)
      = ∑ l, (∑ i, ∑ j, ∑ k, Jacobi.chartCurvatureCoef (I := I) g α i j k l
              (extChartAt I α x)
            * Geodesic.chartCoord (E := E) i X * Geodesic.chartCoord (E := E) j Y
            * Geodesic.chartCoord (E := E) k Z)
          • (chartBasisVecFiber (I := I) α l x : E) := by
    rw [Jacobi.chartCurvatureContraction2, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, ← Tensor.chartBasisVecFiber_eq_tangentCoordChange (I := I) α hx l]
  rw [hLHS]
  conv_rhs => rw [← sum_chartCoord_smul_chartBasisVecFiber (I := I) α hx X,
    ← sum_chartCoord_smul_chartBasisVecFiber (I := I) α hx Y,
    ← sum_chartCoord_smul_chartBasisVecFiber (I := I) α hx Z]
  rw [curvatureTensorAt_sum₃]
  simp only [curvatureTensorAt_chartBasis_of_mem (I := I) g hx, Finset.smul_sum, smul_smul,
    Finset.sum_smul, ← Finset.sum_neg_distrib, ← neg_smul]
  -- both sides are the same fourfold sum; move the basis index `l` from outermost to
  -- innermost to match
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 1
  ring

/-- **Eng.** **The off-diagonal bridge, read the other way.**  Given honest tangent vectors
`X, Y, Z : TangentSpace I x`, reading them into the chart at `α` and contracting the
coordinate curvature at `φ_α x` gives the `α`-reading of `− R(X, Y)Z`:
`R_chart(τX, τY)τZ = τ(− R(X, Y)Z)`, with `τ = tangentCoordChange I x α x`.

The user-facing form of `chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem`, from
which it follows by feeding it `τX, τY, τZ` and collapsing `Φ ∘ τ = id` with the cocycle
law.  Specialises to `chartCurvatureContraction2_eq_neg_curvatureTensorAt` at `α = x`. -/
theorem chartCurvatureContraction2_tangentCoordChange_of_mem (g : RiemannianMetric I M)
    {α x : M} (hx : x ∈ (chartAt H α).source) (X Y Z : TangentSpace I x) :
    Jacobi.chartCurvatureContraction2 (I := I) g α
        (tangentCoordChange I x α x X) (tangentCoordChange I x α x Y)
        (tangentCoordChange I x α x Z) (extChartAt I α x)
      = tangentCoordChange I x α x
          (-curvatureTensorAt (g.leviCivita).toAffineConnection x X Y Z) := by
  have hα : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hself : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
  -- `tangentCoordChange I α x x` inverts `tangentCoordChange I x α x`
  have hround : ∀ u : E, tangentCoordChange I α x x (tangentCoordChange I x α x u) = u := by
    intro u
    rw [tangentCoordChange_comp (I := I) (w := x) (x := α) (y := x) (z := x)
      ⟨⟨hself, hα⟩, hself⟩]
    exact tangentCoordChange_self (I := I) (x := x) (z := x) hself
  have hleft : ∀ u : E, tangentCoordChange I x α x (tangentCoordChange I α x x u) = u := by
    intro u
    rw [tangentCoordChange_comp (I := I) (w := α) (x := x) (y := α) (z := x)
      ⟨⟨hα, hself⟩, hα⟩]
    exact tangentCoordChange_self (I := I) (x := α) (z := x) hα
  have key := chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem (I := I) g hx
    (tangentCoordChange I x α x X) (tangentCoordChange I x α x Y)
    (tangentCoordChange I x α x Z)
  rw [hround, hround, hround] at key
  have h := congrArg (tangentCoordChange I x α x) key
  rwa [hleft] at h

/-! ### The bridge in vector form, and naturality -/

/-- **Math.** **The bridge in vector form, off the diagonal** (Petersen §6.1 /
Morgan–Tian §1.2).  For `x` **anywhere** in the chart at `α`, the vendored chart curvature
*vector* `chartCurvature` transports to Ch. 3's abstract `curvatureTensorAt` at `x` — with
no sign: `Φ(ℛ_chart(A, B)C) = R(ΦA, ΦB)ΦC`, with `Φ = tangentCoordChange I α x x`.

Two sign flips cancel, exactly as in the diagonal
`chartCurvature_eq_curvatureTensorAt`: the do Carmo↔Petersen convention minus supplied by
`chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem`, against the **slot swap** in
`Jacobi.chartCurvatureContraction2_eq_chartCurvature` (which reads
`chartCurvatureContraction2 X Y Z = chartCurvature Y X Z`), undone by the *pointwise*
`curvatureTensorAt_antisymm_first`.  The contraction lemma is already general in its
evaluation point `y`, so nothing but the diagonal bridge had to be generalised.

**This is the statement Jacobi fields need.**  `Jacobi.IsJacobiFieldOn`'s ODE evaluates
`chartCurvature g α (u t) …` at the moving chart point `u t = φ_α (c t)` in *one fixed*
chart `α` across a whole interval; this identity fires at every such `t`. -/
theorem chartCurvature_eq_curvatureTensorAt_of_mem (g : RiemannianMetric I M) {α x : M}
    (hx : x ∈ (chartAt H α).source) (A B C : E) :
    (tangentCoordChange I α x x
        (Jacobi.chartCurvature (I := I) g α (extChartAt I α x) A B C) : TangentSpace I x)
      = curvatureTensorAt (g.leviCivita).toAffineConnection x
          (tangentCoordChange I α x x A) (tangentCoordChange I α x x B)
          (tangentCoordChange I α x x C) := by
  have hy : (extChartAt I α x) ∈ interior (extChartAt I α).target :=
    extChartAt_target_subset_interior_of_boundaryless (I := I) α
      ((extChartAt I α).map_source (by rwa [extChartAt_source]))
  have h1 := Jacobi.chartCurvatureContraction2_eq_chartCurvature (I := I) g α B A C hy
  have h2 := chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem (I := I) g hx B A C
  rw [← h1, h2, curvatureTensorAt_antisymm_first, neg_neg]

/-- **Math.** **Naturality of the chart curvature under a change of chart** (do Carmo
`DoCarmoLib/Riemannian/Jacobi/JacobiChartTransfer.lean`).  The chart curvature vector is a
genuine `(1,3)`-tensor: for `x` in the sources of **both** charts `α` and `β`,

`ℛ_β(τ v, τ w)τ z = τ (ℛ_α(v, w)z)`,  `τ = tangentCoordChange I α β x`,

both sides read at the respective chart images of `x`.

This is a **corollary** of the off-diagonal bridge, not an input to it: both chart
readings are pushed to the *same* abstract `curvatureTensorAt … x` by
`chartCurvature_eq_curvatureTensorAt_of_mem`, and the cocycle law
`tangentCoordChange_comp` identifies the two transports.  In particular it needs no
positive-definiteness of the chart Gram form and no differentiation of the Christoffel
transformation law — the two routes do Carmo's proof and the Christoffel change law
respectively suggest. -/
theorem chartCurvature_coordChange (g : RiemannianMetric I M) {α β x : M}
    (hxα : x ∈ (chartAt H α).source) (hxβ : x ∈ (chartAt H β).source) (v w z : E) :
    Jacobi.chartCurvature (I := I) g β (extChartAt I β x)
        (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
        (tangentCoordChange I α β x z)
      = tangentCoordChange I α β x
          (Jacobi.chartCurvature (I := I) g α (extChartAt I α x) v w z) := by
  have hα : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hβ : x ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hself : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
  -- the cocycle law: transporting `α → β → x` is transporting `α → x`
  have hcomp : ∀ u : E,
      tangentCoordChange I β x x (tangentCoordChange I α β x u)
        = tangentCoordChange I α x x u := fun u =>
    tangentCoordChange_comp (I := I) (w := α) (x := β) (y := x) (z := x) ⟨⟨hα, hβ⟩, hself⟩
  -- `tangentCoordChange I β x x` is injective: `tangentCoordChange I x β x` inverts it
  have hleft : ∀ u : E, tangentCoordChange I x β x (tangentCoordChange I β x x u) = u := by
    intro u
    rw [tangentCoordChange_comp (I := I) (w := β) (x := x) (y := β) (z := x)
      ⟨⟨hβ, hself⟩, hβ⟩]
    exact tangentCoordChange_self (I := I) (x := β) (z := x) hβ
  -- both readings push forward to the *same* abstract curvature at `x`
  have key : tangentCoordChange I β x x
        (Jacobi.chartCurvature (I := I) g β (extChartAt I β x)
          (tangentCoordChange I α β x v) (tangentCoordChange I α β x w)
          (tangentCoordChange I α β x z))
      = tangentCoordChange I β x x (tangentCoordChange I α β x
          (Jacobi.chartCurvature (I := I) g α (extChartAt I α x) v w z)) := by
    rw [chartCurvature_eq_curvatureTensorAt_of_mem (I := I) g hxβ]
    simp only [hcomp]
    rw [chartCurvature_eq_curvatureTensorAt_of_mem (I := I) g hxα]
  have h := congrArg (tangentCoordChange I x β x) key
  rwa [hleft, hleft] at h

/-! ### Consistency with the diagonal bridge -/

/-- **Eng.** *Consistency check* — the off-diagonal bridge **subsumes** the diagonal one.
Specialising `α := p` collapses the transport to the identity (`tangentCoordChange_self`)
and reproduces `chartCurvatureContraction2_eq_neg_curvatureTensorAt` verbatim.  This is the
machine-checked witness that the placement of `tangentCoordChange` above is the right one. -/
example (g : RiemannianMetric I M) (p : M) (X Y Z : TangentSpace I p) :
    Jacobi.chartCurvatureContraction2 (I := I) g p X Y Z (extChartAt I p p)
      = -curvatureTensorAt (g.leviCivita).toAffineConnection p X Y Z := by
  have hid : ∀ v : E, tangentCoordChange I p p p v = v := fun v =>
    tangentCoordChange_self (I := I) (x := p) (z := p) (mem_extChartAt_source (I := I) p)
  have h := chartCurvatureContraction2_eq_neg_curvatureTensorAt_of_mem (I := I) g
    (mem_chart_source H p) X Y Z
  simp only [hid] at h
  exact h

/-- **Eng.** *Consistency check* — the vector-form off-diagonal bridge subsumes
`chartCurvature_eq_curvatureTensorAt`. -/
example (g : RiemannianMetric I M) (p : M) (A B C : TangentSpace I p) :
    Jacobi.chartCurvature (I := I) g p (extChartAt I p p) A B C
      = curvatureTensorAt (g.leviCivita).toAffineConnection p A B C := by
  have hid : ∀ v : E, tangentCoordChange I p p p v = v := fun v =>
    tangentCoordChange_self (I := I) (x := p) (z := p) (mem_extChartAt_source (I := I) p)
  have h := chartCurvature_eq_curvatureTensorAt_of_mem (I := I) g (mem_chart_source H p) A B C
  simp only [hid] at h
  exact h

end PetersenLib

end

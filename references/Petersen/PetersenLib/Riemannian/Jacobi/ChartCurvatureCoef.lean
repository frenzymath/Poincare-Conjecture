/- Petersen's own Riemannian infrastructure.
   Originally derived from the DoCarmo project's `DoCarmoLib/Riemannian/Jacobi/ChartCurvatureContraction.lean`; it is maintained
   here independently and is engineering support, not a blueprint node. -/
import PetersenLib.Riemannian.Connection.ChartChristoffelSmooth

/-!
# The coordinate curvature coefficient `Rˡ_{ijk}` (do Carmo Ch. 5, `def:dc-ch5-2-1`)

The coefficient of the curvature tensor read in a fixed chart at `α`,

  `Rˡ_{ijk} = ∂ⱼΓˡ_{ik} − ∂ᵢΓˡ_{jk} + Σₛ(Γˢ_{ik}Γˡ_{js} − Γˢ_{jk}Γˡ_{is})`,

so that `R(∂ᵢ,∂ⱼ)∂ₖ = Σₗ Rˡ_{ijk} ∂ₗ`. This is the coordinate side of the curvature
tensor; `PetersenLib.chartCurvatureContraction2_eq_curvatureTensorAt`
(`Ch06/CurvatureChartBridge.lean`) identifies its contraction with Ch. 3's abstract
`curvatureTensorAt`, and `PetersenLib.Jacobi.surface_covariant_commutator`
(`Riemannian/Jacobi/SurfaceCurvatureCommutation.lean`) is the commutation identity
it appears in — Petersen's Lemma 6.1.2.

**Sign convention.** This is do Carmo's `R(X,Y) = ∇_Y∇_X − ∇_X∇_Y + ∇_{[X,Y]}`, which is
the *negative* of Petersen's `R(X,Y) = ∇_X∇_Y − ∇_Y∇_X − ∇_{[X,Y]}` (Ch. 3's
`curvatureTensor`). The two conventions differ by the swap `(i,j) ↦ (j,i)`, absorbed in
the bridge by `curvatureTensorAt_antisymm_first`.
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib.Jacobi

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

end PetersenLib.Jacobi

end

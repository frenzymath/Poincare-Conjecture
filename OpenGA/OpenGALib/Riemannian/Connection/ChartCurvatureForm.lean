import OpenGALib.Riemannian.Connection.CurvaturePointwise

/-!
# The pointwise `(0,4)` curvature form in chart coordinates

Combining the pointwise `(0,4)` curvature form `curvatureFormAt`
(`CurvaturePointwise`) with the chart-coordinate expansion of the curvature
operator (`leviCivita_curvature_chartFrame_expansion`, `ChartCurvature`), this
file computes `⟨R(∂ᵢ,∂ⱼ)∂ₖ, ∂ₗ⟩_g` in the chart frame `∂ₐ = chartBasisVecFiber p a`
of the Levi-Civita connection as the coordinate curvature coefficient contracted
with the chart Gram matrix:

`⟨R(∂ᵢ,∂ⱼ)∂ₖ, ∂ₗ⟩_g = Σₘ R^m_{ijk} · G_{ml}`,

`R^m_{ijk} = ∂ⱼΓ^m_{ik} − ∂ᵢΓ^m_{jk} + Σₛ(Γ^s_{ik}Γ^m_{js} − Γ^s_{jk}Γ^m_{is})`
the coordinate coefficient (do Carmo Ch. 8 §3, eq. (2)) and `G_{ml} = ⟨∂ₘ,∂ₗ⟩_g`
the chart Gram matrix. This is the `(0,4)`-lowered form of
`leviCivita_curvature_chartFrame_expansion`, feeding the constant-curvature
computation of `prop:dc-ch8-3-const-curv` through the frame identification
`eq_kronecker_iff_const`/`ext_basis`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8 §3.
-/

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff Matrix RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Eng.** Left additivity of the metric inner product over a finite sum. -/
private theorem metricInner_finsetSum_left (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (v : ι → TangentSpace I p) (w : TangentSpace I p) :
    g.metricInner p (∑ i ∈ s, v i) w = ∑ i ∈ s, g.metricInner p (v i) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, RiemannianMetric.metricInner_add_left, ih]

/-- **Math.** do Carmo Ch. 8 §3 (curvature `(0,4)` form in the chart frame). In
the coordinate frame `∂ₐ = chartBasisVecFiber p a` at `p`, the pointwise `(0,4)`
curvature form of the Levi-Civita connection is the coordinate curvature
coefficient `R^m_{ijk}` contracted with the chart Gram matrix `G_{ml} = ⟨∂ₘ,∂ₗ⟩_g`:

`⟨R(∂ᵢ,∂ⱼ)∂ₖ, ∂ₗ⟩_g = Σₘ (∂ⱼΓ^m_{ik} − ∂ᵢΓ^m_{jk}
    + Σₛ(Γ^s_{ik}Γ^m_{js} − Γ^s_{jk}Γ^m_{is})) · G_{ml}`.

This is the metric-lowered avatar of `leviCivita_curvature_chartFrame_expansion`,
obtained by pairing the frame expansion of `R(∂ᵢ,∂ⱼ)∂ₖ` against `∂ₗ`. -/
theorem leviCivita_curvatureFormAt_chartFrame (g : RiemannianMetric I M) (p : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    g.leviCivitaConnection.curvatureFormAt g p
        (chartBasisVecFiber (I := I) p i p) (chartBasisVecFiber (I := I) p j p)
        (chartBasisVecFiber (I := I) p k p) (chartBasisVecFiber (I := I) p l p)
      = ∑ m, (partialDeriv (E := E) j (chartChristoffel (I := I) g p i k m)
              (extChartAt I p p)
            - partialDeriv (E := E) i (chartChristoffel (I := I) g p j k m)
              (extChartAt I p p)
            + ∑ s, (chartChristoffel (I := I) g p i k s (extChartAt I p p)
                  * chartChristoffel (I := I) g p j s m (extChartAt I p p)
                - chartChristoffel (I := I) g p j k s (extChartAt I p p)
                  * chartChristoffel (I := I) g p i s m (extChartAt I p p)))
          * g.metricInner p (chartBasisVecFiber (I := I) p m p)
              (chartBasisVecFiber (I := I) p l p) := by
  rw [g.leviCivitaConnection.curvatureFormAt_eq g p
      (chartFrameField_apply_self (I := I) p i) (chartFrameField_apply_self (I := I) p j)
      (chartFrameField_apply_self (I := I) p k) (chartFrameField_apply_self (I := I) p l)]
  show g.metricInner p
      ((g.leviCivitaConnection.curvature (chartFrameField (I := I) p i)
        (chartFrameField (I := I) p j) (chartFrameField (I := I) p k)) p)
      ((chartFrameField (I := I) p l) p) = _
  rw [leviCivita_curvature_chartFrame_expansion, chartFrameField_apply_self]
  simp only [metricInner_finsetSum_left, RiemannianMetric.metricInner_smul_left]

end Riemannian

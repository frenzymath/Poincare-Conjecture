import PetersenLib.Ch02.CovariantDerivative
import PetersenLib.Vendored.OpenGA.TensorBundle.SmoothOrthoFrame.ChartBasis

/-!
# Petersen Ch. 2 — Local frame decomposition of a vector field

Reusable infrastructure for §2.2/§2.5: any smooth vector field `Z` decomposes,
on the base set of the tangent-bundle trivialization at `α`, as
`Z = Σ_i Z^i · ∂_i` in the chart frame `∂_i = chartBasisVecFiber α i`, with
**smooth** coefficient functions `Z^i = chartVectorFieldCoeff α Z i`.  The
coefficient is read off through the fixed model-space basis after trivializing,
`Z^i(y) = (finBasis ℝ E).coord i ((triv ⟨y, Z y⟩).2)`, which on the base set
equals the frame-basis coordinate `(chartBasisFamily α hy).repr (Z y) i` and is
smooth because it is a continuous-linear functional of the (smooth) trivialized
section component.

This is the frame-decomposition machinery underlying the along-a-curve locality
of the connection (Lem. 2.2.4) and several §2.5 exercises (normal frames,
incompressible fields, contraction identities).
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The `i`-th coordinate of a vector field `Z` in the chart frame at
`α`, read through the fixed model-space basis after trivializing:
`Z^i(y) = (finBasis ℝ E)ᵢ((triv ⟨y, Z y⟩).2)`.  On the base set of the
trivialization it agrees with the chart-frame coordinate
(`chartVectorFieldCoeff_eq_repr`). -/
def chartVectorFieldCoeff (α : M) (Z : Π x : M, TangentSpace I x)
    (i : Fin (Module.finrank ℝ E)) : M → ℝ :=
  fun y => (Module.finBasis ℝ E).coord i
    ((trivializationAt E (TangentSpace I) α ⟨y, Z y⟩).2)

/-- **Math.** On the base set, the model-space coordinate `chartVectorFieldCoeff`
equals the chart-frame-basis coordinate `(chartBasisFamily α hy).repr (Z y) i`. -/
theorem chartVectorFieldCoeff_eq_repr (α : M) (Z : Π x : M, TangentSpace I x)
    {y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i : Fin (Module.finrank ℝ E)) :
    chartVectorFieldCoeff α Z i y = (chartBasisFamily (I := I) α hy).repr (Z y) i := by
  set triv := trivializationAt E (TangentSpace I) α
  have hφ : (triv ⟨y, Z y⟩).2 = triv.continuousLinearEquivAt ℝ y hy (Z y) :=
    congrArg Prod.snd (triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy (Z y))
  show (Module.finBasis ℝ E).coord i ((triv ⟨y, Z y⟩).2) = _
  rw [hφ]
  unfold chartBasisFamily
  rw [Module.Basis.map_repr]
  rfl

/-- **Math.** The chart-frame coordinates of a **smooth** vector field are smooth
on the base set of the trivialization: `Z^i` is a continuous-linear functional of
the trivialized section component `(triv ⟨y, Z y⟩).2`, which is smooth on the
base set (`Trivialization.contMDiffOn_section_baseSet_iff`). -/
theorem chartVectorFieldCoeff_contMDiffOn (α : M) {Z : Π x : M, TangentSpace I x}
    (hZ : IsSmoothVectorField Z) (i : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞ (chartVectorFieldCoeff α Z i)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  set triv := trivializationAt E (TangentSpace I) α
  have hsnd : ContMDiffOn I 𝓘(ℝ, E) ∞
      (fun y => (triv ⟨y, Z y⟩).2) triv.baseSet := by
    have hsec : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y => (TotalSpace.mk' E y (Z y) : TangentBundle I M)) triv.baseSet :=
      hZ.contMDiffOn
    exact (triv.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞) (s := Z)).mp hsec
  have hL : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)) :=
    (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord i)).contMDiff
  exact hL.comp_contMDiffOn hsnd

/-- **Math.** **Frame decomposition** of a vector field: on the base set of the
trivialization at `α`, `Z = Σ_i Z^i · ∂_i` in the chart frame. -/
theorem vectorField_eq_sum_chartCoeff (α : M) (Z : Π x : M, TangentSpace I x)
    {y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    Z y = ∑ i, chartVectorFieldCoeff α Z i y • chartBasisVecFiber (I := I) α i y := by
  conv_lhs => rw [← (chartBasisFamily (I := I) α hy).sum_repr (Z y)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [chartBasisFamily_apply, chartVectorFieldCoeff_eq_repr]

end PetersenLib

end

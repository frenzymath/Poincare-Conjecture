import PetersenLib.Ch05.ExponentialMap
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Petersen Ch. 5, §5.5 — Riemannian normal coordinates

Blueprint node `rem:pet-ch5-riemannian-normal-coordinates` (Petersen §5.5).
Identifying `T_pM` with the model space and using that `exp_p` is a diffeomorphism
near `0` (Prop. 5.5.1(1), `expMap_localDiffeomorphism`) produces the
**exponential / Riemannian normal coordinate** chart at `p`: the local inverse of
`exp_p`, unique up to the choice of the linear identification `T_pM ≅ ℝⁿ`.

## Blueprint node

* `rem:pet-ch5-riemannian-normal-coordinates` — `riemannianNormalCoordinates`:
  the local inverse of the chart reading of `exp_p` is a local homeomorphism from a
  neighbourhood of `0` onto a neighbourhood of the chart value at `p`, and its
  inverse — the normal coordinate chart — recovers the tangent vector `w` from
  `exp_p(w)` for `w` near `0`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff ENNReal

namespace PetersenLib

open PetersenLib.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** Petersen Ch. 5 (`rem:pet-ch5-riemannian-normal-coordinates`, §5.5).
Identifying `T_pM` with the model normed space `E` and using that `exp_p` is a
diffeomorphism near `0` (Prop. 5.5.1(1), `expMap_localDiffeomorphism`) yields
**Riemannian normal coordinates** at `p`.

Concretely there is a local homeomorphism `φ` (an `OpenPartialHomeomorph`) of `E`
onto `E` with `0` in its source such that:

* on its source, `φ` is the chart reading `w ↦ φ_p(exp_p w)` of the exponential map
  (so `φ` is a diffeomorphism from a neighbourhood of `0 ∈ T_pM` onto a
  neighbourhood of the chart value `φ_p(p)`);
* its inverse `φ.symm` — the **normal coordinate chart** — inverts `exp_p`: for `w`
  near `0`, `φ.symm (φ_p (exp_p w)) = w`, i.e. the normal coordinate of the point
  `exp_p(w)` is exactly the tangent vector `w`.

The chart is unique up to the choice of linear identification `T_pM ≅ ℝⁿ`; here `E`
is already the model space, so no separate identification has to be chosen. -/
theorem riemannianNormalCoordinates (g : RiemannianMetric I M) (p : M) :
    ∃ φ : OpenPartialHomeomorph E E,
      (0 : E) ∈ φ.source ∧
      (∀ w : E, w ∈ φ.source →
          φ w = extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) ∧
      (∀ᶠ w : E in 𝓝 0,
          φ.symm (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) := by
  obtain ⟨_ρ, _hρ, _hdom, _hinj, hstrict, _hmap⟩ := expMap_localDiffeomorphism (I := I) g p
  -- The strict derivative is the identity, an invertible continuous linear map.
  have hstrict' : HasStrictFDerivAt
      (fun w : E => extChartAt I p (expMap (I := I) g p (w : TangentSpace I p)))
      ((ContinuousLinearEquiv.refl ℝ E : E ≃L[ℝ] E) : E →L[ℝ] E) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hstrict
  refine ⟨hstrict'.toOpenPartialHomeomorph _, hstrict'.mem_toOpenPartialHomeomorph_source,
    fun w _ => rfl, ?_⟩
  filter_upwards [hstrict'.eventually_left_inverse] with w hw
  rw [HasStrictFDerivAt.localInverse_def] at hw
  exact hw

end PetersenLib

end

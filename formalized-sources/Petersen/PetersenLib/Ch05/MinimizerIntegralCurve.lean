import PetersenLib.Ch05.DistanceRigidity
import PetersenLib.Ch03.CurvatureCoordinates

/-!
# Petersen Ch. 5, §5.3 — a minimiser is a reparametrised integral curve of `∇r`

`rem:pet-ch5-minimizer-is-reparametrized-integral-curve`.

`Ch05/DistanceRigidity.lean` already proves the remark
(`distanceFunction_minimizer_eq_integralCurve_comp`), but carries an *extra*
hypothesis `hgrad`: that `∇r` is a `C¹` section of `TM` over `U`.  This file
**discharges that hypothesis**, so the remark holds under exactly the book's
hypotheses (`IsDistanceFunction g U r` and nothing more).

The point is that `gradient g r x = ♯_g (mfderiv I 𝓘(ℝ) r x)` is a *local*
construction, whereas the on-disk `gradient_isSmoothVectorField` demands `r`
smooth on all of `M`.  Bump-extending `r` near a point `p ∈ U` to a globally
smooth `F` (`exists_contMDiff_eventuallyEq`) and using that `F =ᶠ[𝓝 p] r`
forces `F =ᶠ[𝓝 y] r` for all `y` near `p`
(`Filter.EventuallyEq.eventuallyEq_nhds`), hence `mfderiv F y = mfderiv r y`
(`Filter.EventuallyEq.mfderiv_eq`) and so `∇F = ∇r` near `p` — giving
smoothness of `∇r` at `p` by transport along an eventual equality.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **Eng.** Smoothness of `∇r` is *local in `r`*: if `r` is smooth on an open
`U` then `∇r` is a smooth section of `TM` at each `p ∈ U`.  Bump-extend `r` to a
globally smooth `F` near `p`, apply the global `gradient_isSmoothVectorField`,
and transport back along `∇F = ∇r` near `p` (locality of `mfderiv`). -/
theorem gradient_contMDiffAt_of_contMDiffOn (g : RiemannianMetric I M) {r : M → ℝ}
    {U : Set M} (hU : IsOpen U) (hr : ContMDiffOn I 𝓘(ℝ) ∞ r U) {p : M} (hp : p ∈ U) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ (⟨x, gradient g r x⟩ : TangentBundle I M)) p := by
  haveI : LocallyCompactSpace H := I.locallyCompactSpace
  haveI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  -- bump-extend `r` to a globally smooth `F` agreeing with `r` near `p`
  obtain ⟨F, hF, hFeq⟩ := exists_contMDiff_eventuallyEq (I := I) hU hr hp
  -- the global gradient is a smooth section
  have hgF : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ (⟨x, gradient g F x⟩ : TangentBundle I M)) p :=
    gradient_isSmoothVectorField g hF p
  -- `gradient` is local: `F = r` near every point near `p`, so the gradients agree there
  refine hgF.congr_of_eventuallyEq ?_
  filter_upwards [hFeq.eventuallyEq_nhds] with y hy
  have : gradient g F y = gradient g r y := by
    simp only [gradient, hy.mfderiv_eq]
  exact congrArg _ this.symm

/-- **Eng.** Set form of `gradient_contMDiffAt_of_contMDiffOn`. -/
theorem gradient_contMDiffOn_of_contMDiffOn (g : RiemannianMetric I M) {r : M → ℝ}
    {U : Set M} (hU : IsOpen U) (hr : ContMDiffOn I 𝓘(ℝ) ∞ r U) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun x ↦ (⟨x, gradient g r x⟩ : TangentBundle I M)) U :=
  fun _ hp ↦ (gradient_contMDiffAt_of_contMDiffOn g hU hr hp).contMDiffWithinAt

/-- **Math.** Petersen **Ch. 5, remark on Lemma 5.3.2**, under exactly the book's
hypotheses.  Let `r` be a distance function on an open `U`, let `c : [a,b] → U`
be a smooth curve realising the bound `L(c)|_a^b = r(c(b)) − r(c(a))`, put
`φ(s) = L(c)|_a^s`, and let `σ` be an integral curve of `∇r` with `σ(0) = c(a)`.
Then `c = σ ∘ φ` on `[a,b]`: a curve realising the bound is a reparametrisation of
an integral curve of `∇r`.

This is `distanceFunction_minimizer_eq_integralCurve_comp` with the `C¹`-section
side condition on `∇r` discharged via `gradient_contMDiffOn_of_contMDiffOn`; the
smoothness of `r` on `U` recorded in `IsDistanceFunction` is all that is needed.
As in the book, the integral curve `σ` is *hypothesised*, not constructed. -/
theorem distanceFunction_minimizer_eq_integralCurve_comp'
    {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {a b : ℝ} (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (heq : curveLength (I := I) g c a b = r (c b) - r (c a))
    {σ : ℝ → M} (hσ : ContMDiff 𝓘(ℝ, ℝ) I ∞ σ) (hσ0 : σ 0 = c a)
    (hσint : ∀ u ∈ Icc 0 (curveLength (I := I) g c a b),
      velocity (I := I) σ u = gradient g r (σ u)) :
    ∀ s ∈ Icc a b, c s = σ (curveLength (I := I) g c a s) :=
  distanceFunction_minimizer_eq_integralCurve_comp hU hr
    ((gradient_contMDiffOn_of_contMDiffOn g hU hr.1).of_le (by norm_num))
    hab hc hcU heq hσ hσ0 hσint

end PetersenLib

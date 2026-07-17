import PoincareLib.Ch02.SliceChartStraightening
import PoincareLib.Ch02.ChartGradientParallel
import PoincareLib.Ch02.BochnerLipschitz

/-!
# Morgan–Tian Ch. 2 — adapted charts: `f` affine in a chart around any point

Blueprint `lem:parallel-gradient-level-sets`(1), chart layer, manifold part.
Around any point `y` where a smooth `f : M → ℝ` has non-vanishing
differential, the extended chart `extChartAt I y` can be corrected by a local
`C^∞` diffeomorphism `G` of the model space
(`exists_openPartialHomeomorph_comp_symm_eq_affine`,
`SliceChartStraightening.lean`) so that in the corrected chart `G ∘ κ` the
function `f` becomes **affine**:
`f(κ⁻¹(G⁻¹(v))) = f(y) + df_y(v − κ(y))`. Consequently the level set
`f⁻¹(f y)` reads in the corrected chart as the affine slice
`{v | df_y(v − κ(y)) = 0}` — the slice-chart normal form of the level set.

For the Bochner package the non-vanishing hypothesis is automatic:
`df_y(∇f(y)) = |∇f(y)|² = 1` (`mfderiv_ne_zero_of_bochner`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4.
-/

open Set Filter Function Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** The coordinate representation `f ∘ κ⁻¹` of a smooth function
has the manifold differential `df_y` as its (total) Fréchet derivative at
`κ(y)` — for a boundaryless model, `mfderiv` *is* the derivative of the
chart representative. -/
theorem hasFDerivAt_comp_extChartAt_symm {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M) :
    HasFDerivAt (f ∘ (extChartAt I y).symm) (mfderiv I 𝓘(ℝ, ℝ) f y)
      (extChartAt I y y) := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
    (hf y).mdifferentiableAt (by simp)
  have h := hmd.hasMFDerivAt.2
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h
  have hfun : writtenInExtChartAt I 𝓘(ℝ, ℝ) y f
      = f ∘ (extChartAt I y).symm := by
    simp [writtenInExtChartAt]
  rwa [hfun] at h

/-- **Math.** Under the unit-gradient hypothesis the differential of `f`
vanishes nowhere: `df_y(∇f(y)) = |∇f(y)|² = 1`. Blueprint
`lem:parallel-gradient-level-sets` (the level sets are regular). -/
theorem mfderiv_ne_zero_of_metricNormSq_gradientField_eq_one
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {y : M}
    (hgrad : metricNormSq g (gradientField g f hf) y = 1) :
    mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0 := by
  intro h0
  have h1 : g.metricInner y (gradientAt g f y) (gradientAt g f y) = 1 := hgrad
  rw [metricInner_gradientAt, h0] at h1
  simp only [ContinuousLinearMap.zero_apply] at h1
  exact zero_ne_one h1

/-- **Math.** **The adapted chart around a regular point** (blueprint
`lem:parallel-gradient-level-sets`(1), chart layer): if `f : M → ℝ` is smooth
with `df_y ≠ 0`, then the extended chart at `y` can be corrected by a local
`C^∞` diffeomorphism `G` of the model space, fixing `κ(y)`, so that in the
corrected chart `f` is **affine**:
`f(κ⁻¹(G⁻¹(v))) = f(y) + df_y(v − κ(y))` for every `v` in the target. In
particular the level set `f⁻¹(f y)` corresponds to the affine hyperplane
slice `{v ∈ G.target | df_y(v − κ(y)) = 0}`: together with the smooth
compatibility of `G` this exhibits `f` as the "last coordinate" of a chart,
the slice-chart normal form of the level set at `y`. -/
theorem exists_extChartAt_openPartialHomeomorph_comp_symm_eq_affine
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (y : M)
    (hdf : mfderiv I 𝓘(ℝ, ℝ) f y ≠ 0) :
    ∃ G : OpenPartialHomeomorph E E,
      G.source ⊆ (extChartAt I y).target ∧
      extChartAt I y y ∈ G.source ∧
      G (extChartAt I y y) = extChartAt I y y ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target ∧
      ∀ v ∈ G.target, f ((extChartAt I y).symm (G.symm v))
        = f y + mfderivReal (I := I) f y (v - extChartAt I y y) := by
  obtain ⟨G, h1, h2, h3, h4, h5, h6⟩ :=
    exists_openPartialHomeomorph_comp_symm_eq_affine
      (isOpen_extChartAt_target (I := I) y)
      (contDiffOn_comp_extChartAt_symm hf y)
      (mem_extChartAt_target (I := I) y)
      (hasFDerivAt_comp_extChartAt_symm hf y) hdf
  refine ⟨G, h1, h2, h3, h4, h5, fun v hv => ?_⟩
  have h := h6 v hv
  rw [Function.comp_apply, Function.comp_apply, extChartAt_to_inv] at h
  rw [mfderivReal_def]
  exact h

end PoincareLib

end

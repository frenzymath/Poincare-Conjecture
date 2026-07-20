import MorganTianLib.Ch02.ChartGradientParallel
import MorganTianLib.Ch01.JacobiManifold

/-!
# Morgan–Tian Ch. 2 — chart-derivative bridges for the gradient-flow isometry

Blueprint `lem:parallel-gradient-flow`(4), transfer layer. The θ_t-isometry
argument analyzes the flow of the gradient field in a fixed chart at `z`;
this file provides the bridges between manifold-level derivatives and their
chart readings:

* `mfderiv_extChartAt_apply_eq_tangentCoordChange` — the differential of the
  chart map `φ = extChartAt I z` at `x` is the tangent coordinate change
  `T_x M → E` into the chart at `z`.
* `mfderiv_extChartAt_symm_apply_eq_trivializationAt_symm` — the differential
  of the inverse chart at a chart-target point is the inverse trivialization
  readback `E → T_b M`.
* `fieldChartRep_apply_eq_tangentCoordChange` — the chart representation of
  a smooth vector field is its tangent-coordinate-change reading.
* `isMIntegralCurveOn_extChartAt_symm_comp` — **chart-to-manifold transfer of
  integral curves**: a solution of the chart ODE `u' = X̂(u)` pushes through
  `φ⁻¹` to an integral curve of `X` (mirrors the flow-box transfer, for the
  `fieldChartRep` right-hand side).
* `fderiv_neg_fieldChartRep_gradientField_of_bochner` — the parallel identity
  for the **negated** gradient field, used for negative flow times.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.4
(blueprint `lem:parallel-gradient-flow`).
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-! ### The differentials of the chart and its inverse -/

/-- **Math.** The differential of the chart map `φ = extChartAt I z` at a
point `x` of its source is the **tangent coordinate change** into the chart
at `z`: `dφ_x = tangentCoordChange I x z x`. -/
theorem mfderiv_extChartAt_apply_eq_tangentCoordChange {z x : M}
    (hx : x ∈ (chartAt H z).source) (v : TangentSpace I x) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I z) x v = tangentCoordChange I x z x v := by
  have hmd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I z) x :=
    mdifferentiableAt_extChartAt hx
  rw [hmd.mfderiv, tangentCoordChange_def]
  congr 1

/-- **Math.** The differential of the inverse chart `φ⁻¹` at a chart-target
point `y` is the **inverse trivialization readback** at the foot
`b = φ⁻¹(y)`: `d(φ⁻¹)_y = (trivializationAt z).symm b`. -/
theorem mfderiv_extChartAt_symm_apply_eq_trivializationAt_symm {z : M} {y : E}
    (hy : y ∈ (extChartAt I z).target) (a : E) :
    mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm y a
      = (trivializationAt E (TangentSpace I) z).symm
          ((extChartAt I z).symm y) a := by
  have hbsrc : (extChartAt I z).symm y ∈ (extChartAt I z).source :=
    (extChartAt I z).map_target hy
  have hbchart : (extChartAt I z).symm y ∈ (chartAt H z).source := by
    rwa [extChartAt_source] at hbsrc
  have hyb : extChartAt I z ((extChartAt I z).symm y) = y :=
    (extChartAt I z).right_inv hy
  have hrange : Set.range (I : H → E) = Set.univ :=
    ModelWithCorners.Boundaryless.range_eq_univ
  -- differentiability of the inverse chart at `y`
  have hmd : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I z).symm y := by
    rw [← mdifferentiableWithinAt_univ, ← hrange]
    exact mdifferentiableWithinAt_extChartAt_symm hy
  -- both sides compute the plain derivative of `φ_b ∘ φ_z⁻¹` at `y`
  have hfun : writtenInExtChartAt 𝓘(ℝ, E) I y ((extChartAt I z).symm)
      = (extChartAt I ((extChartAt I z).symm y)) ∘ ((extChartAt I z).symm) := by
    funext y'
    simp [writtenInExtChartAt, Function.comp]
  have hL : mfderiv 𝓘(ℝ, E) I (extChartAt I z).symm y
      = fderiv ℝ ((extChartAt I ((extChartAt I z).symm y))
          ∘ ((extChartAt I z).symm)) y := by
    rw [hmd.mfderiv, hfun,
      show Set.range ((𝓘(ℝ, E) : ModelWithCorners ℝ E E) : E → E) = Set.univ by simp,
      fderivWithin_univ]
    simp
  have hR : ∀ a' : E, tangentCoordChange I z ((extChartAt I z).symm y)
        ((extChartAt I z).symm y) a'
      = fderiv ℝ ((extChartAt I ((extChartAt I z).symm y))
          ∘ ((extChartAt I z).symm)) y a' := by
    intro a'
    rw [tangentCoordChange_def, hyb, hrange, fderivWithin_univ]
  rw [trivializationAt_symm_eq_tangentCoordChange (I := I) z hbchart, hR a, hL]
  rfl

/-! ### The chart representation of a field as a coordinate change -/

/-- **Math.** The chart-`z` fibre coordinate of a tangent vector at `b` is
its tangent coordinate change into the chart at `z`. -/
theorem chartFiberCoord_eq_tangentCoordChange {z b : M}
    (hb : b ∈ (chartAt H z).source) (v : TangentSpace I b) :
    chartFiberCoord (I := I) z ⟨b, v⟩ = tangentCoordChange I b z b v := by
  have hb' : b ∈ (trivializationAt E (TangentSpace I) z).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have hv : v = (trivializationAt E (TangentSpace I) z).symm b
      (tangentCoordChange I b z b v) :=
    (trivializationAt_symm_tangentCoordChange (I := I) hb v).symm
  have happ := (trivializationAt E (TangentSpace I) z).apply_mk_symm hb'
    (tangentCoordChange I b z b v)
  rw [chartFiberCoord_def]
  conv_lhs => rw [hv]
  rw [happ]

/-- **Math.** The chart representation of a smooth vector field at a
chart-target point `y` is the tangent-coordinate-change reading of the field
at the foot `φ⁻¹(y)`. -/
theorem fieldChartRep_apply_eq_tangentCoordChange (X : SmoothVectorField I M)
    {z : M} {y : E} (hy : y ∈ (extChartAt I z).target) :
    fieldChartRep (I := I) z X y
      = tangentCoordChange I ((extChartAt I z).symm y) z
          ((extChartAt I z).symm y) (X ((extChartAt I z).symm y)) := by
  have hbchart : (extChartAt I z).symm y ∈ (chartAt H z).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I z).map_target hy
  exact chartFiberCoord_eq_tangentCoordChange hbchart _

/-! ### Chart-to-manifold transfer of integral curves -/

/-- **Math.** **Chart-to-manifold transfer of integral curves**: if `u`
solves the chart ODE `u' = X̂(u)` (with `X̂ = fieldChartRep z X`) on an open
set of times, staying in the chart target, then `t ↦ φ⁻¹(u(t))` is an
integral curve of `X`. Mirrors the flow-box transfer through
`tangentCoordChange`. -/
theorem isMIntegralCurveOn_extChartAt_symm_comp (X : SmoothVectorField I M)
    (z : M) {u : ℝ → E} {s : Set ℝ}
    (hmem : ∀ t ∈ s, u t ∈ (extChartAt I z).target)
    (hu : ∀ t ∈ s, HasDerivAt u (fieldChartRep (I := I) z X (u t)) t) :
    IsMIntegralCurveOn (fun t => (extChartAt I z).symm (u t))
      (fun q => X q) s := by
  intro t ht
  set xₜ : M := (extChartAt I z).symm (u t) with hxₜ_def
  have hf3' : u t ∈ (extChartAt I z).target := hmem t ht
  have hft1 : xₜ ∈ (extChartAt I z).source := (extChartAt I z).map_target hf3'
  have hft1' : xₜ ∈ (chartAt H z).source := by rwa [extChartAt_source] at hft1
  have hft2 := mem_extChartAt_source (I := I) xₜ
  -- the chart ODE with the tangent-coordinate-change right-hand side
  have h' : HasDerivAt u (tangentCoordChange I xₜ z xₜ (X xₜ)) t := by
    have h := hu t ht
    rwa [fieldChartRep_apply_eq_tangentCoordChange X hf3'] at h
  -- transfer through the chart, as in the flow box
  apply HasMFDerivAt.hasMFDerivWithinAt
  refine ⟨(continuousAt_extChartAt_symm'' hf3').comp h'.continuousAt,
    HasDerivWithinAt.hasFDerivWithinAt ?_⟩
  simp only [mfld_simps, hasDerivWithinAt_univ]
  change HasDerivAt ((extChartAt I xₜ ∘ (extChartAt I z).symm) ∘ u) (X xₜ) t
  rw [← tangentCoordChange_self (I := I) (x := xₜ) (z := xₜ) (v := X xₜ) hft2,
    ← tangentCoordChange_comp (x := z) ⟨⟨hft2, hft1⟩, hft2⟩]
  apply HasFDerivAt.comp_hasDerivAt _ _ h'
  apply HasFDerivWithinAt.hasFDerivAt (s := range I) _ <|
    mem_nhds_iff.mpr ⟨interior (extChartAt I z).target,
      subset_trans interior_subset (extChartAt_target_subset_range ..),
      isOpen_interior, ?_⟩
  · rw [← (extChartAt I z).right_inv hf3']
    exact hasFDerivWithinAt_tangentCoordChange ⟨hft1, hft2⟩
  · rw [(isOpen_extChartAt_target (I := I) z).interior_eq]
    exact hf3'

/-! ### The parallel identity for the negated gradient field -/

/-- **Math.** The **negated** gradient field also satisfies the fixed-chart
parallel identity `∂(−V̂)(y)·w = −Γ(w, (−V̂)(y))(y)` — the input for flowing
backwards in time. -/
theorem fderiv_neg_fieldChartRep_gradientField_of_bochner
    [SigmaCompactSpace M] [T2Space M] (g : RiemannianMetric I M)
    {nabla : AffineConnection I M} (hLC : nabla.IsLeviCivita g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {c₁ c₂ : ℝ}
    (hgrad : ∀ q, metricNormSq g (gradientField g f hf) q = c₁)
    (hharm : ∀ q, laplacianAt g nabla f q = c₂)
    (hric : ∀ q, 0 ≤ ricciAt g nabla hLC q (gradientAt g f q) (gradientAt g f q))
    (z : M) {y : E} (hy : y ∈ (extChartAt I z).target) (w : E) :
    fderiv ℝ (fun y' => -(fieldChartRep (I := I) z (gradientField g f hf) y')) y w
      = - Geodesic.chartChristoffelContraction (I := I) g z w
          (-(fieldChartRep (I := I) z (gradientField g f hf) y)) y := by
  have hneg : fderiv ℝ
      (fun y' => -(fieldChartRep (I := I) z (gradientField g f hf) y')) y
      = -(fderiv ℝ (fieldChartRep (I := I) z (gradientField g f hf)) y) :=
    fderiv_neg
  rw [hneg, ContinuousLinearMap.neg_apply,
    fderiv_fieldChartRep_gradientField_of_bochner g hLC hf hgrad hharm hric z hy w,
    show (-(fieldChartRep (I := I) z (gradientField g f hf) y))
        = ((-1 : ℝ) • fieldChartRep (I := I) z (gradientField g f hf) y) from
      (neg_one_smul ℝ _).symm,
    Geodesic.chartChristoffelContraction_smul_right]
  simp

end MorganTianLib

end

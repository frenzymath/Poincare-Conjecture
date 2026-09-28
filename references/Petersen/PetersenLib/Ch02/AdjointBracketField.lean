import PetersenLib.Ch02.AdjointBracket
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Bridge B: the group Lie bracket in chart coordinates (Petersen §2.1.4)

The abstract group bracket `⁅U, X⁆` on `GroupLieAlgebra I G`, read through the
chart at `1`, is the flat commutator of the *chart invariant fields*
`Ṽ_Z a = D₂(chartMul)(a, c)·Z`.  This is the "bracket side" of `ad = D(Ad)`.
-/

open Bundle Set Function VectorField
open scoped Manifold ContDiff Topology

noncomputable section

namespace PetersenLib.AdjointBracket

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G] [I.Boundaryless]

/-- The derivative of `(extChartAt I 1).symm` at a target point, inverted, is the
derivative of the chart. -/
lemma mfderivWithin_chartSymm_inverse {a : E} (ha : a ∈ (extChartAt I (1 : G)).target) :
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (range I) a).inverse
      = mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) ((extChartAt I (1 : G)).symm a) :=
  ContinuousLinearMap.inverse_eq
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt ha)
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm ha)

/-- The manifold derivative of `(extChartAt I 1).symm` at `chartOne` is the identity. -/
lemma mfderiv_chartSymm_chartOne :
    mfderiv 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G))
      = ContinuousLinearMap.id ℝ E := by
  have h : mfderiv 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G))
      = mfderivWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (range I)
          (chartOne (I := I) (G := G)) := by
    rw [← mfderivWithin_univ, I.range_eq_univ]
  rw [h]
  exact mfderivWithin_range_extChartAt_symm

/-- **Bridge B core.** The chart-pullback of the left-invariant vector field of `Z`
equals the `chartMul`-invariant field `a ↦ D₂(chartMul)(a, c)·Z`, on the chart target. -/
lemma pullback_mulInvariant_eq (Z : E) {a : E} (ha : a ∈ (extChartAt I (1 : G)).target) :
    mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (mulInvariantVectorField Z) (range I) a
      = fderiv ℝ (fun b => chartMul (I := I) (G := G) a b) (chartOne (I := I) (G := G)) Z := by
  rw [mpullbackWithin_apply, mfderivWithin_chartSymm_inverse ha]
  -- The three smooth pieces of `fun b ↦ chartMul a b = φ ∘ (φ.symm a * ·) ∘ φ.symm`,
  -- at the basepoints required for composition at `chartOne`.
  have hsymm : HasMFDerivAt 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E) := by
    rw [← mfderiv_chartSymm_chartOne (I := I) (G := G)]
    exact ((contMDiffAt_chartSymm (I := I) (G := G)).mdifferentiableAt (by decide)).hasMFDerivAt
  have hL : HasMFDerivAt I I (fun y : G => (extChartAt I (1 : G)).symm a * y)
      ((extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)))
      (mfderiv I I (fun y : G => (extChartAt I (1 : G)).symm a * y)
        ((extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)))) :=
    (contMDiffAt_mul_left.mdifferentiableAt (n := 1) one_ne_zero).hasMFDerivAt
  have hφ : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I (1 : G))
      ((extChartAt I (1 : G)).symm a * (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)))
      (mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G))
        ((extChartAt I (1 : G)).symm a
          * (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)))) := by
    apply MDifferentiableAt.hasMFDerivAt
    apply mdifferentiableAt_extChartAt
    rw [symm_chartOne, mul_one, ← extChartAt_source (I := I)]
    exact (extChartAt I (1 : G)).map_target ha
  have hcomp := hφ.comp (chartOne (I := I) (G := G))
    (hL.comp (chartOne (I := I) (G := G)) hsymm)
  have hfun : (fun b => chartMul (I := I) (G := G) a b)
      = ⇑(extChartAt I (1 : G)) ∘ ((fun y : G => (extChartAt I (1 : G)).symm a * y)
          ∘ ⇑(extChartAt I (1 : G)).symm) := rfl
  rw [hfun, (hasMFDerivAt_iff_hasFDerivAt.mp hcomp).fderiv, symm_chartOne, mul_one]
  rfl

/-- The chart-invariant field of `Z` takes value `Z` at `chartOne` (left unit law). -/
lemma chartInvariantField_chartOne_apply (Z : E) :
    fderiv ℝ (fun b => chartMul (I := I) (G := G) (chartOne (I := I) (G := G)) b)
        (chartOne (I := I) (G := G)) Z = Z := by
  have h : (fun b => chartMul (I := I) (G := G) (chartOne (I := I) (G := G)) b)
      =ᶠ[𝓝 (chartOne (I := I) (G := G))] id := by
    filter_upwards [chartMul_left_id (I := I) (G := G)] with b hb using hb
  rw [h.fderiv_eq, fderiv_id]
  rfl

/-- **Bridge B.** The abstract group Lie bracket `⁅U, X⁆` (as `mlieBracket` of the
left-invariant fields), read in the chart at `1`, is the flat commutator of the
`chartMul`-invariant fields. -/
lemma groupBracket_eq_bracketChart (X U : E) :
    mlieBracket I (mulInvariantVectorField (I := I) (G := G) U)
        (mulInvariantVectorField (I := I) (G := G) X) (1 : G)
      = fderiv ℝ (fun a => fderiv ℝ (fun b => chartMul (I := I) (G := G) a b)
            (chartOne (I := I) (G := G)) X) (chartOne (I := I) (G := G)) U
        - fderiv ℝ (fun a => fderiv ℝ (fun b => chartMul (I := I) (G := G) a b)
            (chartOne (I := I) (G := G)) U) (chartOne (I := I) (G := G)) X := by
  have hbr : mlieBracket I (mulInvariantVectorField (I := I) (G := G) U)
        (mulInvariantVectorField (I := I) (G := G) X) (1 : G)
      = lieBracket ℝ
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (mulInvariantVectorField U)
            (range I))
          (mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (mulInvariantVectorField X)
            (range I))
          (chartOne (I := I) (G := G)) := by
    rw [← mlieBracketWithin_univ, mlieBracketWithin_apply]
    have hset : (extChartAt I (1 : G)).symm ⁻¹' univ ∩ range I = univ := by
      rw [preimage_univ, univ_inter, I.range_eq_univ]
    have hid : (mfderiv I 𝓘(ℝ, E) (extChartAt I (1 : G)) 1).inverse
        = ContinuousLinearMap.id ℝ E := by
      rw [mfderiv_extChartAt_self]; exact ContinuousLinearMap.inverse_id
    rw [hset, lieBracketWithin_univ, hid]
    rfl
  have hUeq : mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (mulInvariantVectorField U)
        (range I)
      =ᶠ[𝓝 (chartOne (I := I) (G := G))]
        (fun a => fderiv ℝ (fun b => chartMul (I := I) (G := G) a b)
          (chartOne (I := I) (G := G)) U) := by
    filter_upwards [target_mem_nhds (I := I) (G := G)] with a ha using pullback_mulInvariant_eq U ha
  have hXeq : mpullbackWithin 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm (mulInvariantVectorField X)
        (range I)
      =ᶠ[𝓝 (chartOne (I := I) (G := G))]
        (fun a => fderiv ℝ (fun b => chartMul (I := I) (G := G) a b)
          (chartOne (I := I) (G := G)) X) := by
    filter_upwards [target_mem_nhds (I := I) (G := G)] with a ha using pullback_mulInvariant_eq X ha
  rw [hbr]
  simp only [lieBracket_eq, hXeq.fderiv_eq, hUeq.fderiv_eq, hUeq.eq_of_nhds, hXeq.eq_of_nhds,
    chartInvariantField_chartOne_apply]

end PetersenLib.AdjointBracket

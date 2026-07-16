import PetersenLib.Ch02.AdjointDifferential
import PetersenLib.Ch02.AdjointBracket

open Bundle Set Function VectorField
open scoped Manifold ContDiff Topology

noncomputable section
namespace PetersenLib.AdjointBracket

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G] [I.Boundaryless]

lemma mfderiv_adMap_eq_adChart (X U : E) :
    mfderiv I 𝓘(ℝ, E) (fun h : G => adMap (I := I) h X) 1 U
      = fderiv ℝ (fun α => fderiv ℝ (fun a =>
          chartMul (I := I) (G := G) (chartMul (I := I) (G := G) α a)
            (chartInv (I := I) (G := G) α))
          (chartOne (I := I) (G := G)) X) (chartOne (I := I) (G := G)) U := by
  haveI : IsTopologicalGroup G := topologicalGroup_of_lieGroup (I := I) (n := ∞)
  set A : E → E := fun α => fderiv ℝ (fun a =>
      chartMul (I := I) (G := G) (chartMul (I := I) (G := G) α a)
        (chartInv (I := I) (G := G) α)) (chartOne (I := I) (G := G)) X with hAdef
  -- A manifold map `G → G` differentiable at `1`: its `mfderiv` is the `fderiv`
  -- of the chart-representation, using boundarylessness (`range I = univ`).
  have mfderiv_eq_written : ∀ (f : G → G), MDifferentiableAt I I f (1 : G) →
      mfderiv I I f (1 : G)
        = fderiv ℝ (writtenInExtChartAt I I (1 : G) f) (chartOne (I := I) (G := G)) := by
    intro f hf
    have hfd := hf.hasMFDerivAt.2
    rw [I.range_eq_univ, hasFDerivWithinAt_univ] at hfd
    exact hfd.fderiv.symm
  -- (A1): the adjoint-orbit map equals `A ∘ φ` near `1`.
  have hA1 : (fun h : G => adMap (I := I) h X)
      =ᶠ[𝓝 (1 : G)] (A ∘ (extChartAt I (1 : G))) := by
    have hsrc : {h : G | h ∈ (extChartAt I (1 : G)).source ∧
        h⁻¹ ∈ (extChartAt I (1 : G)).source} ∈ 𝓝 (1 : G) := by
      refine Filter.inter_mem
        ((isOpen_extChartAt_source (1 : G)).mem_nhds (mem_extChartAt_source (1 : G))) ?_
      have hinv : ContinuousAt (fun g : G => g⁻¹) (1 : G) := continuous_inv.continuousAt
      have : (extChartAt I (1 : G)).source ∈ 𝓝 ((1 : G)⁻¹) := by
        rw [inv_one]; exact (isOpen_extChartAt_source (1 : G)).mem_nhds (mem_extChartAt_source (1 : G))
      exact hinv.preimage_mem_nhds this
    filter_upwards [hsrc] with h hh
    obtain ⟨hh, hhinv⟩ := hh
    -- Reduce `adMap h X` to the chart representation of conjugation.
    rw [adMap_apply, mfderiv_eq_written _ (mdifferentiableAt_conj h 1)]
    -- The chart representation of conjugation, rewritten near `chartOne`.
    have hconj1 : h * (1 : G) * h⁻¹ = 1 := by group
    have hwrit : writtenInExtChartAt I I (1 : G) (fun y => h * y * h⁻¹)
        = fun a => extChartAt I (1 : G)
            (h * (extChartAt I (1 : G)).symm a * h⁻¹) := by
      funext a
      simp only [writtenInExtChartAt, Function.comp_apply, hconj1]
    -- Eventual equality with the chart-multiplication expression.
    have hφsymm_cont : ContinuousAt (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)) :=
      (contMDiffAt_chartSymm (I := I) (G := G)).continuousAt
    have hg_cont : ContinuousAt (fun a => h * (extChartAt I (1 : G)).symm a)
        (chartOne (I := I) (G := G)) :=
      (continuous_const.mul continuous_id).continuousAt.comp hφsymm_cont
    have hanbhd : {a : E | h * (extChartAt I (1 : G)).symm a ∈ (extChartAt I (1 : G)).source}
        ∈ 𝓝 (chartOne (I := I) (G := G)) := by
      apply hg_cont.preimage_mem_nhds
      rw [symm_chartOne, mul_one]
      exact (isOpen_extChartAt_source (1 : G)).mem_nhds hh
    have heq_written : writtenInExtChartAt I I (1 : G) (fun y => h * y * h⁻¹)
        =ᶠ[𝓝 (chartOne (I := I) (G := G))]
        (fun a => chartMul (I := I) (G := G)
          (chartMul (I := I) (G := G) (extChartAt I (1 : G) h) a)
          (chartInv (I := I) (G := G) (extChartAt I (1 : G) h))) := by
      filter_upwards [hanbhd] with a ha
      rw [hwrit]
      simp only [chartMul, chartInv]
      rw [(extChartAt I (1 : G)).left_inv hh, (extChartAt I (1 : G)).left_inv ha,
        (extChartAt I (1 : G)).left_inv hhinv]
    rw [heq_written.fderiv_eq]
    rfl
  rw [hA1.mfderiv_eq]
  -- (A2): `mfderiv (A ∘ φ) 1 U = fderiv A c U`.
  have hφdiff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I (1 : G)) 1 :=
    mdifferentiableAt_extChartAt (mem_chart_source H (1 : G))
  have hadX : MDifferentiableAt I 𝓘(ℝ, E) (fun h : G => adMap (I := I) h X) 1 :=
    (mdifferentiableAt_adMap 1).clm_apply mdifferentiableAt_const
  have hAφ : MDifferentiableAt I 𝓘(ℝ, E) (A ∘ (extChartAt I (1 : G))) 1 :=
    hadX.congr_of_eventuallyEq hA1.symm
  have hφsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I (1 : G)).symm
      (chartOne (I := I) (G := G)) :=
    (contMDiffAt_chartSymm (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hAdiff : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) A (chartOne (I := I) (G := G)) := by
    have hcomp : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
        ((A ∘ (extChartAt I (1 : G))) ∘ (extChartAt I (1 : G)).symm)
        (chartOne (I := I) (G := G)) :=
      MDifferentiableAt.comp_of_eq (hg := hAφ) (hf := hφsymm) (hy := symm_chartOne)
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [target_mem_nhds (I := I) (G := G)] with a ha
    simp only [Function.comp_apply]
    rw [chart_right_inv ha]
  rw [mfderiv_comp (1 : G) hAdiff hφdiff, mfderiv_extChartAt_self, mfderiv_eq_fderiv]
  rfl

end PetersenLib.AdjointBracket

import PetersenLib.Ch01.BiinvariantExistence
import PetersenLib.Ch01.AdjointRepresentation
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# `ad = D(Ad)` for an abstract Lie group (Petersen §2.1.4, Lemma 2.1.7)

This file proves `PetersenLib.mfderiv_adMap_apply_eq_groupBracket`, the abstract
form of Petersen's Lemma 2.1.7 — the last open node of Chapter 1.  The identity
`D(Ad)_e(U)(X) = ⁅U, X⁆` is reduced to a purely normed-space second-derivative
identity of the *chart multiplication*
`μ a b = φ(φ⁻¹ a · φ⁻¹ b)`  (`φ = extChartAt I 1`, `c = φ 1`),
which is `PetersenLib.ChartMul.adChart_eq_bracketChart`.

The manifold ↔ chart bridges are proved here.
-/

open Bundle Set Function VectorField
open scoped Manifold ContDiff Topology

noncomputable section

namespace PetersenLib.AdjointBracket

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G] [I.Boundaryless]

/-- Chart multiplication: the group multiplication read in the chart at `1`. -/
def chartMul (a b : E) : E :=
  extChartAt I (1 : G) ((extChartAt I (1 : G)).symm a * (extChartAt I (1 : G)).symm b)

/-- Chart inversion: the group inversion read in the chart at `1`. -/
def chartInv (a : E) : E :=
  extChartAt I (1 : G) ((extChartAt I (1 : G)).symm a)⁻¹

/-- The chart point of the identity. -/
def chartOne : E := extChartAt I (1 : G) (1 : G)

/-- The chart-inverse of the identity's chart point is `1`. -/
lemma symm_chartOne :
    (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)) = 1 := by
  show (extChartAt I (1 : G)).symm (extChartAt I (1 : G) (1 : G)) = 1
  exact extChartAt_to_inv (1 : G)

/-- The chart target is a neighborhood of `chartOne`. -/
lemma target_mem_nhds :
    (extChartAt I (1 : G)).target ∈ 𝓝 (chartOne (I := I) (G := G)) :=
  extChartAt_target_mem_nhds (1 : G)

/-- On the chart target, `φ ∘ φ.symm = id`. -/
lemma chart_right_inv {a : E} (ha : a ∈ (extChartAt I (1 : G)).target) :
    extChartAt I (1 : G) ((extChartAt I (1 : G)).symm a) = a :=
  PartialEquiv.right_inv _ ha

/-- Right unit law for the chart multiplication, near `chartOne`. -/
lemma chartMul_right_id :
    ∀ᶠ a in 𝓝 (chartOne (I := I) (G := G)), chartMul (I := I) (G := G) a (chartOne (I := I) (G := G)) = a := by
  filter_upwards [target_mem_nhds (I := I) (G := G)] with a ha
  simp only [chartMul, symm_chartOne, mul_one, chart_right_inv ha]

/-- Left unit law for the chart multiplication, near `chartOne`. -/
lemma chartMul_left_id :
    ∀ᶠ b in 𝓝 (chartOne (I := I) (G := G)), chartMul (I := I) (G := G) (chartOne (I := I) (G := G)) b = b := by
  filter_upwards [target_mem_nhds (I := I) (G := G)] with b hb
  simp only [chartMul, symm_chartOne, one_mul, chart_right_inv hb]

/-- The chart inversion fixes `chartOne`. -/
lemma chartInv_chartOne :
    chartInv (I := I) (G := G) (chartOne (I := I) (G := G)) = chartOne (I := I) (G := G) := by
  show extChartAt I (1 : G) ((extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)))⁻¹
      = chartOne (I := I) (G := G)
  rw [symm_chartOne, inv_one]
  rfl

/-- The chart inverse is `C^∞` at `chartOne`. -/
lemma contMDiffAt_chartSymm :
    ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)) :=
  (contMDiffWithinAt_extChartAt_symm_target_self (1 : G)).contMDiffAt
    (target_mem_nhds (I := I) (G := G))

/-- The chart inversion `chartInv` is `C²` at `chartOne`. -/
lemma contDiffAt_chartInv :
    ContDiffAt ℝ 2 (chartInv (I := I) (G := G)) (chartOne (I := I) (G := G)) := by
  have h1 : ContMDiffAt 𝓘(ℝ, E) I 2 (extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)) :=
    (contMDiffAt_chartSymm (I := I) (G := G)).of_le (by decide)
  have h2 : ContMDiffAt I I 2 (fun g : G => g⁻¹)
      ((extChartAt I (1 : G)).symm (chartOne (I := I) (G := G))) :=
    (contMDiff_inv I 2).contMDiffAt
  have h3 : ContMDiffAt I 𝓘(ℝ, E) 2 (extChartAt I (1 : G))
      (((extChartAt I (1 : G)).symm (chartOne (I := I) (G := G)))⁻¹) :=
    contMDiffAt_extChartAt' (by rw [symm_chartOne, inv_one]; exact mem_chart_source H (1 : G))
  have : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2 (chartInv (I := I) (G := G))
      (chartOne (I := I) (G := G)) :=
    h3.comp (chartOne (I := I) (G := G))
      (h2.comp (chartOne (I := I) (G := G)) h1)
  exact contMDiffAt_iff_contDiffAt.mp this

/-- The chart multiplication is `C²` at `(chartOne, chartOne)`. -/
lemma contDiffAt_chartMul :
    ContDiffAt ℝ 2 (fun p : E × E => chartMul (I := I) (G := G) p.1 p.2)
      (chartOne (I := I) (G := G), chartOne (I := I) (G := G)) := by
  have hmul : ContMDiffAt (I.prod I) I 2 (fun q : G × G => q.1 * q.2) ((1 : G), (1 : G)) :=
    contMDiffAt_fst.mul contMDiffAt_snd
  have h := (contMDiffAt_iff.mp hmul).2
  rw [(I.prod I).range_eq_univ, contDiffWithinAt_univ] at h
  have hpt : extChartAt (I.prod I) ((1 : G), (1 : G)) ((1 : G), (1 : G))
      = (chartOne (I := I) (G := G), chartOne (I := I) (G := G)) := by
    rw [extChartAt_prod]; rfl
  have hfun : (extChartAt I ((fun q : G × G => q.1 * q.2) ((1 : G), (1 : G)))
        ∘ (fun q : G × G => q.1 * q.2) ∘ (extChartAt (I.prod I) ((1 : G), (1 : G))).symm)
      = (fun p : E × E => chartMul (I := I) (G := G) p.1 p.2) := by
    funext p
    simp only [Function.comp_apply, mul_one, extChartAt_prod, PartialEquiv.prod_symm,
      PartialEquiv.prod_coe]
    rfl
  rw [hfun, hpt] at h
  exact h

/-- The inverse law for the chart multiplication, near `chartOne`. -/
lemma chartMul_chartInv_self :
    ∀ᶠ α in 𝓝 (chartOne (I := I) (G := G)),
      chartMul (I := I) (G := G) α (chartInv (I := I) (G := G) α) = chartOne (I := I) (G := G) := by
  have hk : ContinuousAt (fun α => ((extChartAt I (1 : G)).symm α)⁻¹) (chartOne (I := I) (G := G)) :=
    ((contMDiff_inv I ∞).continuous.continuousAt).comp
      (contMDiffAt_chartSymm (I := I) (G := G)).continuousAt
  have hsrc : (extChartAt I (1 : G)).source
      ∈ 𝓝 ((fun α => ((extChartAt I (1 : G)).symm α)⁻¹) (chartOne (I := I) (G := G))) := by
    rw [show (fun α => ((extChartAt I (1 : G)).symm α)⁻¹) (chartOne (I := I) (G := G)) = 1 by
      simp only [symm_chartOne, inv_one]]
    exact (isOpen_extChartAt_source (1 : G)).mem_nhds (mem_extChartAt_source (1 : G))
  filter_upwards [hk.preimage_mem_nhds hsrc] with α hα
  simp only [chartMul, chartInv]
  rw [(extChartAt I (1 : G)).left_inv hα, mul_inv_cancel]
  rfl

end PetersenLib.AdjointBracket

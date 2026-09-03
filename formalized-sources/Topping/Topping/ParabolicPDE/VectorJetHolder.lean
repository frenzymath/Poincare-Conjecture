import Topping.ParabolicPDE.VectorJetSections
import Topping.ParabolicPDE.ParabolicHolder

/-!
# Holder controls for sampled vector two-jets

This module supplies the analytic bridge missing between the compactly sampled
coordinate jets and the parabolic section-space consumers.  A Lipschitz path
with image in a compact convex carrier pulls a `C^1` coordinate map back to a
Lipschitz field.  Applying this observation to a `C^3` vector map gives
parabolic Holder controls for its value, first, and second coordinate jets.

No manifold or bundle identification is made here: the carrier and the path
are explicit, so this producer can be used by a later chart assembly.  The
generic statement permits an empty time set (and, in zero model dimension, an
empty coordinate index family); no nonempty source-time interval is asserted.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BigOperators NNReal ENNReal Topology

noncomputable section

/-! ## Pulling back a compact-carrier Lipschitz estimate -/

variable {X T E V : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {J : Set T}

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
/-- A Lipschitz map on a carrier remains parabolically Lipschitz after
composition with a path having separate spatial and temporal Lipschitz bounds.
The image-membership hypothesis is explicit, so the estimate is genuinely
usable for maps which are only controlled on a chart carrier. -/
theorem parabolicHolderControl_comp_of_lipschitzOn
    {K : Set E} {f : E → V} {chi : X × T → E}
    {Lf Lχs Lχt : ℝ≥0}
    (hf : LipschitzOnWith Lf f K)
    (hchiK : ∀ z, chi z ∈ K)
    (hχs : ∀ t ∈ J, LipschitzWith Lχs (fun x : X => chi (x, t)))
    (hχt : ∀ x : X,
      LipschitzOnWith Lχt (fun t : T => chi (x, t)) J) :
    ParabolicHolderControl (fun z => f (chi z)) J
      (Lf * Lχs) 1 (Lf * Lχt) 1 := by
  apply ParabolicHolderControl.of_lipschitz
  · intro t ht
    have hcomp :
        LipschitzOnWith (Lf * Lχs)
          (f ∘ (fun x : X => chi (x, t))) (Set.univ : Set X) :=
      hf.comp (hχs t ht).lipschitzOnWith (by
        intro x hx
        exact hchiK (x, t))
    simpa only [lipschitzOnWith_univ, Function.comp_def] using hcomp
  · intro x
    have hcomp :
        LipschitzOnWith (Lf * Lχt)
          (f ∘ (fun t : T => chi (x, t))) J :=
      hf.comp (hχt x) (by
        intro t ht
        exact hchiK (x, t))
    simpa only [Function.comp_def] using hcomp

/-- A `C^1` map on a compact convex carrier has a finite Lipschitz constant
there, and hence can be composed with the preceding parabolic path estimate. -/
theorem exists_parabolicHolderControl_comp_of_contDiffOn
    {K : Set E} {f : E → V} {chi : X × T → E}
    {Lχs Lχt : ℝ≥0}
    (hf : ContDiffOn ℝ 1 f K)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (hchiK : ∀ z, chi z ∈ K)
    (hχs : ∀ t ∈ J, LipschitzWith Lχs (fun x : X => chi (x, t)))
    (hχt : ∀ x : X,
      LipschitzOnWith Lχt (fun t : T => chi (x, t)) J) :
    ∃ Lf : ℝ≥0,
      ParabolicHolderControl (fun z => f (chi z)) J
        (Lf * Lχs) 1 (Lf * Lχt) 1 := by
  obtain ⟨Lf, hLf⟩ := hf.exists_lipschitzOnWith
    (by norm_num) hKconv hKcompact
  exact ⟨Lf, parabolicHolderControl_comp_of_lipschitzOn
    hLf hchiK hχs hχt⟩

/-! ## Coordinate jet regularity -/

variable [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem contDiffOn_vectorJet_value
    {K : Set E} (u : E → V) (hu : ContDiff ℝ 3 u) :
    ContDiffOn ℝ 1 u K := by
  exact (hu.of_le (by norm_num)).contDiffOn

private theorem contDiffOn_vectorJet_first
  {K : Set E} (u : E → V) (hu : ContDiff ℝ 3 u)
    (i : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ 1
      (fun x : E => fderiv ℝ u x ((Module.finBasis ℝ E) i)) K := by
  have hdu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hi : ContDiff ℝ 2 (fun x : E =>
      fderiv ℝ u x ((Module.finBasis ℝ E) i)) := by
    exact hdu.clm_apply contDiff_const
  exact (hi.of_le (by norm_num)).contDiffOn

private theorem contDiffOn_vectorJet_second
    {K : Set E} (u : E → V) (hu : ContDiff ℝ 3 u)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ 1
      (fun x : E =>
        fderiv ℝ (fun z : E =>
          fderiv ℝ u z ((Module.finBasis ℝ E) j)) x
            ((Module.finBasis ℝ E) i)) K := by
  have hdu : ContDiff ℝ 2 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hj : ContDiff ℝ 2 (fun x : E =>
      fderiv ℝ u x ((Module.finBasis ℝ E) j)) := by
    exact hdu.clm_apply contDiff_const
  have hdj : ContDiff ℝ 1 (fderiv ℝ (fun x : E =>
      fderiv ℝ u x ((Module.finBasis ℝ E) j))) :=
    hj.fderiv_right (by norm_num)
  have hij : ContDiff ℝ 1 (fun x : E =>
      fderiv ℝ (fun z : E =>
        fderiv ℝ u z ((Module.finBasis ℝ E) j)) x
          ((Module.finBasis ℝ E) i)) := by
    exact hdj.clm_apply contDiff_const
  exact hij.contDiffOn

/-! ## The sampled jet producer -/

/-- `C^3` regularity of a vector map and separate Lipschitz control of a
compactly carried coordinate path produce Holder controls for all sampled
value, first-jet, and second-jet fields.  The existential constants are the
finite Lipschitz constants supplied by the compact-carrier theorem; no Holder
estimate is assumed for any of the three jet levels. -/
theorem exists_vectorJet_parabolicHolderControl
    {K : Set E} (u : E → V) (hu : ContDiff ℝ 3 u)
    (hKconv : Convex ℝ K) (hKcompact : IsCompact K)
    (chi : X × T → E) (hchiK : ∀ z, chi z ∈ K)
    {Lχs Lχt : ℝ≥0}
    (hχs : ∀ t ∈ J, LipschitzWith Lχs (fun x : X => chi (x, t)))
    (hχt : ∀ x : X,
      LipschitzOnWith Lχt (fun t : T => chi (x, t)) J) :
    ∃ (LvCs LvCt : ℝ≥0),
      ParabolicHolderControl (fun z => u (chi z)) J LvCs 1 LvCt 1 ∧
      (∀ i, ∃ (LfCs LfCt : ℝ≥0), ParabolicHolderControl
        (fun z => fderiv ℝ u (chi z) ((Module.finBasis ℝ E) i)) J
          LfCs 1 LfCt 1) ∧
      (∀ i j, ∃ (LsCs LsCt : ℝ≥0), ParabolicHolderControl
        (fun z => fderiv ℝ (fun y : E =>
          fderiv ℝ u y ((Module.finBasis ℝ E) j)) (chi z)
            ((Module.finBasis ℝ E) i)) J
          LsCs 1 LsCt 1) := by
  obtain ⟨Lv, hvalue⟩ := exists_parabolicHolderControl_comp_of_contDiffOn
    (J := J) (f := u) (chi := chi)
    (contDiffOn_vectorJet_value (K := K) u hu)
    hKconv hKcompact hchiK hχs hχt
  refine ⟨Lv * Lχs, Lv * Lχt, hvalue, ?_, ?_⟩
  · intro i
    obtain ⟨L, hL⟩ := exists_parabolicHolderControl_comp_of_contDiffOn
      (J := J) (f := fun x : E =>
        fderiv ℝ u x ((Module.finBasis ℝ E) i)) (chi := chi)
      (contDiffOn_vectorJet_first (K := K) u hu i)
      hKconv hKcompact hchiK hχs hχt
    exact ⟨L * Lχs, L * Lχt, by simpa using hL⟩
  · intro i j
    obtain ⟨L, hL⟩ := exists_parabolicHolderControl_comp_of_contDiffOn
      (J := J) (f := fun x : E =>
        fderiv ℝ (fun y : E =>
          fderiv ℝ u y ((Module.finBasis ℝ E) j)) x
            ((Module.finBasis ℝ E) i)) (chi := chi)
      (contDiffOn_vectorJet_second (K := K) u hu i j)
      hKconv hKcompact hchiK hχs hχt
    exact ⟨L * Lχs, L * Lχt, by simpa using hL⟩

end
end ParabolicPDE
end Topping

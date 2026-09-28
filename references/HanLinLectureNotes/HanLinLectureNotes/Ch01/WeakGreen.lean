import HanLinLectureNotes.Ch01.Harmonic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Weak Green identities for Han--Lin Chapter 1

This module keeps the coordinate integration-by-parts layer local to the
Han--Lin project.  It is used by the radial-test proof of the mean-value
formula and does not import `EvansLib`.
-/

open MeasureTheory Metric Set
open scoped Real ContDiff
open InnerProductSpace Laplacian

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- The `i`-th coordinate derivative, written as a Frechet derivative in the
standard Euclidean basis direction. -/
def partialDeriv (i : Fin n) (f : EuclideanSpace Real (Fin n) -> Real) :
    EuclideanSpace Real (Fin n) -> Real :=
  fun x => fderiv Real f x (EuclideanSpace.single i 1)

lemma partialDeriv_apply (i : Fin n) (f : EuclideanSpace Real (Fin n) -> Real)
    (x : EuclideanSpace Real (Fin n)) :
    partialDeriv i f x = fderiv Real f x (EuclideanSpace.single i 1) := rfl

lemma partialDeriv_contDiff {f : EuclideanSpace Real (Fin n) -> Real}
    (hf : ContDiff Real ∞ f) (i : Fin n) :
    ContDiff Real ∞ (partialDeriv i f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

lemma partialDeriv_iterate_two_eq_fderiv_fderiv
    {f : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)}
    (hf : ContDiffAt Real 2 f x) (j : Fin n) :
    (partialDeriv j)^[2] f x =
      fderiv Real (fderiv Real f) x
        (EuclideanSpace.single j 1) (EuclideanSpace.single j 1) := by
  have hdf : DifferentiableAt Real (fderiv Real f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [Function.iterate_succ_apply', Function.iterate_one, partialDeriv_apply]
  have hpj : partialDeriv j f =
      fun y => (fderiv Real f y) (EuclideanSpace.single j 1) := rfl
  rw [hpj, fderiv_clm_apply hdf (differentiableAt_const _)]
  simp

lemma laplacian_eq_sum_partialDeriv_iterate_two
    {f : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)}
    (hf : ContDiffAt Real 2 f x) :
    Δ f x = ∑ j, (partialDeriv j)^[2] f x := by
  have hL : Δ f x = ∑ i, iteratedFDeriv Real 2 f x
      ![EuclideanSpace.basisFun (Fin n) Real i,
        EuclideanSpace.basisFun (Fin n) Real i] :=
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f
      (EuclideanSpace.basisFun (Fin n) Real)) x
  rw [hL]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [EuclideanSpace.basisFun_apply]
  rw [iteratedFDeriv_two_apply, partialDeriv_iterate_two_eq_fderiv_fderiv hf j]
  simp

/-- One-coordinate integration by parts on Euclidean space. -/
theorem integral_mul_partialDeriv_eq_neg (i : Fin n)
    {f g : EuclideanSpace Real (Fin n) -> Real}
    (hf'g : Integrable (fun y => partialDeriv i f y * g y) volume)
    (hfg' : Integrable (fun y => f y * partialDeriv i g y) volume)
    (hfg : Integrable (fun y => f y * g y) volume)
    (hf : ∀ y, y ∈ tsupport g -> DifferentiableAt Real f y)
    (hg : ∀ y, y ∈ tsupport f -> DifferentiableAt Real g y) :
    ∫ y, f y * partialDeriv i g y =
      -∫ y, partialDeriv i f y * g y :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (v := EuclideanSpace.single i 1) hf'g hfg' hfg hf hg

/-- A partial derivative does not enlarge topological support. -/
lemma tsupport_partialDeriv_subset (i : Fin n)
    {f : EuclideanSpace Real (Fin n) -> Real} :
    tsupport (partialDeriv i f) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hxf
  have hzero : f =ᶠ[nhds x] (fun _ => (0 : Real)) := by
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hxf] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  apply hx
  rw [partialDeriv_apply, hzero.fderiv_eq]
  simp

lemma continuous_mul_of_continuousOn_of_tsupport_subset
    {U : Set (EuclideanSpace Real (Fin n))}
    {f g : EuclideanSpace Real (Fin n) -> Real}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Continuous g)
    (hgU : tsupport g ⊆ U) :
    Continuous (fun x => f x * g x) := by
  apply continuousOn_univ.mp
  have hcover : U ∪ (tsupport g)ᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ tsupport g
    · exact Or.inl (hgU hx)
    · exact Or.inr hx
  rw [← hcover]
  apply ContinuousOn.union_of_isOpen (hf.mul hg.continuousOn)
  · refine (continuousOn_const : ContinuousOn
      (fun _ : EuclideanSpace Real (Fin n) => (0 : Real)) (tsupport g)ᶜ).congr ?_
    intro x hx
    simp [image_eq_zero_of_notMem_tsupport hx]
  · exact hU
  · exact (isClosed_tsupport g).isOpen_compl

lemma integrable_mul_of_continuousOn_of_tsupport_subset
    {U : Set (EuclideanSpace Real (Fin n))}
    {f g : EuclideanSpace Real (Fin n) -> Real}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgU : tsupport g ⊆ U) :
    Integrable (fun x => f x * g x) volume := by
  have hcont := continuous_mul_of_continuousOn_of_tsupport_subset hU hf hg hgU
  exact hcont.integrable_of_hasCompactSupport hgc.mul_left

/-- Moving two coordinate derivatives across an integral cancels the two
integration-by-parts signs. -/
theorem integral_mul_partialDeriv_iterate_two_comm (i : Fin n)
    {f g : EuclideanSpace Real (Fin n) -> Real}
    (a1 : Integrable (fun y => partialDeriv i f y * partialDeriv i g y) volume)
    (a2 : Integrable
      (fun y => f y * partialDeriv i (partialDeriv i g) y) volume)
    (a3 : Integrable (fun y => f y * partialDeriv i g y) volume)
    (a4 : ∀ y ∈ tsupport (partialDeriv i g), DifferentiableAt Real f y)
    (a5 : ∀ y ∈ tsupport f, DifferentiableAt Real (partialDeriv i g) y)
    (b1 : Integrable
      (fun y => partialDeriv i (partialDeriv i f) y * g y) volume)
    (b3 : Integrable (fun y => partialDeriv i f y * g y) volume)
    (b4 : ∀ y ∈ tsupport g, DifferentiableAt Real (partialDeriv i f) y)
    (b5 : ∀ y ∈ tsupport (partialDeriv i f), DifferentiableAt Real g y) :
    ∫ y, f y * (partialDeriv i)^[2] g y =
      ∫ y, (partialDeriv i)^[2] f y * g y := by
  simp only [Function.iterate_succ, Function.iterate_zero,
    Function.comp_apply, id_eq]
  rw [integral_mul_partialDeriv_eq_neg i a1 a2 a3 a4 a5,
    integral_mul_partialDeriv_eq_neg i b1 a1 b3 b4 b5, neg_neg]

/-- Two coordinate derivatives can be transferred from a smooth compactly
supported test function to a function which is `C^2` near its support. -/
theorem integral_mul_partialDeriv_iterate_two_comm_of_tsupport (i : Fin n)
    {U : Set (EuclideanSpace Real (Fin n))}
    {u w : EuclideanSpace Real (Fin n) -> Real}
    (hU : IsOpen U) (hu : ContDiffOn Real 2 u U) (hw : ContDiff Real ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * (partialDeriv i)^[2] w y =
      ∫ y, (partialDeriv i)^[2] u y * w y := by
  have hwi : ContDiff Real ∞ (partialDeriv i w) := partialDeriv_contDiff hw i
  have hwii : ContDiff Real ∞ (partialDeriv i (partialDeriv i w)) :=
    partialDeriv_contDiff hwi i
  have hui : ContDiffOn Real 1 (partialDeriv i u) U :=
    ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)
  have huii : ContinuousOn (partialDeriv i (partialDeriv i u)) U :=
    (((hui.fderiv_of_isOpen hU (m := 0) (by norm_num)).clm_apply
      contDiffOn_const).continuousOn)
  have hwiU : tsupport (partialDeriv i w) ⊆ U :=
    (tsupport_partialDeriv_subset i).trans hwU
  have hwiiU : tsupport (partialDeriv i (partialDeriv i w)) ⊆ U :=
    (tsupport_partialDeriv_subset i).trans hwiU
  have hwic : HasCompactSupport (partialDeriv i w) :=
    hwc.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
  have hwiic : HasCompactSupport (partialDeriv i (partialDeriv i w)) :=
    hwic.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
  apply integral_mul_partialDeriv_iterate_two_comm i
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hui.continuousOn
      hwi.continuous hwic hwiU
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hu.continuousOn
      hwii.continuous hwiic hwiiU
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hu.continuousOn
      hwi.continuous hwic hwiU
  · intro y hy
    exact (hu y (hwiU hy)).contDiffAt (hU.mem_nhds (hwiU hy)) |>.differentiableAt
      (by norm_num)
  · intro y _
    exact hwi.differentiable (by norm_num) y
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU huii
      hw.continuous hwc hwU
  · exact integrable_mul_of_continuousOn_of_tsupport_subset hU hui.continuousOn
      hw.continuous hwc hwU
  · intro y hy
    exact (hui y (hwU hy)).contDiffAt (hU.mem_nhds (hwU hy)) |>.differentiableAt
      (by norm_num)
  · intro y _
    exact hw.differentiable (by norm_num) y

/-- Green's second identity in coordinate form, summed over the standard
Euclidean basis. -/
theorem integral_mul_sum_partialDeriv_iterate_two_comm_of_tsupport
    {U : Set (EuclideanSpace Real (Fin n))}
    {u w : EuclideanSpace Real (Fin n) -> Real}
    (hU : IsOpen U) (hu : ContDiffOn Real 2 u U) (hw : ContDiff Real ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * ∑ i, (partialDeriv i)^[2] w y =
      ∫ y, (∑ i, (partialDeriv i)^[2] u y) * w y := by
  classical
  have hleft (i : Fin n) :
      Integrable (fun y => u y * (partialDeriv i)^[2] w y) volume := by
    simp only [Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq]
    have hwi := partialDeriv_contDiff hw i
    have hwii := partialDeriv_contDiff hwi i
    have hwiU : tsupport (partialDeriv i w) ⊆ U :=
      (tsupport_partialDeriv_subset i).trans hwU
    have hwiiU : tsupport (partialDeriv i (partialDeriv i w)) ⊆ U :=
      (tsupport_partialDeriv_subset i).trans hwiU
    have hwic : HasCompactSupport (partialDeriv i w) :=
      hwc.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
    have hwiic : HasCompactSupport (partialDeriv i (partialDeriv i w)) :=
      hwic.of_isClosed_subset (isClosed_tsupport _) (tsupport_partialDeriv_subset i)
    exact integrable_mul_of_continuousOn_of_tsupport_subset hU hu.continuousOn
      hwii.continuous hwiic hwiiU
  have hright (i : Fin n) :
      Integrable (fun y => (partialDeriv i)^[2] u y * w y) volume := by
    simp only [Function.iterate_succ, Function.iterate_zero,
      Function.comp_apply, id_eq]
    have hui : ContDiffOn Real 1 (partialDeriv i u) U :=
      ((hu.fderiv_of_isOpen hU (m := 1) (by norm_num)).clm_apply contDiffOn_const)
    have huii : ContinuousOn (partialDeriv i (partialDeriv i u)) U :=
      (((hui.fderiv_of_isOpen hU (m := 0) (by norm_num)).clm_apply
        contDiffOn_const).continuousOn)
    exact integrable_mul_of_continuousOn_of_tsupport_subset hU huii
      hw.continuous hwc hwU
  calc
    ∫ y, u y * ∑ i, (partialDeriv i)^[2] w y =
        ∫ y, ∑ i, u y * (partialDeriv i)^[2] w y := by
      simp only [Finset.mul_sum]
    _ = ∑ i, ∫ y, u y * (partialDeriv i)^[2] w y := by
      exact integral_finsetSum Finset.univ (fun i _ => hleft i)
    _ = ∑ i, ∫ y, (partialDeriv i)^[2] u y * w y := by
      exact Finset.sum_congr rfl fun i _ =>
        integral_mul_partialDeriv_iterate_two_comm_of_tsupport i hU hu hw hwc hwU
    _ = ∫ y, ∑ i, (partialDeriv i)^[2] u y * w y := by
      exact (integral_finsetSum Finset.univ (fun i _ => hright i)).symm
    _ = ∫ y, (∑ i, (partialDeriv i)^[2] u y) * w y := by
      simp only [Finset.sum_mul]

/-- Green's second identity for a smooth compactly supported test function. -/
theorem integral_mul_laplacian_eq_integral_laplacian_mul
    {U : Set (EuclideanSpace Real (Fin n))}
    {u w : EuclideanSpace Real (Fin n) -> Real}
    (hU : IsOpen U) (hu : ContDiffOn Real 2 u U) (hw : ContDiff Real ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * Δ w y = ∫ y, Δ u y * w y := by
  calc
    ∫ y, u y * Δ w y = ∫ y, u y * ∑ i, (partialDeriv i)^[2] w y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [laplacian_eq_sum_partialDeriv_iterate_two
        (hw.contDiffAt.of_le (WithTop.coe_le_coe.mpr
          (show (2 : ℕ∞) ≤ ⊤ from le_top)))]
    _ = ∫ y, (∑ i, (partialDeriv i)^[2] u y) * w y :=
      integral_mul_sum_partialDeriv_iterate_two_comm_of_tsupport hU hu hw hwc hwU
    _ = ∫ y, Δ u y * w y := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport w
      · have huy : ContDiffAt Real 2 u y :=
          (hu y (hwU hy)).contDiffAt (hU.mem_nhds (hwU hy))
        rw [← laplacian_eq_sum_partialDeriv_iterate_two huy]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero, mul_zero]

/-- A harmonic function annihilates the Laplacian of every smooth compactly
supported test function contained in its harmonicity domain. -/
theorem integral_mul_laplacian_eq_zero_of_harmonicOnNhd
    {U : Set (EuclideanSpace Real (Fin n))}
    {u w : EuclideanSpace Real (Fin n) -> Real}
    (hU : IsOpen U) (hu : HarmonicOnNhd u U) (hw : ContDiff Real ∞ w)
    (hwc : HasCompactSupport w) (hwU : tsupport w ⊆ U) :
    ∫ y, u y * Δ w y = 0 := by
  rw [integral_mul_laplacian_eq_integral_laplacian_mul
    hU hu.contDiffOn hw hwc hwU]
  calc
    ∫ y, Δ u y * w y =
        ∫ _ : EuclideanSpace Real (Fin n), (0 : Real) := by
      apply integral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ tsupport w
      · have hlu : Δ u y = 0 := by
          simpa using (hu y (hwU hy)).2.eq_of_nhds
        rw [hlu, zero_mul]
      · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]
    _ = 0 := by simp

end HanLinLectureNotes.Ch01

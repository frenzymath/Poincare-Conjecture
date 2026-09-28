import HanLinLectureNotes.Ch01.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Moments of Euclidean balls

Symmetry computations for the linear and quadratic moments used in the
averaged Taylor proof of the converse mean-value theorem.
-/

open MeasureTheory Metric Set
open scoped Pointwise

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- A linear isometry of Euclidean space preserves integrals over centred balls. -/
lemma setIntegral_ball_comp_isometry
    (e : EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n))
    (f : EuclideanSpace Real (Fin n) -> Real) (r : Real) :
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, f (e z) =
      ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, f z := by
  have hball : e ⁻¹' ball (0 : EuclideanSpace Real (Fin n)) r =
      ball (0 : EuclideanSpace Real (Fin n)) r := by
    ext z
    simp
  conv_lhs => rw [← hball]
  exact e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding f _

/-- Odd moments vanish on a centred Euclidean ball. -/
lemma setIntegral_ball_clm
    (L : EuclideanSpace Real (Fin n) →L[Real] Real) (r : Real) :
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, L z = 0 := by
  have key : ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, L z =
      - ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, L z := by
    conv_lhs =>
      rw [← setIntegral_ball_comp_isometry (LinearIsometryEquiv.neg Real) L r]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    simp
  linarith

/-- Reflection of one coordinate. -/
def coordReflect (i : Fin n) :
    EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j =>
    if j = i then LinearIsometryEquiv.neg Real
    else LinearIsometryEquiv.refl Real Real

lemma coordReflect_apply (i j : Fin n) (z : EuclideanSpace Real (Fin n)) :
    coordReflect i z j = if j = i then -(z j) else z j := by
  show (LinearIsometryEquiv.piLpCongrRight 2 _ z) j = _
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  by_cases h : j = i <;> simp [h]

/-- Transposition of two coordinates. -/
def coordSwap (i j : Fin n) :
    EuclideanSpace Real (Fin n) ≃ₗᵢ[Real] EuclideanSpace Real (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 Real Real (Equiv.swap i j)

lemma coordSwap_apply (i j k : Fin n) (z : EuclideanSpace Real (Fin n)) :
    coordSwap i j z k = z (Equiv.swap i j k) := by
  show (LinearIsometryEquiv.piLpCongrLeft 2 Real Real (Equiv.swap i j) z) k = _
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft'_apply, Equiv.symm_swap]

/-- All diagonal second moments of a ball agree. -/
lemma setIntegral_ball_mul_self_eq (i j : Fin n) (r : Real) :
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) ^ 2 =
      ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z j) ^ 2 := by
  conv_rhs =>
    rw [← setIntegral_ball_comp_isometry (coordSwap i j) (fun z => (z j) ^ 2) r]
  refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [coordSwap_apply]
  simp [Equiv.swap_apply_right]

/-- Off-diagonal second moments of a ball vanish. -/
lemma setIntegral_ball_mul_of_ne {i j : Fin n} (hij : i ≠ j) (r : Real) :
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) * (z j) = 0 := by
  have key : ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) * (z j) =
      - ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) * (z j) := by
    conv_lhs => rw [← setIntegral_ball_comp_isometry (coordReflect i)
      (fun z => (z i) * (z j)) r]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [coordReflect_apply, coordReflect_apply, if_pos rfl, if_neg hij.symm]
    ring
  linarith

/-- Products of coordinates are integrable on balls. -/
lemma integrable_mul_coords (r : Real) (i j : Fin n) :
    IntegrableOn (fun z : EuclideanSpace Real (Fin n) => (z i) * (z j))
      (ball (0 : EuclideanSpace Real (Fin n)) r) volume := by
  refine integrableOn_ball_of_continuousOn
    (Omega := (univ : Set (EuclideanSpace Real (Fin n)))) ?_ (subset_univ _)
  exact Continuous.continuousOn (by fun_prop)

/-- A continuous bilinear form averages to its trace times a diagonal moment. -/
lemma setIntegral_ball_bilin
    (B : EuclideanSpace Real (Fin n) →L[Real]
      EuclideanSpace Real (Fin n) →L[Real] Real)
    (r : Real) (i0 : Fin n) :
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, B z z =
      (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) *
        ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i0) ^ 2 := by
  have hexp : forall z : EuclideanSpace Real (Fin n), B z z =
      ∑ i, ∑ j, (z i) * (z j) *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro z
    have hz : z = ∑ i, (z i) • EuclideanSpace.single i (1 : Real) := by
      apply (EuclideanSpace.basisFun (Fin n) Real).toBasis.ext_elem
      intro i
      simp
    conv_lhs => rw [hz]
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  calc
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, B z z =
        ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r,
          ∑ i, ∑ j, (z i) * (z j) *
            B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
      setIntegral_congr_fun measurableSet_ball fun z _ => hexp z
    _ = ∑ i, ∑ j,
        (∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) * (z j)) *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
      rw [integral_finsetSum _ fun i _ => ?_]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun j _ => ?_]
        · exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
        · exact (integrable_mul_coords r i j).mul_const _
      · exact integrable_finsetSum _ fun j _ => (integrable_mul_coords r i j).mul_const _
    _ = ∑ i,
        (∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) ^ 2) *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_eq_single i]
      · congr 1
        refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
        ring
      · intro j _ hji
        rw [setIntegral_ball_mul_of_ne (Ne.symm hji), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ i) h
    _ = (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) *
        ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i0) ^ 2 := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [setIntegral_ball_mul_self_eq i i0]
      ring

/-- Scaling of a diagonal second moment. -/
lemma setIntegral_ball_sq_coord_eq_pow {r : Real} (hr : 0 < r) (i : Fin n) :
    ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) ^ 2 =
      r ^ (n + 2) *
        ∫ z in ball (0 : EuclideanSpace Real (Fin n)) 1, (z i) ^ 2 := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (fun z : EuclideanSpace Real (Fin n) => (z i) ^ 2)
    (ball (0 : EuclideanSpace Real (Fin n)) 1) hr
  have hball : r • ball (0 : EuclideanSpace Real (Fin n)) 1 =
      ball (0 : EuclideanSpace Real (Fin n)) r := by
    rw [smul_unitBall hr.ne']
    simp [Real.norm_eq_abs, abs_of_pos hr]
  rw [hball, finrank_euclideanSpace_fin, smul_eq_mul] at h
  have hLHS : ∫ z in ball (0 : EuclideanSpace Real (Fin n)) 1, ((r • z) i) ^ 2 =
      r ^ 2 * ∫ z in ball (0 : EuclideanSpace Real (Fin n)) 1, (z i) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    have hz : (r • z) i = r * z i := by simp
    rw [hz]
    ring
  rw [hLHS] at h
  have hrn : (0 : Real) < r ^ n := by positivity
  have hfin : r ^ n *
      (r ^ 2 * ∫ z in ball (0 : EuclideanSpace Real (Fin n)) 1, (z i) ^ 2) =
        ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) ^ 2 := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul]
  rw [← hfin, pow_add]
  ring

/-- A diagonal second moment has positive integral on a positive-radius ball. -/
lemma setIntegral_ball_sq_coord_pos {r : Real} (hr : 0 < r) (i : Fin n) :
    0 < ∫ z in ball (0 : EuclideanSpace Real (Fin n)) r, (z i) ^ 2 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball (0 : EuclideanSpace Real (Fin n)) r)]
      fun z : EuclideanSpace Real (Fin n) => (z i) ^ 2 :=
    ae_of_all _ fun z => sq_nonneg _
  have hint : IntegrableOn (fun z : EuclideanSpace Real (Fin n) => (z i) ^ 2)
      (ball (0 : EuclideanSpace Real (Fin n)) r) volume := by
    have h := integrable_mul_coords r i i
    simpa [sq] using h
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  set K : Submodule Real (EuclideanSpace Real (Fin n)) :=
    LinearMap.ker ((EuclideanSpace.proj i :
      EuclideanSpace Real (Fin n) →L[Real] Real) :
        EuclideanSpace Real (Fin n) →ₗ[Real] Real) with hK
  have hKne : K ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single i (1 : Real) ∈ K :=
      htop ▸ Submodule.mem_top
    rw [hK, LinearMap.mem_ker] at hmem
    simp at hmem
  have hset :
      (Function.support fun z : EuclideanSpace Real (Fin n) => (z i) ^ 2) ∩
          ball (0 : EuclideanSpace Real (Fin n)) r =
        ball (0 : EuclideanSpace Real (Fin n)) r \ (K : Set (EuclideanSpace Real (Fin n))) := by
    ext z
    simp only [mem_inter_iff, mem_sdiff, Function.mem_support, SetLike.mem_coe, hK,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe, PiLp.proj_apply,
      ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true]
    tauto
  rw [hset, measure_sdiff_null (Measure.addHaar_submodule volume K hKne)]
  exact measure_ball_pos volume _ hr

end HanLinLectureNotes.Ch01

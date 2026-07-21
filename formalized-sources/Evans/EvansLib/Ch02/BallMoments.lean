import EvansLib.Ch02.MeanValue
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Moments of Euclidean balls

Symmetry computations for integrals of linear and quadratic forms over balls
`B(0,r) ⊆ ℝⁿ`, the analytic input to the averaged Taylor expansion behind the
converse mean-value property (Evans §2.2.2 Thm 3):

* `EvansLib.setIntegral_ball_clm` — **odd moments vanish**: `∫_{B(0,r)} L z dz = 0`
  for every linear functional `L` (reflection `z ↦ -z`).
* `EvansLib.setIntegral_ball_mul_self_eq` — the diagonal second moments agree in
  every coordinate (coordinate transposition).
* `EvansLib.setIntegral_ball_mul_of_ne` — the off-diagonal second moments vanish
  (reflection of a single coordinate).
* `EvansLib.setIntegral_ball_bilin` — consequently a continuous bilinear form
  averages to its trace: `∫_{B(0,r)} B(z,z) dz = (∑ᵢ B(eᵢ,eᵢ)) · κᵣ` where
  `κᵣ = ∫_{B(0,r)} z₀² dz`.
* `EvansLib.setIntegral_ball_sq_coord_pos`, `..._eq_pow` — `κᵣ = r^{n+2} κ₁ > 0`
  (scaling `z ↦ r z`; positivity because a hyperplane is Lebesgue-null).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.2.
-/

open MeasureTheory Metric Set
open scoped Pointwise

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## Transfer of ball integrals along linear isometries -/

/-- A linear isometry of `ℝⁿ` preserves integrals over centred balls. -/
lemma setIntegral_ball_comp_isometry
    (e : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (r : ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, f (e z) =
      ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, f z := by
  have hball : e ⁻¹' ball (0 : EuclideanSpace ℝ (Fin n)) r =
      ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    ext z
    simp
  conv_lhs => rw [← hball]
  exact e.measurePreserving.setIntegral_preimage_emb
    e.toHomeomorph.measurableEmbedding f _

/-! ## Odd moments vanish -/

/-- **Odd moments vanish**: the integral of a linear functional over a centred ball is
zero, by the reflection `z ↦ -z`. -/
lemma setIntegral_ball_clm (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (r : ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, L z = 0 := by
  have key : ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, L z =
      - ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, L z := by
    conv_lhs => rw [← setIntegral_ball_comp_isometry (LinearIsometryEquiv.neg ℝ) L r]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    simp
  linarith

/-! ## Second moments: reflections and transpositions -/

/-- Reflection of the `i`-th coordinate, as a linear isometry of `ℝⁿ`. -/
def coordReflect (i : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrRight 2 fun j =>
    if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

lemma coordReflect_apply (i j : Fin n) (z : EuclideanSpace ℝ (Fin n)) :
    coordReflect i z j = if j = i then -(z j) else z j := by
  show (LinearIsometryEquiv.piLpCongrRight 2 _ z) j = _
  rw [LinearIsometryEquiv.piLpCongrRight_apply]
  by_cases h : j = i <;> simp [h]

/-- Transposition of the `i`-th and `j`-th coordinates, as a linear isometry of `ℝⁿ`. -/
def coordSwap (i j : Fin n) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)

lemma coordSwap_apply (i j k : Fin n) (z : EuclideanSpace ℝ (Fin n)) :
    coordSwap i j z k = z (Equiv.swap i j k) := by
  show (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j) z) k = _
  rw [LinearIsometryEquiv.piLpCongrLeft_apply]
  simp [Equiv.piCongrLeft'_apply, Equiv.symm_swap]

/-- The diagonal second moments of a ball agree in every pair of coordinates. -/
lemma setIntegral_ball_mul_self_eq (i j : Fin n) (r : ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) ^ 2 =
      ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z j) ^ 2 := by
  conv_rhs => rw [← setIntegral_ball_comp_isometry (coordSwap i j) (fun z => (z j) ^ 2) r]
  refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [coordSwap_apply]
  simp [Equiv.swap_apply_right]

/-- The off-diagonal second moments of a ball vanish. -/
lemma setIntegral_ball_mul_of_ne {i j : Fin n} (hij : i ≠ j) (r : ℝ) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) * (z j) = 0 := by
  have key : ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) * (z j) =
      - ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) * (z j) := by
    conv_lhs => rw [← setIntegral_ball_comp_isometry (coordReflect i)
      (fun z => (z i) * (z j)) r]
    rw [← integral_neg]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    rw [coordReflect_apply, coordReflect_apply, if_pos rfl, if_neg hij.symm]
    ring
  linarith

/-- Products of coordinates are integrable on balls. -/
lemma integrable_mul_coords (r : ℝ) (i j : Fin n) :
    IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => (z i) * (z j))
      (ball (0 : EuclideanSpace ℝ (Fin n)) r) volume := by
  refine integrableOn_ball_of_continuousOn (U := (univ : Set (EuclideanSpace ℝ (Fin n))))
    ?_ (subset_univ _)
  exact Continuous.continuousOn (by fun_prop)

/-! ## The trace formula for quadratic forms -/

/-- A continuous bilinear form averages over a centred ball to its trace times the
common diagonal second moment `κᵣ = ∫_{B(0,r)} z₀² dz`:
`∫_{B(0,r)} B(z,z) dz = (∑ᵢ B(eᵢ,eᵢ)) κᵣ`. Stated with an arbitrary reference
coordinate `i₀`. -/
lemma setIntegral_ball_bilin
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (r : ℝ) (i₀ : Fin n) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, B z z =
      (∑ i, B (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)) *
        ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i₀) ^ 2 := by
  -- expand `z` in the standard basis inside the bilinear form
  have hexp : ∀ z : EuclideanSpace ℝ (Fin n), B z z =
      ∑ i, ∑ j, (z i) * (z j) *
        B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
    intro z
    have hz : z = ∑ i, (z i) • EuclideanSpace.single i (1 : ℝ) := by
      apply (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.ext_elem
      intro i
      simp
    conv_lhs => rw [hz]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  -- integrate term by term; only the diagonal survives
  calc ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, B z z
      = ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, ∑ i, ∑ j, (z i) * (z j) *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) :=
        setIntegral_congr_fun measurableSet_ball fun z _ => hexp z
    _ = ∑ i, ∑ j, (∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) * (z j)) *
          B (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := by
        rw [integral_finsetSum _ fun i _ => ?_]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => ?_]
          · exact Finset.sum_congr rfl fun j _ => integral_mul_const _ _
          · exact ((integrable_mul_coords r i j).mul_const _)
        · exact integrable_finsetSum _ fun j _ => (integrable_mul_coords r i j).mul_const _
    _ = ∑ i, (∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) ^ 2) *
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
          ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i₀) ^ 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [setIntegral_ball_mul_self_eq i i₀]
        ring

/-! ## Scaling and positivity of the second moment -/

/-- Scaling of the diagonal second moment: `κᵣ = r^(n+2) κ₁`. -/
lemma setIntegral_ball_sq_coord_eq_pow {r : ℝ} (hr : 0 < r) (i : Fin n) :
    ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) ^ 2 =
      r ^ (n + 2) * ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) 1, (z i) ^ 2 := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := volume)
    (fun z : EuclideanSpace ℝ (Fin n) => (z i) ^ 2)
    (ball (0 : EuclideanSpace ℝ (Fin n)) 1) hr
  have hball : r • ball (0 : EuclideanSpace ℝ (Fin n)) 1 =
      ball (0 : EuclideanSpace ℝ (Fin n)) r := by
    rw [smul_unitBall hr.ne']
    simp [Real.norm_eq_abs, abs_of_pos hr]
  rw [hball, finrank_euclideanSpace_fin, smul_eq_mul] at h
  have hLHS : ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) 1, ((r • z) i) ^ 2 =
      r ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) 1, (z i) ^ 2 := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
    have hz : (r • z) i = r * z i := by simp
    rw [hz]; ring
  rw [hLHS] at h
  have hrn : (0 : ℝ) < r ^ n := by positivity
  have hfin : r ^ n * (r ^ 2 * ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) 1, (z i) ^ 2) =
      ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) ^ 2 := by
    rw [h, ← mul_assoc, mul_inv_cancel₀ hrn.ne', one_mul]
  rw [← hfin, pow_add]
  ring

/-- Positivity of the diagonal second moment: `κᵣ > 0` (the coordinate hyperplane is
Lebesgue-null). -/
lemma setIntegral_ball_sq_coord_pos {r : ℝ} (hr : 0 < r) (i : Fin n) :
    0 < ∫ z in ball (0 : EuclideanSpace ℝ (Fin n)) r, (z i) ^ 2 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball (0 : EuclideanSpace ℝ (Fin n)) r)]
      fun z : EuclideanSpace ℝ (Fin n) => (z i) ^ 2 :=
    ae_of_all _ fun z => sq_nonneg _
  have hint : IntegrableOn (fun z : EuclideanSpace ℝ (Fin n) => (z i) ^ 2)
      (ball (0 : EuclideanSpace ℝ (Fin n)) r) volume := by
    have := integrable_mul_coords r i i
    simpa [sq] using this
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnonneg hint]
  -- the support misses only the coordinate hyperplane, a null set
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
    LinearMap.ker ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
      EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) with hK
  have hKne : K ≠ ⊤ := by
    intro htop
    have hmem : EuclideanSpace.single i (1 : ℝ) ∈ K := htop ▸ Submodule.mem_top
    rw [hK, LinearMap.mem_ker] at hmem
    simp at hmem
  have hset : (Function.support fun z : EuclideanSpace ℝ (Fin n) => (z i) ^ 2) ∩
      ball (0 : EuclideanSpace ℝ (Fin n)) r =
      ball (0 : EuclideanSpace ℝ (Fin n)) r \ (K : Set (EuclideanSpace ℝ (Fin n))) := by
    ext z
    simp only [mem_inter_iff, mem_diff, Function.mem_support, SetLike.mem_coe, hK,
      LinearMap.mem_ker, ContinuousLinearMap.coe_coe, PiLp.proj_apply,
      ne_eq, pow_eq_zero_iff, OfNat.ofNat_ne_zero, not_false_eq_true]
    tauto
  rw [hset, measure_diff_null (Measure.addHaar_submodule volume K hKne)]
  exact measure_ball_pos volume _ hr

end EvansLib

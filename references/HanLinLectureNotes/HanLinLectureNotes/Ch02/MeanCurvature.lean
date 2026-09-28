import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Han--Lin Chapter 2: the prescribed mean-curvature example

Algebraic identities for the coefficient matrix and normalized lower-order
term in Example 2.37.
-/

open Filter MeasureTheory Set
open scoped BigOperators Topology

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The coefficient matrix of the prescribed mean-curvature equation. -/
def meanCurvatureCoefficient {n : Nat} (p : EuclideanSpace Real (Fin n)) :
    Matrix (Fin n) (Fin n) Real :=
  (1 + ‖p‖ ^ 2) • (1 : Matrix (Fin n) (Fin n) Real) -
    Matrix.vecMulVec p.ofLp p.ofLp

@[simp]
theorem meanCurvatureCoefficient_apply {n : Nat}
    (p : EuclideanSpace Real (Fin n)) (i j : Fin n) :
    meanCurvatureCoefficient p i j =
      (1 + ‖p‖ ^ 2) * (if i = j then 1 else 0) - p i * p j := by
  simp [meanCurvatureCoefficient, Matrix.one_apply, Matrix.vecMulVec]

private lemma det_one_add_vecMulVec
    {ι : Type} [Fintype ι] [DecidableEq ι] (u v : ι -> Real) :
    (1 + Matrix.vecMulVec u v).det = 1 + v ⬝ᵥ u := by
  rw [Matrix.vecMulVec_eq Unit]
  exact Matrix.det_one_add_replicateCol_mul_replicateRow u v

/-- The determinant of the prescribed mean-curvature coefficient matrix. -/
theorem det_meanCurvatureCoefficient {n : Nat} (hn : 0 < n)
    (p : EuclideanSpace Real (Fin n)) :
    (meanCurvatureCoefficient p).det = (1 + ‖p‖ ^ 2) ^ (n - 1) := by
  let c : Real := 1 + ‖p‖ ^ 2
  have hc : c ≠ 0 := by
    dsimp only [c]
    positivity
  have hfactor :
      meanCurvatureCoefficient p =
        c • (1 + Matrix.vecMulVec ((-c⁻¹) • p.ofLp) p.ofLp) := by
    ext i j
    simp [meanCurvatureCoefficient, c, Matrix.one_apply, Matrix.vecMulVec]
    split_ifs <;> field_simp <;> ring
  have hnorm : p.ofLp ⬝ᵥ p.ofLp = ‖p‖ ^ 2 := by
    rw [dotProduct]
    calc
      (∑ i, p.ofLp i * p.ofLp i) = ∑ i, p.ofLp i ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ‖p‖ ^ 2 := by
        simpa only [Real.norm_eq_abs, sq_abs] using
          (EuclideanSpace.norm_sq_eq p).symm
  rw [hfactor, Matrix.det_smul, Fintype.card_fin,
    det_one_add_vecMulVec, dotProduct_smul, hnorm]
  simp only [smul_eq_mul]
  change c ^ n * (1 + -c⁻¹ * ‖p‖ ^ 2) = c ^ (n - 1)
  have hnormc : ‖p‖ ^ 2 = c - 1 := by
    dsimp only [c]
    ring
  rw [hnormc]
  have hinner : 1 + -c⁻¹ * (c - 1) = c⁻¹ := by
    field_simp
    ring
  rw [hinner]
  calc
    c ^ n * c⁻¹ = c ^ ((n - 1) + 1) * c⁻¹ := by
      congr 2
      omega
    _ = c ^ (n - 1) := by
      rw [pow_succ]
      field_simp

/-- The lower-order term in the prescribed mean-curvature equation. -/
def meanCurvatureForcing (n : Nat) (H : Real) {m : Nat}
    (p : EuclideanSpace Real (Fin m)) : Real :=
  -(n : Real) * H * (1 + ‖p‖ ^ 2) ^ (3 / 2 : Real)

/-- The positive `n`th root of the coefficient determinant. -/
def meanCurvatureDetRoot (n : Nat) {m : Nat}
    (p : EuclideanSpace Real (Fin m)) : Real :=
  (1 + ‖p‖ ^ 2) ^ (((n : Real) - 1) / (n : Real))

/-- The normalized lower-order term has the exponent appearing in Example 2.37. -/
theorem abs_meanCurvatureForcing_div_detRoot
    {n : Nat} (hn : 0 < n) (H : Real)
    (p : EuclideanSpace Real (Fin n)) :
    |meanCurvatureForcing n H p| /
        ((n : Real) * meanCurvatureDetRoot n p) =
      |H| * (1 + ‖p‖ ^ 2) ^ (((n : Real) + 2) / (2 * (n : Real))) := by
  let c : Real := 1 + ‖p‖ ^ 2
  have hc : 0 < c := by
    dsimp only [c]
    positivity
  have hnR : 0 < (n : Real) := by exact_mod_cast hn
  rw [meanCurvatureForcing, meanCurvatureDetRoot]
  change
    |-(n : Real) * H * c ^ (3 / 2 : Real)| /
          ((n : Real) * c ^ (((n : Real) - 1) / (n : Real))) =
      |H| * c ^ (((n : Real) + 2) / (2 * (n : Real)))
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos hnR,
    Real.abs_rpow_of_nonneg hc.le, abs_of_pos hc]
  have hpow : c ^ (((n : Real) - 1) / (n : Real)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hc _)
  have hn0 : (n : Real) ≠ 0 := ne_of_gt hnR
  have hexponent :
      (3 / 2 : Real) - ((n : Real) - 1) / (n : Real) =
        ((n : Real) + 2) / (2 * (n : Real)) := by
    field_simp [hn0]
    ring
  calc
    (n : Real) * |H| * c ^ (3 / 2 : Real) /
          ((n : Real) * c ^ (((n : Real) - 1) / (n : Real))) =
        |H| * (c ^ (3 / 2 : Real) /
          c ^ (((n : Real) - 1) / (n : Real))) := by
      field_simp [hn0, hpow]
    _ = |H| * c ^ ((3 / 2 : Real) - ((n : Real) - 1) / (n : Real)) := by
      rw [Real.rpow_sub hc]
    _ = |H| * c ^ (((n : Real) + 2) / (2 * (n : Real))) := by
      rw [hexponent]

private lemma meanCurvatureRadialNormalizedIdentity
    (n : Nat) (x : Real) (hx : 0 < x) :
    x ^ n * (1 + x ^ 2) ^ (-((n : Real) / 2)) =
      (x ^ 2 / (1 + x ^ 2)) ^ ((n : Real) / 2) := by
  rw [Real.div_rpow (sq_nonneg x) (by positivity)]
  rw [← Real.rpow_two x, ← Real.rpow_mul hx.le]
  rw [show (2 : Real) * ((n : Real) / 2) = (n : Real) by ring,
    Real.rpow_natCast]
  rw [Real.rpow_neg (by positivity)]
  simp only [div_eq_mul_inv]

private lemma meanCurvatureRadialAntiderivative_tendsto (n : Nat) :
    Tendsto
      (fun x : Real => x ^ n * (1 + x ^ 2) ^ (-((n : Real) / 2)))
      atTop (nhds 1) := by
  have hsq : Tendsto (fun x : Real => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have hone : Tendsto (fun _ : Real => (1 : Real)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hden : Tendsto (fun x : Real => 1 + x ^ 2) atTop atTop :=
    (hsq.atTop_add hone).congr (fun x => by ring)
  have hinv : Tendsto (fun x : Real => (1 + x ^ 2)⁻¹) atTop (nhds 0) :=
    hden.inv_tendsto_atTop
  have hq : Tendsto (fun x : Real => x ^ 2 / (1 + x ^ 2)) atTop (nhds 1) := by
    convert hinv.const_sub 1 using 1
    · funext x
      field_simp
      ring
    · norm_num
  have hnormalized :
      Tendsto
        (fun x : Real => (x ^ 2 / (1 + x ^ 2)) ^ ((n : Real) / 2))
        atTop (nhds 1) := by
    simpa using hq.rpow_const (p := (n : Real) / 2) (Or.inl one_ne_zero)
  apply hnormalized.congr'
  filter_upwards [Ioi_mem_atTop (0 : Real)] with x hx
  exact (meanCurvatureRadialNormalizedIdentity n x hx).symm

/-- The one-dimensional radial integral in the mean-curvature weight is normalized to one. -/
theorem meanCurvatureRadialIntegral (n : Nat) (hn : 0 < n) :
    ∫ x in Ioi (0 : Real),
        (n : Real) * (x ^ (n - 1) *
          (1 + x ^ 2) ^ (-(((n : Real) + 2) / 2))) = 1 := by
  let g : Real → Real :=
    fun x => x ^ n * (1 + x ^ 2) ^ (-((n : Real) / 2))
  let g' : Real → Real :=
    fun x => (n : Real) * (x ^ (n - 1) *
      (1 + x ^ 2) ^ (-(((n : Real) + 2) / 2)))
  have hcont : ContinuousWithinAt g (Ici 0) 0 := by
    dsimp only [g]
    exact ((continuousAt_id.pow n).mul
      ((continuousAt_const.add (continuousAt_id.pow 2)).rpow_const
        (Or.inl (by norm_num)))).continuousWithinAt
  have hderiv : ∀ x ∈ Ioi (0 : Real), HasDerivAt g (g' x) x := by
    intro x hx
    have hb : (1 + x ^ 2 : Real) ≠ 0 := by positivity
    have h :=
      ((hasDerivAt_id x).pow n).mul
        (((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)).rpow_const
          (p := -((n : Real) / 2)) (Or.inl hb))
    have hcoeff :
        (n : Real) * x ^ (n - 1) * 1 * (1 + x ^ 2) ^ (-((n : Real) / 2)) +
          x ^ n * ((0 + (2 : Real) * x ^ (2 - 1) * 1) * (-((n : Real) / 2)) *
            (1 + x ^ 2) ^ (-((n : Real) / 2) - 1)) =
        (n : Real) * (x ^ (n - 1) *
          (1 + x ^ 2) ^ (-(((n : Real) + 2) / 2))) := by
      rw [show -((n : Real) / 2) =
            -(((n : Real) + 2) / 2) + 1 by ring,
          Real.rpow_add (by positivity), Real.rpow_one]
      have hpowstep : x ^ n = x ^ (n - 1) * x := by
        calc
          x ^ n = x ^ ((n - 1) + 1) := by congr 1; omega
          _ = x ^ (n - 1) * x := by simpa using (pow_succ x (n - 1))
      rw [hpowstep]
      norm_num
      ring
    change HasDerivAt
      (id ^ n * fun y : Real => (1 + y ^ 2) ^ (-((n : Real) / 2)))
      ((n : Real) * (x ^ (n - 1) *
        (1 + x ^ 2) ^ (-(((n : Real) + 2) / 2)))) x
    exact h.congr_deriv hcoeff
  have hnonneg : ∀ x ∈ Ioi (0 : Real), 0 ≤ g' x := by
    intro x hx
    dsimp only [g']
    exact mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg hx.le _)
        (Real.rpow_nonneg (by positivity) _))
  have hlim : Tendsto g atTop (nhds 1) :=
    meanCurvatureRadialAntiderivative_tendsto n
  have hFTC :=
    integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim
  dsimp only [g'] at hFTC
  simpa [g, hn.ne'] using hFTC

/-- The weight from Example 2.37 integrates to the volume of the unit ball. -/
theorem meanCurvatureWeightIntegral (n : Nat) (hn : 0 < n) :
    ∫ p : EuclideanSpace Real (Fin n),
        (1 + ‖p‖ ^ 2) ^ (-(((n : Real) + 2) / 2)) =
      volume.real (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  have hrad := meanCurvatureRadialIntegral n hn
  rw [integral_fun_norm_addHaar
    (volume : Measure (EuclideanSpace Real (Fin n)))
    (fun r : Real => (1 + r ^ 2) ^ (-(((n : Real) + 2) / 2)))]
  rw [finrank_euclideanSpace_fin]
  simp only [nsmul_eq_mul, smul_eq_mul]
  rw [integral_const_mul] at hrad
  calc
    (n : Real) * (volume.real (Metric.ball
          (0 : EuclideanSpace Real (Fin n)) 1) *
        ∫ y in Ioi (0 : Real), y ^ (n - 1) *
          (1 + y ^ 2) ^ (-(((n : Real) + 2) / 2))) =
      volume.real (Metric.ball
          (0 : EuclideanSpace Real (Fin n)) 1) *
        ((n : Real) * ∫ y in Ioi (0 : Real), y ^ (n - 1) *
          (1 + y ^ 2) ^ (-(((n : Real) + 2) / 2))) := by ring
    _ = volume.real (Metric.ball
          (0 : EuclideanSpace Real (Fin n)) 1) * 1 := by rw [hrad]
    _ = volume.real (Metric.ball
          (0 : EuclideanSpace Real (Fin n)) 1) := by ring

/-- All coefficient and weight identities in the prescribed mean-curvature example. -/
theorem prescribedMeanCurvatureExample
    {n : Nat} (hn : 0 < n) (H : Real)
    (p : EuclideanSpace Real (Fin n)) :
    (∀ i j : Fin n,
      meanCurvatureCoefficient p i j =
        (1 + ‖p‖ ^ 2) * (if i = j then 1 else 0) - p i * p j) ∧
    meanCurvatureForcing n H p =
      -(n : Real) * H * (1 + ‖p‖ ^ 2) ^ (3 / 2 : Real) ∧
    (meanCurvatureCoefficient p).det = (1 + ‖p‖ ^ 2) ^ (n - 1) ∧
    meanCurvatureDetRoot n p =
      (1 + ‖p‖ ^ 2) ^ (((n : Real) - 1) / (n : Real)) ∧
    |meanCurvatureForcing n H p| /
        ((n : Real) * meanCurvatureDetRoot n p) =
      |H| * (1 + ‖p‖ ^ 2) ^ (((n : Real) + 2) / (2 * (n : Real))) ∧
    (∫ q : EuclideanSpace Real (Fin n),
        (1 + ‖q‖ ^ 2) ^ (-(((n : Real) + 2) / 2))) =
      volume.real (Metric.ball (0 : EuclideanSpace Real (Fin n)) 1) := by
  exact ⟨meanCurvatureCoefficient_apply p,
    rfl,
    det_meanCurvatureCoefficient hn p,
    rfl,
    abs_meanCurvatureForcing_div_detRoot hn H p,
    meanCurvatureWeightIntegral n hn⟩

end HanLinLectureNotes.Ch02

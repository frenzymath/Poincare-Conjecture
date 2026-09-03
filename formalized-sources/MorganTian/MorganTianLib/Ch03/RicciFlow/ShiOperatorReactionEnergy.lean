import MorganTianLib.Ch03.RicciFlow.ShiOperatorEnergy

/-!
# Morgan--Tian Ch. 3 -- finite reaction bounds from energy

The curvature-operator evolution is a finite contraction in a moving frame.
`ShiOperatorEnergy` bounds that contraction from entrywise estimates.  This
file supplies the small coercive bridge needed to use the Frobenius energy
itself as the entrywise bound, and packages the resulting cubic reaction
estimate.  The statements are algebraic; the geometric evolution and
commutation inputs remain explicit in the preceding interfaces.
-/

open Matrix

noncomputable section

namespace MorganTianLib

/-- **Math.** The finite absolute mass of a three-index array of structure
constants. -/
def curvatureStructureBound {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) : ℝ :=
  ∑ a, ∑ b, ∑ d, |c a b d|

theorem curvatureStructureBound_nonneg
    {ι : Type*} [Fintype ι] (c : ι → ι → ι → ℝ) :
    0 ≤ curvatureStructureBound c := by
  classical
  unfold curvatureStructureBound
  positivity

/-- **Math.** Every structure coefficient is bounded by the finite absolute
mass. -/
theorem abs_curvatureStructure_le
    {ι : Type*} [Fintype ι] (c : ι → ι → ι → ℝ) (a b d : ι) :
    |c a b d| ≤ curvatureStructureBound c := by
  classical
  unfold curvatureStructureBound
  have hd : |c a b d| ≤ ∑ d', |c a b d'| := by
    exact Finset.single_le_sum
      (fun d' _ => show 0 ≤ |c a b d'| from abs_nonneg _)
      (Finset.mem_univ d)
  have hb : (∑ d', |c a b d'|) ≤ ∑ b', ∑ d', |c a b' d'| := by
    exact Finset.single_le_sum
      (fun b' _ => Finset.sum_nonneg
        (fun d' _ => show 0 ≤ |c a b' d'| from abs_nonneg _))
      (Finset.mem_univ b)
  have ha : (∑ b', ∑ d', |c a b' d'|) ≤
      ∑ a', ∑ b', ∑ d', |c a' b' d'| := by
    exact Finset.single_le_sum
      (fun a' _ => Finset.sum_nonneg (fun b' _ =>
        Finset.sum_nonneg
          (fun d' _ => show 0 ≤ |c a' b' d'| from abs_nonneg _)))
      (Finset.mem_univ a)
  exact hd.trans (hb.trans ha)

/-- **Math.** The Frobenius energy is nonnegative. -/
theorem curvatureOperatorEnergy_nonneg
    {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) :
    0 ≤ curvatureOperatorEnergy T := by
  classical
  unfold curvatureOperatorEnergy
  positivity

/-- **Math.** One matrix entry square is bounded by the Frobenius energy. -/
theorem curvatureOperatorEnergy_entry_sq_le
    {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) (a b : ι) :
    (T a b) ^ 2 ≤ curvatureOperatorEnergy T := by
  classical
  unfold curvatureOperatorEnergy
  have hb : (T a b) ^ 2 ≤ ∑ b', (T a b') ^ 2 := by
    exact Finset.single_le_sum (fun b' _ => sq_nonneg _) (Finset.mem_univ b)
  have ha : (∑ b', (T a b') ^ 2) ≤ ∑ a', ∑ b', (T a' b') ^ 2 := by
    exact Finset.single_le_sum
      (fun a' _ => Finset.sum_nonneg (fun b' _ => sq_nonneg _))
      (Finset.mem_univ a)
  exact hb.trans ha

/-- **Math.** The absolute value of an entry is bounded by the square root of the
Frobenius energy. -/
theorem abs_curvatureOperator_entry_le_sqrt_energy
    {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) (a b : ι) :
    |T a b| ≤ Real.sqrt (curvatureOperatorEnergy T) := by
  apply (Real.le_sqrt (abs_nonneg _) (curvatureOperatorEnergy_nonneg T)).2
  simpa [sq_abs] using curvatureOperatorEnergy_entry_sq_le T a b

/-- **Math.** The finite reaction pairing is controlled directly by operator energy and
the absolute mass of its structure constants. -/
theorem abs_curvatureOperatorReactionPairing_le_of_energy
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) :
    |∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| ≤
      (Fintype.card ι : ℝ) ^ 2 *
        (Real.sqrt (curvatureOperatorEnergy T)) ^ 3 *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) := by
  let B : ℝ := Real.sqrt (curvatureOperatorEnergy T)
  let C : ℝ := curvatureStructureBound c
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact curvatureStructureBound_nonneg c
  have hT : ∀ a b, |T a b| ≤ B := by
    intro a b
    exact abs_curvatureOperator_entry_le_sqrt_energy T a b
  have hc : ∀ a b d, |c a b d| ≤ C := by
    intro a b d
    exact abs_curvatureStructure_le c a b d
  have h := abs_curvatureOperatorReactionPairing_le_of_entrywise_bound
    c T hB hC hT hc
  simpa [B, C] using h

/-- **Math.** The factor-two reaction contribution in the energy derivative, expressed
only through the Frobenius energy and the finite structure bound. -/
theorem abs_two_mul_curvatureOperatorReactionPairing_le_of_energy
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) :
    |2 * ∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| ≤
      2 * (Fintype.card ι : ℝ) ^ 2 *
        (Real.sqrt (curvatureOperatorEnergy T)) ^ 3 *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) := by
  have h := abs_curvatureOperatorReactionPairing_le_of_energy c T
  rw [abs_mul]
  simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc] using
    (mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2))

/-- **Math.** Along the finite curvature-operator evolution, the energy
derivative after subtracting the Laplacian pairing is bounded by an explicit
cubic expression in the energy.  This discharges the auxiliary entrywise
bounds in `abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le`.
-/
theorem abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le_of_energy
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t : ℝ}
    (hdiff : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c) :
    |deriv (fun s => curvatureOperatorEnergy (T s)) t -
        2 * ∑ a, ∑ b, T t a b * lap t a b| ≤
      2 * (Fintype.card ι : ℝ) ^ 2 *
        (Real.sqrt (curvatureOperatorEnergy (T t))) ^ 3 *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) := by
  let B : ℝ := Real.sqrt (curvatureOperatorEnergy (T t))
  let C : ℝ := curvatureStructureBound c
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Real.sqrt_nonneg _
  have hC : 0 ≤ C := by
    dsimp [C]
    exact curvatureStructureBound_nonneg c
  have hT : ∀ a b, |T t a b| ≤ B := by
    intro a b
    exact abs_curvatureOperator_entry_le_sqrt_energy (T t) a b
  have hc : ∀ a b d, |c a b d| ≤ C := by
    intro a b d
    exact abs_curvatureStructure_le c a b d
  have h := abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le
    hdiff hevol hB hC hT hc
  simpa [B, C] using h

end MorganTianLib

end

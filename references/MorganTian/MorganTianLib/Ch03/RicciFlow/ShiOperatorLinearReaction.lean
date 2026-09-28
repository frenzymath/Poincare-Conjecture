import MorganTianLib.Ch03.RicciFlow.ShiOperatorReactionEnergy

/-!
# Morgan--Tian Ch. 3 -- linearising the curvature reaction shell

The finite curvature-operator calculation gives a cubic bound for the reaction
part of the Frobenius energy evolution.  On a time slab where the operator
energy has a fixed square-root bound, that cubic term is linear in the energy.
This is the form consumed by a Shi tower inequality.  The geometric
identification of the operator and the Laplacian pairing is intentionally left
as an explicit input to the surrounding evolution interfaces.
-/

open Matrix

noncomputable section

namespace MorganTianLib

/-! ## Cubic-to-linear arithmetic -/

/-- **Math.** A nonnegative Frobenius energy with square-root at most `B` has
its cubic square-root term bounded by `B` times the energy. -/
theorem curvatureOperatorEnergy_sqrt_cube_le_mul_of_sqrt_le
    {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) {B : ℝ}
    (_hB : 0 ≤ B)
    (hbound : Real.sqrt (curvatureOperatorEnergy T) ≤ B) :
    (Real.sqrt (curvatureOperatorEnergy T)) ^ 3 ≤
      B * curvatureOperatorEnergy T := by
  have henergy : 0 ≤ curvatureOperatorEnergy T :=
    curvatureOperatorEnergy_nonneg T
  have hsquare : (Real.sqrt (curvatureOperatorEnergy T)) ^ 2 =
      curvatureOperatorEnergy T :=
    Real.sq_sqrt henergy
  have hmul := mul_le_mul_of_nonneg_right hbound
    (sq_nonneg (Real.sqrt (curvatureOperatorEnergy T)))
  calc
    (Real.sqrt (curvatureOperatorEnergy T)) ^ 3 =
        Real.sqrt (curvatureOperatorEnergy T) *
          (Real.sqrt (curvatureOperatorEnergy T)) ^ 2 := by ring
    _ ≤ B * (Real.sqrt (curvatureOperatorEnergy T)) ^ 2 := hmul
    _ = B * curvatureOperatorEnergy T := by rw [hsquare]

/-- **Math.** Under a square-root energy bound, the factor-two curvature
reaction pairing is bounded linearly by the Frobenius energy.  The coefficient
is explicit in the finite index cardinality and the absolute structure bound.
-/
theorem abs_two_mul_curvatureOperatorReactionPairing_le_of_sqrt_energy_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) {B : ℝ}
    (hB : 0 ≤ B)
    (hbound : Real.sqrt (curvatureOperatorEnergy T) ≤ B) :
    |2 * ∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b +
          curvatureOperatorSharp c T a b)| ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * B *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) *
        curvatureOperatorEnergy T := by
  let N : ℝ := Fintype.card ι
  let Q : ℝ := N + N ^ 4 * (curvatureStructureBound c) ^ 2
  have hQ : 0 ≤ Q := by
    dsimp [Q, N]
    positivity
  have hN : 0 ≤ 2 * N ^ 2 := by
    positivity
  have hA : 0 ≤ 2 * N ^ 2 * Q :=
    mul_nonneg hN hQ
  have hcube := curvatureOperatorEnergy_sqrt_cube_le_mul_of_sqrt_le T hB hbound
  have hreaction := abs_two_mul_curvatureOperatorReactionPairing_le_of_energy
    c T
  calc
    |2 * ∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b +
          curvatureOperatorSharp c T a b)| ≤
        2 * N ^ 2 * (Real.sqrt (curvatureOperatorEnergy T)) ^ 3 * Q := by
      simpa [N, Q] using hreaction
    _ = (2 * N ^ 2 * Q) *
        (Real.sqrt (curvatureOperatorEnergy T)) ^ 3 := by ring
    _ ≤ (2 * N ^ 2 * Q) *
        (B * curvatureOperatorEnergy T) :=
      mul_le_mul_of_nonneg_left hcube hA
    _ = 2 * N ^ 2 * B * Q * curvatureOperatorEnergy T := by ring
    _ = 2 * (Fintype.card ι : ℝ) ^ 2 * B *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) *
        curvatureOperatorEnergy T := by rfl

/-! ## Linear energy shell -/

/-- **Math.** On a slab carrying a square-root energy bound, the curvature
operator evolution has a linear energy bound after the Laplacian pairing is
removed.  This is the absolute-value form of the reaction shell used by
maximum-principle and Shi-tower arguments.
-/
theorem abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le_of_sqrt_energy_bound
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t B : ℝ}
    (hdiff : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c)
    (hB : 0 ≤ B)
    (hbound : Real.sqrt (curvatureOperatorEnergy (T t)) ≤ B) :
    |deriv (fun s => curvatureOperatorEnergy (T s)) t -
        2 * ∑ a, ∑ b, T t a b * lap t a b| ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * B *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) *
        curvatureOperatorEnergy (T t) := by
  rw [curvatureOperatorEnergy_deriv_eq_laplacian_add_reaction hdiff hevol]
  have hreaction :=
    abs_two_mul_curvatureOperatorReactionPairing_le_of_sqrt_energy_bound
      c (T t) hB hbound
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hreaction

/-! ## Differential inequality -/

/-- **Math.** The finite curvature-operator evolution satisfies a linear
Laplacian-plus-reaction inequality whenever its square-root energy is bounded.
This is the direct cubic-reaction-to-Shi-shell bridge; no target-shaped
existence or geometric identification is hidden in the statement.
-/
theorem curvatureOperatorEnergy_deriv_le_laplacian_add_of_sqrt_energy_bound
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t B : ℝ}
    (hdiff : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c)
    (hB : 0 ≤ B)
    (hbound : Real.sqrt (curvatureOperatorEnergy (T t)) ≤ B) :
    deriv (fun s => curvatureOperatorEnergy (T s)) t ≤
      2 * ∑ a, ∑ b, T t a b * lap t a b +
      2 * (Fintype.card ι : ℝ) ^ 2 * B *
        ((Fintype.card ι : ℝ) +
          (Fintype.card ι : ℝ) ^ 4 * (curvatureStructureBound c) ^ 2) *
        curvatureOperatorEnergy (T t) := by
  have habs :=
    abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le_of_sqrt_energy_bound
      hdiff hevol hB hbound
  have hupper := (le_abs_self _).trans habs
  linarith

end MorganTianLib

end

#print axioms MorganTianLib.curvatureOperatorEnergy_sqrt_cube_le_mul_of_sqrt_le
#print axioms MorganTianLib.abs_two_mul_curvatureOperatorReactionPairing_le_of_sqrt_energy_bound
#print axioms MorganTianLib.abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le_of_sqrt_energy_bound
#print axioms MorganTianLib.curvatureOperatorEnergy_deriv_le_laplacian_add_of_sqrt_energy_bound

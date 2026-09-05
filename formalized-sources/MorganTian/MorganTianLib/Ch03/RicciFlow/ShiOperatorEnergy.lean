import MorganTianLib.Ch03.RicciFlow.VolumeDistortion

open Matrix

noncomputable section

namespace MorganTianLib

/-- **Math.** The finite Frobenius square energy of a matrix. -/
def curvatureOperatorEnergy {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) : ℝ :=
  ∑ a, ∑ b, (T a b) ^ 2

/-- **Math.** Differentiating the finite Frobenius energy entry by entry. -/
theorem hasDerivAt_curvatureOperatorEnergy
    {ι : Type*} [Fintype ι]
    {T : ℝ → Matrix ι ι ℝ} {D : Matrix ι ι ℝ} {t : ℝ}
    (hT : ∀ a b, HasDerivAt (fun s => T s a b) (D a b) t) :
    HasDerivAt (fun s => curvatureOperatorEnergy (T s))
      (2 * ∑ a, ∑ b, T t a b * D a b) t := by
  classical
  have hentry (a b : ι) :
      HasDerivAt (fun s => (T s a b) ^ 2)
        (2 * T t a b * D a b) t := by
    have hm := (hT a b).mul (hT a b)
    have heq : (fun s => T s a b * T s a b) =
        (fun s => (T s a b) ^ 2) := by
      funext s
      ring
    have hd : D a b * T t a b + T t a b * D a b =
        2 * T t a b * D a b := by
      ring
    rw [← heq, ← hd]
    exact hm
  have hsum : HasDerivAt
      (fun s => ∑ a, ∑ b, (T s a b) ^ 2)
      (∑ a, ∑ b, 2 * T t a b * D a b) t := by
    exact HasDerivAt.fun_sum (fun a _ =>
      HasDerivAt.fun_sum (fun b _ => hentry a b))
  simpa [curvatureOperatorEnergy, Finset.mul_sum, mul_assoc, mul_left_comm,
    mul_comm] using hsum

/-- **Math.** The Frobenius energy derivative after inserting the curvature-operator
evolution equation.  The entrywise differentiability assumption is explicit;
the evolution hypothesis supplies the derivative values. -/
theorem curvatureOperatorEnergy_deriv_eq_of_isCurvatureOperatorEvolution
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t : ℝ}
    (hT : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c) :
    deriv (fun s => curvatureOperatorEnergy (T s)) t =
      2 * ∑ a, ∑ b, T t a b *
        (lap t a b + curvatureOperatorSquare (T t) a b +
          curvatureOperatorSharp c (T t) a b) := by
  have hD := hasDerivAt_curvatureOperatorEnergy
    (T := T) (D := fun a b => deriv (fun s => T s a b) t) (t := t)
    (fun a b => (hT a b).hasDerivAt)
  rw [hD.deriv]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hevol t a b]

/-- **Math.** The same energy identity with the Laplacian and algebraic
reaction pairings separated. -/
theorem curvatureOperatorEnergy_deriv_eq_laplacian_add_reaction
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t : ℝ}
    (hT : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c) :
    deriv (fun s => curvatureOperatorEnergy (T s)) t =
      2 * ∑ a, ∑ b, T t a b * lap t a b +
      2 * ∑ a, ∑ b, T t a b *
        (curvatureOperatorSquare (T t) a b +
          curvatureOperatorSharp c (T t) a b) := by
  rw [curvatureOperatorEnergy_deriv_eq_of_isCurvatureOperatorEvolution hT hevol]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- **Math.** An entrywise bound on a finite matrix gives the corresponding
bound for the operator square. -/
theorem abs_curvatureOperatorSquare_le_of_entrywise_bound
    {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hT : ∀ a b, |T a b| ≤ B) (a b : ι) :
    |curvatureOperatorSquare T a b| ≤
      (Fintype.card ι : ℝ) * B ^ 2 := by
  classical
  rw [curvatureOperatorSquare_apply]
  calc
    |∑ c, T a c * T c b| ≤ ∑ c, |T a c * T c b| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ c, |T a c| * |T c b| := by
      apply Finset.sum_congr rfl
      intro c hc
      rw [abs_mul]
    _ ≤ ∑ _c : ι, B ^ 2 := by
      apply Finset.sum_le_sum
      intro c hc
      have hp := mul_le_mul (hT a c) (hT c b)
        (abs_nonneg _) hB
      simpa [pow_two] using hp
    _ = (Fintype.card ι : ℝ) * B ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

/-- **Math.** Entrywise bounds on the structure constants and matrix give a
finite bound for the Lie-algebra sharp term. -/
theorem abs_curvatureOperatorSharp_le_of_entrywise_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ a b, |T a b| ≤ B)
    (hc : ∀ a b d, |c a b d| ≤ C) (a b : ι) :
    |curvatureOperatorSharp c T a b| ≤
      (Fintype.card ι : ℝ) ^ 4 * C ^ 2 * B ^ 2 := by
  classical
  rw [curvatureOperatorSharp_apply]
  have hterm (γ δ ζ η : ι) :
      |c a γ ζ * c b δ η * T γ δ * T ζ η| ≤ C ^ 2 * B ^ 2 := by
    calc
      |c a γ ζ * c b δ η * T γ δ * T ζ η| =
          (|c a γ ζ| * |c b δ η|) * (|T γ δ| * |T ζ η|) := by
            rw [abs_mul, abs_mul, abs_mul]
            ring
      _ ≤ (C * C) * (B * B) := by
        apply mul_le_mul
        · exact mul_le_mul (hc a γ ζ) (hc b δ η)
            (abs_nonneg _) hC
        · exact mul_le_mul (hT γ δ) (hT ζ η)
            (abs_nonneg _) hB
        · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
        · exact mul_nonneg hC hC
      _ = C ^ 2 * B ^ 2 := by ring
  calc
    |∑ γ, ∑ δ, ∑ ζ, ∑ η,
        c a γ ζ * c b δ η * T γ δ * T ζ η| ≤
        ∑ γ, |∑ δ, ∑ ζ, ∑ η,
          c a γ ζ * c b δ η * T γ δ * T ζ η| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ γ, ∑ δ, |∑ ζ, ∑ η,
          c a γ ζ * c b δ η * T γ δ * T ζ η| := by
      apply Finset.sum_le_sum
      intro γ hγ
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ γ, ∑ δ, ∑ ζ, |∑ η,
          c a γ ζ * c b δ η * T γ δ * T ζ η| := by
      apply Finset.sum_le_sum
      intro γ hγ
      apply Finset.sum_le_sum
      intro δ hδ
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ γ, ∑ δ, ∑ ζ, ∑ η,
          |c a γ ζ * c b δ η * T γ δ * T ζ η| := by
      apply Finset.sum_le_sum
      intro γ hγ
      apply Finset.sum_le_sum
      intro δ hδ
      apply Finset.sum_le_sum
      intro ζ hζ
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ γ, ∑ δ, ∑ ζ, ∑ η, C ^ 2 * B ^ 2 := by
      apply Finset.sum_le_sum
      intro γ hγ
      apply Finset.sum_le_sum
      intro δ hδ
      apply Finset.sum_le_sum
      intro ζ hζ
      apply Finset.sum_le_sum
      intro η hη
      exact hterm γ δ ζ η
    _ = (Fintype.card ι : ℝ) ^ 4 * C ^ 2 * B ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

/-- **Math.** The finite reaction pairing is controlled by entrywise bounds on
the operator and on the structure constants.  Here `N = card ι`; the powers
of `N` count the finite contractions in the square and sharp terms. -/
theorem abs_curvatureOperatorReactionPairing_le_of_entrywise_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ a b, |T a b| ≤ B)
    (hc : ∀ a b d, |c a b d| ≤ C) :
    |∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| ≤
      (Fintype.card ι : ℝ) ^ 2 * B ^ 3 *
        ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) ^ 4 * C ^ 2) := by
  classical
  let N : ℝ := Fintype.card ι
  have hsq (a b : ι) :
      |curvatureOperatorSquare T a b| ≤ N * B ^ 2 := by
    simpa [N] using abs_curvatureOperatorSquare_le_of_entrywise_bound
      T hB hT a b
  have hsharp (a b : ι) :
      |curvatureOperatorSharp c T a b| ≤ N ^ 4 * C ^ 2 * B ^ 2 := by
    simpa [N] using abs_curvatureOperatorSharp_le_of_entrywise_bound
      c T hB hC hT hc a b
  calc
    |∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| ≤
        ∑ a, |∑ b, T a b *
          (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, |T a b *
          (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| := by
      apply Finset.sum_le_sum
      intro a ha
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, ∑ b, B * (N * B ^ 2 + N ^ 4 * C ^ 2 * B ^ 2) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      rw [abs_mul]
      have hadd :
          |curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b| ≤
            N * B ^ 2 + N ^ 4 * C ^ 2 * B ^ 2 := by
        calc
          |curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b| ≤
              |curvatureOperatorSquare T a b| +
                |curvatureOperatorSharp c T a b| :=
            abs_add_le _ _
          _ ≤ N * B ^ 2 + N ^ 4 * C ^ 2 * B ^ 2 :=
            add_le_add (hsq a b) (hsharp a b)
      exact mul_le_mul (hT a b) hadd (abs_nonneg _) hB
    _ = N ^ 2 * B ^ 3 * (N + N ^ 4 * C ^ 2) := by
      simp [N, Finset.sum_const, nsmul_eq_mul]
      ring

/-- **Math.** The factor-two reaction contribution appearing in the energy
derivative has the corresponding absolute bound. -/
theorem abs_two_mul_curvatureOperatorReactionPairing_le_of_entrywise_bound
    {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) {B C : ℝ}
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ a b, |T a b| ≤ B)
    (hc : ∀ a b d, |c a b d| ≤ C) :
    |2 * ∑ a, ∑ b, T a b *
        (curvatureOperatorSquare T a b + curvatureOperatorSharp c T a b)| ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * B ^ 3 *
        ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) ^ 4 * C ^ 2) := by
  have hpair := abs_curvatureOperatorReactionPairing_le_of_entrywise_bound
    c T hB hC hT hc
  rw [abs_mul]
  simpa [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_assoc] using
    (mul_le_mul_of_nonneg_left hpair (by norm_num : (0 : ℝ) ≤ 2))

/-- **Math.** Along the operator evolution, the part of the Frobenius energy
derivative left after subtracting the Laplacian pairing is bounded cubically
in an entrywise curvature bound. -/
theorem abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t B C : ℝ}
    (hdiff : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ a b, |T t a b| ≤ B)
    (hc : ∀ a b d, |c a b d| ≤ C) :
    |deriv (fun s => curvatureOperatorEnergy (T s)) t -
        2 * ∑ a, ∑ b, T t a b * lap t a b| ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * B ^ 3 *
        ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) ^ 4 * C ^ 2) := by
  rw [curvatureOperatorEnergy_deriv_eq_laplacian_add_reaction hdiff hevol]
  have hcancel :
      (2 * ∑ a, ∑ b, T t a b * lap t a b +
          2 * ∑ a, ∑ b, T t a b *
            (curvatureOperatorSquare (T t) a b +
              curvatureOperatorSharp c (T t) a b)) -
          2 * ∑ a, ∑ b, T t a b * lap t a b =
        2 * ∑ a, ∑ b, T t a b *
          (curvatureOperatorSquare (T t) a b +
            curvatureOperatorSharp c (T t) a b) := by
    ring
  rw [hcancel]
  exact abs_two_mul_curvatureOperatorReactionPairing_le_of_entrywise_bound
    c (T t) hB hC hT hc

/-! ## Scalar differential inequalities for the Shi maximum principle -/

/-- **Math.** The curvature-operator energy satisfies an upper differential
inequality once the Laplacian pairing and the reaction terms are separated.
This is the scalar interface consumed at a spatial maximum: the Laplacian
pairing remains visible as an input, while the quadratic reaction is replaced
by the explicit cubic bound above. -/
theorem curvatureOperatorEnergy_deriv_le_of_entrywise_bound
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t B C : ℝ}
    (hdiff : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ a b, |T t a b| ≤ B)
    (hc : ∀ a b d, |c a b d| ≤ C) :
    deriv (fun s => curvatureOperatorEnergy (T s)) t ≤
      2 * ∑ a, ∑ b, T t a b * lap t a b +
        2 * (Fintype.card ι : ℝ) ^ 2 * B ^ 3 *
          ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) ^ 4 * C ^ 2) := by
  have hsub := abs_curvatureOperatorEnergy_deriv_sub_laplacianPairing_le
    hdiff hevol hB hC hT hc
  have hreaction :
      deriv (fun s => curvatureOperatorEnergy (T s)) t -
          2 * ∑ a, ∑ b, T t a b * lap t a b ≤
        2 * (Fintype.card ι : ℝ) ^ 2 * B ^ 3 *
          ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) ^ 4 * C ^ 2) :=
    (le_abs_self _).trans hsub
  linarith

/-- **Math.** At a point where the Laplacian pairing is nonpositive, the
curvature-operator energy has a purely reaction-controlled upper derivative. -/
theorem curvatureOperatorEnergy_deriv_le_of_laplacianPairing_nonpos
    {ι : Type*} [Fintype ι]
    {T lap : ℝ → Matrix ι ι ℝ} {c : ι → ι → ι → ℝ} {t B C : ℝ}
    (hdiff : ∀ a b, DifferentiableAt ℝ (fun s => T s a b) t)
    (hevol : IsCurvatureOperatorEvolution T lap c)
    (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hT : ∀ a b, |T t a b| ≤ B)
    (hc : ∀ a b d, |c a b d| ≤ C)
    (hlap : 2 * ∑ a, ∑ b, T t a b * lap t a b ≤ 0) :
    deriv (fun s => curvatureOperatorEnergy (T s)) t ≤
      2 * (Fintype.card ι : ℝ) ^ 2 * B ^ 3 *
        ((Fintype.card ι : ℝ) + (Fintype.card ι : ℝ) ^ 4 * C ^ 2) := by
  have hmain := curvatureOperatorEnergy_deriv_le_of_entrywise_bound
    hdiff hevol hB hC hT hc
  linarith

end MorganTianLib

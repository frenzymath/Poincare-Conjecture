import GilbargTrudinger.Ch05.BanachSpaces

/-! # The method of continuity from Gilbarg--Trudinger, Chapter 5 -/

namespace GilbargTrudinger

open Set

section MethodOfContinuity

variable {B V : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine path joining two bounded linear operators. -/
def affineOperator (L₀ L₁ : B →L[ℝ] V) (t : ℝ) : B →L[ℝ] V :=
  (1 - t) • L₀ + t • L₁

private theorem surjective_affineOperator_of_close (L₀ L₁ : B →L[ℝ] V) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x : B, ‖x‖ ≤ C * ‖affineOperator L₀ L₁ r x‖)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hsurj : Function.Surjective (affineOperator L₀ L₁ s))
    (hclose : C * |t - s| * ‖L₁ - L₀‖ < 1) :
    Function.Surjective (affineOperator L₀ L₁ t) := by
  have hinj : Function.Injective (affineOperator L₀ L₁ s) := by
    intro x z hxz
    have hb := hbound s hs (x - z)
    have hm : affineOperator L₀ L₁ s (x - z) = 0 := by
      rw [map_sub, hxz, sub_self]
    rw [hm, norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hb (norm_nonneg _)))
  let e : B ≃ₗ[ℝ] V :=
    LinearEquiv.ofBijective (affineOperator L₀ L₁ s).toLinearMap ⟨hinj, hsurj⟩
  have he_apply (x : B) : e x = affineOperator L₀ L₁ s x := rfl
  have he_bound (y : V) : ‖e.symm y‖ ≤ C * ‖y‖ := by
    calc
      ‖e.symm y‖ ≤ C * ‖affineOperator L₀ L₁ s (e.symm y)‖ := hbound s hs _
      _ = C * ‖y‖ := by rw [← he_apply, e.apply_symm_apply]
  let inv : V →L[ℝ] B := LinearMap.mkContinuous e.symm.toLinearMap C he_bound
  have hinv_norm : ‖inv‖ ≤ C := inv.opNorm_le_bound hC he_bound
  intro y
  let A : B →L[ℝ] B := (t - s) • (inv.comp (L₁ - L₀))
  have hA_norm : ‖A‖ < 1 := by
    calc
      ‖A‖ = |t - s| * ‖inv.comp (L₁ - L₀)‖ := by
        simp only [A, norm_smul, Real.norm_eq_abs]
      _ ≤ |t - s| * (‖inv‖ * ‖L₁ - L₀‖) :=
        mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le inv (L₁ - L₀))
          (abs_nonneg _)
      _ ≤ |t - s| * (C * ‖L₁ - L₀‖) := by
        gcongr
      _ = C * |t - s| * ‖L₁ - L₀‖ := by ring
      _ < 1 := hclose
  let f : B → B := fun x ↦ inv y - A x
  have hf_lip : LipschitzWith ‖A‖₊ f := by
    simpa only [f, zero_add, neg_apply, sub_eq_add_neg, nnnorm_neg] using
      (LipschitzWith.const (α := B) (inv y)).add (-A).lipschitz
  have hf : ContractingWith ‖A‖₊ f := by
    refine ⟨?_, hf_lip⟩
    exact_mod_cast hA_norm
  obtain ⟨x, hx, -⟩ := contraction_mapping_principle f ⟨‖A‖₊, hf⟩
  refine ⟨x, ?_⟩
  have hx' : x = inv y - A x := hx.symm
  have hleft (z : V) : affineOperator L₀ L₁ s (inv z) = z := by
    change e (e.symm z) = z
    exact e.apply_symm_apply z
  have hAimage :
      affineOperator L₀ L₁ s (A x) = (t - s) • (L₁ - L₀) x := by
    simp only [A, smul_apply, map_smul, ContinuousLinearMap.comp_apply, hleft]
  have hLs := congrArg (affineOperator L₀ L₁ s) hx'
  rw [map_sub, hleft, hAimage] at hLs
  rw [show affineOperator L₀ L₁ t =
      affineOperator L₀ L₁ s + (t - s) • (L₁ - L₀) by
    simp only [affineOperator]
    module]
  simp only [add_apply, smul_apply]
  exact (eq_sub_iff_add_eq).mp hLs

private theorem surjective_affineOperator_one (L₀ L₁ : B →L[ℝ] V) (C : ℝ)
    (hC : 0 ≤ C)
    (hbound : ∀ r ∈ Icc (0 : ℝ) 1, ∀ x : B, ‖x‖ ≤ C * ‖affineOperator L₀ L₁ r x‖) :
    Function.Surjective L₀ → Function.Surjective L₁ := by
  intro h₀
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (C * ‖L₁ - L₀‖)
  have hNreal : 0 < (N : ℝ) :=
    lt_of_le_of_lt (mul_nonneg hC (norm_nonneg _)) hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNreal
  have hsteps : ∀ k : ℕ, k ≤ N →
      Function.Surjective (affineOperator L₀ L₁ ((k : ℝ) / (N : ℝ))) := by
    intro k hk
    induction k with
    | zero =>
        simpa [affineOperator] using h₀
    | succ k ih =>
        refine surjective_affineOperator_of_close L₀ L₁ C hC hbound
          (s := (k : ℝ) / (N : ℝ))
          (t := (Nat.succ k : ℕ) / (N : ℝ)) ?_ ?_ ?_
        · constructor
          · positivity
          · rw [div_le_one hNreal]
            exact_mod_cast Nat.lt_of_succ_le hk |>.le
        · exact ih (Nat.lt_of_succ_le hk).le
        · have hstep :
              ((Nat.succ k : ℕ) : ℝ) / (N : ℝ) - (k : ℝ) / (N : ℝ) =
                1 / (N : ℝ) := by
                rw [Nat.cast_succ]
                ring
          rw [hstep, abs_of_pos (one_div_pos.mpr hNreal)]
          calc
            C * (1 / (N : ℝ)) * ‖L₁ - L₀‖ =
                (C * ‖L₁ - L₀‖) / (N : ℝ) := by ring
            _ < 1 := (div_lt_one hNreal).2 hN
  simpa [div_self hNne, affineOperator] using hsteps N le_rfl

/-- The method of continuity for an affine path of bounded linear operators. -/
theorem method_of_continuity (L₀ L₁ : B →L[ℝ] V) (C : ℝ)
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x : B,
      ‖x‖ ≤ C * ‖affineOperator L₀ L₁ t x‖) :
    Function.Surjective L₀ ↔ Function.Surjective L₁ := by
  cases subsingleton_or_nontrivial B with
  | inl hB =>
      letI : Subsingleton B := hB
      constructor
      · intro h₀ y
        obtain ⟨x, hx⟩ := h₀ y
        refine ⟨0, ?_⟩
        simpa [Subsingleton.elim x 0] using hx
      · intro h₁ y
        obtain ⟨x, hx⟩ := h₁ y
        refine ⟨0, ?_⟩
        simpa [Subsingleton.elim x 0] using hx
  | inr hB =>
      letI : Nontrivial B := hB
      obtain ⟨x, hx⟩ := exists_ne (0 : B)
      have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hb₀ := hbound 0 ⟨le_rfl, zero_le_one⟩ x
      have hprod : 0 < C * ‖affineOperator L₀ L₁ 0 x‖ :=
        lt_of_lt_of_le hxpos hb₀
      have hC : 0 ≤ C := by
        nlinarith [norm_nonneg (affineOperator L₀ L₁ 0 x)]
      have hbound_rev : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z : B,
          ‖z‖ ≤ C * ‖affineOperator L₁ L₀ t z‖ := by
        intro t ht z
        have hrev_mem : 1 - t ∈ Icc (0 : ℝ) 1 := by
          constructor <;> linarith [ht.1, ht.2]
        rw [show affineOperator L₁ L₀ t = affineOperator L₀ L₁ (1 - t) by
          simp only [affineOperator]
          module]
        exact hbound (1 - t) hrev_mem z
      exact ⟨surjective_affineOperator_one L₀ L₁ C hC hbound,
        surjective_affineOperator_one L₁ L₀ C hC hbound_rev⟩

end MethodOfContinuity

end GilbargTrudinger

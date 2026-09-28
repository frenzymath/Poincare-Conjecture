import MorganTianLib.Ch04.RicciOperatorCone

/-!
# Boundary data in the nonnegative Ricci cone

The nonnegative Ricci cone contains nonzero operators with a zero Ricci
eigenvalue.  This finite-dimensional boundary ray is the algebraic obstruction
to upgrading nonnegative Ricci curvature to strict positivity without an
additional geometric strong-maximum or splitting argument.
-/

open Matrix

noncomputable section

namespace MorganTianLib

/-- **Math.** The curvature ray `(k,0,0)` is nonzero and belongs to the
nonnegative Ricci cone, while its Ricci operator has a zero eigenvalue and is
therefore not positive definite. -/
theorem ricciOperator_boundary_ray {k : ℝ} (hk : 0 < k) :
    let A : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![k, 0, 0]
    A ∈ nonnegativeRicciOperatorCone ∧
      A ≠ 0 ∧
      ¬ (ricciOperator A).PosDef ∧
      ricciOperator A = Matrix.diagonal ![0, k, k] := by
  dsimp
  have hcone : Matrix.diagonal ![k, 0, 0] ∈ nonnegativeRicciOperatorCone := by
    rw [mem_diagonal_nonnegativeRicciOperatorCone_iff]
    change 0 ≤ k + 0 ∧ 0 ≤ k + 0 ∧ 0 ≤ (0 : ℝ) + 0
    exact ⟨by simpa using hk.le, by simpa using hk.le, by norm_num⟩
  have hne : (Matrix.diagonal ![k, 0, 0] : Matrix (Fin 3) (Fin 3) ℝ) ≠ 0 := by
    intro h
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M 0 0) h
    simpa [Matrix.diagonal] using hk.ne' h00
  have hformula :
      ricciOperator (Matrix.diagonal ![k, 0, 0]) =
        Matrix.diagonal ![0, k, k] := by
    simpa using (ricciOperator_diagonal (![k, 0, 0] : Fin 3 → ℝ))
  have hnotpd :
      ¬ (ricciOperator (Matrix.diagonal ![k, 0, 0])).PosDef := by
    rw [hformula]
    intro hpd
    have hzero := hpd.2 (x := Finsupp.single 0 1) (by simp)
    simpa [Matrix.diagonal] using hzero
  exact ⟨hcone, hne, hnotpd, hformula⟩

end MorganTianLib

#print axioms MorganTianLib.ricciOperator_boundary_ray

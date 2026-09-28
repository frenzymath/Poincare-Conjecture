import MorganTianLib.Ch04.CurvatureApplications
import MorganTianLib.Ch04.ConvexInvariant
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The three-dimensional nonnegative Ricci cone and its reaction ODE

The Ricci eigenvalues are pairwise sums of curvature-operator eigenvalues.
The corresponding cone is larger than the nonnegative curvature-operator
cone. The diagonal Hamilton reaction preserves this cone, both infinitesimally
and along its actual integral curves on any closed time interval.

Source: Morgan--Tian, Chapter 4, `cor:nonnegative-ricci-preserved`.
The identification with the evolving geometric tensor equation and the
parabolic maximum principle remain separate obligations.
-/

open Set
open scoped Topology

noncomputable section

namespace MorganTianLib

/-- **Math.** The cone defined by nonnegative pairwise curvature-eigenvalue
sums, equivalently nonnegative Ricci eigenvalues in dimension three. -/
def nonnegativeRicciEigenvalueCone : Set (Fin 3 → ℝ) :=
  {v | 0 ≤ v 0 + v 1 ∧ 0 ≤ v 0 + v 2 ∧ 0 ≤ v 1 + v 2}

/-- **Math.** The diagonal entries of the verified three-dimensional reaction. -/
def threeDimensionalEigenvalueReaction (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => threeDimensionalDiagonalReaction (v 0) (v 1) (v 2) i i

/-- **Math.** The Ricci eigenvalue cone is convex. -/
theorem convex_nonnegativeRicciEigenvalueCone :
    Convex ℝ nonnegativeRicciEigenvalueCone := by
  intro u hu v hv a b ha hb hab
  rcases hu with ⟨hu01, hu02, hu12⟩
  rcases hv with ⟨hv01, hv02, hv12⟩
  change 0 ≤ a * u 0 + b * v 0 + (a * u 1 + b * v 1) ∧
    0 ≤ a * u 0 + b * v 0 + (a * u 2 + b * v 2) ∧
    0 ≤ a * u 1 + b * v 1 + (a * u 2 + b * v 2)
  constructor
  · nlinarith [mul_nonneg ha hu01, mul_nonneg hb hv01]
  constructor
  · nlinarith [mul_nonneg ha hu02, mul_nonneg hb hv02]
  · nlinarith [mul_nonneg ha hu12, mul_nonneg hb hv12]

/-- **Math.** The Ricci eigenvalue cone is closed. -/
theorem isClosed_nonnegativeRicciEigenvalueCone :
    IsClosed nonnegativeRicciEigenvalueCone := by
  have h01 : IsClosed {v : Fin 3 → ℝ | 0 ≤ v 0 + v 1} :=
    isClosed_le continuous_const ((continuous_apply 0).add (continuous_apply 1))
  have h02 : IsClosed {v : Fin 3 → ℝ | 0 ≤ v 0 + v 2} :=
    isClosed_le continuous_const ((continuous_apply 0).add (continuous_apply 2))
  have h12 : IsClosed {v : Fin 3 → ℝ | 0 ≤ v 1 + v 2} :=
    isClosed_le continuous_const ((continuous_apply 1).add (continuous_apply 2))
  exact h01.inter (h02.inter h12)

/-- **Math.** For ordered eigenvalues it suffices to test the smallest pair. -/
theorem mem_nonnegativeRicciEigenvalueCone_iff_of_ordered
    {lam mu nu : ℝ} (hmu : mu ≤ lam) (hnu : nu ≤ mu) :
    ![lam, mu, nu] ∈ nonnegativeRicciEigenvalueCone ↔ 0 ≤ mu + nu := by
  simp only [nonnegativeRicciEigenvalueCone, mem_setOf_eq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
  constructor
  · exact fun h => h.2.2
  · intro h
    exact ⟨by linarith, by linarith, h⟩

/-- **Math.** A pairwise reaction sum is nonnegative throughout the Ricci cone. -/
theorem ricci_pair_reaction_nonneg {x y z : ℝ}
    (hxy : 0 ≤ x + y) (hxz : 0 ≤ x + z) (hyz : 0 ≤ y + z) :
    0 ≤ (x ^ 2 + y * z) + (y ^ 2 + x * z) := by
  have h := mul_nonneg hxy (show 0 ≤ x + y + 2 * z by linarith)
  nlinarith [sq_nonneg (x - y)]

/-- **Math.** The Hamilton reaction maps the entire Ricci eigenvalue cone
into itself, including points with a negative curvature eigenvalue. -/
theorem threeDimensionalEigenvalueReaction_mem_nonnegativeRicciEigenvalueCone
    {v : Fin 3 → ℝ} (hv : v ∈ nonnegativeRicciEigenvalueCone) :
    threeDimensionalEigenvalueReaction v ∈ nonnegativeRicciEigenvalueCone := by
  rcases hv with ⟨h01, h02, h12⟩
  simp only [nonnegativeRicciEigenvalueCone, mem_setOf_eq,
    threeDimensionalEigenvalueReaction, threeDimensionalDiagonalReaction_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ]
  refine ⟨ricci_pair_reaction_nonneg h01 h02 h12, ?_, ?_⟩
  · convert ricci_pair_reaction_nonneg h02 h01 (by linarith : 0 ≤ v 2 + v 1) using 1
    ring
  · convert ricci_pair_reaction_nonneg h12 (by linarith : 0 ≤ v 1 + v 0)
      (by linarith : 0 ≤ v 2 + v 0) using 1
    ring

/-- **Math.** The Hamilton reaction satisfies the tangent-cone condition for
the nonnegative Ricci eigenvalue cone. -/
theorem threeDimensionalEigenvalueReaction_preserves_nonnegativeRicciEigenvalueCone :
    vectorFieldPreservesConvexSet nonnegativeRicciEigenvalueCone
      threeDimensionalEigenvalueReaction := by
  apply vectorFieldPreservesConvexSet_of_segment convex_nonnegativeRicciEigenvalueCone
  intro v hv
  have hR := threeDimensionalEigenvalueReaction_mem_nonnegativeRicciEigenvalueCone hv
  refine ⟨v + threeDimensionalEigenvalueReaction v, ?_, by simp⟩
  rcases hv with ⟨hv01, hv02, hv12⟩
  rcases hR with ⟨hR01, hR02, hR12⟩
  change 0 ≤ v 0 + _ + (v 1 + _) ∧ 0 ≤ v 0 + _ + (v 2 + _) ∧
    0 ≤ v 1 + _ + (v 2 + _)
  exact ⟨by linarith, by linarith, by linarith⟩

private theorem nonpos_of_deriv_le_mul_at_pos
    {f f' : ℝ → ℝ} {a b C : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt f (f' t) (Ici t) t)
    (hbound : ∀ t ∈ Ico a b, 0 < f t → f' t ≤ C * f t)
    (hinit : f a ≤ 0) : ∀ t ∈ Icc a b, f t ≤ 0 := by
  have hbarrier : ∀ ε : ℝ, 0 < ε → ∀ t ∈ Icc a b,
      f t ≤ ε * Real.exp ((C + 1) * (t - a)) := by
    intro ε hε t ht
    apply image_le_of_deriv_right_lt_deriv_boundary hf hderiv
      (B := fun s => ε * Real.exp ((C + 1) * (s - a)))
      (B' := fun s => ε * (Real.exp ((C + 1) * (s - a)) * (C + 1)))
      (hinit.trans (by positivity)) _ _ ht
    · intro s
      have hlinear : HasDerivAt (fun r : ℝ => (C + 1) * (r - a)) (C + 1) s := by
        simpa using ((hasDerivAt_id s).sub_const a).const_mul (C + 1)
      exact hlinear.exp.const_mul ε
    · intro s hs hcontact
      have hpos : 0 < f s := by rw [hcontact]; positivity
      have h := hbound s hs hpos
      rw [hcontact] at h
      nlinarith [Real.exp_pos ((C + 1) * (s - a))]
  intro t ht
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hE : 0 < Real.exp ((C + 1) * (t - a)) := Real.exp_pos _
  have h := hbarrier (δ / Real.exp ((C + 1) * (t - a))) (div_pos hδ hE) t ht
  simpa only [zero_add, div_mul_cancel₀ δ hE.ne'] using h

private theorem pair_sum_nonneg_of_reaction
    {x y z : ℝ → ℝ} {a b : ℝ}
    (hx : ContinuousOn x (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hz : ContinuousOn z (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt (fun s => x s + y s)
      (x t ^ 2 + y t ^ 2 + z t * (x t + y t)) (Ici t) t)
    (hinit : 0 ≤ x a + y a) :
    ∀ t ∈ Icc a b, 0 ≤ x t + y t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hz
  have h := nonpos_of_deriv_le_mul_at_pos (f := fun t => -(x t + y t))
    (C := C) (hx.add hy).neg (fun t ht => (hderiv t ht).neg) ?_ (by linarith)
  · intro t ht
    have ht' := h t ht
    linarith
  · intro t ht hpos
    have hzC : z t ≤ C := (le_abs_self _).trans (hC t (Ico_subset_Icc_self ht))
    have hmul := mul_le_mul_of_nonneg_right hzC hpos.le
    nlinarith [sq_nonneg (x t), sq_nonneg (y t)]

/-- **Math.** Every actual integral curve of the three-dimensional Hamilton
reaction preserves nonnegative Ricci eigenvalues. Only the derivative-based
ODE and the initial cone condition are assumed; no global Lipschitz bound
for the quadratic reaction is required. -/
theorem integralCurve_mem_nonnegativeRicciEigenvalueCone
    {v : ℝ → Fin 3 → ℝ} {a b : ℝ}
    (hv : IsIntegralCurveOn v (fun _ => threeDimensionalEigenvalueReaction) (Icc a b))
    (hinit : v a ∈ nonnegativeRicciEigenvalueCone) :
    ∀ t ∈ Icc a b, v t ∈ nonnegativeRicciEigenvalueCone := by
  have hcont (i : Fin 3) : ContinuousOn (fun t => v t i) (Icc a b) :=
    (continuous_apply i).comp_continuousOn hv.continuousOn
  have hd (t : ℝ) (ht : t ∈ Ico a b) (i : Fin 3) :
      HasDerivWithinAt (fun s => v s i)
        (threeDimensionalEigenvalueReaction (v t) i) (Ici t) t :=
    hasDerivWithinAt_pi.mp ((hv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem ht)) i
  have hd0 (t : ℝ) (ht : t ∈ Ico a b) := hd t ht 0
  have hd1 (t : ℝ) (ht : t ∈ Ico a b) := hd t ht 1
  have hd2 (t : ℝ) (ht : t ∈ Ico a b) := hd t ht 2
  simp only [threeDimensionalEigenvalueReaction, threeDimensionalDiagonalReaction_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, Function.comp_apply, Matrix.cons_val_succ] at hd0 hd1 hd2
  rcases hinit with ⟨h01, h02, h12⟩
  have h01' := pair_sum_nonneg_of_reaction (hcont 0) (hcont 1) (hcont 2)
    (fun t ht => by convert (hd0 t ht).add (hd1 t ht) using 1 <;> first | rfl | ring) h01
  have h02' := pair_sum_nonneg_of_reaction (hcont 0) (hcont 2) (hcont 1)
    (fun t ht => by convert (hd0 t ht).add (hd2 t ht) using 1 <;> first | rfl | ring) h02
  have h12' := pair_sum_nonneg_of_reaction (hcont 1) (hcont 2) (hcont 0)
    (fun t ht => by convert (hd1 t ht).add (hd2 t ht) using 1 <;> first | rfl | ring) h12
  exact fun t ht => ⟨h01' t ht, h02' t ht, h12' t ht⟩

/-- **Math.** The nonzero boundary ray with curvature eigenvalues `(k,0,0)`
is invariant under the reaction and retains a zero Ricci pair sum. This
finite-dimensional calculation makes no claim about a manifold example. -/
theorem threeDimensionalEigenvalueReaction_nonzero_boundary_ray
    {k : ℝ} (hk : 0 < k) :
    ![k, 0, 0] ∈ nonnegativeRicciEigenvalueCone ∧
    ![k, 0, 0] ≠ (0 : Fin 3 → ℝ) ∧
    threeDimensionalEigenvalueReaction ![k, 0, 0] = ![k ^ 2, 0, 0] ∧
    threeDimensionalEigenvalueReaction ![k, 0, 0] 1 +
      threeDimensionalEigenvalueReaction ![k, 0, 0] 2 = 0 := by
  have hcone : ![k, 0, 0] ∈ nonnegativeRicciEigenvalueCone := by
    simpa [nonnegativeRicciEigenvalueCone] using hk.le
  have hne : ![k, 0, 0] ≠ (0 : Fin 3 → ℝ) := by
    intro h
    have h0 := congr_fun h 0
    simpa using hk.ne' h0
  have hreaction : threeDimensionalEigenvalueReaction ![k, 0, 0] = ![k ^ 2, 0, 0] := by
    ext i
    fin_cases i <;> simp [threeDimensionalEigenvalueReaction]
  refine ⟨hcone, hne, hreaction, ?_⟩
  rw [hreaction]
  simp

end MorganTianLib

#print axioms MorganTianLib.threeDimensionalEigenvalueReaction_preserves_nonnegativeRicciEigenvalueCone
#print axioms MorganTianLib.integralCurve_mem_nonnegativeRicciEigenvalueCone
#print axioms MorganTianLib.threeDimensionalEigenvalueReaction_nonzero_boundary_ray

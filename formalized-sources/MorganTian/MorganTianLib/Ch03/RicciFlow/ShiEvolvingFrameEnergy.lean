import MorganTianLib.Ch03.RicciFlow.ShiNormEnergy

/-!
# Morgan--Tian Ch. 3 -- componentwise Shi bounds to moving-frame energy

The moving-frame energy is a finite sum of squared curvature components.  This
module supplies the finite-dimensional interface from uniform componentwise
bounds to that energy, and then consumes the existing moving-frame Grönwall
producer.  The geometric identification of a Shi component with a moving-frame
component remains an explicit upstream hypothesis.
-/

open Set
open scoped BigOperators

noncomputable section

namespace MorganTianLib

/-- **Math.** A finite family of scalar components bounded in absolute value has the
expected cardinality-times-square bound. -/
theorem finset_sum_sq_le_card_mul_sq_of_abs_le
    {α : Type*} [Fintype α] {f : α → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (h : ∀ i, |f i| ≤ B) :
    ∑ i, f i ^ 2 ≤ (Fintype.card α : ℝ) * B ^ 2 := by
  classical
  have hterm : ∀ i, f i ^ 2 ≤ B ^ 2 := by
    intro i
    rw [sq_le_sq]
    simpa [abs_of_nonneg hB] using h i
  calc
    ∑ i, f i ^ 2 ≤ ∑ i, B ^ 2 :=
      Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card α : ℝ) * B ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]

theorem evolvingFrameCurvatureEnergy_le_of_component_bound
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    {B : ℝ} (hB : 0 ≤ B)
    (hcomponent : ∀ (slot : Fin 4 → ι) (t : ℝ),
      |evolvingFrameCurvatureComponent F C slot t| ≤ B) :
    ∀ t : ℝ,
      evolvingFrameCurvatureEnergy F C t ≤
        (Fintype.card (Fin 4 → ι) : ℝ) * B ^ 2 := by
  classical
  intro t
  simpa [evolvingFrameCurvatureEnergy, evolvingFrameCurvatureComponentSq] using
    (finset_sum_sq_le_card_mul_sq_of_abs_le
      (f := fun slot : Fin 4 → ι =>
        evolvingFrameCurvatureComponent F C slot t)
      hB (fun slot => hcomponent slot t))

/-- **Math.** Uniform component bounds for the intrinsic and frame terms feed the
existing moving-frame Grönwall estimate.  The componentwise hypotheses are
the explicit geometric/positive-order interface. -/
theorem evolvingFrameCurvatureEnergy_le_gronwall_of_component_bounds
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [CompleteSpace V] [FiniteDimensional ℝ V]
    {ι : Type*} [Fintype ι] {J : Set ℝ}
    {G : EvolvingMetricData V J}
    (F : EvolvingFrameData V ι J G) (C : EvolvingCurvatureData V)
    {a b ε A B E₀ : ℝ}
    (hcont : ContinuousOn (fun s => evolvingFrameCurvatureEnergy F C s)
      (Icc a b))
    (hinit : evolvingFrameCurvatureEnergy F C a ≤ E₀)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hIntrinsic : ∀ s ∈ Ico a b, ∀ slot : Fin 4 → ι,
      |evolvingFrameCurvatureIntrinsicComponent F C slot s| ≤ A)
    (hFrame : ∀ s ∈ Ico a b, ∀ slot : Fin 4 → ι,
      |evolvingFrameCurvatureFrameComponent F C slot s| ≤ B)
    (hε : 0 < ε) :
    ∀ t ∈ Icc a b,
      evolvingFrameCurvatureEnergy F C t ≤
        gronwallBound E₀ ε
          ((2 * ε⁻¹) *
            ((Fintype.card (Fin 4 → ι) : ℝ) * A ^ 2 +
             (Fintype.card (Fin 4 → ι) : ℝ) * B ^ 2))
          (t - a) := by
  let N : ℝ := (Fintype.card (Fin 4 → ι) : ℝ)
  have hIntrinsicEnergy : ∀ s ∈ Ico a b,
      evolvingFrameCurvatureIntrinsicEnergy F C s ≤ N * A ^ 2 := by
    intro s hs
    simpa [evolvingFrameCurvatureIntrinsicEnergy, N] using
      (finset_sum_sq_le_card_mul_sq_of_abs_le
        (f := fun slot : Fin 4 → ι =>
          evolvingFrameCurvatureIntrinsicComponent F C slot s)
        hA (fun slot => hIntrinsic s hs slot))
  have hFrameEnergy : ∀ s ∈ Ico a b,
      evolvingFrameCurvatureFrameEnergy F C s ≤ N * B ^ 2 := by
    intro s hs
    simpa [evolvingFrameCurvatureFrameEnergy, N] using
      (finset_sum_sq_le_card_mul_sq_of_abs_le
        (f := fun slot : Fin 4 → ι =>
          evolvingFrameCurvatureFrameComponent F C slot s)
        hB (fun slot => hFrame s hs slot))
  have hmain := evolvingFrameCurvatureEnergy_le_gronwall_of_uniform_bounds
    (F := F) (C := C) (a := a) (b := b) (ε := ε)
    (A := N * A ^ 2) (B := N * B ^ 2) (E₀ := E₀)
    hcont hinit hIntrinsicEnergy hFrameEnergy hε
  intro t ht
  simpa [N, mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
    (hmain t ht)

end MorganTianLib

end

#print axioms MorganTianLib.finset_sum_sq_le_card_mul_sq_of_abs_le
#print axioms MorganTianLib.evolvingFrameCurvatureEnergy_le_of_component_bound
#print axioms MorganTianLib.evolvingFrameCurvatureEnergy_le_gronwall_of_component_bounds

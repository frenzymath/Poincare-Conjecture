import Topping.MaximumPrinciple.TensorNormAlgebra
import Topping.RicciFlow.CurvatureStar

/-!
# The constant in the curvature-evolution bound is uniform in the metric

`exists_normAt_le_of_isStarProduct` extracts its constant by induction on a
*derivation* of `IsStarProduct g A B C`, and that derivation mentions `g`. So the
constant it produces sits inside the scope of `g`: from it alone one gets
`∀ g, ∃ K, …`, not `∃ K, ∀ g, …`. TOP.CH03 flagged this (inbox I-0476/I-0479) after
first claiming the reverse.

The uniform statement is nevertheless true for the curvature-evolution correction,
and this module proves it. The reason is that
`curvatureEvolutionCorrection` is built from a **fixed** shape — eight terms, each
a double metric contraction of a permutation of `\Rm ⊗ \Rm` — and every factor the
norm estimate contributes depends only on the dimension:

* `normAt_permSlots` — permuting slots is an *isometry*, no constant at all;
* `normAt_traceFirstTwo_le` — each metric contraction costs exactly `√n`;
* `normAt_tensorProd` — the tensor product is multiplicative, no constant.

Two contractions cost `n`, and the twelve signed terms — four Ricci terms plus
twice four `B` terms — therefore give the explicit constant `12n`, independent of
`g` and of `p`. This is Topping's `C(n)`: a constant depending only on the
dimension, in the quantifier order that claim requires.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A double contraction of a permuted tensor product obeys the bound
`|C| ≤ n|A||B|` with the constant `n` depending on nothing but the dimension: each
of the two metric contractions costs `√n` and the permutation costs nothing.

This is the `g`-uniform building block: the constant is written down from the
*shape*, not extracted from a derivation, so it does not sit inside the scope of
`g`. -/
theorem normAt_contract₂Perm_le (g : RiemannianMetric I M)
    (σ : Equiv.Perm (Fin 8)) (A B : CovTensorField I M 4) (p : M) :
    normAt g (contract₂Perm g σ A B) p ≤
      (Module.finrank ℝ E : ℝ) * (normAt g A p * normAt g B p) := by
  have hn : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hsqrt : (0 : ℝ) ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := Real.sqrt_nonneg _
  -- Outer contraction.
  have h1 := normAt_traceFirstTwo_le g
    (k := 4) (traceFirstTwo (k := 6) g (permSlots σ (tensorProd (l := 4) A B))) p
  -- Inner contraction.
  have h2 := normAt_traceFirstTwo_le g
    (k := 6) (permSlots σ (tensorProd (l := 4) A B)) p
  -- Permutation is an isometry, and the tensor product is multiplicative.
  have h3 : normAt g (permSlots σ (tensorProd (l := 4) A B)) p
      = normAt g A p * normAt g B p := by
    rw [normAt_permSlots, normAt_tensorProd]
  rw [h3] at h2
  have hchain : normAt g (contract₂Perm g σ A B) p ≤
      Real.sqrt (Module.finrank ℝ E : ℝ) *
        (Real.sqrt (Module.finrank ℝ E : ℝ) * (normAt g A p * normAt g B p)) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 hsqrt)
  have hsq : Real.sqrt (Module.finrank ℝ E : ℝ) *
      Real.sqrt (Module.finrank ℝ E : ℝ) = (Module.finrank ℝ E : ℝ) :=
    Real.mul_self_sqrt hn
  calc normAt g (contract₂Perm g σ A B) p
      ≤ Real.sqrt (Module.finrank ℝ E : ℝ) *
          (Real.sqrt (Module.finrank ℝ E : ℝ) *
            (normAt g A p * normAt g B p)) := hchain
    _ = (Module.finrank ℝ E : ℝ) * (normAt g A p * normAt g B p) := by
        rw [← mul_assoc, hsq]

/-! ### The component form implies the compact form

Topping states the curvature evolution twice: compactly as
`∂_t\Rm = Δ\Rm + \Rm*\Rm`, and then in components with the eight explicit terms.
`HasCurvatureEvolutionOn` is the compact form, whose star factor is existentially
quantified. `HasCurvatureEvolutionComponentsOn` below is the component form, with
the correction pinned to `curvatureEvolutionCorrection`.

The implication between them is where the star product earns its keep: the
existential is discharged by the *named* witness, using
`isStarProduct_curvatureEvolutionCorrection`. Without that theorem the compact form
would be unreachable from the components. -/

/-- **Math.** Topping's component form of the curvature evolution: the time
derivative of `\Rm` is `Δ\Rm` plus the explicit eight-term correction. -/
def HasCurvatureEvolutionComponentsOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    Prop :=
  ∀ t ∈ J, ∀ (Y : Fin 4 → SmoothVectorField I M) (p : M),
    HasDerivWithinAt (fun s => riemannTensorField (g s) Y p)
      (roughLaplacian (g t) (g t).leviCivitaConnection
          (riemannTensorField (g t)) Y p
        + curvatureEvolutionCorrection (g t) Y p) J t

/-- **Math.** **Topping 2.5.1: the component form gives the compact form.** If the
curvature evolves by `Δ\Rm` plus the explicit correction, then it evolves by
`Δ\Rm + \Rm*\Rm` — because that correction *is* an `\Rm*\Rm`.

This is what discharges the existential in `HasCurvatureEvolutionOn`: the witness
is `curvatureEvolutionCorrection`, and the star-product obligation is
`isStarProduct_curvatureEvolutionCorrection`. -/
theorem hasCurvatureEvolutionOn_of_components {g : ℝ → RiemannianMetric I M}
    {J : Set ℝ} (h : HasCurvatureEvolutionComponentsOn g J) :
    HasCurvatureEvolutionOn g J :=
  fun t ht => ⟨curvatureEvolutionCorrection (g t),
    isStarProduct_curvatureEvolutionCorrection (g t), h t ht⟩

/-! ### Topping's `C(n)`, in the right quantifier order

The correction is a signed sum of eight `contract₂Perm` terms, four of them scaled
by `2`. Bounding term by term with the previous lemma and adding gives the constant
`(1+1+1+1) + 2(1+1+1+1) = 12` times `n`, uniform in `g` and `p`.

Written as `∃ K, ∀ g, ∀ p, …` — the quantifier order that "there is a constant
`C(n)`" actually asserts, and the one `exists_normAt_le_of_isStarProduct` cannot
give, since its constant is extracted from a derivation mentioning `g`. -/

/-- **Math.** **Topping's `C(n)` for the curvature-evolution correction, uniform
in the metric.** There is a constant depending only on the dimension — one may take
`12n` — such that for *every* metric and *every* point,
`|correction| ≤ C(n)|\Rm|^2`.

The uniformity is real and is what Chapter 3 needs: `K` is bound outside `g`, so a
time-dependent family `g t` gets the *same* constant at every time. That is exactly
the gap TOP.CH03 identified in I-0476/I-0479 — their bound is per-metric because
its constant comes from an `IsStarProduct` derivation; this one is read off the
fixed shape of the correction instead. -/
theorem exists_uniform_normAt_curvatureEvolutionCorrection_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : RiemannianMetric I M) (p : M),
      normAt g (curvatureEvolutionCorrection g) p ≤
        K * (normAt g (riemannTensorField g) p) ^ 2 := by
  refine ⟨12 * (Module.finrank ℝ E : ℝ), by positivity, fun g p => ?_⟩
  set Rm := riemannTensorField g with hRm
  set n := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  -- Every one of the eight terms is bounded by `n|Rm|^2`.
  have hterm : ∀ σ : Equiv.Perm (Fin 8), ∀ τ : Equiv.Perm (Fin 4),
      normAt g (permSlots τ (contract₂Perm g σ Rm Rm)) p ≤ n * normAt g Rm p ^ 2 := by
    intro σ τ
    rw [normAt_permSlots]
    have h := normAt_contract₂Perm_le g σ Rm Rm p
    calc normAt g (contract₂Perm g σ Rm Rm) p
        ≤ n * (normAt g Rm p * normAt g Rm p) := h
      _ = n * normAt g Rm p ^ 2 := by ring
  -- The correction is the signed combination; bound it by the triangle inequality.
  have hcorr : curvatureEvolutionCorrection g =
      fun Y q => (-1 : ℝ) *
            permSlots (Equiv.refl _) (contract₂Perm g starPermRic Rm Rm) Y q
          + permSlots (Equiv.swap 2 3) (contract₂Perm g starPermRic Rm Rm) Y q
          - permSlots argSwapPairs (contract₂Perm g starPermRic Rm Rm) Y q
          + permSlots argSwapPairsFlip (contract₂Perm g starPermRic Rm Rm) Y q
        + 2 * (permSlots (Equiv.refl _) (contract₂Perm g starPermB Rm Rm) Y q
            - permSlots (Equiv.swap 2 3) (contract₂Perm g starPermB Rm Rm) Y q
            + permSlots (Equiv.swap 1 2) (contract₂Perm g starPermB Rm Rm) Y q
            - permSlots argRotateLast (contract₂Perm g starPermB Rm Rm) Y q) := by
    funext Y q
    simp only [curvatureEvolutionCorrection, permSlots, hRm,
      contract₂Perm_starPermRic, contract₂Perm_starPermB,
      Equiv.refl_apply, argSwapPairs_zero, argSwapPairs_one, argSwapPairs_two,
      argSwapPairs_three, argSwapPairsFlip_zero, argSwapPairsFlip_one,
      argSwapPairsFlip_two, argSwapPairsFlip_three, argRotateLast_zero,
      argRotateLast_one, argRotateLast_two, argRotateLast_three,
      swap23_zero, swap23_one, swap23_two, swap23_three,
      swap12_zero, swap12_one, swap12_two, swap12_three]
    ring
  -- Abbreviate the eight terms.
  set R0 := permSlots (Equiv.refl (Fin 4)) (contract₂Perm g starPermRic Rm Rm)
  set R1 := permSlots (Equiv.swap 2 3) (contract₂Perm g starPermRic Rm Rm)
  set R2 := permSlots argSwapPairs (contract₂Perm g starPermRic Rm Rm)
  set R3 := permSlots argSwapPairsFlip (contract₂Perm g starPermRic Rm Rm)
  set B0 := permSlots (Equiv.refl (Fin 4)) (contract₂Perm g starPermB Rm Rm)
  set B1 := permSlots (Equiv.swap 2 3) (contract₂Perm g starPermB Rm Rm)
  set B2 := permSlots (Equiv.swap 1 2) (contract₂Perm g starPermB Rm Rm)
  set B3 := permSlots argRotateLast (contract₂Perm g starPermB Rm Rm)
  set b := n * normAt g Rm p ^ 2 with hb
  have hb0 : 0 ≤ b := by positivity
  -- Rewrite the correction as a sum of twelve summands, each of norm at most `b`.
  have hrw : curvatureEvolutionCorrection g =
      fun Y q => ((((-1 : ℝ) * R0 Y q + R1 Y q) + (-1 : ℝ) * R2 Y q) + R3 Y q)
        + (2 : ℝ) * (((B0 Y q + (-1 : ℝ) * B1 Y q) + B2 Y q)
            + (-1 : ℝ) * B3 Y q) := by
    rw [hcorr]; funext Y q; ring
  -- Each of the eight is bounded by `b`; scalar multiples scale the bound.
  have hR0 : normAt g R0 p ≤ b := hterm _ _
  have hR1 : normAt g R1 p ≤ b := hterm _ _
  have hR2 : normAt g R2 p ≤ b := hterm _ _
  have hR3 : normAt g R3 p ≤ b := hterm _ _
  have hB0 : normAt g B0 p ≤ b := hterm _ _
  have hB1 : normAt g B1 p ≤ b := hterm _ _
  have hB2 : normAt g B2 p ≤ b := hterm _ _
  have hB3 : normAt g B3 p ≤ b := hterm _ _
  have hneg : ∀ A : CovTensorField I M 4,
      normAt g (fun Y q => (-1 : ℝ) * A Y q) p = normAt g A p := by
    intro A
    rw [normAt_const_smul]
    simp
  -- Triangle inequality, four times on the Ricci block and four on the `B` block.
  have hRicBlock : normAt g
      (fun Y q => (((-1 : ℝ) * R0 Y q + R1 Y q) + (-1 : ℝ) * R2 Y q) + R3 Y q) p
      ≤ b + b + b + b := by
    refine (normAt_add_le g _ R3 p).trans ?_
    have h3 : normAt g
        (fun Y q => ((-1 : ℝ) * R0 Y q + R1 Y q) + (-1 : ℝ) * R2 Y q) p
        ≤ b + b + b := by
      refine (normAt_add_le g _ (fun Y q => (-1 : ℝ) * R2 Y q) p).trans ?_
      have h2 : normAt g (fun Y q => (-1 : ℝ) * R0 Y q + R1 Y q) p ≤ b + b :=
        (normAt_add_le g _ R1 p).trans (by rw [hneg R0]; linarith)
      rw [hneg R2]
      linarith
    linarith
  have hBBlock : normAt g
      (fun Y q => ((B0 Y q + (-1 : ℝ) * B1 Y q) + B2 Y q) + (-1 : ℝ) * B3 Y q) p
      ≤ b + b + b + b := by
    refine (normAt_add_le g _ (fun Y q => (-1 : ℝ) * B3 Y q) p).trans ?_
    have h3 : normAt g (fun Y q => (B0 Y q + (-1 : ℝ) * B1 Y q) + B2 Y q) p
        ≤ b + b + b := by
      refine (normAt_add_le g _ B2 p).trans ?_
      have h2 : normAt g (fun Y q => B0 Y q + (-1 : ℝ) * B1 Y q) p ≤ b + b :=
        (normAt_add_le g _ (fun Y q => (-1 : ℝ) * B1 Y q) p).trans
          (by rw [hneg B1]; linarith)
      linarith
    rw [hneg B3]
    linarith
  -- Assemble: the four Ricci terms plus twice the four `B` terms.
  rw [hrw]
  refine (normAt_add_le g _ _ p).trans ?_
  have hscaled : normAt g (fun Y q => (2 : ℝ) *
      (((B0 Y q + (-1 : ℝ) * B1 Y q) + B2 Y q) + (-1 : ℝ) * B3 Y q)) p
      ≤ 2 * (b + b + b + b) := by
    rw [normAt_const_smul]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    linarith [hBBlock]
  have hfinal : b + b + b + b + 2 * (b + b + b + b)
      = 12 * (Module.finrank ℝ E : ℝ) * normAt g Rm p ^ 2 := by
    rw [hb]; ring
  linarith [hRicBlock, hscaled]

end Topping

end

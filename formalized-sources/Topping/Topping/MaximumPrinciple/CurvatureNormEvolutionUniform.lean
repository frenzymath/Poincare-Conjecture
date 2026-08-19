import Topping.MaximumPrinciple.CurvatureStarBound
import Topping.RicciFlow.CurvatureStarUniform

/-!
# Proposition 3.2.10 with Topping's `C = C(n)`, on a whole time interval

`exists_curvatureNormEvolution_const_of_ingredients` proves Topping's
Proposition 3.2.10 **at a single time**, and that restriction was not cosmetic:
its constant came from `exists_normAt_le_of_isStarProduct`, whose induction runs
over a derivation of `IsStarProduct g \Rm \Rm Q` and therefore produces a `K`
inside the scope of `g`. At a family `g t` that is `K(t)`, so the conclusion could
not be quantified over `t` with one constant — and `HasCurvatureNormEvolutionInequalityOn g c J`,
the shape Theorem 3.2.11 consumes, needs exactly that.

TOP.CH02's `exists_uniform_normAt_curvatureEvolutionCorrection_le` closes the gap:
the correction of Topping 2.5.1 is a *fixed* shape (eight double contractions of
permutations of `\Rm ⊗ \Rm`), so its bound is read off the shape rather than
extracted from a derivation, and the constant — one may take `12n` — is bound
outside `g`. This module spends that:

* the pairing ingredient is restated with the **named norm correction**
  `curvatureNormEvolutionCorrection` in place of the existentially quantified
  star product (`HasCurvatureNormSqNamedPairingBoundOn`), which is what makes a
  `g`-uniform bound applicable.  Besides the correction in `∂ₜRm`, this includes
  the four inverse-metric derivatives in the contraction defining `|Rm|²`;
* `exists_uniform_curvatureNormEvolution_const` then gives
  `∃ c, 0 ≤ c ∧ ∀ g J, ingredients → HasCurvatureNormEvolutionInequalityOn g c J`,
  with `c` bound before the family, the interval, the time and the point. That
  quantifier order is what "there is `C = C(n)`" asserts (inbox I-0479);
* and `exists_uniform_riemannNormAt_le_of_ingredients` chains it through
  Theorem 3.2.11, so `|\Rm| ≤ M/(1 - ½CMt)` now follows from the two geometric
  ingredients with a single dimension-only `C`.

**Still hypothesis.** The differentiated time-dependent contraction (ingredient
1, now in named form).  The fixed-metric Bochner identity is supplied
unconditionally by `hasCurvatureBochnerIdentityOn`, so it is no longer an
antecedent of 3.2.10 or 3.2.11.
-/

open scoped ContDiff Manifold Topology Bundle
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ### The pairing against the actual correction, and its `g`-uniform bound -/

/-- **Math.** The quadratic correction in the evolution of `|Rm|²`.

The covariant curvature tensor contributes `curvatureEvolutionCorrection` through
`∂ₜRm`.  The norm also contracts four covariant slots with the inverse metric.
Under Ricci flow, each inverse metric has derivative `2 Ric`, so the four slots
contribute four copies of
`Ric(Rm(·,·)·,·) = contract₂Perm starPermRic Rm Rm`.  Thus

`∂ₜ|Rm|² = 2⟨Rm, ΔRm + curvatureNormEvolutionCorrection⟩`.

Keeping this term is essential: it has no fixed sign and cannot be discarded from
an upper bound. -/
def curvatureNormEvolutionCorrection (g : RiemannianMetric I M) :
    CovTensorField I M 4 :=
  fun Y p => curvatureEvolutionCorrection g Y p
    + 4 * contract₂Perm g starPermRic (riemannTensorField g)
        (riemannTensorField g) Y p

set_option linter.unusedSectionVars false in
/-- **Math.** The full norm-evolution correction is an `Rm * Rm`: both its
curvature-evolution part and the inverse-metric contraction part are fixed double
contractions of `Rm ⊗ Rm`. -/
theorem isStarProduct_curvatureNormEvolutionCorrection
    (g : RiemannianMetric I M) :
    IsStarProduct g (riemannCovTensorField g) (riemannCovTensorField g)
      (curvatureNormEvolutionCorrection g) := by
  rw [riemannCovTensorField_eq_riemannTensorField]
  change IsStarProduct g (riemannTensorField g) (riemannTensorField g)
    (fun Y p => curvatureEvolutionCorrection g Y p
      + 4 * contract₂Perm g starPermRic (riemannTensorField g)
          (riemannTensorField g) Y p)
  exact (isStarProduct_curvatureEvolutionCorrection g).add
    ((isStarProduct_contract₂Perm g starPermRic (riemannTensorField g)
      (riemannTensorField g)).smul 4)

set_option linter.unusedSectionVars false in
/-- **Math.** The full norm-evolution correction has a norm bound uniform in the
metric.  The old `curvatureEvolutionCorrection` contributes its uniform bound;
the four inverse-metric terms cost another `4n|Rm|²`. -/
theorem exists_uniform_normAt_curvatureNormEvolutionCorrection_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : RiemannianMetric I M) (p : M),
      normAt g (curvatureNormEvolutionCorrection g) p ≤
        K * (normAt g (riemannTensorField g) p) ^ 2 := by
  obtain ⟨K, hK, hcorr⟩ :=
    exists_uniform_normAt_curvatureEvolutionCorrection_le (I := I) (M := M)
  refine ⟨K + 4 * (Module.finrank ℝ E : ℝ), by positivity, fun g p => ?_⟩
  have hric := normAt_contract₂Perm_le g starPermRic
    (riemannTensorField g) (riemannTensorField g) p
  calc
    normAt g (curvatureNormEvolutionCorrection g) p
        ≤ normAt g (curvatureEvolutionCorrection g) p
          + normAt g (fun Y q => 4 *
              contract₂Perm g starPermRic (riemannTensorField g)
                (riemannTensorField g) Y q) p := by
            exact normAt_add_le g _ _ p
    _ = normAt g (curvatureEvolutionCorrection g) p
          + 4 * normAt g
              (contract₂Perm g starPermRic (riemannTensorField g)
                (riemannTensorField g)) p := by
            rw [normAt_const_smul]
            norm_num
    _ ≤ K * (normAt g (riemannTensorField g) p) ^ 2
          + 4 * ((Module.finrank ℝ E : ℝ) *
              (normAt g (riemannTensorField g) p *
                normAt g (riemannTensorField g) p)) := by
            exact add_le_add (hcorr g p)
              (mul_le_mul_of_nonneg_left hric (by norm_num))
    _ = (K + 4 * (Module.finrank ℝ E : ℝ)) *
          (normAt g (riemannTensorField g) p) ^ 2 := by ring

set_option linter.unusedSectionVars false in
/-- **Math.** **The pairing of `\Rm` against the norm-evolution correction is
at most `C(n)|\Rm|^3`, with `C(n)` uniform in the metric.**

This is Cauchy--Schwarz on top of TOP.CH02's uniform norm bound for
`curvatureNormEvolutionCorrection`. The binder order is the content: `K` is
bound before `g`, so a time-dependent family gets the *same* constant at every
time, unlike a constant extracted separately from each metric's star-product
derivation. -/
theorem exists_uniform_tensorInner_curvatureNormEvolutionCorrection_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : RiemannianMetric I M) (p : M),
      tensorInnerAt g (riemannCovTensorField g)
          (curvatureNormEvolutionCorrection g) p ≤
        K * riemannNormAt g p ^ 3 := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_normAt_curvatureNormEvolutionCorrection_le (I := I) (M := M)
  refine ⟨K, hK, fun g p => ?_⟩
  have hRnn : 0 ≤ riemannNormAt g p := riemannNormAt_nonneg g p
  have hnorm : normAt g (curvatureNormEvolutionCorrection g) p ≤
      K * riemannNormAt g p ^ 2 := by
    have h := hbound g p
    rwa [← riemannNormAt_eq_normAt_riemannTensorField] at h
  calc
    tensorInnerAt g (riemannCovTensorField g)
        (curvatureNormEvolutionCorrection g) p
      ≤ normAt g (riemannCovTensorField g) p *
          normAt g (curvatureNormEvolutionCorrection g) p :=
        tensorInnerAt_le g _ _ p
    _ = riemannNormAt g p *
          normAt g (curvatureNormEvolutionCorrection g) p := by
        rw [riemannNormAt]
    _ ≤ riemannNormAt g p * (K * riemannNormAt g p ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm hRnn
    _ = K * riemannNormAt g p ^ 3 := by ring

/-- **Math.** Ingredient 1 of Topping's Proposition 3.2.10 with the quadratic term
**named**: differentiating the contraction defining `|\Rm|^2` and substituting the
component form of `∂_t\Rm = Δ\Rm + \Rm*\Rm` bounds the time derivative by the
`Δ\Rm` pairing plus the pairing against `curvatureNormEvolutionCorrection`, which
also includes the variation of the four inverse metrics in `|\Rm|²`.

The difference from `HasCurvatureNormSqPairingBoundOn` is that the star product is
not existentially quantified: it is the one tensor the evolution equation has. That
is what makes the `g`-uniform bound applicable, and hence what makes the resulting
constant independent of `t`. -/
def HasCurvatureNormSqNamedPairingBoundOn (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    derivWithin (fun s => riemannNormAt (g s) p ^ 2) J t ≤
      2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
          (roughLaplacian (g t) (g t).leviCivitaConnection
            (riemannCovTensorField (g t))) p
        + 2 * tensorInnerAt (g t) (riemannCovTensorField (g t))
            (curvatureNormEvolutionCorrection (g t)) p

set_option linter.unusedSectionVars false in
/-- **Math.** The named ingredient is stronger than the existential one: the
full correction in the norm evolution *is* an `\Rm*\Rm`, by
`isStarProduct_curvatureNormEvolutionCorrection`. So nothing is lost by working
with the named form. -/
theorem hasCurvatureNormSqPairingBoundOn_of_named
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (h : HasCurvatureNormSqNamedPairingBoundOn g J) :
    HasCurvatureNormSqPairingBoundOn g J := by
  intro t ht
  refine ⟨curvatureNormEvolutionCorrection (g t), ?_, h t ht⟩
  exact isStarProduct_curvatureNormEvolutionCorrection (g t)

/-! ### Proposition 3.2.10 on an interval, with one constant -/

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Proposition 3.2.10, with `C = C(n)`.** There is a constant
depending only on the dimension such that, for *every* family of metrics and
*every* time set, the two geometric ingredients imply

`∂_t|\Rm|^2 ≤ Δ|\Rm|^2 - 2|∇\Rm|^2 + C|\Rm|^3`

at every time of the set and every point.

The quantifier order is the whole point: `c` is bound before `g`, before `J`,
before `t` and before `p`, which is what the book's `C = C(n)` asserts. The
single-time version `exists_curvatureNormEvolution_const_of_ingredients` cannot be
strengthened this way, since its constant is extracted from an `IsStarProduct`
derivation mentioning the metric. -/
theorem exists_uniform_curvatureNormEvolution_const :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ),
      HasCurvatureNormSqNamedPairingBoundOn g J →
      HasCurvatureNormEvolutionInequalityOn g c J := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_uniform_tensorInner_curvatureNormEvolutionCorrection_le
      (I := I) (M := M)
  refine ⟨2 * K, by linarith, fun g J hpair t ht p => ?_⟩
  have hcs := hbound (g t) p
  have hbochp := curvatureBochnerIdentity (g t) p
  have hpairp := hpair t ht p
  rw [hbochp]
  linarith

/-! ### Theorem 3.2.11 with one dimension-only constant

The `|\Rm|` bound consumes the *weakened* inequality (the favourable `-2|∇\Rm|^2`
discarded), so the constant carries through unchanged. Chaining gives Topping's
Theorem 3.2.11 with a `C` fixed before the flow. -/

set_option linter.unusedSectionVars false in
/-- **Math.** **Topping, Theorem 3.2.11, with `C = C(n)`.** There is a constant
depending only on the dimension such that for every family of metrics on a closed
manifold satisfying the two ingredients of Proposition 3.2.10, and with
`|\Rm| ≤ m` at `t = 0`,

`|\Rm| ≤ m / (1 - ½Cmt)`

on any interval `[0,T]` on which the denominator stays positive.

Two honest caveats, both inherited rather than introduced here.

* `hdenom` is unremovable, not merely unproved: past `t = 2/(Cm)` the right-hand
  side is negative while `|\Rm| ≥ 0`, so the book's displayed statement is false
  there and the maximal-time argument that removes the analogous hypothesis for
  the *lower* scalar barrier does not apply to an *upper* one (inbox I-0459,
  I-0460).
* `hm : 0 < m` excludes the book's `m = 0`.

What is new is that `c` is bound before `g`, `m` and `T`, so the constant in the
conclusion is Topping's `C(n)` and not a `C(n, g)`. -/
theorem exists_uniform_riemannNormAt_le_of_ingredients [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (g : ℝ → RiemannianMetric I M) (m T : ℝ),
      0 ≤ T → 0 < m →
      ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
        ((Set.univ : Set M) ×ˢ Icc 0 T) →
      (∀ x t, t ∈ Icc 0 T →
        HasDerivWithinAt (fun s => riemannNormAt (g s) x ^ 2)
          (derivWithin (fun s => riemannNormAt (g s) x ^ 2) (Icc 0 T) t)
          (Icc 0 T) t) →
      HasCurvatureNormSqNamedPairingBoundOn g (Icc 0 T) →
      (∀ t ∈ Icc 0 T, 0 < 1 - c * m * t / 2) →
      (∀ p, riemannNormAt (g 0) p ≤ m) →
      ∀ p t, t ∈ Icc 0 T →
        riemannNormAt (g t) p ≤ m / (1 - c * m * t / 2) := by
  obtain ⟨c, hc, hprop⟩ :=
    exists_uniform_curvatureNormEvolution_const (I := I) (M := M)
  refine ⟨c, hc, fun g m T hT hm hcont hderiv hpair hdenom hzero => ?_⟩
  exact riemannNormAt_le hT hc hm hcont
    (fun t _ht => riemannNormAt_sq_contMDiff (g t)) hderiv
    (hasCurvatureNormSqInequalityOn_of_evolutionInequality
      (hprop g (Icc 0 T) hpair))
    hdenom hzero

#print axioms Topping.isStarProduct_curvatureNormEvolutionCorrection
#print axioms Topping.exists_uniform_normAt_curvatureNormEvolutionCorrection_le
#print axioms Topping.exists_uniform_curvatureNormEvolution_const

end Topping

end

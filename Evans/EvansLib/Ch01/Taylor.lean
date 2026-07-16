import EvansLib.Ch01.Multiindex
import EvansLib.Ch01.Problems
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Evans, Ch. 1, Exercise 4 — Taylor's formula in multiindex notation

Evans' Chapter 1, Exercise 4 asks to prove, for smooth `f : ℝⁿ → ℝ`,
`f(x) = ∑_{|α| ≤ k} (1/α!) Dᵅf(0) xᵅ + O(|x|^{k+1})` as `x → 0`, the multiindex
form of Taylor's theorem.

The route (Evans' hint): fix `x` and study the one-variable function
`g(t) = f(t·x)`. Its `j`-th ordinary derivative is the `j`-th **directional**
derivative of `f` along `x`, and expanding that directional derivative by the
multinomial theorem (`Finset.sum_pow_eq_sum_piAntidiag`) gives
`g⁽ʲ⁾(0) = ∑_{|α|=j} \binom{j}{α} Dᵅf(0) xᵅ`. Summing `g⁽ʲ⁾(0)/j!` over `j ≤ k`
produces the multiindex Taylor polynomial; the one-variable Taylor remainder
transports to the `O(|x|^{k+1})` bound.

This file builds that bridge on top of the coordinate multiindex calculus of
`EvansLib.Ch01.Multiindex`:

* `dirDeriv v f = x ↦ Df(x)(v)`, the directional derivative along a fixed
  vector `v` (so `partialDeriv i = dirDeriv (eᵢ)`).
* `iteratedDeriv_comp_line_dir`: the `j`-fold ordinary derivative of the line
  restriction `t ↦ f(x + t·v)` is `(dirDeriv v)^[j] f` along the line — the
  arbitrary-direction generalization of `EvansLib.iteratedDeriv_comp_line`.
* `dirDeriv_eq_sum`: `dirDeriv v f = ∑ᵢ vᵢ · ∂ᵢf`, expressing the directional
  derivative as the `v`-weighted combination of coordinate partials.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.5,
Exercise 4 and Appendix A.2–A.3.
-/

open scoped BigOperators ContDiff

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-! ## The directional derivative operator `Dᵥ` -/

/-- The **directional derivative** `Dᵥf = x ↦ Df(x)(v)` of `f : ℝⁿ → ℝ` along a
fixed vector `v`. The coordinate partial `∂ᵢ` is the special case `v = eᵢ`:
`partialDeriv i = dirDeriv (EuclideanSpace.single i 1)`. -/
def dirDeriv (v : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => fderiv ℝ f x v

lemma dirDeriv_apply (v : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    dirDeriv v f x = fderiv ℝ f x v := rfl

/-- `partialDeriv i` is directional differentiation along the `i`-th basis vector. -/
lemma partialDeriv_eq_dirDeriv (i : Fin n) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    partialDeriv i f = dirDeriv (EuclideanSpace.single i 1) f := rfl

/-- Directional differentiation preserves smoothness. -/
theorem dirDeriv_contDiff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : EuclideanSpace ℝ (Fin n)) : ContDiff ℝ ∞ (dirDeriv v f) :=
  (hf.fderiv_right (by simp)).clm_apply contDiff_const

/-- Iterating directional differentiation preserves smoothness. -/
theorem dirDeriv_iterate_contDiff {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    ContDiff ℝ ∞ ((dirDeriv v)^[m] f) := by
  induction m generalizing f with
  | zero => simpa using hf
  | succ k ih => rw [Function.iterate_succ_apply]; exact ih (dirDeriv_contDiff hf v)

/-! ## Reduction to one variable along an arbitrary line -/

/-- **Reduction to one variable, arbitrary direction.** The `m`-fold ordinary
derivative of the line restriction `t ↦ f(x + t·v)` equals the `m`-fold
directional derivative `(Dᵥ)^[m] f` evaluated along that line. This is the
arbitrary-direction analogue of `EvansLib.iteratedDeriv_comp_line`. -/
lemma iteratedDeriv_comp_line_dir (v : EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    ∀ {f : EuclideanSpace ℝ (Fin n) → ℝ}, ContDiff ℝ ∞ f →
      iteratedDeriv m (fun t : ℝ => f (x + t • v))
        = fun s : ℝ => (dirDeriv v)^[m] f (x + s • v) := by
  induction m with
  | zero => intro f _; funext s; simp
  | succ k ih =>
    intro f hf
    rw [iteratedDeriv_succ, ih hf]
    funext s
    have hsmooth : ContDiff ℝ ∞ ((dirDeriv v)^[k] f) := dirDeriv_iterate_contDiff hf v k
    rw [(hasDerivAt_comp_line (hsmooth.differentiable (by simp)) x v s).deriv,
      Function.iterate_succ_apply']
    rfl

/-- The `j`-fold ordinary derivative of `t ↦ f(t·x)` at `t = 0` is the `j`-fold
directional derivative of `f` along `x` at the origin: `g⁽ʲ⁾(0) = (Dₓ)^[j] f 0`
for `g(t) = f(t·x)`. -/
lemma iteratedDeriv_scaled_line {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f)
    (x : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => f (t • x)) 0 = (dirDeriv x)^[j] f 0 := by
  have h := congrFun (iteratedDeriv_comp_line_dir x 0 j hf) 0
  simpa using h

/-! ## The directional derivative as a weighted sum of coordinate partials -/

/-- The standard basis expansion of a vector in `ℝⁿ`: `v = ∑ᵢ vᵢ · eᵢ`. -/
lemma sum_smul_single_eq (v : EuclideanSpace ℝ (Fin n)) :
    ∑ i, v i • EuclideanSpace.single i (1 : ℝ) = v := by
  simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr]
    using (EuclideanSpace.basisFun (Fin n) ℝ).sum_repr v

/-- **The directional derivative is the `v`-weighted sum of coordinate partials.**
`Dᵥf(x) = ∑ᵢ vᵢ · ∂ᵢf(x)`. This holds with no differentiability hypothesis: both
sides are `fderiv ℝ f x` (which is `0` where `f` is not differentiable) evaluated
by linearity on the basis expansion of `v`. -/
theorem dirDeriv_eq_sum (v : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    dirDeriv v f = fun x => ∑ i, v i * partialDeriv i f x := by
  funext x
  rw [dirDeriv_apply]
  conv_lhs => rw [← sum_smul_single_eq v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- Pointwise form of `dirDeriv_eq_sum`. -/
lemma dirDeriv_apply_sum (v : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    dirDeriv v f x = ∑ i, v i * partialDeriv i f x := by
  rw [dirDeriv_eq_sum]

/-! ## Multinomial Pascal rule and the reindexing bijection

Iterating `Dᵥ = ∑ᵢ vᵢ∂ᵢ` produces, at order `j+1`, the sum over pairs `(i, α)`
with `|α| = j` of `\binom{j}{α} v^{α+eᵢ} D^{α+eᵢ}`. Reindexing `β = α + eᵢ`
collects, for each `β` with `|β| = j+1`, the coefficient `∑_{i : βᵢ ≥ 1}
\binom{j}{β - eᵢ}`, which the **multinomial Pascal rule** identifies with
`\binom{j+1}{β}`. -/

open Finset in
/-- Factoring one coordinate out of the factorial product: for `βᵢ ≥ 1`,
`∏ₖ βₖ! = (∏ₖ (β-eᵢ)ₖ!) · βᵢ`. -/
private theorem prod_factorial_sub_single {n : ℕ} (β : Fin n → ℕ) (i : Fin n) (hi : 1 ≤ β i) :
    (∏ k, (β k).factorial)
      = (∏ k, ((β - (Pi.single i 1 : Fin n → ℕ)) k).factorial) * β i := by
  rw [← Finset.mul_prod_erase univ (fun k => (β k).factorial) (mem_univ i),
      ← Finset.mul_prod_erase univ
        (fun k => ((β - (Pi.single i 1 : Fin n → ℕ)) k).factorial) (mem_univ i)]
  have herase : ∏ k ∈ univ.erase i, ((β - (Pi.single i 1 : Fin n → ℕ)) k).factorial
      = ∏ k ∈ univ.erase i, (β k).factorial :=
    Finset.prod_congr rfl fun k hk => by simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk)]
  rw [herase]
  have hβi : (β - (Pi.single i 1 : Fin n → ℕ)) i = β i - 1 := by simp [Pi.single_eq_same]
  rw [hβi, ← Nat.mul_factorial_pred (Nat.one_le_iff_ne_zero.mp hi)]; ring

open Finset in
/-- The weight drops by one on subtracting a basis multiindex: for `βᵢ ≥ 1`,
`|β - eᵢ| = |β| - 1`. -/
private theorem sum_sub_single {n : ℕ} (β : Fin n → ℕ) (i : Fin n) (hi : 1 ≤ β i) :
    ∑ k, (β - (Pi.single i 1 : Fin n → ℕ)) k = (∑ k, β k) - 1 := by
  rw [← Finset.add_sum_erase univ (fun k => (β - (Pi.single i 1 : Fin n → ℕ)) k) (mem_univ i),
      ← Finset.add_sum_erase univ (fun k => β k) (mem_univ i)]
  have herase : ∑ k ∈ univ.erase i, (β - (Pi.single i 1 : Fin n → ℕ)) k
      = ∑ k ∈ univ.erase i, β k :=
    Finset.sum_congr rfl fun k hk => by simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk)]
  rw [herase]
  have hβi : (β - (Pi.single i 1 : Fin n → ℕ)) i = β i - 1 := by simp [Pi.single_eq_same]
  rw [hβi]; omega

open Finset in
/-- Only coordinates with `βᵢ ≥ 1` contribute to `∑ βᵢ`. -/
private theorem sum_filter_one_le {n : ℕ} (β : Fin n → ℕ) :
    ∑ i ∈ univ.filter (fun i => 1 ≤ β i), β i = ∑ i, β i := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun i => 1 ≤ β i) β]
  have : ∑ i ∈ univ.filter (fun i => ¬ 1 ≤ β i), β i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      simp only [Finset.mem_filter, not_le, Nat.lt_one_iff] at hi; exact hi.2
  omega

open Finset in
/-- **Multinomial Pascal rule.** For `|β| ≥ 1`,
`∑_{i : βᵢ ≥ 1} \binom{|β|-1}{β-eᵢ} = \binom{|β|}{β}`, i.e.
`∑ᵢ multinomial(β - eᵢ) = multinomial(β)` (summed over `i` with `βᵢ ≥ 1`). -/
theorem multinomial_pascal {n : ℕ} (β : Fin n → ℕ) (hβ : 1 ≤ ∑ i, β i) :
    ∑ i ∈ univ.filter (fun i => 1 ≤ β i),
        Nat.multinomial univ (β - (Pi.single i 1 : Fin n → ℕ)) = Nat.multinomial univ β := by
  have hMpos : 0 < ∏ k, (β k).factorial := Finset.prod_pos fun k _ => Nat.factorial_pos _
  apply Nat.eq_of_mul_eq_mul_left hMpos
  have hRHS : (∏ k, (β k).factorial) * Nat.multinomial univ β = (∑ i, β i).factorial :=
    Nat.multinomial_spec univ β
  have hLHS : ∀ i ∈ univ.filter (fun i => 1 ≤ β i),
      (∏ k, (β k).factorial) * Nat.multinomial univ (β - (Pi.single i 1 : Fin n → ℕ))
        = β i * ((∑ k, β k) - 1).factorial := by
    intro i hi
    have hi1 : 1 ≤ β i := (Finset.mem_filter.mp hi).2
    have hspec := Nat.multinomial_spec univ (β - (Pi.single i 1 : Fin n → ℕ))
    rw [sum_sub_single β i hi1] at hspec
    rw [prod_factorial_sub_single β i hi1, mul_right_comm, hspec, mul_comm]
  rw [Finset.mul_sum, Finset.sum_congr rfl hLHS, ← Finset.sum_mul, sum_filter_one_le, hRHS]
  exact Nat.mul_factorial_pred (by omega)

open Finset in
/-- **Reindexing the order-`(j+1)` multinomial sum.** For any weight `P`, summing
`multinomial(α)·P(α+eᵢ)` over `i` and over `|α| = j` equals summing
`multinomial(β)·P(β)` over `|β| = j+1`. The bijection is `(i, α) ↔ (β, i)` with
`β = α + eᵢ`; the coefficient collapse is `multinomial_pascal`. -/
private theorem multinomial_reindex {n j : ℕ} (P : (Fin n → ℕ) → ℝ) :
    (∑ i, ∑ α ∈ piAntidiag univ j,
        (Nat.multinomial univ α : ℝ) * P (α + (Pi.single i 1 : Fin n → ℕ)))
      = ∑ β ∈ piAntidiag univ (j + 1), (Nat.multinomial univ β : ℝ) * P β := by
  have hpascal : ∀ β ∈ piAntidiag (univ : Finset (Fin n)) (j + 1),
      (Nat.multinomial univ β : ℝ) * P β
        = ∑ i ∈ univ.filter (fun i => 1 ≤ β i),
            (Nat.multinomial univ (β - (Pi.single i 1 : Fin n → ℕ)) : ℝ) * P β := by
    intro β hβ
    have hsum : 1 ≤ ∑ i, β i := by
      have := (Finset.mem_piAntidiag.mp hβ).1; simp only [this]; omega
    rw [← Finset.sum_mul, ← Nat.cast_sum, multinomial_pascal β hsum]
  rw [Finset.sum_congr rfl hpascal,
    Finset.sum_sigma' (piAntidiag univ (j + 1)) (fun β => univ.filter (fun i => 1 ≤ β i))
      (fun β i => (Nat.multinomial univ (β - (Pi.single i 1 : Fin n → ℕ)) : ℝ) * P β),
    ← Finset.sum_product' univ (piAntidiag univ j)
      (fun i α => (Nat.multinomial univ α : ℝ) * P (α + (Pi.single i 1 : Fin n → ℕ)))]
  refine Finset.sum_nbij'
    (fun p => (⟨p.2 + Pi.single p.1 1, p.1⟩ : Σ _ : (Fin n → ℕ), Fin n))
    (fun q => (q.2, q.1 - Pi.single q.2 1)) ?_ ?_ ?_ ?_ ?_
  · -- forward maps product → sigma
    rintro ⟨i, α⟩ hp
    rw [Finset.mem_product] at hp
    have hα : ∑ k, α k = j := (Finset.mem_piAntidiag.mp hp.2).1
    rw [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_filter]
    refine ⟨⟨?_, fun k _ => mem_univ k⟩, mem_univ i, ?_⟩
    · rw [show (univ.sum (α + Pi.single i 1)) = ∑ k, (α k + (Pi.single i 1 : Fin n → ℕ) k) from rfl,
        Finset.sum_add_distrib, hα]
      simp
    · simp [Pi.single_eq_same]
  · -- backward maps sigma → product
    rintro ⟨β, i⟩ hq
    rw [Finset.mem_sigma, Finset.mem_piAntidiag, Finset.mem_filter] at hq
    obtain ⟨⟨hβsum, _⟩, _, hβi⟩ := hq
    have hβsum' : (∑ k, β k) = j + 1 := hβsum
    have hβi' : 1 ≤ β i := hβi
    rw [Finset.mem_product]
    refine ⟨mem_univ i, ?_⟩
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun k _ => mem_univ k⟩
    rw [sum_sub_single β i hβi']; omega
  · -- left inverse
    rintro ⟨i, α⟩ _
    refine Prod.ext rfl ?_
    funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
  · -- right inverse
    rintro ⟨β, i⟩ hq
    rw [Finset.mem_sigma, Finset.mem_filter] at hq
    have hβi : 1 ≤ β i := hq.2.2
    simp only [Sigma.mk.injEq, heq_eq_eq, and_true]
    funext k
    by_cases hk : k = i
    · subst hk
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]; omega
    · simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hk]; omega
  · -- value equality
    rintro ⟨i, α⟩ _
    have hsub : (α + Pi.single i 1) - (Pi.single i 1 : Fin n → ℕ) = α := by
      funext k; simp only [Pi.sub_apply, Pi.add_apply]; omega
    simp only [hsub]

/-! ## The operator multinomial expansion of `Dᵥ^{[j]}` -/

open Finset in
/-- Differentiating a `Dᵅ`-linear combination along axis `i` shifts each `α` to
`α + eᵢ`: `∂ᵢ(∑_α cα Dᵅf) = ∑_α cα D^{α+eᵢ}f`. -/
private theorem partialDeriv_multinomial_sum {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℝ) :
    partialDeriv i (fun y => ∑ α ∈ S, c α * multiPartial α f y)
      = fun x => ∑ α ∈ S, c α * multiPartial (α + (Pi.single i 1 : Fin n → ℕ)) f x := by
  have hbody : (fun y => ∑ α ∈ S, c α * multiPartial α f y)
      = (fun y => ∑ α ∈ S, (c α • multiPartial α f) y) := by
    funext y; exact Finset.sum_congr rfl fun α _ => by simp [smul_eq_mul]
  rw [hbody, partialDeriv_fun_sum i S (fun α => c α • multiPartial α f)
        (fun α _ => (contDiff_const.smul (multiPartial_contDiff hf α)).differentiable (by simp))]
  funext x
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [partialDeriv_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← multiPartial_add_single hf i α]

open Finset in
/-- **Operator multinomial expansion.** The `j`-fold directional derivative
`Dᵥ^{[j]}f = (∑ᵢ vᵢ∂ᵢ)^{[j]} f` expands over multiindices of weight `j`:
`Dᵥ^{[j]}f = ∑_{|α|=j} \binom{j}{α} vᵅ Dᵅf`, with `\binom{j}{α} = j!/α!` the
multinomial coefficient and `vᵅ = ∏ᵢ vᵢ^{αᵢ}`. This is the multivariable
Faà-di-Bruno identity for the line restriction `t ↦ f(t·x)`. -/
theorem dirDeriv_iterate_eq_multinomial {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (v : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    (dirDeriv v)^[j] f
      = fun x => ∑ α ∈ piAntidiag univ j,
          (Nat.multinomial univ α : ℝ) * (∏ i, v i ^ α i) * multiPartial α f x := by
  induction j with
  | zero =>
    funext x
    simp [Finset.piAntidiag_zero, Nat.multinomial]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, dirDeriv_eq_sum]
    funext x
    -- differentiate the order-k expansion along each axis
    have hstep : ∀ i, partialDeriv i (fun y => ∑ α ∈ piAntidiag univ k,
          (Nat.multinomial univ α : ℝ) * (∏ l, v l ^ α l) * multiPartial α f y) x
        = ∑ α ∈ piAntidiag univ k, (Nat.multinomial univ α : ℝ) * (∏ l, v l ^ α l)
              * multiPartial (α + (Pi.single i 1 : Fin n → ℕ)) f x := fun i =>
      congrFun (partialDeriv_multinomial_sum hf i (piAntidiag univ k)
        (fun α => (Nat.multinomial univ α : ℝ) * (∏ l, v l ^ α l))) x
    -- rearrange each summand into `multinomial α · (v^{α+eᵢ} · D^{α+eᵢ}f)`
    have e1 : (∑ i, v i * partialDeriv i (fun y => ∑ α ∈ piAntidiag univ k,
          (Nat.multinomial univ α : ℝ) * (∏ l, v l ^ α l) * multiPartial α f y) x)
        = ∑ i, ∑ α ∈ piAntidiag univ k, (Nat.multinomial univ α : ℝ)
            * ((∏ l, v l ^ (α + (Pi.single i 1 : Fin n → ℕ)) l)
                * multiPartial (α + (Pi.single i 1 : Fin n → ℕ)) f x) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hstep i, Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hvi : (∏ l, v l ^ (α + (Pi.single i 1 : Fin n → ℕ)) l)
          = (∏ l, v l ^ α l) * v i := by
        have hfac : ∀ l, v l ^ (α + (Pi.single i 1 : Fin n → ℕ)) l
            = v l ^ α l * v l ^ (Pi.single i 1 : Fin n → ℕ) l := fun l => by
          rw [Pi.add_apply, pow_add]
        rw [Finset.prod_congr rfl (fun l _ => hfac l), Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_eq_single i]
        · simp [Pi.single_eq_same]
        · intro l _ hl; simp [Pi.single_eq_of_ne hl]
        · intro h; exact absurd (mem_univ i) h
      rw [hvi]; ring
    -- reindex `β = α + eᵢ` collapses the coefficients via `multinomial_pascal`
    rw [e1, multinomial_reindex (fun β => (∏ l, v l ^ β l) * multiPartial β f x)]
    exact Finset.sum_congr rfl fun α _ => by ring

/-! ## The multiindex derivatives of the line restriction -/

open Finset in
/-- **Key bridge.** The `j`-th ordinary derivative at `0` of the line restriction
`g(t) = f(t·x)` is the multinomial sum of the multiindex derivatives of `f`:
`g⁽ʲ⁾(0) = ∑_{|α|=j} \binom{j}{α} Dᵅf(0) xᵅ`. This combines the reduction to one
variable (`iteratedDeriv_scaled_line`) with the operator multinomial expansion
(`dirDeriv_iterate_eq_multinomial`), and is the coefficient identity underlying
Taylor's formula in multiindex notation. -/
theorem iteratedDeriv_scaled_line_multinomial {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) (j : ℕ) :
    iteratedDeriv j (fun t : ℝ => f (t • x)) 0
      = ∑ α ∈ piAntidiag univ j,
          (Nat.multinomial univ α : ℝ) * (∏ i, x i ^ α i) * multiPartial α f 0 := by
  rw [iteratedDeriv_scaled_line hf, dirDeriv_iterate_eq_multinomial hf]

open Finset in
/-- The multinomial coefficient over the factorial-of-weight equals the reciprocal
multiindex factorial: for `|α| = j`, `\binom{j}{α}/j! = 1/α!`, i.e.
`multinomial(α) = j!/∏ᵢαᵢ!`. Cast to `ℝ`. -/
theorem multinomial_div_factorial {n j : ℕ} (α : Fin n → ℕ) (hα : ∑ i, α i = j) :
    (Nat.multinomial univ α : ℝ) * (1 / (j.factorial : ℝ)) = 1 / (∏ i, (α i).factorial : ℝ) := by
  have hspec : (∏ i, ((α i).factorial : ℝ)) * (Nat.multinomial univ α : ℝ) = (j.factorial : ℝ) := by
    have h := Nat.multinomial_spec univ α
    rw [hα] at h; exact_mod_cast h
  have hprodpos : (0 : ℝ) < ∏ i, ((α i).factorial : ℝ) :=
    Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _
  have hjpos : (0 : ℝ) < (j.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos j
  rw [mul_one_div, div_eq_div_iff hjpos.ne' hprodpos.ne', one_mul, mul_comm]
  exact hspec

/-- The generalized bridge at an arbitrary base point `s`: the `j`-th ordinary
derivative of `t ↦ f(t·x)` at `s` is the multinomial sum of the multiindex
derivatives of `f` evaluated at `s·x`. -/
theorem iteratedDeriv_scaled_line_multinomial_at {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) (j : ℕ) (s : ℝ) :
    iteratedDeriv j (fun t : ℝ => f (t • x)) s
      = ∑ α ∈ Finset.piAntidiag Finset.univ j,
          (Nat.multinomial Finset.univ α : ℝ) * (∏ i, x i ^ α i) * multiPartial α f (s • x) := by
  have hfun : (fun t : ℝ => f (0 + t • x)) = fun t : ℝ => f (t • x) := by
    funext t; rw [zero_add]
  have h := congrFun (iteratedDeriv_comp_line_dir x 0 j hf) s
  rw [hfun] at h
  rw [h, zero_add, dirDeriv_iterate_eq_multinomial hf]

/-! ## Multiindex Taylor's formula (Evans, Ch. 1, Exercise 4) -/

open Finset in
/-- The **multiindex Taylor polynomial** of order `k` at the origin:
`∑_{|α| ≤ k} (1/α!) Dᵅf(0) xᵅ`, written as the iterated sum over `j ≤ k` and
multiindices `α` of weight `j` (with `α! = ∏ᵢ αᵢ!` and `xᵅ = ∏ᵢ xᵢ^{αᵢ}`). -/
def multiTaylorPoly (k : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j ∈ range (k + 1), ∑ α ∈ piAntidiag univ j,
    (1 / (∏ i, ((α i).factorial : ℝ))) * multiPartial α f 0 * (∏ i, x i ^ α i)

open Finset in
/-- The monomial `xᵅ` is bounded by `‖x‖^{|α|}`: `|∏ᵢ xᵢ^{αᵢ}| ≤ ‖x‖^{∑αᵢ}`,
using the coordinate bound `|xᵢ| ≤ ‖x‖` for the Euclidean norm. -/
theorem abs_prod_pow_le (x : EuclideanSpace ℝ (Fin n)) (α : Fin n → ℕ) :
    |∏ i, x i ^ α i| ≤ ‖x‖ ^ (∑ i, α i) := by
  rw [Finset.abs_prod]
  calc ∏ i, |x i ^ α i|
      = ∏ i, |x i| ^ α i := by simp [abs_pow]
    _ ≤ ∏ i, ‖x‖ ^ α i :=
        Finset.prod_le_prod (fun i _ => pow_nonneg (abs_nonneg _) _)
          (fun i _ => pow_le_pow_left₀ (abs_nonneg _)
            (by rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le x i) _)
    _ = ‖x‖ ^ (∑ i, α i) := by rw [Finset.prod_pow_eq_pow_sum]

open Finset in
/-- **Polynomial identity.** The one-variable Taylor polynomial of `g(t) = f(t·x)`
at `t = 0`, evaluated at `t = 1`, equals the multiindex Taylor polynomial of `f`
at `x`. The order-`j` coefficient `g⁽ʲ⁾(0)/j!` unpacks, via the bridge
`iteratedDeriv_scaled_line_multinomial` and `multinomial_div_factorial`, into
`∑_{|α|=j} (1/α!) Dᵅf(0) xᵅ`. -/
theorem taylorWithinEval_scaled_line_eq {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : EuclideanSpace ℝ (Fin n)) (k : ℕ) :
    taylorWithinEval (fun t : ℝ => f (t • x)) k (Set.uIcc 0 1) 0 1 = multiTaylorPoly k f x := by
  have hg : ContDiff ℝ ∞ (fun t : ℝ => f (t • x)) := hf.comp (contDiff_id.smul contDiff_const)
  have huniq : UniqueDiffOn ℝ (Set.uIcc (0 : ℝ) 1) := by
    rw [Set.uIcc_of_le zero_le_one]; exact uniqueDiffOn_Icc zero_lt_one
  have hmem0 : (0 : ℝ) ∈ Set.uIcc (0 : ℝ) 1 := Set.left_mem_uIcc
  rw [taylor_within_apply, multiTaylorPoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDerivWithin_eq_iteratedDeriv huniq (hg.contDiffAt.of_le (by exact_mod_cast le_top)) hmem0,
    iteratedDeriv_scaled_line_multinomial hf, sub_zero, one_pow, mul_one,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hcoef := multinomial_div_factorial α (Finset.mem_piAntidiag.mp hα).1
  rw [inv_eq_one_div, ← hcoef]; ring

open Finset in
/-- **Taylor's formula in multiindex notation** (Evans, *Partial Differential
Equations*, Ch. 1, Exercise 4). For smooth `f : ℝⁿ → ℝ` and every order `k`,
`f(x) = ∑_{|α| ≤ k} (1/α!) Dᵅf(0) xᵅ + O(|x|^{k+1})` as `x → 0`, formalized as the
big-`O` bound of the residual against `‖x‖^{k+1}` near the origin.

The proof follows Evans' hint: restrict to the line `g(t) = f(t·x)`, apply the
one-variable Taylor theorem with Lagrange remainder, identify the Taylor
polynomial with the multiindex polynomial via `taylorWithinEval_scaled_line_eq`,
and bound the order-`(k+1)` remainder uniformly on the unit ball using the
operator multinomial expansion (`iteratedDeriv_scaled_line_multinomial_at`) and
the monomial bound `abs_prod_pow_le`. -/
theorem taylor_multiindex {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    (fun x => f x - multiTaylorPoly k f x) =O[nhds 0] fun x => ‖x‖ ^ (k + 1) := by
  -- A uniform bound `M` on `∑_{|α|=k+1} multinomial(α)·|Dᵅf|` over the unit ball.
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).exists_bound_of_continuousOn
    (f := fun y => ∑ α ∈ piAntidiag univ (k + 1),
        (Nat.multinomial univ α : ℝ) * |multiPartial α f y|)
    (Continuous.continuousOn (continuous_finset_sum _ fun α _ =>
      continuous_const.mul (multiPartial_contDiff hf α).continuous.abs))
  have hfacpos : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  rw [Asymptotics.isBigO_iff]
  refine ⟨M / ((k + 1).factorial : ℝ), ?_⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin n)) zero_lt_one]
    with x hxball
  rw [Metric.mem_closedBall, dist_zero_right] at hxball
  -- one-variable Taylor with Lagrange remainder for `g(t) = f(t·x)`
  have hg : ContDiff ℝ ∞ (fun t : ℝ => f (t • x)) := hf.comp (contDiff_id.smul contDiff_const)
  obtain ⟨ξ, hξ, hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := fun t : ℝ => f (t • x)) (x₀ := 0) (x := 1) (n := k)
    zero_ne_one (hg.contDiffOn.of_le (by exact_mod_cast le_top))
  rw [Set.uIoo_of_le zero_le_one] at hξ
  -- the residual is the Lagrange remainder
  have hres : f x - multiTaylorPoly k f x
      = iteratedDeriv (k + 1) (fun t : ℝ => f (t • x)) ξ / ((k + 1).factorial : ℝ) := by
    simp only [one_smul] at hrem
    rw [taylorWithinEval_scaled_line_eq hf x k] at hrem
    rw [hrem]; norm_num
  -- ξ·x lies in the unit ball
  have hξball : ξ • x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hξ.1]
    nlinarith [hξ.2.le, hxball, norm_nonneg x, hξ.1.le]
  -- bound the remainder numerator by `M·‖x‖^{k+1}`
  have hbound : |iteratedDeriv (k + 1) (fun t : ℝ => f (t • x)) ξ| ≤ M * ‖x‖ ^ (k + 1) := by
    rw [iteratedDeriv_scaled_line_multinomial_at hf x (k + 1) ξ]
    calc |∑ α ∈ piAntidiag univ (k + 1),
            (Nat.multinomial univ α : ℝ) * (∏ i, x i ^ α i) * multiPartial α f (ξ • x)|
        ≤ ∑ α ∈ piAntidiag univ (k + 1),
            |(Nat.multinomial univ α : ℝ) * (∏ i, x i ^ α i) * multiPartial α f (ξ • x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ α ∈ piAntidiag univ (k + 1),
            (Nat.multinomial univ α : ℝ) * |multiPartial α f (ξ • x)| * ‖x‖ ^ (k + 1) := by
          refine Finset.sum_le_sum fun α hα => ?_
          have hweight : ∑ i, α i = k + 1 := (Finset.mem_piAntidiag.mp hα).1
          have hx1 : |∏ i, x i ^ α i| ≤ ‖x‖ ^ (k + 1) := hweight ▸ abs_prod_pow_le x α
          calc |(Nat.multinomial univ α : ℝ) * (∏ i, x i ^ α i) * multiPartial α f (ξ • x)|
              = (Nat.multinomial univ α : ℝ) * |∏ i, x i ^ α i| * |multiPartial α f (ξ • x)| := by
                rw [abs_mul, abs_mul, abs_of_nonneg (by positivity)]
            _ ≤ (Nat.multinomial univ α : ℝ) * |multiPartial α f (ξ • x)| * ‖x‖ ^ (k + 1) := by
                rw [show (Nat.multinomial univ α : ℝ) * |∏ i, x i ^ α i| * |multiPartial α f (ξ • x)|
                      = ((Nat.multinomial univ α : ℝ) * |multiPartial α f (ξ • x)|)
                          * |∏ i, x i ^ α i| from by ring]
                exact mul_le_mul_of_nonneg_left hx1 (by positivity)
      _ = (∑ α ∈ piAntidiag univ (k + 1),
            (Nat.multinomial univ α : ℝ) * |multiPartial α f (ξ • x)|) * ‖x‖ ^ (k + 1) := by
          rw [Finset.sum_mul]
      _ ≤ M * ‖x‖ ^ (k + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          have hle := hM (ξ • x) hξball
          rwa [Real.norm_eq_abs,
            abs_of_nonneg (Finset.sum_nonneg fun α _ => by positivity)] at hle
  -- assemble
  rw [hres]
  rw [show ‖(‖x‖ ^ (k + 1) : ℝ)‖ = ‖x‖ ^ (k + 1) from by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hfacpos, div_le_iff₀ hfacpos]
  calc |iteratedDeriv (k + 1) (fun t : ℝ => f (t • x)) ξ|
      ≤ M * ‖x‖ ^ (k + 1) := hbound
    _ = M / ((k + 1).factorial : ℝ) * ‖x‖ ^ (k + 1) * ((k + 1).factorial : ℝ) := by
        field_simp

end EvansLib

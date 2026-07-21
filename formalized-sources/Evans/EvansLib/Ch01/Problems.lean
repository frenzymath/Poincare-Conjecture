import Mathlib.Data.Nat.Choose.Multinomial

/-!
# Evans, Ch. 1 §1.5 — Problems (multiindex practice)

Evans' Chapter 1 exercises. Exercise 1 (classify each PDE of §1.2 by type and
order) is discharged by the classification theorems attached to every example in
`EvansLib.Ch01.Examples` … `EvansLib.Ch01.PhysicalSystems` (e.g.
`EvansLib.laplaceSymbol_isLinearPDE`, `EvansLib.eulerSymbol_isQuasilinearPDESystem`).

Exercise 2 — the **Multinomial Theorem** in multiindex notation — is formalized
below. It is the special case, over the finite index set `Fin n`, of mathlib's
general multinomial expansion `Finset.sum_pow_eq_sum_piAntidiag`.

Exercises 3 (Leibniz' formula `Dᵅ(uv) = ∑_{β≤α} \binom{α}{β} Dᵝu \, D^{α-β}v`) and
4 (multiindex Taylor's formula) require the multiindex partial-derivative operator
`Dᵅ`, which mathlib does not provide (everything is phrased through the
coordinate-free `iteratedFDeriv`). That operator and its calculus are built in
`EvansLib.Ch01.Multiindex`: the coordinate partial `EvansLib.partialDeriv`, the
multiindex derivative `EvansLib.multiPartial` (`Dᵅ`), the equality of mixed
partials `EvansLib.partialDeriv_comm` (Clairaut), and the **single-axis** iterated
Leibniz rule `EvansLib.partialDeriv_iterate_mul`. The full multiindex Leibniz
(Exercise 3) reduces to the single-axis rule plus Clairaut via a Pascal induction
on `|α|`, and multiindex Taylor (Exercise 4) reduces along the line `t ↦ f(t·x)`
using `EvansLib.iteratedDeriv_comp_line`; both assemblies remain to be formalized.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §1.5.
-/

open scoped BigOperators

namespace EvansLib

/-- **Evans, Ch. 1, Exercise 2 (Multinomial Theorem).** For variables
`x = (x₁, …, xₙ)`,
`(x₁ + ⋯ + xₙ)ᵏ = ∑_{|α| = k} \binom{|α|}{α} xᵅ`,
where the sum ranges over multiindices `α : Fin n → ℕ` with `|α| = ∑ᵢ αᵢ = k`
(the finite set `Finset.piAntidiag univ k`), `xᵅ = ∏ᵢ xᵢ^{αᵢ}`, and the
multinomial coefficient `\binom{|α|}{α} = |α|! / α! = k! / ∏ᵢ αᵢ!` is
`Nat.multinomial univ α`. Stated over an arbitrary commutative semiring `R`
(Evans' `R = ℝ` is the special case). This is exactly mathlib's
`Finset.sum_pow_eq_sum_piAntidiag` specialized to the index set `Fin n`. -/
theorem multinomial_theorem {R : Type*} [CommSemiring R] (n k : ℕ) (x : Fin n → R) :
    (∑ i, x i) ^ k
      = ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k,
          (Nat.multinomial Finset.univ α : R) * ∏ i, x i ^ α i :=
  Finset.sum_pow_eq_sum_piAntidiag Finset.univ x k

/-- The index set of the multinomial theorem is exactly the multiindices of
weight `k`: `α ∈ Finset.piAntidiag univ k ↔ |α| = k`. -/
theorem mem_multiindex_weight (n k : ℕ) (α : Fin n → ℕ) :
    α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) k ↔ ∑ i, α i = k := by
  simp [Finset.mem_piAntidiag]

end EvansLib

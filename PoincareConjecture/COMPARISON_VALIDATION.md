# Dini comparison and the scalar lifetime bound

## Mathematical scope

This contribution proves the analytic comparison layer used in the primary
finite-extinction argument. It does **not** prove the geometric width
inequality, construct Ricci flow with surgery, classify extinct components, or
prove the Poincare theorem. Those inputs are neither hidden in definitions nor
introduced as axioms. The lifetime theorem explicitly assumes a scalar width
satisfying the regularity, Dini inequality, initial bound, and no-upward-jump
conditions.

The source is Morgan--Tian, *Ricci Flow and the Poincare Conjecture*,
[arXiv:math/0607607v2](https://arxiv.org/html/math/0607607v2): Lemma 2.22
(forward comparison), Section 18.3.2 (the scalar argument for Theorem 18.1),
and Claims 18.21--18.22 (regular-time continuity and the surgery liminf).
This implementation follows the primary blueprint rather than porting or
modifying the reference packages.

## Corrected endpoint statement

At the starting revision `bb91a091f0b968f8bbe8d861e025a88d82b161be`, the
finite-jump blueprint lemma constrained only interior partition points but
concluded comparison on the closed interval. With one interval `[0,1]`, the
function that is zero before `1` and equals `1` at `1` is a counterexample for
the zero differential equation and zero comparison function.

The corrected statement controls **all right endpoints, including the final
one**. Lean uses `LowerSemicontinuousWithinAt f (Iio b) b`: for every `r < f b`,
eventually `r < f t` as `t` approaches `b` from the left. This is precisely
the no-upward-jump condition, allowing oscillations and not requiring an actual
finite left limit. In the geometric application the final endpoint is covered
by regular-time continuity or the surgery liminf, as appropriate.

## Proof-to-blueprint correspondence

| Blueprint node | Checked Lean conclusion |
| --- | --- |
| `thm:forward-dini-comparison` | `dini_le_of_contDiffOn`: continuous subsolutions with upper right Dini bounds stay below the comparison solution. A one-sided Lipschitz constant is derived on a compact rectangle, not added as a global assumption. |
| `lem:forward-dini-comparison-with-downward-jumps` | `dini_le_of_finite_jumps`: induction over any finite strict partition, with only half-open continuity and no upward jumps. The zero-interval case is included. |
| `lem:scalar-width-lifetime-bound` | `exists_width_lifetime_bound`: a finite time depending only on initial time and width forces every admissible width surviving that long to be negative, independently of the number and placement of partition points. |

`UpperRightDiniLE` means that every strict upper bound eventually bounds the
right-hand secant slopes. No derivative of the subsolution is assumed.
The analytic proof uses Mathlib's one-sided fencing theorem with the strict
barrier `G(t) + ε exp((L+1)(t-a))`, then lets `ε` tend to zero.

The scalar equation is exactly

```text
w' = -2π + 3w / (1 + 4t),    w(s) = A,    s ≥ 0.
```

`hasDerivAt_extinctionBarrier` and `extinctionBarrier_initial` check the
explicit solution against this equation and initial value. Eventual
negativity is proved using the limit `(1+4t)^(-1/4) → 0`, not numerical
sampling. Initial-width sensitivity and monotonicity are proved separately.

## Reproduction

The existing pins are unchanged:

```text
Lean:    leanprover/lean4:v4.32.1
Mathlib: 520045ab14e26149ee970e2e617ca04b09bde5d6
```

From this directory:

```sh
lake exe cache get
lake build
```

The default build includes `PoincareConjectureTests.lean`, which proves:

- the terminal-endpoint counterexample and its rejection by the repaired hypothesis;
- comparison for a real downward discontinuity at an interior partition point,
  together with a proof that the test function is not continuous there;
- comparison for the zero-interval partition and the scalar initial-value identity.

The test module also collects the **transitive kernel axiom dependencies** of
every declaration in the production and test namespaces. It rejects any axiom
outside `propext`, `Classical.choice`, and `Quot.sound`, including `sorryAx`
and native-decision trust axioms. This is stronger than checking source text
for placeholders. The audit runs as part of the default build.

For the repository's dependency-aware validation, from the repository root:

```sh
scripts/validate-lean-changes.sh origin/main
```

On macOS this script requires the modern Bash installed by Homebrew, because
it uses associative arrays; put that Bash on `PATH` before running the script.
No reference package or pinned dependency is changed by this contribution.

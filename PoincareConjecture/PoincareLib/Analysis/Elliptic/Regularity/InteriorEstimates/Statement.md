# Uniform Interior Estimates From Elliptic Powers

## Informal description

Let $O$ be open in $\mathbb R^d$, $d\geq1$, and let
$L=\sum_{i,j}a^{ij}\partial_i\partial_j+\sum_i b^i\partial_i$
have smooth real coefficients on $O$, with $a$ symmetric positive definite
at every point. Let $V$ be open with compact closure contained in $O$,
and let $K\subset V$ be compact. For every integer $m\geq0$, there are an
integer $q\geq0$ and a constant $C>0$, depending only on these fixed data,
such that every smooth real function $u$ on $O$ satisfies, for all $x\in K$,
\[
 \|D^m u(x)\|\leq C\sum_{j=0}^q\|L^ju\|_{L^2(V)}.
\]
The measure is Lebesgue measure, $L^0u=u$, and the pointwise formulation
includes the empty compact set.

## Informal proof

Extend the coefficients smoothly near the compact closure of $V$, preserving
uniform ellipticity there, and extend each solution by a fixed cutoff equal
to one near that closure. Locality preserves every operator power on $V$.
Testing the divergence equation with a squared cutoff times the solution
gives a quantitative first-derivative estimate. Integration by parts in its
smooth drift term moves that derivative onto fixed coefficients and the
cutoff. The quantitative difference-quotient energy estimate and weak
derivative extraction give the second-derivative estimate with its constant.
Differentiating the divergence equation, bounding coefficient commutators,
and choosing fixed intermediate neighborhoods retain constants at every
higher order. Strong induction bounds each local Sobolev profile by finitely
many actual powers of $L$. Quantitative L2 Sobolev embedding on balls and a
finite cover of $K$ give the stated pointwise bound. Every neighborhood,
cutoff and constant is chosen before $u$.

## Proposed formal statements

The differential operator is `secondOrderOperator` from `Operators/Basic.lean`,
defined by the displayed operator formula with classical coordinate partials.
The declaration below is checked in `Uniform.lean`; the retained-metric heat
kernel application is checked in
`Geometry/Riemannian/Heat/Kernel/Regularity/SpacetimeJets.lean`.

```lean
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Basic
import PoincareLib.Analysis.Elliptic.Regularity.Coefficients

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Elliptic.InteriorEstimates

theorem uniform_interior_estimate_of_elliptic_powers
    {d : ℕ} [NeZero d]
    {O V K : Set (EuclideanSpace ℝ (Fin d))}
    (hO : IsOpen O) (hV : IsOpen V)
    (hVc : IsCompact (closure V)) (hVO : closure V ⊆ O)
    (hK : IsCompact K) (hKV : K ⊆ V)
    (a : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ ∞ (fun x => a x i j) O)
    (hpos : ∀ x ∈ O, (a x).PosDef)
    (hb : ∀ i, ContDiffOn ℝ ∞ (b i) O) (m : ℕ) :
    ∃ q : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ {u : EuclideanSpace ℝ (Fin d) → ℝ}, ContDiffOn ℝ ∞ u O → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ m u x‖ ≤ C * ∑ j ∈ Finset.range (q + 1),
          (eLpNorm ((secondOrderOperator a b)^[j] u) 2 (volume.restrict V)).toReal

end Poincare.Analysis.Elliptic.InteriorEstimates
```

## Informal translation

Let $d$ be a positive integer. Let $O,V\subset\mathbb R^d$ be open, with
$\overline V$ compact and contained in $O$, and let $K$ be a compact subset
of $V$. Let $a$ be a real matrix-valued field whose entries are smooth on
$O$ and whose value at every point of $O$ is symmetric positive definite.
Let each component of the real vector field $b$ be smooth on $O$, and put
$Lu=\sum_{i,j}a_{ij}\partial_i\partial_j u+\sum_i b_i\partial_i u$.
For every nonnegative integer $m$, there exist a nonnegative integer $q$
and a positive real number $C$ such that, for every real-valued function
$u$ smooth on $O$ and every $x\in K$,
\[
 \|D^m u(x)\|\leq C\sum_{j=0}^{q}\|L^ju\|_{L^2(V,dx)}.
\]
Here $D^m$ has the multilinear operator norm and $L^0u=u$.

## Alignment review

The separate local translation and comparison passes found no discrepancy
in hypotheses, quantifiers, operator convention, measure, or conclusion.
Both the integer and positive constant precede the function; positive
definiteness over the reals includes symmetry; the pointwise conclusion
permits $K$ to be empty. Each displayed L2 norm is finite because the
coefficients and function are smooth near the compact closure of $V$.

Native independent dispatch was attempted with a fresh context and failed
with `agent thread limit reached`. The separate local passes above use the
fallback in the statement-alignment profile. This is a semantic comparison,
not an independent proof review or kernel evidence.

## References

Evans, *Partial Differential Equations*, second edition, Section 6.3.1,
Theorem 1, printed p. 327 (PDF p. 341), Theorem 2, printed pp. 332-333
(PDF pp. 346-347), and Section 5.6.3, Theorem 6. The iterated-operator
estimate is a consequence of these results, not separately numbered.
The checked source is archived under `references/partial-differential-equations/evans/`.

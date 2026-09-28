# Local smoothness of weak elliptic eigenfunctions

## Informal proof

On nested relatively compact balls, the smooth positive definite coefficients
have uniform ellipticity and derivative bounds. Compactly supported difference
quotient tests give local second weak derivatives in L2. Differentiating the
weak equation and repeating these estimates gives every local Sobolev order.
Sobolev embedding produces smooth representatives on smaller balls.
Continuity and almost-everywhere agreement identify them on overlaps, so they
glue to a smooth representative on the whole open domain.

## Proposed formal statements

```lean
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

open Set MeasureTheory
open scoped ContDiff

namespace Poincare.Analysis.Elliptic

theorem exists_smooth_representative
    {n : ℕ} (hn : 0 < n)
    {O : Set (EuclideanSpace ℝ (Fin n))} (hO : IsOpen O)
    (A : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (c u : EuclideanSpace ℝ (Fin n) → ℝ)
    (p : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hc : ContDiffOn ℝ ∞ c O)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hpartial : ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * φ x))
    (heq : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) =
      ∫ x in O, c x * u x * φ x) :
    ∃ U : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiffOn ℝ ∞ U O ∧ U =ᵐ[volume.restrict O] u := by
  sorry

end Poincare.Analysis.Elliptic
```

## Informal translation

Let n be a positive integer, O an open subset of R^n, A a matrix-valued
function on R^n, and c, u, p_1, ..., p_n real functions on R^n. Assume the
entries of A and c are smooth on O, A is symmetric positive definite at every
point of O, and u and each p_i are square integrable on every compact subset
of O. For every globally smooth test function with compact support in O,
assume the displayed weak derivative identities and the divergence-form
equation. Then there is a function U on R^n smooth on O and equal to u almost
everywhere on O for Lebesgue measure.

## Alignment review

Independent native translator and reviewer accepted the statement on
17 September 2026. Ambient extensions outside O have no effect, compact-local
L2 is the specified local L2 condition, and global smooth tests with compact
support in O represent exactly the required test space by zero extension.

## Reusable prerequisites

### Informal proof

For the second-derivative theorem, cutoff localization reduces to globally
square-integrable data with uniformly elliptic coefficients on a smaller
neighborhood. Smooth approximation permits the difference-quotient test in
the original weak equation. Coercivity and Young's inequality bound the
difference quotients of the weak gradient. Riesz representation then constructs
the second weak derivatives.

For the representative theorem, choose the local Sobolev order above each
desired differentiability order plus half the dimension. Sobolev embedding
gives continuous representatives of every finite differentiability order.
Almost-everywhere equality identifies them on open overlaps, yielding a
smooth representative.

### Proposed formal statements

The following are the complete signatures reviewed independently. `MemWkp`
is the recursively defined weak Sobolev predicate, with its actual weak
derivative identities.

```lean
open Set MeasureTheory
open scoped ContDiff
open Poincare.Analysis.Sobolev.Euclidean

theorem Poincare.Analysis.Elliptic.exists_memWkp_two_of_weakEquation
    {d : ℕ} [NeZero d]
    {O : Set (EuclideanSpace ℝ (Fin d))} (hO : IsOpen O)
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (u f : EuclideanSpace ℝ (Fin d) → ℝ)
    (p : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => A x i j) O)
    (hpos : ∀ x ∈ O, (A x).PosDef)
    (hu : ∀ K, IsCompact K → K ⊆ O → MemLp u 2 (volume.restrict K))
    (hp : ∀ i K, IsCompact K → K ⊆ O → MemLp (p i) 2 (volume.restrict K))
    (hf : ∀ K, IsCompact K → K ⊆ O → MemLp f 2 (volume.restrict K))
    (hpartial : ∀ i φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in O, p i x * φ x))
    (heq : ∀ φ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      (∫ x in O, ∑ i, ∑ j, A x i j * p j x *
        fderiv ℝ φ x (EuclideanSpace.single i 1)) = ∫ x in O, f x * φ x)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ O) :
    ∃ W : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ MemWkp 2 2 u W

theorem Poincare.Analysis.Sobolev.EuclideanIteratedEmbedding.exists_smooth_representative_of_memWkp_locally
    {d : ℕ} [NeZero d]
    {u : EuclideanSpace ℝ (Fin d) → ℝ}
    {Ω : Set (EuclideanSpace ℝ (Fin d))}
    (hu : ∀ x ∈ Ω, ∀ k : ℕ, ∃ V : Set (EuclideanSpace ℝ (Fin d)),
      IsOpen V ∧ x ∈ V ∧ V ⊆ Ω ∧ MemWkp k 2 u V) :
    ∃ U : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiffOn ℝ ∞ U Ω ∧ U =ᵐ[volume.restrict Ω] u
```

### Informal translation

Let d be a positive integer and O an open subset of R^d. Let A be a smooth
symmetric positive definite matrix field on O. Suppose that u, f, and each
p_i are square integrable on every compact subset of O, that p_i is the weak
ith partial derivative of u, and that the integral of A times the weak
gradient paired with the gradient of every smooth compactly supported test
function equals the integral of f times that test function. Every point of O
has an open neighborhood W contained in O such that u belongs to W^{2,2}(W).

Let d be a positive integer, Ω a subset of R^d, and u a real function on R^d.
Suppose that for every point x in Ω and every nonnegative integer k, there
is an open neighborhood V of x contained in Ω on which u belongs to
W^{k,2}(V). There exists a real function U on R^d that is smooth on Ω and
equals u almost everywhere on Ω for Lebesgue measure.

### Alignment review

The independent native translator and alignment reviewer accepted both
prerequisites on 17 September 2026. The first statement needs only pointwise
positive definiteness and compact-local square integrability. In the second,
the neighborhood hypothesis implies that Ω is open; the neighborhood may
depend on both the point and the Sobolev order.

## References

This auxiliary local theorem supports Chow et al., *The Ricci Flow: Techniques
and Applications*, Part III, Theorem 24.30, Section 24.5.1, printed p. 290
(PDF p. 311). Source adaptation uses Chow--Liao--Qin, revision
`1b535dd102b94cc42b107cca27059687888f08b3`, especially
`Analysis/Sobolev/Nirenberg/H2Regularity/`,
`Analysis/Sobolev/Tools/DifferenceQuotientWeakLimitLoc.lean`, and
`Analysis/Sobolev/Euclidean/Embedding/`.

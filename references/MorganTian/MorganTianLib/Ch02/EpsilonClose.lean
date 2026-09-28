import MorganTianLib.Ch01.LeviCivita
import MorganTianLib.Ch01.OrthoFrame

/-!
# Morgan--Tian Ch. 2 -- epsilon-closeness of Riemannian metrics

This file defines the `C^[1/epsilon]` metric comparison used for epsilon-necks.
An open subset is itself a manifold, so the definitions are stated for two
metrics on the same manifold.  The family version adds a time parameter but no
time derivatives.
-/

open Riemannian
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The value of `nabla_(g0)^n (g - g0)` on `n + 2` smooth vector fields.

The first field in the successor case is the differentiation direction.  The
finite sum subtracts the connection correction in every existing covariant
slot, including the two metric slots. -/
def iteratedCovariantMetricDifference
    (g0 g : RiemannianMetric I M) :
    (n : ℕ) -> (Fin (n + 2) -> SmoothVectorField I M) -> M -> ℝ
  | 0, X, p =>
      g.metricInner p (X 0 p) (X 1 p) -
        g0.metricInner p (X 0 p) (X 1 p)
  | n + 1, X, p =>
      let U := X 0
      let Y : Fin (n + 2) -> SmoothVectorField I M := fun i => X i.succ
      U.dir (iteratedCovariantMetricDifference g0 g n Y) p -
        ∑ i : Fin (n + 2),
          iteratedCovariantMetricDifference g0 g n
            (Function.update Y i (g0.leviCivitaConnection.cov U (Y i))) p

/-- **Math.** The squared pointwise `g0`-norm of `nabla_(g0)^n (g - g0)`.

The contraction is evaluated in a local `g0`-orthonormal frame centered at
`p`.  At positive orders this is also the norm of `nabla_(g0)^n g`, since the
Levi-Civita connection of `g0` annihilates `g0`. -/
def metricCovariantDerivativeNormSq
    (g0 g : RiemannianMetric I M) (n : ℕ) (p : M) : ℝ :=
  ∑ indices : Fin (n + 2) -> Fin (Module.finrank ℝ E),
    (iteratedCovariantMetricDifference g0 g n
      (fun i => orthoFrameField g0 p (indices i)) p) ^ 2

/-- **Math.** The integer derivative order `[1 / epsilon]`. -/
def epsilonDerivativeOrder (epsilon : ℝ) : ℕ :=
  ⌊epsilon⁻¹⌋₊

/-- **Math.** The pointwise quantity under the supremum in epsilon-closeness. -/
def epsilonClosenessDensity
    (epsilon : ℝ) (g0 g : RiemannianMetric I M) (p : M) : ℝ :=
  metricCovariantDerivativeNormSq g0 g 0 p +
    ∑ l ∈ Finset.Icc 1 (epsilonDerivativeOrder epsilon),
      metricCovariantDerivativeNormSq g0 g l p

/-- **Math.** `g` is epsilon-close to `g0` in the `C^[1/epsilon]` topology.

The witness `C < epsilon^2` is the strict uniform upper bound represented by
the supremum in the book.  Taking this manifold to be an open submanifold `X`
gives the stated definition for metrics on `X`. -/
def EpsilonClose
    (epsilon : ℝ) (g0 g : RiemannianMetric I M) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 ∧
    ∃ C : ℝ, C < epsilon ^ 2 ∧
      ∀ p : M, epsilonClosenessDensity epsilon g0 g p ≤ C

/-- **Math.** Uniform epsilon-closeness for metric families.  Only spatial covariant
derivatives enter; the parameter type carries no differentiable structure. -/
def EpsilonCloseFamily {T : Type*}
    (epsilon : ℝ) (g0 g : T -> RiemannianMetric I M) : Prop :=
  0 < epsilon ∧ epsilon < 1 / 2 ∧
    ∃ C : ℝ, C < epsilon ^ 2 ∧
      ∀ t : T, ∀ p : M,
        epsilonClosenessDensity epsilon (g0 t) (g t) p ≤ C

end MorganTianLib

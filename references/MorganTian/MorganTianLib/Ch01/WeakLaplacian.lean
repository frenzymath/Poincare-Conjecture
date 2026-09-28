import MorganTianLib.Ch01.RiemannianMeasure
import MorganTianLib.Ch02.Laplacian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Morgan-Tian Ch. 1 - the Laplacian in the weak sense

This file packages the definition used in the blueprint remark
`rem:laplacian-weak-sense`.  For a locally Lipschitz function `f` and a
locally integrable function `h`, the distributional inequality `Delta f <= h`
means that

`integral f * Delta phi dvol_g <= integral h * phi dvol_g`

for every nonnegative, compactly supported smooth test function `phi`.
The Riemannian volume measure is parameterized by the additive Haar measure on
the model space, consistently with `RiemannianMeasure.lean`.
-/

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [SigmaCompactSpace M] [T2Space M] [Nonempty M]

/-- **Math.** The distributional (equivalently, weak) inequality
`Delta f <= h` on the Riemannian manifold `(M, g)`.

Here `f` is locally Lipschitz, `h` is locally integrable for the Riemannian
volume measure, and the inequality is tested against every nonnegative,
compactly supported smooth function `phi`:
`integral_M f Delta phi dvol_g <= integral_M h phi dvol_g`.

The additive Haar measure `mu` fixes the normalization of the Riemannian
measure.  Rescaling it by a positive constant rescales both integrals equally.
Blueprint: `rem:laplacian-weak-sense`. -/
def WeakLaplacianLE (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (f h : M → ℝ) : Prop :=
  LocallyLipschitz f ∧
    LocallyIntegrable h (riemannianMeasure (I := I) g mu) ∧
    ∀ phi : M → ℝ,
      0 ≤ phi →
      HasCompactSupport phi →
      ContMDiff I 𝓘(ℝ, ℝ) ∞ phi →
      (∫ x, f x * laplacianAt g g.leviCivitaConnection phi x
          ∂(riemannianMeasure (I := I) g mu))
        ≤ ∫ x, h x * phi x ∂(riemannianMeasure (I := I) g mu)

end MorganTianLib

end

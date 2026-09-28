import MorganTianLib.Ch01.WeakLaplacianBridge

/-!
# Morgan--Tian Ch. 1: an analytic reduction for the distance function

The distance-function example in the blueprint has two genuinely separate
analytic inputs.  First, the weak Green identity identifies the test integral
for the distance function with the radial derivative pairing.  Second, polar
coordinates and volume comparison bound that pairing by
`(n - 1) / dist p x`.  This file records those inputs explicitly and proves
their formal consequence.  The geometric proof of the polar bound is kept as
an input rather than represented by an unproved axiom.
-/

open MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [SigmaCompactSpace M] [T2Space M] [Nonempty M]

/-- **Math.** The radial pairing appearing in the weak Green identity for `dist p ·`.

The pairing is intentionally an explicit function argument.  In the usual
Riemannian proof it is the almost-everywhere quantity
`⟪∇ (dist p ·), ∇ φ⟫`; making it an argument keeps this interface independent
of a choice of measurable representative for the weak gradient.
-/
def DistanceWeakGreenIdentity
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (p : M)
    (pairing : (M → ℝ) → M → ℝ) : Prop :=
  ∀ phi : M → ℝ,
    HasCompactSupport phi →
    ContMDiff I 𝓘(ℝ, ℝ) ∞ phi →
    (∫ x, dist p x * laplacianAt g g.leviCivitaConnection phi x
        ∂(riemannianMeasure (I := I) g mu)) =
      -∫ x, pairing phi x ∂(riemannianMeasure (I := I) g mu)

/-- **Math.** The polar-coordinate test-function estimate for the distance function.

This is the exact inequality obtained after integrating the radial derivative
in polar coordinates.  The theorem below only uses this estimate, so the
substantial cut-locus and volume-comparison argument can be supplied
independently.
-/
def DistancePolarTestInequality
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (p : M) (n : ℕ)
    (pairing : (M → ℝ) → M → ℝ) : Prop :=
  ∀ phi : M → ℝ,
    0 ≤ phi →
    HasCompactSupport phi →
    ContMDiff I 𝓘(ℝ, ℝ) ∞ phi →
    (-∫ x, pairing phi x ∂(riemannianMeasure (I := I) g mu)) ≤
      ∫ x, ((n : ℝ) - 1) / dist p x * phi x
        ∂(riemannianMeasure (I := I) g mu)

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [SigmaCompactSpace M] [T2Space M] [Nonempty M] in
/-- **Math.** The distance from a fixed point is globally `1`-Lipschitz. -/
theorem lipschitzWith_one_distanceFrom (p : M) :
    LipschitzWith 1 (fun x : M => dist p x) := by
  exact LipschitzWith.dist_right p

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [SigmaCompactSpace M] [T2Space M] [Nonempty M] in
/-- **Math.** In particular, the distance from a fixed point is locally Lipschitz. -/
theorem locallyLipschitz_distanceFrom (p : M) :
    LocallyLipschitz (fun x : M => dist p x) := by
  exact (lipschitzWith_one_distanceFrom p).locallyLipschitz

/-- **Math.**
If the weak Green identity and the polar test-function estimate are available,
then they imply the weak upper-Laplacian bound for the distance function.

The local integrability hypothesis is explicit: it is an analytic consequence
of the dimension/volume behavior near `p`, and is not assumed by the
definition of the two identities above.
-/
theorem weakLaplacianLE_distanceFrom_of_green_and_polar
    (mu : Measure E) [mu.IsAddHaarMeasure]
    (g : RiemannianMetric I M) (p : M) (n : ℕ)
    (pairing : (M → ℝ) → M → ℝ)
    (hInt : LocallyIntegrable
      (fun x : M => ((n : ℝ) - 1) / dist p x)
      (riemannianMeasure (I := I) g mu))
    (hGreen : DistanceWeakGreenIdentity (I := I) mu g p pairing)
    (hPolar : DistancePolarTestInequality (I := I) mu g p n pairing) :
    WeakLaplacianLE (I := I) mu g
      (fun x : M => dist p x)
      (fun x : M => ((n : ℝ) - 1) / dist p x) := by
  refine ⟨locallyLipschitz_distanceFrom p, hInt, ?_⟩
  intro phi hphi hcompact hsmooth
  rw [hGreen phi hcompact hsmooth]
  exact hPolar phi hphi hcompact hsmooth

end MorganTianLib

end

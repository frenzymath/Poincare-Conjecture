import Topping.MaximumPrinciple.CurvatureNorm
import Topping.RicciFlow.Basic
import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Chapter 5: maximal intervals and finite-time singularities

This module fixes the logical and interval-level contracts used in the final
part of Topping Chapter 5.  It does not postulate short-time existence,
uniqueness, or an endpoint regularity theorem.  In particular,
`HasSmoothEndpointRicciExtension` is a definition of the conclusion that the
curvature and derivative estimates must eventually produce, not a theorem
asserting that they already do so.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A Ricci flow `gHat` on `K` extends `g` on `J` when `J` is
contained in `K` and the two metric families agree at every old time.  The old
family's own Ricci-flow property is intentionally separate. -/
def ExtendsRicciFlowOn
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ)
    (gHat : ℝ → RiemannianMetric I M) (K : Set ℝ) : Prop :=
  J ⊆ K ∧ MorganTianLib.IsRicciFlowOn gHat K ∧
    ∀ t ∈ J, gHat t = g t

/-- **Math.** A finite forward Ricci flow on `[0,T)` is maximal when no smooth
Ricci flow on a strictly longer half-open interval agrees with it on all old
times.  This is the singular-endpoint version of Topping's maximal-interval
convention. -/
def IsMaximalForwardRicciFlowOn
    (g : ℝ → RiemannianMetric I M) (T : ℝ) : Prop :=
  0 < T ∧ MorganTianLib.IsRicciFlowOn g (Ico 0 T) ∧
    ¬ ∃ (epsilon : ℝ), 0 < epsilon ∧
      ∃ gHat : ℝ → RiemannianMetric I M,
        ExtendsRicciFlowOn g (Ico 0 T) gHat (Ico 0 (T + epsilon))

/-- **Math.** Maximality rules out any displayed longer smooth Ricci-flow
extension.  This is only the definitional logical consequence; producing such
an extension from bounded curvature remains the analytic content of Theorem
5.3.1. -/
theorem not_extendsRicciFlowOn_longer_of_isMaximalForward
    {g : ℝ → RiemannianMetric I M} {T epsilon : ℝ}
    (hmax : IsMaximalForwardRicciFlowOn g T) (hepsilon : 0 < epsilon)
    (gHat : ℝ → RiemannianMetric I M) :
    ¬ ExtendsRicciFlowOn g (Ico 0 T) gHat (Ico 0 (T + epsilon)) := by
  intro hext
  exact hmax.2.2 ⟨epsilon, hepsilon, gHat, hext⟩

/-- **Math.** The spatial supremum of the pointwise curvature norm at a fixed
time.  On a closed manifold and for a smooth metric this is finite and is
attained, but those analytic facts are not built into the definition. -/
def curvatureSup (g : ℝ → RiemannianMetric I M) (t : ℝ) : ℝ :=
  sSup (range fun p : M => riemannNormAt (g t) p)

/-- **Math.** The exact limit assertion in Topping (5.3.1): the spatial
curvature supremum tends to `+infinity` as time approaches `T` from below. -/
def CurvatureBlowsUpAt
    (g : ℝ → RiemannianMetric I M) (T : ℝ) : Prop :=
  Tendsto (curvatureSup g) (nhdsWithin T (Iio T)) atTop

/-- **Math.** The bounded-curvature hypothesis used in the extension
contradiction, stated uniformly over every point and every old time. -/
def HasUniformCurvatureBoundBefore
    (g : ℝ → RiemannianMetric I M) (T : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ico 0 T, ∀ p : M,
    riemannNormAt (g t) p ≤ C

/-- **Math.** A smooth endpoint extension of a half-open Ricci flow.  It is a
genuine Ricci flow on `[0,T]`, not merely a pointwise limiting tensor, and it
agrees with the old family on `[0,T)`. -/
def HasSmoothEndpointRicciExtension
    (g : ℝ → RiemannianMetric I M) (T : ℝ) : Prop :=
  ∃ gBar : ℝ → RiemannianMetric I M,
    MorganTianLib.IsRicciFlowOn gBar (Icc 0 T) ∧
      ∀ t ∈ Ico 0 T, gBar t = g t

#print axioms not_extendsRicciFlowOn_longer_of_isMaximalForward

end Topping

end

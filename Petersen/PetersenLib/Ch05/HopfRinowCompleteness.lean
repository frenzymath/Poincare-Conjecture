import PetersenLib.Ch05.MetricTopology

/-!
# Petersen Ch. 5, §5.7.1 — completeness consequences of the Hopf–Rinow circle

Petersen's §5.7.1 packages several equivalent notions of completeness for a
connected Riemannian manifold `(M, g)`.  The full equivalence
(`thm:pet-ch5-hopf-rinow`) needs the geodesically-complete `⟹` metrically-complete
direction, which runs through the corner-turning equality case of the first
variation (do Carmo Ch. 3, Cor. 3.9); that direction is still open in the
vendored geodesic engine (`OpenGALib.Riemannian.Geodesic.HopfRinow`,
`complete_of_isGeodesicallyComplete`) and is not used here.

This file lands the **metric-space-only** consequence that does *not* depend on
that gap:

* `cor:pet-ch5-proper-lipschitz-complete` (Cor. 5.7.3) —
  `PetersenLib.properLipschitzFunction_impliesComplete`: a proper Lipschitz
  function `f : M → ℝ` forces `M` to be metrically complete.

The argument is the Heine–Borel step in isolation: a proper Lipschitz `f` makes
every closed ball of the Riemannian metric compact (it sits inside the compact
preimage `f⁻¹([a, b])`), so `M` is a proper metric space, hence complete.  It
uses only the metric-space structure `riemannianMetricSpace` built in Thm. 5.3.8,
not the geodesic machinery.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [T2Space M] [ConnectedSpace M]

/-- **Math.** Petersen Ch. 5, Corollary 5.7.3 (`cor:pet-ch5-proper-lipschitz-complete`):
**a proper Lipschitz function forces completeness.**  Suppose `(M, g)` admits a
function `f : M → ℝ` that is

* *proper* — the preimage of every compact set is compact
  (`hproper : ∀ s, IsCompact s → IsCompact (f ⁻¹' s)`), and
* *Lipschitz* with constant `K ≥ 0` for the Riemannian distance
  (`hlip : ∀ p q, |f p - f q| ≤ K · d(p, q)`).

Then `M`, metrized by the Riemannian distance of `g`, is complete.

Petersen deduces this from the Hopf–Rinow theorem by verifying the Heine–Borel
property; the verification is self-contained.  Any closed ball `B̄(x, r)` maps
under `f` into the interval `[f x − K r, f x + K r]`, so it is contained in the
compact set `f⁻¹([f x − K r, f x + K r])`; being closed, `B̄(x, r)` is itself
compact.  Thus every closed ball is compact, `M` is a proper metric space, and a
proper metric space is complete. -/
theorem properLipschitzFunction_impliesComplete (g : RiemannianMetric I M)
    (f : M → ℝ) (hproper : ∀ s : Set ℝ, IsCompact s → IsCompact (f ⁻¹' s))
    (K : ℝ) (hK : 0 ≤ K)
    (hlip : ∀ p q : M, |f p - f q| ≤ K * riemannianDistance (I := I) g p q) :
    @CompleteSpace M (riemannianMetricSpace (I := I) g).toUniformSpace := by
  letI mm : MetricSpace M := riemannianMetricSpace (I := I) g
  have hdist : ∀ p q : M, dist p q = riemannianDistance (I := I) g p q := fun _ _ => rfl
  haveI : ProperSpace M := by
    refine ⟨fun x r => ?_⟩
    have hsub : Metric.closedBall x r ⊆ f ⁻¹' Set.Icc (f x - K * r) (f x + K * r) := by
      intro y hy
      have hd : dist y x ≤ r := Metric.mem_closedBall.mp hy
      have hfb : |f y - f x| ≤ K * r :=
        calc |f y - f x| ≤ K * riemannianDistance (I := I) g y x := hlip y x
          _ = K * dist y x := by rw [hdist]
          _ ≤ K * r := mul_le_mul_of_nonneg_left hd hK
      have hb := abs_le.mp hfb
      rw [Set.mem_preimage, Set.mem_Icc]
      constructor <;> linarith [hb.1, hb.2]
    have hcpt : IsCompact (f ⁻¹' Set.Icc (f x - K * r) (f x + K * r)) :=
      hproper _ isCompact_Icc
    exact hcpt.of_isClosed_subset Metric.isClosed_closedBall hsub
  exact complete_of_proper

end PetersenLib

end

import MorganTianLib.Ch03.RicciFlow.SmoothPatching

/-!
# Two-sided endpoint calculus for Ricci-flow patching

The patching equation in `SmoothPatching` is stated first on the closed left
and half-open right time sets.  This file records the immediate two-sided
consequence at the joining time.  It is the scalar coefficient statement that
is needed before bootstrapping the patched horizontal metric to joint smooth
regularity.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Under the explicit left-limit hypotheses of the patching
proposition, the patched metric coefficient has the Ricci-flow derivative in
the ordinary two-sided sense at the joining time. -/
theorem patchedMetricFamily_hasDerivAt_at_join
    {a b c : ℝ} (hab : a < b) (hbc : b < c)
    (gLeft gRight : ℝ → RiemannianMetric I M)
    (hLeft : IsRicciFlowEquationOn gLeft (Ico a b))
    (hRight : IsRicciFlowEquationOn gRight (Ico b c))
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y) (𝓝[Ioo a b] b)
        (𝓝 ((gRight b).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y) (𝓝[Ioo a b] b)
        (𝓝 (ricciTensorAt (gRight b) p x y)))
    (p : M) (x y : TangentSpace I p) :
    HasDerivAt
      (fun t => (patchedMetricFamily b gLeft gRight t).metricInner p x y)
      (-2 * ricciTensorAt (gRight b) p x y) b := by
  have hleft := patchedMetricFamily_hasDerivWithinAt_Iic_at_join
    hab gLeft gRight hLeft hMetric hRicci p x y
  have hright : HasDerivWithinAt
      (fun s => (patchedMetricFamily b gLeft gRight s).metricInner p x y)
      (-2 * ricciTensorAt (gRight b) p x y) (Ico b c) b := by
    apply (hRight b ⟨le_rfl, hbc⟩ p x y).congr
    · intro s hs
      rw [patchedMetricFamily_of_le b gLeft gRight hs.1]
    · rw [patchedMetricFamily_at]
  have hrightIci : HasDerivWithinAt
      (fun s => (patchedMetricFamily b gLeft gRight s).metricInner p x y)
      (-2 * ricciTensorAt (gRight b) p x y) (Ici b) b :=
    hright.mono_of_mem_nhdsWithin (Ico_mem_nhdsGE hbc)
  have hunion := hleft.union hrightIci
  rw [Set.Iic_union_Ici] at hunion
  exact hunion.hasDerivAt (by simp)

end MorganTianLib

end

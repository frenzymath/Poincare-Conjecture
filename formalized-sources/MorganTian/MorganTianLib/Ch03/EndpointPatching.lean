import MorganTianLib.Ch03.RicciFlow.EndpointRestartPatching
import MorganTianLib.Ch03.RicciFlow.FlowRestriction

/-!
# Endpoint continuation bookkeeping

This companion module collects the elementary composition rules used when a
finite-time endpoint is followed by one or more restarted pieces.  The
analytic hypotheses remain in `RicciFlow.EndpointPatching`; the results here
only rearrange the explicit extension and patching interfaces.
-/

open scoped ContDiff ContMDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Filter Set Riemannian

noncomputable section

set_option linter.unusedSectionVars false

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Two explicit Ricci-flow extensions compose transitively. -/
theorem RicciFlowExtensionOn.trans
    {g₀ g₁ g₂ : ℝ → RiemannianMetric I M}
    {J₀ J₁ J₂ : Set ℝ}
    (h₀₁ : RicciFlowExtensionOn g₀ J₀ g₁ J₁)
    (h₁₂ : RicciFlowExtensionOn g₁ J₁ g₂ J₂) :
    RicciFlowExtensionOn g₀ J₀ g₂ J₂ := by
  refine ⟨h₀₁.1.trans h₁₂.1, h₁₂.2.1, ?_⟩
  intro t ht
  exact (h₁₂.2.2 t (h₀₁.1 ht)).trans (h₀₁.2.2 t ht)

/-- **Math.** An extension remains an extension after restricting its old time set. -/
theorem RicciFlowExtensionOn.restrict_left
    {g₀ g₁ : ℝ → RiemannianMetric I M}
    {J₀ J₁ K : Set ℝ}
    (h : RicciFlowExtensionOn g₀ J₀ g₁ J₁) (hK : K ⊆ J₀) :
    RicciFlowExtensionOn g₀ K g₁ J₁ := by
  exact ⟨hK.trans h.1, h.2.1, fun t ht => h.2.2 t (hK ht)⟩

/-- **Math.** Any later extension of a joined restart also extends the original
left-hand flow.  This is the continuation rule used when restarting more than
once at successive finite endpoints. -/
theorem SmoothEndpointRestart.extends_left_through
    {a b c : ℝ} {gLeft gRight : ℝ → RiemannianMetric I M}
    (h : SmoothEndpointRestart a b c gLeft gRight)
    {gLater : ℝ → RiemannianMetric I M} {JLater : Set ℝ}
    (hLater : RicciFlowExtensionOn
      (patchedMetricFamily b gLeft gRight) (Ico a c) gLater JLater) :
    RicciFlowExtensionOn gLeft (Ico a b) gLater JLater := by
  exact h.extends_left.trans hLater

/-- **Math.** Patching at two ordered joining times is associative.  Thus a chain of
restarts can be regrouped without changing the resulting metric family. -/
theorem patchedMetricFamily_assoc
    {b c : ℝ} (hbc : b ≤ c)
    (g₀ g₁ g₂ : ℝ → RiemannianMetric I M) :
    patchedMetricFamily c (patchedMetricFamily b g₀ g₁) g₂ =
      patchedMetricFamily b g₀ (patchedMetricFamily c g₁ g₂) := by
  funext t
  by_cases htb : t < b
  · have htc : t < c := lt_of_lt_of_le htb hbc
    simp [patchedMetricFamily, htb, htc]
  · have hbt : b ≤ t := le_of_not_gt htb
    by_cases htc : t < c
    · simp [patchedMetricFamily, htb, htc]
    · simp [patchedMetricFamily, htb, htc]

/-- **Math.** The left and right interval inclusions needed for a two-piece patch. -/
theorem Ico_subset_Ico_of_endpoint_patch
    {a b c : ℝ} (hab : a < b) (hbc : b < c) :
    Ico a b ⊆ Ico a c ∧ Ico b c ⊆ Ico a c := by
  constructor
  · intro t ht
    exact ⟨ht.1, lt_trans ht.2 hbc⟩
  · intro t ht
    exact ⟨(le_of_lt hab).trans ht.1, ht.2⟩

end MorganTianLib

end

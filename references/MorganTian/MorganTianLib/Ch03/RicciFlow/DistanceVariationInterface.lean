import MorganTianLib.Ch03.RicciFlow.DistanceVariation
import MorganTianLib.Ch03.RicciFlow.ForwardDifference
import MorganTianLib.Ch03.RicciFlow.MetricVariation

/-!
# Morgan--Tian Ch. 3 - distance-variation interfaces

The geometric distance-variation proof has two distinct layers. The first is
one-dimensional: a lower right Dini bound for a fixed curve-length functional
can be integrated to an endpoint estimate. The second is geometric: one must
produce that bound from minimizing geodesics, second variation, and the Ricci
cutoff argument. This module closes the first layer and exposes the exact
derivative adapters needed by the second; it does not encode the geometric
producer as an unchecked premise.

The metric-inner adapters below are the pointwise part that follows directly
from `IsMetricVariationOn` (and hence from an ordinary Ricci flow). A genuine
length derivative still requires an integral/variation theorem for the chosen
curve and is intentionally left to a downstream geometric module.
-/

open Filter Real Set Function
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

set_option linter.unusedSectionVars false

/-- **Math.** Negating a function turns a lower forward-difference bound into
the corresponding upper bound. -/
theorem ForwardDiffQuotientGE.to_neg
    {f : ℝ → ℝ} {t c : ℝ}
    (h : ForwardDiffQuotientGE f t c) :
    ForwardDiffQuotientLE (fun s => -f s) t (-c) := by
  intro r hr
  have h' := h (-r) (by linarith)
  filter_upwards [h'] with z hz
  rw [slope_neg]
  linarith

/-- **Math.** A lower forward-Dini bound by a constant integrates to the
corresponding endpoint inequality. This is the fixed-curve length interface
used by the distance argument. -/
theorem lowerEndpointBound_of_forwardDiffQuotientGE
    {f : ℝ → ℝ} {a b C : ℝ}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE f t (-C)) :
    f a - C * (b - a) ≤ f b := by
  let F : ℝ → ℝ := fun t => -f t
  let G : ℝ → ℝ := fun t => -f a + C * (t - a)
  have hF : ContinuousOn F (Icc a b) := by
    change ContinuousOn (fun t => -f t) (Icc a b)
    exact hf.neg
  have hfdF : ∀ t ∈ Ico a b,
      ForwardDiffQuotientLE F t C := by
    intro t ht
    have h := ForwardDiffQuotientGE.to_neg (hfd t ht)
    simpa [F] using h
  have hpsi : ContDiffOn ℝ 1
      (uncurry (fun _ _ : ℝ => C))
      (Icc a b ×ˢ (univ : Set ℝ)) := by
    fun_prop
  have hG : ContinuousOn G (Icc a b) := by
    fun_prop
  have hG' : ∀ t ∈ Ico a b,
      HasDerivWithinAt G C (Ici t) t := by
    intro t ht
    have hlin : HasDerivWithinAt (fun s : ℝ => C * (s - a))
        C (Ici t) t := by
      simpa using
        (((hasDerivAt_id t).sub_const a).const_mul C).hasDerivWithinAt
    simpa [G] using hlin
  have hinit : F a ≤ G a := by
    dsimp [F, G]
    linarith
  have hcomp := le_of_forwardDiffQuotientLE
    (f := F) (G := G) (ψ := fun _ _ : ℝ => C)
    hF hfdF hpsi hG hG' hinit
  have hb := hcomp b ⟨hab, le_rfl⟩
  dsimp [F, G] at hb
  linarith

/-- **Math.** If a supplied real-valued fixed-curve length functional has a
right derivative on a domain containing the forward ray, it has the lower
forward-Dini bound used in the distance argument. -/
theorem fixedCurveLength_forwardDiffQuotientGE_of_hasDerivWithinAt
    {length : ℝ → ℝ} {J : Set ℝ} {t₀ c : ℝ}
    (hJ : Ici t₀ ⊆ J)
    (hLength : HasDerivWithinAt length c J t₀) :
    ForwardDiffQuotientGE length t₀ c :=
  HasDerivWithinAt.forwardDiffQuotientGE (hLength.mono hJ)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A metric variation gives the lower forward-Dini bound for the
metric pairing of any fixed tangent vector, provided the variation domain
contains the forward ray at the time under consideration. -/
theorem metricInner_forwardDiffQuotientGE_of_metricVariation
    {g : ℝ → RiemannianMetric I M}
    {h : ℝ → ∀ p : M, TangentSpace I p → TangentSpace I p → ℝ}
    {J : Set ℝ} (hvar : IsMetricVariationOn g h J)
    {t₀ : ℝ} (hJ : Ici t₀ ⊆ J) (p : M) (v : TangentSpace I p) :
    ForwardDiffQuotientGE
      (fun t => (g t).metricInner p v v) t₀ (h t₀ p v v) := by
  apply HasDerivWithinAt.forwardDiffQuotientGE
  exact (hvar t₀ (hJ (mem_Ici.mpr le_rfl)) p v v).mono hJ

/-- **Math.** The Ricci-flow equation supplies the same fixed-vector lower
forward-Dini bound, with derivative `-2 Ric`. -/
theorem metricInner_forwardDiffQuotientGE_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J)
    {t₀ : ℝ} (hJ : Ici t₀ ⊆ J) (p : M) (v : TangentSpace I p) :
    ForwardDiffQuotientGE
      (fun t => (g t).metricInner p v v) t₀
      (-2 * ricciTensorAt (g t₀) p v v) := by
  exact metricInner_forwardDiffQuotientGE_of_metricVariation
    (isMetricVariationOn_of_isRicciFlowOn hflow) hJ p v

end MorganTianLib

end

import MorganTianLib.Ch03.RicciFlow.DistanceVariationCutoff
import MorganTianLib.Ch03.RicciFlow.DistanceIntegralBound

/-!
# Morgan--Tian Ch. 3 - cutoff variation to endpoint distance control

This is the one-dimensional composition used by the geometric distance
argument.  The second-variation estimate is kept as an explicit hypothesis;
the theorem only combines it with the already proved Dini integration lemma.
-/

open Set intervalIntegral

noncomputable section

namespace MorganTianLib

/-- **Math.** A time-indexed cutoff second-variation estimate gives the
integrated endpoint bound for a fixed curve length functional.  The geometric
input is the lower forward-Dini estimate `hvariation`; the cutoff hypotheses
turn its integral coefficient into the explicit constant from the index-form
calculation.
-/
theorem endpointBound_of_cutoff_secondVariation
    {f : ℝ → ℝ} {q : ℝ → ℝ → ℝ} {a b d N K r : ℝ}
    (hab : a ≤ b)
    (hr : 0 < r)
    (hdr : 2 * r ≤ d)
    (hf : ContinuousOn f (Icc a b))
    (hqL : ∀ t ∈ Ico a b, ContinuousOn (q t) (Icc (0 : ℝ) r))
    (hqR : ∀ t ∈ Ico a b, ContinuousOn (q t) (Icc (d - r) d))
    (hboundL : ∀ t ∈ Ico a b, ∀ u ∈ Icc (0 : ℝ) r, q t u ≤ N * K)
    (hboundR : ∀ t ∈ Ico a b, ∀ u ∈ Icc (d - r) d, q t u ≤ N * K)
    (hsecond : ∀ t ∈ Ico a b, 0 ≤
      -(∫ u in (0 : ℝ)..d, q t u)
        + (∫ u in (0 : ℝ)..r,
            leftDistanceCutoffWeight r u * q t u + N / r ^ 2)
        + (∫ u in (d - r)..d,
            rightDistanceCutoffWeight d r u * q t u + N / r ^ 2))
    (hvariation : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE f t (-(∫ u in (0 : ℝ)..d, q t u))) :
    f a - (2 * N * (2 / 3 * K * r + r⁻¹)) * (b - a) ≤ f b := by
  have hfd : ∀ t ∈ Ico a b,
      ForwardDiffQuotientGE f t (-(2 * N * (2 / 3 * K * r + r⁻¹))) := by
    intro t ht
    have hcut := lowerBound_of_cutoff_secondVariation
      (q := q t) (d := d) (N := N) (K := K) (r := r) hr hdr
      (hqL t ht) (hqR t ht) (hboundL t ht) (hboundR t ht) (hsecond t ht)
    exact (hvariation t ht).mono (by linarith)
  exact lowerEndpointBound_of_forwardDiffQuotientGE hab hf hfd

end MorganTianLib

end

#print axioms MorganTianLib.endpointBound_of_cutoff_secondVariation

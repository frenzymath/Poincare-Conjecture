import PetersenLib.Ch05.MetricStructure

/-!
# Petersen Ch. 5, §5.3 — segments may be translated to start at time `0`

Petersen's `def:pet-ch5-segment` is stated for a curve `σ ∈ Ω_{p,q}`, i.e. on
`[0, 1]`, but the definition `PetersenLib.IsSegment g σ a b` is given on a
general interval `[a, b]`, and the book uses it on `[0, |pq|]` (the
`\overline{pq}` notation) as freely as on any other interval.  This file records
the one fact that makes "`p` and `q` are joined by a segment" independent of the
choice of the domain's left endpoint:

* `IsSegment.translate` — if `σ` is a segment on `[a, b]`, then `s ↦ σ(s + a)` is
  a segment on `[0, b − a]`, with the same proportionality constant `k`.

Both the parametrization-proportional-to-arc-length clause and the
length-realizes-distance clause are invariant under the translation, since
translation is the orientation-preserving affine reparametrization with `c = 1`
(`curveLength_comp_mul_add`, `isPiecewiseSmoothCurve_comp_mul_add`).

**What this file does NOT provide.**  Nothing about *existence* of segments (that
is Hopf–Rinow), and no general affine reparametrization of segments: rescaling
`s ↦ σ(c s)` with `c ≠ 1` changes the constant `k` to `c k`, which is true but
not needed here and not proved.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.3.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Set
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-segment`): **a segment may be
translated to start at time `0`**.  If `σ` is a segment on `[a, b]`, then
`s ↦ σ(s + a)` is a segment on `[0, b − a]` with the same constant `k`.
Translation is the affine reparametrization `s ↦ 1 · s + a`, which preserves
piecewise smoothness (`isPiecewiseSmoothCurve_comp_mul_add`) and every partial
length (`curveLength_comp_mul_add`); the endpoints, hence the distance they must
realize, are unchanged.

Consequently "`p` and `q` are joined by a segment" does not depend on where the
segment's domain begins, and may always be tested on an interval `[0, b]`. -/
theorem IsSegment.translate {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ}
    (h : IsSegment (I := I) g γ a b) :
    IsSegment (I := I) g (fun s => γ (1 * s + a)) 0 (b - a) := by
  obtain ⟨hpw, hlen, k, hk0, hprop⟩ := h
  have e0 : (1 : ℝ) * 0 + a = a := by ring
  have e1 : (1 : ℝ) * (b - a) + a = b := by ring
  refine ⟨isPiecewiseSmoothCurve_comp_mul_add (I := I) one_pos (by rw [e0, e1]; exact hpw),
    ?_, k, hk0, ?_⟩
  · show curveLength (I := I) g (fun s => γ (1 * s + a)) 0 (b - a)
        = riemannianDistance (I := I) g (γ (1 * 0 + a)) (γ (1 * (b - a) + a))
    rw [curveLength_comp_mul_add (I := I) g γ zero_le_one a 0 (b - a), e0, e1, hlen]
  · intro t ht
    show curveLength (I := I) g (fun s => γ (1 * s + a)) 0 t = k * (t - 0)
    rw [curveLength_comp_mul_add (I := I) g γ zero_le_one a 0 t, e0,
      hprop (1 * t + a) ⟨by rw [one_mul]; linarith [ht.1], by rw [one_mul]; linarith [ht.2]⟩]
    ring

end PetersenLib

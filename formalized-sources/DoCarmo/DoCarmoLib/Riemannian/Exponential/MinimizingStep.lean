import DoCarmoLib.Riemannian.Exponential.NormalBallEDist
import DoCarmoLib.Riemannian.Exponential.RayGeodesic

/-!
# The geodesic-sphere step of the Hopf–Rinow argument (do Carmo Ch. 7 §2)

do Carmo, *Riemannian Geometry*, Ch. 7, proof of Theorem 2.8 (a ⟹ f): the
minimizing geodesic from `p` to a far point `q` is grown step by step; each
step starts at a center `x`, picks the point of a small geodesic sphere
`S_δ(x)` closest to `q`, and rides the radial geodesic to it, converting
`d(x, q) = δ + d(x', q)` into progress along a geodesic.

This file assembles the **complete step engine** from the two halves proved
upstream:

* `exists_normalSphere_min_edist` (`NormalBallEDist.lean`) — the metric
  decomposition `d(p, q) = δ + min_{x ∈ S_δ(p)} d(x, q)`;
* `exists_isGeodesicOn_expMap_ray` (`RayGeodesic.lean`) — exponential rays
  are intrinsic geodesics.

`exists_minimizing_step`: for every center `p` there is `δ₀ > 0` such that for
every `0 < δ < δ₀` and every `q` with `d(p, q) ≥ δ` there is a continuous
geodesic segment `γ : [0, 1] → M` from `p` with

* `d(p, γ(1)) = δ` and
* `d(p, q) = δ + d(γ(1), q)`.

What is *not* yet provided is the corner-turning identification (do Carmo's
appeal to Ch. 3, Cor. 3.9): when the step is iterated along a fixed geodesic,
the new segment must be shown to continue the *same* geodesic. That equality
case of the Gauss comparison is the remaining wall of Theorem 2.8 (see
`Geodesic/HopfRinow/PLAN.md`).
-/

noncomputable section

open Bundle Manifold Set Filter Metric
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

namespace Riemannian

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless] [CompleteSpace E]

variable {M' : Type*} [MetricSpace M'] [ChartedSpace H M'] [IsManifold I ∞ M']
variable [T2Space (TangentBundle I M')]

/-- **Math.** **The geodesic-sphere step** (do Carmo Ch. 7, proof of
Theorem 2.8). Under the standing hypothesis `g.IsRiemannianDist`, for every
`p ∈ M` there is `δ₀ > 0` such that for every `0 < δ < δ₀` and every `q` with
`d(p, q) ≥ δ` there is a curve `γ` which

* starts at `p`: `γ 0 = p`;
* is a continuous geodesic segment on `[0, 1]`;
* reaches the geodesic sphere of radius `δ`: `d(p, γ 1) = δ`; and
* makes definite progress towards `q`: `d(p, q) = δ + d(γ 1, q)`.

`γ 1` is the point of the geodesic sphere `S_δ(p)` closest to `q`, and `γ` is
the radial geodesic to it (`exists_isGeodesicOn_expMap_ray` +
`exists_normalSphere_min_edist`). -/
theorem exists_minimizing_step (g : RiemannianMetric I M')
    (hg : g.IsRiemannianDist) (p : M') :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (q : M') (δ : ℝ), 0 < δ → δ < δ₀ → ENNReal.ofReal δ ≤ edist p q →
        ∃ γ : ℝ → M', γ 0 = p ∧
          ContinuousOn γ (Icc 0 1) ∧
          IsGeodesicOn (I := I) g γ (Icc 0 1) ∧
          edist p (γ 1) = ENNReal.ofReal δ ∧
          edist p q = ENNReal.ofReal δ + edist (γ 1) q := by
  classical
  obtain ⟨εs, c, hεs, hc, hdoms, hstep⟩ :=
    exists_normalSphere_min_edist (I := I) g hg p
  obtain ⟨ρ, b, hρ, hb, hadm, hray⟩ :=
    exists_isGeodesicOn_expMap_ray (I := I) g p
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  refine ⟨min εs ρ / Real.sqrt c, by positivity, ?_⟩
  intro q δ hδ hδ₀ hδq
  have hδc : Real.sqrt c * δ < min εs ρ := by
    rw [lt_div_iff₀ hsqrtc] at hδ₀
    linarith [hδ₀]
  have hδεs : Real.sqrt c * δ < εs := hδc.trans_le (min_le_left _ _)
  have hδρ : Real.sqrt c * δ < ρ := hδc.trans_le (min_le_right _ _)
  obtain ⟨z, hz_cδ, hz_εs, hzQ, hz_dist, hz_decomp, hz_min⟩ :=
    hstep q δ hδ hδεs hδq
  have hzρ : ‖z‖ < ρ := hz_cδ.trans_lt hδρ
  obtain ⟨hstart, hvel, hcont, hgeo⟩ := hray z hzρ
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-b) b :=
    Icc_subset_Ioo (by linarith [hb]) hb
  refine ⟨fun t : ℝ => expMap (I := I) g p ((t • z : E) : TangentSpace I p),
    hstart, hcont.mono hsub, hgeo.mono hsub, ?_, ?_⟩
  · -- the endpoint is `exp_p z`, at distance exactly `δ`
    show edist p (expMap (I := I) g p (((1 : ℝ) • z : E) : TangentSpace I p))
      = ENNReal.ofReal δ
    rw [one_smul]
    exact hz_dist
  · -- the decomposition at the endpoint
    show edist p q = ENNReal.ofReal δ
      + edist (expMap (I := I) g p (((1 : ℝ) • z : E) : TangentSpace I p)) q
    rw [one_smul]
    exact hz_decomp

end Exponential

end Riemannian

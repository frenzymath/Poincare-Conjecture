import PetersenLib.Ch05.Geodesics
import PetersenLib.Riemannian.Geodesic.HopfRinow

/-!
# Petersen Ch. 5, §5.7.1 — the Hopf–Rinow theorem (Thm. 5.7.1)

For a connected Riemannian manifold `(M, g)` whose metric-space distance is the
Riemannian distance of `g` (`g.IsRiemannianDist`), the four notions of
completeness that Petersen lists in Theorem 5.7.1 are equivalent:

1. `(M, g)` is **geodesically complete** — every geodesic is defined for all
   time (`PetersenLib.IsGeodesicallyComplete`).
2. `(M, g)` is **geodesically complete at some `p`** — every `v ∈ T_pM`
   generates a geodesic defined on all of `ℝ`.
3. `M` has the **Heine–Borel property** — closed bounded sets are compact
   (`ProperSpace M`).
4. `M` is **metrically complete** (`CompleteSpace M`).

The whole analytic content is the vendored, sorry-free geodesic completeness
engine (`PetersenLib.Riemannian.Geodesic.HopfRinow`, DoCarmo Ch. 7 §2): the
single-point properness `properSpace_of_geodesicallyComplete_at` (do Carmo's
geodesic-sphere growth induction + Bolzano–Weierstrass on the initial data) is
the substantive `(2) ⟹ (3)` step, and `isGeodesicallyComplete_of_complete` (a
maximal geodesic that Cauchy-converges at a finite endpoint is extended by the
local flow) is `(4) ⟹ (1)`.  `(1) ⟹ (2)` is trivial and `(3) ⟹ (4)` is the
metric fact that a proper metric space is complete.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen's `IsGeodesicallyComplete` (Ch. 5 §5.2) agrees with the
vendored geodesic engine's `Geodesic.IsGeodesicallyComplete`: both say every
initial datum `(p, v)` is realised by a continuous geodesic defined on all of
`ℝ`, only differing in the order of the defining conjuncts. -/
theorem isGeodesicallyComplete_iff_geodesic (g : RiemannianMetric I M) :
    IsGeodesicallyComplete (I := I) g ↔ Geodesic.IsGeodesicallyComplete (I := I) g := by
  constructor
  · intro h p v; obtain ⟨γ, hc, h0, hv, hg⟩ := h p v; exact ⟨γ, h0, hv, hc, hg⟩
  · intro h p v; obtain ⟨γ, h0, hv, hc, hg⟩ := h p v; exact ⟨γ, hc, h0, hv, hg⟩

/-- **Math.** Petersen Ch. 5, Theorem 5.7.1 (Hopf–Rinow, 1931;
`thm:pet-ch5-hopf-rinow`).  For a connected Riemannian manifold `(M, g)` whose
metric-space structure is the Riemannian distance of `g` (`g.IsRiemannianDist`),
the following are equivalent:
`(1)` geodesic completeness, `(2)` geodesic completeness at some point,
`(3)` the Heine–Borel property (`ProperSpace M`), and `(4)` metric completeness.

The cycle `(1) ⟹ (2) ⟹ (3) ⟹ (4) ⟹ (1)` is assembled from the vendored engine:
`(2) ⟹ (3)` is `Geodesic.properSpace_of_geodesicallyComplete_at`,
`(3) ⟹ (4)` is `complete_of_proper`, and
`(4) ⟹ (1)` is `Geodesic.isGeodesicallyComplete_of_complete`. -/
theorem hopfRinowTheorem (g : RiemannianMetric I M) [ConnectedSpace M]
    (hg : g.IsRiemannianDist) :
    [ IsGeodesicallyComplete (I := I) g,
      ∃ p : M, ∀ v : TangentSpace I p, ∃ γ : ℝ → M,
        γ 0 = p ∧ HasDerivAt (fun s => extChartAt I p (γ s)) (v : E) 0 ∧ Continuous γ ∧
          IsGeodesic (I := I) g γ,
      ProperSpace M,
      CompleteSpace M ].TFAE := by
  tfae_have 1 → 2 := by
    intro h
    obtain ⟨p⟩ := (inferInstance : Nonempty M)
    refine ⟨p, fun v => ?_⟩
    obtain ⟨γ, hc, h0, hv, hg'⟩ := h p v
    exact ⟨γ, h0, hv, hc, hg'⟩
  tfae_have 2 → 3 := by
    rintro ⟨p, hp⟩
    exact Geodesic.properSpace_of_geodesicallyComplete_at g hg p hp
  tfae_have 3 → 4 := by
    intro h
    letI := h
    exact complete_of_proper
  tfae_have 4 → 1 := by
    intro _
    exact (isGeodesicallyComplete_iff_geodesic g).mpr
      (Geodesic.isGeodesicallyComplete_of_complete g hg)
  tfae_finish

end PetersenLib

end

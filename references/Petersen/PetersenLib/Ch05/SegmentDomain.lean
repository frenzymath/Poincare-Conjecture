import PetersenLib.Ch05.ExponentialMap
import PetersenLib.Ch05.MetricStructure

/-!
# Petersen Ch. 5, §5.7.3–5.7.4 — the segment domain and the cut locus

Definitions for Petersen's segment-domain description of the exponential map on a
complete manifold (`def:pet-ch5-segment-domain`, `def:pet-ch5-cut-locus`).

* `segmentDomain g p` — Petersen's `seg(p) = {v ∈ T_pM ∣ t ↦ exp_p(t v) : [0,1] → M
  is a segment}`: the initial velocities whose unit-time exponential ray is a
  minimizing, constant-speed curve (`IsSegment`).
* `segmentDomainStarInterior g p` — Petersen's star interior
  `seg⁰(p) = {s v ∣ s ∈ [0,1), v ∈ seg(p)}`.
* `cutLocus g p` — Petersen's cut locus in `T_pM`, `seg(p) − seg⁰(p)`; the tangent
  vectors on the star boundary of the segment domain.

Only the definitions and their elementary set-algebra relations are recorded here.
Injectivity of `exp_p` on `seg⁰(p)` (Prop. 5.7.7) is proved downstream, in
`PetersenLib/Ch05/SegmentDomainInjective.lean`; unlike its siblings below it never
differentiates `exp_p` away from `0`, so it needs no global smoothness of `exp`.
The remaining substantive facts of §5.7.3–5.7.4 — that `seg(p)` is closed and
star-shaped with `M = exp_p(seg(p))` (Hopf–Rinow), nonsingularity of `D exp_p` on
`seg⁰(p)` (Lemma 5.7.8), openness of `seg⁰(p)` (Prop. 5.7.10), and the smoothness
of `r` up to the cut point (Cor. 5.7.11) — are not yet formalized.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-segment-domain`): the **segment domain**
`seg(p) ⊂ T_pM` of `p`, the initial velocities `v` for which the unit-time
exponential ray `t ↦ exp_p(t v)`, `t ∈ [0, 1]`, is a **segment** (a
minimizing, constant-speed curve, `IsSegment`).  On a complete manifold this is a
closed, star-shaped set with `M = exp_p(seg(p))`. -/
def segmentDomain (g : RiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  {v | IsSegment (I := I) g (fun t => expMap (I := I) g p (t • v)) 0 1}

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-segment-domain`): the **star interior**
`seg⁰(p) = {s v ∣ s ∈ [0, 1), v ∈ seg(p)}` of the segment domain — the radial
scalings by `s < 1` of the segment-domain vectors. -/
def segmentDomainStarInterior (g : RiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  {v | ∃ s : ℝ, s ∈ Ico (0 : ℝ) 1 ∧ ∃ w ∈ segmentDomain (I := I) g p, v = s • w}

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-cut-locus`): the **cut locus** of `p` in
`T_pM`, `seg(p) − seg⁰(p)` — the segment-domain vectors on the star boundary,
where `exp_p` either fails to be one-to-one or becomes singular.  Its exponential
image is where the distance function `r(x) = |px|` fails to be smooth. -/
def cutLocus (g : RiemannianMetric I M) (p : M) : Set (TangentSpace I p) :=
  segmentDomain (I := I) g p \ segmentDomainStarInterior (I := I) g p

variable {g : RiemannianMetric I M} {p : M}

@[simp] lemma mem_segmentDomain_iff {v : TangentSpace I p} :
    v ∈ segmentDomain (I := I) g p ↔
      IsSegment (I := I) g (fun t => expMap (I := I) g p (t • v)) 0 1 := Iff.rfl

lemma cutLocus_eq (g : RiemannianMetric I M) (p : M) :
    cutLocus (I := I) g p =
      segmentDomain (I := I) g p \ segmentDomainStarInterior (I := I) g p := rfl

/-- **Math.** The cut locus is contained in the segment domain. -/
lemma cutLocus_subset_segmentDomain :
    cutLocus (I := I) g p ⊆ segmentDomain (I := I) g p := diff_subset

/-- **Math.** The cut locus and the star interior are disjoint — `seg⁰(p)` is
exactly the part of `seg(p)` off the cut locus. -/
lemma disjoint_cutLocus_starInterior :
    Disjoint (cutLocus (I := I) g p) (segmentDomainStarInterior (I := I) g p) :=
  disjoint_sdiff_left

/-- **Math.** The segment domain splits as the disjoint union of its star interior
(intersected with the domain) and its cut locus. -/
lemma segmentDomain_eq_starInterior_union_cutLocus :
    segmentDomain (I := I) g p =
      (segmentDomain (I := I) g p ∩ segmentDomainStarInterior (I := I) g p)
        ∪ cutLocus (I := I) g p := by
  rw [cutLocus, inter_union_diff]

end PetersenLib

end

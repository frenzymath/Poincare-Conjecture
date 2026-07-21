import PetersenLib.Ch06.ConvexFunctions
import PetersenLib.Ch05.ExponentialMap
import PetersenLib.Ch05.MetricStructure

/-!
# Petersen Ch. 6, §6.4 — the convexity radius

Petersen §6.4 (p. 275), `def:pet-ch6-convexity-radius`, verbatim:

> The largest `R` such that `r(x)` is convex on `B(p, R)` and any two points in `B(p, R)` are
> joined by unique segments in `B(p, R)` is called the **convexity radius** at `p`.

Globally `conv.rad(M, g) = inf_p conv.rad(p)`.

**This is Petersen's definition, not a proxy.**  Thm. 6.4.8 (`convexityRadiusCriterion`, still
open) gives *sufficient conditions* — `R ≤ ½ inj(x)` and `R ≤ ½π/√K` — for these two properties
to hold, but Petersen does **not** define `conv.rad` by those hypotheses; he defines it by the
two geometric conclusions themselves, and that is what is formalized here.  Encoding the
hypotheses instead would define a smaller quantity (a computable lower bound), name it wrongly,
and additionally drag in a needless connection argument and `√K` junk-value handling.  The
`≥ min{inj/2, π/(2√K)}` estimate — which *is* the hypotheses-to-conclusions implication summed
up — is split off as the separate, still-open `cor:pet-ch6-convexity-radius-bound`.

Because both defining properties are **metric** (`r = |·p|` is the Riemannian distance, and
segments are its minimizers), `convexityRadius` takes no connection argument — it has the same
shape as `injectivityRadius` (`Ch05/ExponentialMap.lean`).

## The uniqueness clause, and the trap it avoids

"Any two points of `B(p,R)` are joined by a **unique** segment in `B(p,R)`" must **not** be
rendered as `∃! γ : ℝ → M, …`.  A segment from `x` to `y` is constrained only on its parameter
interval `[0, |xy|]`; off that interval `γ` is arbitrary, so `∃!` over the whole function `ℝ → M`
is **false for every** `x, y` (extend any witness differently past the endpoint to get a second
one), which would make the witness set empty and `convexityRadius ≡ 0` — a silent vacuity bug.
`UniqueSegmentsInBall` therefore states existence **and** uniqueness *on the parameter interval*
(`Set.EqOn … (Icc 0 (|xy|))`), the honest reading of "unique segment".

## `ℝ≥0∞`

`convexityRadius` returns `ℝ≥0∞`, built as an `sSup` over `ENNReal.ofReal`-images of real
witnesses `R > 0`, mirroring `injectivityRadius` so the two are comparable in `cor:...-bound`
without coercion friction.  The empty-manifold infimum for the global radius is `⊤`, the mirror
of `injectivityRadius`'s `sSup ∅ = 0`.
-/

open Set
open scoped ENNReal Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : RiemannianMetric I M}

/-- **Math.** Petersen §6.4 (p. 275), a clause of `def:pet-ch6-convexity-radius`: **any two points
of `B(p, R)` are joined by a unique segment lying in `B(p, R)`.**

A *segment in the ball* from `x` to `y` is an `IsSegment` on `[0, |xy|]` (piecewise smooth,
length-minimizing, parametrized proportionally to arc length) with endpoints `x, y` whose image
stays in `B(p, R)`.  Uniqueness is asserted **only on the parameter interval** `Icc 0 |xy|`
(`Set.EqOn`), never as `∃!` over `ℝ → M`; see the module docstring for why the latter would be a
vacuity bug. -/
def UniqueSegmentsInBall (g : RiemannianMetric I M) (p : M) (R : ℝ) : Prop :=
  ∀ x ∈ metricBall (I := I) g p R, ∀ y ∈ metricBall (I := I) g p R,
    (∃ γ : ℝ → M, IsSegment (I := I) g γ 0 (riemannianDistance (I := I) g x y) ∧
        γ 0 = x ∧ γ (riemannianDistance (I := I) g x y) = y ∧
        Set.MapsTo γ (Icc 0 (riemannianDistance (I := I) g x y)) (metricBall (I := I) g p R)) ∧
      ∀ γ₁ γ₂ : ℝ → M,
        (IsSegment (I := I) g γ₁ 0 (riemannianDistance (I := I) g x y) ∧
          γ₁ 0 = x ∧ γ₁ (riemannianDistance (I := I) g x y) = y ∧
          Set.MapsTo γ₁ (Icc 0 (riemannianDistance (I := I) g x y)) (metricBall (I := I) g p R)) →
        (IsSegment (I := I) g γ₂ 0 (riemannianDistance (I := I) g x y) ∧
          γ₂ 0 = x ∧ γ₂ (riemannianDistance (I := I) g x y) = y ∧
          Set.MapsTo γ₂ (Icc 0 (riemannianDistance (I := I) g x y)) (metricBall (I := I) g p R)) →
        Set.EqOn γ₁ γ₂ (Icc 0 (riemannianDistance (I := I) g x y))

/-- **Math.** Petersen §6.4 (p. 275), `def:pet-ch6-convexity-radius`: `R > 0` is a **convexity
radius witness** at `p` if the distance function `r = |·p|` is convex on `B(p, R)`
(`IsConvexOn`, i.e. convex along every geodesic staying in the ball) and any two points of
`B(p, R)` are joined by a unique segment in `B(p, R)` (`UniqueSegmentsInBall`).  These are exactly
Petersen's two defining properties. -/
def IsConvexityRadiusWitness (g : RiemannianMetric I M) (p : M) (R : ℝ) : Prop :=
  0 < R ∧
    IsConvexOn (I := I) g (metricBall (I := I) g p R) (fun x => riemannianDistance (I := I) g p x) ∧
    UniqueSegmentsInBall (I := I) g p R

/-- **Math.** Petersen §6.4 (p. 275), `def:pet-ch6-convexity-radius`: the **convexity radius** at
`p`, the supremum of the radii `R > 0` on which `r = |·p|` is convex and any two points are
joined by a unique segment, all inside `B(p, R)` (`IsConvexityRadiusWitness`).

Returns `ℝ≥0∞` as an `sSup` over `ENNReal.ofReal`-images, mirroring `injectivityRadius`.  See the
module docstring: this is Petersen's own definition (the two geometric properties), not the
hypotheses of Thm. 6.4.8. -/
def convexityRadius (g : RiemannianMetric I M) (p : M) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ R : ℝ, r = ENNReal.ofReal R ∧ IsConvexityRadiusWitness (I := I) g p R}

/-- **Math.** Petersen §6.4 (p. 275), `def:pet-ch6-convexity-radius`, global form:
`conv.rad(M, g) = inf_p conv.rad(p)`.  On an empty manifold this is `⊤`, the `ℝ≥0∞` convention
for an infimum over an empty index — the mirror of the `sSup ∅ = 0` convention `injectivityRadius`
inherits at the other end. -/
def globalConvexityRadius (g : RiemannianMetric I M) : ℝ≥0∞ :=
  ⨅ p : M, convexityRadius (I := I) g p

end PetersenLib

end

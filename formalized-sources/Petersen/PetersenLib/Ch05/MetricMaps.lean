import PetersenLib.Ch05.MetricStructure

/-!
# Petersen Ch. 5, §5.6 — submetries and distance coordinates

Two metric-level notions from Petersen §5.6, built directly on the Riemannian
distance `riemannianDistance` and its metric balls `metricBall` of §5.3.

* `IsSubmetry g' g F` (`def:pet-ch5-submetry`) — a map `F : M' → M` between
  Riemannian manifolds `(M', g')`, `(M, g)` is a **submetry** if around every
  point `p'` there is a radius `r > 0` such that `F` carries the metric ball
  `B(p', ε)` *onto* the metric ball `B(F p', ε)` for every `ε ≤ r`.  Submetries
  are locally distance nonincreasing (`IsSubmetry.riemannianDistance_image_lt`),
  the first step towards Berestovskii's theorem (Thm. 5.6.16).
* `distanceCoordinates g q x` (`def:pet-ch5-distance-coordinates`) — the tuple
  `(r_{q₀}(x), …, r_{q_{n-1}}(x))` of Riemannian distances `r_{qᵢ}(x) = |x qᵢ|`
  to a finite family of base points, the raw material of Petersen's
  distance-coordinate charts (used in the Myers–Steenrod theorem, Thm. 5.6.15).

Reference: Petersen, *Riemannian Geometry*, 3rd ed., §5.6.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Manifold Set
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## Submetries -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-submetry`): a map `F : M' → M` between
Riemannian manifolds `(M', g')` and `(M, g)` is a **submetry** if for every
`p' ∈ M'` there is `r > 0` with `F(B(p', ε)) = B(F p', ε)` for all `ε ≤ r` — `F`
carries small metric balls *onto* metric balls of the same radius. -/
def IsSubmetry (g' : RiemannianMetric I' M') (g : RiemannianMetric I M) (F : M' → M) : Prop :=
  ∀ p' : M', ∃ r : ℝ, 0 < r ∧
    ∀ ε : ℝ, ε ≤ r →
      F '' metricBall (I := I') g' p' ε = metricBall (I := I) g (F p') ε

/-- **Math.** A **submetry is locally distance nonincreasing**: for every pair
`p', q'` there is `r > 0` such that whenever `ε ≤ r` and `|p'q'| < ε`, also
`|F p', F q'| < ε`.  This is immediate from the onto-ball property — `q' ∈
B(p', ε)`, hence `F q' ∈ F(B(p', ε)) = B(F p', ε)` — and, letting `ε ↓ |p'q'|`,
yields `|F p', F q'| ≤ |p'q'|` on the ball of radius `r`. -/
theorem IsSubmetry.riemannianDistance_image_lt {g' : RiemannianMetric I' M'}
    {g : RiemannianMetric I M} {F : M' → M}
    (hF : IsSubmetry (I := I) (I' := I') g' g F) (p' q' : M') :
    ∃ r : ℝ, 0 < r ∧ ∀ ε : ℝ, ε ≤ r →
      riemannianDistance (I := I') g' p' q' < ε →
        riemannianDistance (I := I) g (F p') (F q') < ε := by
  obtain ⟨r, hr, hball⟩ := hF p'
  refine ⟨r, hr, fun ε hε hlt => ?_⟩
  have hq' : q' ∈ metricBall (I := I') g' p' ε := by
    simp only [metricBall, mem_setOf_eq]; exact hlt
  have himg : F q' ∈ F '' metricBall (I := I') g' p' ε := ⟨q', hq', rfl⟩
  rw [hball ε hε] at himg
  simpa only [metricBall, mem_setOf_eq] using himg

/-! ## Distance coordinates -/

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-distance-coordinates`): the
**distance coordinates** attached to a finite family `q : Fin n → M` of base
points, `x ↦ (r_{q₀}(x), …, r_{q_{n-1}}(x))` with `r_{qᵢ}(x) = |x qᵢ|` the
Riemannian distance.  When `∇r_{q₀}(p), …, ∇r_{q_{n-1}}(p)` are linearly
independent, this tuple is a coordinate chart near `p` (Petersen's construction
via the inverse function theorem). -/
def distanceCoordinates (g : RiemannianMetric I M) {n : ℕ} (q : Fin n → M) (x : M) :
    Fin n → ℝ :=
  fun i => riemannianDistance (I := I) g (q i) x

@[simp] lemma distanceCoordinates_apply (g : RiemannianMetric I M) {n : ℕ}
    (q : Fin n → M) (x : M) (i : Fin n) :
    distanceCoordinates (I := I) g q x i = riemannianDistance (I := I) g (q i) x := rfl

end PetersenLib

end

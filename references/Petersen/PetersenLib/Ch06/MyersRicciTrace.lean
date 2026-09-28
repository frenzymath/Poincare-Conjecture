import PetersenLib.Ch06.VelocityParallel
import PetersenLib.Ch03.RicciCovariantDerivative
import PetersenLib.Ch03.RicciSectional
import PetersenLib.Ch03.ScalarFormulas

/-!
# Petersen Ch. 6, section 6.3: the Ricci trace along a velocity-seeded frame

Myers' theorem sums the sectional curvatures of the directions perpendicular
to a unit-speed geodesic.  This file packages the pointwise trace step for the
parallel orthonormal frames constructed in `VelocityParallel.lean`.
-/

open Set Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless] [SigmaCompactSpace M]
  [T2Space M] [LocallyCompactSpace M]

/-- **Math.** The Ricci trace in a velocity-seeded orthonormal frame, in the
argument order used by the Myers index form.  If `e n₀ = c'`, then

`Ric(c', c') = sum_{i != n₀} sec(e_i, c')`.

The frame may come from parallel transport, but the identity is pointwise and
therefore only needs orthonormality and the velocity-seeding equality. -/
theorem ricciCurvature_eq_sum_sectional_of_velocitySeededFrame
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    {e : Fin (Module.finrank ℝ E) → (∀ t, TangentSpace I (c t))}
    {n₀ : Fin (Module.finrank ℝ E)}
    (horth : ∀ t ∈ Ioo a b, ∀ i j,
      g.metricInner (c t) (e i t) (e j t) = if i = j then (1 : ℝ) else 0)
    (hvel : ∀ t ∈ Ioo a b,
      e n₀ t = curveVelocity (I := I) c t) :
    ∀ t ∈ Ioo a b,
      RicciCurvature g.leviCivita.toAffineConnection (c t)
          (curveVelocity (I := I) c t) (curveVelocity (I := I) c t) =
        ∑ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))).erase n₀,
          sectionalCurvature g.leviCivita (c t) (e i t)
            (curveVelocity (I := I) c t) := by
  classical
  intro t ht
  obtain ⟨basis, hbasis⟩ :=
    exists_orthonormalBasis_of_family (g := g) (p := c t) (horth t ht)
  have hb : ∀ i, basis i = e i t := fun i => congrFun hbasis i
  have hborth : ∀ i j, g.metricInner (c t) (basis i) (basis j) =
      if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [hb i, hb j]
    exact horth t ht i j
  have htrace := ricciCurvature_eq_sum_sectionalCurvature g.leviCivita
    (c t) basis hborth n₀
  rw [hb n₀, hvel t ht] at htrace
  rw [htrace]
  exact Finset.sum_congr rfl fun i _ => by
    rw [hb i, sectionalCurvature_comm]

end PetersenLib

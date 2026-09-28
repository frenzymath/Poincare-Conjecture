import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3
import DoCarmoLib.Riemannian.Exponential.MinimizingGeodesic

/-!
# A metric bridge for do Carmo's piecewise curves

The definition in `DoCarmoCh3` packages a continuous curve together with a
finite strict `C¹` partition.  The exponential developments already prove the
metric lower bound piece by piece, including the triangle-inequality step at
vertices.  This file exposes that result directly in the do Carmo predicate's
interface.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E]
  [T2Space (TangentBundle I M)]

/-- **Math.** A do Carmo piecewise differentiable curve has length at least
the ambient Riemannian distance between its endpoints.  The proof delegates
the vertex-by-vertex triangle argument to
`Exponential.edist_le_pathELength_piecewise_partition`.
-/
theorem IsPiecewiseDifferentiableCurve.edist_le_pathELength
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {c : ℝ → M} {a b : ℝ}
    (hc : IsPiecewiseDifferentiableCurve (I := I) c a b) :
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩
    edist (c a) (c b) ≤ Manifold.pathELength I c a b := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  rcases hc with ⟨_, ⟨n, τ, hn, hτ0, hτn, hstrict, hpiece⟩⟩
  have hτ : ∀ i < n, τ i ≤ τ (i + 1) := fun i hi => (hstrict i hi).le
  have ha : τ 0 ≤ a := by simp [hτ0]
  have hab : a ≤ b := by
    have hspan : τ 0 ≤ τ n :=
      Exponential.partition_le hτ (Nat.zero_le n) le_rfl
    simpa [hτ0, hτn] using hspan
  have hb : b ≤ τ n := by simp [hτn]
  exact Exponential.edist_le_pathELength_piecewise_partition
    (I := I) g hg hτ hpiece ha hab hb

end Geodesic
end Riemannian

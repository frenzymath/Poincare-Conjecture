import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import MorganTianLib.Ch01.Metric

/-!
# Poincaré Ch. 1, §1.1 — The Levi-Civita connection

Restates Morgan–Tian's Levi-Civita theorem (blueprint
`thm:levi-civita-connection`): given a Riemannian metric `g` on `M` there
uniquely exists a torsion-free connection making `g` parallel. This is
exactly DoCarmoLib's `Riemannian.RiemannianMetric.exists_unique_isLeviCivita`,
where `IsLeviCivita g nabla` packages the torsion-free ("symmetric") and
metric-compatible conditions.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.1
(blueprint `thm:levi-civita-connection`).
-/

open scoped ContDiff Manifold Topology Bundle

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The **Levi-Civita theorem**: given a Riemannian metric `g` on `M`,
there uniquely exists a torsion-free connection `∇` on `TM` making `g` parallel,
i.e. an affine connection that is both symmetric (torsion-free) and compatible
with the metric `g` (`nabla.IsLeviCivita g`). Direct reuse of
`Riemannian.RiemannianMetric.exists_unique_isLeviCivita`.

Blueprint: `thm:levi-civita-connection`. -/
theorem existsUnique_leviCivita (g : Riemannian.RiemannianMetric I M) :
    ∃! nabla : Riemannian.AffineConnection I M, nabla.IsLeviCivita g :=
  g.exists_unique_isLeviCivita

end MorganTianLib

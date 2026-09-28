import MorganTianLib.Ch01.RicciFrame

/-!
# Smoothness of scalar curvature

For a fixed smooth Riemannian metric, scalar curvature is a smooth function of
the spatial variable.  This supplies the regularity hypothesis used by
downstream scalar-curvature variation and evolution interfaces.
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff Bundle

noncomputable section

namespace MorganTianLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M]
    [T2Space M] in
/-- **Math.** Pairing the curvature of four smooth vector fields with a smooth
Riemannian metric gives a smooth scalar function. -/
theorem curvatureForm_contMDiff (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (X Y Z W : SmoothVectorField I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (nabla.curvatureForm g X Y Z W) :=
  g.metricInner_field_contMDiff (nabla.curvature X Y Z) W

/-- **Math.** Scalar curvature of a fixed smooth metric and Levi-Civita
connection is smooth in the spatial variable. -/
theorem scalarCurvatureAt_contMDiff (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (hLC : nabla.IsLeviCivita g) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (scalarCurvatureAt g nabla hLC) := by
  intro p
  have hs : ContMDiffAt I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ i, ∑ j, nabla.curvatureForm g (orthoFrameField g p i)
        (orthoFrameField g p j) (orthoFrameField g p i)
        (orthoFrameField g p j) q) p := by
    exact ContMDiffAt.sum fun i _ =>
      ContMDiffAt.sum fun j _ =>
        (curvatureForm_contMDiff g nabla (orthoFrameField g p i)
          (orthoFrameField g p j) (orthoFrameField g p i)
          (orthoFrameField g p j)).contMDiffAt
  refine (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [(isOpen_orthoFrameSet (I := I) (M := M) p).mem_nhds
      (mem_orthoFrameSet_self (I := I) p)] with q hq
  exact scalarCurvatureAt_eq_frame_sum g nabla hLC p hq

omit [I.Boundaryless] in
private theorem scalarCurvatureCanonicalLC (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** Scalar curvature for the canonical Levi-Civita connection is
smooth in the spatial variable. -/
theorem scalarCurvatureAt_leviCivita_contMDiff (g : RiemannianMetric I M) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞
      (scalarCurvatureAt g g.leviCivitaConnection (scalarCurvatureCanonicalLC g)) :=
  scalarCurvatureAt_contMDiff g g.leviCivitaConnection
    (scalarCurvatureCanonicalLC g)

end MorganTianLib

import MorganTianLib.Ch01.Metric
import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.Pullback
import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Morgan--Tian Ch. 3 - the Ricci flow equation

This module separates the tensor evolution equation from the additional data in
the book's definition of a Ricci flow.  The equation-only predicate is the
shared interface used by downstream projects.  The full predicate also records
that time is a nondegenerate interval and that the metric is jointly smooth in
space and time.

The family is represented on all of `R` so that ordinary within-derivatives can
be used at arbitrary interval endpoints.  All conditions are restricted to the
time set `J`; values away from `J` carry no mathematical content.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] in
private theorem canonicalLC (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** The Ricci tensor of the canonical Levi-Civita connection, as a bilinear
form on a tangent space. -/
noncomputable def ricciTensorAt (g : RiemannianMetric I M) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  Riemannian.ricciBilin
    (g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g
      (canonicalLC g) p)

/-- **Math.** The horizontal tangent space at `(p, t)` in ambient product
space-time is `T_p M`, the pullback of `TM` along the spatial projection. -/
abbrev HorizontalTangentSpace
    (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] (z : M × ℝ) : Type _ :=
  TangentSpace I z.1

noncomputable instance instHorizontalTotalSpaceTopology :
    TopologicalSpace (TotalSpace E (HorizontalTangentSpace I M)) := by
  change TopologicalSpace
    (TotalSpace E
      ((Prod.fst : M × ℝ → M) *ᵖ (TangentSpace I : M → Type _)))
  infer_instance

noncomputable instance instHorizontalFiberBundle :
    FiberBundle E (HorizontalTangentSpace I M) := by
  let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
  change FiberBundle E (f *ᵖ (TangentSpace I : M → Type _))
  infer_instance

noncomputable instance instHorizontalVectorBundle :
    VectorBundle ℝ E (HorizontalTangentSpace I M) := by
  let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
  change VectorBundle ℝ E (f *ᵖ (TangentSpace I : M → Type _))
  infer_instance

noncomputable instance instHorizontalContMDiffVectorBundle :
    ContMDiffVectorBundle ∞ E (HorizontalTangentSpace I M)
      (I.prod 𝓘(ℝ, ℝ)) := by
  let f : C^∞⟮I.prod 𝓘(ℝ, ℝ), M × ℝ; I, M⟯ := ContMDiffMap.fst
  change ContMDiffVectorBundle ∞ E
    (f *ᵖ (TangentSpace I : M → Type _)) (I.prod 𝓘(ℝ, ℝ))
  infer_instance

/-- **Math.** The evolving metric as a section over the ambient product `M x R`.

The fiber over `(p, t)` is the space of continuous bilinear forms on the
horizontal tangent space `T_p M`. Restricting this section to `M x J` gives the
horizontal metric on product space-time. -/
def horizontalMetricSection (g : ℝ → RiemannianMetric I M) (z : M × ℝ) :
    TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
      (fun q : M × ℝ =>
        HorizontalTangentSpace I M q →L[ℝ]
          HorizontalTangentSpace I M q →L[ℝ] ℝ) :=
  TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) z
    ((g z.2).inner z.1)

/-- **Math.** A metric family is smooth on `J` when its associated horizontal bilinear
form is a smooth section on the product space-time `M x J`. -/
def IsSmoothMetricFamilyOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  ContMDiffOn (I.prod 𝓘(ℝ, ℝ))
    ((I.prod 𝓘(ℝ, ℝ)).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (horizontalMetricSection g) ((Set.univ : Set M) ×ˢ J)

/-- **Math.** The Ricci flow equation `partial_t g = -2 Ric(g)` on a time set `J`,
evaluated on arbitrary tangent vectors.  A within-derivative gives the intended
one-sided equation at endpoints. -/
def IsRicciFlowEquationOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (x y : TangentSpace I p),
    HasDerivWithinAt (fun s => (g s).metricInner p x y)
      (-2 * ricciTensorAt (g t) p x y) J t

/-- **Math.** A Ricci flow on a nondegenerate interval `J`: a jointly smooth family of
Riemannian metrics satisfying `partial_t g = -2 Ric(g)` throughout `J`. -/
structure IsRicciFlowOn (g : ℝ → RiemannianMetric I M) (J : Set ℝ) : Prop where
  ordConnected : J.OrdConnected
  nontrivial : J.Nontrivial
  smooth : IsSmoothMetricFamilyOn g J
  equation : IsRicciFlowEquationOn g J

/-- **Math.** An initial time is a least point of the time interval.  A Ricci flow need
not have one. -/
def IsInitialTime (J : Set ℝ) (t0 : ℝ) : Prop :=
  IsLeast J t0

/-- **Math.** The metric at an initial time. -/
abbrev initialMetric (g : ℝ → RiemannianMetric I M) (t0 : ℝ) :
    RiemannianMetric I M :=
  g t0

/-- **Math.** A metric is an initial metric for the family precisely when it occurs at a
least point of the time interval. -/
def IsInitialMetric (g : ℝ → RiemannianMetric I M) (J : Set ℝ)
    (g0 : RiemannianMetric I M) : Prop :=
  ∃ t0, IsInitialTime J t0 ∧ g0 = initialMetric g t0

end MorganTianLib

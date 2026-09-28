import DoCarmoLib.Riemannian.Connection.CurvaturePointwise
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci

/-!
# Curvature conventions and contractions

This module fixes Topping's curvature convention and packages its pointwise
Riemann, Ricci, and scalar curvatures. The underlying curvature operator and
basis-independent traces are provided by `DoCarmoLib` with the same sign
convention.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Topping's curvature operator
`R(X,Y)Z = ∇_Y ∇_X Z - ∇_X ∇_Y Z + ∇_[X,Y] Z`. -/
noncomputable def curvatureOperator (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) : SmoothVectorField I M :=
  g.leviCivitaConnection.curvature X Y Z

omit [I.Boundaryless] in
theorem curvatureOperator_apply (g : RiemannianMetric I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    curvatureOperator g X Y Z p =
      (g.leviCivitaConnection.cov Y (g.leviCivitaConnection.cov X Z)) p
        - (g.leviCivitaConnection.cov X (g.leviCivitaConnection.cov Y Z)) p
        + (g.leviCivitaConnection.cov (bracketField X Y) Z) p := by
  exact g.leviCivitaConnection.curvature_apply X Y Z p

/-- **Math.** The Riemann curvature tensor evaluated on smooth vector fields. -/
noncomputable def riemannCurvature (g : RiemannianMetric I M)
    (X Y Z W : SmoothVectorField I M) (p : M) : ℝ :=
  g.leviCivitaConnection.curvatureForm g X Y Z W p

/-- **Math.** The Riemann curvature tensor on four tangent vectors at a point. -/
noncomputable def riemannCurvatureAt (g : RiemannianMetric I M) (p : M)
    (x y z w : TangentSpace I p) : ℝ :=
  g.leviCivitaConnection.curvatureFormAt g p x y z w

theorem riemannCurvatureAt_eq (g : RiemannianMetric I M) (p : M)
    {x y z w : TangentSpace I p} {X Y Z W : SmoothVectorField I M}
    (hX : X p = x) (hY : Y p = y) (hZ : Z p = z) (hW : W p = w) :
    riemannCurvatureAt g p x y z w = riemannCurvature g X Y Z W p := by
  exact g.leviCivitaConnection.curvatureFormAt_eq g p hX hY hZ hW

/-- **Math.** The pointwise Riemann tensor of a Levi-Civita connection is an algebraic
curvature form. -/
theorem riemannCurvatureAt_isAlg (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    IsAlgCurvatureForm (riemannCurvatureAt g p) := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  let hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W q => g.koszulDualSection_dual X Y W q)
  change IsAlgCurvatureForm (g.leviCivitaConnection.curvatureFormAt g p)
  exact g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g hLC p

/-- **Math.** The Ricci tensor is the trace of the first and fourth slots of the
pointwise Riemann tensor. -/
noncomputable def ricciTensorAt (g : RiemannianMetric I M) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  Riemannian.ricciBilin (riemannCurvatureAt_isAlg g p)

/-- **Math.** Scalar curvature is the metric trace of the Ricci tensor. -/
noncomputable def scalarCurvatureAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  Riemannian.scalarCurvature (riemannCurvatureAt_isAlg g p)

theorem ricciTensorAt_eq_sum (g : RiemannianMetric I M) (p : M)
    (x y : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I p)),
      ricciTensorAt g p x y =
        ∑ i, riemannCurvatureAt g p x (e i) y (e i) := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  intro ι _ e
  simpa [ricciTensorAt, Riemannian.ricciBilin_apply] using
    Riemannian.ricciForm_eq_sum (riemannCurvatureAt_isAlg g p) x y e

theorem ricciTensorAt_symm (g : RiemannianMetric I M) (p : M)
    (x y : TangentSpace I p) :
    ricciTensorAt g p x y = ricciTensorAt g p y x := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  exact Riemannian.ricciForm_symm (riemannCurvatureAt_isAlg g p) x y

theorem scalarCurvatureAt_eq_trace (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    scalarCurvatureAt g p = Riemannian.bilinTrace (ricciTensorAt g p) := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  rfl

theorem scalarCurvatureAt_eq_sum (g : RiemannianMetric I M) (p : M) :
    letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
      ⟨g.toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι ℝ (TangentSpace I p)),
      scalarCurvatureAt g p =
        ∑ i, ∑ j, riemannCurvatureAt g p (e i) (e j) (e i) (e j) := by
  letI : Bundle.RiemannianBundle (fun q : M => TangentSpace I q) :=
    ⟨g.toRiemannianMetric⟩
  intro ι _ e
  simpa [scalarCurvatureAt] using
    Riemannian.scalarCurvature_eq_sum (riemannCurvatureAt_isAlg g p) e

end Topping

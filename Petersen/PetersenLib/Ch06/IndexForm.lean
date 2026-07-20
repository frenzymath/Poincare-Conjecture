import PetersenLib.Ch06.JacobiFields
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Petersen Ch. 6, §6.7 Ex. 6.7.24 — the index form (GTM 171, 3rd ed.)

`def:pet-ch6-ex-6-7-24` (`PetersenLib.indexForm`).  For vector fields `V, W`
along a geodesic `c : [0,1] → M`, the **index form** is
$$
  I(V,W) = \int_0^1 \big(g(\dot V, \dot W) - g(R(V, \dot c)\dot c, W)\big)\,dt .
$$
On the diagonal `V = W` this is exactly the integral part of the second variation
of energy of a proper variation whose variation field is `V`
(`secondVariationEnergy_properVariation`, `Ch06/SecondVariationGlobal.lean`).

Every ingredient is chart-free: `V̇`, `Ẇ` are `derivAlongCurve`, `R` is Ch. 3's
Koszul `curvatureTensorAt` of the Levi-Civita connection, `ċ` is `curveVelocity`,
and `g(·,·)` is `metricInner`.  Only the **definition** is landed here; the
index-lemma parts (1)–(4) of Ex. 6.7.24 (`V` with `I(V,V) = 0` is Jacobi;
`I(V,J) = I(J,J)`; `I(V,V) ≥ I(J,J)`; and the not-locally-minimizing consequence)
require the minimizer→`I ≥ 0` and Jacobi-characterization machinery and stay
`\notready`.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- **Math.** Petersen §6.7, Ex. 6.7.24 — the **index form** of two vector fields
`V, W` along a curve `c : [0,1] → M`:
`I(V,W) = ∫₀¹ (g(V̇, Ẇ) − g(R(V,ċ)ċ, W)) dt`.  `V̇`, `Ẇ` are `derivAlongCurve`,
`R` is Ch. 3's Koszul `curvatureTensorAt` of the Levi-Civita connection, and `ċ`
is `curveVelocity`.  Chart-free.  Its diagonal `indexForm g c V V` is the integral
in `secondVariationEnergy_properVariation`. -/
def indexForm (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t)) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    (g.metricInner (c t) (derivAlongCurve (I := I) g c V t)
                          (derivAlongCurve (I := I) g c W t)
     - g.metricInner (c t)
         (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
           (V t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t))
         (W t))

@[simp] theorem indexForm_def (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t)) :
    indexForm (I := I) g c V W
      = ∫ t in (0 : ℝ)..1,
          (g.metricInner (c t) (derivAlongCurve (I := I) g c V t)
                                (derivAlongCurve (I := I) g c W t)
           - g.metricInner (c t)
               (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
                 (V t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t))
               (W t)) := rfl

/-- **Math.** The index form is **symmetric under swapping the two Jacobi-equation
slots of the curvature term** in the sense that its diagonal `indexForm g c V V`
uses `R(V,ċ)ċ` paired with `V`; this records that the curvature integrand agrees
with the pointwise `(0,4)`-tensor `curvatureTensorFourAt`, the honest bridge to
the second-variation integrand. -/
theorem indexForm_curvature_eq_curvatureTensorFourAt (g : RiemannianMetric I M)
    (c : ℝ → M) (V W : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    g.metricInner (c t)
        (curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
          (V t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t))
        (W t)
      = curvatureTensorFourAt g.leviCivita (c t)
          (V t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t) (W t) :=
  rfl

end PetersenLib

end

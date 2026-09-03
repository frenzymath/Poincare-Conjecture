import MorganTianLib.Ch03.RicciFlow.Basic
import MorganTianLib.Ch02.EpsilonNeck

/-!
# Morgan--Tian Ch. 3 - evolving epsilon-necks

The Chapter 3 definition is a space-time strengthening of the static
`AmbientEpsilonNeck` from Chapter 2.  This file makes the rescaling map,
backward time set, normalized pullback family, standard shrinking-cylinder
family, and the uniform `C^[1/epsilon]` comparison explicit.  In particular,
the metric family in the definition is indexed by rescaled time and its
pullback formula uses the actual time
`t0 + R(x,t0)⁻¹ s`; no target-shaped curvature or closeness hypothesis is
hidden behind a name.

The analytic construction of the canonical metric families from arbitrary
open-submanifold data is separate infrastructure.  Here the fields of
`EvolvingEpsilonNeck` are exactly the geometric data asserted by the source
definition, while every compatibility equation is pointwise and explicit.

Reference: Morgan--Tian, *Ricci Flow and the Poincare Conjecture*, Chapter 3,
definition `def:evolving-epsilon-neck`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ## Rescaled time and the standard cylinder -/

/-- **Math.** The backward rescaled-time interval used by an evolving neck:
`-tau < s <= 0`. -/
def evolvingEpsilonNeckTimeSet (tau : ℝ) : Set ℝ := Ioc (-tau) 0

/-- **Math.** The actual time corresponding to rescaled time `s` at a point
whose scalar-curvature scale is `R`. -/
def evolvingEpsilonNeckActualTime (t0 R s : ℝ) : ℝ :=
  t0 + R⁻¹ * s

/-- **Math.** The central rescaled-time point. -/
def evolvingEpsilonNeckZeroTime {tau : ℝ} (htau : 0 < tau) :
    evolvingEpsilonNeckTimeSet tau :=
  ⟨0, by constructor <;> linarith⟩

@[simp] theorem evolvingEpsilonNeckActualTime_zero (t0 R : ℝ) :
    evolvingEpsilonNeckActualTime t0 R 0 = t0 := by
  simp [evolvingEpsilonNeckActualTime]

theorem evolvingEpsilonNeckZeroTime_mem {tau : ℝ} (htau : 0 < tau) :
    (evolvingEpsilonNeckZeroTime htau : ℝ) ∈ evolvingEpsilonNeckTimeSet tau :=
  (evolvingEpsilonNeckZeroTime htau).property

/-- **Math.** The standard shrinking-cylinder inner product at rescaled time
`s`.  Its spherical factor is `(1-s) h_0`; the axial factor is unchanged. -/
def standardShrinkingCylinderInner {epsilon : ℝ} (s : ℝ)
    (p : epsilonNeckDomain epsilon)
    (v w : TangentSpace EpsilonNeckCylinderModel p) : ℝ :=
  (1 - s) * roundSphereMetric.metricInner p.1.1
      (EuclideanSpace.finAddEquivProd v).1
      (EuclideanSpace.finAddEquivProd w).1 +
    inner ℝ (EuclideanSpace.finAddEquivProd v).2
      (EuclideanSpace.finAddEquivProd w).2

/-!
The cylinder domain in the book depends on `epsilon`.  The inner-product
formula itself is independent of the chosen epsilon; the next predicate is
therefore parameterized by the domain rather than fixing a representative
epsilon.
-/

/-- **Math.** A family of metrics is the standard shrinking round-cylinder
family when its pointwise inner product is
`(1-s) h_0 + ds^2`, where `h_0` is the round sphere metric of Gaussian
curvature `1/2`. -/
def IsStandardShrinkingCylinderFamily (epsilon tau : ℝ)
    (h : evolvingEpsilonNeckTimeSet tau →
      RiemannianMetric EpsilonNeckCylinderModel
        (epsilonNeckDomain epsilon)) : Prop :=
  ∀ (s : evolvingEpsilonNeckTimeSet tau)
    (p : epsilonNeckDomain epsilon)
    (v w : TangentSpace EpsilonNeckCylinderModel p),
    (h s).metricInner p v w =
      (1 - s.1) * roundSphereMetric.metricInner p.1.1
          (EuclideanSpace.finAddEquivProd v).1
          (EuclideanSpace.finAddEquivProd w).1 +
        inner ℝ (EuclideanSpace.finAddEquivProd v).2
          (EuclideanSpace.finAddEquivProd w).2

/-- **Math.** The ambient parametrization of the central neck, viewed as a map
from the cylinder domain directly into `M`. -/
def evolvingEpsilonNeckParametrization
    {epsilon : ℝ} {g : RiemannianMetric I M}
    (A : AmbientEpsilonNeck epsilon g) :
    epsilonNeckDomain epsilon → M :=
  letI := A.carrierSigmaCompact
  fun p => (A.neck.phi p : M)

/-- **Math.** The normalized pullback metric of an ambient neck, evaluated
on a cylinder tangent fiber.  The carrier's sigma-compact instance is
installed locally because the Chapter 2 neck stores it as a structure field.
-/
def AmbientEpsilonNeck.normalizedPullbackMetricInner
    {epsilon : ℝ} {g : RiemannianMetric I M}
    (A : AmbientEpsilonNeck epsilon g)
    (p : epsilonNeckDomain epsilon)
    (v w : TangentSpace EpsilonNeckCylinderModel p) : ℝ :=
  letI := A.carrierSigmaCompact
  A.neck.normalizedPullbackMetric.metricInner p v w

/-! ## The evolving neck contract -/

/-- **Math.** An evolving `epsilon`-neck centered at `(x,t0)` and defined for
backward rescaled time `tau`.

The fields spell out the source definition:

* `flow` is the ambient Ricci-flow contract;
* `centralNeck` is the static epsilon-neck at `(x,t0)`;
* `normalizedMetricFamily` is the exact scalar-curvature-normalized pullback
  of the actual time slices;
* `referenceMetricFamily` is the standard shrinking round cylinder;
* `close` is the uniform `C^[1/epsilon]` comparison over all rescaled times.

The time-availability and central-agreement fields prevent the family from
being merely a target-shaped `Has...` predicate: they identify the actual
time map and its value at the center. -/
structure EvolvingEpsilonNeck
    (epsilon : ℝ) (g : ℝ → RiemannianMetric I M) (J : Set ℝ)
    (x : M) (t0 : J) (tau : ℝ) where
  flow : IsRicciFlowOn g J
  depth_pos : 0 < tau
  scalar_curvature_pos :
    0 < canonicalScalarCurvature (g t0.1) x
  centralNeck : AmbientEpsilonNeck epsilon (g t0.1)
  central_center : centralNeck.ambientCenter = x
  time_available :
    ∀ s : evolvingEpsilonNeckTimeSet tau,
      evolvingEpsilonNeckActualTime t0.1
        (canonicalScalarCurvature (g t0.1) x) s.1 ∈ J
  referenceMetricFamily :
    evolvingEpsilonNeckTimeSet tau →
      RiemannianMetric EpsilonNeckCylinderModel
        (epsilonNeckDomain epsilon)
  referenceMetric_is_standard :
    IsStandardShrinkingCylinderFamily epsilon tau referenceMetricFamily
  normalizedMetricFamily :
    evolvingEpsilonNeckTimeSet tau →
      RiemannianMetric EpsilonNeckCylinderModel
        (epsilonNeckDomain epsilon)
  normalizedMetric_is_pullback :
    ∀ (s : evolvingEpsilonNeckTimeSet tau)
      (p : epsilonNeckDomain epsilon)
      (v w : TangentSpace EpsilonNeckCylinderModel p),
      (normalizedMetricFamily s).metricInner p v w =
        canonicalScalarCurvature (g t0.1) x *
          (g (evolvingEpsilonNeckActualTime t0.1
            (canonicalScalarCurvature (g t0.1) x) s.1)).metricInner
            (evolvingEpsilonNeckParametrization centralNeck p)
            (mfderiv EpsilonNeckCylinderModel I
              (evolvingEpsilonNeckParametrization centralNeck) p v)
            (mfderiv EpsilonNeckCylinderModel I
              (evolvingEpsilonNeckParametrization centralNeck) p w)
  central_agreement :
    ∀ (p : epsilonNeckDomain epsilon)
      (v w : TangentSpace EpsilonNeckCylinderModel p),
      (normalizedMetricFamily (evolvingEpsilonNeckZeroTime depth_pos)).metricInner
          p v w = AmbientEpsilonNeck.normalizedPullbackMetricInner centralNeck p v w
  close : EpsilonCloseFamily epsilon referenceMetricFamily normalizedMetricFamily

/-- **Math.** A strong epsilon-neck is an evolving epsilon-neck defined for
one unit of backward rescaled time. -/
abbrev StrongEpsilonNeck
    (epsilon : ℝ) (g : ℝ → RiemannianMetric I M) (J : Set ℝ)
    (x : M) (t0 : J) :=
  EvolvingEpsilonNeck epsilon g J x t0 1

namespace EvolvingEpsilonNeck

variable {epsilon : ℝ} {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
  {x : M} {t0 : J} {tau : ℝ}

/-- **Math.** The central time in an evolving neck is the time-zero slice of
the normalized family. -/
def centralTime (N : EvolvingEpsilonNeck epsilon g J x t0 tau) : J :=
  ⟨evolvingEpsilonNeckActualTime t0.1
      (canonicalScalarCurvature (g t0.1) x)
      (evolvingEpsilonNeckZeroTime N.depth_pos : ℝ),
    N.time_available (evolvingEpsilonNeckZeroTime N.depth_pos)⟩

@[simp] theorem centralTime_value
    (N : EvolvingEpsilonNeck epsilon g J x t0 tau) :
    (N.centralTime : ℝ) = t0.1 := by
  simp [centralTime, evolvingEpsilonNeckActualTime,
    evolvingEpsilonNeckZeroTime]

@[simp] theorem strongEpsilonNeck_depth
    (N : StrongEpsilonNeck epsilon g J x t0) : 0 < (1 : ℝ) :=
  N.depth_pos

end EvolvingEpsilonNeck

end MorganTianLib

end

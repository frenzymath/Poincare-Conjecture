import MorganTianLib.Ch01.Metric
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Morgan--Tian Ch. 3 -- the Fubini--Study construction interface

The Fubini--Study metric is normalized by requiring the Hopf projection from
the unit sphere in `C^(n+1)` to be a Riemannian submersion.  This file records
that construction as an exact producer interface: the target is a smooth
quotient whose fibers are the circle orbits, and its distinguished metric is
the unique metric with the submersion property.

Petersen proves a concrete inhabitant of this interface for its constructed
complex projective space.  Morgan--Tian does not currently depend on the
Petersen package, so this module keeps the producer abstract rather than
postulating a curvature or Ricci identity.  In particular, it makes no
Einstein claim.
-/

open Metric Module Function
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Riemannian

noncomputable section

namespace MorganTianLib

/-! ## The standard metric on the Hopf sphere -/

/-- **Math.** The unit sphere `S^(2n+1)` in `C^(n+1)`, the total space of the
Hopf fibration over complex projective `n`-space. -/
abbrev HopfSphere (n : Nat) :=
  sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1

/-- **Eng.** The real dimension of `C^(n+1)` is `2n+2`, as required by the
standard sphere manifold instance. -/
instance fact_finrank_hopfAmbient (n : Nat) :
    Fact (Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * n + 1 + 1) := by
  constructor
  have h : Module.finrank ℝ ℂ * Module.finrank ℂ (EuclideanSpace ℂ (Fin (n + 1))) =
      Module.finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) :=
    Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))
  rw [← h, finrank_euclideanSpace, Complex.finrank_real_complex, Fintype.card_fin]
  ring

/-- **Eng.** Circle scalars act on the unit Hopf sphere. -/
instance instMulActionCircleHopfSphere (n : Nat) : MulAction Circle (HopfSphere n) :=
  inferInstanceAs <| MulAction (sphere (0 : ℂ) 1) (HopfSphere n)

/-- **Math.** The round metric on `S^(2n+1)` induced by the standard real
inner product on `C^(n+1)`. -/
noncomputable def hopfSphereMetric (n : Nat) :
    RiemannianMetric (𝓡 (2 * n + 1)) (HopfSphere n) :=
  DCInducedMetric
    (DCEuclideanMetric (F := EuclideanSpace ℂ (Fin (n + 1))))
    ((↑) : HopfSphere n → EuclideanSpace ℂ (Fin (n + 1)))
    ⟨contMDiff_coe_sphere, fun p => mfderiv_coe_sphere_injective p⟩

/-! ## Riemannian submersions and the Fubini--Study producer -/

/-- **Math.** A smooth submersion is Riemannian when its differential is an
isometry on the orthogonal complement of its kernel. -/
def IsRiemannianSubmersion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
    (gM : RiemannianMetric I M) (gN : RiemannianMetric I' N) (f : M → N) : Prop :=
  ContMDiff I I' ∞ f ∧
    (∀ p : M, Surjective (mfderiv I I' f p)) ∧
    ∀ (p : M) (u v : TangentSpace I p),
      (∀ w : TangentSpace I p,
        mfderiv I I' f p w = 0 → gM.metricInner p u w = 0) →
      (∀ w : TangentSpace I p,
        mfderiv I I' f p w = 0 → gM.metricInner p v w = 0) →
      gM.metricInner p u v =
        gN.metricInner (f p) (mfderiv I I' f p u) (mfderiv I I' f p v)

/-- **Math.** The exact construction data for the Fubini--Study metric:

* the Hopf map is an open quotient with precisely the circle orbits as fibers;
* its distinguished metric makes the map a Riemannian submersion;
* that metric is uniquely characterized by this property.

There is intentionally no curvature or Einstein field in this structure. -/
structure FubiniStudyHopfConstruction (n : Nat)
    (P : Type*) [TopologicalSpace P] [ChartedSpace (Fin n → ℂ) P]
    [IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ P] where
  projection : HopfSphere n → P
  isOpenQuotientMap_projection : IsOpenQuotientMap projection
  fiber_eq_circleOrbit : ∀ z z' : HopfSphere n,
    projection z = projection z' ↔ ∃ a : Circle, a • z = z'
  metric : RiemannianMetric 𝓘(ℝ, Fin n → ℂ) P
  isRiemannianSubmersion :
    IsRiemannianSubmersion (hopfSphereMetric n) metric projection
  metric_unique : ∀ g : RiemannianMetric 𝓘(ℝ, Fin n → ℂ) P,
    IsRiemannianSubmersion (hopfSphereMetric n) g projection → g = metric

namespace FubiniStudyHopfConstruction

variable {n : Nat} {P : Type*} [TopologicalSpace P] [ChartedSpace (Fin n → ℂ) P]
  [IsManifold 𝓘(ℝ, Fin n → ℂ) ∞ P]

/-- **Math.** Package an existence-and-uniqueness theorem for a Hopf quotient
metric as a Fubini--Study construction.  This is the direct adapter for a
concrete quotient producer. -/
noncomputable def ofExistsUnique
    (projection : HopfSphere n → P)
    (hquot : IsOpenQuotientMap projection)
    (hfiber : ∀ z z' : HopfSphere n,
      projection z = projection z' ↔ ∃ a : Circle, a • z = z')
    (hmetric : ∃! g : RiemannianMetric 𝓘(ℝ, Fin n → ℂ) P,
      IsRiemannianSubmersion (hopfSphereMetric n) g projection) :
    FubiniStudyHopfConstruction n P where
  projection := projection
  isOpenQuotientMap_projection := hquot
  fiber_eq_circleOrbit := hfiber
  metric := hmetric.exists.choose
  isRiemannianSubmersion := hmetric.exists.choose_spec
  metric_unique := fun _g hg => hmetric.unique hg hmetric.exists.choose_spec

/-- **Math.** The Hopf projection in a Fubini--Study construction is smooth. -/
theorem contMDiff_projection (c : FubiniStudyHopfConstruction n P) :
    ContMDiff (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) ∞ c.projection :=
  c.isRiemannianSubmersion.1

/-- **Math.** The differential of the Hopf projection is surjective at every
point. -/
theorem surjective_mfderiv_projection (c : FubiniStudyHopfConstruction n P)
    (z : HopfSphere n) :
    Surjective (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) c.projection z) :=
  c.isRiemannianSubmersion.2.1 z

/-- **Math.** A tangent vector to the Hopf sphere is horizontal when it is
orthogonal to the kernel of the Hopf differential. -/
def IsHorizontal (c : FubiniStudyHopfConstruction n P) (z : HopfSphere n)
    (u : TangentSpace (𝓡 (2 * n + 1)) z) : Prop :=
  ∀ w : TangentSpace (𝓡 (2 * n + 1)) z,
    mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) c.projection z w = 0 →
      (hopfSphereMetric n).metricInner z u w = 0

/-- **Math.** Fubini--Study normalization: the Hopf differential preserves
the inner product of horizontal tangent vectors. -/
theorem metricInner_mfderiv_projection
    (c : FubiniStudyHopfConstruction n P) (z : HopfSphere n)
    (u v : TangentSpace (𝓡 (2 * n + 1)) z)
    (hu : c.IsHorizontal z u) (hv : c.IsHorizontal z v) :
    c.metric.metricInner (c.projection z)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) c.projection z u)
        (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, Fin n → ℂ) c.projection z v) =
      (hopfSphereMetric n).metricInner z u v :=
  (c.isRiemannianSubmersion.2.2 z u v hu hv).symm

end FubiniStudyHopfConstruction

end MorganTianLib

end

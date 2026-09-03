import MorganTianLib.Ch01.Chapter1BasicRemaining
import MorganTianLib.Ch01.ManifoldCurvature
import MorganTianLib.Ch02.EpsilonClose
import MorganTianLib.Ch02.LevelSetInducedMetric
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Morgan--Tian Ch. 2 -- epsilon-neck structures

This file packages the finite round cylinder used to define an epsilon-neck.
The cylinder model is transported to three-dimensional Euclidean space so that
the metric-closeness API can use its canonical inner product while the
underlying manifold remains the product of a two-sphere and an interval.
-/

open Metric Riemannian Set TopologicalSpace
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

/-- **Math.** The unit two-sphere used as the cross-section of the neck cylinder. -/
abbrev EpsilonNeckSphere :=
  sphere (0 : EuclideanSpace ℝ (Fin (2 + 1))) 1

/-- **Math.** A one-dimensional Euclidean axis, canonically identified with `R`. -/
abbrev EpsilonNeckAxis := EuclideanSpace ℝ (Fin 1)

/-- **Math.** The infinite cylinder before restriction to the finite neck interval. -/
abbrev EpsilonNeckCylinder := EpsilonNeckSphere × EpsilonNeckAxis

/-- **Math.** The native product model of the infinite cylinder. -/
abbrev EpsilonNeckProductModel := (𝓡 2).prod (𝓡 1)

/-- **Math.** The linear identification of the product model with `R^3`. -/
abbrev epsilonNeckModelEquiv :
    (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (2 + 1)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm

/-- **Math.** The product cylinder model transported to `R^3`.

The transport is needed because the ordinary product norm is not induced by an
inner product, whereas `EpsilonClose` uses an inner-product model to contract
covariant tensors. -/
abbrev EpsilonNeckCylinderModel :=
  EpsilonNeckProductModel.transContinuousLinearEquiv epsilonNeckModelEquiv

noncomputable instance epsilonNeckEuclideanNeZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1)))) := by
  constructor
  simp

noncomputable instance epsilonNeckSphereModelNeZero :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := by
  constructor
  simp

/-- **Math.** The open finite cylinder `S^2 x (-epsilon^-1, epsilon^-1)`. -/
noncomputable def epsilonNeckDomain (epsilon : ℝ) : Opens EpsilonNeckCylinder where
  carrier := {p | -epsilon⁻¹ < p.2 0 ∧ p.2 0 < epsilon⁻¹}
  is_open' := by
    have haxis : Continuous (fun p : EpsilonNeckCylinder => p.2 0) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp continuous_snd
    simpa only [setOf_and] using
      (isOpen_lt continuous_const haxis).inter
        (isOpen_lt haxis continuous_const)

noncomputable instance epsilonNeckDomainLocallyCompact (epsilon : ℝ) :
    LocallyCompactSpace (epsilonNeckDomain epsilon) :=
  (epsilonNeckDomain epsilon).isOpen.locallyCompactSpace

/-- **Math.** Reflection of the finite cylinder across its central slice. -/
def epsilonNeckReflectionPoint {epsilon : ℝ}
    (p : epsilonNeckDomain epsilon) : epsilonNeckDomain epsilon :=
  ⟨(p.1.1, -p.1.2), by
    change -epsilon⁻¹ < -(p.1.2 0) ∧ -(p.1.2 0) < epsilon⁻¹
    constructor <;> linarith [p.2.1, p.2.2]⟩

/-- **Math.** Axial reflection is an involutive equivalence of the finite
cylinder. -/
def epsilonNeckReflectionEquiv (epsilon : ℝ) :
    epsilonNeckDomain epsilon ≃ epsilonNeckDomain epsilon where
  toFun := epsilonNeckReflectionPoint
  invFun := epsilonNeckReflectionPoint
  left_inv := by
    intro p
    ext <;> simp [epsilonNeckReflectionPoint]
  right_inv := by
    intro p
    ext <;> simp [epsilonNeckReflectionPoint]

/-- **Math.** Axial reflection as a diffeomorphism for the native product
model of the cylinder. -/
noncomputable def epsilonNeckProductReflection (epsilon : ℝ) :
    Diffeomorph EpsilonNeckProductModel EpsilonNeckProductModel
      (epsilonNeckDomain epsilon) (epsilonNeckDomain epsilon) ∞ where
  toEquiv := epsilonNeckReflectionEquiv epsilon
  contMDiff_toFun := by
    rw [← ContMDiff.subtypeVal_comp_iff (epsilonNeckDomain epsilon)]
    change ContMDiff EpsilonNeckProductModel EpsilonNeckProductModel ∞
      (fun p : epsilonNeckDomain epsilon => (p.1.1, -p.1.2))
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (contDiff_neg.contMDiff.comp (contMDiff_snd.comp contMDiff_subtype_val))
  contMDiff_invFun := by
    rw [← ContMDiff.subtypeVal_comp_iff (epsilonNeckDomain epsilon)]
    change ContMDiff EpsilonNeckProductModel EpsilonNeckProductModel ∞
      (fun p : epsilonNeckDomain epsilon => (p.1.1, -p.1.2))
    exact (contMDiff_fst.comp contMDiff_subtype_val).prodMk
      (contDiff_neg.contMDiff.comp (contMDiff_snd.comp contMDiff_subtype_val))

/-- **Math.** Axial reflection as a diffeomorphism in the transported
three-dimensional cylinder model. -/
noncomputable def epsilonNeckReflection (epsilon : ℝ) :
    Diffeomorph EpsilonNeckCylinderModel EpsilonNeckCylinderModel
      (epsilonNeckDomain epsilon) (epsilonNeckDomain epsilon) ∞ :=
  let changeModel := ContinuousLinearEquiv.toTransContinuousLinearEquiv
    EpsilonNeckProductModel (epsilonNeckDomain epsilon) epsilonNeckModelEquiv
  changeModel.symm.trans
    ((epsilonNeckProductReflection epsilon).trans changeModel)

/-- **Math.** The round unit-sphere metric induced from Euclidean three-space. -/
noncomputable def unitRoundSphereMetric :
    RiemannianMetric (𝓡 2) EpsilonNeckSphere :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 + 1))) = 2 + 1) :=
    ⟨by simp⟩
  DCInducedMetric
    (DCEuclideanMetric (F := EuclideanSpace ℝ (Fin (2 + 1))))
    ((↑) : EpsilonNeckSphere → EuclideanSpace ℝ (Fin (2 + 1)))
    ⟨contMDiff_coe_sphere, fun p => mfderiv_coe_sphere_injective p⟩

/-- **Math.** The round sphere metric of Gaussian curvature `1 / 2`, obtained by
rescaling the unit-sphere metric by `2`. -/
noncomputable def roundSphereMetric :
    RiemannianMetric (𝓡 2) EpsilonNeckSphere :=
  rescaledMetric unitRoundSphereMetric 2 (by norm_num)

/-!
The bundled constant-curvature producer for the induced unit-sphere metric is
not yet available in this project.  This adapter isolates that missing input:
once the unit-sphere statement is supplied, the curvature of the declared
radius-`sqrt 2` round metric follows from the checked rescaling law.
-/

theorem roundSphereMetric_isConstantCurvature_of_unitRoundSphereMetric
    (hunit : unitRoundSphereMetric.leviCivitaConnection.IsConstantCurvature
      unitRoundSphereMetric (1 : ℝ)) :
    roundSphereMetric.leviCivitaConnection.IsConstantCurvature
      roundSphereMetric (1 / 2 : ℝ) := by
  simpa [roundSphereMetric] using
    (rescaledMetric_isConstantCurvature unitRoundSphereMetric 2 (by norm_num)
      1 hunit)

/-- **Math.** A metric on the finite cylinder is the product of the round sphere metric
of curvature `1 / 2` and the Euclidean metric on the axis. -/
def IsRoundCylinderMetric (epsilon : ℝ)
    (g0 : RiemannianMetric EpsilonNeckCylinderModel
      (epsilonNeckDomain epsilon)) : Prop :=
  roundSphereMetric.leviCivitaConnection.IsConstantCurvature
      roundSphereMetric (1 / 2 : ℝ) ∧
    ∀ (p : epsilonNeckDomain epsilon)
      (v w : TangentSpace EpsilonNeckCylinderModel p),
      g0.metricInner p v w =
        roundSphereMetric.metricInner p.1.1
          (EuclideanSpace.finAddEquivProd v).1
          (EuclideanSpace.finAddEquivProd w).1 +
        inner ℝ (EuclideanSpace.finAddEquivProd v).2
          (EuclideanSpace.finAddEquivProd w).2

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [I.Boundaryless] [SigmaCompactSpace N] [T2Space N]

/-- **Math.** Scalar curvature computed using the canonical Levi-Civita connection. -/
def canonicalScalarCurvature (g : RiemannianMetric I N) (x : N) : ℝ :=
  scalarCurvatureAt g g.leviCivitaConnection
    (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y W p => g.koszulDualSection_dual X Y W p)) x

/-- **Math.** The sphere slice with axial coordinate `t`. -/
def epsilonNeckSlice {epsilon : ℝ}
    (phi : Diffeomorph EpsilonNeckCylinderModel I
      (epsilonNeckDomain epsilon) N ∞) (t : ℝ) : Set N :=
  {y | (phi.symm y).1.2 0 = t}

/-- **Math.** An epsilon-neck structure centered at `x`.

The two metric fields expose the comparison as a type-level assertion: the
second is exactly scalar curvature at `x` times the pullback of `g`, and it is
epsilon-close to the fixed round product metric. -/
structure EpsilonNeckStructure (epsilon : ℝ)
    (g : RiemannianMetric I N) (x : N) where
  dimension_three : Module.finrank ℝ E = 3
  phi : Diffeomorph EpsilonNeckCylinderModel I
    (epsilonNeckDomain epsilon) N ∞
  referenceMetric :
    RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain epsilon)
  normalizedPullbackMetric :
    RiemannianMetric EpsilonNeckCylinderModel (epsilonNeckDomain epsilon)
  reference_is_round : IsRoundCylinderMetric epsilon referenceMetric
  normalized_pullback : ∀ (p : epsilonNeckDomain epsilon)
      (v w : TangentSpace EpsilonNeckCylinderModel p),
    normalizedPullbackMetric.metricInner p v w =
      canonicalScalarCurvature g x *
        g.metricInner (phi p)
          (mfderiv EpsilonNeckCylinderModel I phi p v)
          (mfderiv EpsilonNeckCylinderModel I phi p w)
  close : EpsilonClose epsilon referenceMetric normalizedPullbackMetric
  center_mem : x ∈ epsilonNeckSlice phi 0

/-- **Math.** The unit vector in the positive axial direction, expressed in
the transported three-dimensional cylinder model. -/
def epsilonNeckAxialUnit : EuclideanSpace ℝ (Fin (2 + 1)) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := 2) (m := 1)).symm
    (0, EuclideanSpace.single 0 1)

namespace EpsilonNeckStructure

variable {epsilon : ℝ} {g : RiemannianMetric I N} {x : N}

/-- **Math.** The axial coordinate `s_N = p_2 ∘ phi⁻¹`. -/
def axialCoordinate (S : EpsilonNeckStructure epsilon g x) (y : N) : ℝ :=
  (S.phi.symm y).1.2 0

/-- **Math.** The axial vector field `partial / partial s_N`, obtained by
pushing the unit axial vector forward through the neck parametrization. -/
def axialVector (S : EpsilonNeckStructure epsilon g x) (y : N) :
    TangentSpace I y :=
  mfderiv EpsilonNeckCylinderModel I S.phi (S.phi.symm y)
    epsilonNeckAxialUnit

/-- **Math.** The end on which the axial coordinate is negative. -/
def negativeEnd (S : EpsilonNeckStructure epsilon g x) : Set N :=
  {y | S.axialCoordinate y < 0}

/-- **Math.** The end on which the axial coordinate is positive. -/
def positiveEnd (S : EpsilonNeckStructure epsilon g x) : Set N :=
  {y | 0 < S.axialCoordinate y}

/-- **Math.** The fractional subneck between the axial fractions `a` and `b`.
Its coordinate interval is `(a * epsilon⁻¹, b * epsilon⁻¹)`. -/
def fractionalSubneck (S : EpsilonNeckStructure epsilon g x) (a b : ℝ) : Set N :=
  {y | a * epsilon⁻¹ < S.axialCoordinate y ∧
    S.axialCoordinate y < b * epsilon⁻¹}

/-- **Math.** The neck scale `r_N = R(x)^{-1/2}`. -/
def scale (_S : EpsilonNeckStructure epsilon g x) : ℝ :=
  (Real.sqrt (canonicalScalarCurvature g x))⁻¹

/-- **Math.** The reversed neck parametrization
`phi ∘ (id_(S^2) x (-1))`. -/
noncomputable def reversedParametrization
    (S : EpsilonNeckStructure epsilon g x) :
    Diffeomorph EpsilonNeckCylinderModel I
      (epsilonNeckDomain epsilon) N ∞ :=
  (epsilonNeckReflection epsilon).trans S.phi

/-- **Math.** The reversed parametrization is exactly
`p ↦ phi (p_1, -p_2)`. -/
@[simp] theorem reversedParametrization_apply
    (S : EpsilonNeckStructure epsilon g x)
    (p : epsilonNeckDomain epsilon) :
    S.reversedParametrization p = S.phi (epsilonNeckReflectionPoint p) :=
  rfl

end EpsilonNeckStructure

/-- **Math.** An epsilon-neck in an ambient Riemannian three-manifold is an
open, hence codimension-zero, submanifold with its induced metric and an
epsilon-neck structure. -/
structure AmbientEpsilonNeck (epsilon : ℝ) (g : RiemannianMetric I N) where
  carrier : Opens N
  [carrierSigmaCompact : SigmaCompactSpace carrier]
  inducedMetric : RiemannianMetric I carrier
  induced_metric : ∀ (p : carrier) (v w : TangentSpace I p),
    inducedMetric.metricInner p v w =
      g.metricInner p.1
        (mfderiv I I ((↑) : carrier → N) p v)
        (mfderiv I I ((↑) : carrier → N) p w)
  center : carrier
  neck : EpsilonNeckStructure epsilon inducedMetric center

variable {epsilon : ℝ} {g : RiemannianMetric I N}

/-- **Math.** The center of an ambient neck, viewed in the ambient manifold. -/
def AmbientEpsilonNeck.ambientCenter
    (A : AmbientEpsilonNeck epsilon g) : N :=
  A.center

/-- **Math.** The scale of an ambient neck is the scale of its intrinsic neck
structure. -/
def AmbientEpsilonNeck.scale (A : AmbientEpsilonNeck epsilon g) : ℝ :=
  letI := A.carrierSigmaCompact
  A.neck.scale

end MorganTianLib

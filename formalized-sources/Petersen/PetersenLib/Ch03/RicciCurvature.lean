import PetersenLib.Ch03.SectionalCurvature

/-!
# Petersen Ch. 3, §3.1.4–§3.1.5 — Ricci and scalar curvature (definitions)

The Ricci curvature as the trace `Ric(v,w) = tr(x ↦ R(x,v)w)`
(`RicciCurvature`, via the packaged linear map
`curvatureTensorAtFirstLinear`), Einstein manifolds (`IsEinstein`), and the
scalar curvature `scal = tr(Ric)` (`scalarCurvature`, via the metric-Riesz
`(1,1)`-form of the Ricci tensor).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.4–§3.1.5.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- The pointwise curvature tensor packaged as a linear map in its first slot,
`x ↦ R(x,v)w`. -/
def curvatureTensorAtFirstLinear (D : AffineConnection I M) (p : M)
    (v w : TangentSpace I p) : TangentSpace I p →ₗ[ℝ] TangentSpace I p where
  toFun := fun x => curvatureTensorAt D p x v w
  map_add' := fun x₁ x₂ => curvatureTensorAt_add_first D p x₁ x₂ v w
  map_smul' := fun c x => curvatureTensorAt_smul_first D p c x v w

@[simp]
theorem curvatureTensorAtFirstLinear_apply (D : AffineConnection I M) (p : M)
    (v w x : TangentSpace I p) :
    curvatureTensorAtFirstLinear D p v w x = curvatureTensorAt D p x v w := rfl

/-- **Math.** The **Ricci curvature** (Petersen §3.1.4): the trace
`Ric(v,w) = tr(x ↦ R(x,v)w)`; in a `g`-orthonormal basis `e₁, …, eₙ` of `T_pM`
this is `∑ᵢ g(R(eᵢ,v)w, eᵢ)`. A symmetric bilinear form on `T_pM`. -/
def RicciCurvature (D : AffineConnection I M) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  LinearMap.trace ℝ (TangentSpace I p) (curvatureTensorAtFirstLinear D p v w)

/-- **Math.** **Einstein manifolds** (Petersen §3.1.4): `(M,g)` is Einstein
with Einstein constant `k` if `Ric(v) = k·v` for all `v`, equivalently
`Ric(v,w) = k·g(v,w)` for all `v, w`. -/
def IsEinstein {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    (k : ℝ) : Prop :=
  ∀ (p : M) (v w : TangentSpace I p),
    RicciCurvature D.toAffineConnection p v w = k * g.metricInner p v w

/-- The Ricci tensor as a `(1,1)`-tensor `Ric(v) ∈ T_pM`, via the metric-Riesz
duality: `g(Ric(v), w) = Ric(v,w)`. -/
def ricciEndomorphism {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    (p : M) (v : TangentSpace I p) : TangentSpace I p :=
  g.metricRiesz p (LinearMap.toContinuousLinearMap
    { toFun := fun w => RicciCurvature D.toAffineConnection p v w
      map_add' := fun w₁ w₂ => by
        simp only [RicciCurvature]
        rw [← map_add]
        congr 1
        ext x
        simp only [LinearMap.add_apply, curvatureTensorAtFirstLinear_apply]
        exact curvatureTensorAt_add_field D.toAffineConnection p x v w₁ w₂
      map_smul' := fun c w => by
        simp only [RicciCurvature, RingHom.id_apply]
        rw [← map_smul]
        congr 1
        ext x
        simp only [LinearMap.smul_apply, curvatureTensorAtFirstLinear_apply]
        exact curvatureTensorAt_smul_field D.toAffineConnection p c x v w })

@[simp]
theorem metricInner_ricciEndomorphism {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) (v w : TangentSpace I p) :
    g.metricInner p (ricciEndomorphism D p v) w
      = RicciCurvature D.toAffineConnection p v w := by
  rw [ricciEndomorphism, RiemannianMetric.metricRiesz_inner]
  rfl

/-- The Ricci `(1,1)`-tensor is linear in `v`. -/
def ricciEndomorphismLinear {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) :
    TangentSpace I p →ₗ[ℝ] TangentSpace I p where
  toFun := ricciEndomorphism D p
  map_add' := fun v₁ v₂ => by
    refine (g.metricInner_eq_iff_eq p _ _).mp fun z => ?_
    rw [metricInner_ricciEndomorphism, g.metricInner_add_left,
      metricInner_ricciEndomorphism, metricInner_ricciEndomorphism]
    simp only [RicciCurvature]
    rw [← map_add]
    congr 1
    ext x
    simp only [LinearMap.add_apply, curvatureTensorAtFirstLinear_apply]
    exact curvatureTensorAt_add_middle D.toAffineConnection p x v₁ v₂ z
  map_smul' := fun c v => by
    refine (g.metricInner_eq_iff_eq p _ _).mp fun z => ?_
    simp only [RingHom.id_apply]
    rw [metricInner_ricciEndomorphism, g.metricInner_smul_left,
      metricInner_ricciEndomorphism]
    simp only [RicciCurvature]
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    ext x
    simp only [LinearMap.smul_apply, curvatureTensorAtFirstLinear_apply]
    exact curvatureTensorAt_smul_middle D.toAffineConnection p c x v z

/-- **Math.** The **scalar curvature** (Petersen §3.1.5):
`scal = tr(Ric) : M → ℝ` — the trace of the `(1,1)`-Ricci tensor (equal to
`2·tr 𝔯` for the curvature operator `𝔯`). -/
def scalarCurvature {g : RiemannianMetric I M} (D : RiemannianConnection I g) :
    M → ℝ :=
  fun p => LinearMap.trace ℝ (TangentSpace I p) (ricciEndomorphismLinear D p)

end PetersenLib

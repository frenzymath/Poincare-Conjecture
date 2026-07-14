import PetersenLib.Ch03.SectionalCurvature
import Mathlib.LinearAlgebra.Trace

/-!
# Petersen Ch. 3, §3.1.2 — The curvature operator

The curvature operator `𝔯 : Λ²T_pM → Λ²T_pM` (Petersen §3.1.2,
`def:pet-ch3-curvature-operator`), with `Λ²T_pM` realized as the space of
`g`-skew-symmetric endomorphisms of `T_pM`: a bivector `x ∧ y` is identified
with the skew map `(x∧y)(v) = g(x,v)y − g(y,v)x` (`bivectorSkewMap`,
packaged here as the endomorphism `wedgeEndo`), and in finite dimension the
wedges span all skew endomorphisms (`IsSkewAt.eq_sum_wedgeEndo`), so this is
the standard metric identification `Λ²V ≅ 𝔰𝔬(V)`.

* `bivectorEndoInner A B = −½·tr(A∘B)` — the inner product on `Λ²T_pM`;
  on wedges it is the Gram-determinant bivector inner product
  (`bivectorEndoInner_wedgeEndo_wedgeEndo`), and against a single wedge it is
  `⟨A, v∧w⟩ = g(A(v), w)` (`bivectorEndoInner_wedgeEndo_right`).
* `curvatureOperator D p` — the curvature operator, defined basis-free by
  `g(𝔯(A)(v), w) = −½·tr(A ∘ curvatureRieszEndo D p w v)` via Riesz duality;
  its defining property `⟨𝔯(x∧y), v∧w⟩ = R(x,y,w,v)`
  (note Petersen's reversal of the last two arguments) is
  `bivectorEndoInner_curvatureOperator_wedge_wedge`, extended to finite sums
  of wedges by `bivectorEndoInner_curvatureOperator_sum_wedges`.
* `curvatureOperator_isSelfAdjoint` — `⟨𝔯(A), B⟩ = ⟨A, 𝔯(B)⟩` on skew
  endomorphisms, from the pair-swap symmetry of `R`.
* `curvatureOperator_unique` — a linear operator with skew values satisfying
  the defining property on wedges agrees with `𝔯` on all of `Λ²T_pM`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.2.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ## Riesz representation of linear functionals -/

/-- The tangent vector `g`-representing a linear functional on `T_pM`
(the plain-`LinearMap` interface to `metricRiesz`; in finite dimension every
linear functional is continuous). -/
def metricRieszOfLinear (g : RiemannianMetric I M) (p : M)
    (φ : TangentSpace I p →ₗ[ℝ] ℝ) : TangentSpace I p :=
  g.metricRiesz p (LinearMap.toContinuousLinearMap φ)

@[simp]
theorem metricInner_metricRieszOfLinear (g : RiemannianMetric I M) (p : M)
    (φ : TangentSpace I p →ₗ[ℝ] ℝ) (t : TangentSpace I p) :
    g.metricInner p (metricRieszOfLinear g p φ) t = φ t :=
  g.metricRiesz_inner p (LinearMap.toContinuousLinearMap φ) t

theorem metricRieszOfLinear_unique (g : RiemannianMetric I M) (p : M)
    {φ : TangentSpace I p →ₗ[ℝ] ℝ} {v : TangentSpace I p}
    (h : ∀ t, g.metricInner p v t = φ t) :
    v = metricRieszOfLinear g p φ :=
  g.metricRiesz_unique p v (LinearMap.toContinuousLinearMap φ) h

/-- `g`-inner products distribute over finite sums in the left slot. -/
theorem metricInner_finsetSum_left (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (f : ι → TangentSpace I p)
    (w : TangentSpace I p) :
    g.metricInner p (∑ i ∈ s, f i) w = ∑ i ∈ s, g.metricInner p (f i) w := by
  calc g.metricInner p (∑ i ∈ s, f i) w
      = g.metricBilin p (∑ i ∈ s, f i) w := rfl
    _ = (∑ i ∈ s, g.metricBilin p (f i)) w := by rw [map_sum]
    _ = ∑ i ∈ s, g.metricBilin p (f i) w := by rw [LinearMap.sum_apply]
    _ = ∑ i ∈ s, g.metricInner p (f i) w := rfl

/-! ## Bivectors as skew-symmetric endomorphisms -/

/-- **Math.** The bivector `x ∧ y` as an endomorphism of `T_pM`
(Petersen §3.1.2): the linear-map packaging of `bivectorSkewMap`,
`(x∧y)(v) = g(x,v)y − g(y,v)x`. -/
def wedgeEndo (g : RiemannianMetric I M) (p : M) (x y : TangentSpace I p) :
    Module.End ℝ (TangentSpace I p) :=
  (g.metricBilin p x).smulRight y - (g.metricBilin p y).smulRight x

@[simp]
theorem wedgeEndo_apply (g : RiemannianMetric I M) (p : M)
    (x y v : TangentSpace I p) :
    wedgeEndo g p x y v = bivectorSkewMap g p x y v := rfl

/-- **Math.** A `g_p`-skew-symmetric endomorphism of `T_pM`: the pointwise
model for `Λ²T_pM` (Petersen §3.1.2). -/
def IsSkewAt (g : RiemannianMetric I M) (p : M)
    (A : Module.End ℝ (TangentSpace I p)) : Prop :=
  ∀ v w : TangentSpace I p,
    g.metricInner p (A v) w = -g.metricInner p v (A w)

/-- Wedges are skew. -/
theorem isSkewAt_wedgeEndo (g : RiemannianMetric I M) (p : M)
    (x y : TangentSpace I p) : IsSkewAt g p (wedgeEndo g p x y) := by
  intro v w
  simp only [wedgeEndo_apply, bivectorSkewMap]
  rw [g.metricInner_sub_left, g.metricInner_smul_left, g.metricInner_smul_left,
    g.metricInner_sub_right, g.metricInner_smul_right, g.metricInner_smul_right,
    g.metricInner_comm p y v, g.metricInner_comm p x v,
    g.metricInner_comm p v x, g.metricInner_comm p v y]
  ring

/-! ## The inner product on `Λ²T_pM` -/

/-- **Math.** The inner product on `Λ²T_pM` in the skew-endomorphism model
(Petersen §3.1.2): `⟨A, B⟩ = −½·tr(A∘B)`; on wedges this is the Gram
determinant `g(x∧y, v∧w)` (`bivectorEndoInner_wedgeEndo_wedgeEndo`). -/
def bivectorEndoInner (g : RiemannianMetric I M) (p : M)
    (A B : Module.End ℝ (TangentSpace I p)) : ℝ :=
  -(1 / 2 : ℝ) * LinearMap.trace ℝ (TangentSpace I p) (A * B)

theorem bivectorEndoInner_comm (g : RiemannianMetric I M) (p : M)
    (A B : Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p A B = bivectorEndoInner g p B A := by
  rw [bivectorEndoInner, bivectorEndoInner, LinearMap.trace_mul_comm]

theorem bivectorEndoInner_add_left (g : RiemannianMetric I M) (p : M)
    (A₁ A₂ B : Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p (A₁ + A₂) B
      = bivectorEndoInner g p A₁ B + bivectorEndoInner g p A₂ B := by
  simp only [bivectorEndoInner, add_mul, map_add]
  ring

theorem bivectorEndoInner_smul_left (g : RiemannianMetric I M) (p : M)
    (c : ℝ) (A B : Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p (c • A) B = c * bivectorEndoInner g p A B := by
  simp only [bivectorEndoInner, smul_mul_assoc, map_smul, smul_eq_mul]
  ring

theorem bivectorEndoInner_add_right (g : RiemannianMetric I M) (p : M)
    (A B₁ B₂ : Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p A (B₁ + B₂)
      = bivectorEndoInner g p A B₁ + bivectorEndoInner g p A B₂ := by
  simp only [bivectorEndoInner, mul_add, map_add]

theorem bivectorEndoInner_smul_right (g : RiemannianMetric I M) (p : M)
    (c : ℝ) (A B : Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p A (c • B) = c * bivectorEndoInner g p A B := by
  simp only [bivectorEndoInner, mul_smul_comm, map_smul, smul_eq_mul]
  ring

theorem bivectorEndoInner_sum_left (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (f : ι → Module.End ℝ (TangentSpace I p))
    (B : Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p (∑ i ∈ s, f i) B
      = ∑ i ∈ s, bivectorEndoInner g p (f i) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, bivectorEndoInner, zero_mul, map_zero,
        mul_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        bivectorEndoInner_add_left, ih]

theorem bivectorEndoInner_sum_right (g : RiemannianMetric I M) (p : M)
    {ι : Type*} (s : Finset ι) (A : Module.End ℝ (TangentSpace I p))
    (f : ι → Module.End ℝ (TangentSpace I p)) :
    bivectorEndoInner g p A (∑ i ∈ s, f i)
      = ∑ i ∈ s, bivectorEndoInner g p A (f i) := by
  rw [bivectorEndoInner_comm, bivectorEndoInner_sum_left]
  exact Finset.sum_congr rfl fun i _ => bivectorEndoInner_comm g p (f i) A

/-- Composition with a wedge on the right, in `smulRight` normal form. -/
theorem mul_wedgeEndo (g : RiemannianMetric I M) (p : M)
    (A : Module.End ℝ (TangentSpace I p)) (v w : TangentSpace I p) :
    A * wedgeEndo g p v w
      = (g.metricBilin p v).smulRight (A w) - (g.metricBilin p w).smulRight (A v) := by
  ext z
  simp only [Module.End.mul_apply, wedgeEndo_apply, bivectorSkewMap,
    LinearMap.sub_apply, LinearMap.smulRight_apply, map_sub, map_smul,
    RiemannianMetric.metricBilin_apply]

/-- **Math.** Against a single wedge, the `Λ²` inner product of a *skew*
endomorphism reads off its matrix entry: `⟨A, v∧w⟩ = g(A(v), w)` —
the extension of `bivectorSkewMap_metricInner` from wedges to all of
`Λ²T_pM`. -/
theorem bivectorEndoInner_wedgeEndo_right (g : RiemannianMetric I M) (p : M)
    {A : Module.End ℝ (TangentSpace I p)} (hA : IsSkewAt g p A)
    (v w : TangentSpace I p) :
    bivectorEndoInner g p A (wedgeEndo g p v w) = g.metricInner p (A v) w := by
  rw [bivectorEndoInner, mul_wedgeEndo, map_sub, LinearMap.trace_smulRight,
    LinearMap.trace_smulRight]
  simp only [RiemannianMetric.metricBilin_apply]
  rw [g.metricInner_comm p w (A v), hA v w, g.metricInner_comm p v (A w)]
  ring

/-- **Math.** On wedges, `⟨·,·⟩` is the bivector inner product
`g(x∧y, v∧w) = g(x,v)g(y,w) − g(x,w)g(y,v)` (Petersen §3.1.2). -/
theorem bivectorEndoInner_wedgeEndo_wedgeEndo (g : RiemannianMetric I M)
    (p : M) (x y v w : TangentSpace I p) :
    bivectorEndoInner g p (wedgeEndo g p x y) (wedgeEndo g p v w)
      = bivectorInnerProduct g p x y v w := by
  rw [bivectorEndoInner_wedgeEndo_right g p (isSkewAt_wedgeEndo g p x y) v w,
    wedgeEndo_apply, bivectorSkewMap_metricInner]

/-! ## The curvature operator -/

variable {g : RiemannianMetric I M}

/-- The `(0,4)`-curvature tensor at `p`, `t ↦ R(z,t,w,v)`, as a linear
functional in its second slot. -/
def curvatureFourFunctional (D : RiemannianConnection I g) (p : M)
    (z w v : TangentSpace I p) : TangentSpace I p →ₗ[ℝ] ℝ where
  toFun t := curvatureTensorFourAt D p z t w v
  map_add' t₁ t₂ := (isAlgCurvatureForm_curvatureTensorFourAt D p).add_two z t₁ t₂ w v
  map_smul' c t := (isAlgCurvatureForm_curvatureTensorFourAt D p).smul_two c z t w v

@[simp]
theorem curvatureFourFunctional_apply (D : RiemannianConnection I g) (p : M)
    (z w v t : TangentSpace I p) :
    curvatureFourFunctional D p z w v t = curvatureTensorFourAt D p z t w v := rfl

/-- **Math.** For fixed `w, v ∈ T_pM`, the skew endomorphism `C_{w,v}`
with `g(C_{w,v}(z), t) = R(z,t,w,v)` — the `(0,4)`-curvature tensor with its
last two slots frozen, raised to a `(1,1)`-tensor by Riesz duality. -/
def curvatureRieszEndo (D : RiemannianConnection I g) (p : M)
    (w v : TangentSpace I p) : Module.End ℝ (TangentSpace I p) where
  toFun z := metricRieszOfLinear g p (curvatureFourFunctional D p z w v)
  map_add' z₁ z₂ := by
    refine (metricRieszOfLinear_unique g p fun t => ?_).symm
    rw [g.metricInner_add_left, metricInner_metricRieszOfLinear,
      metricInner_metricRieszOfLinear]
    simp only [curvatureFourFunctional_apply]
    exact ((isAlgCurvatureForm_curvatureTensorFourAt D p).add_left z₁ z₂ t w v).symm
  map_smul' c z := by
    refine (metricRieszOfLinear_unique g p fun t => ?_).symm
    rw [RingHom.id_apply, g.metricInner_smul_left, metricInner_metricRieszOfLinear]
    simp only [curvatureFourFunctional_apply]
    exact ((isAlgCurvatureForm_curvatureTensorFourAt D p).smul_left c z t w v).symm

@[simp]
theorem metricInner_curvatureRieszEndo (D : RiemannianConnection I g) (p : M)
    (w v z t : TangentSpace I p) :
    g.metricInner p (curvatureRieszEndo D p w v z) t
      = curvatureTensorFourAt D p z t w v := by
  show g.metricInner p (metricRieszOfLinear g p _) t = _
  rw [metricInner_metricRieszOfLinear, curvatureFourFunctional_apply]

/-- Linearity of `C_{w,v}` in `w` (third slot of `R`). -/
theorem curvatureRieszEndo_add_w (D : RiemannianConnection I g) (p : M)
    (w₁ w₂ v : TangentSpace I p) :
    curvatureRieszEndo D p (w₁ + w₂) v
      = curvatureRieszEndo D p w₁ v + curvatureRieszEndo D p w₂ v := by
  ext z
  refine ((g.metricInner_eq_iff_eq p _ _).mp fun t => ?_)
  rw [metricInner_curvatureRieszEndo]
  show _ = g.metricInner p (curvatureRieszEndo D p w₁ v z
    + curvatureRieszEndo D p w₂ v z) t
  rw [g.metricInner_add_left, metricInner_curvatureRieszEndo,
    metricInner_curvatureRieszEndo]
  exact (isAlgCurvatureForm_curvatureTensorFourAt D p).add_three z t w₁ w₂ v

theorem curvatureRieszEndo_smul_w (D : RiemannianConnection I g) (p : M)
    (c : ℝ) (w v : TangentSpace I p) :
    curvatureRieszEndo D p (c • w) v = c • curvatureRieszEndo D p w v := by
  ext z
  refine ((g.metricInner_eq_iff_eq p _ _).mp fun t => ?_)
  rw [metricInner_curvatureRieszEndo]
  show _ = g.metricInner p (c • curvatureRieszEndo D p w v z) t
  rw [g.metricInner_smul_left, metricInner_curvatureRieszEndo]
  exact (isAlgCurvatureForm_curvatureTensorFourAt D p).smul_three c z t w v

/-- Linearity of `C_{w,v}` in `v` (fourth slot of `R`). -/
theorem curvatureRieszEndo_add_v (D : RiemannianConnection I g) (p : M)
    (w v₁ v₂ : TangentSpace I p) :
    curvatureRieszEndo D p w (v₁ + v₂)
      = curvatureRieszEndo D p w v₁ + curvatureRieszEndo D p w v₂ := by
  ext z
  refine ((g.metricInner_eq_iff_eq p _ _).mp fun t => ?_)
  rw [metricInner_curvatureRieszEndo]
  show _ = g.metricInner p (curvatureRieszEndo D p w v₁ z
    + curvatureRieszEndo D p w v₂ z) t
  rw [g.metricInner_add_left, metricInner_curvatureRieszEndo,
    metricInner_curvatureRieszEndo]
  exact (isAlgCurvatureForm_curvatureTensorFourAt D p).add_four z t w v₁ v₂

theorem curvatureRieszEndo_smul_v (D : RiemannianConnection I g) (p : M)
    (c : ℝ) (w v : TangentSpace I p) :
    curvatureRieszEndo D p w (c • v) = c • curvatureRieszEndo D p w v := by
  ext z
  refine ((g.metricInner_eq_iff_eq p _ _).mp fun t => ?_)
  rw [metricInner_curvatureRieszEndo]
  show _ = g.metricInner p (c • curvatureRieszEndo D p w v z) t
  rw [g.metricInner_smul_left, metricInner_curvatureRieszEndo]
  exact (isAlgCurvatureForm_curvatureTensorFourAt D p).smul_four c z t w v

/-- Antisymmetry `C_{w,v} = −C_{v,w}` (skew-symmetry of `R` in its last
pair). -/
theorem curvatureRieszEndo_antisymm (D : RiemannianConnection I g) (p : M)
    (w v : TangentSpace I p) :
    curvatureRieszEndo D p w v = -curvatureRieszEndo D p v w := by
  ext z
  refine ((g.metricInner_eq_iff_eq p _ _).mp fun t => ?_)
  rw [metricInner_curvatureRieszEndo]
  show _ = g.metricInner p (-(curvatureRieszEndo D p v w z)) t
  rw [g.metricInner_neg_left, metricInner_curvatureRieszEndo]
  exact (isAlgCurvatureForm_curvatureTensorFourAt D p).antisymm₃₄ z t w v

/-- The functional `w ↦ −½·tr(A ∘ C_{w,v})` defining `𝔯(A)(v)`. -/
def curvatureOperatorFunctional (D : RiemannianConnection I g) (p : M)
    (A : Module.End ℝ (TangentSpace I p)) (v : TangentSpace I p) :
    TangentSpace I p →ₗ[ℝ] ℝ where
  toFun w := -(1 / 2 : ℝ)
    * LinearMap.trace ℝ (TangentSpace I p) (A * curvatureRieszEndo D p w v)
  map_add' w₁ w₂ := by
    rw [curvatureRieszEndo_add_w, mul_add, map_add]
    ring
  map_smul' c w := by
    rw [RingHom.id_apply, curvatureRieszEndo_smul_w, mul_smul_comm, map_smul,
      smul_eq_mul]
    ring

@[simp]
theorem curvatureOperatorFunctional_apply (D : RiemannianConnection I g)
    (p : M) (A : Module.End ℝ (TangentSpace I p)) (v w : TangentSpace I p) :
    curvatureOperatorFunctional D p A v w
      = -(1 / 2 : ℝ)
        * LinearMap.trace ℝ (TangentSpace I p) (A * curvatureRieszEndo D p w v) := rfl

/-- **Math.** The **curvature operator** `𝔯 : Λ²T_pM → Λ²T_pM`
(Petersen §3.1.2): the unique self-adjoint operator on bivectors with
`g(𝔯(Σᵢ xᵢ∧yᵢ), Σⱼ vⱼ∧wⱼ) = Σᵢⱼ R(xᵢ,yᵢ,wⱼ,vⱼ)` (note the reversal of the
last two arguments). In the skew-endomorphism model it is defined
basis-free by `g(𝔯(A)(v), w) = −½·tr(A ∘ C_{w,v})`, where
`g(C_{w,v}(z), t) = R(z,t,w,v)`; the defining property on wedges is
`bivectorEndoInner_curvatureOperator_wedge_wedge`, self-adjointness is
`curvatureOperator_isSelfAdjoint`, and uniqueness is
`curvatureOperator_unique`. -/
def curvatureOperator (D : RiemannianConnection I g) (p : M)
    (A : Module.End ℝ (TangentSpace I p)) : Module.End ℝ (TangentSpace I p) where
  toFun v := metricRieszOfLinear g p (curvatureOperatorFunctional D p A v)
  map_add' v₁ v₂ := by
    refine (metricRieszOfLinear_unique g p fun w => ?_).symm
    rw [g.metricInner_add_left, metricInner_metricRieszOfLinear,
      metricInner_metricRieszOfLinear]
    simp only [curvatureOperatorFunctional_apply]
    rw [curvatureRieszEndo_add_v, mul_add, map_add]
    ring
  map_smul' c v := by
    refine (metricRieszOfLinear_unique g p fun w => ?_).symm
    rw [RingHom.id_apply, g.metricInner_smul_left, metricInner_metricRieszOfLinear]
    simp only [curvatureOperatorFunctional_apply]
    rw [curvatureRieszEndo_smul_v, mul_smul_comm, map_smul, smul_eq_mul]
    ring

/-- The defining trace formula for `𝔯`. -/
theorem metricInner_curvatureOperator_apply (D : RiemannianConnection I g)
    (p : M) (A : Module.End ℝ (TangentSpace I p)) (v w : TangentSpace I p) :
    g.metricInner p (curvatureOperator D p A v) w
      = -(1 / 2 : ℝ)
        * LinearMap.trace ℝ (TangentSpace I p) (A * curvatureRieszEndo D p w v) := by
  show g.metricInner p (metricRieszOfLinear g p _) w = _
  rw [metricInner_metricRieszOfLinear, curvatureOperatorFunctional_apply]

/-- **Math.** The defining property of the curvature operator on wedges
(Petersen §3.1.2): `g(𝔯(x∧y)(v), w) = R(x,y,w,v)`. -/
theorem metricInner_curvatureOperator_wedge (D : RiemannianConnection I g)
    (p : M) (x y v w : TangentSpace I p) :
    g.metricInner p (curvatureOperator D p (wedgeEndo g p x y) v) w
      = curvatureTensorFourAt D p x y w v := by
  rw [metricInner_curvatureOperator_apply, LinearMap.trace_mul_comm,
    mul_wedgeEndo, map_sub, LinearMap.trace_smulRight, LinearMap.trace_smulRight]
  simp only [RiemannianMetric.metricBilin_apply]
  rw [g.metricInner_comm p x (curvatureRieszEndo D p w v y),
    g.metricInner_comm p y (curvatureRieszEndo D p w v x),
    metricInner_curvatureRieszEndo, metricInner_curvatureRieszEndo]
  have h := (isAlgCurvatureForm_curvatureTensorFourAt D p).antisymm₁₂ y x w v
  rw [h]
  ring

/-- **Math.** The values of `𝔯` are skew: `𝔯` maps `Λ²T_pM` to itself. -/
theorem isSkewAt_curvatureOperator (D : RiemannianConnection I g) (p : M)
    (A : Module.End ℝ (TangentSpace I p)) :
    IsSkewAt g p (curvatureOperator D p A) := by
  intro v w
  rw [metricInner_curvatureOperator_apply,
    g.metricInner_comm p v (curvatureOperator D p A w),
    metricInner_curvatureOperator_apply,
    curvatureRieszEndo_antisymm D p w v, mul_neg, map_neg]
  ring

/-- **Math.** The **curvature operator's defining property** in inner-product
form (Petersen §3.1.2, `def:pet-ch3-curvature-operator`):
`g(𝔯(x∧y), v∧w) = R(x,y,w,v)`. -/
theorem bivectorEndoInner_curvatureOperator_wedge_wedge
    (D : RiemannianConnection I g) (p : M) (x y v w : TangentSpace I p) :
    bivectorEndoInner g p (curvatureOperator D p (wedgeEndo g p x y))
        (wedgeEndo g p v w)
      = curvatureTensorFourAt D p x y w v := by
  rw [bivectorEndoInner_wedgeEndo_right g p (isSkewAt_curvatureOperator D p _) v w,
    metricInner_curvatureOperator_wedge]

/-- `𝔯` packaged as a linear operator. -/
def curvatureOperatorLinear (D : RiemannianConnection I g) (p : M) :
    Module.End ℝ (TangentSpace I p) →ₗ[ℝ] Module.End ℝ (TangentSpace I p) where
  toFun := curvatureOperator D p
  map_add' A B := by
    ext v
    refine ((g.metricInner_eq_iff_eq p _ _).mp fun w => ?_)
    rw [metricInner_curvatureOperator_apply]
    show _ = g.metricInner p (curvatureOperator D p A v
      + curvatureOperator D p B v) w
    rw [g.metricInner_add_left, metricInner_curvatureOperator_apply,
      metricInner_curvatureOperator_apply, add_mul, map_add]
    ring
  map_smul' c A := by
    ext v
    refine ((g.metricInner_eq_iff_eq p _ _).mp fun w => ?_)
    rw [metricInner_curvatureOperator_apply]
    show _ = g.metricInner p (c • curvatureOperator D p A v) w
    rw [g.metricInner_smul_left, metricInner_curvatureOperator_apply,
      smul_mul_assoc, map_smul, smul_eq_mul]
    ring

@[simp]
theorem curvatureOperatorLinear_apply (D : RiemannianConnection I g) (p : M)
    (A : Module.End ℝ (TangentSpace I p)) :
    curvatureOperatorLinear D p A = curvatureOperator D p A := rfl

theorem curvatureOperator_sum (D : RiemannianConnection I g) (p : M)
    {ι : Type*} (s : Finset ι) (f : ι → Module.End ℝ (TangentSpace I p)) :
    curvatureOperator D p (∑ i ∈ s, f i)
      = ∑ i ∈ s, curvatureOperator D p (f i) := by
  rw [← curvatureOperatorLinear_apply, map_sum]
  simp only [curvatureOperatorLinear_apply]

theorem curvatureOperator_smul (D : RiemannianConnection I g) (p : M)
    (c : ℝ) (A : Module.End ℝ (TangentSpace I p)) :
    curvatureOperator D p (c • A) = c • curvatureOperator D p A := by
  rw [← curvatureOperatorLinear_apply, map_smul, curvatureOperatorLinear_apply]

/-- **Math.** The defining property on finite sums of wedges — Petersen's
display `g(𝔯(Σᵢ Xᵢ∧Yᵢ), Σⱼ Vⱼ∧Wⱼ) = Σᵢⱼ R(Xᵢ,Yᵢ,Wⱼ,Vⱼ)` (§3.1.2). -/
theorem bivectorEndoInner_curvatureOperator_sum_wedges
    (D : RiemannianConnection I g) (p : M)
    {ι κ : Type*} (s : Finset ι) (t : Finset κ)
    (x y : ι → TangentSpace I p) (v w : κ → TangentSpace I p) :
    bivectorEndoInner g p
        (curvatureOperator D p (∑ i ∈ s, wedgeEndo g p (x i) (y i)))
        (∑ j ∈ t, wedgeEndo g p (v j) (w j))
      = ∑ i ∈ s, ∑ j ∈ t, curvatureTensorFourAt D p (x i) (y i) (w j) (v j) := by
  rw [curvatureOperator_sum, bivectorEndoInner_sum_left]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bivectorEndoInner_sum_right]
  exact Finset.sum_congr rfl fun j _ =>
    bivectorEndoInner_curvatureOperator_wedge_wedge D p (x i) (y i) (v j) (w j)

/-! ## Expansion of skew endomorphisms in wedges -/

/-- **Math.** In a `g`-orthonormal basis `b`, every skew endomorphism is a sum
of wedges: `A = ½·Σᵢⱼ g(A(bᵢ), bⱼ)·(bᵢ∧bⱼ)` — the identification
`Λ²T_pM ≅ 𝔰𝔬(T_pM)` is onto. -/
theorem IsSkewAt.eq_sum_wedgeEndo {p : M}
    {A : Module.End ℝ (TangentSpace I p)} (hA : IsSkewAt g p A)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    A = (1 / 2 : ℝ) • ∑ i, ∑ j,
      g.metricInner p (A (b i)) (b j) • wedgeEndo g p (b i) (b j) := by
  classical
  -- a vector `g`-orthogonal to every basis vector vanishes
  have expand : ∀ u : TangentSpace I p,
      (∀ j, g.metricInner p u (b j) = 0) → u = 0 := by
    intro u hu
    have h0 : (g.metricBilin p u : TangentSpace I p →ₗ[ℝ] ℝ) = 0 :=
      b.ext fun j => by simpa using hu j
    refine (g.metricInner_eq_iff_eq p u 0).mp fun z => ?_
    have hz : g.metricBilin p u z = (0 : TangentSpace I p →ₗ[ℝ] ℝ) z := by
      rw [h0]
    simpa [g.metricInner_zero_left] using hz
  -- both sides agree on every basis vector
  refine b.ext fun k => ?_
  refine sub_eq_zero.mp (expand _ fun l => ?_)
  rw [g.metricInner_sub_left]
  -- evaluate the wedge sum on `b k`, then pair against `b l`
  have happ : ((1 / 2 : ℝ) • ∑ i, ∑ j,
      g.metricInner p (A (b i)) (b j) • wedgeEndo g p (b i) (b j)) (b k)
      = (1 / 2 : ℝ) • ∑ i, ∑ j, g.metricInner p (A (b i)) (b j)
          • (g.metricInner p (b i) (b k) • b j
            - g.metricInner p (b j) (b k) • b i) := by
    simp only [LinearMap.smul_apply, LinearMap.sum_apply, wedgeEndo_apply,
      bivectorSkewMap]
  rw [happ, g.metricInner_smul_left, metricInner_finsetSum_left]
  have hterm : ∀ i, g.metricInner p
      ((∑ j, g.metricInner p (A (b i)) (b j)
        • (g.metricInner p (b i) (b k) • b j
          - g.metricInner p (b j) (b k) • b i)) : TangentSpace I p) (b l)
      = ∑ j, g.metricInner p (A (b i)) (b j)
          * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
            - (if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0)) := by
    intro i
    rw [metricInner_finsetSum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [g.metricInner_smul_left, g.metricInner_sub_left,
      g.metricInner_smul_left, g.metricInner_smul_left, hb j l, hb i l,
      hb i k, hb j k]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- reduce the Kronecker double sum
  have hs : (∑ i, ∑ j, g.metricInner p (A (b i)) (b j)
      * ((if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
        - (if j = k then (1 : ℝ) else 0) * (if i = l then (1 : ℝ) else 0)))
      = g.metricInner p (A (b k)) (b l) - g.metricInner p (A (b l)) (b k) := by
    simp [mul_sub, Finset.sum_sub_distrib, mul_ite, ite_mul, mul_one,
      mul_zero, one_mul, zero_mul, Finset.sum_ite_eq']
  rw [hs]
  have hskew := hA (b l) (b k)
  rw [g.metricInner_comm p (b l) (A (b k))] at hskew
  rw [hskew]
  ring

/-! ## Self-adjointness and uniqueness -/

/-- **Math.** The curvature operator is **self-adjoint** on `Λ²T_pM`
(Petersen §3.1.2): `⟨𝔯(A), B⟩ = ⟨A, 𝔯(B)⟩` for skew `A, B`. The proof
expands `A` and `B` in wedges of a `g`-orthonormal basis and reduces to the
pair-swap symmetry `R(x,y,w,v) = R(w,v,x,y)` of Prop. 3.1.1. -/
theorem curvatureOperator_isSelfAdjoint (D : RiemannianConnection I g) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    {A B : Module.End ℝ (TangentSpace I p)}
    (hA : IsSkewAt g p A) (hB : IsSkewAt g p B) :
    bivectorEndoInner g p (curvatureOperator D p A) B
      = bivectorEndoInner g p A (curvatureOperator D p B) := by
  classical
  -- the two expressions agree on wedge pairs, by pair-swap symmetry
  have key : ∀ x y v w : TangentSpace I p,
      bivectorEndoInner g p (curvatureOperator D p (wedgeEndo g p x y))
          (wedgeEndo g p v w)
        = bivectorEndoInner g p (wedgeEndo g p x y)
            (curvatureOperator D p (wedgeEndo g p v w)) := by
    intro x y v w
    rw [bivectorEndoInner_curvatureOperator_wedge_wedge,
      bivectorEndoInner_comm,
      bivectorEndoInner_curvatureOperator_wedge_wedge]
    have h1 := (isAlgCurvatureForm_curvatureTensorFourAt D p).pairSwap v w y x
    have h2 := (isAlgCurvatureForm_curvatureTensorFourAt D p).antisymm₁₂ y x v w
    have h3 := (isAlgCurvatureForm_curvatureTensorFourAt D p).antisymm₃₄ x y v w
    rw [h1]
    linarith [h2, h3]
  -- expand both arguments in wedges and push linearity through
  rw [hA.eq_sum_wedgeEndo b hb, hB.eq_sum_wedgeEndo b hb]
  simp only [curvatureOperator_sum, curvatureOperator_smul,
    bivectorEndoInner_sum_left, bivectorEndoInner_sum_right,
    bivectorEndoInner_smul_left, bivectorEndoInner_smul_right,
    Finset.mul_sum, key]

/-- **Math.** **Uniqueness** (Petersen §3.1.2): any linear operator `L` on
endomorphisms whose values are skew and which satisfies the defining property
`⟨L(x∧y), v∧w⟩ = R(x,y,w,v)` on wedges agrees with the curvature operator on
every skew endomorphism, i.e. on all of `Λ²T_pM`. -/
theorem curvatureOperator_unique (D : RiemannianConnection I g) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (L : Module.End ℝ (TangentSpace I p) →ₗ[ℝ] Module.End ℝ (TangentSpace I p))
    (hLskew : ∀ A, IsSkewAt g p A → IsSkewAt g p (L A))
    (hL : ∀ x y v w : TangentSpace I p,
      bivectorEndoInner g p (L (wedgeEndo g p x y)) (wedgeEndo g p v w)
        = curvatureTensorFourAt D p x y w v)
    {A : Module.End ℝ (TangentSpace I p)} (hA : IsSkewAt g p A) :
    L A = curvatureOperator D p A := by
  classical
  -- on wedges: L(x∧y) and 𝔯(x∧y) are skew with the same wedge pairings
  have wedge_eq : ∀ x y : TangentSpace I p,
      L (wedgeEndo g p x y) = curvatureOperator D p (wedgeEndo g p x y) := by
    intro x y
    have hLw : IsSkewAt g p (L (wedgeEndo g p x y)) :=
      hLskew _ (isSkewAt_wedgeEndo g p x y)
    ext v
    refine ((g.metricInner_eq_iff_eq p _ _).mp fun w => ?_)
    have h1 : g.metricInner p (L (wedgeEndo g p x y) v) w
        = curvatureTensorFourAt D p x y w v := by
      rw [← bivectorEndoInner_wedgeEndo_right g p hLw v w, hL]
    rw [h1, ← metricInner_curvatureOperator_wedge D p x y v w]
  -- expand A in wedges
  rw [hA.eq_sum_wedgeEndo b hb]
  simp only [map_smul, map_sum, curvatureOperator_smul, curvatureOperator_sum,
    wedge_eq]

end PetersenLib

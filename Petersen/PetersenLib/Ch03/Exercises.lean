import PetersenLib.Ch03.AlgebraicCurvatureForm
import PetersenLib.Ch03.ContractedBianchi
import PetersenLib.Ch03.CurvatureCovariantDerivativeFour
import PetersenLib.Ch03.RicciCovariantDerivative
import PetersenLib.Ch03.GramFrame
import PetersenLib.Ch03.ConstantOfZeroDifferential
import PetersenLib.Ch03.RadialCurvature
import PetersenLib.Ch03.RiemannConstantCurvature
import PetersenLib.Ch04.BiinvariantMetrics

/-!
# Petersen Ch. 3, §3.4 — Exercises (tractable subset)

A tractable subset of the §3.4 exercises.

* **Exercise 3.4.7** (`exercise3_4_7`): a Riemannian manifold with **parallel
  Ricci tensor** has **constant scalar curvature**. Via the contracted Bianchi
  identity `d(scal) = −2·∇*Ric` (Prop. 3.1.5): if `∇Ric = 0` then `∇*Ric = 0`,
  so `d(scal) ≡ 0`, and a function with vanishing differential on a connected
  manifold is constant.
* **Exercise 3.4.23** (`kulkarniNomizuProduct`, `kulkarniNomizuProduct_comm`,
  `exercise3_4_23`): the **Kulkarni–Nomizu product** `h ⊛ k` of two symmetric
  `(0,2)`-forms is commutative and, when both factors are symmetric, is an
  algebraic curvature form (properties (1)–(3) of Prop. 3.1.1).
* **Exercise 3.4.32** (`exercise3_4_32`): the curvature of a **biinvariant
  metric** at the Lie-algebra level — `∇_X Y = ½[X,Y]` (Koszul),
  `R(X,Y)Z = ¼[Z,[X,Y]]`, `R(X,Y,Z,W) = −¼⟪[X,Y],[Z,W]⟫`, and nonnegative
  sectional curvature — packaged from the reusable biinvariant-curvature layer
  `PetersenLib.Ch04.BiinvariantMetrics` in Petersen's sign convention.
* **Exercise 3.4.24** (`schoutenForm`, `schoutenForm_trace`, `exercise3_4_24`):
  the **Schouten tensor** `P = 2/(n-2)·Ric − scal/((n-1)(n-2))·g` for `n > 2`.
  Its trace is `tr P = scal/(n-1)` (`schoutenForm_trace`), whence part (1):
  `P ≡ 0 ⟹ Ric = 0` (`exercise3_4_24`), via the abstract Ricci/scalar
  contraction of an `IsAlgCurvatureForm` (`ricciForm`, `scalarCurvature`).
  Part (6) — the Ricci-recovery contraction `Ric(X,Y)=Σᵢ(P⊛g)(X,Eᵢ,Eᵢ,Y)` — is
  `exercise3_4_24_ricci_recovery`, via the Kulkarni–Nomizu Ricci contraction
  (`kulkarniNomizu_inner_contraction`); parts (2)–(5) are deferred.
* **Exercise 3.4.25** (`weylForm`, `exercise3_4_25`): the **Weyl tensor** `W`, the
  trace-free part of the curvature; part (2), `Σᵢ W(X,Eᵢ,Eᵢ,Y) = 0`, via the
  Ricci recovery formula.
* **Exercise 3.4.16** (`einsteinForm`, `exercise3_4_16`): the **Einstein tensor**
  `G = Ric − ½·scal·g + c·g`; part (3), `G ≡ 0 ⟹ Ric = (scal/n)·g` (Einstein)
  for `n > 2`, by a trace argument.
* **Exercise 3.4.34** (`exercise3_4_34`): the structure constants
  `cᵏᵢⱼ = ⟪[Eᵢ,Eⱼ],Eₖ⟫` of a **biinvariant metric** are totally antisymmetric.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.4.
-/

open Bundle Set Function Finset Filter
open Module (finrank)
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open Riemannian

/-- Petersen's own algebraic-curvature-form predicate (`PetersenLib.IsAlgCurvatureForm`,
Ch. 3 §3.1) has the same defining fields as the shared `Riemannian.IsAlgCurvatureForm`.
On an inner product space this converts a Petersen form to the shared one, so it can
feed the shared inner-product curvature contractions (`ricciForm`, `scalarCurvature`, …). -/
def IsAlgCurvatureForm.toR {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) : Riemannian.IsAlgCurvatureForm B :=
  ⟨hB.add_left, hB.smul_left, hB.antisymm₁₂, hB.antisymm₃₄, hB.bianchi⟩

/-! ## Exercise 3.4.23 — the Kulkarni–Nomizu product -/

section KulkarniNomizu

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- **Math.** Petersen §3.4, Exercise 3.4.23: the **Kulkarni–Nomizu product**
`h ⊛ k` of two symmetric `(0,2)`-tensors `h, k`, the `(0,4)`-form
`h ⊛ k(v₁,v₂,v₃,v₄) = ½(h(v₁,v₄)k(v₂,v₃) + h(v₂,v₃)k(v₁,v₄))
  − ½(h(v₁,v₃)k(v₂,v₄) + h(v₂,v₄)k(v₁,v₃))`.
Here `h, k : LinearMap.BilinForm ℝ V` are bilinear forms standing in for the
`(0,2)`-tensors. -/
def kulkarniNomizuProduct (h k : LinearMap.BilinForm ℝ V) (v₁ v₂ v₃ v₄ : V) : ℝ :=
  (h v₁ v₄ * k v₂ v₃ + h v₂ v₃ * k v₁ v₄) / 2
    - (h v₁ v₃ * k v₂ v₄ + h v₂ v₄ * k v₁ v₃) / 2

/-- **Math.** Petersen §3.4, Exercise 3.4.23 (1): the Kulkarni–Nomizu product is
**commutative**, `h ⊛ k = k ⊛ h`. Immediate from commutativity of `ℝ`
multiplication; no symmetry of `h, k` is needed. -/
theorem kulkarniNomizuProduct_comm (h k : LinearMap.BilinForm ℝ V)
    (v₁ v₂ v₃ v₄ : V) :
    kulkarniNomizuProduct h k v₁ v₂ v₃ v₄ = kulkarniNomizuProduct k h v₁ v₂ v₃ v₄ := by
  simp only [kulkarniNomizuProduct]; ring

/-- **Math.** Petersen §3.4, Exercise 3.4.23 (4): the **Kulkarni–Nomizu product**
`h ⊛ k` of two *symmetric* `(0,2)`-forms satisfies properties (1)–(3) of
Prop. 3.1.1, i.e. is an **algebraic curvature form**. Multilinearity and the two
pair-antisymmetries hold for any bilinear `h, k`; the first Bianchi identity is
where symmetry of `h` and `k` is used (the twelve product terms cancel in pairs
after symmetrizing the indices). -/
theorem exercise3_4_23 (h k : LinearMap.BilinForm ℝ V)
    (hh : ∀ a b, h a b = h b a) (hk : ∀ a b, k a b = k b a) :
    IsAlgCurvatureForm (fun v₁ v₂ v₃ v₄ => kulkarniNomizuProduct h k v₁ v₂ v₃ v₄) where
  add_left x₁ x₂ y z t := by
    simp only [kulkarniNomizuProduct, map_add, LinearMap.add_apply]; ring
  smul_left a x y z t := by
    simp only [kulkarniNomizuProduct, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  antisymm₁₂ x y z t := by simp only [kulkarniNomizuProduct]; ring
  antisymm₃₄ x y z t := by simp only [kulkarniNomizuProduct]; ring
  bianchi x y z t := by
    simp only [kulkarniNomizuProduct]
    rw [hh y x, hh z x, hh z y, hk y x, hk z x, hk z y]
    ring

end KulkarniNomizu

/-! ## Kulkarni–Nomizu Ricci contraction (infrastructure for Ex 3.4.24(6), 3.4.25)

Contracting a Kulkarni–Nomizu product `h ⊛ g` against the metric `g = ⟪·,·⟫`
recovers `h` up to a trace term. This is the algebraic engine behind the
Ricci-recovery formula (Ex 3.4.24(6)) and the trace-free Weyl decomposition
(Ex 3.4.25). -/

section KulkarniNomizuContraction

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Frame reproduction.** A bilinear form recovers its value from an
orthonormal frame in its second slot: `h x y = ∑ᵢ ⟪Eᵢ, y⟫ · h x Eᵢ` (expand
`y = ∑ᵢ ⟪Eᵢ, y⟫ Eᵢ` and use linearity of `h x`). -/
theorem bilin_eq_sum_inner_mul_right (h : LinearMap.BilinForm ℝ V)
    (e : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V) (x y : V) :
    h x y = ∑ i, ⟪e i, y⟫ * h x (e i) := by
  conv_lhs => rw [← e.sum_repr y, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, e.repr_apply_apply]

/-- **Frame reproduction (first slot).** `h x y = ∑ᵢ ⟪Eᵢ, x⟫ · h Eᵢ y`. -/
theorem bilin_eq_sum_inner_mul_left (h : LinearMap.BilinForm ℝ V)
    (e : OrthonormalBasis (Fin (finrank ℝ V)) ℝ V) (x y : V) :
    h x y = ∑ i, ⟪e i, x⟫ * h (e i) y := by
  conv_lhs => rw [← e.sum_repr x, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, e.repr_apply_apply]

/-- **Math.** The **Kulkarni–Nomizu Ricci contraction**: for a bilinear form `h`
on an `n`-dimensional inner product space and the metric `g = ⟪·,·⟫` (as the
bilinear form `innerₗ V`), contracting the second and fourth slots of `h ⊛ g`
against an orthonormal frame gives
`∑ᵢ (h ⊛ g)(x, Eᵢ, y, Eᵢ) = −((n−2)/2)·h(x,y) − ½·tr(h)·⟪x,y⟫`.
The two "diagonal" terms contribute `n·h(x,y)` and `tr(h)·⟪x,y⟫`; the two
"cross" terms each reproduce `h(x,y)` by frame reproduction. -/
theorem kulkarniNomizu_inner_contraction (h : LinearMap.BilinForm ℝ V) (x y : V) :
    ∑ i, kulkarniNomizuProduct h (innerₗ V) x (stdOrthonormalBasis ℝ V i) y
        (stdOrthonormalBasis ℝ V i)
      = -(((finrank ℝ V : ℝ) - 2) / 2) * h x y - 2⁻¹ * bilinTrace h * ⟪x, y⟫ := by
  set e := stdOrthonormalBasis ℝ V with he
  have hS1 : ∑ i, h x (e i) * ⟪e i, y⟫ = h x y := by
    rw [bilin_eq_sum_inner_mul_right h e x y]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hS2 : ∑ i, h (e i) y * ⟪x, e i⟫ = h x y := by
    rw [bilin_eq_sum_inner_mul_left h e x y]
    exact Finset.sum_congr rfl fun i _ => by rw [real_inner_comm x (e i), mul_comm]
  have hcard : (∑ i, (⟪e i, e i⟫ : ℝ)) = (finrank ℝ V : ℝ) := by
    have h1 : ∀ i, (⟪e i, e i⟫ : ℝ) = 1 := fun i => by
      have h := orthonormal_iff_ite.mp e.orthonormal i i
      rwa [if_pos rfl] at h
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hC : ∑ i, h x y * ⟪e i, e i⟫ = h x y * (finrank ℝ V : ℝ) := by
    rw [← Finset.mul_sum, hcard]
  have hD : ∑ i, h (e i) (e i) * ⟪x, y⟫ = bilinTrace h * ⟪x, y⟫ := by
    rw [← Finset.sum_mul, ← bilinTrace_eq_sum h e]
  have hexp : ∀ i, kulkarniNomizuProduct h (innerₗ V) x (e i) y (e i)
      = (h x (e i) * ⟪e i, y⟫ + h (e i) y * ⟪x, e i⟫) / 2
        - (h x y * ⟪e i, e i⟫ + h (e i) (e i) * ⟪x, y⟫) / 2 := fun i => by
    simp only [kulkarniNomizuProduct, innerₗ_apply_apply]
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_sub_distrib,
    ← Finset.sum_div, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib,
    hS1, hS2, hC, hD]
  ring

end KulkarniNomizuContraction

/-! ## Exercise 3.4.7 — parallel Ricci tensor ⟹ constant scalar curvature -/

section ParallelRicci

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-- **Math.** Petersen §3.4, Exercise 3.4.7: a Riemannian manifold with
**parallel Ricci tensor** (`∇Ric = 0`) has **constant scalar curvature**. By the
contracted Bianchi identity `d(scal) = −2·∇*Ric` (Prop. 3.1.5), a vanishing
covariant derivative of `Ric` makes `∇*Ric = 0`, hence `d(scal) ≡ 0`; on a
(pre)connected manifold this forces `scal` to be constant. (The converse fails,
and a metric with parallel curvature tensor need not be Einstein.) -/
theorem exercise3_4_7 [PreconnectedSpace M] (D : RiemannianConnection I g)
    (hpar : ∀ (p : M) (v x y : TangentSpace I p),
      covariantDerivativeTwoTensorAt D.toAffineConnection
        (fun q => RicciCurvature D.toAffineConnection q) p v x y = 0)
    (x y : M) :
    scalarCurvature D x = scalarCurvature D y := by
  refine apply_eq_of_mfderiv_eq_zero
    ((contMDiff_scalarCurvature D).mdifferentiable (by simp)) (fun p => ?_) x y
  refine ContinuousLinearMap.ext fun w => ?_
  have hdiv : divergenceAdjoint D
      (fun q => RicciCurvature D.toAffineConnection q) p w = 0 := by
    simp only [divergenceAdjoint, neg_eq_zero]
    exact Finset.sum_eq_zero fun i _ => hpar p _ _ _
  have hb := contractedBianchiIdentity D p w
  rw [hdiv, mul_zero] at hb
  rw [ContinuousLinearMap.zero_apply]
  exact hb

end ParallelRicci

/-! ## Exercise 3.4.5 — both Bianchi identities at a point -/

section BianchiAtPoint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-- **Math.** Petersen §3.4, Exercise 3.4.5: **both Bianchi identities** hold at
every point of a Riemannian manifold — the first (algebraic) Bianchi identity
`R(X,Y)Z + R(Z,X)Y + R(Y,Z)X = 0`, and the second (differential) Bianchi identity
`(∇_X R)(Y,Z)W + (∇_Y R)(Z,X)W + (∇_Z R)(X,Y)W = 0`. Petersen's exercise proves
these at a point via a coordinate system with `∇_{∂ᵢ}∂ⱼ = 0` at `p`; here they are
the `curvatureTensor_firstBianchi` / `curvatureTensor_secondBianchi` components of
the curvature symmetries (`prop:pet-ch3-curvature-symmetries`), which hold
coordinate-freely and hence at every point. -/
theorem exercise3_4_5 (D : RiemannianConnection I g)
    {X Y Z W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (hW : IsSmoothVectorField W) (p : M) :
    (curvatureTensor D.toAffineConnection X Y Z p
        + curvatureTensor D.toAffineConnection Z X Y p
        + curvatureTensor D.toAffineConnection Y Z X p = 0)
      ∧ (covariantDerivativeCurvature D.toAffineConnection X Y Z W p
        + covariantDerivativeCurvature D.toAffineConnection Y Z X W p
        + covariantDerivativeCurvature D.toAffineConnection Z X Y W p = 0) :=
  ⟨curvatureTensor_firstBianchi D hX hY hZ p,
    curvatureTensor_secondBianchi D hX hY hZ hW p⟩

end BianchiAtPoint

/-! ## Exercise 3.4.8 — the contracted second Bianchi identity for `R` -/

section ContractedSecondBianchi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-- **Math.** The **divergence adjoint of the `(0,4)`-curvature tensor**,
`(∇^*R)(A,B,C) = −∑ᵢ (∇_{Eᵢ}R)(Eᵢ,A,B,C)`, contracting the differentiation
direction with the first slot of `R` against a `g`-orthonormal frame `Eᵢ`
of `T_pM` (the `(0,4)` case of `notation:pet-ch3-divergence-adjoint`,
independent of the frame for tensorial `R`). -/
noncomputable def divergenceAdjointCurvatureFour (D : RiemannianConnection I g)
    (A B C : Π x : M, TangentSpace I x) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩;
  -∑ i, covariantDerivativeCurvatureFour D
    (⇑(extendTangentVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)))
    (⇑(extendTangentVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)))
    A B C p

/-- **Math.** Petersen §3.4, Exercise 3.4.8: the **once-contracted second Bianchi
identity** for the full `(0,4)`-curvature tensor,
`(∇^*R)(Z,X,Y) = (∇_X Ric)(Y,Z) − (∇_Y Ric)(X,Z)`. Contract the differential
Bianchi identity `(∇_{Eᵢ}R)(Eᵢ,Z,X,Y) + (∇_{Eᵢ}R)(Z,Eᵢ,X,Y) + (∇_Z R)(Eᵢ,Eᵢ,X,Y)`
against an orthonormal frame: the third term vanishes by antisymmetry of `R` in
its first pair, and a second application of the Bianchi identity together with
the trace formula `(∇_X Ric)(Y,Z) = ∑ᵢ (∇_X R)(Eᵢ,Y,Z,Eᵢ)`
(`covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour`) reassembles
the two Ricci-derivative terms. In particular `∇^*R = 0` whenever `∇Ric = 0`. -/
theorem exercise3_4_8 (D : RiemannianConnection I g)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    divergenceAdjointCurvatureFour D Z X Y p
      = covariantDerivativeRicci D X Y Z p - covariantDerivativeRicci D Y X Z p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  set F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x :=
    fun i => ⇑(extendTangentVector p (e i)) with hFdef
  have hF : ∀ i, IsSmoothVectorField (F i) :=
    fun i => (extendTangentVector p (e i)).smooth
  have hFp : ∀ i, F i p = e i := fun i => extendTangentVector_apply p (e i)
  have horth : ∀ i j, g.metricInner p (F i p) (F j p)
      = if i = j then 1 else 0 := by
    intro i j
    rw [hFp i, hFp j]
    exact orthonormal_iff_ite.mp e.orthonormal i j
  have hdiv : divergenceAdjointCurvatureFour D Z X Y p
      = -∑ i, covariantDerivativeCurvatureFour D (F i) (F i) Z X Y p := rfl
  -- termwise: `(∇_{Eᵢ}R)(Eᵢ,Z,X,Y) = -(∇_X R)(Eᵢ,Y,Z,Eᵢ) + (∇_Y R)(Eᵢ,X,Z,Eᵢ)`.
  have hterm : ∀ i, covariantDerivativeCurvatureFour D (F i) (F i) Z X Y p
      = - covariantDerivativeCurvatureFour D X (F i) Y Z (F i) p
        + covariantDerivativeCurvatureFour D Y (F i) X Z (F i) p := by
    intro i
    have hb1 := covariantDerivativeCurvatureFour_secondBianchi D (hF i) (hF i) hZ hX hY p
    have hz1 : covariantDerivativeCurvatureFour D Z (F i) (F i) X Y p = 0 := by
      have h := covariantDerivativeCurvatureFour_antisymm₁₂ (X := Z) D (hF i) (hF i) hX hY p
      linarith
    have hps := covariantDerivativeCurvatureFour_pairSwap D (hF i) hZ (hF i) hX hY p
    have hb2 := covariantDerivativeCurvatureFour_secondBianchi D (hF i) hX hY hZ (hF i) p
    have ha := covariantDerivativeCurvatureFour_antisymm₁₂ (X := X) D hY (hF i) hZ (hF i) p
    linarith [hb1, hz1, hps, hb2, ha]
  have hbrX := covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour
    D hF hX hY hZ horth
  have hbrY := covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour
    D hF hY hX hZ horth
  rw [hdiv, Finset.sum_congr rfl (fun i _ => hterm i), hbrX, hbrY,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end ContractedSecondBianchi

/-! ## Exercise 3.4.32 — curvature of a biinvariant metric -/

section BiinvariantLie

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {bracket : V →ₗ[ℝ] V →ₗ[ℝ] V}

/-- **Math.** Petersen §3.4, Exercise 3.4.32: the curvature of a **biinvariant
metric** on a Lie group `G`, computed at the level of the Lie algebra `𝔤`
(here a real inner-product space `V` with the bracket carried as an explicit
bilinear map, to avoid the `AddCommGroup` diamond between `LieRing` and
`InnerProductSpace`; see `PetersenLib.Ch04.BiinvariantMetrics`). Hypotheses:
`hskew` = alternating bracket, `hjac` = Jacobi identity, `had` = each `ad x`
skew-adjoint (the infinitesimal biinvariance). The four claims are Petersen's:

1. **(1)** `∇_X Y = ½[X,Y]` is the Levi-Civita connection, i.e. it satisfies
   Koszul's formula `2⟪½[Y,X],Z⟫ = −⟪[X,Y],Z⟫ − ⟪[Y,Z],X⟫ + ⟪[Z,X],Y⟫` (for
   constant left-invariant fields the metric-derivative terms drop out);
2. **(2)** `R(X,Y)Z = ¼[Z,[X,Y]]` (a pure Jacobi-identity computation from the
   connection `∇_· · = ½[·,·]`);
3. **(3)** the `(0,4)`-curvature `R(X,Y,Z,W) = g(R(X,Y)Z,W) = −¼⟪[X,Y],[Z,W]⟫`
   (by invariance of the metric);
4. **(3′)** consequently the sectional curvatures are **nonnegative**,
   `R(X,Y,Y,X) = ¼‖[X,Y]‖² ≥ 0`.

(Parts (4)–(5) of Petersen's exercise — nonnegativity of the curvature operator
`𝔯` and `Ric(X,X) = 0 ⇔ X` central — require the bivector/orthonormal-frame
trace layer and are not part of this Lie-algebra-level packaging.) -/
theorem exercise3_4_32 (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) :
    (∀ x y z : V, 2 * ⟪(2⁻¹ : ℝ) • bracket y x, z⟫
        = -⟪bracket x y, z⟫ - ⟪bracket y z, x⟫ + ⟪bracket z x, y⟫) ∧
    (∀ x y z : V,
        (2⁻¹ : ℝ) • bracket x ((2⁻¹ : ℝ) • bracket y z)
          - (2⁻¹ : ℝ) • bracket y ((2⁻¹ : ℝ) • bracket x z)
          - (2⁻¹ : ℝ) • bracket (bracket x y) z
        = (4⁻¹ : ℝ) • bracket z (bracket x y)) ∧
    (∀ x y z t : V,
        ⟪(2⁻¹ : ℝ) • bracket x ((2⁻¹ : ℝ) • bracket y z)
          - (2⁻¹ : ℝ) • bracket y ((2⁻¹ : ℝ) • bracket x z)
          - (2⁻¹ : ℝ) • bracket (bracket x y) z, t⟫
        = -(4⁻¹ : ℝ) * ⟪bracket x y, bracket z t⟫) ∧
    (∀ x y : V, 0 ≤ ⟪bracket x y, bracket x y⟫) := by
  obtain ⟨koszul, curv, _form⟩ := biinvariantConnectionCurvature hskew hjac had
  refine ⟨koszul, fun x y z => ?_, fun x y z t => ?_, fun x y => real_inner_self_nonneg⟩
  · rw [curv x y z, bracket_skew hskew z (bracket x y)]; module
  · rw [curv x y z, real_inner_smul_left, inner_bracket_invariance hskew had (bracket x y) z t]

end BiinvariantLie

/-! ## Exercise 3.4.24 — the Schouten tensor -/

section Schouten

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Math.** Petersen §3.4, Exercise 3.4.24: the **Schouten tensor**
`P = 2/(n-2)·Ric − scal/((n-1)(n-2))·g` of an algebraic curvature form `B` on an
`n`-dimensional inner product space (`n = finrank ℝ V`), where `Ric = ricciForm`
and `scal = scalarCurvature` are the abstract Ricci and scalar contractions.
The formula is meaningful for `n > 2`. -/
def schoutenForm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (x y : V) : ℝ :=
  (2 / ((finrank ℝ V : ℝ) - 2)) * ricciForm hB.toR x y
    - Riemannian.scalarCurvature hB.toR / (((finrank ℝ V : ℝ) - 1) * ((finrank ℝ V : ℝ) - 2)) * ⟪x, y⟫

/-- **Math.** Petersen §3.4, Exercise 3.4.24: the **trace of the Schouten tensor**
is `tr P = scal/(n-1)`. In a `g`-orthonormal frame `Eᵢ`,
`∑ᵢ P(Eᵢ,Eᵢ) = 2/(n-2)·scal − scal·n/((n-1)(n-2)) = scal/(n-1)`, using
`∑ᵢ Ric(Eᵢ,Eᵢ) = scal` and `∑ᵢ g(Eᵢ,Eᵢ) = n`. -/
theorem schoutenForm_trace {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hn : 2 < finrank ℝ V) :
    ∑ i, schoutenForm hB (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i)
      = Riemannian.scalarCurvature hB.toR / ((finrank ℝ V : ℝ) - 1) := by
  set n : ℝ := (finrank ℝ V : ℝ) with hn_def
  have hn2 : (2 : ℝ) < n := by rw [hn_def]; exact_mod_cast hn
  have hne2 : n - 2 ≠ 0 := by linarith
  have hne1 : n - 1 ≠ 0 := by linarith
  set e := stdOrthonormalBasis ℝ V with he
  have hscal : Riemannian.scalarCurvature hB.toR = ∑ i, ricciForm hB.toR (e i) (e i) :=
    Riemannian.scalarCurvature_eq_sum_ricci hB.toR e
  have hcard : (∑ i, ⟪e i, e i⟫) = n := by
    have h1 : ∀ i, ⟪e i, e i⟫ = (1 : ℝ) := fun i => by
      have h := orthonormal_iff_ite.mp e.orthonormal i i
      rwa [if_pos rfl] at h
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hn_def]
  rw [show (∑ i, schoutenForm hB (e i) (e i))
      = (2 / (n - 2)) * (∑ i, ricciForm hB.toR (e i) (e i))
        - Riemannian.scalarCurvature hB.toR / ((n - 1) * (n - 2)) * (∑ i, ⟪e i, e i⟫) from by
    simp only [schoutenForm, Finset.sum_sub_distrib, ← Finset.mul_sum, hn_def]]
  rw [← hscal, hcard]
  field_simp
  ring

/-- **Math.** Petersen §3.4, Exercise 3.4.24 (1): for `n > 2`, if the **Schouten
tensor vanishes** (`P ≡ 0`) then the **Ricci tensor vanishes** (`Ric = 0`).
Tracing `P ≡ 0` gives `tr P = scal/(n-1) = 0`, so `scal = 0`; then `P ≡ 0`
reads `2/(n-2)·Ric = 0`, forcing `Ric = 0` since `2/(n-2) ≠ 0`. -/
theorem exercise3_4_24 {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hn : 2 < finrank ℝ V)
    (hP : ∀ x y, schoutenForm hB x y = 0) : ∀ x y, ricciForm hB.toR x y = 0 := by
  set n : ℝ := (finrank ℝ V : ℝ) with hn_def
  have hn2 : (2 : ℝ) < n := by rw [hn_def]; exact_mod_cast hn
  have hne2 : n - 2 ≠ 0 := by linarith
  have hne1 : n - 1 ≠ 0 := by linarith
  have htr : Riemannian.scalarCurvature hB.toR / (n - 1) = 0 := by
    rw [← schoutenForm_trace hB hn]
    exact Finset.sum_eq_zero fun i _ => hP _ _
  have hs : Riemannian.scalarCurvature hB.toR = 0 := by
    rcases div_eq_zero_iff.mp htr with h | h
    · exact h
    · exact absurd h hne1
  intro x y
  have hxy := hP x y
  rw [schoutenForm, hs] at hxy
  simp only [zero_div, zero_mul, sub_zero] at hxy
  have h2 : (2 / (n - 2)) ≠ 0 := div_ne_zero two_ne_zero hne2
  exact (mul_eq_zero.mp hxy).resolve_left h2

end Schouten

/-! ## Exercises 3.4.24(6) & 3.4.25 — Ricci recovery and the Weyl tensor -/

section Weyl

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The **Schouten tensor** `P = 2/(n-2)·Ric − scal/((n-1)(n-2))·g` packaged as a
bilinear form (so it can enter a Kulkarni–Nomizu product). Agrees with
`schoutenForm` (`schoutenBilin_apply`). -/
def schoutenBilin {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) :
    LinearMap.BilinForm ℝ V :=
  (2 / ((finrank ℝ V : ℝ) - 2)) • ricciBilin hB.toR
    - (Riemannian.scalarCurvature hB.toR / (((finrank ℝ V : ℝ) - 1) * ((finrank ℝ V : ℝ) - 2))) • innerₗ V

@[simp] theorem schoutenBilin_apply {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x y : V) : schoutenBilin hB x y = schoutenForm hB x y := by
  simp only [schoutenBilin, schoutenForm, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, ricciBilin_apply, innerₗ_apply_apply]

theorem bilinTrace_schoutenBilin {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hn : 2 < finrank ℝ V) :
    bilinTrace (schoutenBilin hB) = Riemannian.scalarCurvature hB.toR / ((finrank ℝ V : ℝ) - 1) := by
  rw [bilinTrace_eq_sum _ (stdOrthonormalBasis ℝ V)]
  simp only [schoutenBilin_apply]
  exact schoutenForm_trace hB hn

/-- Kulkarni–Nomizu Ricci contraction in the "middle" slot pattern:
`∑ᵢ (h ⊛ g)(x, Eᵢ, Eᵢ, y) = ((n−2)/2)·h(x,y) + ½·tr(h)·⟪x,y⟫`. Obtained from the
`(2,4)`-contraction by antisymmetry of `h ⊛ g` in its last pair. -/
theorem kulkarniNomizu_inner_contraction' (h : LinearMap.BilinForm ℝ V) (x y : V) :
    ∑ i, kulkarniNomizuProduct h (innerₗ V) x (stdOrthonormalBasis ℝ V i)
        (stdOrthonormalBasis ℝ V i) y
      = (((finrank ℝ V : ℝ) - 2) / 2) * h x y + 2⁻¹ * bilinTrace h * ⟪x, y⟫ := by
  have hswap : ∀ i, kulkarniNomizuProduct h (innerₗ V) x (stdOrthonormalBasis ℝ V i)
        (stdOrthonormalBasis ℝ V i) y
      = - kulkarniNomizuProduct h (innerₗ V) x (stdOrthonormalBasis ℝ V i) y
          (stdOrthonormalBasis ℝ V i) := fun i => by
    simp only [kulkarniNomizuProduct]; ring
  rw [Finset.sum_congr rfl (fun i _ => hswap i), Finset.sum_neg_distrib,
    kulkarniNomizu_inner_contraction]
  ring

/-- **Math.** Petersen §3.4, Exercise 3.4.24 (6): the **Ricci recovery formula**
`Ric(X,Y) = ∑ᵢ (P ⊛ g)(X, Eᵢ, Eᵢ, Y)`, contracting the Kulkarni–Nomizu product
of the Schouten tensor with the metric back to the Ricci tensor. Immediate from
the middle-slot contraction with `h = P` (whose trace is `scal/(n−1)`) and the
definition of `P`; needs `n > 2`. -/
theorem exercise3_4_24_ricci_recovery {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hn : 2 < finrank ℝ V) (x y : V) :
    ricciForm hB.toR x y
      = ∑ i, kulkarniNomizuProduct (schoutenBilin hB) (innerₗ V)
          x (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i) y := by
  rw [kulkarniNomizu_inner_contraction', bilinTrace_schoutenBilin hB hn, schoutenBilin_apply,
    schoutenForm]
  have hn2 : (2 : ℝ) < (finrank ℝ V : ℝ) := by exact_mod_cast hn
  have hne2 : (finrank ℝ V : ℝ) - 2 ≠ 0 := by linarith
  have hne1 : (finrank ℝ V : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- **Math.** Petersen §3.4, Exercise 3.4.25: the **Weyl tensor** `W`, the
trace-free part of the curvature in the orthogonal decomposition
`R = P ⊛ g + W`. Working in the do Carmo curvature-sign convention of the
abstract layer (where `ricciForm hB.toR x y = ∑ᵢ B x Eᵢ y Eᵢ`), the trace-free part
is `W = B + P ⊛ g`, matching Petersen's `R − P ⊛ g` after the overall
curvature-sign flip (cf. `biinvariantCurvatureForm`). -/
def weylForm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) :
    V → V → V → V → ℝ :=
  fun x y z t => B x y z t + kulkarniNomizuProduct (schoutenBilin hB) (innerₗ V) x y z t

/-- **Math.** Petersen §3.4, Exercise 3.4.25 (2): the **Weyl tensor is trace-free**,
`∑ᵢ W(X, Eᵢ, Eᵢ, Y) = 0` for any orthonormal frame `Eᵢ` (`n > 2`). The curvature
part contracts to `−Ric` (antisymmetry) and the `P ⊛ g` part to `+Ric`
(Ricci recovery, `exercise3_4_24_ricci_recovery`), so the two cancel. -/
theorem exercise3_4_25 {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hn : 2 < finrank ℝ V) (x y : V) :
    ∑ i, weylForm hB x (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i) y = 0 := by
  simp only [weylForm, Finset.sum_add_distrib]
  have hBcontract : ∑ i, B x (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i) y
      = - ricciForm hB.toR x y := by
    have hanti : ∀ i, B x (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V i) y
        = - B x (stdOrthonormalBasis ℝ V i) y (stdOrthonormalBasis ℝ V i) :=
      fun i => hB.antisymm₃₄ x _ _ y
    rw [Finset.sum_congr rfl (fun i _ => hanti i), Finset.sum_neg_distrib,
      ← ricciForm_eq_sum hB.toR x y (stdOrthonormalBasis ℝ V)]
  rw [hBcontract, ← exercise3_4_24_ricci_recovery hB hn]
  ring

end Weyl

/-! ## Exercise 3.4.16 — the Einstein tensor -/

section EinsteinTensor

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Math.** Petersen §3.4, Exercise 3.4.16: the **Einstein tensor**
`G(x,y) = Ric(x,y) − ½·scal·⟪x,y⟫ + c·⟪x,y⟫` of an algebraic curvature form `B`
on an inner product space, with cosmological constant `c` (the `(0,2)`-tensor
`T = Ric + b·scal·g + cg` at the divergence-free value `b = −½`). Here
`Ric = ricciForm` and `scal = scalarCurvature` are the abstract Ricci and
scalar contractions. -/
def einsteinForm {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (c : ℝ) (x y : V) : ℝ :=
  ricciForm hB.toR x y - (Riemannian.scalarCurvature hB.toR / 2) * ⟪x, y⟫ + c * ⟪x, y⟫

/-- **Math.** Petersen §3.4, Exercise 3.4.16 (3): for `n > 2`, if the **Einstein
tensor vanishes** (`G ≡ 0`) then the metric is **Einstein**,
`Ric = (scal/n)·g`. Tracing `Ric = (scal/2 − c)·g` in a `g`-orthonormal frame
gives `scal = (scal/2 − c)·n`, hence `scal/n = scal/2 − c`, and the pointwise
identity follows. -/
theorem exercise3_4_16 {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) (c : ℝ)
    (hn : 2 < finrank ℝ V) (hG : ∀ x y, einsteinForm hB c x y = 0) :
    ∀ x y, ricciForm hB.toR x y = (Riemannian.scalarCurvature hB.toR / (finrank ℝ V : ℝ)) * ⟪x, y⟫ := by
  set n : ℝ := (finrank ℝ V : ℝ) with hn_def
  set s : ℝ := Riemannian.scalarCurvature hB.toR with hs_def
  have hn0 : n ≠ 0 := by
    rw [hn_def]; exact_mod_cast (by omega : finrank ℝ V ≠ 0)
  set e := stdOrthonormalBasis ℝ V with he
  have hRic : ∀ x y, ricciForm hB.toR x y = (s / 2 - c) * ⟪x, y⟫ := fun x y => by
    have h := hG x y
    simp only [einsteinForm, ← hs_def] at h
    linear_combination h
  have hcard : (∑ i, (⟪e i, e i⟫ : ℝ)) = n := by
    have h1 : ∀ i, (⟪e i, e i⟫ : ℝ) = 1 := fun i => by
      have h := orthonormal_iff_ite.mp e.orthonormal i i
      rwa [if_pos rfl] at h
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, hn_def]
  have htr : s = (s / 2 - c) * n := by
    have hsum := Riemannian.scalarCurvature_eq_sum_ricci hB.toR e
    rw [← hs_def] at hsum
    conv_lhs => rw [hsum]
    rw [Finset.sum_congr rfl (fun i _ => hRic (e i) (e i)), ← Finset.mul_sum, hcard]
  intro x y
  rw [hRic x y, show s / n = s / 2 - c from by rw [div_eq_iff hn0]; linarith [htr]]

end EinsteinTensor

/-! ## Exercise 3.4.34 — structure constants of a biinvariant metric -/

section StructureConstants

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {bracket : V →ₗ[ℝ] V →ₗ[ℝ] V}

/-- **Math.** Petersen §3.4, Exercise 3.4.34: **cyclic invariance** of the
structure constants of a biinvariant metric, `⟪[x,y],z⟫ = ⟪[y,z],x⟫`. Immediate
from invariance of the metric `⟪[x,y],z⟫ = ⟪x,[y,z]⟫` and symmetry of the inner
product. -/
theorem inner_bracket_cyclic (hskew : ∀ x : V, bracket x x = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) (x y z : V) :
    ⟪bracket x y, z⟫ = ⟪bracket y z, x⟫ := by
  rw [inner_bracket_invariance hskew had x y z, real_inner_comm]

/-- **Math.** Petersen §3.4, Exercise 3.4.34: for an orthonormal basis `Eᵢ` of the
Lie algebra of a group with a biinvariant metric, the structure constants
`cᵏᵢⱼ = ⟪[Eᵢ,Eⱼ],Eₖ⟫` are **totally antisymmetric** — `cᵏᵢⱼ = −cᵏⱼᵢ`
(skew-symmetry of the bracket) and `cᵏᵢⱼ = cⁱⱼₖ` (biinvariance), so
`⟪[Eᵢ,Eⱼ],Eₖ⟫` is alternating in `i, j, k`. -/
theorem exercise3_4_34 [FiniteDimensional ℝ V]
    (hskew : ∀ x : V, bracket x x = 0)
    (had : ∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫)
    (i j k : Fin (finrank ℝ V)) :
    (⟪bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j),
          stdOrthonormalBasis ℝ V k⟫
        = -⟪bracket (stdOrthonormalBasis ℝ V j) (stdOrthonormalBasis ℝ V i),
            stdOrthonormalBasis ℝ V k⟫) ∧
      (⟪bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j),
          stdOrthonormalBasis ℝ V k⟫
        = ⟪bracket (stdOrthonormalBasis ℝ V j) (stdOrthonormalBasis ℝ V k),
            stdOrthonormalBasis ℝ V i⟫) := by
  refine ⟨?_, inner_bracket_cyclic hskew had _ _ _⟩
  rw [bracket_skew hskew (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j),
    inner_neg_left]

end StructureConstants

/-! ## Exercise 3.4.29 — the polarization identity for an algebraic curvature form -/

section Polarization

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {B : V → V → V → V → ℝ}

/-- **Math.** Petersen §3.4, Exercise 3.4.29 (2): the **polarization identity**
`6·R(x,y,v,w) = …` recovering an algebraic curvature form from its diagonal
(sectional) values `R(a,b,b,a)`. Every summand on the right-hand side has the
diagonal shape `B a b b a`; expanding by multilinearity
(`add_left`/`add_two`/`add_three`/`add_four`) collapses the identity to a small
linear combination that the antisymmetries, pair-swap symmetry, and first Bianchi
identity close. -/
theorem exercise3_4_29 (hB : IsAlgCurvatureForm B) (x y v w : V) :
    6 * B x y v w =
      B (x + w) (y + v) (y + v) (x + w) - B x (y + v) (y + v) x - B w (y + v) (y + v) w
      - B (x + w) v v (x + w) - B (x + w) y y (x + w) + B x v v x + B w v v w
      + B x y y x + B w y y w - B (x + v) (y + w) (y + w) (x + v)
      + B x (y + w) (y + w) x + B v (y + w) (y + w) v + B (x + v) y y (x + v)
      + B (x + v) w w (x + v)
      - B x y y x - B v y y v - B x w w x - B v w w v := by
  simp only [hB.add_left, hB.add_two, hB.add_three, hB.add_four]
  have e1 := hB.antisymm₃₄ x y v w
  have e2 := hB.pairSwap v w y x
  have e3 := hB.antisymm₁₂ y x v w
  have e4 := hB.pairSwap w v y x
  have e5 := hB.antisymm₃₄ y x v w
  have e6 := hB.bianchi x y v w
  have e7 := hB.pairSwap y v x w
  have e8 := hB.antisymm₁₂ v x y w
  have e9 := hB.bianchi v y w x
  have e10 := hB.antisymm₁₂ w y v x
  linarith [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10]

end Polarization

/-! ## Exercise 3.4.10 — constant curvature at a point vs. `R(v,w)z = 0` on
orthogonal triples -/

section ConstantCurvatureAtPoint

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- **Math.** Petersen §3.4, Exercise 3.4.10: `(M,g)` has **constant curvature**
at `p` — i.e. the algebraic curvature form `B` is a scalar multiple `k` of the
model form `g(x∧y,x∧y) = ⟪x,x⟫⟪y,y⟫ − ⟪x,y⟫²` on the diagonal — **iff**
`R(v,w)z = 0` (encoded via nondegeneracy of `g` as `B v w z t = 0` for all
`t`) whenever `v,w,z` are pairwise orthogonal.

`(⇒)`: `IsAlgCurvatureForm.eq_smul_bivectorPairing_of_const` upgrades the
diagonal identity to the full tensor identity `B = k·g(·∧·,·∧·)`; on a
pairwise-orthogonal triple `v,w,z` two of the four Gram factors of
`bivectorPairing` vanish, killing it for every `t`.

`(⇐)`, the hint's algebraic core (do Carmo Ch. 4, Exercise 4 / Petersen's
symmetric-bilinear-form lemma): fix an orthonormal basis `e`. For `a ≠ v`,
`b ≠ v`, `a ≠ b`, the vectors `e a + e b` and `e a − e b` are orthogonal to
each other and to `e v`, so the hypothesis applied to this triple — expanded
quadrilinearly and using that any 3-of-4 pairwise-orthogonal basis vectors
kill `B` regardless of the 4th argument — forces
`B(e v,e a,e a,e v) = B(e v,e b,e b,e v)`, i.e. the "sectional curvature"
`B(e v,e a,e v,e a)` is independent of `a` (`connect`). Chaining through two
fixed reference indices shows it is a single global constant `k'`
(`Sconst`), and a further case analysis (using the same pairwise-orthogonal
vanishing plus the algebraic symmetries) shows `B` agrees with
`k'·bivectorPairing` on every basis quadruple (`quad`), whence
`IsAlgCurvatureForm.ext_basis` gives the full tensor identity, in particular
the diagonal one. The degenerate case `finrank ℝ V ≤ 1` is handled directly:
any two vectors are then dependent, so both sides of the diagonal identity
vanish (with `k = 0`), without using the hypothesis at all. -/
theorem exercise3_4_10 {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B) :
    (∃ k : ℝ, ∀ x y : V, B x y x y = k * (⟪x, x⟫ * ⟪y, y⟫ - ⟪x, y⟫ ^ 2)) ↔
    (∀ v w z : V, ⟪v, w⟫ = 0 → ⟪v, z⟫ = 0 → ⟪w, z⟫ = 0 → ∀ t : V, B v w z t = 0) := by
  constructor
  · rintro ⟨k, hk⟩ v w z _hvw hvz hwz t
    have hG : ∀ a b : V, innerₗ V a b = innerₗ V b a := fun a b => real_inner_comm b a
    have hfull := hB.eq_smul_bivectorPairing_of_const (innerₗ V) hG k (by
      intro x y
      rw [hk x y]
      simp only [bivectorPairing, innerₗ_apply_apply]
      rw [real_inner_comm y x, sq])
    rw [hfull v w z t]
    simp only [bivectorPairing, innerₗ_apply_apply, hvz, hwz, zero_mul, mul_zero, sub_zero]
  · intro horth
    by_cases hn : 2 ≤ Module.finrank ℝ V
    · set n := Module.finrank ℝ V with hn_def
      set e := stdOrthonormalBasis ℝ V with he_def
      have hOB : ∀ i j : Fin n, ⟪e i, e j⟫ = if i = j then 1 else 0 :=
        fun i j => orthonormal_iff_ite.mp e.orthonormal i j
      have hG : ∀ a b : V, innerₗ V a b = innerₗ V b a := fun a b => real_inner_comm b a
      set G := innerₗ V with hG_def
      -- three pairwise-orthogonal basis vectors give a zero quadrilinear value for any 4th arg
      have H1 : ∀ p q r s : Fin n, p ≠ q → p ≠ r → q ≠ r →
          B (e p) (e q) (e r) (e s) = 0 := by
        intro p q r s hpq hpr hqr
        have hpq' : ⟪e p, e q⟫ = 0 := by rw [hOB]; simp [hpq]
        have hpr' : ⟪e p, e r⟫ = 0 := by rw [hOB]; simp [hpr]
        have hqr' : ⟪e q, e r⟫ = 0 := by rw [hOB]; simp [hqr]
        exact horth (e p) (e q) (e r) hpq' hpr' hqr' (e s)
      have H2 : ∀ p q r s : Fin n, p ≠ q → p ≠ r → q ≠ r →
          B (e p) (e q) (e s) (e r) = 0 := by
        intro p q r s hpq hpr hqr
        have h0 := H1 p q r s hpq hpr hqr
        have hswap := hB.antisymm₃₄ (e p) (e q) (e s) (e r)
        linarith [h0, hswap]
      -- the "same first vector" connecting identity, via `(e a + e b) ⊥ (e a - e b)`
      have connect : ∀ v a b : Fin n, a ≠ v → b ≠ v → a ≠ b →
          B (e v) (e a) (e v) (e a) = B (e v) (e b) (e v) (e b) := by
        intro v a b hav hbv hab
        have hva : ⟪e v, e a⟫ = 0 := by rw [hOB]; simp [Ne.symm hav]
        have hvb : ⟪e v, e b⟫ = 0 := by rw [hOB]; simp [Ne.symm hbv]
        have hab' : ⟪e a, e b⟫ = 0 := by rw [hOB]; simp [hab]
        have hz1 : ⟪e v, e a + e b⟫ = 0 := by
          rw [inner_add_right, hva, hvb, add_zero]
        have hz2 : ⟪e v, e a - e b⟫ = 0 := by
          rw [inner_sub_right, hva, hvb, sub_zero]
        have hz3 : ⟪e a + e b, e a - e b⟫ = 0 := by
          rw [inner_add_left, inner_sub_right, inner_sub_right, hab', hOB a a, hOB b a,
            hOB b b, if_pos rfl, if_pos rfl, if_neg (Ne.symm hab)]
          ring
        have h0 := horth (e v) (e a + e b) (e a - e b) hz1 hz2 hz3 (e v)
        have expand : B (e v) (e a + e b) (e a - e b) (e v)
            = B (e v) (e a) (e a) (e v) - B (e v) (e a) (e b) (e v)
              + B (e v) (e b) (e a) (e v) - B (e v) (e b) (e b) (e v) := by
          have hsub : e a - e b = e a + (-1 : ℝ) • e b := by rw [neg_one_smul]; abel
          rw [hsub, hB.add_two, hB.add_three, hB.add_three, hB.smul_three, hB.smul_three]
          ring
        rw [expand] at h0
        have hcross1 : B (e v) (e a) (e b) (e v) = 0 :=
          H1 v a b v (Ne.symm hav) (Ne.symm hbv) hab
        have hcross2 : B (e v) (e b) (e a) (e v) = 0 :=
          H1 v b a v (Ne.symm hbv) (Ne.symm hav) (Ne.symm hab)
        have hdiag : B (e v) (e a) (e a) (e v) = B (e v) (e b) (e b) (e v) := by
          linarith [h0, hcross1, hcross2]
        have hswapA := hB.antisymm₃₄ (e v) (e a) (e v) (e a)
        have hswapB := hB.antisymm₃₄ (e v) (e b) (e v) (e b)
        linarith [hdiag, hswapA, hswapB]
      -- the trivial swap `S(p,q) = S(q,p)`
      have swapS : ∀ p q : Fin n, p ≠ q →
          B (e p) (e q) (e p) (e q) = B (e q) (e p) (e q) (e p) := by
        intro p q _hpq
        have h1 := hB.antisymm₁₂ (e p) (e q) (e p) (e q)
        have h2 := hB.antisymm₃₄ (e q) (e p) (e p) (e q)
        linarith [h1, h2]
      have hi0 : (0 : ℕ) < n := by omega
      have hi1 : (1 : ℕ) < n := by omega
      set i0 : Fin n := ⟨0, hi0⟩ with hi0_def
      set i1 : Fin n := ⟨1, hi1⟩ with hi1_def
      have hi01 : i0 ≠ i1 := by
        intro h; simp [hi0_def, hi1_def, Fin.ext_iff] at h
      set k' : ℝ := B (e i0) (e i1) (e i0) (e i1) with hk'_def
      have Sconst : ∀ i j : Fin n, i ≠ j → B (e i) (e j) (e i) (e j) = k' := by
        intro i j hij
        rw [hk'_def]
        rcases eq_or_ne i i0 with hi | hi
        · subst hi
          rcases eq_or_ne j i1 with hj | hj
          · subst hj; rfl
          · exact connect i0 j i1 hij.symm hi01.symm hj
        · rcases eq_or_ne i i1 with hi' | hi'
          · subst hi'
            rcases eq_or_ne j i0 with hj | hj
            · subst hj
              exact (swapS i0 i1 hi01).symm
            · exact (connect i1 j i0 hij.symm hi01 hj).trans (swapS i1 i0 hi01.symm)
          · rcases eq_or_ne j i0 with hj | hj
            · subst hj
              rw [swapS i i0 hi, connect i0 i i1 hi hi01.symm hi']
            · rcases eq_or_ne j i1 with hj' | hj'
              · subst hj'
                rw [swapS i i1 hi', connect i1 i i0 hi' hi01 hi]
                exact (swapS i0 i1 hi01).symm
              · rw [connect i j i0 hij.symm hi.symm hj,
                  swapS i i0 hi, connect i0 i i1 hi hi01.symm hi']
      have hGOB : ∀ p q : Fin n, G (e p) (e q) = if p = q then (1 : ℝ) else 0 := by
        intro p q; rw [hG_def, innerₗ_apply_apply]; exact hOB p q
      have hRHS : ∀ i j k l : Fin n, bivectorPairing G (e i) (e j) (e k) (e l)
          = (if i = k then (1 : ℝ) else 0) * (if j = l then (1 : ℝ) else 0)
            - (if i = l then (1 : ℝ) else 0) * (if j = k then (1 : ℝ) else 0) := by
        intro i j k l; simp only [bivectorPairing, hGOB]
      have quad : ∀ i j k l : Fin n,
          B (e i) (e j) (e k) (e l) = k' * bivectorPairing G (e i) (e j) (e k) (e l) := by
        intro i j k l
        by_cases hij : i = j
        · subst hij
          rw [hB.self_left]
          have : bivectorPairing G (e i) (e i) (e k) (e l) = 0 := by
            simp only [bivectorPairing]; ring
          rw [this, mul_zero]
        by_cases hkl : k = l
        · subst hkl
          rw [hB.self_right]
          have : bivectorPairing G (e i) (e j) (e k) (e k) = 0 := by
            simp only [bivectorPairing]; ring
          rw [this, mul_zero]
        rw [hRHS]
        by_cases hki : k = i
        · rw [hki]
          have hil : i ≠ l := by have h := hkl; rw [hki] at h; exact h
          by_cases hjl : j = l
          · rw [hjl, Sconst i l hil, if_pos rfl, if_pos rfl, if_neg hil,
              if_neg (Ne.symm hil)]
            ring
          · rw [H2 i j l i hij hil hjl, if_pos rfl, if_neg hjl, if_neg hil]
            ring
        · by_cases hkj : k = j
          · rw [hkj]
            have hjl : j ≠ l := by have h := hkl; rw [hkj] at h; exact h
            by_cases hil : i = l
            · have hswap := hB.antisymm₃₄ (e i) (e j) (e i) (e j)
              have hSij := Sconst i j hij
              have hval : B (e i) (e j) (e j) (e l) = -k' := by
                rw [← hil]; linarith [hswap, hSij]
              rw [hval, if_neg hij, if_pos hil, if_pos rfl]
              ring
            · rw [H2 i j l j hij hil hjl, if_neg hij, if_neg hil]
              ring
          · rw [H1 i j k l hij (Ne.symm hki) (Ne.symm hkj), if_neg (Ne.symm hki),
              if_neg (Ne.symm hkj)]
            ring
      have hfullT := hB.ext_basis ((isAlgCurvatureForm_bivectorPairing G hG).smul k')
        e.toBasis (fun i j k l => quad i j k l)
      refine ⟨k', fun x y => ?_⟩
      have hxy := hfullT x y x y
      rw [hxy]
      simp only [bivectorPairing, hG_def, innerₗ_apply_apply]
      rw [real_inner_comm y x, sq]
    · -- `finrank ≤ 1`: any two vectors are dependent, so both sides vanish.
      have hle : Module.finrank ℝ V ≤ 1 := by omega
      obtain ⟨v0, hv0⟩ := finrank_le_one_iff.mp hle
      refine ⟨0, fun x y => ?_⟩
      obtain ⟨cx, hcx⟩ := hv0 x
      obtain ⟨cy, hcy⟩ := hv0 y
      subst hcx; subst hcy
      simp only [zero_mul]
      rw [hB.smul_left, hB.smul_two, hB.smul_three, hB.smul_four, hB.self_left]
      ring

end ConstantCurvatureAtPoint

/-! ## Exercise 3.4.15 — 3-manifold: diagonal curvature operator ⇒ diagonal Ricci -/

section ThreeManifoldRicci

private theorem finMkTwo (h : 2 < 3) : (⟨2, h⟩ : Fin 3) = 2 := rfl

/-- Helper: `B x y x y = B y x y x` (swapping the pair in a diagonal entry),
by combining `antisymm₁₂` and `antisymm₃₄`. -/
theorem IsAlgCurvatureForm.diag_swap {V : Type*} [AddCommGroup V] [Module ℝ V]
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (x y : V) : B x y x y = B y x y x := by
  have h1 := hB.antisymm₁₂ y x y x
  have h2 := hB.antisymm₃₄ x y y x
  linarith

/-- **Math.** Petersen §3.4, Exercise 3.4.15: if the curvature operator of a
3-manifold is diagonal in the bivector basis `e₀∧e₁, e₀∧e₂, e₁∧e₂` with
diagonal entries `α, β, γ` — i.e. `α = B(e₀,e₁,e₀,e₁)`, `β = B(e₁,e₂,e₁,e₂)`,
`γ = B(e₀,e₂,e₀,e₂)` are the sectional-curvature numerators on the
coordinate 2-planes (the area is `1` since `e₀,e₁,e₂` are orthonormal), and
`B(eᵢ,eⱼ,eₖ,eₗ) = 0` whenever `{i,j} ≠ {k,l}` as unordered pairs — then the
Ricci curvature is diagonal with `Ric(e₀,e₀) = α+γ`, `Ric(e₁,e₁) = α+β`,
`Ric(e₂,e₂) = β+γ`, and `Ric(eᵢ,eⱼ) = 0` for `i ≠ j`.

Proof: `Ric(x,x) = ∑ₖ B(x,eₖ,x,eₖ)` (`ricciForm_eq_sum`) already only involves
diagonal curvature-operator entries `B(eᵢ,eⱼ,eᵢ,eⱼ)` (via `self_left` on the
repeated term and `diag_swap` to reorder the other two), with *no* need for
the diagonal hypothesis; the off-diagonal vanishing genuinely uses it, killing
the one cross term `B(eᵢ,eₖ,eⱼ,eₖ)` (`k` the third index) via `hDiag`, while
the other two terms of the 3-term sum vanish by `self_left`/`self_right`.

(We use the `B(x,y,x,y)`-pattern for the sectional-curvature numerator rather
than the naively-symmetric `B(x,y,y,x)` pattern: with this codebase's algebraic
sign convention for `ricciForm` and `bivectorPairing` — the standard model of
constant curvature `1` — `B(x,y,x,y)` is the sign that makes `Ric = (n-1)·k·g`
positive for positive curvature, and is exactly the diagonal entry
`⟨R(eᵢ∧eⱼ),eᵢ∧eⱼ⟩` of the curvature operator on bivectors, matching the
exercise's "curvature operator in diagonal form" framing.) -/
theorem exercise3_4_15 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (e : OrthonormalBasis (Fin 3) ℝ V)
    {B : V → V → V → V → ℝ} (hB : IsAlgCurvatureForm B)
    (hDiag : ∀ i j k l : Fin 3, ({i, j} : Finset (Fin 3)) ≠ {k, l} →
      B (e i) (e j) (e k) (e l) = 0)
    (α β γ : ℝ) (hα : α = B (e 0) (e 1) (e 0) (e 1)) (hβ : β = B (e 1) (e 2) (e 1) (e 2))
    (hγ : γ = B (e 0) (e 2) (e 0) (e 2)) :
    ricciForm hB.toR (e 0) (e 0) = α + γ ∧
    ricciForm hB.toR (e 1) (e 1) = α + β ∧
    ricciForm hB.toR (e 2) (e 2) = β + γ ∧
    ∀ i j : Fin 3, i ≠ j → ricciForm hB.toR (e i) (e j) = 0 := by
  subst hα hβ hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ricciForm_eq_sum hB.toR (e 0) (e 0) e, Fin.sum_univ_three]
    have h0 := hB.self_left (e 0) (e 0) (e 0)
    rw [h0]; ring
  · rw [ricciForm_eq_sum hB.toR (e 1) (e 1) e, Fin.sum_univ_three]
    have h0 := hB.self_left (e 1) (e 1) (e 1)
    have hswap := hB.diag_swap (e 0) (e 1)
    rw [h0, ← hswap]; ring
  · rw [ricciForm_eq_sum hB.toR (e 2) (e 2) e, Fin.sum_univ_three]
    have h0 := hB.self_left (e 2) (e 2) (e 2)
    have hswap1 := hB.diag_swap (e 0) (e 2)
    have hswap2 := hB.diag_swap (e 1) (e 2)
    rw [h0, ← hswap1, ← hswap2]; ring
  · intro i j hij
    rw [ricciForm_eq_sum hB.toR (e i) (e j) e, Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.mk_zero, Fin.mk_one, finMkTwo] at hij ⊢ <;>
      first
        | exact absurd rfl hij
        | (rw [hB.self_left (e 0) (e 1) (e 0), hB.self_right (e 0) (e 1) (e 1),
            hDiag 0 2 1 2 (by decide)]; ring)
        | (rw [hB.self_left (e 0) (e 2) (e 0), hB.self_right (e 0) (e 2) (e 2),
            hDiag 0 1 2 1 (by decide)]; ring)
        | (rw [hB.self_left (e 1) (e 0) (e 1), hB.self_right (e 1) (e 0) (e 0),
            hDiag 1 2 0 2 (by decide)]; ring)
        | (rw [hB.self_left (e 1) (e 2) (e 1), hB.self_right (e 1) (e 2) (e 2),
            hDiag 1 0 2 0 (by decide)]; ring)
        | (rw [hB.self_left (e 2) (e 0) (e 2), hB.self_right (e 2) (e 0) (e 0),
            hDiag 2 1 0 1 (by decide)]; ring)
        | (rw [hB.self_left (e 2) (e 1) (e 2), hB.self_right (e 2) (e 1) (e 1),
            hDiag 2 0 1 0 (by decide)]; ring)

end ThreeManifoldRicci

/-! ## Exercise 3.4.33 — Killing form: biinvariance and Ric = −¼K -/

section BiinvariantKilling

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable {bracket : V →ₗ[ℝ] V →ₗ[ℝ] V}

/-- The **Killing form** `K(x,y) = trace(ad x ∘ ad y)` of a Lie algebra `V` with
bracket `bracket`, where `ad x = bracket x : V →ₗ[ℝ] V`. -/
def bracketKillingForm (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y : V) : ℝ :=
  LinearMap.trace ℝ V (bracket x * bracket y)

/-- `ad_{[x,y]} = ad_x ∘ ad_y - ad_y ∘ ad_x`, i.e. `ad` is a Lie algebra
homomorphism into `End V`. Pointwise version, from the Jacobi identity. -/
theorem bracket_bracket_eq (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (x y z : V) :
    bracket (bracket x y) z = bracket x (bracket y z) - bracket y (bracket x z) := by
  have h := hjac x y z
  have h1 : bracket (bracket y z) x = -bracket x (bracket y z) := bracket_skew hskew _ _
  have h2 : bracket (bracket z x) y = bracket y (bracket x z) := by
    rw [bracket_skew hskew z x, map_neg, LinearMap.neg_apply,
      bracket_skew hskew (bracket x z) y, neg_neg]
  rw [h1, h2] at h
  linear_combination (norm := module) h

/-- `ad_{[x,y]} = ad_x * ad_y - ad_y * ad_x` as endomorphisms of `V`. -/
theorem adComp_sub (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (x y : V) :
    bracket (bracket x y) = bracket x * bracket y - bracket y * bracket x := by
  ext z
  rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply]
  exact bracket_bracket_eq hskew hjac x y z

/-- The Killing form is **symmetric**: `K(x,y) = K(y,x)`. -/
theorem bracketKillingForm_symm (x y : V) : bracketKillingForm bracket x y = bracketKillingForm bracket y x := by
  unfold bracketKillingForm
  exact LinearMap.trace_mul_comm ℝ (bracket x) (bracket y)

/-- The Killing form is **ad-invariant**: `K([x,y],z) = K(x,[y,z])`. -/
theorem bracketKillingForm_bracket_left (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (x y z : V) :
    bracketKillingForm bracket (bracket x y) z = bracketKillingForm bracket x (bracket y z) := by
  unfold bracketKillingForm
  have hcyc : LinearMap.trace ℝ V (bracket y * bracket x * bracket z)
      = LinearMap.trace ℝ V (bracket x * bracket z * bracket y) := by
    have h := LinearMap.trace_mul_comm ℝ (bracket y) (bracket x * bracket z)
    rwa [← mul_assoc] at h
  have heq : bracket x * bracket y * bracket z - bracket x * bracket z * bracket y
      = bracket x * bracket (bracket y z) := by
    rw [adComp_sub hskew hjac y z]; noncomm_ring
  calc LinearMap.trace ℝ V (bracket (bracket x y) * bracket z)
      = LinearMap.trace ℝ V ((bracket x * bracket y - bracket y * bracket x) * bracket z) := by
        rw [adComp_sub hskew hjac x y]
    _ = LinearMap.trace ℝ V (bracket x * bracket y * bracket z)
          - LinearMap.trace ℝ V (bracket y * bracket x * bracket z) := by rw [sub_mul, map_sub]
    _ = LinearMap.trace ℝ V (bracket x * bracket y * bracket z)
          - LinearMap.trace ℝ V (bracket x * bracket z * bracket y) := by rw [hcyc]
    _ = LinearMap.trace ℝ V (bracket x * bracket y * bracket z
          - bracket x * bracket z * bracket y) := (map_sub _ _ _).symm
    _ = LinearMap.trace ℝ V (bracket x * bracket (bracket y z)) := by rw [heq]

/-- The Killing form satisfies the **infinitesimal biinvariance identity**
(skew-adjointness of `ad`), the `had` hypothesis needed by the biinvariant
curvature layer, when packaged as `−K`: `K([x,y],z) = −K(y,[x,z])`. -/
theorem bracketKillingForm_ad_skew (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (x y z : V) :
    bracketKillingForm bracket (bracket x y) z = -bracketKillingForm bracket y (bracket x z) := by
  have h1 := bracketKillingForm_bracket_left hskew hjac y x z
  have h2 : bracketKillingForm bracket (bracket y x) z = -bracketKillingForm bracket (bracket x y) z := by
    unfold bracketKillingForm
    rw [bracket_skew hskew y x, map_neg, neg_mul, map_neg]
  rw [h1] at h2
  linarith

/-- **Exercise 3.4.33, part (1).** If the ambient inner product on `V` *is* minus
the Killing form (`⟪x,y⟫ = −K(x,y)`), then this metric is **biinvariant** in its
infinitesimal form: each `ad x` is skew-adjoint, `⟪[x,y],z⟫ = −⟪y,[x,z]⟫` — the
`had` hypothesis expected by `PetersenLib.Ch04.BiinvariantMetrics`. -/
theorem bracketKillingForm_had (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (hK : ∀ x y : V, ⟪x, y⟫ = -bracketKillingForm bracket x y) (x y z : V) :
    ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫ := by
  rw [hK, hK, bracketKillingForm_ad_skew hskew hjac x y z]

/-- **Exercise 3.4.33, part (2).** With the biinvariant metric `⟪x,y⟫ = −K(x,y)`,
the **Ricci curvature is `−¼` times the Killing form**: `Ric(x,y) = −¼K(x,y)`.
Via the orthonormal-basis formula for the Ricci form and the ad-invariance
identity `bracketKillingForm_had`, both `∑ᵢ⟪[x,eᵢ],[y,eᵢ]⟫` and `K(x,y)` reduce to the
same trace, related by a sign flip. -/
theorem ricciForm_biinvariant_eq_neg_quarter_bracketKillingForm
    (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (hK : ∀ x y : V, ⟪x, y⟫ = -bracketKillingForm bracket x y) (x y : V) :
    ricciForm (biinvariantCurvatureForm_isAlgCurvatureForm hskew hjac (bracketKillingForm_had hskew hjac hK))
        x y
      = -(1 / 4 : ℝ) * bracketKillingForm bracket x y := by
  set had := bracketKillingForm_had hskew hjac hK with hhad
  set hB := biinvariantCurvatureForm_isAlgCurvatureForm hskew hjac had with hhB
  set e := stdOrthonormalBasis ℝ V with he
  rw [ricciForm_eq_sum hB x y e]
  have hterm : ∀ i, biinvariantCurvatureForm bracket x (e i) y (e i)
      = (1 / 4 : ℝ) * ⟪bracket x (e i), bracket y (e i)⟫ := by
    intro i
    unfold biinvariantCurvatureForm
    rw [inner_bracket_invariance hskew had (bracket x (e i)) y (e i)]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Finset.mul_sum]
  have hsum : ∑ i, ⟪bracket x (e i), bracket y (e i)⟫ = -bracketKillingForm bracket x y := by
    have htrace : bracketKillingForm bracket x y = ∑ i, ⟪e i, bracket x (bracket y (e i))⟫ := by
      unfold bracketKillingForm
      rw [LinearMap.trace_eq_sum_inner (bracket x * bracket y) e]
      simp [Module.End.mul_apply]
    have hpt : ∀ i, ⟪e i, bracket x (bracket y (e i))⟫ = -⟪bracket x (e i), bracket y (e i)⟫ := by
      intro i
      rw [real_inner_comm, had x (bracket y (e i)) (e i), real_inner_comm (bracket y (e i))]
    rw [htrace, Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_neg_distrib, neg_neg]
  rw [hsum]
  ring

/-- **Exercise 3.4.33.** For a Lie group with nondegenerate Killing form `K`,
using `−K` as the left-invariant metric (hypothesis `hK : ⟪x,y⟫ = −K(x,y)`):

1. this metric is **biinvariant**, in infinitesimal form
   `⟪[x,y],z⟫ = −⟪y,[x,z]⟫` (each `ad x` skew-adjoint);
2. the **Ricci curvature is `Ric = −¼K`**.

Formalized at the Lie-algebra level, building on `exercise3_4_32`'s biinvariant
curvature layer and `inner_bracket_cyclic`/`exercise3_4_34`'s ad-invariance
computations, via the Killing form `bracketKillingForm bracket x y = trace(ad x ∘ ad y)`
and the abstract Ricci contraction `ricciForm`. -/
theorem exercise3_4_33 (hskew : ∀ x : V, bracket x x = 0)
    (hjac : ∀ x y z : V,
      bracket (bracket x y) z + bracket (bracket y z) x + bracket (bracket z x) y = 0)
    (hK : ∀ x y : V, ⟪x, y⟫ = -bracketKillingForm bracket x y) :
    (∀ x y z : V, ⟪bracket x y, z⟫ = -⟪y, bracket x z⟫) ∧
      ∀ x y : V,
        ricciForm (biinvariantCurvatureForm_isAlgCurvatureForm hskew hjac
              (bracketKillingForm_had hskew hjac hK)) x y
          = -(1 / 4 : ℝ) * bracketKillingForm bracket x y :=
  ⟨bracketKillingForm_had hskew hjac hK, ricciForm_biinvariant_eq_neg_quarter_bracketKillingForm hskew hjac hK⟩

end BiinvariantKilling


/-! ## Exercise 3.4.2 — `|∇f|` constant ⇔ `∇_{∇f}∇f = 0` -/

section GradientConstant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M]
  [T2Space M] [LocallyCompactSpace M] in
/-- Scratch: the directional derivative of `|∇f|²` equals `2 g(∇_{∇f}∇f, X)`. -/
theorem hessianGrad_eq (D : RiemannianConnection I g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hgradf : IsSmoothVectorField (gradient g f))
    (p : M) {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X) :
    directionalDerivative X
        (fun q => g.metricInner q (gradient g f q) (gradient g f q)) p
      = 2 * g.metricInner p (D.cov p (gradient g f p) (gradient g f)) (X p) := by
  have hcompat := D.metric_compat hgradf hgradf p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have h1 : g.metricInner p (D.cov p (X p) (gradient g f)) (gradient g f p)
      = hessianLieDerivative g f ![X, gradient g f] p :=
    (hessianLieDerivative_eq_metricInner_cov D hf hX hgradf hgradf p).symm
  have h2 : g.metricInner p (gradient g f p) (D.cov p (X p) (gradient g f))
      = hessianLieDerivative g f ![X, gradient g f] p := by
    rw [g.metricInner_comm]; exact h1
  rw [h1, h2] at hcompat
  have h3 : hessianLieDerivative g f ![X, gradient g f] p
      = hessianLieDerivative g f ![gradient g f, X] p :=
    hessianLieDerivative_symm D hf hX hgradf hgradf p
  have h4 : hessianLieDerivative g f ![gradient g f, X] p
      = g.metricInner p (D.cov p (gradient g f p) (gradient g f)) (X p) :=
    hessianLieDerivative_eq_metricInner_cov D hf hgradf hX hgradf p
  rw [h3, h4] at hcompat
  linarith [hcompat]

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [LocallyCompactSpace M] in
/-- **Math.** Petersen §3.4, Exercise 3.4.2, pointwise algebraic core: for
`f : (M, g) → ℝ` smooth with smooth gradient, `∇_{∇f}∇f = 0` at `p` iff the
differential of `|∇f|²` vanishes at `p`. -/
theorem exercise3_4_2 (D : RiemannianConnection I g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hgradf : IsSmoothVectorField (gradient g f))
    (p : M) :
    D.cov p (gradient g f p) (gradient g f) = 0 ↔
      mfderiv I 𝓘(ℝ) (fun q => g.metricInner q (gradient g f q) (gradient g f q)) p
        = 0 := by
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro w
    have hkey := hessianGrad_eq D hf hgradf p (extendTangentVector p w).smooth
    rw [extendTangentVector_apply, directionalDerivative_apply,
      extendTangentVector_apply, h] at hkey
    simpa using hkey
  · intro h
    have hzero : ∀ v : TangentSpace I p,
        g.metricInner p (D.cov p (gradient g f p) (gradient g f)) v = 0 := by
      intro v
      have hkey := hessianGrad_eq D hf hgradf p (extendTangentVector p v).smooth
      rw [extendTangentVector_apply, directionalDerivative_apply,
        extendTangentVector_apply] at hkey
      have h0 : mfderiv I 𝓘(ℝ)
          (fun q => g.metricInner q (gradient g f q) (gradient g f q)) p v = 0 := by
        rw [h, ContinuousLinearMap.zero_apply]
      rw [h0] at hkey
      have hX2 : 2 * g.metricInner p (D.cov p (gradient g f p) (gradient g f)) v = 0 :=
        hkey.symm
      exact (mul_eq_zero.mp hX2).resolve_left (by norm_num)
    by_contra hne
    have hpos := g.metricInner_self_pos p _ hne
    have hz := hzero (D.cov p (gradient g f p) (gradient g f))
    linarith

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [LocallyCompactSpace M] in
/-- **Math.** Petersen §3.4, Exercise 3.4.2, direction (1) ⇒ (2): if `|∇f|`
(equivalently `|∇f|²`) is constant on a preconnected manifold, then
`∇_{∇f}∇f = 0` everywhere. -/
theorem exercise3_4_2_of_constant [PreconnectedSpace M] (D : RiemannianConnection I g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hgradf : IsSmoothVectorField (gradient g f))
    (hconst : ∀ x y : M,
      g.metricInner x (gradient g f x) (gradient g f x)
        = g.metricInner y (gradient g f y) (gradient g f y)) (p : M) :
    D.cov p (gradient g f p) (gradient g f) = 0 := by
  apply (exercise3_4_2 D hf hgradf p).mpr
  have hFeq : (fun q => g.metricInner q (gradient g f q) (gradient g f q))
      = (fun _ : M => g.metricInner p (gradient g f p) (gradient g f p)) := by
    funext q; exact hconst q p
  rw [hFeq]
  exact mfderiv_const

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] [LocallyCompactSpace M] in
/-- **Math.** Petersen §3.4, Exercise 3.4.2, direction (2) ⇒ (1): if
`∇_{∇f}∇f = 0` everywhere on a preconnected manifold, then `|∇f|²` (hence
`|∇f|`) is constant. -/
theorem exercise3_4_2_to_constant [PreconnectedSpace M] (D : RiemannianConnection I g)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hgradf : IsSmoothVectorField (gradient g f))
    (hcov : ∀ p : M, D.cov p (gradient g f p) (gradient g f) = 0) (x y : M) :
    g.metricInner x (gradient g f x) (gradient g f x)
      = g.metricInner y (gradient g f y) (gradient g f y) := by
  have hsmooth : ContMDiff I 𝓘(ℝ) ∞
      (fun q => g.metricInner q (gradient g f q) (gradient g f q)) := by
    intro q
    exact contMDiffWithinAt_univ.mp
      (g.metricInner_contMDiffWithinAt (hgradf q).contMDiffWithinAt
        (hgradf q).contMDiffWithinAt)
  exact apply_eq_of_mfderiv_eq_zero (hsmooth.mdifferentiable (by simp))
    (fun p => (exercise3_4_2 D hf hgradf p).mp (hcov p)) x y

end GradientConstant

/-! ## Exercise 3.4.6 — constant curvature ⇒ parallel curvature tensor -/

section ConstantCurvatureParallel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-- The pointwise `(0,4)`-curvature tensor of a constant-curvature connection
equals `-k` times the bivector-inner-product model tensor. -/
theorem curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature
    (D : RiemannianConnection I g) (k : ℝ) (hD : HasConstantCurvature D k)
    {Y Z V U : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hV : IsSmoothVectorField V) (q : M) :
    curvatureTensorFour D Y Z V U q
      = -k * bivectorInnerProduct g q (Y q) (Z q) (V q) (U q) := by
  have hmodel := (hasConstantCurvature_iff_curvature_eq D k).mp hD q (Y q) (Z q) (V q)
  rw [curvatureTensorFour_apply, ← curvatureTensorAt_apply D.toAffineConnection hY hZ hV q,
    hmodel, g.metricInner_smul_left, bivectorSkewMap_metricInner]

/-- The Leibniz rule for the directional derivative of the bivector-inner-product
model `(0,4)`-tensor `g(Y,V)g(Z,U) − g(Y,U)g(Z,V)`, through metric compatibility
`∇g = 0`. -/
theorem directionalDerivative_bivectorInnerProduct
    (D : RiemannianConnection I g)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hV : IsSmoothVectorField V) (hU : IsSmoothVectorField U) (p : M) :
    directionalDerivative X (fun q => bivectorInnerProduct g q (Y q) (Z q) (V q) (U q)) p
      = bivectorInnerProduct g p (D.toAffineConnection.covField X Y p) (Z p) (V p) (U p)
        + bivectorInnerProduct g p (Y p) (D.toAffineConnection.covField X Z p) (V p) (U p)
        + bivectorInnerProduct g p (Y p) (Z p) (D.toAffineConnection.covField X V p) (U p)
        + bivectorInnerProduct g p (Y p) (Z p) (V p) (D.toAffineConnection.covField X U p) := by
  have hYp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Y y⟩ : TangentBundle I M)) p :=
    (hY p).mdifferentiableAt (by decide)
  have hZp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Z y⟩ : TangentBundle I M)) p :=
    (hZ p).mdifferentiableAt (by decide)
  have hVp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, V y⟩ : TangentBundle I M)) p :=
    (hV p).mdifferentiableAt (by decide)
  have hUp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, U y⟩ : TangentBundle I M)) p :=
    (hU p).mdifferentiableAt (by decide)
  have hda : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (Y q) (V q)) p :=
    Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hYp hVp
  have hdb : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (Z q) (U q)) p :=
    Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hZp hUp
  have hdc : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (Y q) (U q)) p :=
    Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hYp hUp
  have hdd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (Z q) (V q)) p :=
    Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hZp hVp
  have hfun : (fun q => bivectorInnerProduct g q (Y q) (Z q) (V q) (U q))
      = (fun q => g.metricInner q (Y q) (V q)) * (fun q => g.metricInner q (Z q) (U q))
        - (fun q => g.metricInner q (Y q) (U q)) * (fun q => g.metricInner q (Z q) (V q)) := by
    funext q; show bivectorInnerProduct g q (Y q) (Z q) (V q) (U q) = _
    simp [bivectorInnerProduct]
  rw [hfun, directionalDerivative_sub (hda.mul hdb) (hdc.mul hdd),
    directionalDerivative_mul hda hdb, directionalDerivative_mul hdc hdd]
  have compat_a : directionalDerivative X (fun q => g.metricInner q (Y q) (V q)) p
      = g.metricInner p (D.cov p (X p) Y) (V p) + g.metricInner p (Y p) (D.cov p (X p) V) := by
    rw [← dirTangent_eq_directionalDerivative]; exact D.metric_compat hY hV p (X p)
  have compat_b : directionalDerivative X (fun q => g.metricInner q (Z q) (U q)) p
      = g.metricInner p (D.cov p (X p) Z) (U p) + g.metricInner p (Z p) (D.cov p (X p) U) := by
    rw [← dirTangent_eq_directionalDerivative]; exact D.metric_compat hZ hU p (X p)
  have compat_c : directionalDerivative X (fun q => g.metricInner q (Y q) (U q)) p
      = g.metricInner p (D.cov p (X p) Y) (U p) + g.metricInner p (Y p) (D.cov p (X p) U) := by
    rw [← dirTangent_eq_directionalDerivative]; exact D.metric_compat hY hU p (X p)
  have compat_d : directionalDerivative X (fun q => g.metricInner q (Z q) (V q)) p
      = g.metricInner p (D.cov p (X p) Z) (V p) + g.metricInner p (Z p) (D.cov p (X p) V) := by
    rw [← dirTangent_eq_directionalDerivative]; exact D.metric_compat hZ hV p (X p)
  rw [compat_a, compat_b, compat_c, compat_d]
  simp only [bivectorInnerProduct, AffineConnection.covField_apply]
  ring

/-- **Math.** Petersen §3.4, Exercise 3.4.6: a Riemannian manifold with
**constant curvature** `k` has **parallel curvature tensor**, `∇R = 0`. Since
constant curvature forces `R = -k·(g ∧ g)` pointwise
(`curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature`, via
Riemann's equivalence `hasConstantCurvature_iff_curvature_eq`), and the model
`(0,4)`-tensor `g ∧ g` is parallel because `∇g = 0` (metric compatibility,
`directionalDerivative_bivectorInnerProduct`), the Leibniz-rule correction terms
in `∇R` cancel exactly against the derivative of `-k·(g∧g)`. -/
theorem exercise3_4_6 (D : RiemannianConnection I g) (k : ℝ) (hD : HasConstantCurvature D k)
    {X Y Z V U : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (hZ : IsSmoothVectorField Z)
    (hV : IsSmoothVectorField V) (hU : IsSmoothVectorField U) (p : M) :
    covariantDerivativeCurvatureFour D X Y Z V U p = 0 := by
  have hY1 : IsSmoothVectorField (D.toAffineConnection.covField X Y) := D.smooth_cov hX hY
  have hZ1 : IsSmoothVectorField (D.toAffineConnection.covField X Z) := D.smooth_cov hX hZ
  have hV1 : IsSmoothVectorField (D.toAffineConnection.covField X V) := D.smooth_cov hX hV
  have hfun : curvatureTensorFour D Y Z V U
      = fun q => -k * bivectorInnerProduct g q (Y q) (Z q) (V q) (U q) := by
    funext q
    exact curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature D k hD hY hZ hV q
  have hEq1 : curvatureTensorFour D (D.toAffineConnection.covField X Y) Z V U p
      = -k * bivectorInnerProduct g p (D.toAffineConnection.covField X Y p) (Z p) (V p) (U p) :=
    curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature D k hD hY1 hZ hV p
  have hEq2 : curvatureTensorFour D Y (D.toAffineConnection.covField X Z) V U p
      = -k * bivectorInnerProduct g p (Y p) (D.toAffineConnection.covField X Z p) (V p) (U p) :=
    curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature D k hD hY hZ1 hV p
  have hEq3 : curvatureTensorFour D Y Z (D.toAffineConnection.covField X V) U p
      = -k * bivectorInnerProduct g p (Y p) (Z p) (D.toAffineConnection.covField X V p) (U p) :=
    curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature D k hD hY hZ hV1 p
  have hda : MDifferentiableAt I 𝓘(ℝ)
      (fun q => bivectorInnerProduct g q (Y q) (Z q) (V q) (U q)) p := by
    have hYp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Y y⟩ : TangentBundle I M)) p :=
      (hY p).mdifferentiableAt (by decide)
    have hZp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Z y⟩ : TangentBundle I M)) p :=
      (hZ p).mdifferentiableAt (by decide)
    have hVp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, V y⟩ : TangentBundle I M)) p :=
      (hV p).mdifferentiableAt (by decide)
    have hUp : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, U y⟩ : TangentBundle I M)) p :=
      (hU p).mdifferentiableAt (by decide)
    exact (Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hYp hVp).mul
      (Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hZp hUp) |>.sub
      ((Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hYp hUp).mul
        (Riemannian.RiemannianMetric.metricInner_raw_mdifferentiableAt g hZp hVp))
  rw [covariantDerivativeCurvatureFour_apply, hfun,
    directionalDerivative_const_smul hda, hEq1, hEq2, hEq3,
    curvatureTensorFour_eq_bivectorInnerProduct_of_hasConstantCurvature D k hD hY hZ hV p,
    directionalDerivative_bivectorInnerProduct D hY hZ hV hU p]
  ring

end ConstantCurvatureParallel

/-! ## Exercise 3.4.19 — affine vector field: `∇²_{U,V}X = −R(X,U)V` -/

section AffineVectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {g : RiemannianMetric I M}

/-- Key bridging identity: for any Riemannian connection and any smooth vector
fields `X, U, V`, `(L_X ∇)(U,V) = R(X,U)V + ∇²_{U,V}X`. -/
theorem lieDerivativeConnection_eq_curvature_add_secondCovariantDerivativeField
    (D : RiemannianConnection I g)
    {X U V : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U) (hV : IsSmoothVectorField V)
    (p : M) :
    lieDerivativeConnection D.toAffineConnection X U V p
      = curvatureTensor D.toAffineConnection X U V p
        + secondCovariantDerivativeField D.toAffineConnection U V X p := by
  have hcovUV : IsSmoothVectorField (D.toAffineConnection.covField U V) :=
    D.toAffineConnection.smooth_cov hU hV
  have hstep1 : lieDerivativeVectorField I X (D.toAffineConnection.covField U V) p
      = D.toAffineConnection.cov p (X p) (D.toAffineConnection.covField U V)
        - D.toAffineConnection.cov p (D.toAffineConnection.covField U V p) X :=
    (D.torsion_free hX hcovUV p).symm
  have hcovXV : IsSmoothVectorField (D.toAffineConnection.covField X V) :=
    D.toAffineConnection.smooth_cov hX hV
  have hcovVX : IsSmoothVectorField (D.toAffineConnection.covField V X) :=
    D.toAffineConnection.smooth_cov hV hX
  have hXV : lieDerivativeVectorField I X V
      = D.toAffineConnection.covField X V - D.toAffineConnection.covField V X := by
    funext q
    exact (D.torsion_free hX hV q).symm
  have hUcov : D.toAffineConnection.cov p (U p) (lieDerivativeVectorField I X V)
      = D.toAffineConnection.cov p (U p) (D.toAffineConnection.covField X V)
        - D.toAffineConnection.cov p (U p) (D.toAffineConnection.covField V X) := by
    rw [hXV]
    exact D.toAffineConnection.sub_field p (U p) hcovXV hcovVX
  simp only [lieDerivativeConnection, curvatureTensor_apply, secondCovariantDerivativeField_apply]
  rw [hstep1, hUcov]
  module

/-- **Exercise 3.4.19.** An **affine vector field** `X` (one with `L_X ∇ = 0`)
satisfies `∇²_{U,V}X = −R(X,U)V`. -/
theorem exercise3_4_19 (D : RiemannianConnection I g)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    (hAffine : ∀ (U V : Π x : M, TangentSpace I x) (p : M),
      lieDerivativeConnection D.toAffineConnection X U V p = 0)
    {U V : Π x : M, TangentSpace I x} (hU : IsSmoothVectorField U) (hV : IsSmoothVectorField V)
    (p : M) :
    secondCovariantDerivativeField D.toAffineConnection U V X p
      = -curvatureTensor D.toAffineConnection X U V p := by
  have h := lieDerivativeConnection_eq_curvature_add_secondCovariantDerivativeField D hX hU hV p
  rw [hAffine U V p] at h
  linear_combination (norm := module) -h

end AffineVectorField


end PetersenLib

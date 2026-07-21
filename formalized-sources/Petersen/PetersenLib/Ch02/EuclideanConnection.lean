import PetersenLib.Ch01.RiemannianManifolds
import PetersenLib.Ch02.Connections
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Petersen Ch. 2, §2.2.1 — The covariant derivative on Euclidean space

The Euclidean-space nodes of Petersen §2.2.1, with the model space `E` (a real
normed, resp. inner product, space) regarded as a manifold over itself:

* `covariantDerivativeEuclidean` — the covariant derivative
  `∇_Y X = fderiv ℝ X · (Y ·)` on `E` (Cartesian differentiation of the
  coefficients), with its pointwise algebra: tensoriality in the direction
  (`covariantDerivativeEuclidean_add_left`,
  `covariantDerivativeEuclidean_smul_left`), the Leibniz rule in the
  differentiated field (`covariantDerivativeEuclidean_leibniz`), and the
  vanishing on constant fields (`covariantDerivativeEuclidean_const`).
* `covariantDerivativeEuclidean_sub_eq_bracket` — torsion-freeness
  `∇_X Y − ∇_Y X = [X, Y]` on `E`.
* `covariantDerivative_implicit_euclidean` — **Prop. 2.2.1**: the implicit
  metric formula `2 g(∇_Y X, Z) = (L_X g)(Y, Z) + (dθ_X)(Y, Z)` for the
  canonical inner-product metric on `E`.
* `killingField_euclidean_characterization` — the remark on Killing fields on
  `ℝⁿ`: `X` is Killing for the flat metric iff
  `⟪DX(v), w⟫ + ⟪v, DX(w)⟫ = 0` at every point (the basis-free form of
  `∂ᵢXʲ + ∂ⱼXⁱ = 0`).

## Design notes

* Vector fields are dependent functions `Π x : E, TangentSpace 𝓘(ℝ, E) x`,
  which are definitionally maps `E → E`, so `fderiv ℝ` applies directly.
* The bridge between the chart-level bracket `VectorField.mlieBracket` and the
  flat-space bracket `DY(X) − DX(Y)` is Mathlib's
  `VectorField.mlieBracketWithin_eq_lieBracketWithin`
  (`lieDerivativeVectorField_euclidean_apply`); the bridge between
  `IsSmoothVectorField` and `ContDiff` on the model space is Mathlib's
  `contMDiff_vectorSpace_iff_contDiff` (`isSmoothVectorField_iff_contDiff`).
* The remark `rem:pet-ch2-killing-field-euclidean` is formalized as the
  pointwise skew-adjointness characterization only; the classification
  `X = Ax + β` with `A` skew-symmetric (integrating the PDE) is not
  formalized here.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.1.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The covariant derivative on Euclidean space -/

/-- **Math.** The **covariant derivative on Euclidean space** (Petersen §2.2.1):
for vector fields on `E` (writing `X = Xⁱ∂ᵢ` in Cartesian coordinates),
`∇_Y X = (D_Y Xⁱ)∂ᵢ = dX(Y)`, i.e. the differential of `X : E → E` evaluated in
the direction `Y`. A vector field with constant coefficients has vanishing
covariant derivative. -/
def covariantDerivativeEuclidean (Y X : Π x : E, TangentSpace 𝓘(ℝ, E) x) (x : E) :
    TangentSpace 𝓘(ℝ, E) x :=
  fderiv ℝ X x (Y x)

@[simp]
theorem covariantDerivativeEuclidean_apply (Y X : Π x : E, TangentSpace 𝓘(ℝ, E) x)
    (x : E) : covariantDerivativeEuclidean Y X x = fderiv ℝ X x (Y x) := rfl

/-! ### Tensoriality in the direction -/

theorem covariantDerivativeEuclidean_add_left (Y Z X : Π x : E, TangentSpace 𝓘(ℝ, E) x)
    (x : E) :
    covariantDerivativeEuclidean (fun p => Y p + Z p) X x
      = covariantDerivativeEuclidean Y X x + covariantDerivativeEuclidean Z X x :=
  (fderiv ℝ X x).map_add (Y x) (Z x)

/-- `∇_{hY} X = h · ∇_Y X`: the covariant derivative is `C^∞(E)`-linear
(tensorial) in the direction. -/
theorem covariantDerivativeEuclidean_smul_left (h : E → ℝ)
    (Y X : Π x : E, TangentSpace 𝓘(ℝ, E) x) (x : E) :
    covariantDerivativeEuclidean (fun p => h p • Y p) X x
      = h x • covariantDerivativeEuclidean Y X x :=
  (fderiv ℝ X x).map_smul (h x) (Y x)

/-! ### Derivation property in the differentiated field -/

/-- **Math.** Leibniz rule for the Euclidean covariant derivative (Petersen
§2.2.1): `∇_Y (fX) = (D_Y f) X + f ∇_Y X`. -/
theorem covariantDerivativeEuclidean_leibniz {f : E → ℝ}
    {X : Π x : E, TangentSpace 𝓘(ℝ, E) x} {x : E}
    (hf : DifferentiableAt ℝ f x) (hX : DifferentiableAt ℝ X x)
    (Y : Π x : E, TangentSpace 𝓘(ℝ, E) x) :
    covariantDerivativeEuclidean Y (fun p => f p • X p) x
      = directionalDerivative Y f x • X x + f x • covariantDerivativeEuclidean Y X x := by
  have hdf : directionalDerivative Y f x = fderiv ℝ f x (Y x) := by
    rw [directionalDerivative_apply, mfderiv_eq_fderiv]
    rfl
  have hs := (hf.hasFDerivAt.smul hX.hasFDerivAt).fderiv
  refine (congrArg (fun L : E →L[ℝ] E => L (Y x)) hs).trans ?_
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, covariantDerivativeEuclidean_apply, hdf]
  exact add_comm _ _

/-- **Math.** A constant vector field has vanishing covariant derivative
(Petersen §2.2.1). -/
@[simp]
theorem covariantDerivativeEuclidean_const (Y : Π x : E, TangentSpace 𝓘(ℝ, E) x)
    (v : E) (x : E) :
    covariantDerivativeEuclidean Y (fun _ => v) x = 0 := by
  show fderiv ℝ (fun _ : E => v) x (Y x) = 0
  rw [fderiv_fun_const]
  rfl

/-! ## Smooth vector fields on the model space -/

/-- **Eng.** On the model space `E` over itself, a vector field is smooth in the
manifold sense (`IsSmoothVectorField`) iff it is `C^∞` as a map `E → E`. -/
theorem isSmoothVectorField_iff_contDiff {X : Π x : E, TangentSpace 𝓘(ℝ, E) x} :
    IsSmoothVectorField X ↔ ContDiff ℝ ∞ X :=
  contMDiff_vectorSpace_iff_contDiff

/-- Constant vector fields on `E` are smooth. -/
theorem isSmoothVectorField_const (v : E) :
    IsSmoothVectorField (I := 𝓘(ℝ, E)) (fun _ : E => v) :=
  isSmoothVectorField_iff_contDiff.2 contDiff_const

/-- A smooth vector field on the model space `E` is differentiable as a map
`E → E`. -/
theorem IsSmoothVectorField.differentiableAt {X : Π x : E, TangentSpace 𝓘(ℝ, E) x}
    (hX : IsSmoothVectorField X) (x : E) : DifferentiableAt ℝ X x :=
  ((isSmoothVectorField_iff_contDiff.1 hX).differentiable (by decide)).differentiableAt

/-! ## Torsion-freeness -/

/-- **Eng.** On the model space `E`, the Lie derivative of a vector field
(Mathlib's chart-level `VectorField.mlieBracket`) is the flat-space bracket
`[X, Y] = ∇_X Y − ∇_Y X = DY(X) − DX(Y)`. -/
theorem lieDerivativeVectorField_euclidean_apply
    (X Y : Π x : E, TangentSpace 𝓘(ℝ, E) x) (x : E) :
    lieDerivativeVectorField 𝓘(ℝ, E) X Y x
      = covariantDerivativeEuclidean X Y x - covariantDerivativeEuclidean Y X x := by
  rw [lieDerivativeVectorField_eq_mlieBracket, ← VectorField.mlieBracketWithin_univ,
    VectorField.mlieBracketWithin_eq_lieBracketWithin, VectorField.lieBracketWithin_univ]
  rfl

/-- **Math.** Torsion-freeness of the Euclidean covariant derivative (Petersen
§2.2.1): `∇_X Y − ∇_Y X = [X, Y] = L_X Y`. -/
theorem covariantDerivativeEuclidean_sub_eq_bracket
    (X Y : Π x : E, TangentSpace 𝓘(ℝ, E) x) (x : E) :
    covariantDerivativeEuclidean X Y x - covariantDerivativeEuclidean Y X x
      = lieDerivativeVectorField 𝓘(ℝ, E) X Y x :=
  (lieDerivativeVectorField_euclidean_apply X Y x).symm

/-! ## The implicit formula for the flat metric (Prop. 2.2.1) -/

section InnerProduct

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Eng.** Directional derivative of a metric pairing on Euclidean space: for
the canonical metric, `D_V ⟨Y, Z⟩ = ⟨Y, ∇_V Z⟩ + ⟨∇_V Y, Z⟩` (the flat metric is
parallel). -/
theorem directionalDerivative_metricInner_euclidean
    {Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F}
    (hY : DifferentiableAt ℝ Y x) (hZ : DifferentiableAt ℝ Z x)
    (V : Π x : F, TangentSpace 𝓘(ℝ, F) x) :
    directionalDerivative V
        (fun q => (innerProductSpaceMetric F).metricInner q (Y q) (Z q)) x
      = @inner ℝ F _ (Y x) (fderiv ℝ Z x (V x))
        + @inner ℝ F _ (fderiv ℝ Y x (V x)) (Z x) := by
  have hfun : (fun q => (innerProductSpaceMetric F).metricInner q (Y q) (Z q))
      = fun q => @inner ℝ F _ (Y q) (Z q) := by
    funext q
    exact innerProductSpaceMetric_apply F q (Y q) (Z q)
  rw [directionalDerivative_apply, mfderiv_eq_fderiv, hfun]
  exact fderiv_inner_apply ℝ hY hZ (V x)

/-- **Eng.** The Lie derivative of the flat metric, evaluated on two fields
differentiable at `x`:
`(L_X g)(Y₀, Y₁)|_x = ⟨DX(Y₀), Y₁⟩ + ⟨Y₀, DX(Y₁)⟩` — the coefficient-wise
symmetrized derivative of `X`. -/
theorem lieDerivativeTensor_metricOperator_euclidean_apply
    {X : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    {Y : Fin 2 → Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F}
    (h0 : DifferentiableAt ℝ (Y 0) x) (h1 : DifferentiableAt ℝ (Y 1) x) :
    lieDerivativeTensor 𝓘(ℝ, F) X (metricOperator (innerProductSpaceMetric F)) Y x
      = @inner ℝ F _ (fderiv ℝ X x (Y 0 x)) (Y 1 x)
        + @inner ℝ F _ (Y 0 x) (fderiv ℝ X x (Y 1 x)) := by
  rw [lieDerivativeTensor_formula, Fin.sum_univ_two]
  have hfun : metricOperator (innerProductSpaceMetric F) Y
      = fun q => (innerProductSpaceMetric F).metricInner q (Y 0 q) (Y 1 q) := rfl
  have e0 : metricOperator (innerProductSpaceMetric F)
        (Function.update Y 0 (lieDerivativeVectorField 𝓘(ℝ, F) X (Y 0))) x
      = @inner ℝ F _ (fderiv ℝ (Y 0) x (X x)) (Y 1 x)
        - @inner ℝ F _ (fderiv ℝ X x (Y 0 x)) (Y 1 x) := by
    rw [metricOperator_apply, Function.update_self,
      Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide),
      lieDerivativeVectorField_euclidean_apply,
      (innerProductSpaceMetric F).metricInner_sub_left]
    simp only [innerProductSpaceMetric_apply, covariantDerivativeEuclidean_apply]
  have e1 : metricOperator (innerProductSpaceMetric F)
        (Function.update Y 1 (lieDerivativeVectorField 𝓘(ℝ, F) X (Y 1))) x
      = @inner ℝ F _ (Y 0 x) (fderiv ℝ (Y 1) x (X x))
        - @inner ℝ F _ (Y 0 x) (fderiv ℝ X x (Y 1 x)) := by
    rw [metricOperator_apply, Function.update_self,
      Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide),
      lieDerivativeVectorField_euclidean_apply,
      (innerProductSpaceMetric F).metricInner_sub_right]
    simp only [innerProductSpaceMetric_apply, covariantDerivativeEuclidean_apply]
  rw [hfun, directionalDerivative_metricInner_euclidean h0 h1 X, e0, e1]
  ring

/-- **Eng.** On Euclidean space the six-term Koszul expression collapses to
`2⟨∇_Y X, Z⟩`: the flat metric is parallel and the bracket is the difference of
covariant derivatives, so all terms cancel except `2⟨∇_Y X, Z⟩`. -/
theorem koszulExpression_euclidean_apply
    {X Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x} {x : F}
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) :
    koszulExpression (innerProductSpaceMetric F) X Y Z x
      = 2 * @inner ℝ F _ (fderiv ℝ X x (Y x)) (Z x) := by
  have hDX := directionalDerivative_metricInner_euclidean hY hZ X
  have hDY := directionalDerivative_metricInner_euclidean hX hZ Y
  have hDZ := directionalDerivative_metricInner_euclidean hX hY Z
  rw [koszulExpression, hDX, hDY, hDZ,
    lieDerivativeVectorField_euclidean_apply X Y x,
    lieDerivativeVectorField_euclidean_apply Y Z x,
    lieDerivativeVectorField_euclidean_apply Z X x,
    (innerProductSpaceMetric F).metricInner_sub_left,
    (innerProductSpaceMetric F).metricInner_sub_left,
    (innerProductSpaceMetric F).metricInner_sub_left]
  simp only [innerProductSpaceMetric_apply, covariantDerivativeEuclidean_apply]
  rw [real_inner_comm (fderiv ℝ Z x (X x)) (Y x),
    real_inner_comm (fderiv ℝ Z x (Y x)) (X x),
    real_inner_comm (fderiv ℝ Y x (Z x)) (X x)]
  ring

/-- **Math.** **Prop. 2.2.1** (Petersen §2.2.1): the covariant derivative on
Euclidean space satisfies the implicit formula
`2 g(∇_Y X, Z) = (L_X g)(Y, Z) + (dθ_X)(Y, Z)`
for the canonical inner-product metric `g`, where `θ_X = i_X g` is the dual
`1`-form of `X`. This is the identity that makes sense on any Riemannian
manifold and defines the Riemannian connection there. -/
theorem covariantDerivative_implicit_euclidean
    {X Y Z : Π x : F, TangentSpace 𝓘(ℝ, F) x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (x : F) :
    2 * (innerProductSpaceMetric F).metricInner x
        (covariantDerivativeEuclidean Y X x) (Z x)
      = lieDerivativeTensor 𝓘(ℝ, F) X (metricOperator (innerProductSpaceMetric F))
          ![Y, Z] x
        + exteriorDerivative_lieFormula 𝓘(ℝ, F)
            (dualOneForm (innerProductSpaceMetric F) X) ![Y, Z] x := by
  rw [koszulFormula (innerProductSpaceMetric F) hX hY hZ x,
    koszulExpression_euclidean_apply (hX.differentiableAt x) (hY.differentiableAt x)
      (hZ.differentiableAt x),
    innerProductSpaceMetric_apply, covariantDerivativeEuclidean_apply]

/-! ## Killing fields on Euclidean space -/

/-- **Math.** Killing fields on Euclidean space (Petersen §2.2.1, remark): for
the canonical metric on `F`, a vector field `X` is a Killing field iff
its differential is pointwise skew-adjoint,
`⟨DX(v), w⟩ + ⟨v, DX(w)⟩ = 0` for all `x, v, w` — the basis-free form of the
coordinate equations `∂ᵢXʲ + ∂ⱼXⁱ = 0`. No smoothness of `X` is needed: both
sides read the derivative of `X` through the same (junk-value consistent)
`fderiv`. (Petersen's further classification `X = Ax + β` with `A`
skew-symmetric, obtained by integrating these equations, is not formalized
here.) -/
theorem killingField_euclidean_characterization
    {X : Π x : F, TangentSpace 𝓘(ℝ, F) x} :
    IsKillingField (innerProductSpaceMetric F) X ↔
      ∀ (x : F) (v w : F), ⟪fderiv ℝ X x v, w⟫_ℝ + ⟪v, fderiv ℝ X x w⟫_ℝ = 0 := by
  constructor
  · -- Killing ⇒ pointwise skew-adjointness: test on constant fields.
    intro h x v w
    have hsm : ∀ i, IsSmoothVectorField
        ((![fun _ => v, fun _ => w] : Fin 2 → Π x : F, TangentSpace 𝓘(ℝ, F) x) i) := by
      intro i
      fin_cases i
      · exact isSmoothVectorField_const v
      · exact isSmoothVectorField_const w
    have h2 := congrFun (h ![fun _ => v, fun _ => w] hsm) x
    rw [lieDerivativeTensor_metricOperator_euclidean_apply
      (Y := ![fun _ => v, fun _ => w])
      (differentiableAt_const v) (differentiableAt_const w)] at h2
    simpa using h2
  · -- pointwise skew-adjointness ⇒ Killing: evaluate `L_X g` on smooth fields.
    intro h Y hY
    funext x
    rw [lieDerivativeTensor_metricOperator_euclidean_apply
      ((hY 0).differentiableAt x) ((hY 1).differentiableAt x)]
    exact h x (Y 0 x) (Y 1 x)

end InnerProduct

end PetersenLib

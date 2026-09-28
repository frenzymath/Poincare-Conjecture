import PetersenLib.Ch02.Connections
import PetersenLib.Ch02.GeneralizedJacobi

/-!
# Petersen Ch. 2, §2.2.2 — Covariant derivatives of tensors

The covariant derivative of a `(0,k)`-tensor (`covariantDerivativeTensor`),
parallel tensors (`IsParallel`) and the parallelism of the metric, the
differential as a `(0,1)`-tensor (`differentialOperator`), the Hessian via the
covariant derivative (Prop. 2.2.6, `hessian_via_covariantDerivative`), the
exterior derivative via `∇` (`exteriorDerivative_covariantFormula`), the second
covariant derivative (`secondCovariantDerivative`) with the Hessian identity
(`hessian_eq_secondCovariantDerivative`), and the Lie and covariant derivatives
of the connection itself (`lieDerivativeConnection`,
`covariantDerivativeConnection`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.2.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The covariant derivative of a `(0,k)`-tensor -/

/-- The covariant derivative `∇_v X` in the direction of the value of a vector
field, as a vector field: `(∇_Y X)(p) = ∇_{Y(p)} X`. -/
def AffineConnection.covField (D : AffineConnection I M)
    (Y X : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => D.cov p (Y p) X

@[simp]
theorem AffineConnection.covField_apply (D : AffineConnection I M)
    (Y X : Π x : M, TangentSpace I x) (p : M) :
    D.covField Y X p = D.cov p (Y p) X := rfl

/-- **Math.** The **covariant derivative of a `(0,k)`-tensor** (Petersen §2.2.2):
the `(0,k)`-tensor `∇_X S` determined by the Leibniz rule,
`(∇_X S)(Y₁, …, Y_k) = D_X(S(Y₁, …, Y_k)) − Σᵢ S(Y₁, …, ∇_X Yᵢ, …, Y_k)`.
Petersen's `(0,k+1)`-tensor `∇S` is `∇S(X, Y₁, …, Y_k) = (∇_X S)(Y₁, …, Y_k)`. -/
def covariantDerivativeTensor (D : AffineConnection I M)
    (X : Π x : M, TangentSpace I x) {k : ℕ} (T : TensorOperator I M k) :
    TensorOperator I M k :=
  fun Y => directionalDerivative X (T Y)
    - ∑ i, T (Function.update Y i (D.covField X (Y i)))

theorem covariantDerivativeTensor_formula (D : AffineConnection I M)
    (X : Π x : M, TangentSpace I x) {k : ℕ} (T : TensorOperator I M k)
    (Y : Fin k → Π x : M, TangentSpace I x) (x : M) :
    covariantDerivativeTensor D X T Y x
      = directionalDerivative X (T Y) x
        - ∑ i, T (Function.update Y i (D.covField X (Y i))) x := by
  simp [covariantDerivativeTensor]

/-- **Math.** A tensor is **parallel** if `∇S = 0` (Petersen §2.2.2, Def. of
parallel tensor). -/
def IsParallel (D : AffineConnection I M) {k : ℕ} (T : TensorOperator I M k) : Prop :=
  ∀ (X : Π x : M, TangentSpace I x), IsSmoothVectorField X →
    ∀ (Y : Fin k → Π x : M, TangentSpace I x), (∀ i, IsSmoothVectorField (Y i)) →
      covariantDerivativeTensor D X T Y = 0

/-! ## The metric is parallel (metric half of Prop. 2.2.5) -/

/-- **Math.** `∇g = 0`: the metric is parallel for any Riemannian connection
(the metric half of Prop. 2.2.5; the volume half is proved with the volume
form). -/
theorem metric_parallel {g : RiemannianMetric I M} (D : RiemannianConnection I g) :
    IsParallel D.toAffineConnection (metricOperator g) := by
  intro X hX Y hY
  funext p
  have hcompat := D.metric_compat (hY 0) (hY 1) p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  have h0 : (Function.update Y 0 (D.covField X (Y 0)))
      = ![D.covField X (Y 0), Y 1] := by
    funext j
    fin_cases j
    · simp
    · simp [Function.update_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have h1 : (Function.update Y 1 (D.covField X (Y 1)))
      = ![Y 0, D.covField X (Y 1)] := by
    funext j
    fin_cases j
    · simp [Function.update_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
    · simp
  have hYeq : Y = ![Y 0, Y 1] := by
    funext j; fin_cases j <;> simp
  rw [covariantDerivativeTensor_formula, Fin.sum_univ_two, h0, h1]
  have hval : directionalDerivative X (metricOperator g Y) p
      = g.metricInner p (D.cov p (X p) (Y 0)) (Y 1 p)
        + g.metricInner p (Y 0 p) (D.cov p (X p) (Y 1)) := by
    have : metricOperator g Y = fun q => g.metricInner q (Y 0 q) (Y 1 q) := rfl
    rw [this]
    exact hcompat
  rw [hval]
  simp only [metricOperator_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, AffineConnection.covField_apply, Pi.zero_apply]
  ring

/-! ## The differential as a `(0,1)`-tensor and Prop. 2.2.6 -/

/-- The differential `df` of a function as a `(0,1)`-tensor operator:
`df(Y) = D_Y f`. -/
def differentialOperator (f : M → ℝ) : TensorOperator I M 1 :=
  fun Y => directionalDerivative (Y 0) f

@[simp]
theorem differentialOperator_apply (f : M → ℝ)
    (Y : Fin 1 → Π x : M, TangentSpace I x) (x : M) :
    differentialOperator f Y x = directionalDerivative (Y 0) f x := rfl

section HessianCovariant

variable [FiniteDimensional ℝ E]

/-- **Math.** First half of **Prop. 2.2.6**: `(∇_X df)(Y) = g(∇_X ∇f, Y)` — the
covariant derivative of the differential is implicitly given through the
covariant derivative of the gradient. -/
theorem covariantDerivative_differential_eq_gradient
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {f : M → ℝ}
    (X Y : Π x : M, TangentSpace I x)
    (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    covariantDerivativeTensor D.toAffineConnection X (differentialOperator f) ![Y] p
      = g.metricInner p (D.cov p (X p) (gradient g f)) (Y p) := by
  have hcompat := D.metric_compat hgradf hY p (X p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  rw [covariantDerivativeTensor_formula, Fin.sum_univ_one]
  have hupd : Function.update (![Y] : Fin 1 → Π x : M, TangentSpace I x) 0
      (D.covField X Y) = ![D.covField X Y] := by
    funext j; fin_cases j; simp
  simp only [Matrix.cons_val_zero]
  rw [hupd]
  have hdfY : (differentialOperator f ![Y] : M → ℝ)
      = fun q => g.metricInner q (gradient g f q) (Y q) := by
    funext q
    simp only [differentialOperator_apply, Matrix.cons_val_zero]
    exact directionalDerivative_eq_metricInner_gradient g f Y q
  have hdfCov : differentialOperator f ![D.covField X Y] p
      = g.metricInner p (gradient g f p) (D.cov p (X p) Y) := by
    simp only [differentialOperator_apply, Matrix.cons_val_zero,
      AffineConnection.covField_apply]
    exact (metricInner_gradient g f p (D.cov p (X p) Y)).symm
  rw [hdfY, hdfCov, hcompat]
  ring

/-- Symmetry of `∇df`: `(∇_X df)(Y) = (∇_Y df)(X)` for a torsion-free (i.e.
Riemannian) connection — the covariant Hessian is symmetric. -/
theorem covariantDerivative_differential_symm [I.Boundaryless] [CompleteSpace E]
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (p : M) :
    covariantDerivativeTensor D.toAffineConnection X (differentialOperator f) ![Y] p
      = covariantDerivativeTensor D.toAffineConnection Y
          (differentialOperator f) ![X] p := by
  have hupdY : Function.update (![Y] : Fin 1 → Π x : M, TangentSpace I x) 0
      (D.covField X Y) = ![D.covField X Y] := by
    funext j; fin_cases j; simp
  have hupdX : Function.update (![X] : Fin 1 → Π x : M, TangentSpace I x) 0
      (D.covField Y X) = ![D.covField Y X] := by
    funext j; fin_cases j; simp
  rw [covariantDerivativeTensor_formula, covariantDerivativeTensor_formula,
    Fin.sum_univ_one, Fin.sum_univ_one]
  simp only [Matrix.cons_val_zero]
  rw [hupdY, hupdX]
  have hDf : (differentialOperator f (![Y]) : M → ℝ) = directionalDerivative Y f := by
    funext q; simp
  have hDf' : (differentialOperator f (![X]) : M → ℝ) = directionalDerivative X f := by
    funext q; simp
  simp only [differentialOperator_apply, Matrix.cons_val_zero,
    AffineConnection.covField_apply, hDf, hDf']
  -- reduce to the commutator identity + torsion-freeness
  have hcomm := lieDerivative_vectorField_eq_bracket hX hY hf p
  have htf := D.torsion_free hX hY p
  have hsub : directionalDerivative (D.covField X Y) f p
      - directionalDerivative (D.covField Y X) f p
      = directionalDerivative (lieDerivativeVectorField I X Y) f p := by
    have hmap := (mfderiv I 𝓘(ℝ) f p).map_sub (D.cov p (X p) Y) (D.cov p (Y p) X)
    have h1 : directionalDerivative (D.covField X Y) f p
        - directionalDerivative (D.covField Y X) f p
        = (mfderiv I 𝓘(ℝ) f p (D.cov p (X p) Y - D.cov p (Y p) X) : ℝ) := hmap.symm
    rw [h1, htf]
    rfl
  linarith [hcomm, hsub]

end HessianCovariant

/-! ## Smoothness of the gradient -/

section GradientSmooth

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [InnerProductSpace ℝ E]
  [NeZero (Module.finrank ℝ E)]

/-- The gradient of a smooth function is a smooth vector field (Riesz duality of
the differential, smooth by the vendored musical-isomorphism machinery). -/
theorem gradient_isSmoothVectorField (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    IsSmoothVectorField (gradient g f) := by
  intro p
  have hx : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  refine Tensor.metricRiesz_section_contMDiffAt_of_within g (α := p) hx
    (Φ := fun y => mfderiv I 𝓘(ℝ) f y) ?_
  intro j
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => Tensor.chartBasisVecFiber (I := I) p j q)
    (s := (trivializationAt E (TangentSpace I) p).baseSet) hbaseopen
    (Tensor.chartBasisVec_contMDiffOn (I := I) p j) hx
  have hsmooth : ContMDiffWithinAt I 𝓘(ℝ) ∞
      (directionalDerivative (Z : Π q, TangentSpace I q) f)
      (trivializationAt E (TangentSpace I) p).baseSet p :=
    ((IsSmoothVectorField.directionalDerivative_contMDiff Z.smooth hf) p).contMDiffWithinAt
  have heq : (fun y => mfderiv I 𝓘(ℝ) f y (Tensor.chartBasisVecFiber (I := I) p j y))
      =ᶠ[nhds p] directionalDerivative (Z : Π q, TangentSpace I q) f := by
    filter_upwards [hZ] with y hy
    rw [directionalDerivative_apply, ← hy]
  exact hsmooth.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
    heq.self_of_nhds

end GradientSmooth

/-! ## Prop. 2.2.6 — the Hessian via the covariant derivative -/

section Hessian226

variable [FiniteDimensional ℝ E] [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Prop. 2.2.6**: `(∇_X df)(Y) = Hess f(X, Y)` — the covariant
derivative of the differential is the Hessian `½ L_{∇f} g` defined through the
Lie derivative. Together with `covariantDerivative_differential_eq_gradient`
this realizes `(∇ df)(X,Y) = g(∇_X ∇f, Y) = Hess f(X,Y)`. -/
theorem hessian_via_covariantDerivative {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hgradf : IsSmoothVectorField (gradient g f)) (p : M) :
    covariantDerivativeTensor D.toAffineConnection X (differentialOperator f) ![Y] p
      = hessianLieDerivative g f ![X, Y] p := by
  -- expand the Lie-derivative Hessian
  have hLg : lieDerivativeTensor I (gradient g f) (metricOperator g) ![X, Y] p
      = directionalDerivative (gradient g f)
          (fun q => g.metricInner q (X q) (Y q)) p
        - g.metricInner p (lieDerivativeVectorField I (gradient g f) X p) (Y p)
        - g.metricInner p (X p) (lieDerivativeVectorField I (gradient g f) Y p) := by
    rw [lieDerivativeTensor_formula, Fin.sum_univ_two]
    have h0 : (Function.update (![X, Y]) (0 : Fin 2)
        (lieDerivativeVectorField I (gradient g f) X))
        = ![lieDerivativeVectorField I (gradient g f) X, Y] := by
      funext j; fin_cases j <;> simp
    have h1 : (Function.update (![X, Y]) (1 : Fin 2)
        (lieDerivativeVectorField I (gradient g f) Y))
        = ![X, lieDerivativeVectorField I (gradient g f) Y] := by
      funext j; fin_cases j <;> simp
    have hXY : (fun q => metricOperator g ![X, Y] q)
        = fun q => g.metricInner q (X q) (Y q) := by
      funext q; simp [metricOperator]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, h0, h1,
      metricOperator_apply, hXY]
    ring
  -- metric compatibility along ∇f
  have hcompat := D.metric_compat hX hY p (gradient g f p)
  rw [dirTangent_eq_directionalDerivative] at hcompat
  -- torsion-freeness against X and Y
  have htfX := D.torsion_free hgradf hX p
  have htfY := D.torsion_free hgradf hY p
  -- symmetry of ∇df
  have hsymm := covariantDerivative_differential_symm D hf hX hY p
  have hgradX := covariantDerivative_differential_eq_gradient D X Y hY hgradf p
  have hgradY := covariantDerivative_differential_eq_gradient D Y X hX hgradf p
  -- assemble
  rw [hessianLieDerivative_apply, hLg, ← htfX, ← htfY, hcompat]
  rw [g.metricInner_sub_left, g.metricInner_sub_right]
  have hc₁ : g.metricInner p (X p) (D.cov p (gradient g f p) Y)
      = g.metricInner p (D.cov p (gradient g f p) Y) (X p) := g.metricInner_comm ..
  have hc₂ : g.metricInner p (X p) (D.cov p (Y p) (gradient g f))
      = g.metricInner p (D.cov p (Y p) (gradient g f)) (X p) := g.metricInner_comm ..
  rw [hc₁, hc₂]
  have hXY' : g.metricInner p (D.cov p (Y p) (gradient g f)) (X p)
      = g.metricInner p (D.cov p (X p) (gradient g f)) (Y p) := by
    rw [← hgradX, ← hgradY, hsymm]
  rw [hXY', hgradX]
  ring

end Hessian226

/-! ## The second covariant derivative and `∇` of `∇` -/

/-- **Math.** The **second covariant derivative** (Petersen §2.2.2.3):
`∇²_{X₁,X₂} S = ∇_{X₁}(∇_{X₂} S) − ∇_{∇_{X₁}X₂} S`, the `(0,k+2)`-tensor
`(∇_{X₁}(∇S))(X₂, …)`. -/
def secondCovariantDerivative (D : AffineConnection I M)
    (X₁ X₂ : Π x : M, TangentSpace I x) {k : ℕ} (T : TensorOperator I M k) :
    TensorOperator I M k :=
  covariantDerivativeTensor D X₁ (covariantDerivativeTensor D X₂ T)
    - covariantDerivativeTensor D (D.covField X₁ X₂) T

/-- **Math.** The Hessian as a second covariant derivative (Petersen §2.2.2.3):
`∇²_{X,Y} f = D_X (D_Y f) − D_{∇_X Y} f = (∇_X df)(Y) = Hess f(X, Y)` — where a
function is a `(0,0)`-tensor. -/
theorem hessian_eq_secondCovariantDerivative (D : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) (f : M → ℝ)
    (v : Fin 0 → Π x : M, TangentSpace I x) (p : M) :
    secondCovariantDerivative D X Y (fun _ => f) v p
      = covariantDerivativeTensor D X (differentialOperator f) ![Y] p := by
  have hupd : Function.update (![Y] : Fin 1 → Π x : M, TangentSpace I x) 0
      (D.covField X Y) = ![D.covField X Y] := by
    funext j; fin_cases j; simp
  simp only [secondCovariantDerivative, Pi.sub_apply]
  rw [covariantDerivativeTensor_formula, covariantDerivativeTensor_formula,
    covariantDerivativeTensor_formula]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, sub_zero, Fin.sum_univ_one,
    Matrix.cons_val_zero]
  rw [hupd]
  have h₁ : (covariantDerivativeTensor D Y (fun _ => f) : TensorOperator I M 0) v
      = directionalDerivative Y f := by
    funext q
    rw [covariantDerivativeTensor_formula]
    simp
  have h₂ : ∀ q, (fun (_ : Fin 0 → Π x : M, TangentSpace I x) => f) v q = f q :=
    fun q => rfl
  simp only [differentialOperator_apply, Matrix.cons_val_zero,
    AffineConnection.covField_apply]
  rw [h₁]
  rfl

/-- **Math.** The **exterior derivative through the covariant derivative**
(Petersen §2.2.2.2): `(dω)(X₀, …, X_k) = Σᵢ (−1)ⁱ (∇_{Xᵢ}ω)(X₀, …, X̂ᵢ, …, X_k)`. -/
def exteriorDerivative_covariantFormula (D : AffineConnection I M) {k : ℕ}
    (T : TensorOperator I M k) : TensorOperator I M (k + 1) :=
  fun Y x => ∑ i : Fin (k + 1), (-1 : ℝ) ^ (i : ℕ) *
    covariantDerivativeTensor D (Y i) T (fun j => Y (i.succAbove j)) x

/-- **Math.** The **Lie derivative of the connection** (Petersen §2.2.2.4):
`(L_X ∇)(U, V) = L_X(∇_U V) − ∇_{L_X U} V − ∇_U (L_X V)`. -/
def lieDerivativeConnection (D : AffineConnection I M)
    (X U V : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => lieDerivativeVectorField I X (D.covField U V) p
    - D.cov p (lieDerivativeVectorField I X U p) V
    - D.cov p (U p) (lieDerivativeVectorField I X V)

/-- **Math.** The **covariant derivative of the connection** (Petersen §2.2.2.5):
`(∇_X ∇)_Y T = ∇_X(∇_Y T) − ∇_{∇_X Y} T − ∇_Y(∇_X T)`; it is not tensorial in
`X`, and relates to the second covariant derivative by
`∇²_{X,Y} T = (∇_X ∇)_Y T + ∇_Y (∇_X T)`. -/
def covariantDerivativeConnection (D : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) {k : ℕ} (T : TensorOperator I M k) :
    TensorOperator I M k :=
  covariantDerivativeTensor D X (covariantDerivativeTensor D Y T)
    - covariantDerivativeTensor D (D.covField X Y) T
    - covariantDerivativeTensor D Y (covariantDerivativeTensor D X T)

/-- The second covariant derivative through `∇∇` (the displayed relation of
Petersen §2.2.2.5). -/
theorem secondCovariantDerivative_eq_covariantDerivativeConnection
    (D : AffineConnection I M) (X Y : Π x : M, TangentSpace I x) {k : ℕ}
    (T : TensorOperator I M k) :
    secondCovariantDerivative D X Y T
      = covariantDerivativeConnection D X Y T
        + covariantDerivativeTensor D Y (covariantDerivativeTensor D X T) := by
  funext Z x
  simp only [secondCovariantDerivative, covariantDerivativeConnection,
    Pi.sub_apply, Pi.add_apply]
  ring

/-! ## Symmetry of the Lie derivative of the connection (§2.2.2.4) -/

section LieDerivativeConnectionSymm

variable [I.Boundaryless] [CompleteSpace E]

/-- The Leibniz (Jacobi) identity for the chapter's bracket, pointwise. -/
private theorem lieDerivativeVectorField_leibniz
    {X U V : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (p : M) :
    lieDerivativeVectorField I X (lieDerivativeVectorField I U V) p
      = lieDerivativeVectorField I (lieDerivativeVectorField I X U) V p
        + lieDerivativeVectorField I U (lieDerivativeVectorField I X V) p := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have h2 : ∀ {W : Π x : M, TangentSpace I x}, IsSmoothVectorField W →
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun y => (⟨y, W y⟩ : TangentBundle I M)) p := by
    intro W hW
    refine (hW p).of_le ?_
    rw [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top
  exact VectorField.leibniz_identity_mlieBracket_apply (h2 hX) (h2 hU) (h2 hV)

/-- **Math.** Symmetry of the Lie derivative of the connection (Petersen
§2.2.2.4): for a Riemannian (torsion-free) connection,
`(L_X ∇)(U, V) = (L_X ∇)(V, U)`; the proof combines torsion-freeness with the
(generalized) Jacobi identity. Together with tensoriality in `U`
(`lieDerivativeConnection_smul_direction`), `L_X ∇` is tensorial in both
variables. -/
theorem lieDerivativeConnection_symmetric {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X U V : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hU : IsSmoothVectorField U)
    (hV : IsSmoothVectorField V) (p : M) :
    lieDerivativeConnection D.toAffineConnection X U V p
      = lieDerivativeConnection D.toAffineConnection X V U p := by
  have hUV : IsSmoothVectorField (lieDerivativeVectorField I U V) :=
    hU.lieDerivativeVectorField hV
  have hXU : IsSmoothVectorField (lieDerivativeVectorField I X U) :=
    hX.lieDerivativeVectorField hU
  have hXV : IsSmoothVectorField (lieDerivativeVectorField I X V) :=
    hX.lieDerivativeVectorField hV
  have hcovUV : IsSmoothVectorField (D.covField U V) := D.smooth_cov hU hV
  have hcovVU : IsSmoothVectorField (D.covField V U) := D.smooth_cov hV hU
  -- [X, ∇_U V] − [X, ∇_V U] = [X, [U,V]]
  have hd : ∀ {W : Π x : M, TangentSpace I x}, IsSmoothVectorField W →
      MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => (⟨y, W y⟩ : TangentBundle I M)) p :=
    fun hW => (hW p).mdifferentiableAt (by decide)
  have hA : lieDerivativeVectorField I X (D.covField U V) p
      - lieDerivativeVectorField I X (D.covField V U) p
      = lieDerivativeVectorField I X (lieDerivativeVectorField I U V) p := by
    have hb2 : VectorField.mlieBracket I X ((-1 : ℝ) • D.covField V U) p
        = (-1 : ℝ) • VectorField.mlieBracket I X (D.covField V U) p :=
      VectorField.mlieBracket_const_smul_right (hd hcovVU)
    have hsmulsec : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
        (fun y => (⟨y, ((-1 : ℝ) • D.covField V U) y⟩ : TangentBundle I M)) p :=
      MDifferentiableAt.smul_section (mdifferentiableAt_const) (hd hcovVU)
    have hb3 : VectorField.mlieBracket I X
          (D.covField U V + (-1 : ℝ) • D.covField V U) p
        = VectorField.mlieBracket I X (D.covField U V) p
          + VectorField.mlieBracket I X ((-1 : ℝ) • D.covField V U) p :=
      VectorField.mlieBracket_add_right (hd hcovUV) hsmulsec
    have hfield : D.covField U V + (-1 : ℝ) • D.covField V U
        = lieDerivativeVectorField I U V := by
      funext q
      rw [Pi.add_apply, Pi.smul_apply, neg_one_smul, ← sub_eq_add_neg]
      exact D.torsion_free hU hV q
    calc lieDerivativeVectorField I X (D.covField U V) p
        - lieDerivativeVectorField I X (D.covField V U) p
        = lieDerivativeVectorField I X (D.covField U V) p
          + (-1 : ℝ) • lieDerivativeVectorField I X (D.covField V U) p := by
          rw [neg_one_smul, ← sub_eq_add_neg]
      _ = lieDerivativeVectorField I X
            (D.covField U V + (-1 : ℝ) • D.covField V U) p := by
          simp only [lieDerivativeVectorField_eq_mlieBracket]
          rw [hb3, hb2]
      _ = lieDerivativeVectorField I X (lieDerivativeVectorField I U V) p := by
          rw [hfield]
  -- torsion applied to the pairs ([X,U], V) and (U, [X,V])
  have hB : D.cov p (lieDerivativeVectorField I X U p) V - D.cov p (V p)
        (lieDerivativeVectorField I X U)
      = lieDerivativeVectorField I (lieDerivativeVectorField I X U) V p :=
    D.torsion_free hXU hV p
  have hC : D.cov p (U p) (lieDerivativeVectorField I X V) - D.cov p
        (lieDerivativeVectorField I X V p) U
      = lieDerivativeVectorField I U (lieDerivativeVectorField I X V) p :=
    D.torsion_free hU hXV p
  have hjacobi := lieDerivativeVectorField_leibniz hX hU hV p
  simp only [lieDerivativeConnection]
  have goal_eq : lieDerivativeVectorField I X (D.covField U V) p
      - D.cov p (lieDerivativeVectorField I X U p) V
      - D.cov p (U p) (lieDerivativeVectorField I X V)
      - (lieDerivativeVectorField I X (D.covField V U) p
        - D.cov p (lieDerivativeVectorField I X V p) U
        - D.cov p (V p) (lieDerivativeVectorField I X U))
      = (lieDerivativeVectorField I X (D.covField U V) p
          - lieDerivativeVectorField I X (D.covField V U) p)
        - (D.cov p (lieDerivativeVectorField I X U p) V
            - D.cov p (V p) (lieDerivativeVectorField I X U))
        - (D.cov p (U p) (lieDerivativeVectorField I X V)
            - D.cov p (lieDerivativeVectorField I X V p) U) := by
    abel
  have hzero : lieDerivativeVectorField I X (D.covField U V) p
      - D.cov p (lieDerivativeVectorField I X U p) V
      - D.cov p (U p) (lieDerivativeVectorField I X V)
      - (lieDerivativeVectorField I X (D.covField V U) p
        - D.cov p (lieDerivativeVectorField I X V p) U
        - D.cov p (V p) (lieDerivativeVectorField I X U)) = 0 := by
    rw [goal_eq, hA, hB, hC, hjacobi]
    abel
  have := sub_eq_zero.mp hzero
  exact this

end LieDerivativeConnectionSymm

/-! ## Prop. 2.3.4 — the Lie derivative decomposes through `∇` -/

/-- **Math.** **Prop. 2.3.4**: `L_U = ∇_U − (∇U)` — the Lie derivative in the
direction `U` decomposes as the covariant derivative minus the action of the
`(1,1)`-tensor `∇U : Y ↦ ∇_Y U` as an endomorphism derivation; on a
`(0,k)`-tensor, `(L_U T)(Y₁, …, Y_k) = (∇_U T)(Y₁, …, Y_k) + Σᵢ T(Y₁, …, ∇_{Yᵢ}U, …, Y_k)`
(the endomorphism derivation acts on `(0,k)`-tensors by
`((∇U)·T)(Y₁,…) = −Σᵢ T(…, ∇_{Yᵢ}U, …)`, cf. `endomorphismDerivation`). -/
theorem lieDerivative_eq_covariant_minus_endomorphism
    {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {U : Π x : M, TangentSpace I x} (hU : IsSmoothVectorField U)
    {k : ℕ} {T : TensorOperator I M k} (hT : IsTensorOperator T)
    (Y : Fin k → Π x : M, TangentSpace I x) (hY : ∀ i, IsSmoothVectorField (Y i))
    (x : M) :
    lieDerivativeTensor I U T Y x
      = covariantDerivativeTensor D.toAffineConnection U T Y x
        + ∑ i, T (Function.update Y i (D.covField (Y i) U)) x := by
  rw [lieDerivativeTensor_formula, covariantDerivativeTensor_formula]
  have hterm : ∀ i : Fin k,
      T (Function.update Y i (lieDerivativeVectorField I U (Y i))) x
        = T (Function.update Y i (D.covField U (Y i))) x
          - T (Function.update Y i (D.covField (Y i) U)) x := by
    intro i
    have hbr : lieDerivativeVectorField I U (Y i)
        = fun p => D.covField U (Y i) p - D.covField (Y i) U p := by
      funext p
      exact (D.torsion_free hU (hY i) p).symm
    rw [IsTensorOperator.congr_slot (T := T) hbr, hT.sub_slot]
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib]
  ring

/-! ## Locality (Lem. 2.2.3) -/

section Locality

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

/-- **Math.** **Lem. 2.2.3 (locality on open sets)**: if the smooth vector
fields `X` and `Y` agree on a neighborhood `U` of `p`, then `∇_v X = ∇_v Y` for
every `v ∈ T_pM`. Petersen's proof: choose a smooth cutoff `λ` with `λ ≡ 1`
near `p` and `λ ≡ 0` off `U`; then `λX = λY` globally and the Leibniz rule
gives `∇_v(λX) = ∇_v X` since `dλ|_p = 0` and `λ(p) = 1`. -/
theorem connection_local_openSet (D : AffineConnection I M) {p : M}
    (v : TangentSpace I p) {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    {U : Set M} (hU : IsOpen U) (hpU : p ∈ U) (hXY : Set.EqOn X Y U) :
    D.cov p v X = D.cov p v Y := by
  -- a compact neighborhood inside U
  obtain ⟨K, hKc, hpK, hKU⟩ := exists_compact_subset hU hpU
  -- smooth cutoff: 0 on Uᶜ, 1 on K
  obtain ⟨lam, hlam0, hlam1, -⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed I (isClosed_compl_iff.mpr hU)
      hKc.isClosed (by rw [Set.disjoint_compl_left_iff_subset]; exact hKU)
  have hlam_smooth : ContMDiff I 𝓘(ℝ) ∞ (lam : M → ℝ) := lam.contMDiff
  have hpK' : p ∈ K := interior_subset hpK
  -- λ ≡ 1 near p, so dλ|_p = 0
  have hlam_ev : (lam : M → ℝ) =ᶠ[nhds p] fun _ => 1 := by
    filter_upwards [isOpen_interior.mem_nhds hpK] with q hq
    exact hlam1 (interior_subset hq)
  have hdlam : mfderiv I 𝓘(ℝ) (lam : M → ℝ) p = mfderiv I 𝓘(ℝ) (fun _ => (1 : ℝ)) p :=
    hlam_ev.mfderiv_eq
  have hdlam0 : dirTangent (lam : M → ℝ) v = 0 := by
    show NormedSpace.fromTangentSpace _ (mfderiv I 𝓘(ℝ) (lam : M → ℝ) p v) = 0
    rw [hdlam, mfderiv_const]
    rfl
  -- λ·X = λ·Y globally
  have hlamXY : (fun q => (lam : M → ℝ) q • X q) = fun q => (lam : M → ℝ) q • Y q := by
    funext q
    by_cases hq : q ∈ U
    · rw [hXY hq]
    · have hlamq : (lam : M → ℝ) q = 0 := by simpa using hlam0 (Set.mem_compl hq)
      rw [hlamq, zero_smul, zero_smul]
  have hlamp : (lam : M → ℝ) p = 1 := by simpa using hlam1 hpK'
  -- Leibniz on both cutoffs
  have h₁ := D.leibniz p v hlam_smooth hX
  have h₂ := D.leibniz p v hlam_smooth hY
  rw [hlamXY] at h₁
  rw [h₁] at h₂
  rw [hdlam0, hlamp] at h₂
  simpa using h₂

end Locality

end PetersenLib

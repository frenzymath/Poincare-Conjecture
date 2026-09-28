import PetersenLib.Ch02.CovariantDerivative
import PetersenLib.Ch02.EuclideanConnection

/-!
# Petersen Ch. 2, §2.5 — Exercises (selection)

A tractable subset of the §2.5 exercises, formalized with the machinery of
this chapter:

* **Exercise 2.5.1** (`exercise2_5_1`, `exercise2_5_1_unique`): on Euclidean
  space, the Euclidean covariant derivative is the only affine connection
  with `∇X = 0` for all constant vector fields `X`.
* **Exercise 2.5.3** (`torsionTensor`, `exercise2_5_3`): for an affine
  connection `∇`, the torsion `T(X, Y) = ∇_X Y − ∇_Y X − [X, Y]` is a
  `(2,1)`-tensor — antisymmetric, additive, and `C^∞(M)`-homogeneous in each
  argument.
* **Exercise 2.5.7** (`exercise2_5_7`): for the dual `1`-form `θ_X = i_X g` of
  a vector field `X` and any Riemannian connection `∇`,
  `dθ_X(Y, Z) = g(∇_Y X, Z) − g(Y, ∇_Z X)`.
* **Exercise 2.5.17** (`exercise2_5_17`): a vector field of constant length is
  perpendicular to its covariant derivatives, `∇_v X ⊥ X`.

## Design notes

* The torsion is realized pointwise (`torsionTensor D X Y p ∈ T_pM`), exactly
  as the chapter realizes the covariant derivative; tensoriality is the
  statement that the value is `C^∞(M)`-homogeneous and additive in each field
  argument.  In the first argument the Leibniz term `−df(Y)·X` of
  `AffineConnection.leibniz` cancels against the Leibniz term of Mathlib's
  `VectorField.mlieBracket_smul_left`; the second argument follows from the
  first by the antisymmetry `T(X, Y) = −T(Y, X)`.
* Exercise 2.5.1 avoids any Hadamard/Taylor remainder: Euclidean space carries
  a *global* frame of constant fields, so every smooth field decomposes
  globally as `X = Σᵢ (bᵢ ∘ X)·eᵢ` with globally smooth coefficients
  (`bᵢ` the coordinate functionals of a basis `eᵢ`), and the Leibniz rule
  together with `∇(const) = 0` forces `∇_v X = Σᵢ d(bᵢ∘X)(v)·eᵢ = DX(v)`.
  This is Petersen's intended computation `∇_v(Xⁱ∂ᵢ) = (D_v Xⁱ)∂ᵢ`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Exercise 2.5.3 — the torsion tensor -/

/-- **Math.** The **torsion** of an affine connection (Petersen §2.5,
Exercise 2.5.3): `T(X, Y) = ∇_X Y − ∇_Y X − [X, Y]`, realized pointwise as
`T(X, Y)|_p = ∇_{X|_p} Y − ∇_{Y|_p} X − [X, Y]|_p ∈ T_pM`.  Exercise 2.5.3
asserts that this defines a `(2,1)`-tensor (`exercise2_5_3`). -/
def torsionTensor (D : AffineConnection I M) (X Y : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  fun p => D.cov p (X p) Y - D.cov p (Y p) X - lieDerivativeVectorField I X Y p

@[simp]
theorem torsionTensor_apply (D : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) (p : M) :
    torsionTensor D X Y p
      = D.cov p (X p) Y - D.cov p (Y p) X - lieDerivativeVectorField I X Y p := rfl

/-- **Math.** The torsion is antisymmetric: `T(X, Y) = −T(Y, X)` (Petersen
§2.5, Exercise 2.5.3; no smoothness is needed, by the normalization of the
connection and the antisymmetry of the bracket). -/
theorem torsionTensor_antisymm (D : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) (p : M) :
    torsionTensor D X Y p = -torsionTensor D Y X p := by
  simp only [torsionTensor]
  rw [show lieDerivativeVectorField I X Y p = -lieDerivativeVectorField I Y X p from
    VectorField.mlieBracket_swap_apply]
  abel

section Tensoriality

variable [CompleteSpace E]

/-- **Math.** `C^∞(M)`-homogeneity of the torsion in its first argument
(Petersen §2.5, Exercise 2.5.3): `T(fX, Y) = f·T(X, Y)` for smooth `f, X, Y`.
The Leibniz term of `∇_Y(fX)` cancels against the Leibniz term of `[fX, Y]`. -/
theorem torsionTensor_smul_left (D : AffineConnection I M)
    {f : M → ℝ} {X : Π x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : IsSmoothVectorField X)
    (Y : Π x : M, TangentSpace I x) (p : M) :
    torsionTensor D (fun q => f q • X q) Y p = f p • torsionTensor D X Y p := by
  have hfd : MDifferentiableAt I 𝓘(ℝ) f p := (hf p).mdifferentiableAt (by decide)
  have hXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p :=
    (hX p).mdifferentiableAt (by decide)
  -- direction slot: pointwise homogeneity of the connection
  have h₁ : D.cov p ((fun q => f q • X q) p) Y = f p • D.cov p (X p) Y :=
    D.smul_direction p (f p) (X p) Y
  -- differentiated slot: the Leibniz rule of the connection
  have h₂ : D.cov p (Y p) (fun q => f q • X q)
      = dirTangent f (Y p) • X p + f p • D.cov p (Y p) X :=
    D.leibniz p (Y p) hf hX
  -- bracket: the Leibniz rule of the Lie bracket
  have h₃ : lieDerivativeVectorField I (fun q => f q • X q) Y p
      = -(dirTangent f (Y p)) • X p + f p • lieDerivativeVectorField I X Y p := by
    have hsm : (fun q => f q • X q) = f • X := rfl
    rw [lieDerivativeVectorField_eq_mlieBracket, hsm,
      VectorField.mlieBracket_smul_left hfd hXd]
    rfl
  rw [torsionTensor_apply, torsionTensor_apply, h₁, h₂, h₃]
  simp only [neg_smul, smul_sub]
  abel

/-- **Math.** Additivity of the torsion in its first argument (Petersen §2.5,
Exercise 2.5.3): `T(X + X', Y) = T(X, Y) + T(X', Y)` for smooth `X, X', Y`. -/
theorem torsionTensor_add_left (D : AffineConnection I M)
    {X X' : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hX' : IsSmoothVectorField X')
    (Y : Π x : M, TangentSpace I x) (p : M) :
    torsionTensor D (fun q => X q + X' q) Y p
      = torsionTensor D X Y p + torsionTensor D X' Y p := by
  have hXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p :=
    (hX p).mdifferentiableAt (by decide)
  have hX'd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X' q⟩ : TangentBundle I M)) p :=
    (hX' p).mdifferentiableAt (by decide)
  have h₁ : D.cov p ((fun q => X q + X' q) p) Y
      = D.cov p (X p) Y + D.cov p (X' p) Y :=
    D.add_direction p (X p) (X' p) Y
  have h₂ : D.cov p (Y p) (fun q => X q + X' q)
      = D.cov p (Y p) X + D.cov p (Y p) X' :=
    D.add_field p (Y p) hX hX'
  have h₃ : lieDerivativeVectorField I (fun q => X q + X' q) Y p
      = lieDerivativeVectorField I X Y p + lieDerivativeVectorField I X' Y p := by
    have hsm : (fun q => X q + X' q) = X + X' := rfl
    rw [lieDerivativeVectorField_eq_mlieBracket, hsm,
      VectorField.mlieBracket_add_left hXd hX'd]
    rfl
  rw [torsionTensor_apply, torsionTensor_apply, torsionTensor_apply, h₁, h₂, h₃]
  abel

/-- **Math.** `C^∞(M)`-homogeneity of the torsion in its second argument
(Petersen §2.5, Exercise 2.5.3): `T(X, fY) = f·T(X, Y)`, by the antisymmetry
`T(X, Y) = −T(Y, X)` and homogeneity in the first argument. -/
theorem torsionTensor_smul_right (D : AffineConnection I M)
    {f : M → ℝ} {Y : Π x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hY : IsSmoothVectorField Y)
    (X : Π x : M, TangentSpace I x) (p : M) :
    torsionTensor D X (fun q => f q • Y q) p = f p • torsionTensor D X Y p := by
  rw [torsionTensor_antisymm D X (fun q => f q • Y q) p,
    torsionTensor_smul_left D hf hY X p, torsionTensor_antisymm D X Y p, smul_neg]

/-- **Math.** Additivity of the torsion in its second argument (Petersen §2.5,
Exercise 2.5.3), by antisymmetry and additivity in the first argument. -/
theorem torsionTensor_add_right (D : AffineConnection I M)
    {Y Y' : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hY' : IsSmoothVectorField Y')
    (X : Π x : M, TangentSpace I x) (p : M) :
    torsionTensor D X (fun q => Y q + Y' q) p
      = torsionTensor D X Y p + torsionTensor D X Y' p := by
  rw [torsionTensor_antisymm D X (fun q => Y q + Y' q) p,
    torsionTensor_add_left D hY hY' X p, torsionTensor_antisymm D X Y p,
    torsionTensor_antisymm D X Y' p]
  abel

/-- **Math.** **Exercise 2.5.3** (Petersen §2.5): for an affine connection `∇`,
the torsion `T(X, Y) = ∇_X Y − ∇_Y X − [X, Y]` defines a `(2,1)`-tensor: it is
`C^∞(M)`-homogeneous in each argument, additive, and antisymmetric.  (The
individual statements are `torsionTensor_smul_left`, `torsionTensor_smul_right`,
`torsionTensor_add_left`/`torsionTensor_add_right`, `torsionTensor_antisymm`.) -/
theorem exercise2_5_3 (D : AffineConnection I M)
    {f : M → ℝ} {X X' Y : Π x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : IsSmoothVectorField X)
    (hX' : IsSmoothVectorField X') (hY : IsSmoothVectorField Y) (p : M) :
    torsionTensor D (fun q => f q • X q) Y p = f p • torsionTensor D X Y p
      ∧ torsionTensor D X (fun q => f q • Y q) p = f p • torsionTensor D X Y p
      ∧ torsionTensor D (fun q => X q + X' q) Y p
          = torsionTensor D X Y p + torsionTensor D X' Y p
      ∧ torsionTensor D X Y p = -torsionTensor D Y X p :=
  ⟨torsionTensor_smul_left D hf hX Y p, torsionTensor_smul_right D hf hY X p,
    torsionTensor_add_left D hX hX' Y p, torsionTensor_antisymm D X Y p⟩

end Tensoriality

/-! ## Exercise 2.5.7 — `dθ_X` through the connection -/

/-- **Math.** **Exercise 2.5.7** (Petersen §2.5): for a smooth vector field `X`
with dual `1`-form `θ_X = i_X g` and any Riemannian connection `∇` on `(M, g)`,
`dθ_X(Y, Z) = g(∇_Y X, Z) − g(Y, ∇_Z X)`.

Proof: expand `dθ_X(Y, Z) = D_Y(g(X, Z)) − D_Z(g(X, Y)) − g(X, [Y, Z])` by the
Lie-derivative formula for the exterior derivative of a `1`-form; the metric
property rewrites the two derivative terms, torsion-freeness rewrites the
bracket, and everything cancels by the symmetry of `g`. -/
theorem exercise2_5_7 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    exteriorDerivative_lieFormula I (dualOneForm g X) ![Y, Z] p
      = g.metricInner p (D.cov p (Y p) X) (Z p)
        - g.metricInner p (Y p) (D.cov p (Z p) X) := by
  rw [exteriorDerivative_lieFormula_oneForm (dualOneForm_isTensorOperator g hX)]
  -- identify the two scalar evaluations of θ_X
  have hθZ : (fun q => dualOneForm g X ![Z] q)
      = fun q => g.metricInner q (X q) (Z q) := by
    funext q; simp [dualOneForm]
  have hθY : (fun q => dualOneForm g X ![Y] q)
      = fun q => g.metricInner q (X q) (Y q) := by
    funext q; simp [dualOneForm]
  simp only [dualOneForm_apply, Matrix.cons_val_zero, hθZ, hθY]
  -- the metric property on the two derivative terms
  have hDY : directionalDerivative Y (fun q => g.metricInner q (X q) (Z q)) p
      = g.metricInner p (D.cov p (Y p) X) (Z p)
        + g.metricInner p (X p) (D.cov p (Y p) Z) := by
    rw [← dirTangent_eq_directionalDerivative]
    exact D.metric_compat hX hZ p (Y p)
  have hDZ : directionalDerivative Z (fun q => g.metricInner q (X q) (Y q)) p
      = g.metricInner p (D.cov p (Z p) X) (Y p)
        + g.metricInner p (X p) (D.cov p (Z p) Y) := by
    rw [← dirTangent_eq_directionalDerivative]
    exact D.metric_compat hX hY p (Z p)
  -- torsion-freeness on the bracket term
  have hbr : g.metricInner p (X p) (lieDerivativeVectorField I Y Z p)
      = g.metricInner p (X p) (D.cov p (Y p) Z)
        - g.metricInner p (X p) (D.cov p (Z p) Y) := by
    rw [← D.torsion_free hY hZ p, g.metricInner_sub_right]
  have hcomm : g.metricInner p (D.cov p (Z p) X) (Y p)
      = g.metricInner p (Y p) (D.cov p (Z p) X) := g.metricInner_comm ..
  rw [hDY, hDZ, hbr, hcomm]
  ring

/-! ## Exercise 2.5.17 — constant-length fields -/

/-- **Math.** **Exercise 2.5.17** (Petersen §2.5): if `X` has constant length
on `(M, g)` — here, `g(X, X) ≡ c` — then `∇_v X ⊥ X` for every tangent vector
`v` and any Riemannian connection `∇`.

Proof: the metric property gives `D_v g(X, X) = 2 g(∇_v X, X)`, and the left
side is the derivative of a constant function. -/
theorem exercise2_5_17 {g : RiemannianMetric I M} (D : RiemannianConnection I g)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X) {c : ℝ}
    (hc : ∀ q, g.metricInner q (X q) (X q) = c) (p : M) (v : TangentSpace I p) :
    g.metricInner p (D.cov p v X) (X p) = 0 := by
  have hcompat := D.metric_compat hX hX p v
  rw [show (fun q => g.metricInner q (X q) (X q)) = fun _ => c from funext hc]
    at hcompat
  have h0 : dirTangent (fun _ : M => c) v = 0 := by
    show mfderiv I 𝓘(ℝ, ℝ) (fun _ : M => c) p v = 0
    rw [mfderiv_const]
    rfl
  have hsym : g.metricInner p (X p) (D.cov p v X)
      = g.metricInner p (D.cov p v X) (X p) := g.metricInner_comm ..
  rw [h0, hsym] at hcompat
  linarith

/-! ## Exercise 2.5.18 — Lie and covariant derivatives agree where a tensor vanishes -/

/-- **Math.** **Exercise 2.5.18** (Petersen §2.5): if a `(0, k)`-tensor field
`T` vanishes at `p` (`T Z p = 0` for every tuple `Z` — the faithful statement
that the multilinear map `T_p` is zero), then its Lie derivative and covariant
derivative agree there, `L_X T|_p = ∇_X T|_p`, for any vector field `X` and any
affine connection `∇`.  Both derivatives differ from `D_X(T(Y))` only by
correction terms of the form `T(…, Wᵢ, …)` — the bracket `[X, Yᵢ]` for `L_X`
and `∇_X Yᵢ` for `∇` (whose difference is `∇_{Yᵢ}X` by torsion) — and every such
term is annihilated by `T` at `p`.  In particular, at a critical point of a
function the metric-correction term of the Hessian drops out, which is the
metric-independence of the second derivative there. -/
theorem exercise2_5_18 (D : AffineConnection I M)
    (X : Π x : M, TangentSpace I x) {k : ℕ} (T : TensorOperator I M k)
    (Y : Fin k → Π x : M, TangentSpace I x) {p : M}
    (hT0 : ∀ Z : Fin k → Π x : M, TangentSpace I x, T Z p = 0) :
    lieDerivativeTensor I X T Y p = covariantDerivativeTensor D X T Y p := by
  rw [lieDerivativeTensor_formula, covariantDerivativeTensor_formula]
  have h1 : ∑ i, T (Function.update Y i (lieDerivativeVectorField I X (Y i))) p = 0 :=
    Finset.sum_eq_zero fun i _ => hT0 _
  have h2 : ∑ i, T (Function.update Y i (D.covField X (Y i))) p = 0 :=
    Finset.sum_eq_zero fun i _ => hT0 _
  rw [h1, h2]

/-! ## Exercise 2.5.1 — uniqueness of the Euclidean connection -/

section Euclidean

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite-sum additivity of an affine connection in the differentiated field,
on the model space `E` (each summand a smooth field).  The zero field is
constant, so its covariant derivative vanishes by hypothesis. -/
private theorem cov_finset_sum_euclidean (D : AffineConnection 𝓘(ℝ, E) E)
    (p : E) (v : TangentSpace 𝓘(ℝ, E) p)
    (h0 : D.cov p v (fun _ => 0) = 0)
    {ι : Type*} (s : Finset ι) (X : ι → Π x : E, TangentSpace 𝓘(ℝ, E) x)
    (hX : ∀ i, IsSmoothVectorField (X i)) :
    D.cov p v (fun q => ∑ i ∈ s, X i q) = ∑ i ∈ s, D.cov p v (X i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih =>
    have hsum : IsSmoothVectorField (fun q => ∑ i ∈ s, X i q) :=
      isSmoothVectorField_iff_contDiff.2
        (ContDiff.sum fun i _ => isSmoothVectorField_iff_contDiff.1 (hX i))
    have hins : (fun q => ∑ i ∈ insert a s, X i q)
        = fun q => X a q + ∑ i ∈ s, X i q := by
      funext q
      exact Finset.sum_insert ha
    rw [hins, D.add_field p v (hX a) hsum, ih, Finset.sum_insert ha]

/-- **Math.** **Exercise 2.5.1** (Petersen §2.5): an affine connection on
Euclidean space with `∇X = 0` for all constant vector fields `X` is the
Euclidean covariant derivative, `∇_v X = DX(v)`, on every smooth field.
(The Euclidean covariant derivative itself kills constant fields —
`covariantDerivativeEuclidean_const` — so it is the *only* such connection;
see `exercise2_5_1_unique`.)

Proof: fix a basis `eᵢ` of `E` with coordinate functionals `bᵢ`.  Every smooth
field decomposes globally in the constant frame, `X = Σᵢ (bᵢ ∘ X) • eᵢ`, with
globally smooth coefficients; additivity, the Leibniz rule, and `∇(const) = 0`
give `∇_v X = Σᵢ d(bᵢ ∘ X)(v) • eᵢ = Σᵢ bᵢ(DX(v)) • eᵢ = DX(v)`. -/
theorem exercise2_5_1 [FiniteDimensional ℝ E] (D : AffineConnection 𝓘(ℝ, E) E)
    (hD : ∀ (p : E) (v : TangentSpace 𝓘(ℝ, E) p) (w : E),
      D.cov p v (fun _ => w) = 0)
    {X : Π x : E, TangentSpace 𝓘(ℝ, E) x} (hX : IsSmoothVectorField X)
    (p : E) (v : TangentSpace 𝓘(ℝ, E) p) :
    D.cov p v X = covariantDerivativeEuclidean (fun _ => v) X p := by
  classical
  have hX' : ContDiff ℝ ∞ X := isSmoothVectorField_iff_contDiff.1 hX
  set b := Module.finBasis ℝ E with hb
  set c : Fin (Module.finrank ℝ E) → E →L[ℝ] ℝ :=
    fun i => LinearMap.toContinuousLinearMap (b.coord i) with hc
  have hcw : ∀ (i : Fin (Module.finrank ℝ E)) (w : E), c i w = b.repr w i := by
    intro i w
    simp [hc]
  -- global decomposition of `X` in the constant frame
  have hdecomp : (fun q => ∑ i, c i (X q) • (b i : E)
      : Π x : E, TangentSpace 𝓘(ℝ, E) x) = X := by
    funext q
    calc ∑ i, c i (X q) • (b i : E)
        = ∑ i, b.repr (X q) i • b i :=
          Finset.sum_congr rfl fun i _ => by rw [hcw]
      _ = X q := b.sum_repr (X q)
  -- smoothness of the frame coefficients and of the summands
  have hfc : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun q => c i (X q)) := fun i =>
    contMDiff_iff_contDiff.2 ((c i).contDiff.comp hX')
  have hXi : ∀ i : Fin (Module.finrank ℝ E),
      IsSmoothVectorField (fun q => c i (X q) • (b i : E)) := fun i =>
    isSmoothVectorField_iff_contDiff.2 (((c i).contDiff.comp hX').smul contDiff_const)
  -- the derivative of the `i`th coefficient is the `i`th coefficient of `DX(v)`
  have hdir : ∀ i : Fin (Module.finrank ℝ E),
      dirTangent (fun q => c i (X q)) v = c i (fderiv ℝ X p v) := by
    intro i
    show mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (fun q => c i (X q)) p v = c i (fderiv ℝ X p v)
    have hcomp : fderiv ℝ (fun q => c i (X q)) p = (c i).comp (fderiv ℝ X p) :=
      ((c i).hasFDerivAt.comp p (hX.differentiableAt p).hasFDerivAt).fderiv
    rw [mfderiv_eq_fderiv, hcomp]
    rfl
  -- each summand by the Leibniz rule and the hypothesis on constant fields
  have hterm : ∀ i : Fin (Module.finrank ℝ E),
      D.cov p v (fun q => c i (X q) • (b i : E))
        = c i (fderiv ℝ X p v) • (b i : E) := by
    intro i
    have hL := D.leibniz p v (hfc i) (isSmoothVectorField_const (b i))
    rw [hD p v (b i), smul_zero, add_zero, hdir i] at hL
    exact hL
  -- assemble: additivity over the frame, then the basis representation
  have hstep : D.cov p v (fun q => ∑ i, c i (X q) • (b i : E))
      = ∑ i, D.cov p v (fun q => c i (X q) • (b i : E)) :=
    cov_finset_sum_euclidean D p v (hD p v 0) Finset.univ _ hXi
  have hcov : D.cov p v X = ∑ i, D.cov p v (fun q => c i (X q) • (b i : E)) := by
    rw [← hstep, hdecomp]
  rw [hcov, Finset.sum_congr rfl fun i _ => hterm i]
  show (∑ i, c i (fderiv ℝ X p v) • (b i : E)) = fderiv ℝ X p v
  calc ∑ i, c i (fderiv ℝ X p v) • (b i : E)
      = ∑ i, b.repr (fderiv ℝ X p v) i • b i :=
        Finset.sum_congr rfl fun i _ => by rw [hcw]
    _ = fderiv ℝ X p v := b.sum_repr _

/-- **Math.** **Exercise 2.5.1, uniqueness form** (Petersen §2.5): any two
affine connections on Euclidean space with `∇X = 0` for all constant fields
`X` are equal (both compute `∇_v X = DX(v)` on smooth fields, and affine
connections agreeing on smooth fields coincide). -/
theorem exercise2_5_1_unique [FiniteDimensional ℝ E]
    (D₁ D₂ : AffineConnection 𝓘(ℝ, E) E)
    (h₁ : ∀ (p : E) (v : TangentSpace 𝓘(ℝ, E) p) (w : E),
      D₁.cov p v (fun _ => w) = 0)
    (h₂ : ∀ (p : E) (v : TangentSpace 𝓘(ℝ, E) p) (w : E),
      D₂.cov p v (fun _ => w) = 0) :
    D₁ = D₂ :=
  AffineConnection.ext_of_smooth fun p v X hX => by
    rw [exercise2_5_1 D₁ h₁ hX p v, exercise2_5_1 D₂ h₂ hX p v]

end Euclidean

end PetersenLib

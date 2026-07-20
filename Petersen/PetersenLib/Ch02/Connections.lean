import PetersenLib.Ch02.MetricOperator
import Mathlib.Geometry.Manifold.VectorBundle.Tensoriality

/-!
# Petersen Ch. 2, §2.2.1 — Connections and the Fundamental Theorem of
Riemannian Geometry

Affine connections (`AffineConnection`), Riemannian connections
(`RiemannianConnection`), Koszul's formula (`koszulFormula`,
`koszulExpression`), and the Fundamental Theorem of Riemannian Geometry
(`fundamentalTheoremRiemannianGeometry`): on `(M, g)` there is exactly one
Riemannian connection, given implicitly by Koszul's formula.

## Design notes

* Petersen's affine connection is a map `∇ : TM × 𝔛(M) → TM`: the direction is
  a single tangent vector, the differentiated argument a (smooth) vector field.
  The structure `AffineConnection` mirrors this: `cov p v X ∈ T_pM` for
  `v ∈ T_pM`, with linearity in `v`, additivity and the Leibniz rule in `X`
  (quantified over smooth fields), preservation of smoothness, and the
  normalization `cov p v X = 0` for non-smooth `X` (the classical object is
  only defined on `𝔛(M)`; normalizing the junk values makes uniqueness
  literal).
* Existence rides on this project’s own Koszul machinery
  (`RiemannianMetric.koszulDualSection` and its smoothness); the pointwise
  well-definedness in the direction slot is Mathlib's tensoriality criterion
  `TensorialAt.pointwise` applied to the Koszul expression in its middle slot.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.1–§2.2.2.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The Koszul expression -/

/-- **Eng.** The six-term metric-only right-hand side of **Koszul's formula**
(Petersen §2.2.1):
`D_X g(Y,Z) + D_Y g(X,Z) − D_Z g(X,Y) − g([X,Y],Z) − g([Y,Z],X) + g([Z,X],Y)`.
Any Riemannian connection satisfies `2 g(∇_Y X, Z) = koszulExpression g X Y Z`. -/
def koszulExpression (g : RiemannianMetric I M) (X Y Z : Π x : M, TangentSpace I x) :
    M → ℝ :=
  fun p =>
    directionalDerivative X (fun q => g.metricInner q (Y q) (Z q)) p
      + directionalDerivative Y (fun q => g.metricInner q (X q) (Z q)) p
      - directionalDerivative Z (fun q => g.metricInner q (X q) (Y q)) p
      - g.metricInner p (lieDerivativeVectorField I X Y p) (Z p)
      - g.metricInner p (lieDerivativeVectorField I Y Z p) (X p)
      + g.metricInner p (lieDerivativeVectorField I Z X p) (Y p)

/-- **Math.** **Koszul's formula** (Petersen §2.2.1, remark): on any Riemannian
manifold the expression `(L_X g)(Y, Z) + (dθ_X)(Y, Z)` — which on Euclidean
space computes `2 g(∇_Y X, Z)` — expands, by the algebraic formula for `L_X g`
and the Lie-derivative formula for `dθ_X`, into the six metric-only terms of
`koszulExpression`. -/
theorem koszulFormula (g : RiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    lieDerivativeTensor I X (metricOperator g) ![Y, Z] p
      + exteriorDerivative_lieFormula I (dualOneForm g X) ![Y, Z] p
      = koszulExpression g X Y Z p := by
  -- Expand (L_X g)(Y, Z) by the tensor formula.
  have hLg : lieDerivativeTensor I X (metricOperator g) ![Y, Z] p
      = directionalDerivative X (fun q => g.metricInner q (Y q) (Z q)) p
        - g.metricInner p (lieDerivativeVectorField I X Y p) (Z p)
        - g.metricInner p (Y p) (lieDerivativeVectorField I X Z p) := by
    rw [lieDerivativeTensor_formula, Fin.sum_univ_two]
    have h0 : (Function.update (![Y, Z]) (0 : Fin 2)
        (lieDerivativeVectorField I X Y)) = ![lieDerivativeVectorField I X Y, Z] := by
      funext j; fin_cases j <;> simp
    have h1 : (Function.update (![Y, Z]) (1 : Fin 2)
        (lieDerivativeVectorField I X Z)) = ![Y, lieDerivativeVectorField I X Z] := by
      funext j; fin_cases j <;> simp
    have hYZ : (fun q => metricOperator g ![Y, Z] q)
        = fun q => g.metricInner q (Y q) (Z q) := by
      funext q; simp [metricOperator]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, h1,
      metricOperator_apply, hYZ]
    ring
  -- Expand (dθ_X)(Y, Z) by the 1-form specialization.
  have hdθ : exteriorDerivative_lieFormula I (dualOneForm g X) ![Y, Z] p
      = directionalDerivative Y (fun q => g.metricInner q (X q) (Z q)) p
        - directionalDerivative Z (fun q => g.metricInner q (X q) (Y q)) p
        - g.metricInner p (X p) (lieDerivativeVectorField I Y Z p) := by
    rw [exteriorDerivative_lieFormula_oneForm (dualOneForm_isTensorOperator g hX)]
    have hZ' : (fun q => dualOneForm g X ![Z] q)
        = fun q => g.metricInner q (X q) (Z q) := by
      funext q; simp [dualOneForm]
    have hY' : (fun q => dualOneForm g X ![Y] q)
        = fun q => g.metricInner q (X q) (Y q) := by
      funext q; simp [dualOneForm]
    simp only [dualOneForm_apply, Matrix.cons_val_zero, hZ', hY']
  rw [hLg, hdθ, koszulExpression]
  -- match the remaining bracket terms using symmetry and antisymmetry
  have h₁ : g.metricInner p (Y p) (lieDerivativeVectorField I X Z p)
      = -(g.metricInner p (lieDerivativeVectorField I Z X p) (Y p)) := by
    rw [g.metricInner_comm]
    have : lieDerivativeVectorField I X Z p = -(lieDerivativeVectorField I Z X p) :=
      VectorField.mlieBracket_swap_apply
    rw [this, g.metricInner_neg_left]
  have h₂ : g.metricInner p (X p) (lieDerivativeVectorField I Y Z p)
      = g.metricInner p (lieDerivativeVectorField I Y Z p) (X p) :=
    g.metricInner_comm ..
  rw [h₁, h₂]
  ring

/-! ## Affine and Riemannian connections -/

variable (I) in
/-- **Math.** An **affine connection** on `M` (Petersen §2.2.1): an assignment
`(v, X) ↦ ∇_v X ∈ T_pM` for `v ∈ T_pM` and `X ∈ 𝔛(M)` such that (1) `v ↦ ∇_v X`
is linear (a `(1,1)`-tensor), and (2) `X ↦ ∇_v X` is a derivation: additive,
with the Leibniz rule `∇_v(fX) = df(v)·X|_p + f(p)·∇_v X`.

**Eng.** `cov` is defined on all of `(Π x, TangentSpace I x)` and normalized to
`0` on non-smooth fields (`junk`), so that connections agreeing on `𝔛(M)` are
literally equal; `smooth_cov` records that `∇_Y X ∈ 𝔛(M)` for `X, Y ∈ 𝔛(M)`. -/
structure AffineConnection (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] where
  /-- The covariant derivative `∇_v X` of the field `X` in the direction
  `v ∈ T_pM`. -/
  cov : ∀ p : M, TangentSpace I p → (Π x : M, TangentSpace I x) → TangentSpace I p
  /-- Additivity in the direction. -/
  add_direction : ∀ (p : M) (v w : TangentSpace I p) (X : Π x : M, TangentSpace I x),
    cov p (v + w) X = cov p v X + cov p w X
  /-- Homogeneity in the direction. -/
  smul_direction : ∀ (p : M) (c : ℝ) (v : TangentSpace I p)
    (X : Π x : M, TangentSpace I x), cov p (c • v) X = c • cov p v X
  /-- Additivity in the differentiated field. -/
  add_field : ∀ (p : M) (v : TangentSpace I p) {X₁ X₂ : Π x : M, TangentSpace I x},
    IsSmoothVectorField X₁ → IsSmoothVectorField X₂ →
    cov p v (fun q => X₁ q + X₂ q) = cov p v X₁ + cov p v X₂
  /-- The Leibniz rule `∇_v (fX) = df(v)·X|_p + f(p)·∇_v X`. -/
  leibniz : ∀ (p : M) (v : TangentSpace I p) {f : M → ℝ}
    {X : Π x : M, TangentSpace I x}, ContMDiff I 𝓘(ℝ) ∞ f → IsSmoothVectorField X →
    cov p v (fun q => f q • X q) = dirTangent f v • X p + f p • cov p v X
  /-- `∇_Y X` is a smooth field for smooth `X`, `Y`. -/
  smooth_cov : ∀ {Y X : Π x : M, TangentSpace I x},
    IsSmoothVectorField Y → IsSmoothVectorField X →
    IsSmoothVectorField (fun p => cov p (Y p) X)
  /-- Normalization: `∇_v X = 0` for non-smooth `X` (the classical connection is
  only defined on `𝔛(M)`). -/
  junk : ∀ (p : M) (v : TangentSpace I p) {X : Π x : M, TangentSpace I x},
    ¬IsSmoothVectorField X → cov p v X = 0

/-- Two affine connections agreeing on smooth fields are equal. -/
theorem AffineConnection.ext_of_smooth {D₁ D₂ : AffineConnection I M}
    (h : ∀ (p : M) (v : TangentSpace I p) (X : Π x : M, TangentSpace I x),
      IsSmoothVectorField X → D₁.cov p v X = D₂.cov p v X) : D₁ = D₂ := by
  cases D₁ with | mk cov₁ a₁ s₁ af₁ l₁ sc₁ j₁ =>
  cases D₂ with | mk cov₂ a₂ s₂ af₂ l₂ sc₂ j₂ =>
  simp only [AffineConnection.mk.injEq]
  funext p v X
  by_cases hX : IsSmoothVectorField X
  · exact h p v X hX
  · rw [j₁ p v hX, j₂ p v hX]

variable (I) in
/-- **Math.** A **Riemannian connection** on `(M, g)` (Petersen §2.2.1): an
affine connection that is in addition (3) torsion free,
`∇_X Y − ∇_Y X = [X, Y]`, and (4) metric,
`D_v g(X,Y) = g(∇_v X, Y) + g(X, ∇_v Y)`. -/
structure RiemannianConnection {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] (g : RiemannianMetric I M) extends AffineConnection I M where
  /-- Torsion-freeness: `∇_X Y − ∇_Y X = [X, Y]`. -/
  torsion_free : ∀ {X Y : Π x : M, TangentSpace I x},
    IsSmoothVectorField X → IsSmoothVectorField Y → ∀ p : M,
    cov p (X p) Y - cov p (Y p) X = lieDerivativeVectorField I X Y p
  /-- The metric property: `D_v g(X,Y) = g(∇_v X, Y) + g(X, ∇_v Y)`. -/
  metric_compat : ∀ {X Y : Π x : M, TangentSpace I x},
    IsSmoothVectorField X → IsSmoothVectorField Y → ∀ (p : M) (v : TangentSpace I p),
    dirTangent (fun q => g.metricInner q (X q) (Y q)) v
      = g.metricInner p (cov p v X) (Y p) + g.metricInner p (X p) (cov p v Y)

omit [IsManifold I ∞ M] in
/-- `dirTangent` along the value of a vector field is the directional
derivative. -/
theorem dirTangent_eq_directionalDerivative (f : M → ℝ)
    (X : Π x : M, TangentSpace I x) (p : M) :
    dirTangent f (X p) = directionalDerivative X f p := rfl

/-- **Math.** Every Riemannian connection satisfies **Koszul's formula**
`2 g(∇_Y X, Z) = koszulExpression g X Y Z` — the uniqueness half of the
Fundamental Theorem: the right-hand side does not mention `∇`. -/
theorem RiemannianConnection.koszul {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    2 * g.metricInner p (D.cov p (Y p) X) (Z p) = koszulExpression g X Y Z p := by
  have hDX : directionalDerivative X (fun q => g.metricInner q (Y q) (Z q)) p
      = g.metricInner p (D.cov p (X p) Y) (Z p)
        + g.metricInner p (Y p) (D.cov p (X p) Z) := by
    rw [← dirTangent_eq_directionalDerivative]
    exact D.metric_compat hY hZ p (X p)
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
  have hbXY : g.metricInner p (lieDerivativeVectorField I X Y p) (Z p)
      = g.metricInner p (D.cov p (X p) Y) (Z p)
        - g.metricInner p (D.cov p (Y p) X) (Z p) := by
    rw [← D.torsion_free hX hY p, g.metricInner_sub_left]
  have hbYZ : g.metricInner p (lieDerivativeVectorField I Y Z p) (X p)
      = g.metricInner p (D.cov p (Y p) Z) (X p)
        - g.metricInner p (D.cov p (Z p) Y) (X p) := by
    rw [← D.torsion_free hY hZ p, g.metricInner_sub_left]
  have hbZX : g.metricInner p (lieDerivativeVectorField I Z X p) (Y p)
      = g.metricInner p (D.cov p (Z p) X) (Y p)
        - g.metricInner p (D.cov p (X p) Z) (Y p) := by
    rw [← D.torsion_free hZ hX p, g.metricInner_sub_left]
  have hsym₁ : g.metricInner p (Y p) (D.cov p (X p) Z)
      = g.metricInner p (D.cov p (X p) Z) (Y p) := g.metricInner_comm ..
  have hsym₂ : g.metricInner p (X p) (D.cov p (Y p) Z)
      = g.metricInner p (D.cov p (Y p) Z) (X p) := g.metricInner_comm ..
  have hsym₃ : g.metricInner p (X p) (D.cov p (Z p) Y)
      = g.metricInner p (D.cov p (Z p) Y) (X p) := g.metricInner_comm ..
  rw [koszulExpression, hDX, hDY, hDZ, hbXY, hbYZ, hbZX, hsym₁, hsym₂, hsym₃]
  ring

/-! ## Existence: the Levi-Civita connection

The Koszul expression, tensorial in its direction slot, defines through the
metric-Riesz duality a pointwise covariant derivative; smoothness is the
vendored `koszulDualSection_contMDiffAt`. -/

section LeviCivita

variable [I.Boundaryless] [CompleteSpace E]

/-- The Koszul expression agrees with the this project’s own Koszul functional on
smooth vector fields. -/
theorem koszulExpression_eq_koszulRHS (g : RiemannianMetric I M)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) (p : M) :
    koszulExpression g X Y Z p
      = g.koszulRHS ⟨X, hX⟩ ⟨Y, hY⟩ ⟨Z, hZ⟩ p := by
  have hcomm : (fun q => g.metricInner q (Z q) (X q))
      = fun q => g.metricInner q (X q) (Z q) := by
    funext q; exact g.metricInner_comm ..
  have h₁ : (⟨X, hX⟩ : SmoothVectorField I M).dir
      (fun q => g.metricInner q (Y q) (Z q)) p
      = directionalDerivative X (fun q => g.metricInner q (Y q) (Z q)) p := rfl
  have h₂ : (⟨Y, hY⟩ : SmoothVectorField I M).dir
      (fun q => g.metricInner q (Z q) (X q)) p
      = directionalDerivative Y (fun q => g.metricInner q (X q) (Z q)) p := by
    rw [show SmoothVectorField.dir (⟨Y, hY⟩ : SmoothVectorField I M)
        (fun q => g.metricInner q (Z q) (X q)) p
        = directionalDerivative Y (fun q => g.metricInner q (Z q) (X q)) p from rfl,
      hcomm]
  have h₃ : (⟨Z, hZ⟩ : SmoothVectorField I M).dir
      (fun q => g.metricInner q (X q) (Y q)) p
      = directionalDerivative Z (fun q => g.metricInner q (X q) (Y q)) p := rfl
  have h₄ : g.metricInner p (DCLieBracket
        (⟨X, hX⟩ : SmoothVectorField I M) ⟨Z, hZ⟩ p) (Y p)
      = -(g.metricInner p (lieDerivativeVectorField I Z X p) (Y p)) := by
    rw [show DCLieBracket (⟨X, hX⟩ : SmoothVectorField I M) ⟨Z, hZ⟩ p
        = lieDerivativeVectorField I X Z p from rfl,
      show lieDerivativeVectorField I X Z p = -(lieDerivativeVectorField I Z X p) from
        VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  have h₅ : g.metricInner p (DCLieBracket
        (⟨Y, hY⟩ : SmoothVectorField I M) ⟨Z, hZ⟩ p) (X p)
      = g.metricInner p (lieDerivativeVectorField I Y Z p) (X p) := rfl
  have h₆ : g.metricInner p (DCLieBracket
        (⟨X, hX⟩ : SmoothVectorField I M) ⟨Y, hY⟩ p) (Z p)
      = g.metricInner p (lieDerivativeVectorField I X Y p) (Z p) := rfl
  show koszulExpression g X Y Z p = _
  rw [RiemannianMetric.koszulRHS, h₁, h₂, h₃, h₄, h₅, h₆, koszulExpression]
  ring

/-- **Math.** The Koszul expression is tensorial (`C^∞(M)`-linear on germs) in
its **direction** slot: the well-definedness input for defining `∇_v X` from
Koszul's formula with `v` a single tangent vector. -/
theorem koszulExpression_tensorialAt_direction (g : RiemannianMetric I M)
    {X Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hZ : IsSmoothVectorField Z) (p : M) :
    TensorialAt I E (fun σ => koszulExpression g X σ Z p) p := by
  have hXp : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := (hX p).mdifferentiableAt (by decide)
  have hZp : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, Z q⟩ : TangentBundle I M)) p := (hZ p).mdifferentiableAt (by decide)
  have hXZd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (X q) (Z q)) p :=
    g.metricInner_raw_mdifferentiableAt hXp hZp
  constructor
  · -- 𝒟(M)-homogeneity in the direction
    intro f σ hf hσ
    have hσZd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (σ q) (Z q)) p :=
      g.metricInner_raw_mdifferentiableAt hσ hZp
    have hXσd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (X q) (σ q)) p :=
      g.metricInner_raw_mdifferentiableAt hXp hσ
    have e₁ : (fun q => g.metricInner q ((f • σ) q) (Z q))
        = f * fun q => g.metricInner q (σ q) (Z q) := by
      funext q; exact g.metricInner_smul_left ..
    have e₃ : (fun q => g.metricInner q (X q) ((f • σ) q))
        = f * fun q => g.metricInner q (X q) (σ q) := by
      funext q; exact g.metricInner_smul_right ..
    have hbr₄ : lieDerivativeVectorField I X (f • σ) p
        = directionalDerivative X f p • σ p
          + f p • lieDerivativeVectorField I X σ p := by
      rw [lieDerivativeVectorField_eq_mlieBracket,
        VectorField.mlieBracket_smul_right hf hσ]
      rfl
    have hbr₅ : lieDerivativeVectorField I (f • σ) Z p
        = -(directionalDerivative Z f p) • σ p
          + f p • lieDerivativeVectorField I σ Z p := by
      rw [lieDerivativeVectorField_eq_mlieBracket,
        VectorField.mlieBracket_smul_left hf hσ]
      rfl
    have hD₂ : directionalDerivative (f • σ)
        (fun q => g.metricInner q (X q) (Z q)) p
        = f p * directionalDerivative σ (fun q => g.metricInner q (X q) (Z q)) p :=
      directionalDerivative_smul_left f σ _ p
    have hDmul₁ : directionalDerivative X
        (fun q => f q * g.metricInner q (σ q) (Z q)) p
        = f p * directionalDerivative X (fun q => g.metricInner q (σ q) (Z q)) p
          + g.metricInner p (σ p) (Z p) * directionalDerivative X f p :=
      directionalDerivative_mul hf hσZd X
    have hDmul₃ : directionalDerivative Z
        (fun q => f q * g.metricInner q (X q) (σ q)) p
        = f p * directionalDerivative Z (fun q => g.metricInner q (X q) (σ q)) p
          + g.metricInner p (X p) (σ p) * directionalDerivative Z f p :=
      directionalDerivative_mul hf hXσd Z
    simp only [koszulExpression, e₁, e₃, Pi.mul_apply, hDmul₁, hDmul₃,
      hD₂, hbr₄, hbr₅, g.metricInner_add_left, g.metricInner_smul_left,
      g.metricInner_smul_right, Pi.smul_apply', smul_eq_mul]
    have hcomm : g.metricInner p (σ p) (X p) = g.metricInner p (X p) (σ p) :=
      g.metricInner_comm ..
    rw [hcomm]
    ring
  · -- additivity in the direction
    intro σ σ' hσ hσ'
    have hσZd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (σ q) (Z q)) p :=
      g.metricInner_raw_mdifferentiableAt hσ hZp
    have hσ'Zd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (σ' q) (Z q)) p :=
      g.metricInner_raw_mdifferentiableAt hσ' hZp
    have hXσd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (X q) (σ q)) p :=
      g.metricInner_raw_mdifferentiableAt hXp hσ
    have hXσ'd : MDifferentiableAt I 𝓘(ℝ) (fun q => g.metricInner q (X q) (σ' q)) p :=
      g.metricInner_raw_mdifferentiableAt hXp hσ'
    have e₁ : (fun q => g.metricInner q ((σ + σ') q) (Z q))
        = (fun q => g.metricInner q (σ q) (Z q))
          + fun q => g.metricInner q (σ' q) (Z q) := by
      funext q; exact g.metricInner_add_left ..
    have e₃ : (fun q => g.metricInner q (X q) ((σ + σ') q))
        = (fun q => g.metricInner q (X q) (σ q))
          + fun q => g.metricInner q (X q) (σ' q) := by
      funext q; exact g.metricInner_add_right ..
    have hbr₄ : lieDerivativeVectorField I X (σ + σ') p
        = lieDerivativeVectorField I X σ p + lieDerivativeVectorField I X σ' p := by
      rw [lieDerivativeVectorField_eq_mlieBracket,
        VectorField.mlieBracket_add_right hσ hσ']
      rfl
    have hbr₅ : lieDerivativeVectorField I (σ + σ') Z p
        = lieDerivativeVectorField I σ Z p + lieDerivativeVectorField I σ' Z p := by
      rw [lieDerivativeVectorField_eq_mlieBracket,
        VectorField.mlieBracket_add_left hσ hσ']
      rfl
    have hD₂ : directionalDerivative (σ + σ')
        (fun q => g.metricInner q (X q) (Z q)) p
        = directionalDerivative σ (fun q => g.metricInner q (X q) (Z q)) p
          + directionalDerivative σ' (fun q => g.metricInner q (X q) (Z q)) p :=
      directionalDerivative_add_left σ σ' _ p
    have hDadd₁ : directionalDerivative X
        (fun q => g.metricInner q (σ q) (Z q) + g.metricInner q (σ' q) (Z q)) p
        = directionalDerivative X (fun q => g.metricInner q (σ q) (Z q)) p
          + directionalDerivative X (fun q => g.metricInner q (σ' q) (Z q)) p :=
      directionalDerivative_add hσZd hσ'Zd X
    have hDadd₃ : directionalDerivative Z
        (fun q => g.metricInner q (X q) (σ q) + g.metricInner q (X q) (σ' q)) p
        = directionalDerivative Z (fun q => g.metricInner q (X q) (σ q)) p
          + directionalDerivative Z (fun q => g.metricInner q (X q) (σ' q)) p :=
      directionalDerivative_add hXσd hXσ'd Z
    simp only [koszulExpression, e₁, e₃, Pi.add_apply, hDadd₁, hDadd₃,
      hD₂, hbr₄, hbr₅, g.metricInner_add_left, g.metricInner_add_right]
    ring

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- A global smooth vector field through a prescribed tangent vector
(bump-function extension, from the this project’s own Riemannian infrastructure). -/
def extendTangentVector (p : M) (v : TangentSpace I p) : SmoothVectorField I M :=
  (exists_smoothVectorField_eq p v).choose

@[simp]
theorem extendTangentVector_apply (p : M) (v : TangentSpace I p) :
    extendTangentVector p v p = v :=
  (exists_smoothVectorField_eq p v).choose_spec

/-- The Koszul expression only sees the direction through its value at `p`. -/
theorem koszulExpression_congr_direction (g : RiemannianMetric I M)
    {X Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hZ : IsSmoothVectorField Z)
    {Y₁ Y₂ : Π x : M, TangentSpace I x} {p : M}
    (hY₁ : IsSmoothVectorField Y₁) (hY₂ : IsSmoothVectorField Y₂)
    (h : Y₁ p = Y₂ p) :
    koszulExpression g X Y₁ Z p = koszulExpression g X Y₂ Z p :=
  (koszulExpression_tensorialAt_direction g hX hZ p).pointwise
    ((hY₁ p).mdifferentiableAt (by decide))
    ((hY₂ p).mdifferentiableAt (by decide)) h

open Classical in
/-- The pointwise Levi-Civita covariant derivative `∇_v X ∈ T_pM`: the
metric-Riesz dual of the (halved) Koszul expression in the direction of any
smooth extension of `v`, normalized to `0` on non-smooth `X`. -/
noncomputable def RiemannianMetric.covAt (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) (X : Π x : M, TangentSpace I x) : TangentSpace I p :=
  if hX : IsSmoothVectorField X then
    g.koszulDualSection ⟨X, hX⟩ (extendTangentVector p v) p
  else 0

/-- **Math.** The defining property of the Levi-Civita covariant derivative:
`2 g(∇_v X, Z|_p) = koszulExpression g X Y Z |_p` for every smooth extension
`Y` of `v` and every smooth test field `Z`. -/
theorem RiemannianMetric.covAt_dual (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (hYv : Y p = v)
    (hZ : IsSmoothVectorField Z) :
    2 * g.metricInner p (g.covAt p v X) (Z p) = koszulExpression g X Y Z p := by
  rw [RiemannianMetric.covAt, dif_pos hX]
  have hext : IsSmoothVectorField (extendTangentVector p v : Π x : M, TangentSpace I x) :=
    (extendTangentVector p v).smooth
  calc 2 * g.metricInner p (g.koszulDualSection ⟨X, hX⟩ (extendTangentVector p v) p)
        (Z p)
      = g.koszulRHS ⟨X, hX⟩ (extendTangentVector p v) ⟨Z, hZ⟩ p := by
        have h := g.koszulDualSection_dual (X := ⟨X, hX⟩)
          (Y := extendTangentVector p v) (Z := ⟨Z, hZ⟩) p
        exact h
    _ = koszulExpression g X (extendTangentVector p v) Z p := by
        rw [koszulExpression_eq_koszulRHS g hX hext hZ p]
    _ = koszulExpression g X Y Z p :=
        koszulExpression_congr_direction g hX hZ hext hY
          (by rw [extendTangentVector_apply, hYv])

/-- Vectors with equal inner products against every tangent vector at `p` are
equal — packaged for testing against values of smooth fields. -/
private theorem eq_of_metricInner_eq (g : RiemannianMetric I M) {p : M}
    {v w : TangentSpace I p}
    (h : ∀ z : TangentSpace I p, g.metricInner p v z = g.metricInner p w z) :
    v = w :=
  (g.metricInner_eq_iff_eq p v w).mp h

/-- The defining property of `covAt` against a tangent test vector. -/
theorem RiemannianMetric.covAt_dual_vec (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) {X : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (z : TangentSpace I p) :
    2 * g.metricInner p (g.covAt p v X) z
      = koszulExpression g X (extendTangentVector p v)
          (extendTangentVector p z) p := by
  have h := g.covAt_dual p v hX (Y := (extendTangentVector p v : Π x, TangentSpace I x))
    (extendTangentVector p v).smooth (extendTangentVector_apply ..)
    (Z := (extendTangentVector p z : Π x, TangentSpace I x))
    (extendTangentVector p z).smooth
  rwa [extendTangentVector_apply] at h

/-! ### Antisymmetrization and symmetrization of the Koszul expression -/

/-- Antisymmetrizing Koszul's formula in the differentiated field and the
direction produces the bracket: `koszul(Y; X, Z) − koszul(X; Y, Z) = 2 g([X,Y], Z)`
(the torsion-free property of the Koszul-defined connection). -/
theorem koszulExpression_antisymm (g : RiemannianMetric I M)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    koszulExpression g Y X Z p - koszulExpression g X Y Z p
      = 2 * g.metricInner p (lieDerivativeVectorField I X Y p) (Z p) := by
  have hcomm : (fun q => g.metricInner q (Y q) (X q))
      = fun q => g.metricInner q (X q) (Y q) := by
    funext q; exact g.metricInner_comm ..
  have hswap₁ : g.metricInner p (lieDerivativeVectorField I Y X p) (Z p)
      = -(g.metricInner p (lieDerivativeVectorField I X Y p) (Z p)) := by
    rw [show lieDerivativeVectorField I Y X p = -(lieDerivativeVectorField I X Y p)
      from VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  have hswap₂ : g.metricInner p (lieDerivativeVectorField I X Z p) (Y p)
      = -(g.metricInner p (lieDerivativeVectorField I Z X p) (Y p)) := by
    rw [show lieDerivativeVectorField I X Z p = -(lieDerivativeVectorField I Z X p)
      from VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  have hswap₃ : g.metricInner p (lieDerivativeVectorField I Z Y p) (X p)
      = -(g.metricInner p (lieDerivativeVectorField I Y Z p) (X p)) := by
    rw [show lieDerivativeVectorField I Z Y p = -(lieDerivativeVectorField I Y Z p)
      from VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  simp only [koszulExpression, hcomm, hswap₁, hswap₂, hswap₃]
  ring

/-- Symmetrizing Koszul's formula in its differentiated/test fields produces
the metric property: `koszul(X; Z, Y) + koszul(Y; Z, X) = 2 D_Z g(X,Y)`. -/
theorem koszulExpression_symm_sum (g : RiemannianMetric I M)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    koszulExpression g X Z Y p + koszulExpression g Y Z X p
      = 2 * directionalDerivative Z (fun q => g.metricInner q (X q) (Y q)) p := by
  have hcomm₁ : (fun q => g.metricInner q (Z q) (Y q))
      = fun q => g.metricInner q (Y q) (Z q) := by
    funext q; exact g.metricInner_comm ..
  have hcomm₂ : (fun q => g.metricInner q (Z q) (X q))
      = fun q => g.metricInner q (X q) (Z q) := by
    funext q; exact g.metricInner_comm ..
  have hcomm₃ : (fun q => g.metricInner q (Y q) (X q))
      = fun q => g.metricInner q (X q) (Y q) := by
    funext q; exact g.metricInner_comm ..
  have hswap₁ : g.metricInner p (lieDerivativeVectorField I X Z p) (Y p)
      = -(g.metricInner p (lieDerivativeVectorField I Z X p) (Y p)) := by
    rw [show lieDerivativeVectorField I X Z p = -(lieDerivativeVectorField I Z X p)
      from VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  have hswap₂ : g.metricInner p (lieDerivativeVectorField I Z Y p) (X p)
      = -(g.metricInner p (lieDerivativeVectorField I Y Z p) (X p)) := by
    rw [show lieDerivativeVectorField I Z Y p = -(lieDerivativeVectorField I Y Z p)
      from VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  have hswap₃ : g.metricInner p (lieDerivativeVectorField I Y X p) (Z p)
      = -(g.metricInner p (lieDerivativeVectorField I X Y p) (Z p)) := by
    rw [show lieDerivativeVectorField I Y X p = -(lieDerivativeVectorField I X Y p)
      from VectorField.mlieBracket_swap_apply, g.metricInner_neg_left]
  simp only [koszulExpression, hcomm₁, hcomm₂, hcomm₃, hswap₁, hswap₂, hswap₃]
  ring

variable [NeZero (Module.finrank ℝ E)]

/-- **Math.** The **Levi-Civita connection** of `(M, g)`: the Riemannian
connection produced by Koszul's formula. Its `cov` is `RiemannianMetric.covAt`;
each axiom is the corresponding multilinearity identity of the Koszul
expression, transported through the pointwise non-degeneracy of the metric. -/
noncomputable def RiemannianMetric.leviCivita (g : RiemannianMetric I M) :
    RiemannianConnection I g where
  cov := g.covAt
  add_direction p v w X := by
    by_cases hX : IsSmoothVectorField X
    · refine eq_of_metricInner_eq g (fun z => ?_)
      have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
      refine mul_left_cancel₀ h2 ?_
      set σv : Π q : M, TangentSpace I q := ⇑(extendTangentVector p v) with hσv
      set σw : Π q : M, TangentSpace I q := ⇑(extendTangentVector p w) with hσw
      have hσvS : IsSmoothVectorField σv := (extendTangentVector p v).smooth
      have hσwS : IsSmoothVectorField σw := (extendTangentVector p w).smooth
      have hσv' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun q => (⟨q, σv q⟩ : TangentBundle I M)) p :=
        (hσvS p).mdifferentiableAt (by decide)
      have hσw' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun q => (⟨q, σw q⟩ : TangentBundle I M)) p :=
        (hσwS p).mdifferentiableAt (by decide)
      have hT := koszulExpression_tensorialAt_direction g hX
        (extendTangentVector p z).smooth p
      have hσ2' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun q => (⟨q, extendTangentVector p (v + w) q⟩ : TangentBundle I M)) p :=
        ((extendTangentVector p (v + w)).smooth p).mdifferentiableAt (by decide)
      have hptw : koszulExpression g X
          (extendTangentVector p (v + w)) (extendTangentVector p z) p
          = koszulExpression g X (σv + σw) (extendTangentVector p z) p := by
        refine hT.pointwise hσ2' (mdifferentiableAt_add_section hσv' hσw') ?_
        rw [extendTangentVector_apply]
        show v + w = σv p + σw p
        rw [hσv, hσw, extendTangentVector_apply, extendTangentVector_apply]
      calc 2 * g.metricInner p (g.covAt p (v + w) X) z
          = koszulExpression g X (extendTangentVector p (v + w))
              (extendTangentVector p z) p := g.covAt_dual_vec p (v + w) hX z
        _ = koszulExpression g X (σv + σw) (extendTangentVector p z) p := hptw
        _ = koszulExpression g X σv (extendTangentVector p z) p
              + koszulExpression g X σw (extendTangentVector p z) p :=
            hT.add hσv' hσw'
        _ = 2 * g.metricInner p (g.covAt p v X) z
              + 2 * g.metricInner p (g.covAt p w X) z := by
            rw [g.covAt_dual_vec p v hX z, g.covAt_dual_vec p w hX z]
        _ = 2 * g.metricInner p (g.covAt p v X + g.covAt p w X) z := by
            rw [g.metricInner_add_left]; ring
    · simp [RiemannianMetric.covAt, dif_neg hX]
  smul_direction p c v X := by
    by_cases hX : IsSmoothVectorField X
    · refine eq_of_metricInner_eq g (fun z => ?_)
      refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
      set σv : Π q : M, TangentSpace I q := ⇑(extendTangentVector p v) with hσv
      have hσvS : IsSmoothVectorField σv := (extendTangentVector p v).smooth
      have hσv' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun q => (⟨q, σv q⟩ : TangentBundle I M)) p :=
        (hσvS p).mdifferentiableAt (by decide)
      have hT := koszulExpression_tensorialAt_direction g hX
        (extendTangentVector p z).smooth p
      have hσ2' : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
          (fun q => (⟨q, extendTangentVector p (c • v) q⟩ : TangentBundle I M)) p :=
        ((extendTangentVector p (c • v)).smooth p).mdifferentiableAt (by decide)
      have hcs : MDifferentiableAt I 𝓘(ℝ) (fun _ : M => c) p := mdifferentiableAt_const
      have hptw : koszulExpression g X
          (extendTangentVector p (c • v)) (extendTangentVector p z) p
          = koszulExpression g X ((fun _ : M => c) • σv) (extendTangentVector p z) p := by
        refine hT.pointwise hσ2' (hcs.smul_section hσv') ?_
        rw [extendTangentVector_apply]
        show c • v = c • σv p
        rw [hσv, extendTangentVector_apply]
      calc 2 * g.metricInner p (g.covAt p (c • v) X) z
          = koszulExpression g X (extendTangentVector p (c • v))
              (extendTangentVector p z) p := g.covAt_dual_vec p (c • v) hX z
        _ = koszulExpression g X ((fun _ : M => c) • σv)
              (extendTangentVector p z) p := hptw
        _ = c • koszulExpression g X σv (extendTangentVector p z) p :=
            hT.smul hcs hσv'
        _ = c * (2 * g.metricInner p (g.covAt p v X) z) := by
            rw [g.covAt_dual_vec p v hX z]; exact smul_eq_mul ..
        _ = 2 * g.metricInner p (c • g.covAt p v X) z := by
            rw [g.metricInner_smul_left]; ring
    · simp [RiemannianMetric.covAt, dif_neg hX]
  add_field p v {X₁ X₂} hX₁ hX₂ := by
    have hsum : IsSmoothVectorField (fun q => X₁ q + X₂ q) := by
      have := ((⟨X₁, hX₁⟩ : SmoothVectorField I M)
        + ⟨X₂, hX₂⟩ : SmoothVectorField I M).smooth
      simpa using this
    refine eq_of_metricInner_eq g (fun z => ?_)
    refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
    have hσvS : IsSmoothVectorField
        (extendTangentVector p v : Π q, TangentSpace I q) :=
      (extendTangentVector p v).smooth
    have hZS : IsSmoothVectorField
        (extendTangentVector p z : Π q, TangentSpace I q) :=
      (extendTangentVector p z).smooth
    have hbridge₁ := koszulExpression_eq_koszulRHS g hsum hσvS hZS p
    have hbridge₂ := koszulExpression_eq_koszulRHS g hX₁ hσvS hZS p
    have hbridge₃ := koszulExpression_eq_koszulRHS g hX₂ hσvS hZS p
    have hSVF : (⟨fun q => X₁ q + X₂ q, hsum⟩ : SmoothVectorField I M)
        = (⟨X₁, hX₁⟩ : SmoothVectorField I M) + ⟨X₂, hX₂⟩ := by
      ext q; simp
    calc 2 * g.metricInner p (g.covAt p v (fun q => X₁ q + X₂ q)) z
        = koszulExpression g (fun q => X₁ q + X₂ q) (extendTangentVector p v)
            (extendTangentVector p z) p := g.covAt_dual_vec p v hsum z
      _ = g.koszulRHS ((⟨X₁, hX₁⟩ : SmoothVectorField I M) + ⟨X₂, hX₂⟩)
            (extendTangentVector p v) (extendTangentVector p z) p := by
          rw [hbridge₁, hSVF]
      _ = g.koszulRHS ⟨X₁, hX₁⟩ (extendTangentVector p v)
            (extendTangentVector p z) p
          + g.koszulRHS ⟨X₂, hX₂⟩ (extendTangentVector p v)
            (extendTangentVector p z) p :=
          g.koszulRHS_add_left ..
      _ = 2 * g.metricInner p (g.covAt p v X₁) z
          + 2 * g.metricInner p (g.covAt p v X₂) z := by
          rw [← hbridge₂, ← hbridge₃, g.covAt_dual_vec p v hX₁ z,
            g.covAt_dual_vec p v hX₂ z]
      _ = 2 * g.metricInner p (g.covAt p v X₁ + g.covAt p v X₂) z := by
          rw [g.metricInner_add_left]; ring
  leibniz p v {f X} hf hX := by
    have hfX : IsSmoothVectorField (fun q => f q • X q) := by
      have := (SmoothVectorField.smul f hf ⟨X, hX⟩).smooth
      simpa using this
    refine eq_of_metricInner_eq g (fun z => ?_)
    refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
    have hσvS : IsSmoothVectorField
        (extendTangentVector p v : Π q, TangentSpace I q) :=
      (extendTangentVector p v).smooth
    have hZS : IsSmoothVectorField
        (extendTangentVector p z : Π q, TangentSpace I q) :=
      (extendTangentVector p z).smooth
    have hbridge₁ := koszulExpression_eq_koszulRHS g hfX hσvS hZS p
    have hbridge₂ := koszulExpression_eq_koszulRHS g hX hσvS hZS p
    have hSVF : (⟨fun q => f q • X q, hfX⟩ : SmoothVectorField I M)
        = SmoothVectorField.smul f hf ⟨X, hX⟩ := by
      ext q; simp [SmoothVectorField.smul]
    have hdirf : (extendTangentVector p v).dir f p = dirTangent f v := by
      show mfderiv I 𝓘(ℝ, ℝ) f p (extendTangentVector p v p) = _
      rw [extendTangentVector_apply]
      rfl
    calc 2 * g.metricInner p (g.covAt p v (fun q => f q • X q)) z
        = koszulExpression g (fun q => f q • X q) (extendTangentVector p v)
            (extendTangentVector p z) p := g.covAt_dual_vec p v hfX z
      _ = g.koszulRHS (SmoothVectorField.smul f hf ⟨X, hX⟩)
            (extendTangentVector p v) (extendTangentVector p z) p := by
          rw [hbridge₁, hSVF]
      _ = f p * g.koszulRHS ⟨X, hX⟩ (extendTangentVector p v)
            (extendTangentVector p z) p
          + 2 * ((extendTangentVector p v).dir f p)
            * g.metricInner p (X p) (extendTangentVector p z p) :=
          g.koszulRHS_leibniz_left hf ..
      _ = f p * (2 * g.metricInner p (g.covAt p v X) z)
          + 2 * dirTangent f v * g.metricInner p (X p) z := by
          rw [← hbridge₂, g.covAt_dual_vec p v hX z, hdirf, extendTangentVector_apply]
      _ = 2 * g.metricInner p (dirTangent f v • X p + f p • g.covAt p v X) z := by
          rw [g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_left]
          ring
  smooth_cov {Y X} hY hX := by
    have heq : (fun p => g.covAt p (Y p) X)
        = fun p => g.koszulDualSection ⟨X, hX⟩ ⟨Y, hY⟩ p := by
      funext p
      refine eq_of_metricInner_eq g (fun z => ?_)
      refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
      have hZS : IsSmoothVectorField
          (extendTangentVector p z : Π q, TangentSpace I q) :=
        (extendTangentVector p z).smooth
      have h₁ : 2 * g.metricInner p (g.covAt p (Y p) X) z
          = koszulExpression g X Y (extendTangentVector p z) p := by
        have h := g.covAt_dual p (Y p) hX (Y := Y) hY rfl
          (Z := (extendTangentVector p z : Π q, TangentSpace I q)) hZS
        rwa [extendTangentVector_apply] at h
      have h₂ : 2 * g.metricInner p (g.koszulDualSection ⟨X, hX⟩ ⟨Y, hY⟩ p) z
          = koszulExpression g X Y (extendTangentVector p z) p := by
        have h := g.koszulDualSection_dual (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩)
          (Z := extendTangentVector p z) p
        rw [koszulExpression_eq_koszulRHS g hX hY hZS p]
        rw [extendTangentVector_apply] at h
        exact h
      rw [h₁, h₂]
    rw [heq]
    intro p
    exact g.koszulDualSection_contMDiffAt ⟨X, hX⟩ ⟨Y, hY⟩ p
  junk p v {X} hX := by simp [RiemannianMetric.covAt, dif_neg hX]
  torsion_free {X Y} hX hY p := by
    refine eq_of_metricInner_eq g (fun z => ?_)
    refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
    have hZS : IsSmoothVectorField
        (extendTangentVector p z : Π q, TangentSpace I q) :=
      (extendTangentVector p z).smooth
    have h₁ : 2 * g.metricInner p (g.covAt p (X p) Y) z
        = koszulExpression g Y X (extendTangentVector p z) p := by
      have h := g.covAt_dual p (X p) hY (Y := X) hX rfl
        (Z := (extendTangentVector p z : Π q, TangentSpace I q)) hZS
      rwa [extendTangentVector_apply] at h
    have h₂ : 2 * g.metricInner p (g.covAt p (Y p) X) z
        = koszulExpression g X Y (extendTangentVector p z) p := by
      have h := g.covAt_dual p (Y p) hX (Y := Y) hY rfl
        (Z := (extendTangentVector p z : Π q, TangentSpace I q)) hZS
      rwa [extendTangentVector_apply] at h
    have hanti := koszulExpression_antisymm g X Y
      (extendTangentVector p z : Π q, TangentSpace I q) p
    rw [extendTangentVector_apply] at hanti
    rw [g.metricInner_sub_left, mul_sub, h₁, h₂, hanti]
  metric_compat {X Y} hX hY p v := by
    refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
    have hσvS : IsSmoothVectorField
        (extendTangentVector p v : Π q, TangentSpace I q) :=
      (extendTangentVector p v).smooth
    have h₁ : 2 * g.metricInner p (g.covAt p v X) (Y p)
        = koszulExpression g X (extendTangentVector p v) Y p :=
      g.covAt_dual p v hX (Y := (extendTangentVector p v : Π q, TangentSpace I q))
        hσvS (extendTangentVector_apply ..) (Z := Y) hY
    have h₂ : 2 * g.metricInner p (g.covAt p v Y) (X p)
        = koszulExpression g Y (extendTangentVector p v) X p :=
      g.covAt_dual p v hY (Y := (extendTangentVector p v : Π q, TangentSpace I q))
        hσvS (extendTangentVector_apply ..) (Z := X) hX
    have hsum := koszulExpression_symm_sum g X Y
      (extendTangentVector p v : Π q, TangentSpace I q) p
    have hdir : directionalDerivative
        (extendTangentVector p v : Π q, TangentSpace I q)
        (fun q => g.metricInner q (X q) (Y q)) p
        = dirTangent (fun q => g.metricInner q (X q) (Y q)) v := by
      show mfderiv I 𝓘(ℝ) (fun q => g.metricInner q (X q) (Y q)) p
        (extendTangentVector p v p) = _
      rw [extendTangentVector_apply]
      rfl
    have hcommXY : g.metricInner p (X p) (g.covAt p v Y)
        = g.metricInner p (g.covAt p v Y) (X p) := g.metricInner_comm ..
    rw [mul_add, hcommXY, h₁, h₂, ← hdir, ← hsum]

/-- **Math.** Uniqueness half of the Fundamental Theorem: any two Riemannian
connections on `(M, g)` coincide (both satisfy Koszul's formula, whose
right-hand side does not mention the connection). -/
theorem riemannianConnection_unique (g : RiemannianMetric I M)
    (D₁ D₂ : RiemannianConnection I g) : D₁ = D₂ := by
  have hcov : ∀ (p : M) (v : TangentSpace I p) (X : Π x : M, TangentSpace I x),
      IsSmoothVectorField X → D₁.cov p v X = D₂.cov p v X := by
    intro p v X hX
    refine eq_of_metricInner_eq g (fun z => ?_)
    refine mul_left_cancel₀ (two_ne_zero (α := ℝ)) ?_
    have hvS : IsSmoothVectorField
        (extendTangentVector p v : Π q, TangentSpace I q) :=
      (extendTangentVector p v).smooth
    have hZS : IsSmoothVectorField
        (extendTangentVector p z : Π q, TangentSpace I q) :=
      (extendTangentVector p z).smooth
    have h₁ := D₁.koszul hX hvS hZS p
    have h₂ := D₂.koszul hX hvS hZS p
    rw [extendTangentVector_apply, extendTangentVector_apply] at h₁ h₂
    rw [h₁, h₂]
  cases D₁ with | mk A₁ tf₁ mc₁ =>
  cases D₂ with | mk A₂ tf₂ mc₂ =>
  congr 1
  exact AffineConnection.ext_of_smooth hcov

/-- **Math.** **Thm. 2.2.2 — the Fundamental Theorem of Riemannian Geometry**
(Petersen §2.2.1): on a Riemannian manifold `(M, g)` there is exactly one
Riemannian connection, and it is given implicitly by **Koszul's formula**
`2 g(∇_Y X, Z) = D_X g(Y,Z) + D_Y g(X,Z) − D_Z g(X,Y)
               − g([X,Y],Z) − g([Y,Z],X) + g([Z,X],Y)`. -/
theorem fundamentalTheoremRiemannianGeometry (g : RiemannianMetric I M) :
    ∃! D : RiemannianConnection I g,
      ∀ {X Y Z : Π x : M, TangentSpace I x},
        IsSmoothVectorField X → IsSmoothVectorField Y → IsSmoothVectorField Z →
        ∀ p : M, 2 * g.metricInner p (D.cov p (Y p) X) (Z p)
          = koszulExpression g X Y Z p := by
  refine ⟨g.leviCivita, ?_, ?_⟩
  · intro X Y Z hX hY hZ p
    exact (g.leviCivita).koszul hX hY hZ p
  · intro D _
    exact riemannianConnection_unique g D g.leviCivita

end LeviCivita

end PetersenLib

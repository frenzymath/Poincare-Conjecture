import PetersenLib.Ch02.MetricOperator

/-!
# Petersen Ch. 2, §2.5 — Almost complex structures, the Nijenhuis tensor, and
the Kähler form (Exercise 2.5.33)

An **almost complex structure** on `M` is a smooth `(1,1)`-tensor field `J` with
`J² = -I`, realized here as a pointwise-linear endomorphism `J_x : T_xM → T_xM`
of each tangent space (`AlmostComplexStructure`).  A **Hermitian structure** on
`(M, g)` is such a `J` compatible with the metric, `g(Jv, Jw) = g(v, w)`
(`IsHermitian`); its **Kähler form** is `ω(X, Y) = g(JX, Y)` (`kahlerForm`).

This file formalizes the tensoriality parts of Petersen §2.5, Exercise 2.5.33:

* the **Nijenhuis tensor**
  `N(X, Y) = [JX, JY] − J[JX, Y] − J[X, JY] − [X, Y]` is a `(2,1)`-tensor —
  antisymmetric, additive, and `C^∞(M)`-homogeneous in each argument
  (`nijenhuis`, `nijenhuis_antisymm`, `nijenhuis_add_left`,
  `nijenhuis_smul_left`/`_smul_right`); all the derivative (Leibniz) terms cancel
  exactly as in the torsion tensor of Exercise 2.5.3, the two carried by `J`
  collapsing through `J² = -I`;
* the Kähler form `ω` is a `2`-form: a smooth `(0,2)`-tensor operator
  (`kahlerForm_isTensorOperator`) that is antisymmetric when `J` is Hermitian
  (`kahlerForm_antisymm`).

`exercise2_5_33` bundles these.  The remaining parts of the exercise — that `N`
vanishes when `J` comes from a complex structure (whose converse is the
Newlander–Nirenberg theorem), and that `dω = 0 ⇔ ∇J = 0` (the Kähler
condition) — are classical and are not formalized here: they require the
exterior derivative `d` acting on `2`-forms and the Newlander–Nirenberg theorem,
neither of which is available in this development.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.33.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Almost complex structures -/

/-- **Math.** An **almost complex structure** on a manifold `M` (Petersen §2.5,
Exercise 2.5.33): a smooth `(1,1)`-tensor field `J` with `J² = -I`, realized as
a pointwise-linear endomorphism `J_x : T_xM → T_xM` of each tangent space (so
`C^∞(M)`-homogeneity and additivity in the vector-field argument are automatic
from the pointwise linearity). -/
structure AlmostComplexStructure (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] where
  /-- The pointwise-linear endomorphism `J_x` at each point. -/
  toFun : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x
  /-- `J` maps smooth vector fields to smooth vector fields. -/
  smooth' : ∀ X : ∀ x : M, TangentSpace I x, IsSmoothVectorField X →
    IsSmoothVectorField (fun x => toFun x (X x))
  /-- `J² = -I`. -/
  sq' : ∀ (x : M) (v : TangentSpace I x), toFun x (toFun x v) = -v

namespace AlmostComplexStructure

/-- **Math.** The vector field `J X` obtained by applying `J` pointwise. -/
def field (J : AlmostComplexStructure I M) (X : ∀ x : M, TangentSpace I x) :
    ∀ x : M, TangentSpace I x :=
  fun x => J.toFun x (X x)

@[simp] theorem field_apply (J : AlmostComplexStructure I M)
    (X : ∀ x : M, TangentSpace I x) (x : M) :
    J.field X x = J.toFun x (X x) := rfl

theorem field_smooth (J : AlmostComplexStructure I M)
    {X : ∀ x : M, TangentSpace I x} (hX : IsSmoothVectorField X) :
    IsSmoothVectorField (J.field X) := J.smooth' X hX

@[simp] theorem toFun_toFun (J : AlmostComplexStructure I M)
    (x : M) (v : TangentSpace I x) : J.toFun x (J.toFun x v) = -v := J.sq' x v

theorem field_smul (J : AlmostComplexStructure I M) (f : M → ℝ)
    (X : ∀ x : M, TangentSpace I x) :
    J.field (fun q => f q • X q) = fun q => f q • J.field X q := by
  funext q; simp [field, map_smul]

theorem field_add (J : AlmostComplexStructure I M)
    (X X' : ∀ x : M, TangentSpace I x) :
    J.field (fun q => X q + X' q) = fun q => J.field X q + J.field X' q := by
  funext q; simp [field, map_add]

end AlmostComplexStructure

/-! ## The Nijenhuis tensor -/

section Nijenhuis

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** The **Nijenhuis tensor** of an almost complex structure `J`
(Petersen §2.5, Exercise 2.5.33):
`N(X, Y) = [JX, JY] − J[JX, Y] − J[X, JY] − [X, Y]`, realized pointwise in
`T_pM`. -/
def nijenhuis (J : AlmostComplexStructure I M) (X Y : ∀ x : M, TangentSpace I x) :
    ∀ x : M, TangentSpace I x :=
  fun p => lieDerivativeVectorField I (J.field X) (J.field Y) p
    - J.toFun p (lieDerivativeVectorField I (J.field X) Y p)
    - J.toFun p (lieDerivativeVectorField I X (J.field Y) p)
    - lieDerivativeVectorField I X Y p

theorem nijenhuis_apply (J : AlmostComplexStructure I M)
    (X Y : ∀ x : M, TangentSpace I x) (p : M) :
    nijenhuis J X Y p
      = lieDerivativeVectorField I (J.field X) (J.field Y) p
        - J.toFun p (lieDerivativeVectorField I (J.field X) Y p)
        - J.toFun p (lieDerivativeVectorField I X (J.field Y) p)
        - lieDerivativeVectorField I X Y p := rfl

/-- **Math.** The Nijenhuis tensor is antisymmetric, `N(X, Y) = −N(Y, X)`
(Petersen §2.5, Exercise 2.5.33): each bracket flips sign under the swap
`[A, B] = −[B, A]`, the two `J`-carried brackets picking up the sign inside `J`
by linearity. -/
theorem nijenhuis_antisymm (J : AlmostComplexStructure I M)
    (X Y : ∀ x : M, TangentSpace I x) (p : M) :
    nijenhuis J X Y p = -nijenhuis J Y X p := by
  simp only [nijenhuis, lieDerivativeVectorField_eq_mlieBracket]
  rw [VectorField.mlieBracket_swap_apply (V := J.field X) (W := J.field Y),
    VectorField.mlieBracket_swap_apply (V := J.field X) (W := Y),
    VectorField.mlieBracket_swap_apply (V := X) (W := J.field Y),
    VectorField.mlieBracket_swap_apply (V := X) (W := Y)]
  simp only [map_neg]
  abel

/-- **Math.** Additivity of the Nijenhuis tensor in its first argument
(Petersen §2.5, Exercise 2.5.33): `N(X + X', Y) = N(X, Y) + N(X', Y)`. -/
theorem nijenhuis_add_left (J : AlmostComplexStructure I M)
    {X X' : ∀ x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hX' : IsSmoothVectorField X')
    (Y : ∀ x : M, TangentSpace I x) (p : M) :
    nijenhuis J (fun q => X q + X' q) Y p
      = nijenhuis J X Y p + nijenhuis J X' Y p := by
  have hJX : IsSmoothVectorField (J.field X) := J.field_smooth hX
  have hJX' : IsSmoothVectorField (J.field X') := J.field_smooth hX'
  have hXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := (hX p).mdifferentiableAt (by decide)
  have hX'd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X' q⟩ : TangentBundle I M)) p := (hX' p).mdifferentiableAt (by decide)
  have hJXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, J.field X q⟩ : TangentBundle I M)) p := (hJX p).mdifferentiableAt (by decide)
  have hJX'd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, J.field X' q⟩ : TangentBundle I M)) p := (hJX' p).mdifferentiableAt (by decide)
  have hJfield : J.field (fun q => X q + X' q) = fun q => J.field X q + J.field X' q :=
    J.field_add X X'
  simp only [nijenhuis, hJfield, lieDerivativeVectorField_eq_mlieBracket]
  rw [show (fun q => J.field X q + J.field X' q) = J.field X + J.field X' from rfl,
    show (fun q => X q + X' q) = X + X' from rfl,
    VectorField.mlieBracket_add_left hJXd hJX'd,
    VectorField.mlieBracket_add_left hJXd hJX'd,
    VectorField.mlieBracket_add_left hXd hX'd,
    VectorField.mlieBracket_add_left hXd hX'd]
  simp only [map_add]
  abel

/-- **Math.** `C^∞(M)`-homogeneity of the Nijenhuis tensor in its first argument
(Petersen §2.5, Exercise 2.5.33): `N(fX, Y) = f·N(X, Y)`.  Each of the four
brackets contributes a Leibniz term; the two derivative terms in the direction
`Y` (carried by `J`) cancel using `J² = -I`, and the two in the direction `JY`
cancel directly. -/
theorem nijenhuis_smul_left (J : AlmostComplexStructure I M)
    {f : M → ℝ} {X : ∀ x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : IsSmoothVectorField X)
    (Y : ∀ x : M, TangentSpace I x) (p : M) :
    nijenhuis J (fun q => f q • X q) Y p = f p • nijenhuis J X Y p := by
  have hJX : IsSmoothVectorField (J.field X) := J.field_smooth hX
  have hfd : MDifferentiableAt I 𝓘(ℝ) f p := (hf p).mdifferentiableAt (by decide)
  have hXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := (hX p).mdifferentiableAt (by decide)
  have hJXd : MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, J.field X q⟩ : TangentBundle I M)) p := (hJX p).mdifferentiableAt (by decide)
  have hJfield : J.field (fun q => f q • X q) = fun q => f q • J.field X q :=
    J.field_smul f X
  simp only [nijenhuis, hJfield, lieDerivativeVectorField_eq_mlieBracket]
  rw [show (fun q => f q • J.field X q) = f • J.field X from rfl,
    show (fun q => f q • X q) = f • X from rfl,
    VectorField.mlieBracket_smul_left hfd hJXd,
    VectorField.mlieBracket_smul_left hfd hJXd,
    VectorField.mlieBracket_smul_left hfd hXd,
    VectorField.mlieBracket_smul_left hfd hXd]
  simp only [map_add, map_smul, AlmostComplexStructure.field_apply,
    AlmostComplexStructure.toFun_toFun, smul_sub, smul_neg]
  abel

/-- **Math.** `C^∞(M)`-homogeneity of the Nijenhuis tensor in its second argument
(Petersen §2.5, Exercise 2.5.33), by antisymmetry and homogeneity in the first
argument. -/
theorem nijenhuis_smul_right (J : AlmostComplexStructure I M)
    {f : M → ℝ} {Y : ∀ x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hY : IsSmoothVectorField Y)
    (X : ∀ x : M, TangentSpace I x) (p : M) :
    nijenhuis J X (fun q => f q • Y q) p = f p • nijenhuis J X Y p := by
  rw [nijenhuis_antisymm J X (fun q => f q • Y q) p, nijenhuis_smul_left J hf hY X p,
    nijenhuis_antisymm J X Y p, smul_neg]

/-- **Math.** Additivity of the Nijenhuis tensor in its second argument
(Petersen §2.5, Exercise 2.5.33), by antisymmetry and additivity in the first
argument. -/
theorem nijenhuis_add_right (J : AlmostComplexStructure I M)
    {Y Y' : ∀ x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hY' : IsSmoothVectorField Y')
    (X : ∀ x : M, TangentSpace I x) (p : M) :
    nijenhuis J X (fun q => Y q + Y' q) p
      = nijenhuis J X Y p + nijenhuis J X Y' p := by
  rw [nijenhuis_antisymm J X (fun q => Y q + Y' q) p, nijenhuis_add_left J hY hY' X p,
    nijenhuis_antisymm J X Y p, nijenhuis_antisymm J X Y' p]
  abel

end Nijenhuis

/-! ## Hermitian structures and the Kähler form -/

/-- **Math.** A **Hermitian structure** on `(M, g)` (Petersen §2.5,
Exercise 2.5.33): an almost complex structure `J` compatible with the metric,
`g(Jv, Jw) = g(v, w)` — i.e. each `J_x` is an orthogonal transformation. -/
def IsHermitian (J : AlmostComplexStructure I M) (g : RiemannianMetric I M) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x),
    g.metricInner x (J.toFun x v) (J.toFun x w) = g.metricInner x v w

/-- **Math.** The **Kähler form** of a Hermitian structure (Petersen §2.5,
Exercise 2.5.33): `ω(X, Y) = g(JX, Y)`, a `(0,2)`-tensor operator. -/
def kahlerForm (J : AlmostComplexStructure I M) (g : RiemannianMetric I M) :
    TensorOperator I M 2 :=
  fun Y p => g.metricInner p (J.field (Y 0) p) (Y 1 p)

@[simp] theorem kahlerForm_apply (J : AlmostComplexStructure I M)
    (g : RiemannianMetric I M) (Y : Fin 2 → ∀ x : M, TangentSpace I x) (p : M) :
    kahlerForm J g Y p = g.metricInner p (J.field (Y 0) p) (Y 1 p) := rfl

/-- **Math.** The Kähler form is a smooth `(0,2)`-tensor operator (Petersen §2.5,
Exercise 2.5.33): smoothness because `JX` is a smooth field of a smooth field,
additivity and `C^∞(M)`-homogeneity from the (bi)linearity of `g` and the
pointwise linearity of `J`. -/
theorem kahlerForm_isTensorOperator (J : AlmostComplexStructure I M)
    (g : RiemannianMetric I M) : IsTensorOperator (kahlerForm J g) := by
  constructor
  · intro Y hY x
    have hJ0 : IsSmoothVectorField (J.field (Y 0)) := J.field_smooth (hY 0)
    have h := g.metricInner_contMDiffWithinAt (v := J.field (Y 0)) (w := Y 1)
      (s := Set.univ) (x := x) (n := ∞)
      ((hJ0 x).contMDiffWithinAt) (((hY 1) x).contMDiffWithinAt)
    rwa [contMDiffWithinAt_univ] at h
  · intro Y i V W x
    fin_cases i
    · simp [kahlerForm, AlmostComplexStructure.field, map_add]
    · simp [kahlerForm, AlmostComplexStructure.field]
  · intro Y i f V x
    fin_cases i
    · simp [kahlerForm, AlmostComplexStructure.field, map_smul]
    · simp [kahlerForm, AlmostComplexStructure.field]

/-- **Math.** The Kähler form of a Hermitian structure is antisymmetric
(Petersen §2.5, Exercise 2.5.33): `ω(X, Y) = −ω(Y, X)`, so together with
`kahlerForm_isTensorOperator` it is a `2`-form.  The proof uses `J² = -I` and
the compatibility `g(Jv, Jw) = g(v, w)`. -/
theorem kahlerForm_antisymm (J : AlmostComplexStructure I M)
    (g : RiemannianMetric I M) (h : IsHermitian J g)
    (X Y : ∀ x : M, TangentSpace I x) (p : M) :
    kahlerForm J g ![X, Y] p = -kahlerForm J g ![Y, X] p := by
  simp only [kahlerForm, AlmostComplexStructure.field_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have key := h p (X p) (-(J.toFun p (Y p)))
  simp only [map_neg, AlmostComplexStructure.toFun_toFun, neg_neg] at key
  rw [key, g.metricInner_neg_right, g.metricInner_comm p (X p) (J.toFun p (Y p))]

/-! ## Exercise 2.5.33 -/

/-- **Math.** **Exercise 2.5.33** (Petersen §2.5): for an almost complex
structure `J` (a smooth `(1,1)`-tensor with `J² = -I`) that is Hermitian with
respect to `g`, the Nijenhuis tensor
`N(X, Y) = [JX, JY] − J[JX, Y] − J[X, JY] − [X, Y]` is a `(2,1)`-tensor
(`C^∞(M)`-homogeneous and additive in each argument, antisymmetric), and the
Kähler form `ω(X, Y) = g(JX, Y)` is a `2`-form (a smooth `(0,2)`-tensor operator,
antisymmetric).

The remaining parts of the exercise — `N = 0` for `J` induced by a complex
structure (whose converse is Newlander–Nirenberg), and `dω = 0 ⇔ ∇J = 0` (the
Kähler condition) — are classical and not formalized here (they require the
exterior derivative on `2`-forms and the Newlander–Nirenberg theorem). -/
theorem exercise2_5_33 [I.Boundaryless] [CompleteSpace E]
    (J : AlmostComplexStructure I M) (g : RiemannianMetric I M) (h : IsHermitian J g)
    {f : M → ℝ} {X X' Y : ∀ x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : IsSmoothVectorField X)
    (hX' : IsSmoothVectorField X') (hY : IsSmoothVectorField Y) (p : M) :
    (nijenhuis J (fun q => f q • X q) Y p = f p • nijenhuis J X Y p
      ∧ nijenhuis J X (fun q => f q • Y q) p = f p • nijenhuis J X Y p
      ∧ nijenhuis J (fun q => X q + X' q) Y p
          = nijenhuis J X Y p + nijenhuis J X' Y p
      ∧ nijenhuis J X Y p = -nijenhuis J Y X p)
    ∧ (IsTensorOperator (kahlerForm J g)
      ∧ kahlerForm J g ![X, Y] p = -kahlerForm J g ![Y, X] p) :=
  ⟨⟨nijenhuis_smul_left J hf hX Y p, nijenhuis_smul_right J hf hY X p,
      nijenhuis_add_left J hX hX' Y p, nijenhuis_antisymm J X Y p⟩,
    kahlerForm_isTensorOperator J g, kahlerForm_antisymm J g h X Y p⟩

end PetersenLib

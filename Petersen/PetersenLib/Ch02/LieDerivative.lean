import PetersenLib.Ch02.DirectionalDerivative
import OpenGALib.Riemannian.Manifold.DoCarmoCh2
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# Petersen Ch. 2, §2.1.2 — Lie derivatives

The Lie derivative of a function (`lieDerivativeFunction`), of a vector
field (`lieDerivativeVectorField`), and of a `(0,k)`-tensor
(`lieDerivativeTensor`), together with Petersen's Propositions 2.1.1–2.1.5:

* `lieDerivative_vectorField_eq_bracket` — Prop. 2.1.1: `L_X Y = [X, Y]`,
  realized as the statement that the Lie derivative of a vector field acts on
  functions as the commutator of directional derivatives (Petersen's defining
  property of the Lie bracket).
* `lieDerivativeTensor_formula` — Prop. 2.1.2: the algebraic formula
  `(L_X T)(Y₁, …, Y_k) = D_X(T(Y₁, …, Y_k)) − Σᵢ T(Y₁, …, L_X Yᵢ, …, Y_k)`.
* `lieDerivative_product_rule` — Prop. 2.1.3: `L_X(T₁·T₂) = (L_X T₁)·T₂ + T₁·(L_X T₂)`.
* `lieDerivative_scale_direction` — Prop. 2.1.4: the formula for `L_{fX} T`.
* `lieDerivative_local_at_zero` — Lem. 2.1.5: at a zero of `X`, `(L_X T)|_p`
  depends only on `T|_p`.

## Design notes

* Petersen defines the Lie derivative through the local flow `Fᵗ` of `X` and
  *proves* the algebraic formulas (Props. 2.1.1, 2.1.2). Mathlib has no local
  flow of a vector field on a manifold yet, so here the definitions are the
  algebraic characterizations themselves: `L_X f := D_X f`,
  `L_X Y := VectorField.mlieBracket I X Y` (Mathlib's chart-level bracket) and
  `L_X T` is *defined* by the formula of Prop. 2.1.2. The mathematical content
  of Prop. 2.1.1 then lives in the commutator identity
  `D_{L_X Y} = [D_X, D_Y]` (which is Petersen's definition of the bracket);
  the flow characterization of the bracket for a given local flow is the
  vendored `DCLieBracket_eq_flow_lieDerivative`.
* A `(0,k)`-tensor is manipulated throughout, as in Petersen's proofs, through
  its evaluation on `k` vector fields: the working representation is
  `TensorOperator I M k := (Fin k → Π x, TangentSpace I x) → M → ℝ`, with the
  predicate `IsTensorOperator` (smooth evaluations, slotwise additivity and
  `C^∞(M)`-homogeneity) recording that an operator is the evaluation of an
  honest smooth tensor field.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Lie derivative of a function and of a vector field -/

/-- **Math.** The **Lie derivative of a function**: the first-order effect of the
flow of `X` on `f`, `f ∘ Fᵗ = f + t L_X f + o(t)`; equivalently (Petersen §2.1.2)
`L_X f = D_X f = df(X)`. -/
def lieDerivativeFunction (X : Π x : M, TangentSpace I x) (f : M → ℝ) : M → ℝ :=
  directionalDerivative X f

@[simp]
theorem lieDerivativeFunction_eq_directionalDerivative
    (X : Π x : M, TangentSpace I x) (f : M → ℝ) :
    lieDerivativeFunction X f = directionalDerivative X f := rfl

variable (I) in
/-- **Math.** The **Lie derivative of a vector field**: the first-order term of
`t ↦ DF⁻ᵗ(Y|_{Fᵗ(p)})` along the flow of `X`. By Prop. 2.1.1 it equals the Lie
bracket `[X, Y]`, whose Lean realization is Mathlib's chart-level
`VectorField.mlieBracket`. -/
def lieDerivativeVectorField (X Y : Π x : M, TangentSpace I x) :
    Π x : M, TangentSpace I x :=
  VectorField.mlieBracket I X Y

@[simp]
theorem lieDerivativeVectorField_eq_mlieBracket (X Y : Π x : M, TangentSpace I x) :
    lieDerivativeVectorField I X Y = VectorField.mlieBracket I X Y := rfl

section Bracket

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Prop. 2.1.1**: `L_X Y = [X, Y]` — the Lie derivative of a vector
field acts on functions as the commutator of directional derivatives,
`D_{L_X Y} f = D_X (D_Y f) − D_Y (D_X f)`, which is Petersen's defining property
of the Lie bracket `[X, Y]`. -/
theorem lieDerivative_vectorField_eq_bracket
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (x : M) :
    directionalDerivative (lieDerivativeVectorField I X Y) f x
      = directionalDerivative X (directionalDerivative Y f) x
        - directionalDerivative Y (directionalDerivative X f) x :=
  mfderiv_mlieBracket_eq_commutator ⟨X, hX⟩ ⟨Y, hY⟩ hf x

/-- The Lie bracket of smooth vector fields is a smooth vector field. -/
theorem IsSmoothVectorField.lieDerivativeVectorField
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) :
    IsSmoothVectorField (lieDerivativeVectorField I X Y) := by
  intro x
  exact (DCLieBracket_contMDiffAt ⟨X, hX⟩ ⟨Y, hY⟩ x)

end Bracket

/-- Smoothness of the directional derivative: if `f` and `X` are smooth then so
is `D_X f` (via the tangent map of `f`). -/
theorem IsSmoothVectorField.directionalDerivative_contMDiff
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) :
    ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative X f) :=
  SmoothVectorField.dir_contMDiff ⟨X, hX⟩ hf

/-! ## `(0,k)`-tensors as multilinear operators on vector fields -/

variable (I) in
/-- **Eng.** The working representation of (the evaluation of) a `(0,k)`-tensor
field: an assignment of a function `M → ℝ` to every `k`-tuple of vector fields.
All statements of Petersen §2.1–2.2 manipulate tensors exclusively through such
evaluations. -/
abbrev TensorOperator (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (k : ℕ) :=
  (Fin k → Π x : M, TangentSpace I x) → M → ℝ

/-- **Math.** `T` is (the evaluation of) a **smooth `(0,k)`-tensor field**: its
evaluation on smooth vector fields is smooth, and it is additive and
`C^∞(M)`-homogeneous in each slot. -/
structure IsTensorOperator {k : ℕ} (T : TensorOperator I M k) : Prop where
  /-- Evaluation on smooth vector fields is a smooth function. -/
  smooth_eval : ∀ Y : Fin k → Π x : M, TangentSpace I x,
    (∀ i, IsSmoothVectorField (Y i)) → ContMDiff I 𝓘(ℝ) ∞ (T Y)
  /-- Additivity in each slot. -/
  add_slot : ∀ (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k)
    (V W : Π x : M, TangentSpace I x) (x : M),
    T (Function.update Y i (fun p => V p + W p)) x
      = T (Function.update Y i V) x + T (Function.update Y i W) x
  /-- `C^∞(M)`-homogeneity in each slot. -/
  smul_slot : ∀ (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k)
    (g : M → ℝ) (V : Π x : M, TangentSpace I x) (x : M),
    T (Function.update Y i (fun p => g p • V p)) x
      = g x * T (Function.update Y i V) x

namespace IsTensorOperator

variable {k : ℕ} {T : TensorOperator I M k}

theorem const_smul_slot (hT : IsTensorOperator T)
    (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k) (c : ℝ)
    (V : Π x : M, TangentSpace I x) (x : M) :
    T (Function.update Y i (fun p => c • V p)) x = c * T (Function.update Y i V) x :=
  hT.smul_slot Y i (fun _ => c) V x

theorem zero_slot (hT : IsTensorOperator T)
    (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k) (x : M) :
    T (Function.update Y i (fun _ => 0)) x = 0 := by
  have h := hT.smul_slot Y i (fun _ => (0 : ℝ)) (fun _ => 0) x
  simpa using h

theorem neg_slot (hT : IsTensorOperator T)
    (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k)
    (V : Π x : M, TangentSpace I x) (x : M) :
    T (Function.update Y i (fun p => -V p)) x = -(T (Function.update Y i V) x) := by
  have h := hT.const_smul_slot Y i (-1) V x
  simpa [neg_one_smul] using h

theorem sub_slot (hT : IsTensorOperator T)
    (Y : Fin k → Π x : M, TangentSpace I x) (i : Fin k)
    (V W : Π x : M, TangentSpace I x) (x : M) :
    T (Function.update Y i (fun p => V p - W p)) x
      = T (Function.update Y i V) x - T (Function.update Y i W) x := by
  have h₁ : (fun p => V p - W p) = (fun p => V p + -W p) := by
    funext p; exact sub_eq_add_neg (V p) (W p)
  rw [h₁, hT.add_slot, hT.neg_slot, sub_eq_add_neg]

/-- Congruence: `T (update Y i V) = T (update Y i W)` whenever `V = W`. -/
theorem congr_slot {Y : Fin k → Π x : M, TangentSpace I x} {i : Fin k}
    {V W : Π x : M, TangentSpace I x} (h : V = W) (x : M) :
    T (Function.update Y i V) x = T (Function.update Y i W) x := by rw [h]

end IsTensorOperator

/-! ## The Lie derivative of a `(0,k)`-tensor -/

variable (I) in
/-- **Math.** The **Lie derivative of a `(0,k)`-tensor**: the first-order term of
the pullback `(Fᵗ)^*T` along the flow of `X`, realized (Prop. 2.1.2) by the
algebraic formula
`(L_X T)(Y₁, …, Y_k) = D_X(T(Y₁, …, Y_k)) − Σᵢ T(Y₁, …, [X, Yᵢ], …, Y_k)`. -/
def lieDerivativeTensor (X : Π x : M, TangentSpace I x) {k : ℕ}
    (T : TensorOperator I M k) : TensorOperator I M k :=
  fun Y => directionalDerivative X (T Y)
    - ∑ i, T (Function.update Y i (lieDerivativeVectorField I X (Y i)))

/-- **Math.** **Prop. 2.1.2**: the algebraic formula for the Lie derivative of a
`(0,k)`-tensor,
`(L_X T)(Y₁, …, Y_k) = D_X(T(Y₁, …, Y_k)) − Σᵢ T(Y₁, …, L_X Yᵢ, …, Y_k)`. -/
theorem lieDerivativeTensor_formula (X : Π x : M, TangentSpace I x) {k : ℕ}
    (T : TensorOperator I M k) (Y : Fin k → Π x : M, TangentSpace I x) (x : M) :
    lieDerivativeTensor I X T Y x
      = directionalDerivative X (T Y) x
        - ∑ i, T (Function.update Y i (lieDerivativeVectorField I X (Y i))) x := by
  simp [lieDerivativeTensor]

/-- The Lie derivative of a `(0,0)`-tensor (a function, evaluated on the empty
tuple) is the Lie derivative of the function. -/
theorem lieDerivativeTensor_zero_ary (X : Π x : M, TangentSpace I x)
    (T : TensorOperator I M 0) (Y : Fin 0 → Π x : M, TangentSpace I x) :
    lieDerivativeTensor I X T Y = lieDerivativeFunction X (T Y) := by
  funext x
  simp [lieDerivativeTensor_formula, lieDerivativeFunction]

section SmoothEval

variable [I.Boundaryless] [CompleteSpace E]

/-- The Lie derivative preserves smoothness of evaluations. -/
theorem lieDerivativeTensor_smooth_eval {X : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) {k : ℕ} {T : TensorOperator I M k}
    (hT : IsTensorOperator T)
    (Y : Fin k → Π x : M, TangentSpace I x) (hY : ∀ i, IsSmoothVectorField (Y i)) :
    ContMDiff I 𝓘(ℝ) ∞ (lieDerivativeTensor I X T Y) := by
  have h₁ : ContMDiff I 𝓘(ℝ) ∞ (directionalDerivative X (T Y)) :=
    hX.directionalDerivative_contMDiff (hT.smooth_eval Y hY)
  have h₂ : ∀ i : Fin k, ContMDiff I 𝓘(ℝ) ∞
      (T (Function.update Y i (lieDerivativeVectorField I X (Y i)))) := by
    intro i
    refine hT.smooth_eval _ (fun j => ?_)
    rcases eq_or_ne j i with rfl | hj
    · simpa using hX.lieDerivativeVectorField (hY j)
    · simpa [Function.update_of_ne hj] using hY j
  have hsum : ContMDiff I 𝓘(ℝ) ∞
      (fun x => ∑ i, T (Function.update Y i (lieDerivativeVectorField I X (Y i))) x) :=
    ContMDiff.sum (fun i _ => h₂ i)
  have : lieDerivativeTensor I X T Y
      = fun x => directionalDerivative X (T Y) x
        - ∑ i, T (Function.update Y i (lieDerivativeVectorField I X (Y i))) x := by
    funext x; simp [lieDerivativeTensor]
  rw [this]
  exact h₁.sub hsum

end SmoothEval

/-! ## Product rule (Prop. 2.1.3) -/

/-- **Math.** The **product of tensors**:
`(T₁·T₂)(X₁, …, X_{k₁}, Y₁, …, Y_{k₂}) = T₁(X₁, …, X_{k₁}) · T₂(Y₁, …, Y_{k₂})`. -/
def TensorOperator.mul {k₁ k₂ : ℕ} (T₁ : TensorOperator I M k₁)
    (T₂ : TensorOperator I M k₂) : TensorOperator I M (k₁ + k₂) :=
  fun Y x => T₁ (fun i => Y (Fin.castAdd k₂ i)) x * T₂ (fun j => Y (Fin.natAdd k₁ j)) x

theorem TensorOperator.mul_apply {k₁ k₂ : ℕ} (T₁ : TensorOperator I M k₁)
    (T₂ : TensorOperator I M k₂) (Y : Fin (k₁ + k₂) → Π x : M, TangentSpace I x) (x : M) :
    T₁.mul T₂ Y x
      = T₁ (fun i => Y (Fin.castAdd k₂ i)) x * T₂ (fun j => Y (Fin.natAdd k₁ j)) x := rfl

section ProductRule

variable {k₁ k₂ : ℕ} {T₁ : TensorOperator I M k₁} {T₂ : TensorOperator I M k₂}

/-- Updating a slot in the left factor block leaves the right block unchanged. -/
private theorem update_castAdd_natAdd (Y : Fin (k₁ + k₂) → Π x : M, TangentSpace I x)
    (i : Fin k₁) (V : Π x : M, TangentSpace I x) :
    (fun j => Function.update Y (Fin.castAdd k₂ i) V (Fin.natAdd k₁ j)) =
      fun j => Y (Fin.natAdd k₁ j) := by
  funext j
  refine Function.update_of_ne ?_ _ _
  intro h
  have := congrArg Fin.val h
  simp [Fin.coe_natAdd, Fin.coe_castAdd] at this
  omega

/-- Updating a slot in the right factor block leaves the left block unchanged. -/
private theorem update_natAdd_castAdd (Y : Fin (k₁ + k₂) → Π x : M, TangentSpace I x)
    (j : Fin k₂) (V : Π x : M, TangentSpace I x) :
    (fun i => Function.update Y (Fin.natAdd k₁ j) V (Fin.castAdd k₂ i)) =
      fun i => Y (Fin.castAdd k₂ i) := by
  funext i
  refine Function.update_of_ne ?_ _ _
  intro h
  have := congrArg Fin.val h
  simp [Fin.coe_natAdd, Fin.coe_castAdd] at this
  omega

private theorem update_castAdd_comp (Y : Fin (k₁ + k₂) → Π x : M, TangentSpace I x)
    (i : Fin k₁) (V : Π x : M, TangentSpace I x) :
    (fun i' => Function.update Y (Fin.castAdd k₂ i) V (Fin.castAdd k₂ i')) =
      Function.update (fun i' => Y (Fin.castAdd k₂ i')) i V := by
  funext i'
  rcases eq_or_ne i' i with rfl | hne
  · simp
  · rw [Function.update_of_ne hne,
      Function.update_of_ne (fun h => hne (Fin.castAdd_injective _ _ h))]

private theorem update_natAdd_comp (Y : Fin (k₁ + k₂) → Π x : M, TangentSpace I x)
    (j : Fin k₂) (V : Π x : M, TangentSpace I x) :
    (fun j' => Function.update Y (Fin.natAdd k₁ j) V (Fin.natAdd k₁ j')) =
      Function.update (fun j' => Y (Fin.natAdd k₁ j')) j V := by
  funext j'
  rcases eq_or_ne j' j with rfl | hne
  · simp
  · rw [Function.update_of_ne hne,
      Function.update_of_ne (fun h => hne (Fin.natAdd_injective _ _ h))]

/-- **Math.** **Prop. 2.1.3 (product rule)**:
`L_X(T₁·T₂) = (L_X T₁)·T₂ + T₁·(L_X T₂)`. -/
theorem lieDerivative_product_rule
    {X : Π x : M, TangentSpace I x}
    (hT₁ : IsTensorOperator T₁) (hT₂ : IsTensorOperator T₂)
    (Y : Fin (k₁ + k₂) → Π x : M, TangentSpace I x)
    (hY : ∀ i, IsSmoothVectorField (Y i)) (x : M) :
    lieDerivativeTensor I X (T₁.mul T₂) Y x
      = (lieDerivativeTensor I X T₁).mul T₂ Y x
        + T₁.mul (lieDerivativeTensor I X T₂) Y x := by
  set Yl : Fin k₁ → Π x : M, TangentSpace I x := fun i => Y (Fin.castAdd k₂ i) with hYl
  set Yr : Fin k₂ → Π x : M, TangentSpace I x := fun j => Y (Fin.natAdd k₁ j) with hYr
  have hYl_s : ∀ i, IsSmoothVectorField (Yl i) := fun i => hY _
  have hYr_s : ∀ j, IsSmoothVectorField (Yr j) := fun j => hY _
  have hT₁d : MDifferentiableAt I 𝓘(ℝ) (T₁ Yl) x :=
    ((hT₁.smooth_eval Yl hYl_s) x).mdifferentiableAt (by decide)
  have hT₂d : MDifferentiableAt I 𝓘(ℝ) (T₂ Yr) x :=
    ((hT₂.smooth_eval Yr hYr_s) x).mdifferentiableAt (by decide)
  -- the evaluation of the product is the product of the evaluations
  have hmul : T₁.mul T₂ Y = (T₁ Yl) * (T₂ Yr) := rfl
  -- expand the directional-derivative term by the Leibniz rule
  have hD : directionalDerivative X (T₁.mul T₂ Y) x
      = T₁ Yl x * directionalDerivative X (T₂ Yr) x
        + T₂ Yr x * directionalDerivative X (T₁ Yl) x := by
    rw [hmul]; exact directionalDerivative_mul hT₁d hT₂d X
  -- split the correction sum into the two blocks
  have hsum : ∑ i : Fin (k₁ + k₂),
        (T₁.mul T₂) (Function.update Y i (lieDerivativeVectorField I X (Y i))) x
      = (∑ i : Fin k₁,
          T₁ (Function.update Yl i (lieDerivativeVectorField I X (Yl i))) x) * T₂ Yr x
        + T₁ Yl x * ∑ j : Fin k₂,
            T₂ (Function.update Yr j (lieDerivativeVectorField I X (Yr j))) x := by
    rw [Fin.sum_univ_add]
    congr 1
    · rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [TensorOperator.mul_apply, update_castAdd_comp, update_castAdd_natAdd]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [TensorOperator.mul_apply, update_natAdd_comp, update_natAdd_castAdd]
  -- assemble
  have hL : lieDerivativeTensor I X (T₁.mul T₂) Y x
      = directionalDerivative X (T₁.mul T₂ Y) x
        - ∑ i, (T₁.mul T₂) (Function.update Y i (lieDerivativeVectorField I X (Y i))) x :=
    lieDerivativeTensor_formula ..
  rw [hL, hD, hsum]
  have h₁ : (lieDerivativeTensor I X T₁).mul T₂ Y x
      = (directionalDerivative X (T₁ Yl) x
          - ∑ i, T₁ (Function.update Yl i (lieDerivativeVectorField I X (Yl i))) x)
        * T₂ Yr x := by
    rw [TensorOperator.mul_apply]
    congr 1
    exact lieDerivativeTensor_formula ..
  have h₂ : T₁.mul (lieDerivativeTensor I X T₂) Y x
      = T₁ Yl x * (directionalDerivative X (T₂ Yr) x
          - ∑ j, T₂ (Function.update Yr j (lieDerivativeVectorField I X (Yr j))) x) := by
    rw [TensorOperator.mul_apply]
    congr 1
    exact lieDerivativeTensor_formula ..
  rw [h₁, h₂]
  ring

end ProductRule

/-! ## Lie derivative in a scaled direction (Prop. 2.1.4) -/

section ScaleDirection

variable [I.Boundaryless] [CompleteSpace E]

/-- **Math.** **Prop. 2.1.4**: the Lie derivative in the direction `fX`,
`(L_{fX} T)(Y₁, …, Y_k) = f·(L_X T)(Y₁, …, Y_k) + Σᵢ (L_{Yᵢ} f)·T(Y₁, …, X, …, Y_k)`,
with `X` replacing `Yᵢ` in the `i`th slot. -/
theorem lieDerivative_scale_direction
    {k : ℕ} {T : TensorOperator I M k} (hT : IsTensorOperator T)
    {X : Π x : M, TangentSpace I x} (hX : IsSmoothVectorField X)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (Y : Fin k → Π x : M, TangentSpace I x) (hY : ∀ i, IsSmoothVectorField (Y i))
    (x : M) :
    lieDerivativeTensor I (fun p => f p • X p) T Y x
      = f x * lieDerivativeTensor I X T Y x
        + ∑ i, directionalDerivative (Y i) f x * T (Function.update Y i X) x := by
  have hfd : ∀ p, MDifferentiableAt I 𝓘(ℝ) f p :=
    fun p => (hf p).mdifferentiableAt (by decide)
  have hXd : ∀ p, MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p :=
    fun p => (hX p).mdifferentiableAt (by decide)
  -- the bracket [fX, Yᵢ] as a field
  have hbr : ∀ i : Fin k, lieDerivativeVectorField I (fun p => f p • X p) (Y i)
      = fun p => (-(directionalDerivative (Y i) f p)) • X p
        + f p • lieDerivativeVectorField I X (Y i) p := by
    intro i
    funext p
    have hsm : (fun p => f p • X p) = f • X := rfl
    rw [lieDerivativeVectorField_eq_mlieBracket, hsm,
      VectorField.mlieBracket_smul_left (hfd p) (hXd p)]
    show _ • X p + f p • VectorField.mlieBracket I X (Y i) p = _
    congr 1
  -- expand both sides via the formula
  rw [lieDerivativeTensor_formula, lieDerivativeTensor_formula]
  -- directional-derivative term: D_{fX} = f·D_X
  have hDfX : directionalDerivative (fun p => f p • X p) (T Y) x
      = f x * directionalDerivative X (T Y) x :=
    directionalDerivative_smul_left f X (T Y) x
  -- each correction term splits
  have hterm : ∀ i : Fin k,
      T (Function.update Y i (lieDerivativeVectorField I (fun p => f p • X p) (Y i))) x
        = f x * T (Function.update Y i (lieDerivativeVectorField I X (Y i))) x
          - directionalDerivative (Y i) f x * T (Function.update Y i X) x := by
    intro i
    rw [IsTensorOperator.congr_slot (T := T) (hbr i)]
    rw [hT.add_slot]
    have h₁ : T (Function.update Y i
        (fun p => (-(directionalDerivative (Y i) f p)) • X p)) x
        = -(directionalDerivative (Y i) f x) * T (Function.update Y i X) x :=
      hT.smul_slot Y i (fun p => -(directionalDerivative (Y i) f p)) X x
    have h₂ : T (Function.update Y i
        (fun p => f p • lieDerivativeVectorField I X (Y i) p)) x
        = f x * T (Function.update Y i (lieDerivativeVectorField I X (Y i))) x :=
      hT.smul_slot Y i f (lieDerivativeVectorField I X (Y i)) x
    rw [h₁, h₂]
    ring
  rw [hDfX, Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_sub_distrib,
    ← Finset.mul_sum]
  ring

end ScaleDirection

/-! ## Locality at a zero of the direction (Lem. 2.1.5) -/

/-- **Math.** **Lem. 2.1.5**: if `X` vanishes at `x`, then `(L_X T)|_x` depends
only on the value of `T` at `x`: two tensors whose evaluations agree at `x` have
Lie derivatives agreeing at `x`. -/
theorem lieDerivative_local_at_zero
    {X : Π x : M, TangentSpace I x} {x : M} (hX : X x = 0)
    {k : ℕ} {T S : TensorOperator I M k}
    (hTS : ∀ Z : Fin k → Π x : M, TangentSpace I x, T Z x = S Z x)
    (Y : Fin k → Π x : M, TangentSpace I x) :
    lieDerivativeTensor I X T Y x = lieDerivativeTensor I X S Y x := by
  rw [lieDerivativeTensor_formula, lieDerivativeTensor_formula]
  have hD : ∀ g : M → ℝ, directionalDerivative X g x = 0 := by
    intro g
    rw [directionalDerivative_apply, hX]
    exact (mfderiv I 𝓘(ℝ) g x).map_zero
  rw [hD, hD]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hTS _)

end PetersenLib

import OpenGALib.Riemannian.Manifold.DoCarmoCh2

/-!
# do Carmo Chapter 4 interface — curvature

Faithful Lean interface for do Carmo's Chapter 4 (§2 Curvature, §3 Sectional
curvature). Building on the abstract affine connection `AffineConnection`
(Ch. 2, `def:dc-ch2-2-1`) and its Levi-Civita specialisation
(`thm:dc-ch2-3-6`), we introduce:

* the **curvature operator** `R(X,Y)Z = ∇_Y ∇_X Z − ∇_X ∇_Y Z + ∇_{[X,Y]} Z`
  (do Carmo's sign convention, `def:dc-ch4-2-1`);
* its `ℝ`-bilinearity in `(X, Y)` and additivity in `Z`, and antisymmetry
  `R(X,Y)Z = −R(Y,X)Z` (part of `prop:dc-ch4-2-5`);
* the **first Bianchi identity**
  `R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0` (`prop:dc-ch4-2-4`), for a *symmetric*
  connection, via the Jacobi identity for vector fields;
* the full `𝒟(M)`-linearity of `R` (`prop:dc-ch4-2-2`), including the
  tensoriality `R(X,Y)(fZ) = f R(X,Y)Z`;
* the four symmetries of the curvature 4-tensor `⟨R(X,Y)Z, T⟩`
  (`prop:dc-ch4-2-5`) for a Levi-Civita connection.

Vector fields are the bundled `SmoothVectorField I M` (`= 𝒳(M)`). The Lie
bracket `[X, Y]` is packaged as the smooth vector field `bracketField X Y`
using `DCLieBracket_contMDiffAt`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4 §2–§3.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The Lie bracket `[X, Y]` of two smooth vector fields, packaged as a
`SmoothVectorField I M`. Its underlying section is `p ↦ DCLieBracket X Y p`,
smooth by `DCLieBracket_contMDiffAt`. -/
noncomputable def bracketField (X Y : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun p => DCLieBracket X Y p
  smooth := fun p => DCLieBracket_contMDiffAt X Y p

@[simp] theorem bracketField_apply (X Y : SmoothVectorField I M) (p : M) :
    bracketField X Y p = DCLieBracket X Y p := rfl

/-- **Math.** `[X, Y] = −[Y, X]` at the level of the bundled bracket fields. -/
theorem bracketField_antisymm (X Y : SmoothVectorField I M) :
    bracketField X Y = -bracketField Y X := by
  ext p
  simp [DCLieBracket_antisymm X Y p]

/-- **Math.** `[X₁ + X₂, Y] = [X₁, Y] + [X₂, Y]` for bundled bracket fields. -/
theorem bracketField_add_left (X₁ X₂ Y : SmoothVectorField I M) :
    bracketField (X₁ + X₂) Y = bracketField X₁ Y + bracketField X₂ Y := by
  ext p
  simp only [bracketField_apply, SmoothVectorField.add_apply,
    DCLieBracket_add_left X₁ X₂ Y p]

/-- **Math.** `[X, Y₁ + Y₂] = [X, Y₁] + [X, Y₂]` for bundled bracket fields. -/
theorem bracketField_add_right (X Y₁ Y₂ : SmoothVectorField I M) :
    bracketField X (Y₁ + Y₂) = bracketField X Y₁ + bracketField X Y₂ := by
  ext p
  simp only [bracketField_apply, SmoothVectorField.add_apply,
    DCLieBracket_add_right X Y₁ Y₂ p]

/-- **Math.** do Carmo Ch. 0, Lemma 5.2, read on functions: the Lie bracket acts
on a smooth scalar `f` as the commutator of directional derivatives,
`[X,Y] f = X(Y f) − Y(X f)`, pointwise. This is the identity behind the
cancellation of the `∇_{[X,Y]}` term in the tensoriality of the curvature
(do Carmo Remark 2.3). -/
theorem bracketField_dir [I.Boundaryless] (X Y : SmoothVectorField I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) :
    (bracketField X Y).dir f p = X.dir (Y.dir f) p - Y.dir (X.dir f) p :=
  mfderiv_mlieBracket_eq_commutator X Y hf p

/-- **Math.** Bracket Leibniz in the first slot as an identity of vector fields:
`[fX, Y] = f [X, Y] − (Yf) X`. -/
theorem bracketField_smul_left {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) :
    bracketField (SmoothVectorField.smul f hf X) Y
      = SmoothVectorField.smul f hf (bracketField X Y)
        - SmoothVectorField.smul (Y.dir f) (Y.dir_contMDiff hf) X := by
  ext p
  simp only [bracketField_apply, SmoothVectorField.sub_apply,
    SmoothVectorField.smul_apply, DCLieBracket_smul_left hf X Y p]
  module

omit [CompleteSpace E] in
/-- **Math.** Homogeneity of the directional derivative under a constant scalar
factor of its function argument: `X(c·F) = c·X(F)`. -/
theorem SmoothVectorField.dir_const_mul (X : SmoothVectorField I M) (c : ℝ)
    {F : M → ℝ} (p : M) (hF : MDifferentiableAt I 𝓘(ℝ, ℝ) F p) :
    X.dir (fun q => c * F q) p = c * X.dir F p := by
  have h := X.dir_mul (f := fun _ => c) (h := F) p (mdifferentiableAt_const) hF
  have h0 : X.dir (fun _ : M => c) p = 0 := by
    simp only [SmoothVectorField.dir, mfderiv_const]; rfl
  rw [h, h0]; ring

namespace AffineConnection

/-! ### Algebraic identities of the covariant derivative

The connection is `𝒟(M)`-linear (hence in particular `ℝ`-linear, hence additive)
in its first slot and additive in its second slot. From the additive structure
we derive the behaviour on `0`, negation and subtraction of vector fields,
pointwise on tangent vectors. -/

variable (nabla : AffineConnection I M)

omit [CompleteSpace E] in
/-- `∇_0 Z = 0`, pointwise. -/
theorem cov_zero_left (Z : SmoothVectorField I M) (p : M) :
    (nabla.cov 0 Z) p = 0 := by
  have h := nabla.add_left 0 0 Z
  have e : (0 : SmoothVectorField I M) + 0 = 0 := by ext q; simp
  rw [e] at h
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  linear_combination (norm := module) -h'

omit [CompleteSpace E] in
/-- `∇_X 0 = 0`, pointwise. -/
theorem cov_zero_right (X : SmoothVectorField I M) (p : M) :
    (nabla.cov X 0) p = 0 := by
  have h := nabla.add_right X 0 0
  have e : (0 : SmoothVectorField I M) + 0 = 0 := by ext q; simp
  rw [e] at h
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  linear_combination (norm := module) -h'

omit [CompleteSpace E] in
/-- `∇_{-X} Z = −∇_X Z`, pointwise. -/
theorem cov_neg_left (X Z : SmoothVectorField I M) (p : M) :
    (nabla.cov (-X) Z) p = -(nabla.cov X Z) p := by
  have h := nabla.add_left (-X) X Z
  have e : (-X) + X = (0 : SmoothVectorField I M) := by ext q; simp
  rw [e] at h
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  rw [nabla.cov_zero_left Z p] at h'
  linear_combination (norm := module) -h'

omit [CompleteSpace E] in
/-- `∇_X (-Z) = −∇_X Z`, pointwise. -/
theorem cov_neg_right (X Z : SmoothVectorField I M) (p : M) :
    (nabla.cov X (-Z)) p = -(nabla.cov X Z) p := by
  have h := nabla.add_right X (-Z) Z
  have e : (-Z) + Z = (0 : SmoothVectorField I M) := by ext q; simp
  rw [e] at h
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  rw [nabla.cov_zero_right X p] at h'
  linear_combination (norm := module) -h'

omit [CompleteSpace E] in
/-- `∇_{X - Y} Z = ∇_X Z − ∇_Y Z`, pointwise. -/
theorem cov_sub_left (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.cov (X - Y) Z) p = (nabla.cov X Z) p - (nabla.cov Y Z) p := by
  have h := nabla.add_left (X - Y) Y Z
  have e : (X - Y) + Y = X := by ext q; simp
  rw [e] at h
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  linear_combination (norm := module) -h'

omit [CompleteSpace E] in
/-- `∇_X (Y - Z) = ∇_X Y − ∇_X Z`, pointwise. -/
theorem cov_sub_right (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.cov X (Y - Z)) p = (nabla.cov X Y) p - (nabla.cov X Z) p := by
  have h := nabla.add_right X (Y - Z) Z
  have e : (Y - Z) + Z = Y := by ext q; simp
  rw [e] at h
  have h' := congrArg (fun s : SmoothVectorField I M => s p) h
  simp only [SmoothVectorField.add_apply] at h'
  linear_combination (norm := module) -h'

/-! ### The curvature operator -/

/-- **Math.** do Carmo Ch. 4, Def. 2.1: the **curvature** `R` of the connection
`∇` associates to `X, Y ∈ 𝒳(M)` the operator `R(X,Y) : 𝒳(M) → 𝒳(M)`,

`R(X,Y)Z = ∇_Y ∇_X Z − ∇_X ∇_Y Z + ∇_{[X,Y]} Z`.

This is do Carmo's sign convention (some texts differ by a sign). The bracket
`[X, Y]` is the bundled `bracketField X Y`. -/
noncomputable def curvature (X Y Z : SmoothVectorField I M) : SmoothVectorField I M :=
  nabla.cov Y (nabla.cov X Z) - nabla.cov X (nabla.cov Y Z)
    + nabla.cov (bracketField X Y) Z

theorem curvature_apply (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y Z) p =
      (nabla.cov Y (nabla.cov X Z)) p - (nabla.cov X (nabla.cov Y Z)) p
        + (nabla.cov (bracketField X Y) Z) p := by
  simp only [curvature, SmoothVectorField.add_apply, SmoothVectorField.sub_apply]

/-- **Math.** do Carmo Ch. 4, Prop. 2.5(b): the curvature is **antisymmetric in
its first pair of arguments**, `R(X,Y)Z = −R(Y,X)Z`. This is immediate from the
definition: swapping `X, Y` flips the two double-covariant-derivative terms and
sends `[X,Y]` to `[Y,X] = −[X,Y]`. -/
theorem curvature_antisymm_left (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y Z) p = -(nabla.curvature Y X Z) p := by
  rw [curvature_apply, curvature_apply]
  have hbr : (nabla.cov (bracketField X Y) Z) p
      = -(nabla.cov (bracketField Y X) Z) p := by
    rw [bracketField_antisymm X Y]; exact nabla.cov_neg_left _ _ _
  rw [hbr]; module

/-- **Math.** do Carmo Ch. 4, Prop. 2.4 — the **first Bianchi identity**. For a
*symmetric* affine connection `∇` (`IsSymmetric`),

`R(X,Y)Z + R(Y,Z)X + R(Z,X)Y = 0`.

The proof regroups the six double-covariant-derivative terms into three
`∇_A [B,C]` terms using symmetry `∇_B W − ∇_W B = [B,W]`, pairs each with its
bracket-slot partner `∇_{[·,·]}·` to form nested brackets `[A,[B,C]]`, and closes
with the Jacobi identity for vector fields (`DCLieBracket_jacobi_cyclic`). -/
theorem curvature_bianchi (hsym : nabla.IsSymmetric)
    (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y Z) p + (nabla.curvature Y Z X) p
      + (nabla.curvature Z X Y) p = 0 := by
  -- symmetry as an identity of bundled vector fields
  have symm_field : ∀ A B : SmoothVectorField I M,
      nabla.cov A B - nabla.cov B A = bracketField A B := by
    intro A B; ext q
    simp only [SmoothVectorField.sub_apply, bracketField_apply]
    exact hsym A B q
  -- regroup: ∇_A(∇_B W) − ∇_A(∇_W B) = ∇_A[B,W]
  have G : ∀ A B W : SmoothVectorField I M,
      (nabla.cov A (nabla.cov B W)) p - (nabla.cov A (nabla.cov W B)) p
        = (nabla.cov A (bracketField B W)) p := by
    intro A B W
    rw [← nabla.cov_sub_right A (nabla.cov B W) (nabla.cov W B), symm_field B W]
  -- pair a double-derived bracket with its bracket-slot partner to form [A,[B,W]]
  have P : ∀ A B W : SmoothVectorField I M,
      (nabla.cov A (bracketField B W)) p + (nabla.cov (bracketField W B) A) p
        = DCLieBracket A (bracketField B W) p := by
    intro A B W
    have hbr : (nabla.cov (bracketField W B) A) p
        = -(nabla.cov (bracketField B W) A) p := by
      rw [bracketField_antisymm W B]; exact nabla.cov_neg_left _ _ _
    have h2 := congrArg (fun s : SmoothVectorField I M => s p)
      (symm_field A (bracketField B W))
    simp only [SmoothVectorField.sub_apply, bracketField_apply] at h2
    rw [hbr]; linear_combination (norm := module) h2
  -- Jacobi: [Y,[X,Z]] + [Z,[Y,X]] + [X,[Z,Y]] = 0
  have jac : DCLieBracket Y (bracketField X Z) p
      + DCLieBracket Z (bracketField Y X) p
      + DCLieBracket X (bracketField Z Y) p = 0 := by
    have hcyc := DCLieBracket_jacobi_cyclic X Z Y p
    have s1 : DCLieBracket Y (bracketField X Z) p
        = - VectorField.mlieBracket I
            (VectorField.mlieBracket I X.toFun Z.toFun) Y.toFun p := by
      show VectorField.mlieBracket I Y.toFun
        (VectorField.mlieBracket I X.toFun Z.toFun) p = _
      exact VectorField.mlieBracket_swap_apply
    have s2 : DCLieBracket Z (bracketField Y X) p
        = - VectorField.mlieBracket I
            (VectorField.mlieBracket I Y.toFun X.toFun) Z.toFun p := by
      show VectorField.mlieBracket I Z.toFun
        (VectorField.mlieBracket I Y.toFun X.toFun) p = _
      exact VectorField.mlieBracket_swap_apply
    have s3 : DCLieBracket X (bracketField Z Y) p
        = - VectorField.mlieBracket I
            (VectorField.mlieBracket I Z.toFun Y.toFun) X.toFun p := by
      show VectorField.mlieBracket I X.toFun
        (VectorField.mlieBracket I Z.toFun Y.toFun) p = _
      exact VectorField.mlieBracket_swap_apply
    rw [s1, s2, s3]; linear_combination (norm := module) -hcyc
  rw [curvature_apply, curvature_apply, curvature_apply]
  have gYXZ := G Y X Z
  have gZYX := G Z Y X
  have gXZY := G X Z Y
  have p1 := P Y X Z
  have p2 := P Z Y X
  have p3 := P X Z Y
  linear_combination (norm := module) gYXZ + gZYX + gXZY + p1 + p2 + p3 + jac

/-! ### Additive linearity of the curvature (do Carmo Prop. 2.2)

The `𝒟(M)`-bilinearity of `R` in `(X, Y)` (Prop. 2.2(i)) and the linearity of the
operator `R(X,Y)` (Prop. 2.2(ii)) split into additivity — established here — and
function-homogeneity (the genuine *tensoriality*, `R(X,Y)fZ = fR(X,Y)Z`), whose
`[X,Y]`-term cancellation is Remark 2.3. -/

/-- **Math.** Prop. 2.2(ii), additive part: `R(X,Y)` is additive in its argument,
`R(X,Y)(Z + W) = R(X,Y)Z + R(X,Y)W`. Uses only additivity of `∇` in the second
slot. -/
theorem curvature_add_right (X Y Z W : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y (Z + W)) p
      = (nabla.curvature X Y Z) p + (nabla.curvature X Y W) p := by
  rw [curvature_apply, curvature_apply, curvature_apply,
    nabla.add_right X Z W, nabla.add_right Y Z W,
    nabla.add_right Y (nabla.cov X Z) (nabla.cov X W),
    nabla.add_right X (nabla.cov Y Z) (nabla.cov Y W),
    nabla.add_right (bracketField X Y) Z W]
  simp only [SmoothVectorField.add_apply]; module

/-- **Math.** Prop. 2.2(i), additive part in the first slot:
`R(X₁ + X₂, Y)Z = R(X₁,Y)Z + R(X₂,Y)Z`. Uses additivity of `∇` in the first slot
and additivity of the Lie bracket. -/
theorem curvature_add_left (X₁ X₂ Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature (X₁ + X₂) Y Z) p
      = (nabla.curvature X₁ Y Z) p + (nabla.curvature X₂ Y Z) p := by
  rw [curvature_apply, curvature_apply, curvature_apply,
    nabla.add_left X₁ X₂ Z,
    nabla.add_right Y (nabla.cov X₁ Z) (nabla.cov X₂ Z),
    nabla.add_left X₁ X₂ (nabla.cov Y Z),
    bracketField_add_left X₁ X₂ Y,
    nabla.add_left (bracketField X₁ Y) (bracketField X₂ Y) Z]
  simp only [SmoothVectorField.add_apply]; module

/-- **Math.** Prop. 2.2(i), additive part in the second slot:
`R(X, Y₁ + Y₂)Z = R(X,Y₁)Z + R(X,Y₂)Z`. -/
theorem curvature_add_middle (X Y₁ Y₂ Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X (Y₁ + Y₂) Z) p
      = (nabla.curvature X Y₁ Z) p + (nabla.curvature X Y₂ Z) p := by
  rw [curvature_apply, curvature_apply, curvature_apply,
    nabla.add_left Y₁ Y₂ (nabla.cov X Z),
    nabla.add_left Y₁ Y₂ Z,
    nabla.add_right X (nabla.cov Y₁ Z) (nabla.cov Y₂ Z),
    bracketField_add_right X Y₁ Y₂,
    nabla.add_left (bracketField X Y₁) (bracketField X Y₂) Z]
  simp only [SmoothVectorField.add_apply]; module

/-! ### Tensoriality of the curvature in the last slot (do Carmo Prop. 2.2/Rem. 2.3)

`R(X,Y)(fZ) = f R(X,Y)Z`. Unlike the covariant derivative, `R` *is* a tensor:
the Leibniz second-derivative terms from `∇_Y∇_X(fZ) − ∇_X∇_Y(fZ)` are exactly
cancelled by the `∇_{[X,Y]}(fZ)` term, via the bracket-commutator
`[X,Y]f = X(Yf) − Y(Xf)`. This is the content of do Carmo's Remark 2.3. -/

omit [CompleteSpace E] in
/-- **Math.** Leibniz decomposition of `∇` in the second slot as an identity of
vector fields: `∇_A (f B) = f (∇_A B) + (Af) B`, where `Af = A.dir f` is the
directional derivative (a smooth scalar). -/
theorem cov_smul_right {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (A B : SmoothVectorField I M) :
    nabla.cov A (SmoothVectorField.smul f hf B)
      = SmoothVectorField.smul f hf (nabla.cov A B)
        + SmoothVectorField.smul (A.dir f) (A.dir_contMDiff hf) B := by
  ext p
  simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
  exact nabla.leibniz f hf A B p

/-- **Math.** do Carmo Ch. 4, Prop. 2.2(ii) — **tensoriality of the curvature in
its last argument**: `R(X,Y)(fZ) = f · R(X,Y)Z` for every smooth scalar `f`. The
first-order (`Af`, `Bf`) correction terms from the two double covariant
derivatives cancel against each other, and the second-order terms cancel against
the `∇_{[X,Y]}` term through the commutator `[X,Y]f = X(Yf) − Y(Xf)`
(`bracketField_dir`). -/
theorem curvature_smul_right [I.Boundaryless] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X Y (SmoothVectorField.smul f hf Z)) p
      = f p • (nabla.curvature X Y Z) p := by
  have hXfZ := nabla.cov_smul_right hf X Z
  have hYfZ := nabla.cov_smul_right hf Y Z
  -- `∇_Y ∇_X (fZ)` expanded pointwise
  have T1 : (nabla.cov Y (nabla.cov X (SmoothVectorField.smul f hf Z))) p
      = f p • (nabla.cov Y (nabla.cov X Z)) p + Y.dir f p • (nabla.cov X Z) p
        + X.dir f p • (nabla.cov Y Z) p + Y.dir (X.dir f) p • Z p := by
    rw [hXfZ, nabla.add_right, nabla.cov_smul_right hf Y (nabla.cov X Z),
      nabla.cov_smul_right (X.dir_contMDiff hf) Y Z]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]; module
  -- `∇_X ∇_Y (fZ)` expanded pointwise
  have T2 : (nabla.cov X (nabla.cov Y (SmoothVectorField.smul f hf Z))) p
      = f p • (nabla.cov X (nabla.cov Y Z)) p + X.dir f p • (nabla.cov Y Z) p
        + Y.dir f p • (nabla.cov X Z) p + X.dir (Y.dir f) p • Z p := by
    rw [hYfZ, nabla.add_right, nabla.cov_smul_right hf X (nabla.cov Y Z),
      nabla.cov_smul_right (Y.dir_contMDiff hf) X Z]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]; module
  -- `∇_{[X,Y]} (fZ)` expanded pointwise
  have T3 : (nabla.cov (bracketField X Y) (SmoothVectorField.smul f hf Z)) p
      = f p • (nabla.cov (bracketField X Y) Z) p + (bracketField X Y).dir f p • Z p := by
    rw [nabla.cov_smul_right hf (bracketField X Y) Z]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
  rw [curvature_apply, T1, T2, T3, curvature_apply, bracketField_dir X Y hf p]
  module

/-- **Math.** do Carmo Ch. 4, Prop. 2.2(i) — **homogeneity of the curvature in
its first argument**: `R(fX, Y)Z = f · R(X,Y)Z`. Here the `∇` first slot is
`𝒟(M)`-linear (no Leibniz correction), and the one first-order term `(Yf)∇_X Z`
produced by `∇_Y ∇_{fX} Z` is cancelled by the `−(Yf)X` part of `[fX, Y]` — no
commutator needed. -/
theorem curvature_smul_left {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature (SmoothVectorField.smul f hf X) Y Z) p
      = f p • (nabla.curvature X Y Z) p := by
  have s1 : (nabla.cov Y (nabla.cov (SmoothVectorField.smul f hf X) Z)) p
      = f p • (nabla.cov Y (nabla.cov X Z)) p + Y.dir f p • (nabla.cov X Z) p := by
    rw [nabla.smul_left f hf X Z, nabla.cov_smul_right hf Y (nabla.cov X Z)]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
  have s2 : (nabla.cov (SmoothVectorField.smul f hf X) (nabla.cov Y Z)) p
      = f p • (nabla.cov X (nabla.cov Y Z)) p := by
    rw [nabla.smul_left f hf X (nabla.cov Y Z)]
    simp only [SmoothVectorField.smul_apply]
  have s3 : (nabla.cov (bracketField (SmoothVectorField.smul f hf X) Y) Z) p
      = f p • (nabla.cov (bracketField X Y) Z) p - Y.dir f p • (nabla.cov X Z) p := by
    rw [bracketField_smul_left hf X Y, nabla.cov_sub_left,
      nabla.smul_left f hf (bracketField X Y) Z,
      nabla.smul_left (Y.dir f) (Y.dir_contMDiff hf) X Z]
    simp only [SmoothVectorField.smul_apply]
  rw [curvature_apply, s1, s2, s3, curvature_apply]
  module

/-- **Math.** do Carmo Ch. 4, Prop. 2.2(i) — **homogeneity of the curvature in
its second argument**: `R(X, fY)Z = f · R(X,Y)Z`. Immediate from
`curvature_smul_left` and the antisymmetry `R(X,Y) = −R(Y,X)`. -/
theorem curvature_smul_middle {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y Z : SmoothVectorField I M) (p : M) :
    (nabla.curvature X (SmoothVectorField.smul f hf Y) Z) p
      = f p • (nabla.curvature X Y Z) p := by
  rw [nabla.curvature_antisymm_left X (SmoothVectorField.smul f hf Y) Z,
    nabla.curvature_smul_left hf Y X Z, nabla.curvature_antisymm_left X Y Z]
  module

/-! ### Symmetries of `⟨R(X,Y)Z,T⟩` (do Carmo Prop. 2.5)

For a Levi-Civita (symmetric, metric-compatible) connection the curvature
4-tensor `(X,Y,Z,T) = ⟨R(X,Y)Z,T⟩` enjoys the four symmetries. Antisymmetry in
the first pair (b) is `curvature_antisymm_left`; the cyclic identity (a) is the
Bianchi identity. Here we add antisymmetry in the **second** pair (c) and the
**pair-swap** symmetry (d), both of which use metric compatibility. -/

section MetricSymmetry

variable [I.Boundaryless] (g : RiemannianMetric I M)

/-- **Math.** do Carmo Ch. 4, Prop. 2.5(c), key step: `⟨R(X,Y)Z, Z⟩ = 0` for a
metric-compatible connection. Using compatibility, `⟨∇_W Z, Z⟩ = ½ W⟨Z,Z⟩`, so
the two double-derivative terms become `½Y(X⟨Z,Z⟩) − ½X(Y⟨Z,Z⟩)` and the
`∇_{[X,Y]}` term becomes `½[X,Y]⟨Z,Z⟩ = ½(X(Y⟨Z,Z⟩) − Y(X⟨Z,Z⟩))`; they cancel. -/
theorem curvature_inner_self (hcompat : nabla.IsMetricCompatible g)
    (X Y Z : SmoothVectorField I M) (p : M) :
    g.metricInner p ((nabla.curvature X Y Z) p) (Z p) = 0 := by
  set hf : M → ℝ := fun r => g.metricInner r (Z r) (Z r) with hfdef
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ hf := g.metricInner_field_contMDiff Z Z
  have hXdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (X.dir hf) p :=
    (X.dir_contMDiff hf_smooth p).mdifferentiableAt (by simp)
  have hYdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (Y.dir hf) p :=
    (Y.dir_contMDiff hf_smooth p).mdifferentiableAt (by simp)
  -- ⟨∇_W Z, Z⟩ = ½ W⟨Z,Z⟩
  have hφ : ∀ (W : SmoothVectorField I M) (q : M),
      g.metricInner q ((nabla.cov W Z) q) (Z q) = (1/2) * W.dir hf q := by
    intro W q
    have hc : W.dir hf q = g.metricInner q ((nabla.cov W Z) q) (Z q)
        + g.metricInner q (Z q) ((nabla.cov W Z) q) := hcompat W Z Z q
    rw [g.metricInner_comm q (Z q) ((nabla.cov W Z) q)] at hc
    linarith [hc]
  have hψX : (fun q => g.metricInner q ((nabla.cov X Z) q) (Z q))
      = (fun q => (1/2) * X.dir hf q) := funext (hφ X)
  have hψY : (fun q => g.metricInner q ((nabla.cov Y Z) q) (Z q))
      = (fun q => (1/2) * Y.dir hf q) := funext (hφ Y)
  have hI1 : Y.dir (fun q => g.metricInner q ((nabla.cov X Z) q) (Z q)) p
      = g.metricInner p (nabla.cov Y (nabla.cov X Z) p) (Z p)
        + g.metricInner p ((nabla.cov X Z) p) (nabla.cov Y Z p) :=
    hcompat Y (nabla.cov X Z) Z p
  have hI2 : X.dir (fun q => g.metricInner q ((nabla.cov Y Z) q) (Z q)) p
      = g.metricInner p (nabla.cov X (nabla.cov Y Z) p) (Z p)
        + g.metricInner p ((nabla.cov Y Z) p) (nabla.cov X Z p) :=
    hcompat X (nabla.cov Y Z) Z p
  rw [hψX, Y.dir_const_mul (1/2) p hXdiff] at hI1
  rw [hψY, X.dir_const_mul (1/2) p hYdiff] at hI2
  rw [curvature_apply, RiemannianMetric.metricInner_add_left,
    RiemannianMetric.metricInner_sub_left,
    hφ (bracketField X Y) p, bracketField_dir X Y hf_smooth p]
  have e1 : g.metricInner p (nabla.cov Y (nabla.cov X Z) p) (Z p)
      = (1/2) * Y.dir (X.dir hf) p
        - g.metricInner p ((nabla.cov X Z) p) (nabla.cov Y Z p) := by linarith [hI1]
  have e2 : g.metricInner p (nabla.cov X (nabla.cov Y Z) p) (Z p)
      = (1/2) * X.dir (Y.dir hf) p
        - g.metricInner p ((nabla.cov Y Z) p) (nabla.cov X Z p) := by linarith [hI2]
  rw [e1, e2, g.metricInner_comm p ((nabla.cov X Z) p) (nabla.cov Y Z p)]
  ring

/-- **Math.** do Carmo Ch. 4, Prop. 2.5(c): antisymmetry of the curvature
4-tensor in its **second pair** of arguments,
`⟨R(X,Y)Z, T⟩ = −⟨R(X,Y)T, Z⟩`. Polarize `⟨R(X,Y)(Z+T), Z+T⟩ = 0`. -/
theorem curvature_inner_antisymm_right (hcompat : nabla.IsMetricCompatible g)
    (X Y Z T : SmoothVectorField I M) (p : M) :
    g.metricInner p ((nabla.curvature X Y Z) p) (T p)
      = -g.metricInner p ((nabla.curvature X Y T) p) (Z p) := by
  have h0 := nabla.curvature_inner_self g hcompat X Y (Z + T) p
  have hZ := nabla.curvature_inner_self g hcompat X Y Z p
  have hT := nabla.curvature_inner_self g hcompat X Y T p
  rw [nabla.curvature_add_right X Y Z T] at h0
  simp only [SmoothVectorField.add_apply, RiemannianMetric.metricInner_add_left,
    RiemannianMetric.metricInner_add_right] at h0
  linarith [h0, hZ, hT]

/-- **Math.** do Carmo Ch. 4, Prop. 2.5: the curvature 4-tensor
`(X,Y,Z,T) = ⟨R(X,Y)Z, T⟩`. -/
def curvatureForm (X Y Z T : SmoothVectorField I M) (p : M) : ℝ :=
  g.metricInner p ((nabla.curvature X Y Z) p) (T p)

omit [I.Boundaryless] in
/-- **Math.** Prop. 2.5(b) on the 4-tensor: `(X,Y,Z,T) = −(Y,X,Z,T)`. -/
theorem curvatureForm_antisymm_left (X Y Z T : SmoothVectorField I M) (p : M) :
    nabla.curvatureForm g X Y Z T p = -nabla.curvatureForm g Y X Z T p := by
  simp only [curvatureForm, nabla.curvature_antisymm_left X Y Z,
    RiemannianMetric.metricInner_neg_left]

/-- **Math.** Prop. 2.5(c) on the 4-tensor: `(X,Y,Z,T) = −(X,Y,T,Z)`. -/
theorem curvatureForm_antisymm_right (hcompat : nabla.IsMetricCompatible g)
    (X Y Z T : SmoothVectorField I M) (p : M) :
    nabla.curvatureForm g X Y Z T p = -nabla.curvatureForm g X Y T Z p :=
  nabla.curvature_inner_antisymm_right g hcompat X Y Z T p

omit [I.Boundaryless] in
/-- **Math.** Prop. 2.5(a) on the 4-tensor (Bianchi):
`(X,Y,Z,T) + (Y,Z,X,T) + (Z,X,Y,T) = 0`. -/
theorem curvatureForm_bianchi (hsym : nabla.IsSymmetric)
    (X Y Z T : SmoothVectorField I M) (p : M) :
    nabla.curvatureForm g X Y Z T p + nabla.curvatureForm g Y Z X T p
      + nabla.curvatureForm g Z X Y T p = 0 := by
  have hb := nabla.curvature_bianchi hsym X Y Z p
  simp only [curvatureForm]
  rw [← RiemannianMetric.metricInner_add_left,
    ← RiemannianMetric.metricInner_add_left, hb,
    RiemannianMetric.metricInner_zero_left]

/-- **Math.** do Carmo Ch. 4, Prop. 2.5(d) — **pair-swap symmetry** of the
curvature 4-tensor: `(X,Y,Z,T) = (Z,T,X,Y)`. Obtained (do Carmo's argument) by
summing the four cyclic Bianchi identities and cancelling with (b), (c). -/
theorem curvatureForm_pairSwap (hsym : nabla.IsSymmetric)
    (hcompat : nabla.IsMetricCompatible g)
    (X Y Z T : SmoothVectorField I M) (p : M) :
    nabla.curvatureForm g X Y Z T p = nabla.curvatureForm g Z T X Y p := by
  have Eq1 := nabla.curvatureForm_bianchi g hsym Y Z X T p
  have Eq2 := nabla.curvatureForm_bianchi g hsym Z X T Y p
  have Eq3 := nabla.curvatureForm_bianchi g hsym X T Y Z p
  have Eq4 := nabla.curvatureForm_bianchi g hsym T Y Z X p
  have ar1 := nabla.curvatureForm_antisymm_right g hcompat Y Z X T p
  have ar2 := nabla.curvatureForm_antisymm_right g hcompat Z X Y T p
  have ar3 := nabla.curvatureForm_antisymm_right g hcompat X T Z Y p
  have ar4 := nabla.curvatureForm_antisymm_right g hcompat T Y Z X p
  have ar5 := nabla.curvatureForm_antisymm_right g hcompat X Y Z T p
  have ar6 := nabla.curvatureForm_antisymm_right g hcompat T Z X Y p
  have al5 := nabla.curvatureForm_antisymm_left g Y X T Z p
  have al6 := nabla.curvatureForm_antisymm_left g Z T Y X p
  have al7 := nabla.curvatureForm_antisymm_left g T Z X Y p
  linarith [Eq1, Eq2, Eq3, Eq4, ar1, ar2, ar3, ar4, ar5, ar6, al5, al6, al7]

end MetricSymmetry

end AffineConnection

end Riemannian

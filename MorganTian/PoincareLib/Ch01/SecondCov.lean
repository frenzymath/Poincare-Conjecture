import PoincareLib.Ch01.CurvatureTensor
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Locality

/-!
# Poincaré Ch. 1 — the second covariant derivative and the Ricci commutation
identity

Morgan–Tian introduce, for a vector field `Z` (and more generally any tensor),
the **second covariant derivative**
`∇²Z(X, Y) = ∇_X (∇_Y Z) − ∇_{∇_X Y} Z`
(blueprint Ch. 1, discussion preceding `lem:laplacian-one-form`), and record
that it is tensorial in the two direction slots and that its antisymmetrization
in `X, Y` is the curvature:
`∇²Z(X, Y) − ∇²Z(Y, X) = ℛ_MT(X, Y) Z` (the **Ricci commutation identity**),
where `ℛ_MT` is Morgan–Tian's curvature operator `PoincareLib.riemannCurvature`.

This file provides that engine on vector fields:

* `secondCov nabla X Y Z` — the second covariant derivative, as a smooth
  vector field;
* tensoriality in the direction slots: additivity (`secondCov_add_left`,
  `secondCov_add_middle`) and `𝒟(M)`-homogeneity (`secondCov_smul_left`,
  `secondCov_smul_middle`) — for the middle slot the two Leibniz cross terms
  `X(φ)·∇_Y Z` cancel exactly, which is the point of the `− ∇_{∇_X Y} Z`
  correction;
* pointwise locality in the outer direction slot (`secondCov_congr_left`):
  `∇²Z(X, Y)(p)` depends on `X` only through `X(p)` — by applying the
  direction-slot locality of `∇` (`AffineConnection.cov_congr_apply_left`)
  twice;
* the **Ricci commutation identity** (`secondCov_sub_swap`,
  `secondCov_sub_swap_apply`) for a torsion-free connection.

These feed the Bochner formula for functions (blueprint Ch. 2,
`lem:laplacian-square-norm-one-form`, `lem:function-bochner-formula`) and the
connection Laplacian on one-tensors (blueprint Ch. 1,
`lem:laplacian-one-form`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1
(discussion preceding eq. `lapformula`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The **second covariant derivative** of a vector field `Z` in the
directions `X, Y`:
`∇²Z(X, Y) = ∇_X (∇_Y Z) − ∇_{∇_X Y} Z`.
The correction term `− ∇_{∇_X Y} Z` makes the expression tensorial in both
direction slots (`secondCov_smul_left`, `secondCov_smul_middle`).
Blueprint: Ch. 1, discussion preceding `lem:laplacian-one-form`. -/
def secondCov (nabla : AffineConnection I M) (X Y Z : SmoothVectorField I M) :
    SmoothVectorField I M :=
  nabla.cov X (nabla.cov Y Z) - nabla.cov (nabla.cov X Y) Z

omit [CompleteSpace E] in
/-- **Math.** Unfolding lemma for the second covariant derivative.
Blueprint: Ch. 1, discussion preceding `lem:laplacian-one-form`. -/
@[simp] theorem secondCov_apply (nabla : AffineConnection I M)
    (X Y Z : SmoothVectorField I M) (p : M) :
    secondCov nabla X Y Z p
      = (nabla.cov X (nabla.cov Y Z)) p - (nabla.cov (nabla.cov X Y) Z) p :=
  rfl

/-! ### Tensoriality in the direction slots -/

omit [CompleteSpace E] in
/-- **Math.** The second covariant derivative is additive in the outer
direction slot. Blueprint: Ch. 1, discussion preceding
`lem:laplacian-one-form`. -/
theorem secondCov_add_left (nabla : AffineConnection I M)
    (X X' Y Z : SmoothVectorField I M) :
    secondCov nabla (X + X') Y Z = secondCov nabla X Y Z + secondCov nabla X' Y Z := by
  ext p
  simp only [secondCov_apply, SmoothVectorField.add_apply, nabla.add_left]
  abel

omit [CompleteSpace E] in
/-- **Math.** The second covariant derivative is `𝒟(M)`-homogeneous in the
outer direction slot: `∇²Z(φX, Y) = φ · ∇²Z(X, Y)`. Blueprint: Ch. 1,
discussion preceding `lem:laplacian-one-form`. -/
theorem secondCov_smul_left (nabla : AffineConnection I M) {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (X Y Z : SmoothVectorField I M) :
    secondCov nabla (SmoothVectorField.smul φ hφ X) Y Z
      = SmoothVectorField.smul φ hφ (secondCov nabla X Y Z) := by
  ext p
  simp only [secondCov_apply, nabla.smul_left φ hφ,
    SmoothVectorField.smul_apply, smul_sub]

omit [CompleteSpace E] in
/-- **Math.** The second covariant derivative is additive in the middle
(inner) direction slot. Blueprint: Ch. 1, discussion preceding
`lem:laplacian-one-form`. -/
theorem secondCov_add_middle (nabla : AffineConnection I M)
    (X Y Y' Z : SmoothVectorField I M) :
    secondCov nabla X (Y + Y') Z = secondCov nabla X Y Z + secondCov nabla X Y' Z := by
  ext p
  simp only [secondCov_apply, nabla.add_left, nabla.add_right,
    SmoothVectorField.add_apply]
  abel

omit [CompleteSpace E] in
/-- **Math.** The second covariant derivative is `𝒟(M)`-homogeneous in the
middle direction slot: `∇²Z(X, φY) = φ · ∇²Z(X, Y)`. The two Leibniz cross
terms `X(φ) · ∇_Y Z` — one from `∇_X (∇_{φY} Z) = ∇_X (φ ∇_Y Z)` and one from
`∇_{∇_X (φY)} Z = ∇_{φ ∇_X Y + X(φ) Y} Z` — cancel exactly; this cancellation
is the reason for the correction term in the definition. Blueprint: Ch. 1,
discussion preceding `lem:laplacian-one-form`. -/
theorem secondCov_smul_middle (nabla : AffineConnection I M) {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (X Y Z : SmoothVectorField I M) :
    secondCov nabla X (SmoothVectorField.smul φ hφ Y) Z
      = SmoothVectorField.smul φ hφ (secondCov nabla X Y Z) := by
  have h₁ : nabla.cov (SmoothVectorField.smul φ hφ Y) Z
      = SmoothVectorField.smul φ hφ (nabla.cov Y Z) :=
    nabla.smul_left φ hφ Y Z
  have h₂ : nabla.cov X (SmoothVectorField.smul φ hφ Y)
      = SmoothVectorField.smul φ hφ (nabla.cov X Y)
        + SmoothVectorField.smul (X.dir φ) (X.dir_contMDiff hφ) Y :=
    nabla.cov_smul_right hφ X Y
  ext p
  have hout := nabla.cov_smul_right hφ X (nabla.cov Y Z)
  have happ : (nabla.cov X (nabla.cov (SmoothVectorField.smul φ hφ Y) Z)) p
      = φ p • (nabla.cov X (nabla.cov Y Z)) p
        + X.dir φ p • (nabla.cov Y Z) p := by
    rw [h₁, hout]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
  have hin : (nabla.cov (nabla.cov X (SmoothVectorField.smul φ hφ Y)) Z) p
      = φ p • (nabla.cov (nabla.cov X Y) Z) p
        + X.dir φ p • (nabla.cov Y Z) p := by
    rw [h₂, nabla.add_left, nabla.smul_left φ hφ,
      nabla.smul_left (X.dir φ) (X.dir_contMDiff hφ)]
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
  simp only [secondCov_apply, SmoothVectorField.smul_apply, happ, hin, smul_sub]
  abel

omit [CompleteSpace E] in
/-- **Math.** **Pointwise locality of `∇²Z(X, Y)` in the outer direction
slot**: the value at `p` depends on `X` only through `X(p)`. Both terms of the
definition are covariant derivatives in the direction `X` — of `∇_Y Z` and,
after locality of `∇_X Y` itself, of `Z` — so the direction-slot locality of
`∇` (`AffineConnection.cov_congr_apply_left`) applies to each. Blueprint:
Ch. 1, discussion preceding `lem:laplacian-one-form`. -/
theorem secondCov_congr_left [FiniteDimensional ℝ E] [SigmaCompactSpace M]
    [T2Space M] (nabla : AffineConnection I M) {X X' : SmoothVectorField I M}
    (Y Z : SmoothVectorField I M) {p : M} (h : X p = X' p) :
    secondCov nabla X Y Z p = secondCov nabla X' Y Z p := by
  have h₁ : (nabla.cov X (nabla.cov Y Z)) p = (nabla.cov X' (nabla.cov Y Z)) p :=
    nabla.cov_congr_apply_left (nabla.cov Y Z) h
  have h₂ : (nabla.cov X Y) p = (nabla.cov X' Y) p :=
    nabla.cov_congr_apply_left Y h
  have h₃ : (nabla.cov (nabla.cov X Y) Z) p = (nabla.cov (nabla.cov X' Y) Z) p :=
    nabla.cov_congr_apply_left Z h₂
  simp only [secondCov_apply, h₁, h₃]

omit [CompleteSpace E] in
/-- **Math.** Covariant derivatives commute with *constant* scalar multiples:
`∇_X (c • W) = c • ∇_X W`. The Leibniz cross term `X(c) • W` vanishes because
the derivative of a constant is zero. Blueprint: `thm:levi-civita-connection`
(connection algebra). -/
theorem cov_constSMul_right (nabla : AffineConnection I M) (c : ℝ)
    (X W : SmoothVectorField I M) :
    nabla.cov X (c • W) = c • nabla.cov X W := by
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => c) := contMDiff_const
  have h : c • W = SmoothVectorField.smul (fun _ => c) hconst W := by
    ext q; rfl
  rw [h, nabla.cov_smul_right hconst X W]
  ext q
  have hdir : X.dir (fun _ : M => c) q = 0 := by
    simp only [SmoothVectorField.dir, mfderiv_const]
    rfl
  show (SmoothVectorField.smul _ hconst (nabla.cov X W)) q
      + (SmoothVectorField.smul (X.dir fun _ => c) _ W) q
    = c • (nabla.cov X W) q
  rw [SmoothVectorField.smul_apply, SmoothVectorField.smul_apply, hdir,
    zero_smul, add_zero]

/-! ### The Ricci commutation identity -/

/-- **Math.** For a torsion-free connection, `∇_X Y − ∇_Y X = [X, Y]` at the
level of bundled smooth vector fields. Blueprint: `thm:levi-civita-connection`
(torsion-freeness). -/
theorem cov_sub_cov_swap_of_isSymmetric {nabla : AffineConnection I M}
    (hsym : nabla.IsSymmetric) (X Y : SmoothVectorField I M) :
    nabla.cov X Y - nabla.cov Y X = bracketField X Y := by
  ext q
  rw [SmoothVectorField.sub_apply, bracketField_apply]
  exact hsym X Y q

/-- **Math.** The **Ricci commutation identity** for vector fields: for a
torsion-free connection,
`∇²Z(X, Y) − ∇²Z(Y, X) = ℛ_MT(X, Y) Z`.
Indeed the double-derivative terms of the two sides match by definition of
`riemannCurvature`, while the correction terms combine, via torsion-freeness
`∇_X Y − ∇_Y X = [X, Y]` and additivity of `∇` in its direction slot, into
`∇_{[X,Y]} Z`. Blueprint: Ch. 1, discussion preceding
`lem:laplacian-one-form`. -/
theorem secondCov_sub_swap {nabla : AffineConnection I M}
    (hsym : nabla.IsSymmetric) (X Y Z : SmoothVectorField I M) :
    secondCov nabla X Y Z - secondCov nabla Y X Z
      = riemannCurvature nabla X Y Z := by
  ext p
  have hbr : (nabla.cov (bracketField X Y) Z) p
      = (nabla.cov (nabla.cov X Y) Z) p - (nabla.cov (nabla.cov Y X) Z) p := by
    rw [← cov_sub_cov_swap_of_isSymmetric hsym X Y, nabla.cov_sub_left]
  simp only [SmoothVectorField.sub_apply, secondCov_apply, riemannCurvature,
    hbr]
  abel

/-- **Math.** Pointwise form of the Ricci commutation identity
(`secondCov_sub_swap`). Blueprint: Ch. 1, discussion preceding
`lem:laplacian-one-form`. -/
theorem secondCov_sub_swap_apply {nabla : AffineConnection I M}
    (hsym : nabla.IsSymmetric) (X Y Z : SmoothVectorField I M) (p : M) :
    secondCov nabla X Y Z p - secondCov nabla Y X Z p
      = riemannCurvature nabla X Y Z p := by
  rw [← SmoothVectorField.sub_apply, secondCov_sub_swap hsym]

end PoincareLib

end

import PetersenLib.Ch02.LieDerivative

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.2 (regularity of skew-symmetry and Jacobi)

Petersen's Exercise 2.5.2 asks to show that the skew-symmetry property
`[X, Y] = -[Y, X]` does *not* necessarily hold for `C¹` vector fields, and that
the Jacobi identity *does* hold for `C²` vector fields.

## Mathematical content and what is formalized

Petersen defines `[X, Y]` primarily as the *flow-defined* Lie derivative
`L_X Y = d/dt|₀ (F^{-t})_* Y` (§2.1, `lieDerivative_vectorField_eq_bracket`).
Its identification with the manifestly antisymmetric *coordinate commutator*
`[X, Y] = (Xⁱ ∂ᵢ Yʲ − Yⁱ ∂ᵢ Xʲ) ∂ⱼ` is Proposition 2.1.1, whose proof
differentiates the flow's Jacobian to first order and interchanges derivatives —
a Schwarz/Clairaut commutation that only holds once the data is `C²`. It is this
identification, not skew-symmetry of any single fixed formula, that breaks below
`C²`; the skew-symmetry failure Petersen refers to is therefore a feature of the
flow-defined bracket, whose formalization would require the differentiation
theory of flows of merely-`C¹` vector fields (not available in Mathlib).

For the *coordinate* bracket used throughout this formalization — Mathlib's
`VectorField.mlieBracket`, equal to `lieDerivativeVectorField` — skew-symmetry
holds unconditionally (`VectorField.mlieBracket_swap`, needing no regularity),
so there is no counterexample at this level; see `exercise2_5_2_skew`.

The substantive, coordinate-independent content of the exercise is the **Jacobi
identity for `C²` vector fields**, formalized here as `exercise2_5_2` (Leibniz
form) and `exercise2_5_2_cyclic` (the classical cyclic form). The `C²`
hypothesis is exactly Petersen's, and is genuinely used: it is the smoothness at
which Mathlib's `VectorField.leibniz_identity_mlieBracket` becomes available
(`minSmoothness ℝ 2 = 2`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), Exercise 2.5.2, p. 88.
-/

open Bundle Set Function
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Eng.** A vector field is `C²` when the associated section of the tangent
bundle is `C²`. This is the `C²` analogue of `IsSmoothVectorField`; it is the
regularity Petersen singles out for the Jacobi identity in Exercise 2.5.2. -/
def IsC2VectorField (X : Π x : M, TangentSpace I x) : Prop :=
  ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (fun x => (⟨x, X x⟩ : TangentBundle I M))

omit [CompleteSpace E] in
theorem IsSmoothVectorField.isC2VectorField {X : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) : IsC2VectorField X :=
  hX.of_le (by norm_cast)

omit [CompleteSpace E] in
/-- Bridge to Mathlib's `leibniz_identity_mlieBracket_apply` hypothesis
`ContMDiffAt … (minSmoothness ℝ 2) …`, which for `ℝ` is just `C²`. -/
private theorem IsC2VectorField.contMDiffAt_minSmoothness
    {X : Π x : M, TangentSpace I x} (hX : IsC2VectorField X) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := by
  rw [minSmoothness_of_isRCLikeNormedField]
  exact hX.contMDiffAt

omit [CompleteSpace E] [IsManifold I ∞ M] in
/-- **Skew-symmetry holds for the coordinate bracket, unconditionally.**
For the coordinate Lie bracket `[X, Y] = L_X Y` used in this formalization,
`[X, Y] = -[Y, X]` holds for *all* vector fields, with no regularity hypothesis
whatsoever. Consequently the `C¹`-failure of skew-symmetry that Petersen's
Exercise 2.5.2 refers to concerns the flow definition of the bracket, not this
coordinate commutator (see the module docstring). -/
theorem exercise2_5_2_skew (X Y : Π x : M, TangentSpace I x) :
    lieDerivativeVectorField I X Y = -lieDerivativeVectorField I Y X :=
  VectorField.mlieBracket_swap

omit [CompleteSpace E] [IsManifold I ∞ M] in
theorem exercise2_5_2_skew_apply (X Y : Π x : M, TangentSpace I x) (p : M) :
    lieDerivativeVectorField I X Y p = -lieDerivativeVectorField I Y X p :=
  VectorField.mlieBracket_swap_apply

/-- **Exercise 2.5.2 — the Jacobi identity for `C²` vector fields (Leibniz form).**
For `C²` vector fields `X, Y, W` the Lie bracket satisfies
`[X, [Y, W]] = [[X, Y], W] + [Y, [X, W]]`. This is the substantive content of the
exercise; the `C²` hypothesis is exactly the regularity at which the underlying
Schwarz symmetry of second derivatives (used in the identification of the bracket
with the coordinate commutator) is available. -/
theorem exercise2_5_2 {X Y W : Π x : M, TangentSpace I x}
    (hX : IsC2VectorField X) (hY : IsC2VectorField Y) (hW : IsC2VectorField W) :
    lieDerivativeVectorField I X (lieDerivativeVectorField I Y W)
      = fun p => lieDerivativeVectorField I (lieDerivativeVectorField I X Y) W p
        + lieDerivativeVectorField I Y (lieDerivativeVectorField I X W) p := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  funext p
  simpa [lieDerivativeVectorField] using
    VectorField.leibniz_identity_mlieBracket_apply
      (hX.contMDiffAt_minSmoothness p) (hY.contMDiffAt_minSmoothness p)
      (hW.contMDiffAt_minSmoothness p)

/-- The Lie bracket of two `C²` vector fields is `C¹`, hence differentiable — the
regularity needed to move `-` across the outer bracket in the cyclic Jacobi
identity. -/
private theorem mdifferentiableAt_bracket {X W : Π x : M, TangentSpace I x}
    (hX : IsC2VectorField X) (hW : IsC2VectorField W) (p : M) :
    MDifferentiableAt I (I.prod 𝓘(ℝ, E))
      (fun q => (⟨q, lieDerivativeVectorField I X W q⟩ : TangentBundle I M)) p := by
  have hman : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  rw [minSmoothness_of_isRCLikeNormedField] at hman
  haveI : IsManifold I ((2 : ℕ∞) + 1) M := hman
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hX2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
      (fun q => (⟨q, X q⟩ : TangentBundle I M)) p := hX.contMDiffAt
  have hW2 : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (2 : ℕ∞)
      (fun q => (⟨q, W q⟩ : TangentBundle I M)) p := hW.contMDiffAt
  have hmn : minSmoothness ℝ ((1 : ℕ∞) + 1) ≤ (2 : ℕ∞) := by
    rw [minSmoothness_of_isRCLikeNormedField]; exact le_rfl
  have hb : ContMDiffAt I (I.prod 𝓘(ℝ, E)) (1 : ℕ∞)
      (fun q => (⟨q, VectorField.mlieBracket I X W q⟩ : TangentBundle I M)) p :=
    ContMDiffAt.mlieBracket_vectorField (m := 1) (n := 2) hX2 hW2 hmn
  exact hb.mdifferentiableAt (by norm_num)

/-- **Exercise 2.5.2 — the Jacobi identity for `C²` vector fields (cyclic form).**
For `C²` vector fields `X, Y, W`,
`[X, [Y, W]] + [Y, [W, X]] + [W, [X, Y]] = 0`. This is the classical Jacobi
identity; it follows from the Leibniz form `exercise2_5_2` together with
skew-symmetry of the coordinate bracket (`exercise2_5_2_skew`). -/
theorem exercise2_5_2_cyclic {X Y W : Π x : M, TangentSpace I x}
    (hX : IsC2VectorField X) (hY : IsC2VectorField Y) (hW : IsC2VectorField W) :
    (fun p => lieDerivativeVectorField I X (lieDerivativeVectorField I Y W) p
        + lieDerivativeVectorField I Y (lieDerivativeVectorField I W X) p
        + lieDerivativeVectorField I W (lieDerivativeVectorField I X Y) p) = 0 := by
  haveI : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  have hL := exercise2_5_2 hX hY hW
  funext p
  have hLp := congrFun hL p
  -- Move `-` across the outer bracket of the two "reversed" terms via skew-symmetry.
  have e1 : lieDerivativeVectorField I W (lieDerivativeVectorField I X Y) p
      = -lieDerivativeVectorField I (lieDerivativeVectorField I X Y) W p :=
    exercise2_5_2_skew_apply _ _ p
  have e2 : lieDerivativeVectorField I Y (lieDerivativeVectorField I W X) p
      = -lieDerivativeVectorField I Y (lieDerivativeVectorField I X W) p := by
    rw [show lieDerivativeVectorField I W X = (-1 : ℝ) • lieDerivativeVectorField I X W from by
        rw [exercise2_5_2_skew]; ext q; simp]
    rw [show lieDerivativeVectorField I Y ((-1 : ℝ) • lieDerivativeVectorField I X W) p
        = VectorField.mlieBracket I Y ((-1 : ℝ) • lieDerivativeVectorField I X W) p from rfl,
      VectorField.mlieBracket_const_smul_right (mdifferentiableAt_bracket hX hW p)]
    simp [lieDerivativeVectorField]
  simp only [Pi.zero_apply]
  rw [e1, e2, hLp]
  abel

end PetersenLib

import PetersenLib.Ch02.CovariantDerivative

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.25 (second fundamental form)

For an isometric immersion `F : (M, g_M) ↪ (M̃, g_{M̃})` the ambient covariant
derivative `∇^{M̃}_X Y` of two tangent fields splits into a tangential part —
which is the induced connection `∇^M_X Y` — and a normal part, the **second
fundamental form** `II(X, Y) = ∇^{M̃}_X Y − ∇^M_X Y`.  Exercise 2.5.25 asks to
show `II` is symmetric and tensorial.

Both properties are *algebraic*, depending only on the two connections through
their difference: for **any** two affine connections `∇¹, ∇²` on a manifold,
the difference `(X, Y) ↦ ∇¹_X Y − ∇²_X Y` is a genuine `(2,1)`-tensor
(`connectionDifference`), because the two Leibniz terms `df(X)·Y` cancel; and
if both connections are torsion free (so both satisfy
`∇_X Y − ∇_Y X = [X, Y]` with the *same* Lie bracket), the difference is
symmetric, `∇¹_X Y − ∇²_X Y = ∇¹_Y X − ∇²_Y X`.  This is exactly the
content of Exercise 2.5.25, since the ambient and induced Levi-Civita
connections are both torsion free.

`connectionDifference` is reusable Riemannian-geometry infrastructure (the
difference of two connections is a tensor — the foundation of the
Gauss/Weingarten formalism); it complements `torsionTensor` (Exercise 2.5.3).

## Design notes

* `connectionDifference` is realized pointwise, `connectionDifference D₁ D₂ X Y p
  ∈ T_pM`, as the chapter realizes every derivative.  Its tensoriality needs
  **no** smoothness beyond that of the differentiated field (unlike the torsion,
  whose homogeneity relies on the Leibniz rule of the Lie bracket): the two
  connections' own Leibniz terms cancel against each other.
* The formalization proves the algebraic conclusion (`II` symmetric, `II`
  tensorial).  The geometric realization — that for an isometric immersion the
  tangential projection of the ambient `∇^{M̃}` *is* the Levi-Civita connection
  of the induced metric (the Gauss formula), so `II` is genuinely the normal
  part — needs the immersion / tangent–normal splitting infrastructure, which is
  not built in this development.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.25.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The difference of two connections as a `(2,1)`-tensor -/

/-- **Math.** The **difference** of two affine connections `∇¹, ∇²`,
`(∇¹ − ∇²)(X, Y)|_p = ∇¹_{X|_p} Y − ∇²_{X|_p} Y ∈ T_pM`.  For an isometric
immersion with `∇¹` the ambient and `∇²` the induced Levi-Civita connection this
is the second fundamental form `II(X, Y)` (Petersen §2.5, Exercise 2.5.25). -/
def connectionDifference (D₁ D₂ : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) : Π x : M, TangentSpace I x :=
  fun p => D₁.cov p (X p) Y - D₂.cov p (X p) Y

@[simp]
theorem connectionDifference_apply (D₁ D₂ : AffineConnection I M)
    (X Y : Π x : M, TangentSpace I x) (p : M) :
    connectionDifference D₁ D₂ X Y p
      = D₁.cov p (X p) Y - D₂.cov p (X p) Y := rfl

/-- **Math.** `C^∞(M)`-homogeneity of the connection difference in its first
(direction) argument: `(∇¹ − ∇²)(fX, Y) = f·(∇¹ − ∇²)(X, Y)`.  Immediate from
the homogeneity of each connection in the direction; no smoothness needed. -/
theorem connectionDifference_smul_left (D₁ D₂ : AffineConnection I M)
    (f : M → ℝ) (X Y : Π x : M, TangentSpace I x) (p : M) :
    connectionDifference D₁ D₂ (fun q => f q • X q) Y p
      = f p • connectionDifference D₁ D₂ X Y p := by
  simp only [connectionDifference_apply]
  rw [D₁.smul_direction p (f p) (X p) Y, D₂.smul_direction p (f p) (X p) Y, smul_sub]

/-- **Math.** Additivity of the connection difference in its first (direction)
argument: `(∇¹ − ∇²)(X + X', Y) = (∇¹ − ∇²)(X, Y) + (∇¹ − ∇²)(X', Y)`. -/
theorem connectionDifference_add_left (D₁ D₂ : AffineConnection I M)
    (X X' Y : Π x : M, TangentSpace I x) (p : M) :
    connectionDifference D₁ D₂ (fun q => X q + X' q) Y p
      = connectionDifference D₁ D₂ X Y p + connectionDifference D₁ D₂ X' Y p := by
  simp only [connectionDifference_apply]
  rw [D₁.add_direction p (X p) (X' p) Y, D₂.add_direction p (X p) (X' p) Y]
  abel

/-- **Math.** `C^∞(M)`-homogeneity of the connection difference in its second
(differentiated) argument: `(∇¹ − ∇²)(X, fY) = f·(∇¹ − ∇²)(X, Y)`.  The two
Leibniz terms `df(X)·Y` cancel, leaving only the homogeneous part. -/
theorem connectionDifference_smul_right (D₁ D₂ : AffineConnection I M)
    {f : M → ℝ} {Y : Π x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hY : IsSmoothVectorField Y)
    (X : Π x : M, TangentSpace I x) (p : M) :
    connectionDifference D₁ D₂ X (fun q => f q • Y q) p
      = f p • connectionDifference D₁ D₂ X Y p := by
  simp only [connectionDifference_apply]
  rw [D₁.leibniz p (X p) hf hY, D₂.leibniz p (X p) hf hY, smul_sub]
  abel

/-- **Math.** Additivity of the connection difference in its second
(differentiated) argument: `(∇¹ − ∇²)(X, Y + Y') = (∇¹ − ∇²)(X, Y) +
(∇¹ − ∇²)(X, Y')`, for smooth `Y, Y'`. -/
theorem connectionDifference_add_right (D₁ D₂ : AffineConnection I M)
    {Y Y' : Π x : M, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hY' : IsSmoothVectorField Y')
    (X : Π x : M, TangentSpace I x) (p : M) :
    connectionDifference D₁ D₂ X (fun q => Y q + Y' q) p
      = connectionDifference D₁ D₂ X Y p + connectionDifference D₁ D₂ X Y' p := by
  simp only [connectionDifference_apply]
  rw [D₁.add_field p (X p) hY hY', D₂.add_field p (X p) hY hY']
  abel

/-- **Math.** If both connections are torsion free (with the *same* underlying
Lie bracket), their difference is **symmetric**: `(∇¹ − ∇²)(X, Y) =
(∇¹ − ∇²)(Y, X)`.  Subtracting the two torsion-free identities
`∇^i_X Y − ∇^i_Y X = [X, Y]` cancels the common bracket.  For the second
fundamental form (`∇¹` ambient, `∇²` induced Levi-Civita) this is the symmetry
of `II` (Petersen §2.5, Exercise 2.5.25). -/
theorem connectionDifference_symm {g₁ : RiemannianMetric I M}
    (D₁ : RiemannianConnection I g₁) {g₂ : RiemannianMetric I M}
    (D₂ : RiemannianConnection I g₂)
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (p : M) :
    connectionDifference D₁.toAffineConnection D₂.toAffineConnection X Y p
      = connectionDifference D₁.toAffineConnection D₂.toAffineConnection Y X p := by
  simp only [connectionDifference_apply]
  have h1 := D₁.torsion_free hX hY p
  have h2 := D₂.torsion_free hX hY p
  have h3 : D₁.cov p (X p) Y - D₁.cov p (Y p) X
      = D₂.cov p (X p) Y - D₂.cov p (Y p) X := by rw [h1, h2]
  rw [← sub_eq_zero]
  rw [← sub_eq_zero] at h3
  rw [← h3]; abel

/-! ## Exercise 2.5.25 -/

/-- **Math.** **Exercise 2.5.25** (Petersen §2.5): for an isometric immersion,
the second fundamental form `II(X, Y) = ∇^{M̃}_X Y − ∇^M_X Y` is **symmetric**
and **tensorial**.  Formalized as the difference of the ambient and induced
(Riemannian, hence torsion-free) connections `D₁, D₂`: `connectionDifference`
is symmetric (`connectionDifference_symm`) and `C^∞(M)`-homogeneous in each
argument (`connectionDifference_smul_left`/`connectionDifference_smul_right`;
additivity is `connectionDifference_add_left`/`connectionDifference_add_right`).

The tangential-projection realization — that for an isometric immersion the
tangential part of the ambient `∇^{M̃}` is the Levi-Civita connection of the
induced metric (the Gauss formula), so `II` is precisely the normal part —
needs the immersion / normal-bundle infrastructure, not built here. -/
theorem exercise2_5_25 {g₁ : RiemannianMetric I M}
    (D₁ : RiemannianConnection I g₁) {g₂ : RiemannianMetric I M}
    (D₂ : RiemannianConnection I g₂)
    {f : M → ℝ} {X Y : Π x : M, TangentSpace I x}
    (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hX : IsSmoothVectorField X)
    (hY : IsSmoothVectorField Y) (p : M) :
    connectionDifference D₁.toAffineConnection D₂.toAffineConnection X Y p
        = connectionDifference D₁.toAffineConnection D₂.toAffineConnection Y X p
      ∧ connectionDifference D₁.toAffineConnection D₂.toAffineConnection
            (fun q => f q • X q) Y p
          = f p • connectionDifference D₁.toAffineConnection D₂.toAffineConnection X Y p
      ∧ connectionDifference D₁.toAffineConnection D₂.toAffineConnection X
            (fun q => f q • Y q) p
          = f p • connectionDifference D₁.toAffineConnection D₂.toAffineConnection X Y p :=
  ⟨connectionDifference_symm D₁ D₂ hX hY p,
    connectionDifference_smul_left _ _ f X Y p,
    connectionDifference_smul_right _ _ hf hY X p⟩

end PetersenLib

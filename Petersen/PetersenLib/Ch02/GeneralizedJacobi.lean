import PetersenLib.Ch02.LieDerivative

/-!
# Petersen Ch. 2, §2.1.2 — The generalized Jacobi identity

The iterated Lie derivative `(L_X L)_Y` acting on `(0,k)`-tensors
(`generalizedLieDerivative`) and Petersen's **Proposition 2.1.6**, the
*generalized Jacobi identity* (`generalizedJacobiIdentity`):

`(L_X L)_Y T = L_X (L_Y T) − L_{L_X Y} T − L_Y (L_X T) = 0`

for all smooth vector fields `X`, `Y` and every smooth `(0,k)`-tensor `T`.

## Design notes

* Petersen proves Prop. 2.1.6 in four separate cases — functions, vector
  fields, `1`-forms, and finally general `(0,k)`-tensors by induction on the
  structure of the tensor algebra. Working with the evaluation representation
  `TensorOperator` of `PetersenLib.Ch02.LieDerivative`, the four cases collapse
  into a single direct computation valid for every `k`: both iterated Lie
  derivatives are expanded through the formula of Prop. 2.1.2
  (`lieDerivativeTensor_formula`) into a five-term normal form
  (`lieDerivativeTensor_lieDerivativeTensor`); the pure derivative part then
  cancels by the bracket–commutator identity `D_{[X,Y]} = [D_X, D_Y]`
  (Prop. 2.1.1, `lieDerivative_vectorField_eq_bracket`), the off-diagonal
  correction terms cancel pairwise by symmetry of the double sum, and the
  diagonal ones cancel by the Jacobi identity for the Lie bracket
  (Mathlib's `VectorField.leibniz_identity_mlieBracket_apply`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.1.2.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The iterated Lie derivative -/

variable (I) in
/-- **Math.** The **iterated Lie derivative** `(L_X L)_Y` of Petersen §2.1.2 acting on
`(0,k)`-tensors: `(L_X L)_Y T := L_X (L_Y T) − L_{L_X Y} T − L_Y (L_X T)`, the second-order
operator measuring the failure of `L` to be flat in the direction slot. By Prop. 2.1.6
(`generalizedJacobiIdentity`) it vanishes identically on smooth tensors. -/
def generalizedLieDerivative (X Y : Π x : M, TangentSpace I x) {k : ℕ}
    (T : TensorOperator I M k) : TensorOperator I M k :=
  lieDerivativeTensor I X (lieDerivativeTensor I Y T)
    - lieDerivativeTensor I (lieDerivativeVectorField I X Y) T
    - lieDerivativeTensor I Y (lieDerivativeTensor I X T)

omit [IsManifold I ∞ M] in
theorem generalizedLieDerivative_apply (X Y : Π x : M, TangentSpace I x) {k : ℕ}
    (T : TensorOperator I M k) (Z : Fin k → Π x : M, TangentSpace I x) (x : M) :
    generalizedLieDerivative I X Y T Z x
      = lieDerivativeTensor I X (lieDerivativeTensor I Y T) Z x
        - lieDerivativeTensor I (lieDerivativeVectorField I X Y) T Z x
        - lieDerivativeTensor I Y (lieDerivativeTensor I X T) Z x := rfl

/-! ## Sum rules for the directional derivative -/

omit [IsManifold I ∞ M] in
private theorem mdifferentiableAt_finset_sum {ι : Type*} (s : Finset ι)
    (g : ι → M → ℝ) (x : M) :
    (∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (g i) x) →
      MDifferentiableAt I 𝓘(ℝ) (∑ i ∈ s, g i) x := by
  induction s using Finset.cons_induction with
  | empty => intro _; simpa using mdifferentiableAt_const (c := (0 : ℝ))
  | cons a s ha ih =>
    intro hg
    rw [Finset.sum_cons]
    exact (hg a (Finset.mem_cons_self a s)).add
      (ih fun i hi => hg i (Finset.mem_cons_of_mem hi))

private theorem directionalDerivative_finset_sum {ι : Type*} (s : Finset ι)
    (g : ι → M → ℝ) (x : M) (Y : Π x : M, TangentSpace I x) :
    (∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (g i) x) →
      directionalDerivative Y (∑ i ∈ s, g i) x = ∑ i ∈ s, directionalDerivative Y (g i) x := by
  induction s using Finset.cons_induction with
  | empty =>
    intro _
    rw [Finset.sum_empty, Finset.sum_empty]
    exact directionalDerivative_const Y 0 x
  | cons a s ha ih =>
    intro hg
    have hgs : ∀ i ∈ s, MDifferentiableAt I 𝓘(ℝ) (g i) x :=
      fun i hi => hg i (Finset.mem_cons_of_mem hi)
    rw [Finset.sum_cons, Finset.sum_cons,
      directionalDerivative_add (hg a (Finset.mem_cons_self a s))
        (mdifferentiableAt_finset_sum s g x hgs) Y,
      ih hgs]

/-- Updating one slot of a tuple of smooth vector fields by a smooth vector field yields
a tuple of smooth vector fields. -/
private theorem isSmoothVectorField_update {k : ℕ}
    {Z : Fin k → Π x : M, TangentSpace I x} (hZ : ∀ i, IsSmoothVectorField (Z i))
    {j : Fin k} {U : Π x : M, TangentSpace I x} (hU : IsSmoothVectorField U) :
    ∀ i, IsSmoothVectorField (Function.update Z j U i) := by
  intro i
  rcases eq_or_ne i j with rfl | hij
  · simpa using hU
  · simpa [Function.update_of_ne hij] using hZ i

/-! ## The Jacobi identity for the Lie bracket, pointwise -/

section BracketJacobi

variable [CompleteSpace E]

/-- The Jacobi identity for the Lie bracket of smooth vector fields, in Leibniz form:
`[X, [Y, W]] = [[X, Y], W] + [Y, [X, W]]`, as an identity of vector fields. -/
private theorem lieDerivativeVectorField_jacobi
    {X Y W : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) (hW : IsSmoothVectorField W) :
    lieDerivativeVectorField I X (lieDerivativeVectorField I Y W)
      = fun p => lieDerivativeVectorField I (lieDerivativeVectorField I X Y) W p
        + lieDerivativeVectorField I Y (lieDerivativeVectorField I X W) p := by
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
  funext p
  have hsm : ∀ {V : Π x : M, TangentSpace I x}, IsSmoothVectorField V →
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) (minSmoothness ℝ 2)
        (fun q => (⟨q, V q⟩ : TangentBundle I M)) p := fun hV => by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact (hV p).of_le (WithTop.coe_le_coe.mpr le_top)
  simpa using VectorField.leibniz_identity_mlieBracket_apply (hsm hX) (hsm hY) (hsm hW)

end BracketJacobi

/-! ## Proposition 2.1.6: the generalized Jacobi identity -/

section GeneralizedJacobi

variable [I.Boundaryless] [CompleteSpace E]

/-- Normal form of the iterated Lie derivative: expanding `L_V (L_W T)` twice through the
formula of Prop. 2.1.2 yields five groups of terms — the pure second derivative, the two
mixed single sums, the diagonal double-bracket sum, and the off-diagonal double sum. -/
private theorem lieDerivativeTensor_lieDerivativeTensor
    (V : Π x : M, TangentSpace I x) {W : Π x : M, TangentSpace I x}
    (hW : IsSmoothVectorField W)
    {k : ℕ} {T : TensorOperator I M k} (hT : IsTensorOperator T)
    (Z : Fin k → Π x : M, TangentSpace I x) (hZ : ∀ i, IsSmoothVectorField (Z i))
    (x : M) :
    lieDerivativeTensor I V (lieDerivativeTensor I W T) Z x
      = directionalDerivative V (directionalDerivative W (T Z)) x
        - (∑ i, directionalDerivative V
            (T (Function.update Z i (lieDerivativeVectorField I W (Z i)))) x)
        - (∑ j, directionalDerivative W
            (T (Function.update Z j (lieDerivativeVectorField I V (Z j)))) x)
        + (∑ j, T (Function.update Z j
            (lieDerivativeVectorField I W (lieDerivativeVectorField I V (Z j)))) x)
        + ∑ j, ∑ i ∈ Finset.univ.erase j,
            T (Function.update (Function.update Z j (lieDerivativeVectorField I V (Z j))) i
                (lieDerivativeVectorField I W (Z i))) x := by
  -- differentiability of the ingredients at `x`
  have hTupd : ∀ i : Fin k, MDifferentiableAt I 𝓘(ℝ)
      (T (Function.update Z i (lieDerivativeVectorField I W (Z i)))) x := fun i =>
    ((hT.smooth_eval _
      (isSmoothVectorField_update hZ (hW.lieDerivativeVectorField (hZ i)))) x).mdifferentiableAt
      (by decide)
  have hDW : MDifferentiableAt I 𝓘(ℝ) (directionalDerivative W (T Z)) x :=
    ((hW.directionalDerivative_contMDiff (hT.smooth_eval Z hZ)) x).mdifferentiableAt (by decide)
  have hsum : MDifferentiableAt I 𝓘(ℝ)
      (∑ i, T (Function.update Z i (lieDerivativeVectorField I W (Z i)))) x :=
    mdifferentiableAt_finset_sum _ _ _ (fun i _ => hTupd i)
  -- expansion of the derivative term
  have h₁ : directionalDerivative V (lieDerivativeTensor I W T Z) x
      = directionalDerivative V (directionalDerivative W (T Z)) x
        - ∑ i, directionalDerivative V
            (T (Function.update Z i (lieDerivativeVectorField I W (Z i)))) x := by
    have hfun : lieDerivativeTensor I W T Z
        = directionalDerivative W (T Z)
          - ∑ i, T (Function.update Z i (lieDerivativeVectorField I W (Z i))) := rfl
    rw [hfun, directionalDerivative_sub hDW hsum V]
    congr 1
    exact directionalDerivative_finset_sum _ _ _ V (fun i _ => hTupd i)
  -- expansion of each correction term: the inner update at `i = j` overwrites the outer one
  have h₂ : ∀ j : Fin k,
      lieDerivativeTensor I W T (Function.update Z j (lieDerivativeVectorField I V (Z j))) x
        = directionalDerivative W
            (T (Function.update Z j (lieDerivativeVectorField I V (Z j)))) x
          - (T (Function.update Z j
                (lieDerivativeVectorField I W (lieDerivativeVectorField I V (Z j)))) x
              + ∑ i ∈ Finset.univ.erase j,
                T (Function.update (Function.update Z j (lieDerivativeVectorField I V (Z j))) i
                    (lieDerivativeVectorField I W (Z i))) x) := by
    intro j
    rw [lieDerivativeTensor_formula]
    congr 1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    · rw [Function.update_self, Function.update_idem]
    · exact Finset.sum_congr rfl fun i hi => by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  rw [lieDerivativeTensor_formula, h₁, Finset.sum_congr rfl (fun j _ => h₂ j),
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  ring

/-- **Math.** **Prop. 2.1.6 (the generalized Jacobi identity)**: for smooth vector fields
`X`, `Y` and every smooth `(0,k)`-tensor `T`,

`(L_X L)_Y T = L_X (L_Y T) − L_{L_X Y} T − L_Y (L_X T) = 0.`

Petersen proves this in four cases — functions, vector fields, `1`-forms, and general
`(0,k)`-tensors. Here the four cases are replaced by one direct computation valid for all
`k`: both iterated derivatives are expanded into normal form by Prop. 2.1.2, the
second-derivative terms cancel by the commutator identity `D_{[X,Y]} = [D_X, D_Y]`
(Prop. 2.1.1), the off-diagonal double sums cancel by symmetry, and the diagonal terms
cancel by the Jacobi identity `[X, [Y, Z]] = [[X, Y], Z] + [Y, [X, Z]]` for the Lie
bracket. -/
theorem generalizedJacobiIdentity
    {X Y : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    {k : ℕ} {T : TensorOperator I M k} (hT : IsTensorOperator T)
    (Z : Fin k → Π x : M, TangentSpace I x) (hZ : ∀ i, IsSmoothVectorField (Z i))
    (x : M) :
    generalizedLieDerivative I X Y T Z x = 0 := by
  -- the two iterated expansions, in normal form
  have hEXY := lieDerivativeTensor_lieDerivativeTensor X hY hT Z hZ x
  have hEYX := lieDerivativeTensor_lieDerivativeTensor Y hX hT Z hZ x
  -- Prop. 2.1.1: `L_{[X,Y]}` differentiates `T Z` as the commutator of `D_X` and `D_Y`
  have hmid : lieDerivativeTensor I (lieDerivativeVectorField I X Y) T Z x
      = (directionalDerivative X (directionalDerivative Y (T Z)) x
          - directionalDerivative Y (directionalDerivative X (T Z)) x)
        - ∑ j, T (Function.update Z j
            (lieDerivativeVectorField I (lieDerivativeVectorField I X Y) (Z j))) x := by
    rw [lieDerivativeTensor_formula,
      lieDerivative_vectorField_eq_bracket hX hY (hT.smooth_eval Z hZ) x]
  -- the diagonal terms recombine through the Jacobi identity for the bracket
  have hR : (∑ j, T (Function.update Z j
        (lieDerivativeVectorField I X (lieDerivativeVectorField I Y (Z j)))) x)
      = (∑ j, T (Function.update Z j
          (lieDerivativeVectorField I (lieDerivativeVectorField I X Y) (Z j))) x)
        + ∑ j, T (Function.update Z j
            (lieDerivativeVectorField I Y (lieDerivativeVectorField I X (Z j)))) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IsTensorOperator.congr_slot (T := T)
      (lieDerivativeVectorField_jacobi hX hY (hZ j)) x, hT.add_slot]
  -- the off-diagonal double sums agree after commuting the two slot updates
  have hcond : ∀ a b : Fin k,
      a ∈ (Finset.univ : Finset (Fin k)) ∧ b ∈ Finset.univ.erase a
        ↔ a ∈ Finset.univ.erase b ∧ b ∈ (Finset.univ : Finset (Fin k)) := by
    intro a b
    simp [Finset.mem_erase, ne_comm]
  have hswap : (∑ j, ∑ i ∈ Finset.univ.erase j,
        T (Function.update (Function.update Z j (lieDerivativeVectorField I Y (Z j))) i
            (lieDerivativeVectorField I X (Z i))) x)
      = ∑ j, ∑ i ∈ Finset.univ.erase j,
        T (Function.update (Function.update Z j (lieDerivativeVectorField I X (Z j))) i
            (lieDerivativeVectorField I Y (Z i))) x := by
    rw [Finset.sum_comm' hcond]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b hb => ?_
    rw [Function.update_comm (Finset.ne_of_mem_erase hb)]
  rw [generalizedLieDerivative_apply, hEXY, hEYX, hmid, hR, hswap]
  ring

end GeneralizedJacobi

end PetersenLib

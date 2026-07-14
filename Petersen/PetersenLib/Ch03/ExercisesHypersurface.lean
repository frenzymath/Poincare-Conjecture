import PetersenLib.Ch03.Exercises

/-!
# Petersen Ch. 3, §3.4 — Exercise 3.4.12 (Ricci curvature of a hypersurface)

Petersen, *Riemannian Geometry* (3rd ed.), §3.4, Exercise 3.4.12: for a
hypersurface `H^{n-1} ⊂ ℝⁿ` with second fundamental form `Π`,
`Ric^H = tr(Π)·Π − Π²`.

## Modelling

At a point `p ∈ H` the tangent space is a real inner product space `V = T_pH`.
The **shape operator** `S : V → V` is the self-adjoint endomorphism representing
the second fundamental form, `Π(x,y) = ⟪S x, y⟫` (`hS : S.IsSymmetric`).

The ambient `ℝⁿ` is **flat**, so the Gauss equation (Thm 3.2.4,
`thm:pet-ch3-tangential-curvature-equation`, with ambient curvature `R ≡ 0`)
identifies the *intrinsic* `(0,4)`-curvature of `H` with the Kulkarni–Nomizu
square of `Π`:
`R^H(x,y,z,w) = Π(x,w)Π(y,z) − Π(x,z)Π(y,w) = (Π ⊛ Π)(x,y,z,w)`,
which is exactly `PetersenLib.kulkarniNomizuProduct Π Π` (the `½`-symmetrisation
collapses because both factors are `Π`).

Contracting `R^H` in Petersen's Ricci convention
`Ric(v,w) = ∑ᵢ R(eᵢ,v,w,eᵢ)` (an orthonormal frame `eᵢ`) gives the closed form
`Ric^H(v,w) = tr(Π)·Π(v,w) − Π²(v,w)`, where `tr(Π) = bilinTrace Π` and
`Π²(v,w) = ⟪S(S v),w⟫ = Π(S v, w)` is the `(0,2)`-tensor of the operator square
`S ∘ S`.
-/

open Module (finrank)
open scoped RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

namespace Ex12

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The **second fundamental form** of a hypersurface, as the bilinear form
`Π(x,y) = ⟪S x, y⟫` of the shape operator `S`. -/
def secondFundamentalBilin (S : V →ₗ[ℝ] V) : LinearMap.BilinForm ℝ V :=
  (innerₗ V) ∘ₗ S

@[simp] theorem secondFundamentalBilin_apply (S : V →ₗ[ℝ] V) (x y : V) :
    secondFundamentalBilin S x y = ⟪S x, y⟫ := by
  simp [secondFundamentalBilin, innerₗ_apply_apply]

/-- The **Gauss curvature form** of a hypersurface in a flat ambient space:
`R^H = Π ⊛ Π`. Its Ricci contraction is `exercise3_4_12` below. -/
def gaussCurvatureForm (S : V →ₗ[ℝ] V) : V → V → V → V → ℝ :=
  fun v₁ v₂ v₃ v₄ =>
    kulkarniNomizuProduct (secondFundamentalBilin S) (secondFundamentalBilin S) v₁ v₂ v₃ v₄

/-- The Gauss form is an algebraic curvature form (Prop. 3.1.1 (1)–(3)), being a
Kulkarni–Nomizu product of the symmetric form `Π` with itself. -/
theorem isAlgCurvatureForm_gaussCurvatureForm (S : V →ₗ[ℝ] V) (hS : S.IsSymmetric) :
    IsAlgCurvatureForm (gaussCurvatureForm S) := by
  have hsymm : ∀ a b, secondFundamentalBilin S a b = secondFundamentalBilin S b a := by
    intro a b
    simp only [secondFundamentalBilin_apply]
    rw [hS a b, real_inner_comm]
  exact exercise3_4_23 (secondFundamentalBilin S) (secondFundamentalBilin S) hsymm hsymm

end Ex12

open Ex12 in
/-- **Math.** Petersen §3.4, Exercise 3.4.12: the **Ricci curvature of a
hypersurface** `H^{n-1} ⊂ ℝⁿ` is `Ric^H = tr(Π)·Π − Π²`, where `Π` is the
second fundamental form and `Π²` the `(0,2)`-tensor of the squared shape
operator `S ∘ S`.

Contracting the Gauss form `R^H = Π ⊛ Π` (Thm 3.2.4 in the flat ambient) in
Petersen's Ricci convention `Ric(v,w) = ∑ᵢ R^H(eᵢ,v,w,eᵢ)` over the standard
orthonormal frame `eᵢ`: the `Π(eᵢ,eᵢ)` term yields `tr(Π)·Π(v,w)` and the cross
term `∑ᵢ Π(eᵢ,w)Π(v,eᵢ) = ⟪S v, S w⟫ = Π²(v,w)` by frame reproduction. -/
theorem exercise3_4_12 {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (S : V →ₗ[ℝ] V) (hS : S.IsSymmetric) (v w : V) :
    ∑ i, gaussCurvatureForm S (stdOrthonormalBasis ℝ V i) v w (stdOrthonormalBasis ℝ V i)
      = bilinTrace (secondFundamentalBilin S) * secondFundamentalBilin S v w
        - secondFundamentalBilin S (S v) w := by
  set e := stdOrthonormalBasis ℝ V with he
  set B := secondFundamentalBilin S with hB
  -- Termwise expansion of the Kulkarni–Nomizu square at `(eᵢ, v, w, eᵢ)`.
  have key : ∀ i, gaussCurvatureForm S (e i) v w (e i)
      = B (e i) (e i) * B v w - B (e i) w * B v (e i) := by
    intro i
    simp only [gaussCurvatureForm, kulkarniNomizuProduct, hB]
    ring
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_sub_distrib, ← Finset.sum_mul]
  congr 1
  · -- diagonal term: `(∑ᵢ Π(eᵢ,eᵢ)) = tr(Π)`
    rw [bilinTrace_eq_sum B e]
  · -- cross term: `∑ᵢ Π(eᵢ,w)·Π(v,eᵢ) = ⟪S v, S w⟫ = Π(S v, w)`
    have hcross : ∑ i, B (e i) w * B v (e i) = ∑ i, ⟪S v, e i⟫ * ⟪e i, S w⟫ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hB, secondFundamentalBilin_apply]
      rw [hS (e i) w]
      ring
    rw [hcross, OrthonormalBasis.sum_inner_mul_inner e (S v) (S w)]
    simp only [hB, secondFundamentalBilin_apply]
    rw [hS (S v) w]

end PetersenLib

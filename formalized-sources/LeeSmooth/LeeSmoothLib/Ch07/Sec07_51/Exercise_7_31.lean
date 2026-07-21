import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.GroupTheory.SemidirectProduct
import LeeSmoothLib.Ch07.Sec07_47.Definition_7_47_extra_1
-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

section SemidirectProductOnProd

universe u𝕜 uEN uEH uHN uHH uN uH

variable {N : Type uN} [Group N]
variable {H : Type uH} [Group H]

/-- Helper for Exercise 7.31: the textbook semidirect-product multiplication on `N × H`. -/
def semidirectProductMul (θ : H →* MulAut N) (a b : N × H) : N × H :=
  (a.1 * θ a.2 b.1, a.2 * b.2)

/-- Helper for Exercise 7.31: the textbook semidirect-product inverse on `N × H`. -/
def semidirectProductInv (θ : H →* MulAut N) (a : N × H) : N × H :=
  (θ (a.2⁻¹) (a.1⁻¹), a.2⁻¹)

/-- Helper for Exercise 7.31: the textbook semidirect-product multiplication on `N × H`
is associative. -/
theorem semidirectProductMul_assoc (θ : H →* MulAut N) (a b c : N × H) :
    semidirectProductMul θ (semidirectProductMul θ a b) c =
      semidirectProductMul θ a (semidirectProductMul θ b c) := by
  ext <;> simp [semidirectProductMul, mul_assoc, map_mul, MulAut.mul_apply]

/-- Helper for Exercise 7.31: `(1, 1)` is a left identity for the textbook semidirect-product
law on `N × H`. -/
theorem semidirectProductOne_mul (θ : H →* MulAut N) (a : N × H) :
    semidirectProductMul θ (1, 1) a = a := by
  ext <;> simp [semidirectProductMul]

/-- Helper for Exercise 7.31: `(1, 1)` is a right identity for the textbook semidirect-product
law on `N × H`. -/
theorem semidirectProductMul_one (θ : H →* MulAut N) (a : N × H) :
    semidirectProductMul θ a (1, 1) = a := by
  ext <;> simp [semidirectProductMul]

/-- Helper for Exercise 7.31: the textbook inverse is a left inverse for the textbook
semidirect-product law on `N × H`. -/
theorem semidirectProductInv_mul_cancel (θ : H →* MulAut N) (a : N × H) :
    semidirectProductMul θ (semidirectProductInv θ a) a = (1, 1) := by
  ext <;> simp [semidirectProductMul, semidirectProductInv]

/-- Part of Exercise 7.31: transport mathlib's canonical semidirect product `N ⋊[θ] H`
across `SemidirectProduct.equivProd` to realize it on the product type `N × H`. -/
abbrev semidirectProductGroup (θ : H →* MulAut N) : Group (N × H) where
  mul := semidirectProductMul θ
  one := (1, 1)
  inv := semidirectProductInv θ
  div := fun a b ↦ semidirectProductMul θ a (semidirectProductInv θ b)
  mul_assoc := semidirectProductMul_assoc θ
  one_mul := semidirectProductOne_mul θ
  mul_one := semidirectProductMul_one θ
  inv_mul_cancel := semidirectProductInv_mul_cancel θ
  div_eq_mul_inv := fun a b ↦ rfl

/-- Multiplication in `semidirectProductGroup θ` is the textbook semidirect-product formula. -/
theorem semidirectProductGroup_mul_eq (θ : H →* MulAut N) (a b : N × H) :
    (semidirectProductGroup θ).mul a b = (a.1 * θ a.2 b.1, a.2 * b.2) := by
  rfl

/-- Part of Exercise 7.31: the identity element of `semidirectProductGroup θ` is `(e, e)`. -/
theorem semidirectProductGroup_one_eq (θ : H →* MulAut N) :
    (semidirectProductGroup θ).one = (1, 1) := by
  rfl

/-- Helper for Exercise 7.31: the first coordinate of the semidirect-product inverse can be
written either using the inverse automorphism `MulEquiv.symm (θ h)` or the textbook action
`θ h⁻¹` on `n⁻¹`. -/
theorem semidirectProductInvFirst_eq (θ : H →* MulAut N) (a : N × H) :
    ((MulEquiv.symm (θ a.2)) a.1)⁻¹ = θ (a.2⁻¹) (a.1⁻¹) := by
  calc
    ((MulEquiv.symm (θ a.2)) a.1)⁻¹ = (θ (a.2⁻¹) a.1)⁻¹ := by
      simp
    _ = θ (a.2⁻¹) (a.1⁻¹) := by
      simp

/-- Part of Exercise 7.31: the inverse in `semidirectProductGroup θ` is
`(n, h)⁻¹ = (θ_{h⁻¹}(n⁻¹), h⁻¹)`. -/
theorem semidirectProductGroup_inv_eq (θ : H →* MulAut N) (a : N × H) :
    (semidirectProductGroup θ).inv a = (θ (a.2⁻¹) (a.1⁻¹), a.2⁻¹) := by
  rfl

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {I : ModelWithCorners 𝕜 EN HN} {J : ModelWithCorners 𝕜 EH HH}
variable [TopologicalSpace N] [ChartedSpace HN N]
variable [TopologicalSpace H] [ChartedSpace HH H]

variable [LieGroup I ∞ N] [LieGroup J ∞ H]

omit [Group N] [Group H] [LieGroup I ∞ N] [LieGroup J ∞ H] in
/-- Helper for Exercise 7.31: the multiplication proof feeds `hθ` with the reordered input
`(p.1.2, p.2.1) : H × N`. -/
theorem semidirectProductMulActionInput_contMDiff :
    ContMDiff ((I.prod J).prod (I.prod J)) (J.prod I) ∞
      (fun p : (N × H) × (N × H) ↦ (p.1.2, p.2.1)) := by
  -- Pair the `H`-coordinate from the left factor with the `N`-coordinate from the right factor.
  exact (contMDiff_fst.snd).prodMk contMDiff_snd.fst

/-- Helper for Exercise 7.31: the inverse proof feeds `hθ` with the reordered input
`(a.2⁻¹, a.1⁻¹) : H × N`. -/
theorem semidirectProductInvActionInput_contMDiff :
    ContMDiff (I.prod J) (J.prod I) ∞ (fun a : N × H ↦ (a.2⁻¹, a.1⁻¹)) := by
  -- Apply inversion on both coordinates before pairing them in the `H × N` order.
  exact (contMDiff_snd.inv).prodMk contMDiff_fst.inv

/-- Helper for Exercise 7.31: multiplication on `N × H` is smooth for the transported
semidirect-product group law. -/
theorem semidirectProductMul_contMDiff (θ : H →* MulAut N)
    (hθ : ContMDiff (J.prod I) I ∞ fun p : H × N ↦ θ p.1 p.2) :
    ContMDiff ((I.prod J).prod (I.prod J)) (I.prod J) ∞
      (fun p : (N × H) × (N × H) ↦ semidirectProductMul θ p.1 p.2) := by
  have hAction :
      ContMDiff ((I.prod J).prod (I.prod J)) I ∞
        (fun p : (N × H) × (N × H) ↦ θ p.1.2 p.2.1) := by
    -- Feed the smooth action map with the named `H × N` bridge from the product coordinates.
    exact hθ.comp semidirectProductMulActionInput_contMDiff
  -- Build the two coordinates directly from the smooth multiplication maps on `N` and `H`.
  simpa [semidirectProductMul] using
    ((contMDiff_fst.fst).mul hAction).prodMk ((contMDiff_fst.snd).mul contMDiff_snd.snd)

/-- Helper for Exercise 7.31: inversion on `N × H` is smooth for the transported
semidirect-product group law. -/
theorem semidirectProductInv_contMDiff (θ : H →* MulAut N)
    (hθ : ContMDiff (J.prod I) I ∞ fun p : H × N ↦ θ p.1 p.2) :
    ContMDiff (I.prod J) (I.prod J) ∞ (fun a : N × H ↦ semidirectProductInv θ a) := by
  have hAction :
      ContMDiff (I.prod J) I ∞ (fun a : N × H ↦ θ (a.2⁻¹) (a.1⁻¹)) := by
    -- Feed the smooth action map with the named inverse-input bridge into `H × N`.
    exact hθ.comp semidirectProductInvActionInput_contMDiff
  -- Pair the smooth first coordinate with inversion in `H`.
  simpa [semidirectProductInv] using hAction.prodMk contMDiff_snd.inv

/-- Exercise 7.31: if the action map `(h, n) ↦ θ h n` is smooth, then the transported
semidirect-product group structure on `N × H` is a Lie group structure on the product manifold. -/
theorem semidirectProductLieGroup (θ : H →* MulAut N)
    (hθ : ContMDiff (J.prod I) I ∞ fun p : H × N ↦ θ p.1 p.2) :
    let _ : Group (N × H) := semidirectProductGroup θ
    LieGroup (I.prod J) ∞ (N × H) := by
  let _ : Mul (N × H) := (semidirectProductGroup θ).toMulOneClass.toMul
  let _ : Inv (N × H) := (semidirectProductGroup θ).toInv
  let _ : Group (N × H) := semidirectProductGroup θ
  -- Assemble the Lie-group structure from the cached smooth multiplication and inversion facts.
  refine { toContMDiffMul := ?_, contMDiff_inv := ?_ }
  · refine { contMDiff_mul := ?_ }
    -- Reuse the direct smooth multiplication proof in the theorem's own operation spelling.
    change ContMDiff ((I.prod J).prod (I.prod J)) (I.prod J) ∞
      (fun p : (N × H) × (N × H) ↦ semidirectProductMul θ p.1 p.2)
    exact semidirectProductMul_contMDiff θ hθ
  · -- Reuse the direct smooth inversion proof in the theorem's own operation spelling.
    change ContMDiff (I.prod J) (I.prod J) ∞ (fun a : N × H ↦ semidirectProductInv θ a)
    exact semidirectProductInv_contMDiff θ hθ

end SemidirectProductOnProd

section SemidirectProductIsomorphism

universe u𝕜 uEN uHN uN uEH uHH uH uEG uHG uG

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {EN : Type uEN} [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
variable {HN : Type uHN} [TopologicalSpace HN]
variable {N : Type uN} [Group N] [TopologicalSpace N] [ChartedSpace HN N]
variable {EH : Type uEH} [NormedAddCommGroup EH] [NormedSpace 𝕜 EH]
variable {HH : Type uHH} [TopologicalSpace HH]
variable {H : Type uH} [Group H] [TopologicalSpace H] [ChartedSpace HH H]
variable {EG : Type uEG} [NormedAddCommGroup EG] [NormedSpace 𝕜 EG]
variable {HG : Type uHG} [TopologicalSpace HG]
variable {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace HG G]
variable (I_N : ModelWithCorners 𝕜 EN HN)
variable (I_H : ModelWithCorners 𝕜 EH HH)
variable (I_G : ModelWithCorners 𝕜 EG HG)
variable [LieGroup I_N ∞ N] [LieGroup I_H ∞ H] [LieGroup I_G ∞ G]

/-- Source-facing owner: `G` is Lie-group-isomorphic to a semidirect product `N ⋊ H`. -/
def LieGroupIsomorphicToSemidirectProduct : Prop :=
  ∃ θ : H →* MulAut N,
    ∃ hθ : ContMDiff (I_H.prod I_N) I_N ∞ (fun p : H × N ↦ θ p.1 p.2),
      let _ : Group (N × H) := semidirectProductGroup θ
      let _ : LieGroup (I_N.prod I_H) ∞ (N × H) := semidirectProductLieGroup θ hθ
      Nonempty (LieGroupIsomorphism (I_N.prod I_H) I_G (N × H) G)

end SemidirectProductIsomorphism

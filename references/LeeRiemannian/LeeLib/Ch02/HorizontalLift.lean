/-
Chapter 2, "Riemannian Metrics", §"Riemannian Submersions": the linear algebra of
horizontal lifts.

Let `B` be a positive definite bilinear form on a finite-dimensional real vector
space `E` and let `A : E →L[ℝ] E'` be surjective.  The **horizontal lift**
`horizontalLift B A : E' →L[ℝ] E` is the unique right inverse of `A` whose range
is `B`-orthogonal to `ker A`.  Applied fibrewise to `B = g̃|_x` and
`A = dπ_x`, it is the pointwise content of Lee's Proposition 2.25: `T_x M̃`
splits as `H_x ⊕ V_x` with `V_x = ker dπ_x` and `H_x = V_x^⊥`, and a vector
field on the base has a unique horizontal lift.

The point of the file is not existence of the lift — which is elementary — but
**smoothness in the pair `(B, A)`** (`contDiffAt_horizontalLift`), which is what
says that the horizontal distribution `x ↦ (ker dπ_x)^⊥` varies smoothly and
hence that Lee's horizontal lift is a *smooth* vector field.

The construction is coordinate-free, and in particular chooses no inner product
on the target `E'`.  The trick is that a bilinear form `B : E →L[ℝ] E →L[ℝ] ℝ`
*is literally its own Riesz map* `E → E*`, invertible exactly when `B` is
nondegenerate.  Writing `Aᵗ : (E')* →L[ℝ] E*` for the transpose, put

* `raisedTranspose B A = B⁻¹ ∘ Aᵗ : (E')* →L[ℝ] E`, whose range is `(ker A)^⊥`;
* `horizontalLift B A = raisedTranspose B A ∘ (A ∘ raisedTranspose B A)⁻¹`.

Both inversions are inversions of continuous linear maps, and
`ContinuousLinearMap.inverse` is smooth at invertible points, so the whole
formula is smooth in `(B, A)`.  In matrix notation this is the familiar
`L = B⁻¹Aᵗ(AB⁻¹Aᵗ)⁻¹`, the `B`-weighted Moore–Penrose right inverse.

`horizontalLift_congr` is the naturality statement that transports the lift
through a pair of linear isomorphisms; it is what lets `LeeLib.Ch02.RiemannianSubmersion`
compute the lift in a local trivialization of the tangent bundle and so descend
`contDiffAt_horizontalLift` to a statement about smooth sections.

## Provenance

This file is vendored verbatim (up to the namespace) from
`PetersenLib/Foundations/HorizontalLift.lean` in the sibling Petersen project,
where it was written for Petersen §1.3.  Cross-project `lake` dependencies are
banned in this workspace (I-0109), so shared mathlib-only infrastructure is
duplicated rather than imported.  The file depends on nothing but mathlib, so
the copy is exact; keep the two in sync if either is corrected.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension

open scoped ContDiff

namespace LeeLib.Ch02

section HorizontalLift

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']

/- **Math.** The **transpose** operator `A ↦ Aᵗ`, where `Aᵗ : (E')* →L[ℝ] E*` is
`ξ ↦ ξ ∘ A`.  It is bundled as a continuous linear map *in `A`* — that is what
makes `A ↦ Aᵗ` smooth — and is `flip`ped composition, of type
`(E →L[ℝ] E') →L[ℝ] ((E' →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ))`.

This is deliberately a notation rather than a `def`: sealing the expression behind
a constant freezes the `SeminormedAddCommGroup` instance path that `compL`
elaborates with, and Mathlib's calculus lemmas (stated for `NormedAddCommGroup`)
then fail to unify with it. -/
set_option quotPrecheck false in
local notation "transposeCLM" => (ContinuousLinearMap.compL ℝ E E' ℝ).flip

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem transposeCLM_apply (A : E →L[ℝ] E') (ξ : E' →L[ℝ] ℝ) (x : E) :
    transposeCLM A ξ x = ξ (A x) := rfl

/-- **Eng.** The continuous dual of a finite-dimensional real normed space has the
same dimension as the space: `E →L[ℝ] ℝ` is linearly isomorphic to the algebraic
dual `E →ₗ[ℝ] ℝ`, whose dimension is `finrank ℝ E`. -/
theorem finrank_continuousDual (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] :
    Module.finrank ℝ (F →L[ℝ] ℝ) = Module.finrank ℝ F :=
  (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := F) (F' := ℝ)).symm.finrank_eq.trans
    Subspace.dual_finrank_eq

/-- **Math.** A positive-definite form `B` on a finite-dimensional space is its own
Riesz isomorphism `E ≅ E*`: it is injective because `B x = 0` forces `B x x = 0`,
hence `x = 0`, and injective endomorphisms between spaces of equal dimension are
bijective. -/
theorem isInvertible_of_posDef {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) :
    (B : E →L[ℝ] (E →L[ℝ] ℝ)).IsInvertible := by
  have hinj : Function.Injective (B : E →ₗ[ℝ] (E →L[ℝ] ℝ)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    have hpos : 0 < B x x := hB x hne
    have hzero : B x x = 0 := by
      have : (B x : E →L[ℝ] ℝ) = 0 := hx
      rw [this]; rfl
    exact hpos.ne' hzero
  have hsurj : Function.Surjective (B : E →ₗ[ℝ] (E →L[ℝ] ℝ)) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuousDual E).symm).mp hinj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv,
    by ext x; rfl⟩

/-- **Math.** `raisedTranspose B A = B⁻¹ ∘ Aᵗ : (E')* →L[ℝ] E`.  Its defining
property is `B (raisedTranspose B A ξ) = ξ ∘ A` (`raisedTranspose_spec`): the
vector `B`-dual to the pulled-back functional `ξ ∘ A`.  Its range is exactly the
`B`-orthogonal complement `(ker A)^⊥`. -/
noncomputable def raisedTranspose (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E') :
    (E' →L[ℝ] ℝ) →L[ℝ] E :=
  (ContinuousLinearMap.inverse (B : E →L[ℝ] (E →L[ℝ] ℝ))).comp (transposeCLM A)

omit [FiniteDimensional ℝ E'] in
/-- **Math.** The defining property of `raisedTranspose`: `B (B⁻¹(ξ ∘ A)) = ξ ∘ A`. -/
theorem raisedTranspose_spec {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) (A : E →L[ℝ] E') (ξ : E' →L[ℝ] ℝ) (w : E) :
    B (raisedTranspose B A ξ) w = ξ (A w) := by
  have h := (isInvertible_of_posDef hB).self_apply_inverse (transposeCLM A ξ)
  have : (B (raisedTranspose B A ξ) : E →L[ℝ] ℝ) = transposeCLM A ξ := h
  rw [this]
  rfl

/-- **Eng.** `A ∘ raisedTranspose B A : (E')* →L[ℝ] E'` is invertible when `B` is
positive definite and `A` is surjective.  Injectivity: if `A (B⁻¹(ξ ∘ A)) = 0`,
then `x = B⁻¹(ξ ∘ A)` satisfies `B x x = ξ (A x) = 0`, so `x = 0` and `ξ ∘ A = 0`;
surjectivity of `A` then gives `ξ = 0`.  Equal dimensions upgrade injectivity to
bijectivity. -/
theorem isInvertible_comp_raisedTranspose {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) {A : E →L[ℝ] E'} (hA : Function.Surjective A) :
    (A.comp (raisedTranspose B A)).IsInvertible := by
  set T := A.comp (raisedTranspose B A) with hT
  have hinj : Function.Injective (T : (E' →L[ℝ] ℝ) →ₗ[ℝ] E') := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro ξ hξ
    -- `x` is the raised transpose of `ξ`; it lies in the kernel of `A`.
    set x : E := raisedTranspose B A ξ with hx
    have hAx : A x = 0 := hξ
    -- so `B x x = ξ (A x) = 0`, forcing `x = 0`
    have hxx : B x x = 0 := by rw [raisedTranspose_spec hB A ξ x, hAx, map_zero]
    have hx0 : x = 0 := by
      by_contra hne
      exact (hB x hne).ne' hxx
    -- then `ξ ∘ A = B x = 0`, and `A` is surjective, so `ξ = 0`
    ext y
    obtain ⟨w, rfl⟩ := hA y
    rw [← raisedTranspose_spec hB A ξ w, ← hx, hx0]
    simp
  have hsurj : Function.Surjective (T : (E' →L[ℝ] ℝ) →ₗ[ℝ] E') :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (finrank_continuousDual E')).mp hinj
  exact ⟨(LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩).toContinuousLinearEquiv, by ext ξ; rfl⟩

/-- **Math.** The **horizontal lift** of a surjective `A : E →L[ℝ] E'` relative to a
positive-definite form `B`: the unique right inverse of `A` whose range is
`B`-orthogonal to `ker A`.  Explicitly `L = B⁻¹Aᵗ(AB⁻¹Aᵗ)⁻¹`, the `B`-weighted
Moore–Penrose right inverse of `A`. -/
noncomputable def horizontalLift (B : E →L[ℝ] E →L[ℝ] ℝ) (A : E →L[ℝ] E') :
    E' →L[ℝ] E :=
  (raisedTranspose B A).comp
    (ContinuousLinearMap.inverse (A.comp (raisedTranspose B A)))

/-- **Math.** The horizontal lift is a right inverse of `A`: `A (L u) = u`. -/
theorem horizontalLift_rightInverse {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) {A : E →L[ℝ] E'} (hA : Function.Surjective A)
    (u : E') : A (horizontalLift B A u) = u :=
  (isInvertible_comp_raisedTranspose hB hA).self_apply_inverse u

omit [FiniteDimensional ℝ E'] in
/-- **Math.** The horizontal lift is *horizontal*: its values are `B`-orthogonal to
`ker A`.  Indeed `B (L u) w = ξ (A w) = 0` for `w ∈ ker A`, where `ξ` is the
functional whose raised transpose is `L u`. -/
theorem horizontalLift_horizontal {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) (A : E →L[ℝ] E') (u : E')
    {w : E} (hw : A w = 0) : B (horizontalLift B A u) w = 0 := by
  rw [horizontalLift]
  rw [ContinuousLinearMap.comp_apply, raisedTranspose_spec hB A _ w, hw, map_zero]

/-- **Math.** The two properties characterize the horizontal lift: a right inverse of
`A` with `B`-horizontal values *is* `horizontalLift B A`.  (If `x` and `x'` are two
horizontal preimages of `u`, their difference `d` is both vertical and horizontal,
so `B d d = 0` and `d = 0`.) -/
theorem horizontalLift_unique {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) {A : E →L[ℝ] E'} (hA : Function.Surjective A)
    {L : E' →L[ℝ] E} (h1 : ∀ u : E', A (L u) = u)
    (h2 : ∀ (u : E') (w : E), A w = 0 → B (L u) w = 0) :
    L = horizontalLift B A := by
  ext u
  set d : E := L u - horizontalLift B A u with hd
  -- `d` is vertical …
  have hvert : A d = 0 := by
    rw [hd, map_sub, h1 u, horizontalLift_rightInverse hB hA u, sub_self]
  -- … and horizontal, hence `B d d = 0`
  have hdd : B d d = 0 := by
    have e1 : B (L u) d = 0 := h2 u d hvert
    have e2 : B (horizontalLift B A u) d = 0 := horizontalLift_horizontal hB A u hvert
    have : B d d = B (L u) d - B (horizontalLift B A u) d := by
      rw [hd]; simp
    rw [this, e1, e2, sub_zero]
  have : d = 0 := by
    by_contra hne
    exact (hB d hne).ne' hdd
  have := sub_eq_zero.mp this
  exact this

/-- **Math.** A horizontal vector is recovered from its image: if `x` is
`B`-orthogonal to `ker A`, then `horizontalLift B A (A x) = x`.  This is the sense
in which `L ∘ A` is the `B`-orthogonal projection onto the horizontal space. -/
theorem horizontalLift_apply_apply_of_horizontal {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) {A : E →L[ℝ] E'} (hA : Function.Surjective A)
    {x : E} (hx : ∀ w : E, A w = 0 → B x w = 0) :
    horizontalLift B A (A x) = x := by
  set d : E := horizontalLift B A (A x) - x with hd
  have hvert : A d = 0 := by
    rw [hd, map_sub, horizontalLift_rightInverse hB hA (A x), sub_self]
  have hdd : B d d = 0 := by
    have e1 : B (horizontalLift B A (A x)) d = 0 :=
      horizontalLift_horizontal hB A (A x) hvert
    have e2 : B x d = 0 := hx d hvert
    have : B d d = B (horizontalLift B A (A x)) d - B x d := by rw [hd]; simp
    rw [this, e1, e2, sub_zero]
  have hzero : d = 0 := by
    by_contra hne
    exact (hB d hne).ne' hdd
  exact sub_eq_zero.mp hzero

/-- **Math.** The horizontal lift is nonzero on nonzero vectors (it is injective,
being a right inverse). -/
theorem horizontalLift_ne_zero {B : E →L[ℝ] E →L[ℝ] ℝ}
    (hB : ∀ x : E, x ≠ 0 → 0 < B x x) {A : E →L[ℝ] E'} (hA : Function.Surjective A)
    {u : E'} (hu : u ≠ 0) : horizontalLift B A u ≠ 0 := by
  intro h
  apply hu
  rw [← horizontalLift_rightInverse hB hA u, h, map_zero]

/-! ## Naturality

The horizontal lift transforms covariantly under linear isomorphisms of the source
and target: this is what lets one compute it in a chart / local trivialization. -/

/-- **Math.** **Naturality of the horizontal lift.**  If `θ : E ≃L[ℝ] F` and
`ι : E' ≃L[ℝ] F'` are linear isomorphisms, `B` is a positive-definite form on `E`
and `A : E →L[ℝ] E'` is surjective, then the horizontal lift of the transported
data `(B ∘ (θ⁻¹ × θ⁻¹), ι ∘ A ∘ θ⁻¹)` is `θ ∘ (horizontalLift B A) ∘ ι⁻¹`. -/
theorem horizontalLift_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    [FiniteDimensional ℝ F']
    {B : E →L[ℝ] E →L[ℝ] ℝ} (hB : ∀ x : E, x ≠ 0 → 0 < B x x)
    {A : E →L[ℝ] E'} (hA : Function.Surjective A)
    (θ : E ≃L[ℝ] F) (ι : E' ≃L[ℝ] F')
    {B' : F →L[ℝ] F →L[ℝ] ℝ} {A' : F →L[ℝ] F'}
    (hB' : ∀ x y : F, B' x y = B (θ.symm x) (θ.symm y))
    (hA' : ∀ x : F, A' x = ι (A (θ.symm x))) (u : F') :
    horizontalLift B' A' u = θ (horizontalLift B A (ι.symm u)) := by
  -- `B'` is positive definite and `A'` is surjective, so the lift is characterized
  -- by the two defining properties; the transported map satisfies them.
  have hB'pos : ∀ x : F, x ≠ 0 → 0 < B' x x := by
    intro x hx
    rw [hB' x x]
    exact hB _ (fun h => hx (by simpa using congrArg θ h))
  have hA'surj : Function.Surjective A' := by
    intro v
    obtain ⟨x, hx⟩ := hA (ι.symm v)
    exact ⟨θ x, by rw [hA', θ.symm_apply_apply, hx, ι.apply_symm_apply]⟩
  set L : F' →L[ℝ] F :=
    (θ : E →L[ℝ] F).comp ((horizontalLift B A).comp (ι.symm : F' →L[ℝ] E')) with hL
  have h1 : ∀ v : F', A' (L v) = v := by
    intro v
    rw [hL]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hA', θ.symm_apply_apply, horizontalLift_rightInverse hB hA, ι.apply_symm_apply]
  have h2 : ∀ (v : F') (w : F), A' w = 0 → B' (L v) w = 0 := by
    intro v w hw
    have hw0 : A (θ.symm w) = 0 := by
      have := hA' w
      rw [hw] at this
      exact ι.map_eq_zero_iff.mp this.symm
    rw [hL]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [hB', θ.symm_apply_apply]
    exact horizontalLift_horizontal hB A _ hw0
  have := horizontalLift_unique hB'pos hA'surj h1 h2
  rw [← this, hL]
  rfl

/-! ## Smoothness

The whole point: `horizontalLift` depends smoothly on `(B, A)` near any pair with
`B` positive definite and `A` surjective. -/

/-- **Math.** **Smooth dependence of the horizontal lift on the data.**  If `x ↦ B x`
and `x ↦ A x` are `C^∞` at `x₀`, `B x₀` is positive definite and `A x₀` is
surjective, then `x ↦ horizontalLift (B x) (A x)` is `C^∞` at `x₀`.

This is the statement that the horizontal distribution of a submersion varies
smoothly, and it is what makes a quotient metric a *smooth* section.  The proof is
the formula `L = B⁻¹Aᵗ(AB⁻¹Aᵗ)⁻¹` together with smoothness of operator inversion
at invertible operators. -/
theorem contDiffAt_horizontalLift {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {B : X → (E →L[ℝ] E →L[ℝ] ℝ)} {A : X → (E →L[ℝ] E')} {x₀ : X}
    (hBd : ContDiffAt ℝ ∞ B x₀) (hAd : ContDiffAt ℝ ∞ A x₀)
    (hB : ∀ x : E, x ≠ 0 → 0 < B x₀ x x) (hA : Function.Surjective (A x₀)) :
    ContDiffAt ℝ ∞ (fun x => horizontalLift (B x) (A x)) x₀ := by
  -- `x ↦ Aᵗ x` is smooth, being a continuous linear image of `A`.
  have htr : ContDiffAt ℝ ∞ (fun x => transposeCLM (A x)) x₀ :=
    ContDiffAt.continuousLinearMap_comp _ hAd
  -- `x ↦ (B x)⁻¹` is smooth at `x₀` because `B x₀` is invertible.
  have hBinv : ContDiffAt ℝ ∞
      (fun x => ContinuousLinearMap.inverse (B x : E →L[ℝ] (E →L[ℝ] ℝ))) x₀ := by
    have h := ((isInvertible_of_posDef hB).contDiffAt_map_inverse (n := ∞)).comp x₀ hBd
    simpa [Function.comp_def] using h
  -- hence `x ↦ raisedTranspose (B x) (A x)` is smooth.
  have hS : ContDiffAt ℝ ∞ (fun x => raisedTranspose (B x) (A x)) x₀ :=
    hBinv.clm_comp htr
  -- `x ↦ A x ∘ raisedTranspose (B x) (A x)` is smooth and invertible at `x₀`.
  have hAS : ContDiffAt ℝ ∞
      (fun x => (A x).comp (raisedTranspose (B x) (A x))) x₀ := hAd.clm_comp hS
  have hASinv : ContDiffAt ℝ ∞
      (fun x => ContinuousLinearMap.inverse ((A x).comp (raisedTranspose (B x) (A x)))) x₀ := by
    have h := ((isInvertible_comp_raisedTranspose hB hA).contDiffAt_map_inverse (n := ∞)).comp x₀ hAS
    simpa [Function.comp_def] using h
  exact hS.clm_comp hASinv

end HorizontalLift

end LeeLib.Ch02

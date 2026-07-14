import MorganTianLib.Ch01.Hessian
import MorganTianLib.Ch01.PointwiseCurvature
import OpenGALib.Algebraic.Auxiliary.OrthonormalBasisDiagonal

/-!
# Morgan–Tian Ch. 1 §"Laplacian" / Ch. 2 §2.2 — the Laplacian of a smooth function

Morgan–Tian define the Laplacian of a smooth `f : M → ℝ` as the metric trace of
its Hessian, `Δf = g^{ij} Hess(f)(∂_i, ∂_j)` (blueprint eq. `laplacformula`,
consumed in Ch. 2 by `lem:laplacian-nonpositive-at-max` and the maximum
principle cluster). This file provides the pointwise (fiberwise) Laplacian on
top of `MorganTianLib.hessian`:

* slotwise tensoriality of the Hessian (`hessian_add_left`, `hessian_smul_left`,
  `hessian_add_right`, `hessian_smul_right`) and the resulting pointwise
  locality (`hessian_congr_left`, `hessian_congr_right`): the value
  `Hess(f)(X,Y)(p)` only sees `X(p)` and `Y(p)`;
* locality in the function argument (`hessian_congr_of_eventuallyEq`): the
  Hessian at `p` only sees the germ of `f` at `p`;
* `hessianAt nabla f p : T_pM → T_pM → ℝ`, the Hessian as a bilinear form on
  the tangent space, defined via arbitrary global extensions (`extendVector`)
  and well defined by locality (`hessianAt_eq`), with its bilinearity
  (`hessianAt_add_left` … `hessianAt_smul_right`) and symmetry
  (`hessianAt_symm`);
* `laplacianAt g nabla f p`, the **Laplacian** `Δf(p) = tr_g Hess(f)_p`,
  defined as the diagonal sum of `hessianAt` over an orthonormal basis of
  `(T_pM, g_p)` (through Mathlib's `Bundle.RiemannianBundle` instances, exactly
  as in `MorganTianLib.scalarCurvatureAt`), together with basis-independence
  (`laplacianAt_eq_sum`: *every* orthonormal basis of `(T_pM, g_p)` computes
  the same value) and locality in `f` (`laplacianAt_congr_of_eventuallyEq`).

The extremum properties of the Laplacian (`dv(q) = 0` and `Δv(q) ≤ 0` at a
local maximum, blueprint `lem:laplacian-nonpositive-at-max`) are proved in
`MorganTianLib.Ch02.LaplacianExtremum`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1
(eq. `laplacformula`) and Ch. 2 §2.2.
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Slotwise tensoriality of the Hessian

`MorganTianLib.hessian_smul` records joint `𝒟(M)`-homogeneity; the locality
engine of `MorganTianLib.Ch01.PointwiseCurvature` needs the four slotwise
laws separately. The first slot is tensorial for *any* `f : M → ℝ`; the
second slot needs `f` smooth (its Leibniz cross-terms only cancel against
honest derivatives of `f`). -/

omit [CompleteSpace E] in
/-- **Math.** The Hessian is additive in its first vector-field slot.
Blueprint: `lem:hessian-symmetric` (tensoriality). -/
theorem hessian_add_left (nabla : AffineConnection I M) (f : M → ℝ)
    (X X' Y : SmoothVectorField I M) (q : M) :
    hessian nabla f (X + X') Y q
      = hessian nabla f X Y q + hessian nabla f X' Y q := by
  unfold hessian
  rw [SmoothVectorField.dir_add_field, nabla.add_left,
    SmoothVectorField.dir_add_field]
  ring

omit [CompleteSpace E] in
/-- **Math.** The Hessian is `𝒟(M)`-homogeneous in its first vector-field
slot: `Hess(f)(φX, Y) = φ · Hess(f)(X, Y)`.
Blueprint: `lem:hessian-symmetric` (tensoriality). -/
theorem hessian_smul_left (nabla : AffineConnection I M) {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ, ℝ) ∞ φ) (f : M → ℝ)
    (X Y : SmoothVectorField I M) (q : M) :
    hessian nabla f (SmoothVectorField.smul φ hφ X) Y q
      = φ q * hessian nabla f X Y q := by
  unfold hessian
  rw [SmoothVectorField.dir_smul_field, nabla.smul_left,
    SmoothVectorField.dir_smul_field]
  ring

omit [CompleteSpace E] in
/-- **Math.** The Hessian of a smooth function is additive in its second
vector-field slot. Blueprint: `lem:hessian-symmetric` (tensoriality). -/
theorem hessian_add_right (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y Y' : SmoothVectorField I M) (q : M) :
    hessian nabla f X (Y + Y') q
      = hessian nabla f X Y q + hessian nabla f X Y' q := by
  unfold hessian
  have hfun : ((Y + Y').dir f) = fun r => Y.dir f r + Y'.dir f r :=
    funext fun r => SmoothVectorField.dir_add_field Y Y' f r
  have hA : X.dir ((Y + Y').dir f) q = X.dir (Y.dir f) q + X.dir (Y'.dir f) q := by
    rw [hfun]
    exact X.dir_add q ((Y.dir_contMDiff hf q).mdifferentiableAt (by simp))
      ((Y'.dir_contMDiff hf q).mdifferentiableAt (by simp))
  rw [hA, nabla.add_right, SmoothVectorField.dir_add_field]
  ring

omit [CompleteSpace E] in
/-- **Math.** The Hessian of a smooth function is `𝒟(M)`-homogeneous in its
second vector-field slot: `Hess(f)(X, ψY) = ψ · Hess(f)(X, Y)`. The
first-derivative cross-terms produced by the Leibniz rules of `X(·)` and of
`∇` cancel exactly. Blueprint: `lem:hessian-symmetric` (tensoriality). -/
theorem hessian_smul_right (nabla : AffineConnection I M) {ψ f : M → ℝ}
    (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (X Y : SmoothVectorField I M) (q : M) :
    hessian nabla f X (SmoothVectorField.smul ψ hψ Y) q
      = ψ q * hessian nabla f X Y q := by
  have hfun : ((SmoothVectorField.smul ψ hψ Y).dir f) = fun r => ψ r * Y.dir f r :=
    funext fun r => SmoothVectorField.dir_smul_field hψ Y f r
  have hA : X.dir ((SmoothVectorField.smul ψ hψ Y).dir f) q
      = ψ q * X.dir (Y.dir f) q + Y.dir f q * X.dir ψ q := by
    rw [hfun]
    exact X.dir_mul q (hψ.mdifferentiableAt (by simp))
      ((Y.dir_contMDiff hf q).mdifferentiableAt (by simp))
  have hB : (nabla.cov X (SmoothVectorField.smul ψ hψ Y)).dir f q
      = ψ q * (nabla.cov X Y).dir f q + X.dir ψ q * Y.dir f q := by
    have hL := nabla.leibniz ψ hψ X Y q
    simp only [SmoothVectorField.dir, hL, map_add, map_smul]
    rfl
  unfold hessian
  rw [hA, hB]
  ring

variable [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] in
/-- **Math.** Pointwise locality of the Hessian in its first slot: the value
`Hess(f)(X, Y)(p)` only sees `X(p)`.
Blueprint: `lem:hessian-symmetric` (tensoriality). -/
theorem hessian_congr_left (nabla : AffineConnection I M) (f : M → ℝ)
    {X X' : SmoothVectorField I M} (Y : SmoothVectorField I M) {p : M}
    (h : X p = X' p) : hessian nabla f X Y p = hessian nabla f X' Y p :=
  tensorial_congr_apply (fun A => hessian nabla f A Y)
    (fun A B q => hessian_add_left nabla f A B Y q)
    (fun _ hφ A q => hessian_smul_left nabla hφ f A Y q) h

omit [CompleteSpace E] in
/-- **Math.** Pointwise locality of the Hessian of a smooth function in its
second slot: the value `Hess(f)(X, Y)(p)` only sees `Y(p)`.
Blueprint: `lem:hessian-symmetric` (tensoriality). -/
theorem hessian_congr_right (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X : SmoothVectorField I M)
    {Y Y' : SmoothVectorField I M} {p : M}
    (h : Y p = Y' p) : hessian nabla f X Y p = hessian nabla f X Y' p :=
  tensorial_congr_apply (fun B => hessian nabla f X B)
    (fun A B q => hessian_add_right nabla hf X A B q)
    (fun _ hψ B q => hessian_smul_right nabla hψ hf X B q) h

omit [CompleteSpace E] [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Locality of the Hessian in the function argument: if `f = f'`
near `p` then `Hess(f)(X,Y)(p) = Hess(f')(X,Y)(p)` — the Hessian at `p` only
sees the germ of the function at `p` (all three constituents are `mfderiv`s,
which only see germs). Blueprint: `lem:hessian-symmetric`. -/
theorem hessian_congr_of_eventuallyEq (nabla : AffineConnection I M)
    {f f' : M → ℝ} (X Y : SmoothVectorField I M) {p : M}
    (hff' : f =ᶠ[nhds p] f') :
    hessian nabla f X Y p = hessian nabla f' X Y p := by
  have h1 : Y.dir f =ᶠ[nhds p] Y.dir f' := by
    filter_upwards [hff'.eventually_nhds] with r hr
    simp only [SmoothVectorField.dir, Filter.EventuallyEq.mfderiv_eq hr]
    rfl
  have h2 : X.dir (Y.dir f) p = X.dir (Y.dir f') p := by
    simp only [SmoothVectorField.dir, Filter.EventuallyEq.mfderiv_eq h1]
    rfl
  have h3 : (nabla.cov X Y).dir f p = (nabla.cov X Y).dir f' p := by
    simp only [SmoothVectorField.dir, Filter.EventuallyEq.mfderiv_eq hff']
    rfl
  unfold hessian
  rw [h2, h3]

/-! ### The Hessian as a pointwise bilinear form on the tangent space -/

/-- **Math.** The **Hessian of `f` at `p` as a bilinear form on tangent
vectors**: `Hess(f)_p(v, w) = Hess(f)(V, W)(p)` for any global extensions
`V, W` of `v, w` (well defined for smooth `f` by `hessianAt_eq`; the chosen
extensions are `extendVector`). Blueprint: `lem:hessian-symmetric`. -/
noncomputable def hessianAt (nabla : AffineConnection I M) (f : M → ℝ) (p : M)
    (v w : TangentSpace I p) : ℝ :=
  hessian nabla f (extendVector p v) (extendVector p w) p

omit [CompleteSpace E] in
/-- **Math.** Unfolding lemma for `hessianAt` in terms of the chosen
extensions. Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_def (nabla : AffineConnection I M) (f : M → ℝ) (p : M)
    (v w : TangentSpace I p) :
    hessianAt nabla f p v w
      = hessian nabla f (extendVector p v) (extendVector p w) p := rfl

omit [CompleteSpace E] in
/-- **Math.** **The pointwise Hessian evaluates vector fields pointwise**: for
any smooth vector fields `X, Y`,
`hessianAt nabla f p (X p) (Y p) = Hess(f)(X, Y)(p)`. This is the statement
that the Hessian of a smooth function is a tensor.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_eq (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (X Y : SmoothVectorField I M) (p : M) :
    hessianAt nabla f p (X p) (Y p) = hessian nabla f X Y p := by
  rw [hessianAt_def,
    hessian_congr_left nabla f (extendVector p (Y p)) (extendVector_apply p (X p)),
    hessian_congr_right nabla hf X (extendVector_apply p (Y p))]

omit [CompleteSpace E] in
/-- **Math.** `hessianAt` is additive in its first slot.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_add_left (nabla : AffineConnection I M) (f : M → ℝ) (p : M)
    (v₁ v₂ w : TangentSpace I p) :
    hessianAt nabla f p (v₁ + v₂) w
      = hessianAt nabla f p v₁ w + hessianAt nabla f p v₂ w := by
  have h1 : hessian nabla f (extendVector p (v₁ + v₂)) (extendVector p w) p
      = hessian nabla f (extendVector p v₁ + extendVector p v₂)
          (extendVector p w) p :=
    hessian_congr_left nabla f _ (by simp)
  simp only [hessianAt_def]
  rw [h1, hessian_add_left]

omit [CompleteSpace E] in
/-- **Math.** `hessianAt` is `ℝ`-homogeneous in its first slot.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_smul_left (nabla : AffineConnection I M) (f : M → ℝ) (p : M)
    (a : ℝ) (v w : TangentSpace I p) :
    hessianAt nabla f p (a • v) w = a * hessianAt nabla f p v w := by
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h1 : hessian nabla f (extendVector p (a • v)) (extendVector p w) p
      = hessian nabla f
          (SmoothVectorField.smul (fun _ => a) hconst (extendVector p v))
          (extendVector p w) p :=
    hessian_congr_left nabla f _ (by simp)
  simp only [hessianAt_def]
  rw [h1, hessian_smul_left]

omit [CompleteSpace E] in
/-- **Math.** `hessianAt` of a smooth function is additive in its second slot.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_add_right (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (v w₁ w₂ : TangentSpace I p) :
    hessianAt nabla f p v (w₁ + w₂)
      = hessianAt nabla f p v w₁ + hessianAt nabla f p v w₂ := by
  have h1 : hessian nabla f (extendVector p v) (extendVector p (w₁ + w₂)) p
      = hessian nabla f (extendVector p v)
          (extendVector p w₁ + extendVector p w₂) p :=
    hessian_congr_right nabla hf _ (by simp)
  simp only [hessianAt_def]
  rw [h1, hessian_add_right nabla hf]

omit [CompleteSpace E] in
/-- **Math.** `hessianAt` of a smooth function is `ℝ`-homogeneous in its
second slot. Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_smul_right (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (a : ℝ) (v w : TangentSpace I p) :
    hessianAt nabla f p v (a • w) = a * hessianAt nabla f p v w := by
  have hconst : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun _ : M => a) := contMDiff_const
  have h1 : hessian nabla f (extendVector p v) (extendVector p (a • w)) p
      = hessian nabla f (extendVector p v)
          (SmoothVectorField.smul (fun _ => a) hconst (extendVector p w)) p :=
    hessian_congr_right nabla hf _ (by simp)
  simp only [hessianAt_def]
  rw [h1, hessian_smul_right nabla hconst hf]

/-- **Math.** The pointwise Hessian of a smooth function with respect to a
torsion-free connection is **symmetric**: `Hess(f)_p(v, w) = Hess(f)_p(w, v)`.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_symm [I.Boundaryless] (nabla : AffineConnection I M)
    (hsym : nabla.IsSymmetric) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) (v w : TangentSpace I p) :
    hessianAt nabla f p v w = hessianAt nabla f p w v :=
  hessian_symm nabla hsym hf (extendVector p v) (extendVector p w) p

omit [CompleteSpace E] in
/-- **Math.** Locality of the pointwise Hessian in the function argument: the
Hessian at `p` only sees the germ of the function at `p`.
Blueprint: `lem:hessian-symmetric`. -/
theorem hessianAt_congr_of_eventuallyEq (nabla : AffineConnection I M)
    {f f' : M → ℝ} {p : M} (hff' : f =ᶠ[nhds p] f') (v w : TangentSpace I p) :
    hessianAt nabla f p v w = hessianAt nabla f' p v w :=
  hessian_congr_of_eventuallyEq nabla _ _ hff'

/-! ### The Laplacian as the metric trace of the Hessian

We equip the fibre `T_pM` with the inner product of `g` through Mathlib's
`Bundle.RiemannianBundle` route, exactly as in
`MorganTianLib.scalarCurvatureAt`. -/

/-- **Math.** The **Laplacian** of `f : M → ℝ` at `p`: the metric trace of the
Hessian, `Δf(p) = tr_g Hess(f)_p = Σᵢ Hess(f)_p(eᵢ, eᵢ)` for an orthonormal
basis `{eᵢ}` of `(T_pM, g_p)`. The definition uses the standard orthonormal
basis of `(T_pM, g_p)`; by `laplacianAt_eq_sum` every orthonormal basis
computes the same value, so `Δ` is well defined. For the Levi-Civita
connection this is Morgan–Tian's Laplacian
`Δf = g^{ij} Hess(f)(∂_i, ∂_j)`. Blueprint: eq. `laplacformula`. -/
noncomputable def laplacianAt (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) (f : M → ℝ) (p : M) : ℝ :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  ∑ i, hessianAt nabla f p (stdOrthonormalBasis ℝ (TangentSpace I p) i)
    (stdOrthonormalBasis ℝ (TangentSpace I p) i)

omit [CompleteSpace E] in
/-- **Math.** The Laplacian is the diagonal sum of the Hessian in **every**
orthonormal basis of `(T_pM, g_p)`: `Δf(p) = Σᵢ Hess(f)_p(eᵢ, eᵢ)`. In
particular the choice of basis in the definition of `laplacianAt` is
immaterial. Blueprint: eq. `laplacformula`. -/
theorem laplacianAt_eq_sum (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M) {ι : Type*} [Fintype ι]
    (e : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      OrthonormalBasis ι ℝ (TangentSpace I p)) :
    laplacianAt g nabla f p = ∑ i, hessianAt nabla f p (e i) (e i) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let B : TangentSpace I p →ₗ[ℝ] TangentSpace I p →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (hessianAt nabla f p)
      (fun v₁ v₂ w => hessianAt_add_left nabla f p v₁ v₂ w)
      (fun a v w => hessianAt_smul_left nabla f p a v w)
      (fun v w₁ w₂ => hessianAt_add_right nabla hf p v w₁ w₂)
      (fun a v w => hessianAt_smul_right nabla hf p a v w)
  have hB : ∀ (v w : TangentSpace I p), B v w = hessianAt nabla f p v w :=
    fun v w => rfl
  calc laplacianAt g nabla f p
      = ∑ i, B (stdOrthonormalBasis ℝ (TangentSpace I p) i)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
        simp only [laplacianAt, hB]
    _ = ∑ i, B (e i) (e i) :=
        OrthonormalBasis.sum_apply_diagonal_invariant
          (stdOrthonormalBasis ℝ (TangentSpace I p)) e B
    _ = ∑ i, hessianAt nabla f p (e i) (e i) := by
        simp only [hB]

omit [CompleteSpace E] in
/-- **Math.** Locality of the Laplacian in the function argument: if `f = f'`
near `p` then `Δf(p) = Δf'(p)`. Blueprint: eq. `laplacformula`. -/
theorem laplacianAt_congr_of_eventuallyEq (g : RiemannianMetric I M)
    (nabla : AffineConnection I M) {f f' : M → ℝ} {p : M}
    (hff' : f =ᶠ[nhds p] f') :
    laplacianAt g nabla f p = laplacianAt g nabla f' p := by
  unfold laplacianAt
  exact Finset.sum_congr rfl fun i _ =>
    hessianAt_congr_of_eventuallyEq nabla hff' _ _

end MorganTianLib

end

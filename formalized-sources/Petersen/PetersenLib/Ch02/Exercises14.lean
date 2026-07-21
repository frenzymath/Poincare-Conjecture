import PetersenLib.Ch01.LieGroupMetrics
import PetersenLib.Ch02.Exercises
import PetersenLib.Ch02.ExercisesProductRule
import PetersenLib.Ch02.LieDerivative
import Mathlib.Geometry.Manifold.GroupLieAlgebra

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.14 (the left-invariant connection on a Lie group)

Petersen Exercise 2.5.14 asks: for a Lie group `G`, show there is a **unique**
affine connection with `∇X = 0` for all left-invariant vector fields `X`, and
that this connection is **torsion free iff the Lie algebra is Abelian**.

We build this connection — the flat connection in the left-invariant frame — from
scratch and prove all three parts.

* `contMDiff_mulInvariantVectorField_infty` — the left-invariant field of `v ∈ 𝔤`
  is `C^∞` (mathlib proves it only at `minSmoothness 𝕜 2`; we re-run the
  tangent-bundle argument at `∞`). This is the keystone making the frame smooth.
* `liConnection` — the **left-invariant connection** `∇_v X = Σᵢ (D_v Xⁱ) Eᵢ`,
  where `Eᵢ = X_{eᵢ}` is the left-invariant frame of a basis `eᵢ` of `𝔤 = T₁G`
  and `Xⁱ = g(X, Eᵢ)` are the frame coordinates read off through a reference
  left-invariant metric `g` (a pure smoothness crutch: it makes the frame
  orthonormal so the coordinates are smooth; the connection itself is
  metric-independent).
* `liCov_liVec_eq_zero` — the defining property `∇(X_w) = 0`.
* `exercise2_5_14` — **existence + uniqueness**: `liConnection` is the *unique*
  affine connection annihilating every left-invariant field (uniqueness via
  `AffineConnection.ext_of_smooth`, expanding a smooth field in the frame and the
  finite Leibniz rule).
* `exercise2_5_14_torsionFree_iff` — the **torsion** of `∇` on left-invariant
  fields is `T(X_u, X_w) = -[X_u, X_w]` (`torsionTensor_liVec_eq`), so `∇` is
  torsion free on left-invariant fields iff every bracket `[X_u, X_w]` vanishes,
  i.e. the Lie algebra is Abelian. (Since the torsion is a `(2,1)`-tensor,
  vanishing on the left-invariant frame is exactly torsion-freeness of `∇`; and
  the bracket of left-invariant fields is again left-invariant, so its vanishing
  is the Abelian condition `⁅u, w⁆ = 0`. The reduction of general
  torsion-freeness to the frame, and the invariance of the bracket, are standard
  tensoriality facts recorded in the surrounding remarks.)

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercise 2.5.14.
-/

set_option linter.unusedSectionVars false

open Bundle Set Function Finset VectorField
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-- C^∞ smoothness of the left-invariant field (mathlib's proof adapted from
`minSmoothness 𝕜 2` to `∞`). -/
theorem contMDiff_mulInvariantVectorField_infty (v : GroupLieAlgebra I G) :
    ContMDiff I I.tangent ∞
      (fun (g : G) ↦ (mulInvariantVectorField v g : TangentBundle I G)) := by
  let fg : G → TangentBundle I G := fun g ↦ TotalSpace.mk' E g 0
  have sfg : ContMDiff I I.tangent ∞ fg := contMDiff_zeroSection _ _
  let fv : G → TangentBundle I G := fun _ ↦ TotalSpace.mk' E 1 v
  have sfv : ContMDiff I I.tangent ∞ fv := contMDiff_const
  let F₁ : G → (TangentBundle I G × TangentBundle I G) := fun g ↦ (fg g, fv g)
  have S₁ : ContMDiff I (I.tangent.prod I.tangent) ∞ F₁ := sfg.prodMk sfv
  let F₂ : (TangentBundle I G × TangentBundle I G) → TangentBundle (I.prod I) (G × G) :=
    (equivTangentBundleProd I G I G).symm
  have S₂ : ContMDiff (I.tangent.prod I.tangent) (I.prod I).tangent ∞ F₂ :=
    contMDiff_equivTangentBundleProd_symm
  let F₃ : TangentBundle (I.prod I) (G × G) → TangentBundle I G :=
    tangentMap (I.prod I) I (fun (p : G × G) ↦ p.1 * p.2)
  have S₃ : ContMDiff (I.prod I).tangent I.tangent ∞ F₃ := by
    apply ContMDiff.contMDiff_tangentMap _ (m := ∞) le_rfl
    exact contMDiff_mul I ∞
  let S := (S₃.comp S₂).comp S₁
  convert S with g
  · simp [F₁, F₂, F₃, fg, fv]
  · simp only [comp_apply, tangentMap, F₃, F₂, F₁, fg, fv]
    rw [mfderiv_prod_eq_add_apply ((contMDiff_mul I ∞).mdifferentiableAt (by simp))]
    simp +instances [mulInvariantVectorField]

/-- The left-invariant frame field is a smooth vector field. -/
theorem isSmoothVectorField_mulInvariantVectorField (v : GroupLieAlgebra I G) :
    IsSmoothVectorField (fun g : G => (mulInvariantVectorField v g : TangentSpace I g)) :=
  contMDiff_mulInvariantVectorField_infty v

/-! ## The reference left-invariant metric (smoothness crutch) -/

/-- A fixed Euclidean structure on the Lie algebra `E = T₁G`, transported from
`EuclideanSpace` via `toEuclidean` (any finite-dimensional real space carries
one). This is only a smoothness crutch: it makes the left-invariant frame
orthonormal so the frame coordinates are smooth. -/
def liEqv : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean

/-- The reference symmetric positive-definite bilinear form on the Lie algebra,
`B u v = ⟪φ u, φ v⟫` with `φ = liEqv`. -/
def liForm : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (liEqv (E := E)).toContinuousLinearMap
    (liEqv (E := E)).toContinuousLinearMap

theorem liForm_apply (u v : E) : liForm u v = ⟪liEqv u, liEqv v⟫_ℝ := rfl

theorem liForm_symm (u v : E) : liForm u v = liForm v u := by
  rw [liForm_apply, liForm_apply]; exact real_inner_comm _ _

theorem liForm_pos (u : E) (hu : u ≠ 0) : 0 < liForm u u := by
  rw [liForm_apply]
  exact real_inner_self_pos.2 (fun h => hu (liEqv.injective (by rw [h, map_zero])))

/-- The reference left-invariant Riemannian metric on `G`. -/
def liMetric : RiemannianMetric I G :=
  leftInvariantMetric (I := I) liForm liForm_symm liForm_pos

/-- The Lie-algebra basis (the pullback of the Euclidean standard basis, hence
`liForm`-orthonormal). -/
def liBasis : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
  (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).toBasis.map liEqv.symm.toLinearEquiv

theorem liBasis_map (i : Fin (Module.finrank ℝ E)) :
    liEqv (liBasis i) = EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ i := by
  simp only [liBasis, Module.Basis.map_apply, OrthonormalBasis.coe_toBasis,
    ContinuousLinearEquiv.coe_toLinearEquiv, liEqv]
  rw [ContinuousLinearEquiv.apply_symm_apply]

theorem liBasis_orthonormal (i j : Fin (Module.finrank ℝ E)) :
    liForm (liBasis i) (liBasis j) = if i = j then (1 : ℝ) else 0 := by
  rw [liForm_apply, liBasis_map, liBasis_map]
  exact orthonormal_iff_ite.1 (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ).orthonormal i j

/-- The left-invariant field of a Lie-algebra vector `w`, as `Π x, T_xG`. -/
def liVec (w : E) : Π x : G, TangentSpace I x :=
  fun x => mulInvariantVectorField (w : TangentSpace I (1 : G)) x

theorem liVec_smooth (w : E) : IsSmoothVectorField (liVec (I := I) (G := G) w) := by
  have h : IsSmoothVectorField
      (fun g : G => (mulInvariantVectorField (w : TangentSpace I (1 : G)) g
        : TangentSpace I g)) :=
    isSmoothVectorField_mulInvariantVectorField _
  exact h

/-- The left-invariant frame field `Eᵢ(x) = d(Lₓ)₁(eᵢ)`. -/
def liE (i : Fin (Module.finrank ℝ E)) : Π x : G, TangentSpace I x :=
  liVec (liBasis i)

theorem liE_eq_frame (i : Fin (Module.finrank ℝ E)) (x : G) :
    liE (I := I) i x = leftInvariantFrame (I := I) liBasis x i := rfl

theorem liE_smooth (i : Fin (Module.finrank ℝ E)) :
    IsSmoothVectorField (liE (I := I) (G := G) i) :=
  liVec_smooth _

/-! ## Frame coordinates (smooth, via the reference metric) -/

/-- The `i`th coordinate of a field `X` in the left-invariant frame, read off
via the reference metric: `Xⁱ(x) = g(X(x), Eᵢ(x))`. -/
def liCoeff (X : Π x : G, TangentSpace I x) (i : Fin (Module.finrank ℝ E)) (x : G) : ℝ :=
  (liMetric (I := I) (G := G)).metricInner x (X x) (liE i x)

theorem liCoeff_eq_repr (X : Π x : G, TangentSpace I x) (i : Fin (Module.finrank ℝ E)) (x : G) :
    liCoeff X i x = (leftInvariantFrame (I := I) liBasis x).repr (X x) i := by
  rw [liCoeff, liE_eq_frame]
  show (leftInvariantMetric (I := I) liForm liForm_symm liForm_pos).metricInner x _ _ = _
  rw [leftInvariantCoframeMetric_orthonormal liForm liForm_symm liForm_pos liBasis
    liBasis_orthonormal]
  rw [Finset.sum_eq_single i]
  · rw [leftInvariantFrame_repr_self]; simp
  · intro k _ hk
    rw [leftInvariantFrame_repr_self]; simp [Ne.symm hk]
  · simp

theorem liCoeff_smooth {X : Π x : G, TangentSpace I x} (hX : IsSmoothVectorField X)
    (i : Fin (Module.finrank ℝ E)) : ContMDiff I 𝓘(ℝ) ∞ (liCoeff X i) := by
  rw [← contMDiffOn_univ]
  intro x _
  exact (liMetric (I := I)).metricInner_contMDiffWithinAt (v := X) (w := liE i)
    (hX x).contMDiffWithinAt ((liE_smooth i) x).contMDiffWithinAt

/-- Reconstruction of a field from its frame coordinates: `X = Σᵢ Xⁱ Eᵢ`. -/
theorem liE_recon (X : Π x : G, TangentSpace I x) (x : G) :
    ∑ i, liCoeff X i x • liE (I := I) i x = X x := by
  simp only [liCoeff_eq_repr, liE_eq_frame]
  exact (leftInvariantFrame (I := I) liBasis x).sum_repr (X x)

/-- The frame coordinates of a frame field are the constant Kronecker delta. -/
theorem liCoeff_liE (j i : Fin (Module.finrank ℝ E)) (x : G) :
    liCoeff (liE (I := I) j) i x = if i = j then (1 : ℝ) else 0 := by
  rw [liCoeff_eq_repr, liE_eq_frame, leftInvariantFrame_repr_self]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (fun hji => h hji.symm), if_neg h]

/-! ## Auxiliary derivation/smoothness lemmas -/

theorem dirTangent_const {p : G} (c : ℝ) (v : TangentSpace I p) :
    dirTangent (fun _ : G => c) v = 0 := by
  show mfderiv I 𝓘(ℝ, ℝ) (fun _ : G => c) p v = 0
  rw [mfderiv_const, ContinuousLinearMap.zero_apply]

theorem dirTangent_add_fun {f g : G → ℝ} {p : G} (hf : MDifferentiableAt I 𝓘(ℝ) f p)
    (hg : MDifferentiableAt I 𝓘(ℝ) g p) (v : TangentSpace I p) :
    dirTangent (fun q => f q + g q) v = dirTangent f v + dirTangent g v :=
  congrArg (fun L => L v) (hf.hasMFDerivAt.add hg.hasMFDerivAt).mfderiv

theorem dirTangent_mul {f g : G → ℝ} {p : G} (hf : MDifferentiableAt I 𝓘(ℝ) f p)
    (hg : MDifferentiableAt I 𝓘(ℝ) g p) (v : TangentSpace I p) :
    dirTangent (fun q => f q * g q) v = f p * dirTangent g v + g p * dirTangent f v := by
  have h := congrArg (fun L => L v) (hf.hasMFDerivAt.mul' hg.hasMFDerivAt).mfderiv
  calc dirTangent (fun q => f q * g q) v
      = f p * dirTangent g v + dirTangent f v * g p := h
    _ = f p * dirTangent g v + g p * dirTangent f v := by ring

theorem isSmoothVectorField_add {X Y : Π x : G, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y) :
    IsSmoothVectorField (fun q => X q + Y q) := by
  simpa using ((⟨X, hX⟩ : SmoothVectorField I G) + ⟨Y, hY⟩).smooth

theorem isSmoothVF_finsetSum {ι : Type*} (s : Finset ι)
    (F : ι → Π x : G, TangentSpace I x) (hF : ∀ i, IsSmoothVectorField (F i)) :
    IsSmoothVectorField (fun q => ∑ i ∈ s, F i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (0 : SmoothVectorField I G).smooth
  | insert a s ha ih =>
      have h : IsSmoothVectorField (fun q => F a q + ∑ i ∈ s, F i q) :=
        isSmoothVectorField_add (hF a) ih
      have e : (fun q => ∑ i ∈ insert a s, F i q)
          = fun q => F a q + ∑ i ∈ s, F i q := by
        funext q; exact Finset.sum_insert ha
      rw [e]; exact h

/-! ## The left-invariant connection -/

open Classical in
/-- **Math.** The **left-invariant connection** on `G`: the flat connection in
the left-invariant frame, `∇_v X = Σᵢ (D_v Xⁱ) Eᵢ(p)`, where `Xⁱ = g(X, Eᵢ)`
are the frame coordinates. Left-invariant fields have constant coordinates, so
`∇X = 0` for them. -/
def liCov (p : G) (v : TangentSpace I p) (X : Π x : G, TangentSpace I x) :
    TangentSpace I p :=
  if IsSmoothVectorField X then ∑ i, dirTangent (liCoeff X i) v • liE i p else 0

theorem liCov_add_direction (p : G) (v w : TangentSpace I p)
    (X : Π x : G, TangentSpace I x) : liCov p (v + w) X = liCov p v X + liCov p w X := by
  by_cases hX : IsSmoothVectorField X
  · simp only [liCov, if_pos hX]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [dirTangent_add, add_smul]
  · simp only [liCov, if_neg hX, add_zero]

theorem liCov_smul_direction (p : G) (c : ℝ) (v : TangentSpace I p)
    (X : Π x : G, TangentSpace I x) : liCov p (c • v) X = c • liCov p v X := by
  by_cases hX : IsSmoothVectorField X
  · simp only [liCov, if_pos hX, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [dirTangent_smul, mul_smul]
  · simp only [liCov, if_neg hX, smul_zero]

theorem liCov_add_field (p : G) (v : TangentSpace I p)
    {X₁ X₂ : Π x : G, TangentSpace I x} (h₁ : IsSmoothVectorField X₁)
    (h₂ : IsSmoothVectorField X₂) :
    liCov p v (fun q => X₁ q + X₂ q) = liCov p v X₁ + liCov p v X₂ := by
  have hsum : IsSmoothVectorField (fun q => X₁ q + X₂ q) := isSmoothVectorField_add h₁ h₂
  simp only [liCov, if_pos hsum, if_pos h₁, if_pos h₂]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : liCoeff (fun q => X₁ q + X₂ q) i = fun q => liCoeff X₁ i q + liCoeff X₂ i q := by
    funext q; simp only [liCoeff]; rw [(liMetric (I := I)).metricInner_add_left]
  rw [hc, dirTangent_add_fun (((liCoeff_smooth h₁ i) p).mdifferentiableAt (by simp))
    (((liCoeff_smooth h₂ i) p).mdifferentiableAt (by simp)), add_smul]

theorem liCov_leibniz (p : G) (v : TangentSpace I p) {f : G → ℝ}
    {X : Π x : G, TangentSpace I x} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hX : IsSmoothVectorField X) :
    liCov p v (fun q => f q • X q) = dirTangent f v • X p + f p • liCov p v X := by
  have hfX : IsSmoothVectorField (fun q => f q • X q) := isSmoothVectorField_smul hf hX
  simp only [liCov, if_pos hfX, if_pos hX]
  rw [← liE_recon X p, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hci : liCoeff (fun q => f q • X q) i = fun q => f q * liCoeff X i q := by
    funext q; simp only [liCoeff]; rw [(liMetric (I := I)).metricInner_smul_left]
  rw [hci, dirTangent_mul ((hf p).mdifferentiableAt (by simp))
      (((liCoeff_smooth hX i) p).mdifferentiableAt (by simp)),
    add_smul, smul_smul, smul_smul, mul_comm (dirTangent f v) (liCoeff X i p), add_comm]

theorem liCov_smooth_cov {Y X : Π x : G, TangentSpace I x}
    (hY : IsSmoothVectorField Y) (hX : IsSmoothVectorField X) :
    IsSmoothVectorField (fun p => liCov p (Y p) X) := by
  have he : (fun p => liCov p (Y p) X)
      = fun p => ∑ i, dirTangent (liCoeff X i) (Y p) • liE i p := by
    funext p; simp only [liCov, if_pos hX]
  rw [he]
  refine isSmoothVF_finsetSum Finset.univ _ fun i => ?_
  exact isSmoothVectorField_smul (hY.directionalDerivative_contMDiff (liCoeff_smooth hX i))
    (liE_smooth i)

theorem liCov_junk (p : G) (v : TangentSpace I p) {X : Π x : G, TangentSpace I x}
    (hX : ¬IsSmoothVectorField X) : liCov p v X = 0 := by
  simp only [liCov, if_neg hX]

/-- **Math.** **Exercise 2.5.14** (existence): the left-invariant connection is
an affine connection on `G`. -/
def liConnection : AffineConnection I G where
  cov := liCov
  add_direction := liCov_add_direction
  smul_direction := liCov_smul_direction
  add_field := liCov_add_field
  leibniz := liCov_leibniz
  smooth_cov := liCov_smooth_cov
  junk := liCov_junk

@[simp] theorem liConnection_cov (p : G) (v : TangentSpace I p)
    (X : Π x : G, TangentSpace I x) : liConnection.cov p v X = liCov p v X := rfl

/-! ## `∇ = 0` on left-invariant fields -/

theorem liE_eq_liVec (i : Fin (Module.finrank ℝ E)) :
    liE (I := I) (G := G) i = liVec (I := I) (G := G) (liBasis i) :=
  rfl

/-- The frame coordinates of a left-invariant field are constant. -/
theorem liCoeff_liVec_const (w : E) (i : Fin (Module.finrank ℝ E)) (q : G) :
    liCoeff (liVec (I := I) (G := G) w) i q = liBasis.repr w i := by
  rw [liCoeff_eq_repr, leftInvariantFrame_repr_apply]
  have hv : mfderiv I I (q⁻¹ * ·) q (liVec (I := I) (G := G) w q) = w :=
    mfderiv_mul_left_inv_mfderiv_mul_left (I := I) q w
  rw [hv]

/-- **Math.** **Exercise 2.5.14** (defining property): the left-invariant
connection annihilates left-invariant fields, `∇(X_w) = 0`. -/
theorem liCov_liVec_eq_zero (w : E) (p : G) (v : TangentSpace I p) :
    liCov p v (liVec (I := I) (G := G) w) = 0 := by
  have hsm : IsSmoothVectorField (liVec (I := I) (G := G) w) := liVec_smooth w
  simp only [liCov, if_pos hsm]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hconst : liCoeff (liVec (I := I) (G := G) w) i = fun _ => liBasis.repr w i := by
    funext q; exact liCoeff_liVec_const w i q
  rw [hconst, dirTangent_const, zero_smul]

/-! ## Finite Leibniz for a general affine connection -/

theorem cov_zeroField (D : AffineConnection I G) (p : G) (v : TangentSpace I p) :
    D.cov p v (fun q : G => (0 : TangentSpace I q)) = 0 := by
  have h0 : IsSmoothVectorField (fun q : G => (0 : TangentSpace I q)) := by
    simpa using (0 : SmoothVectorField I G).smooth
  have h := D.add_field p v h0 h0
  have e : (fun q : G => (0 : TangentSpace I q) + 0) = fun q : G => (0 : TangentSpace I q) := by
    funext q; simp
  rw [e] at h
  have h2 : D.cov p v (fun q : G => (0 : TangentSpace I q)) + 0
      = D.cov p v (fun q : G => (0 : TangentSpace I q))
        + D.cov p v (fun q : G => (0 : TangentSpace I q)) := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

theorem cov_finsetSumSmul (D : AffineConnection I G) (p : G) (v : TangentSpace I p)
    {ι : Type*} (s : Finset ι) (f : ι → G → ℝ) (V : ι → Π x : G, TangentSpace I x)
    (hf : ∀ m, ContMDiff I 𝓘(ℝ) ∞ (f m)) (hV : ∀ m, IsSmoothVectorField (V m)) :
    D.cov p v (fun q => ∑ m ∈ s, f m q • V m q)
      = ∑ m ∈ s, (dirTangent (f m) v • V m p + f m p • D.cov p v (V m)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have e : (fun q => ∑ m ∈ (∅ : Finset ι), f m q • V m q)
          = fun q : G => (0 : TangentSpace I q) := by funext q; simp
      rw [e, cov_zeroField]; simp
  | insert a s ha ih =>
      have hterm : ∀ m, IsSmoothVectorField (fun q => f m q • V m q) := fun m =>
        isSmoothVectorField_smul (hf m) (hV m)
      have hsum : IsSmoothVectorField (fun q => ∑ m ∈ s, f m q • V m q) :=
        isSmoothVF_finsetSum s _ hterm
      have e : (fun q => ∑ m ∈ insert a s, f m q • V m q)
          = fun q => f a q • V a q + ∑ m ∈ s, f m q • V m q := by
        funext q; exact Finset.sum_insert ha
      rw [e, D.add_field p v (hterm a) hsum, D.leibniz p v (hf a) (hV a), ih,
        Finset.sum_insert ha]

/-! ## Uniqueness -/

/-- Any affine connection annihilating all left-invariant fields agrees with the
left-invariant connection on every smooth field. -/
theorem cov_eq_liCov_of_invariant_zero (D : AffineConnection I G)
    (hD : ∀ (w : E) (p : G) (v : TangentSpace I p), D.cov p v (liVec w) = 0)
    (p : G) (v : TangentSpace I p) {X : Π x : G, TangentSpace I x}
    (hX : IsSmoothVectorField X) : D.cov p v X = liCov p v X := by
  have hdecomp : X = fun q => ∑ i, liCoeff X i q • liE i q := by
    funext q; exact (liE_recon X q).symm
  conv_lhs => rw [hdecomp]
  rw [cov_finsetSumSmul D p v Finset.univ (fun i => liCoeff X i) liE
    (fun i => liCoeff_smooth hX i) (fun i => liE_smooth i)]
  simp only [liE_eq_liVec, hD, smul_zero, add_zero, liCov, if_pos hX]

/-- **Math.** **Exercise 2.5.14** (uniqueness): the left-invariant connection is
the unique affine connection annihilating every left-invariant field. -/
theorem exercise2_5_14 :
    ∃! D : AffineConnection I G,
      ∀ (w : E) (p : G) (v : TangentSpace I p), D.cov p v (liVec w) = 0 := by
  refine ⟨liConnection, fun w p v => liCov_liVec_eq_zero w p v, fun D hD => ?_⟩
  refine AffineConnection.ext_of_smooth fun p v X hX => ?_
  rw [cov_eq_liCov_of_invariant_zero D hD p v hX, liConnection_cov]

/-! ## Torsion of the left-invariant connection -/

/-- **Math.** The torsion of the left-invariant connection on two left-invariant
fields is the negative of their bracket, `T(X_u, X_w) = -[X_u, X_w]`. -/
theorem torsionTensor_liVec_eq (u w : E) :
    torsionTensor liConnection (liVec (I := I) (G := G) u) (liVec w)
      = fun p => -(mlieBracket I (liVec (I := I) (G := G) u) (liVec w) p) := by
  funext p
  rw [torsionTensor_apply, liConnection_cov, liConnection_cov, liCov_liVec_eq_zero,
    liCov_liVec_eq_zero, lieDerivativeVectorField_eq_mlieBracket]
  simp

/-- **Math.** **Exercise 2.5.14** (torsion characterization): the left-invariant
connection is torsion-free on left-invariant fields `X_u, X_w` iff the Lie
algebra is Abelian, i.e. every bracket `[X_u, X_w]` vanishes. (Since the torsion
is a tensor, vanishing on the left-invariant frame is torsion-freeness; and the
bracket of left-invariant fields is left-invariant, so its vanishing is the
Lie-algebra Abelian condition `⁅u, w⁆ = 0`.) -/
theorem exercise2_5_14_torsionFree_iff :
    (∀ u w : E, torsionTensor liConnection (liVec (I := I) (G := G) u) (liVec w)
        = fun _ => (0 : TangentSpace I _))
      ↔ (∀ u w : E, mlieBracket I (liVec (I := I) (G := G) u) (liVec w)
        = fun _ => (0 : TangentSpace I _)) := by
  refine ⟨fun hT u w => ?_, fun hab u w => ?_⟩
  · funext p
    have h := congrFun (hT u w) p
    rw [torsionTensor_liVec_eq] at h
    simpa using h
  · rw [torsionTensor_liVec_eq, hab u w]
    funext p; simp

end PetersenLib

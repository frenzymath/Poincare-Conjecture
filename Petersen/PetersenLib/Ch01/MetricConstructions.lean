import PetersenLib.Ch01.RiemannianManifolds
import PetersenLib.Foundations.LocalSection
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.Covering.Basic

/-!
# Petersen Ch. 1, §1.3 — Constructions of Riemannian metrics

Constructions of Petersen §1.3.2–§1.3.3: the product metric
(`productMetric`), left-invariant metrics on Lie groups
(`leftInvariantMetric`, with the left-invariance theorem
`leftInvariantMetric_leftInvariant`), metrics induced by covering maps
(`coveringInducedMetric`) together with the quotient-metric
existence-and-uniqueness statement (`quotientMetric`), and the flat torus
(`circleMetric`, `flatTorus`).

The product and left-invariant constructions are vendored from the shared
OpenGALib construction (`DoCarmoCh1.lean`: `DCProductForm`/`DCProductMetric`
and `DCLeftInvariantForm`/`DCLeftInvariantMetric`, identical in the openga
and DoCarmo projects), renamed into the PetersenLib namespace.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.3.
-/

open Bundle Bornology
open scoped ContDiff Manifold Topology

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## The product metric

Not singled out by Petersen in §1.3, but used throughout (Exercise 1.6.1,
doubly warped products in §1.4.5, and the flat torus of Example 1.3.6 as
`S¹ × S¹`). -/

section ProductMetric

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

/-- **Math.** Petersen Exercise 1.6.1: the **product form** on `M₁ × M₂`,
`⟨u, v⟩_{(p,q)} = ⟨dπ₁ u, dπ₁ v⟩_p + ⟨dπ₂ u, dπ₂ v⟩_q`, the sum of the two
factor metrics pulled back along the projections `π₁, π₂`. It is the sum
`pullbackForm g₁ π₁ + pullbackForm g₂ π₂` of two pullback forms in the same
bundle over `M₁ × M₂`. -/
def productForm (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) :
    TangentSpace (I₁.prod I₂) p →L[ℝ] TangentSpace (I₁.prod I₂) p →L[ℝ] ℝ :=
  pullbackForm (I := I₁.prod I₂) g₁ Prod.fst p +
    pullbackForm (I := I₁.prod I₂) g₂ Prod.snd p

/-- **Math.** The product form is symmetric, inherited termwise from `g₁` and
`g₂`. -/
theorem productForm_symm (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) (u v : TangentSpace (I₁.prod I₂) p) :
    productForm g₁ g₂ p u v = productForm g₁ g₂ p v u := by
  simp only [productForm, ContinuousLinearMap.add_apply]
  rw [pullbackForm_symm, pullbackForm_symm (F := Prod.snd)]

/-- **Math.** The product form is positive definite: for `u ≠ 0` either
`dπ₁ u = u.1 ≠ 0` or `dπ₂ u = u.2 ≠ 0`, so the corresponding summand is
strictly positive while the other is `≥ 0`. -/
theorem productForm_self_pos (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) (u : TangentSpace (I₁.prod I₂) p) (hu : u ≠ 0) :
    0 < productForm g₁ g₂ p u u := by
  have hfst : mfderiv (I₁.prod I₂) I₁ Prod.fst p u = u.1 := by rw [mfderiv_fst]; rfl
  have hsnd : mfderiv (I₁.prod I₂) I₂ Prod.snd p u = u.2 := by rw [mfderiv_snd]; rfl
  have e1 : 0 ≤ pullbackForm (I := I₁.prod I₂) g₁ Prod.fst p u u := by
    rw [pullbackForm_apply, hfst]; exact g₁.metricInner_self_nonneg _ _
  have e2 : 0 ≤ pullbackForm (I := I₁.prod I₂) g₂ Prod.snd p u u := by
    rw [pullbackForm_apply, hsnd]; exact g₂.metricInner_self_nonneg _ _
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]; exact fun h => hu (Prod.ext h.1 h.2)
  simp only [productForm, ContinuousLinearMap.add_apply]
  rcases hor with h1 | h2
  · have hp1 : 0 < pullbackForm (I := I₁.prod I₂) g₁ Prod.fst p u u := by
      rw [pullbackForm_apply, hfst]; exact g₁.metricInner_self_pos _ _ h1
    linarith
  · have hp2 : 0 < pullbackForm (I := I₁.prod I₂) g₂ Prod.snd p u u := by
      rw [pullbackForm_apply, hsnd]; exact g₂.metricInner_self_pos _ _ h2
    linarith

/-- **Math.** Petersen Exercise 1.6.1: **the product metric** on `M₁ × M₂`.
Given Riemannian metrics `g₁, g₂` on the factors,
`⟨u, v⟩_{(p,q)} = ⟨dπ₁ u, dπ₁ v⟩_p + ⟨dπ₂ u, dπ₂ v⟩_q` is a Riemannian metric:
symmetric and bilinear termwise, positive definite because `u ≠ 0` forces a
nonzero projection, and smooth as the sum of two smooth pullback sections
(`pullbackForm_contMDiff` along the smooth projections). Taking `S¹ × S¹`
gives the flat torus of Petersen Example 1.3.6. -/
def productMetric (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] :
    RiemannianMetric (I₁.prod I₂) (M₁ × M₂) where
  inner p := productForm g₁ g₂ p
  symm p u v := productForm_symm g₁ g₂ p u v
  pos p u hu := productForm_self_pos g₁ g₂ p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E₁ × E₂) (productForm g₁ g₂ p) (fun u hu => ?_)
    exact productForm_self_pos g₁ g₂ p u hu
  contMDiff :=
    ContMDiff.add_section (pullbackForm_contMDiff g₁ contMDiff_fst)
      (pullbackForm_contMDiff g₂ contMDiff_snd)

/-- **Math.** The product metric computes as the sum of the factor metrics on
the components of a product tangent vector:
`⟨u, v⟩_{(p₁,p₂)} = ⟨u₁, v₁⟩_{p₁} + ⟨u₂, v₂⟩_{p₂}` under the canonical
identification `T_{(p₁,p₂)}(M₁ × M₂) = T_{p₁}M₁ × T_{p₂}M₂` (`dπᵢ u = uᵢ`). -/
@[simp]
theorem productMetric_apply (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    (p : M₁ × M₂) (u v : TangentSpace (I₁.prod I₂) p) :
    (productMetric g₁ g₂).metricInner p u v =
      g₁.metricInner p.1 u.1 v.1 + g₂.metricInner p.2 u.2 v.2 := by
  have hfst : ∀ w : TangentSpace (I₁.prod I₂) p,
      mfderiv (I₁.prod I₂) I₁ Prod.fst p w = w.1 := fun w => by rw [mfderiv_fst]; rfl
  have hsnd : ∀ w : TangentSpace (I₁.prod I₂) p,
      mfderiv (I₁.prod I₂) I₂ Prod.snd p w = w.2 := fun w => by rw [mfderiv_snd]; rfl
  show productForm g₁ g₂ p u v = _
  simp only [productForm, ContinuousLinearMap.add_apply, pullbackForm_apply, hfst, hsnd]

end ProductMetric

/-! ## Left-invariant metrics on Lie groups (Petersen §1.3.2) -/

section LieGroupMetric

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-- **Math.** Petersen §1.3.2 (left-invariant metric): the **left-invariant
form** obtained by transporting a fixed bilinear form `b` on the Lie algebra
`T_eG` back to every tangent space through the differential of left
translation by `x⁻¹`, `⟨u, v⟩_x = b(d(L_{x⁻¹})_x u, d(L_{x⁻¹})_x v)`. Because
`L_{x⁻¹}(x) = e`, the differential `d(L_{x⁻¹})_x` lands in `T_eG` (all fibres
share the model space `E`). It is left invariant by construction
(`leftInvariantMetric_leftInvariant`). -/
def leftInvariantForm (b : E →L[ℝ] E →L[ℝ] ℝ) (x : G) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let A : E →L[ℝ] E := mfderiv I I (x⁻¹ * ·) x
  (b.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ G] [LieGroup I ∞ G] in
@[simp]
theorem leftInvariantForm_apply (b : E →L[ℝ] E →L[ℝ] ℝ) (x : G) (u v : TangentSpace I x) :
    leftInvariantForm (I := I) b x u v
      = b (mfderiv I I (x⁻¹ * ·) x u) (mfderiv I I (x⁻¹ * ·) x v) :=
  rfl

omit [IsManifold I ∞ G] in
/-- **Math.** The differential of left translation by `x⁻¹` at `x` is
injective: `L_x` is its smooth inverse, so
`d(L_x)_e ∘ d(L_{x⁻¹})_x = d(L_x ∘ L_{x⁻¹})_x = d(id)_x = 1`. -/
theorem mfderiv_mul_left_inv_injective (x : G) :
    Function.Injective (mfderiv I I (x⁻¹ * ·) x) := by
  have key : (mfderiv I I (x * ·) (x⁻¹ * x)).comp (mfderiv I I (x⁻¹ * ·) x)
      = ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    have h := (mfderiv_comp x (mdifferentiableAt_mul_left (I := I) (a := x) (b := x⁻¹ * x))
                 (mdifferentiableAt_mul_left (I := I) (a := x⁻¹) (b := x))).symm
    rw [h]
    have hcomp : ((x * ·) ∘ (x⁻¹ * ·)) = (id : G → G) := by
      funext y; simp [mul_inv_cancel_left]
    rw [hcomp, mfderiv_id]
  refine Function.LeftInverse.injective
    (g := mfderiv I I (x * ·) (x⁻¹ * x)) fun u => ?_
  have := congrArg (fun T : TangentSpace I x →L[ℝ] TangentSpace I x => T u) key
  simpa using this

omit [IsManifold I ∞ G] [LieGroup I ∞ G] in
/-- **Math.** The left-invariant form is symmetric when the seed form `b` is. -/
theorem leftInvariantForm_symm (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ u v : E, b u v = b v u) (x : G) (u v : TangentSpace I x) :
    leftInvariantForm (I := I) b x u v = leftInvariantForm (I := I) b x v u := by
  simp only [leftInvariantForm_apply]; exact hb _ _

omit [IsManifold I ∞ G] in
/-- **Math.** The left-invariant form is positive definite when the seed form
`b` is, because `d(L_{x⁻¹})_x` is injective (so `u ≠ 0 ⇒ d(L_{x⁻¹})_x u ≠ 0`). -/
theorem leftInvariantForm_pos (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ u : E, u ≠ 0 → 0 < b u u) (x : G) (u : TangentSpace I x) (hu : u ≠ 0) :
    0 < leftInvariantForm (I := I) b x u u := by
  rw [leftInvariantForm_apply]
  refine hb _ (fun h => hu ?_)
  exact mfderiv_mul_left_inv_injective x (h.trans (map_zero _).symm)

omit [IsManifold I ∞ G] in
/-- **Math.** The left-invariant form varies smoothly. In tangent coordinates
around `x₀` the section `x ↦ ⟨d(L_{x⁻¹})_x·, d(L_{x⁻¹})_x·⟩` equals
`ξ ↦ B(D x ·)(D x ·)`, where
`D x = inTangentCoordinates I I id (·⁻¹·) (mfderiv (·⁻¹ * ·)) x₀ x` is the
differential of left translation read in tangent coordinates (smooth by the
family lemma `ContMDiffAt.mfderiv`, since `(x, y) ↦ x⁻¹ * y` is smooth on a
Lie group) and `B` is the fixed seed form `b` transported through the
(constant) target coordinate change at `e`. This is a composition of smooth
model-space maps, so the coordinate representation — hence the bundle
section — is smooth. -/
theorem leftInvariantForm_contMDiff (b : E →L[ℝ] E →L[ℝ] ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : G ↦ (⟨x, leftInvariantForm (I := I) b x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x : G ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  -- Since `x⁻¹ * x = e` for all `x`, the target base point of the differential is the constant `e`,
  -- so its trivialization sits at the fixed point `e` (all coordinate changes there are constant).
  have hbase : (fun x : G => x⁻¹ * x) = (fun _ : G => (1 : G)) := by
    funext x; rw [inv_mul_cancel]
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E (TangentSpace I) (1 : G) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have ht1 : (1 : G) ∈ tT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) _
  -- `D`: the differential of left translation read in tangent coordinates, smooth by the family
  -- lemma `ContMDiffAt.mfderiv` (the joint map `(x, y) ↦ x⁻¹ * y` is smooth on a Lie group).
  set D : G → (E →L[ℝ] E) :=
    inTangentCoordinates I I id (fun _ : G => (1 : G)) (fun x => mfderiv I I (x⁻¹ * ·) x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ D x₀ := by
    have hf : ContMDiffAt (I.prod I) I ∞
        (Function.uncurry (fun x y : G => x⁻¹ * y)) (x₀, id x₀) :=
      (contMDiffAt_fst.inv).mul contMDiffAt_snd
    have hmn : (∞ : WithTop ℕ∞) + 1 ≤ ∞ := by simp
    have h0 := ContMDiffAt.mfderiv (fun x y : G => x⁻¹ * y) id hf contMDiffAt_id hmn
    simp only [id_eq] at h0
    rw [hbase] at h0
    rw [hD]; exact h0
  -- The fixed target coordinate change at `e`, packaging `b`.
  set B : E →L[ℝ] E →L[ℝ] ℝ :=
    (b.bilinearComp
      ((tT.continuousLinearEquivAt ℝ (1 : G) ht1).symm.toContinuousLinearMap : E →L[ℝ] E)
      ((tT.continuousLinearEquivAt ℝ (1 : G) ht1).symm.toContinuousLinearMap : E →L[ℝ] E)
      : E →L[ℝ] E →L[ℝ] ℝ) with hB
  have hΨ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp (B.comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun x => B.comp (D x)) x₀ :=
      (contMDiffAt_const (c := B)).clm_comp hDsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  filter_upwards [hUs] with x hx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun c => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp (B.comp (D x))) a) c
      = B (D x a) (D x c) := rfl
  -- Key: the fixed coordinate change at `e` undoes the target trivialization inside `D`.
  have hkey : ∀ u : E, (tT.continuousLinearEquivAt ℝ (1 : G) ht1).symm (D x u)
      = mfderiv I I (x⁻¹ * ·) x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (1 : G) ht1
        (mfderiv I I (x⁻¹ * ·) x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx ht1]
      rfl
    have hcoeS : (sT.symm x : E → TangentSpace I x)
        = ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hx]; rfl
    rw [hDu, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hB]
  have htrivM : trivializationAt ℝ (Bundle.Trivial G ℝ) x₀ = Bundle.Trivial.trivialization G ℝ :=
    Bundle.Trivial.eq_trivialization G ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial G ℝ) hx hx (by simp)]
  simp only [htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    leftInvariantForm_apply, ← hsT, ContinuousLinearMap.bilinearComp_apply, ← hkey a, ← hkey c]
  rfl

/-- **Math.** Petersen §1.3.2: **the left-invariant metric of a Lie group.**
Left translation trivializes `TG ≃ G × T_eG`, so any inner product `b` on the
Lie algebra `T_eG` induces a Riemannian metric on `G`,
`⟨u, v⟩_x = b(d(L_{x⁻¹})_x u, d(L_{x⁻¹})_x v)`, for which every left
translation `L_x` is a Riemannian isometry
(`leftInvariantMetric_leftInvariant`). It is symmetric
(`leftInvariantForm_symm`), positive definite (`leftInvariantForm_pos`, via
injectivity of `d(L_{x⁻¹})_x`), and smooth (`leftInvariantForm_contMDiff`,
from smoothness of the group multiplication). Distinct inner products on
`T_eG` need not give isometric metrics, so a Lie group carries no canonical
choice. -/
def leftInvariantMetric [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) :
    RiemannianMetric I G where
  inner x := leftInvariantForm (I := I) b x
  symm x u v := leftInvariantForm_symm b hsymm x u v
  pos x u hu := leftInvariantForm_pos b hpos x u hu
  isVonNBounded x := by
    refine isVonNBounded_of_posDef (E := E) (leftInvariantForm (I := I) b x) (fun u hu => ?_)
    exact leftInvariantForm_pos b hpos x u hu
  contMDiff := leftInvariantForm_contMDiff b

/-- **Math.** Petersen §1.3.2: the metric `leftInvariantMetric b` is
**left invariant** — every left translation `L_x : y ↦ x * y` preserves it.
Chain rule: the form at `x * y` evaluates `b` through
`d(L_{(xy)⁻¹})_{xy} ∘ d(L_x)_y = d(L_{(xy)⁻¹} ∘ L_x)_y = d(L_{y⁻¹})_y`
(since `(xy)⁻¹ · (x·z) = y⁻¹·z`), which is exactly the form at `y`. -/
theorem leftInvariantMetric_leftInvariant [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) (x : G) :
    PreservesMetric (leftInvariantMetric (I := I) b hsymm hpos)
      (leftInvariantMetric (I := I) b hsymm hpos) (x * ·) := by
  intro y u v
  have hxy : ∀ w : TangentSpace I y,
      mfderiv I I ((x * y)⁻¹ * ·) (x * y) (mfderiv I I (x * ·) y w)
        = mfderiv I I (y⁻¹ * ·) y w := by
    intro w
    have hfun : (((x * y)⁻¹ * ·) ∘ (x * ·) : G → G) = (y⁻¹ * ·) := by
      funext z
      show (x * y)⁻¹ * (x * z) = y⁻¹ * z
      simp [mul_assoc]
    have h1 : mfderiv I I (((x * y)⁻¹ * ·) ∘ (x * ·)) y w
        = mfderiv I I ((x * y)⁻¹ * ·) (x * y) (mfderiv I I (x * ·) y w) :=
      mfderiv_comp_apply y
        (mdifferentiableAt_mul_left (I := I) (a := (x * y)⁻¹) (b := x * y))
        (mdifferentiableAt_mul_left (I := I) (a := x) (b := y)) w
    rw [← h1, hfun]
  show leftInvariantForm (I := I) b y u v
      = leftInvariantForm (I := I) b (x * y)
          (mfderiv I I (x * ·) y u) (mfderiv I I (x * ·) y v)
  simp only [leftInvariantForm_apply]
  rw [hxy u, hxy v]

/-- **Math.** Petersen §1.3.2: every left translation `L_x` is a full
**Riemannian isometry** of `(G, leftInvariantMetric b)` — it is a
diffeomorphism (with smooth inverse `L_{x⁻¹}`) and preserves the metric. -/
theorem leftInvariantMetric_isRiemannianIsometry [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) (x : G) :
    IsRiemannianIsometry (leftInvariantMetric (I := I) b hsymm hpos)
      (leftInvariantMetric (I := I) b hsymm hpos) (x * ·) := by
  refine ⟨⟨⟨⟨(x * ·), (x⁻¹ * ·), fun z => by simp, fun z => by simp⟩,
      contMDiff_mul_left, contMDiff_mul_left⟩, rfl⟩, ?_⟩
  exact leftInvariantMetric_leftInvariant b hsymm hpos x

end LieGroupMetric

/-! ## Covering maps and quotient metrics (Petersen §1.3.3) -/

section Covering

variable [FiniteDimensional ℝ E]

/-- **Math.** Petersen §1.3.3: a covering map `F : M → N` is both an immersion
and a submersion, so a Riemannian metric on `N` **pulls back** to `M`
(`F^*g_N`), making `F` an isometric immersion (a *Riemannian covering*); since
`dim M = dim N`, `F` is in fact a local isometry
(`coveringInducedMetric_isLocalIsometry`). The immersion half of the covering
hypothesis is what the pullback construction consumes, so the definition is
literally `pullbackMetric`. -/
def coveringInducedMetric (gN : RiemannianMetric I' M') (F : M → M')
    (hF : IsSmoothImmersion (I := I) (I' := I') F) :
    RiemannianMetric I M :=
  pullbackMetric gN F hF

/-- **Math.** Petersen §1.3.3: with the covering-induced metric upstairs, the
covering `F` preserves inner products of tangent vectors,
`⟨u, v⟩_p = ⟨DF(u), DF(v)⟩_{F(p)}` — the metric clause of `F` being a **local
isometry** (`DF_p` is additionally a linear isomorphism since
`dim M = dim N`). True by definition of the pullback. -/
theorem coveringInducedMetric_isLocalIsometry (gN : RiemannianMetric I' M')
    (F : M → M') (hF : IsSmoothImmersion (I := I) (I' := I') F)
    (p : M) (u v : TangentSpace I p) :
    (coveringInducedMetric gN F hF).metricInner p u v =
      gN.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v) :=
  rfl

/-- **Math.** The covering-induced metric makes the covering map a
metric-preserving map: `F^*g_N = g_M` by construction. -/
theorem coveringInducedMetric_preservesMetric (gN : RiemannianMetric I' M')
    (F : M → M') (hF : IsSmoothImmersion (I := I) (I' := I') F) :
    PreservesMetric (coveringInducedMetric gN F hF) gN F :=
  fun _ _ _ => rfl

omit [FiniteDimensional ℝ E] in
/-- **Eng.** Two Riemannian metrics with the same inner products agree; all
remaining structure fields are propositions. -/
theorem RiemannianMetric.ext_inner {g₁ g₂ : RiemannianMetric I M}
    (h : ∀ x : M, g₁.inner x = g₂.inner x) : g₁ = g₂ := by
  obtain ⟨inn₁, symm₁, pos₁, bdd₁, cont₁⟩ := g₁
  obtain ⟨inn₂, symm₂, pos₂, bdd₂, cont₂⟩ := g₂
  obtain rfl : inn₁ = inn₂ := funext h
  rfl

/-- **Math.** Petersen §1.3.3 (quotient metric): if `(M, g)` is Riemannian and
a group `Γ` acts on `M` by isometries with quotient `N = M/Γ`, there is a
*unique* Riemannian metric on `N` making the quotient map a local isometry.

Mathlib has no quotient-manifold construction, so the quotient is
represented by hypotheses: a smooth manifold `M'`, a map `q : M → M'` that is
a surjective smooth covering map whose differentials are linear isomorphisms
(the "local diffeomorphism" content of a same-dimension covering), and the
`Γ`-invariance of `g` phrased fibrewise on the deck-transformation relation
`q p = q p'`: vectors over `p` and `p'` with the same image under `Dq` have
the same inner products. (For a normal covering with deck group `Γ` this is
exactly "`Γ` acts by isometries": `u' = Dγ(u)` iff `Dq_{p'}(u') = Dq_p(u)`.)
The conclusion is the existence of a unique metric `gN` on `M'` with
`q^*g_N = g` — the local-isometry clause for `q`.

Both halves are now proved.  Uniqueness follows from surjectivity of `q` and of
its differentials (they force the value of `gN` on every tangent plane).  For
existence, `gN` is defined at `y` by transporting `g` through the *inverse* of
the (bijective) differential of `q` at any point over `y` — well defined by
`hinv` — and its smoothness is exactly where the local sections of
`PetersenLib.exists_localSection_of_mfderiv_surjective` are used: near `y₀`,
choosing a smooth local section `s` of `q`, one has `Ds_y = (Dq_{s y})⁻¹`
(`mfderiv_localSection_eq_symm`), so the candidate metric *coincides with the
pullback* `s^*g` near `y₀`, and `pullbackForm_contMDiffAt` applies. -/
theorem quotientMetric [FiniteDimensional ℝ E'] [I.Boundaryless] [I'.Boundaryless]
    (g : RiemannianMetric I M) (q : M → M')
    (hq_cont : ContMDiff I I' ∞ q)
    (hq_cov : IsCoveringMap q)
    (hq_surj : Function.Surjective q)
    (hq_bij : ∀ p : M, Function.Bijective (mfderiv I I' q p))
    (hinv : ∀ (p p' : M), q p = q p' →
      ∀ (u v : TangentSpace I p) (u' v' : TangentSpace I p'),
        mfderiv I I' q p u = mfderiv I I' q p' u' →
        mfderiv I I' q p v = mfderiv I I' q p' v' →
        g.metricInner p u v = g.metricInner p' u' v') :
    ∃! gN : RiemannianMetric I' M', PreservesMetric g gN q := by
  classical
  obtain ⟨gN, hgN⟩ : ∃ gN : RiemannianMetric I' M', PreservesMetric g gN q := by
    -- `D p : E →L[ℝ] E'` is the differential of `q` at `p` (the tangent spaces are
    -- definitionally the model spaces), and `Inv p` is its inverse.
    set D : M → (E →L[ℝ] E') := fun p => mfderiv I I' q p with hD
    have hDbij : ∀ p : M, Function.Bijective (D p) := hq_bij
    set Eqv : ∀ p : M, E ≃ₗ[ℝ] E' := fun p =>
      LinearEquiv.ofBijective (D p).toLinearMap (hDbij p) with hEqv
    set Inv : M → (E' →L[ℝ] E) := fun p =>
      LinearMap.toContinuousLinearMap (Eqv p).symm with hInv
    have hInv_right : ∀ (p : M) (u : E'), D p (Inv p u) = u := fun p u =>
      (Eqv p).apply_symm_apply u
    have hInv_left : ∀ (p : M) (w : E), Inv p (D p w) = w := fun p w =>
      (Eqv p).symm_apply_apply w
    -- The candidate form at a point `p` of the fibre.
    set B : M → (E →L[ℝ] E →L[ℝ] ℝ) := fun p => g.inner p with hB
    set QF : M → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun p =>
      ((B p).bilinearComp (Inv p) (Inv p) : E' →L[ℝ] E' →L[ℝ] ℝ) with hQF
    have hQF_apply : ∀ (p : M) (u v : E'),
        QF p u v = g.metricInner p (Inv p u) (Inv p v) := fun _ _ _ => rfl
    -- Well definedness across a fibre: this is exactly `hinv`.
    have hwd : ∀ (p p' : M), q p = q p' → ∀ u v : E', QF p u v = QF p' u v := by
      intro p p' hpp' u v
      rw [hQF_apply, hQF_apply]
      exact hinv p p' hpp' (Inv p u) (Inv p v) (Inv p' u) (Inv p' v)
        ((hInv_right p u).trans (hInv_right p' u).symm)
        ((hInv_right p v).trans (hInv_right p' v).symm)
    -- Choose a point over each `y`.
    choose pt hpt using hq_surj
    have hQFsymm : ∀ (p : M) (u v : E'), QF p u v = QF p v u := by
      intro p u v; rw [hQF_apply, hQF_apply, g.metricInner_comm]
    have hInv_ne : ∀ (p : M) (u : E'), u ≠ 0 → Inv p u ≠ 0 := by
      intro p u hu h0
      apply hu
      rw [← hInv_right p u, h0, map_zero]
    have hQFpos : ∀ (p : M) (u : E'), u ≠ 0 → 0 < QF p u u := by
      intro p u hu
      rw [hQF_apply]
      exact g.metricInner_self_pos p _ (hInv_ne p u hu)
    refine ⟨{ inner := fun y => QF (pt y)
              symm := fun y u v => hQFsymm (pt y) u v
              pos := fun y u hu => hQFpos (pt y) u hu
              isVonNBounded := fun y =>
                isVonNBounded_of_posDef (E := E') (QF (pt y)) (fun u hu => hQFpos (pt y) u hu)
              contMDiff := ?_ }, ?_⟩
    · -- Smoothness: near `y₀` the candidate is the pullback along a local section.
      intro y₀
      set p₀ := pt y₀ with hp₀
      have hqp₀ : q p₀ = y₀ := hpt y₀
      obtain ⟨s, hs0, hsdiff, hssec, hsmd⟩ :=
        exists_localSection_of_mfderiv_surjective (q := q) (p := p₀)
          hq_cont.contMDiffAt (hq_bij p₀).2
      rw [hqp₀] at hs0 hsdiff hssec hsmd
      -- Near `y₀`, `QF (pt y) = pullbackForm g s y`.
      have hkey : ∀ᶠ y in 𝓝 y₀,
          QF (pt y) = pullbackForm (I := I') (I' := I) g s y := by
        filter_upwards [hssec, hsmd, hssec.eventually_nhds] with y hy hmd hy2
        -- `Ds_y` inverts `Dq_{s y}`, so `Inv (s y) = Ds_y`.
        have hqmd : MDifferentiableAt I I' q (s y) := hq_cont.mdifferentiableAt (by simp)
        have hDs : ∀ u : E', Inv (s y) u = (mfderiv I' I s y : E' →L[ℝ] E) u := by
          intro u
          have h1 : (mfderiv I I' q (s y) : E →L[ℝ] E')
              ((mfderiv I' I s y : E' →L[ℝ] E) u) = u :=
            mfderiv_localSection_eq_symm hmd hqmd hy2 u
          have h2 : (mfderiv I I' q (s y) : E →L[ℝ] E') (Inv (s y) u) = u := hInv_right (s y) u
          exact (hq_bij (s y)).1 (h2.trans h1.symm)
        refine ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v => ?_
        have hfib : q (pt y) = q (s y) := by rw [hpt y, hy]
        rw [hwd (pt y) (s y) hfib u v, hQF_apply, hDs u, hDs v]
        rfl
      -- Transfer smoothness from the pullback form.
      refine (pullbackForm_contMDiffAt (I := I') (I' := I) g hsdiff).congr_of_eventuallyEq ?_
      filter_upwards [hkey] with y hy
      rw [hy]
    · -- `q` preserves the metric: this is `hwd` plus `Inv ∘ Dq = id`.
      intro p u v
      show g.metricInner p u v = QF (pt (q p)) _ _
      have hfib : q (pt (q p)) = q p := hpt (q p)
      have e1 : Inv p ((mfderiv I I' q p : E →L[ℝ] E') u) = u := hInv_left p u
      have e2 : Inv p ((mfderiv I I' q p : E →L[ℝ] E') v) = v := hInv_left p v
      rw [hwd (pt (q p)) p hfib, hQF_apply, e1, e2]
  refine ⟨gN, hgN, fun gN' hgN' => ?_⟩
  refine RiemannianMetric.ext_inner fun y => ?_
  obtain ⟨p, rfl⟩ := hq_surj y
  refine ContinuousLinearMap.ext fun u' => ContinuousLinearMap.ext fun v' => ?_
  obtain ⟨u, rfl⟩ := (hq_bij p).2 u'
  obtain ⟨v, rfl⟩ := (hq_bij p).2 v'
  exact (hgN' p u v).symm.trans (hgN p u v)

end Covering

/-! ## The flat torus (Petersen Example 1.3.6) -/

section FlatTorus

open Complex

attribute [local instance] finrank_real_complex_fact'

/-- **Math.** The inclusion `S¹ ↪ ℂ` of the unit circle is smooth
(`contMDiff_coe_sphere` specialised to `Circle = sphere (0 : ℂ) 1`). -/
theorem contMDiff_circle_coe :
    ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) :=
  contMDiff_coe_sphere (E := ℂ) (n := 1)

/-- **Math.** The differential of the inclusion `S¹ ↪ ℂ` is injective at every
point (`mfderiv_coe_sphere_injective`): the circle inclusion is an immersion. -/
theorem mfderiv_circle_coe_injective (z : Circle) :
    Function.Injective (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) z) :=
  mfderiv_coe_sphere_injective (E := ℂ) (n := 1) z

/-- **Math.** The inclusion `S¹ ↪ ℂ` is a smooth immersion. -/
theorem isSmoothImmersion_circle_coe :
    IsSmoothImmersion (I := 𝓡 1) (I' := 𝓘(ℝ, ℂ)) (fun z : Circle => (z : ℂ)) :=
  ⟨contMDiff_circle_coe, fun z => mfderiv_circle_coe_injective z⟩

/-- **Math.** The **canonical metric on the circle** `S¹ ⊂ ℂ`: the pullback of
the inner-product metric of `ℂ ≃ ℝ²` along the (smooth, immersive) inclusion
`S¹ ↪ ℂ` — the round metric on `S¹(1)`, cf. Petersen Example 1.1.3 with
`n = 1`. -/
def circleMetric : RiemannianMetric (𝓡 1) Circle :=
  pullbackMetric (innerProductSpaceMetric ℂ) (fun z : Circle => (z : ℂ))
    isSmoothImmersion_circle_coe

/-- **Math.** Petersen Example 1.3.6: **the flat torus** `T² = S¹ × S¹` with
the product of the canonical circle metrics.

Petersen constructs the flat torus as the quotient `ℝ²/ℤ²` for a lattice
spanned by a basis `v₁, v₂`, with the flat metric induced by the isometric
translation action (the metric depends on `|v₁|, |v₂|, ∠(v₁,v₂)`, and distinct
lattices need not give isometric tori). Mathlib has no quotient-manifold
construction (see `quotientMetric`), so the faithful formalizable model is the
product of two unit circles — the member of Petersen's family corresponding to
the square lattice; it is flat, and as a product of the Lie group `S¹` with
itself the metric is bi-invariant. -/
def flatTorus : RiemannianMetric ((𝓡 1).prod (𝓡 1)) (Circle × Circle) :=
  productMetric circleMetric circleMetric

end FlatTorus

end PetersenLib

/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": the pullback metric of an immersion.

Lee's Lemma 2.11: if `(M̃, g̃)` is a Riemannian manifold, `M` is a smooth
manifold and `F : M → M̃` is smooth, then the smooth `2`-tensor field
`g = F^* g̃` is a Riemannian metric on `M` if and only if `F` is an immersion.

This is the source of most of the metrics one meets: every submanifold of a
Riemannian manifold inherits one, by pulling back along the inclusion.

The pullback form `(F^* g̃)_p(v,w) = g̃_{F(p)}(dF_p v, dF_p w)` is symmetric
for free, and smooth for free (Lee's "smooth `2`-tensor field" is part of the
hypothesis).  The whole content of the lemma is therefore that *positive
definiteness of the pullback is equivalent to injectivity of the differential*,
which is `pullbackForm_posDef_iff_immersion` below:

* if `dF_p` is injective and `v ≠ 0` then `dF_p v ≠ 0`, so
  `g̃(dF_p v, dF_p v) > 0`;
* conversely if `dF_p v = 0` for some `v ≠ 0`, the pullback form has
  `(F^* g̃)_p(v,v) = g̃(0,0) = 0`, so it is not positive definite.

`pullbackMetric` then packages the pullback of a smooth immersion as a
`RiemannianMetric`, which additionally requires discharging the smoothness of
the resulting section of the bilinear-form bundle.

Provenance: the smoothness argument `pullbackForm_contMDiff` is vendored from
the shared OpenGALib development (`OpenGALib/Riemannian/Manifold/DoCarmoCh1.lean`,
do Carmo Ch. 1 Ex. 2.5), for the reasons recorded in `LeeLib.Ch02.MetricExistence`.
The equivalence `pullbackForm_posDef_iff_immersion` — Lee's actual Lemma 2.11,
which is an "if and only if" where do Carmo's exercise asks only for one
direction — is new here.
-/
import LeeLib.Ch02.MetricExistence
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom

namespace LeeLib.Ch02

open Bornology Bundle Manifold ContinuousLinearMap
open scoped Manifold ContDiff Topology

section Pullback

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **The pullback of a field of bilinear forms** along a smooth map:
`(F^* b)_p(v,w) = b_{F(p)}(dF_p v, dF_p w)`.

Stated for a bare family of forms rather than for a metric, because pulling back uses
*nothing* about the form beyond bilinearity — not positivity, not nondegeneracy, not even
symmetry.  Both `pullbackForm` (Riemannian) and `pseudoPullbackForm` (indefinite) are this
definition applied to their respective form fields, and both inherit
`contMDiff_pullbackFormOf` rather than reproving smoothness. -/
noncomputable def pullbackFormOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I I' F p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := b (F p)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp] theorem pullbackFormOf_apply
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pullbackFormOf b F p v w = b (F p) (mfderiv I I' F p v) (mfderiv I I' F p w) :=
  rfl

/-- **The pullback form** `(F^* g̃)_p(v,w) = g̃_{F(p)}(dF_p v, dF_p w)` (Lee, §2.3):
the bilinear form on `T_p M` obtained by transporting the metric of the target
through the differential of `F`. -/
noncomputable def pullbackForm (g' : RiemannianMetric I' M') (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  pullbackFormOf (fun y => g'.inner y) F p

omit [IsManifold I ∞ M] in
@[simp] theorem pullbackForm_apply (g' : RiemannianMetric I' M') (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pullbackForm g' F p v w = g'.inner (F p) (mfderiv I I' F p v) (mfderiv I I' F p w) :=
  rfl

omit [IsManifold I ∞ M] in
/-- The pullback form is symmetric, inherited from the symmetry of `g̃`. -/
theorem pullbackForm_symm (g' : RiemannianMetric I' M') (F : M → M') (p : M)
    (v w : TangentSpace I p) :
    pullbackForm g' F p v w = pullbackForm g' F p w v := by
  simp only [pullbackForm_apply]
  exact g'.symm _ _ _

omit [IsManifold I ∞ M] in
/-- **Lee's Lemma 2.11**: the pullback `F^* g̃` is positive definite exactly when `F`
is an immersion.

Together with `pullbackForm_symm` (symmetry, automatic) and `pullbackForm_contMDiff`
(smoothness, automatic for smooth `F`), this is the whole content of Lee's lemma:
`F^* g̃` is a Riemannian metric if and only if `F` is an immersion. -/
theorem pullbackForm_posDef_iff_immersion (g' : RiemannianMetric I' M') (F : M → M') :
    (∀ (p : M) (v : TangentSpace I p), v ≠ 0 → 0 < pullbackForm g' F p v v) ↔
      ∀ p : M, Function.Injective (mfderiv I I' F p) := by
  constructor
  · -- positive definite ⟹ immersion: a vector in the kernel has length zero
    intro hpos p
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hv0
    have := hpos p v hv0
    rw [pullbackForm_apply, hv] at this
    simp at this
  · -- immersion ⟹ positive definite: `dF_p v ≠ 0`, so `g̃(dF_p v, dF_p v) > 0`
    intro himm p v hv
    rw [pullbackForm_apply]
    exact g'.pos _ _ fun h => hv (himm p (by rw [h, map_zero]))

/-- **A field of bilinear forms transported by a family of linear maps**:
`(A^* b)_p(v, w) = b_{F p}(A_p v, A_p w)`, for an arbitrary family `A_p : T_p M →
T_{F p} M'` covering `F`.

`pullbackFormOf` is the case `A = dF`.  The generality is what Lee's Theorem 2.28
needs: there the transporting family is the horizontal lift of a Riemannian
submersion, which is not the differential of any map.

As in `pullbackFormOf`, both `A p` and `b (F p)` must be pinned to the model
spaces — `TangentSpace` carries no norm, so `bilinearComp` cannot see its normed
structure otherwise. -/
noncomputable def bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) {F : M → M'}
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x)) (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A' : E →L[ℝ] E' := A p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := b (F p)
  (B.bilinearComp A' A' : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp] theorem bilinearCompOf_apply
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) {F : M → M'}
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x)) (p : M)
    (v w : TangentSpace I p) :
    bilinearCompOf b A p v w = b (F p) (A p v) (A p w) :=
  rfl

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- `pullbackFormOf` is `bilinearCompOf` for the family of differentials. -/
theorem pullbackFormOf_eq_bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ) (F : M → M') (p : M) :
    pullbackFormOf b F p = bilinearCompOf b (fun x => mfderiv I I' F x) p :=
  rfl

/-- **A smooth field of bilinear forms, transported by a smooth family of linear
maps, is smooth.**

Given a smooth field of bilinear forms `b` on `M'`, a map `F : M → M'` smooth at
`x₀`, and a family of linear maps `A x : T_x M → T_{F x} M'` whose representation
in tangent coordinates is smooth at `x₀`, the field `x ↦ b_{F x}(A x ·, A x ·)`
is a smooth section of the bilinear-form bundle of `M` at `x₀`.

Read in tangent coordinates around `x₀`, that section is `ξ ↦ G(F x)(D x ·)(D x ·)`,
where `D x` is `A x` read in tangent coordinates and `G` is `b` read in
coordinates.  This is a composition of smooth model-space-valued maps, so the
coordinate representation — hence the section itself — is smooth.

The family `A` is left abstract, and the hypotheses are local, because the two
consumers need exactly that:

* `contMDiff_pullbackFormOf` is the case `A = dF`, whose coordinate smoothness is
  mathlib's `ContMDiffAt.mfderiv_const`;
* Lee's Theorem 2.28 (`LeeLib.Ch02.existsUnique_isRiemannianSubmersion_metric`,
  via `LeeLib.Ch02.contMDiff_quotientInner`) is the case where `A` is the
  horizontal lift of a Riemannian submersion along a *local* section `σ`.  That `A` is not the differential of any map, and `σ` is
  smooth only at the one point that `LeeLib.AppendixA.exists_localSection`
  provides — hence `ContMDiffAt` rather than `ContMDiff` throughout.

Positivity and symmetry play no part, which is why this is stated for a bare
family of forms. -/
theorem contMDiffAt_bilinearCompOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (hb : ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y ↦ (⟨y, b y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))))
    {F : M → M'} {x₀ : M} (hF : ContMDiffAt I I' ∞ F x₀)
    (A : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I' (F x))
    (hA : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ (inTangentCoordinates I I' id F A x₀) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, bilinearCompOf b A x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (F x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : F x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') (F x₀)
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id F A x₀ with hD
  set G : M' → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace I') (E' →L[ℝ] ℝ)
      (fun y => TangentSpace I' y →L[ℝ] ℝ) (F x₀) y (F x₀) y (b y) with hG
  have hGsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G (F x₀) :=
    ((contMDiffAt_hom_bundle _).mp hb.contMDiffAt).2
  have hΨ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((G (F x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (G (F x)).comp (D x)) x₀ :=
      (hGsmooth.comp x₀ hF).clm_comp hA
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hA).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | F x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hF.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b' => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp ((G (F x)).comp (D x))) a) b'
      = G (F x) (D x a) (D x b') := rfl
  -- the target coordinate change undoes itself through `A`
  have hkey : ∀ u : E, tT.symm (F x) (D x u) = A x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (F x) hfx
        (A x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (F x) : E' → TangentSpace I' (F x))
        = ⇑(tT.continuousLinearEquivAt ℝ (F x) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]; rfl
    have hcoeS : (sT.symm x : E → TangentSpace I x)
        = ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hx]; rfl
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hG]
  have htrivM' :
      trivializationAt ℝ (Bundle.Trivial M' ℝ) (F x₀) = Bundle.Trivial.trivialization M' ℝ :=
    Bundle.Trivial.eq_trivialization M' ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    bilinearCompOf_apply, ← htT, ← hsT, hkey]

/-- **The pullback of a smooth field of bilinear forms is smooth.**

The case `A = dF` of `contMDiffAt_bilinearCompOf`: the differential of a smooth
map is smooth in tangent coordinates, which is mathlib's
`ContMDiffAt.mfderiv_const`.

Positivity plays no part, which is why this is stated for a bare smooth family of forms:
`pullbackForm_contMDiff` and `pseudoPullbackForm_contMDiff` are both instances of it. -/
theorem contMDiff_pullbackFormOf
    (b : ∀ y : M', TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ)
    (hb : ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y ↦ (⟨y, b y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))))
    {F : M → M'} (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackFormOf b F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := fun x₀ =>
  contMDiffAt_bilinearCompOf b hb hF.contMDiffAt (fun x => mfderiv I I' F x)
    (hF.contMDiffAt.mfderiv_const (by simp))

/-- The pullback form of a smooth map varies smoothly with the base point — the Riemannian
case of `contMDiff_pullbackFormOf`. -/
theorem pullbackForm_contMDiff (g' : RiemannianMetric I' M') {F : M → M'}
    (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackForm g' F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
  contMDiff_pullbackFormOf (fun y => g'.inner y) g'.contMDiff hF

variable [FiniteDimensional ℝ E]

/-- **The metric induced by a smooth immersion** (Lee, Lemma 2.11 and the
definition following it): if `F : M → M̃` is a smooth immersion and `g̃` is a
Riemannian metric on `M̃`, then `F^* g̃` is a Riemannian metric on `M`.

Specializing to the inclusion of a submanifold gives Lee's induced metric on a
Riemannian submanifold — in particular the round metric on `S^n` (Lee, Example
2.13), pulled back from the Euclidean metric of `ℝ^{n+1}`. -/
noncomputable def pullbackMetric (g' : RiemannianMetric I' M') (F : M → M')
    (hF : ContMDiff I I' ∞ F) (himm : ∀ p : M, Function.Injective (mfderiv I I' F p)) :
    RiemannianMetric I M where
  inner p := pullbackForm g' F p
  symm p v w := pullbackForm_symm g' F p v w
  pos p v hv := (pullbackForm_posDef_iff_immersion g' F).mpr himm p v hv
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (F := E) (pullbackForm g' F p) (fun v hv => ?_)
    exact (pullbackForm_posDef_iff_immersion g' F).mpr himm p v hv
  contMDiff := pullbackForm_contMDiff g' hF

end Pullback

end LeeLib.Ch02

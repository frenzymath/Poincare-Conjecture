import PetersenLib.Foundations.RiemannianMetric
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Bounded

/-!
# Petersen Ch. 1, §1.1 — Riemannian manifolds and maps

The abstract spine of Petersen §1.1: Riemannian isometries
(`IsRiemannianIsometry`), the metric of an inner product space
(`innerProductSpaceMetric`, `euclideanMetric`), pullback metrics along
immersions (`pullbackMetric`, `IsRiemannianImmersion`), Riemannian
submersions (`IsRiemannianSubmersion`, `orthogonalProjectionSubmersion`),
and pseudo-Riemannian metrics with their index
(`PseudoRiemannianMetric`, `pseudoRiemannianIndex`, `minkowskiMetric`).

The pullback-metric smoothness argument is adapted from the shared
DoCarmoLib construction (`DoCarmoCh1.lean`: `DCInducedForm`,
`DCInducedForm_contMDiff`, `DCInducedMetric`, identical in the openga and
DoCarmo projects).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.1.
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

/-! ## Riemannian isometries (Petersen §1.1) -/

/-- **Math.** Petersen §1.1: `F` **preserves the metric** (`F^*g_N = g_M`) if
its differential carries the inner product of `gM` to that of `gN` at every
point: `g_M(u, v) = g_N(DF(u), DF(v))` for all `p ∈ M` and `u, v ∈ T_pM`. -/
def PreservesMetric (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M')
    (F : M → M') : Prop :=
  ∀ (p : M) (u v : TangentSpace I p),
    gM.metricInner p u v =
      gN.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v)

/-- **Math.** Petersen §1.1, Def. of Riemannian isometry: a **Riemannian
isometry** between Riemannian manifolds `(M, g_M)` and `(N, g_N)` is a
diffeomorphism `F : M → N` such that `F^*g_N = g_M`, i.e.
`g_N(DF(u), DF(v)) = g_M(u, v)` for all `p ∈ M`, `u, v ∈ T_pM`. -/
def IsRiemannianIsometry (gM : RiemannianMetric I M)
    (gN : RiemannianMetric I' M') (F : M → M') : Prop :=
  (∃ Φ : Diffeomorph I I' M M' ∞, ⇑Φ = F) ∧ PreservesMetric gM gN F

theorem IsRiemannianIsometry.preservesMetric {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {F : M → M'}
    (h : IsRiemannianIsometry gM gN F) : PreservesMetric gM gN F :=
  h.2

/-- **Math.** The identity is a Riemannian isometry of `(M, g)` to itself. -/
theorem isRiemannianIsometry_id (g : RiemannianMetric I M) :
    IsRiemannianIsometry g g (id : M → M) := by
  refine ⟨⟨Diffeomorph.refl I M ∞, rfl⟩, fun p u v => ?_⟩
  have h : mfderiv I I (id : M → M) p = ContinuousLinearMap.id ℝ (TangentSpace I p) :=
    mfderiv_id
  rw [h]
  rfl

/-! ## Inner product spaces as Riemannian manifolds
(Petersen Examples 1.1.1, 1.1.2) -/

section InnerProductSpace

variable (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** Petersen Example 1.1.2: any real inner product space `V` becomes
a Riemannian manifold by giving each tangent space `T_pV = V` the ambient inner
product: `g((p,v), (p,w)) = v ⋅ w`. This wraps Mathlib's
`riemannianMetricVectorSpace`, weakening its analytic smoothness to `C^∞`. -/
def innerProductSpaceMetric : RiemannianMetric 𝓘(ℝ, F) F :=
  { riemannianMetricVectorSpace F with
    contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }

@[simp]
theorem innerProductSpaceMetric_apply (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    (innerProductSpaceMetric F).metricInner x v w = @inner ℝ F _ v w :=
  rfl

end InnerProductSpace

/-- **Math.** Petersen Example 1.1.1: **Euclidean space** `(ℝⁿ, g_{ℝⁿ})`, the
most fundamental Riemannian manifold. Via the canonical identification
`Tℝⁿ ≃ ℝⁿ × ℝⁿ`, the metric is `g((p,v), (p,w)) = v ⋅ w`, the standard
Euclidean inner product on each tangent space. -/
def euclideanMetric (n : ℕ) :
    RiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin n)) :=
  innerProductSpaceMetric (EuclideanSpace ℝ (Fin n))

@[simp]
theorem euclideanMetric_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    (euclideanMetric n).metricInner x v w = @inner ℝ (EuclideanSpace ℝ (Fin n)) _ v w :=
  rfl

section LinearIsometry

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- **Math.** Petersen Example 1.1.2: a **linear isometry** between inner
product spaces (viewed as Riemannian manifolds via
`innerProductSpaceMetric`) is a Riemannian isometry; hence any two isometric
inner product spaces of the same dimension are isometric as Riemannian
manifolds. -/
theorem linearIsometryEquiv_isRiemannianIsometry (e : F ≃ₗᵢ[ℝ] W) :
    IsRiemannianIsometry (innerProductSpaceMetric F) (innerProductSpaceMetric W) e := by
  constructor
  · exact ⟨e.toContinuousLinearEquiv.toDiffeomorph, rfl⟩
  · intro p u v
    have hmf : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, W) e p
        = (e.toContinuousLinearEquiv : F →L[ℝ] W) := by
      rw [mfderiv_eq_fderiv]
      exact (e.toContinuousLinearEquiv : F →L[ℝ] W).fderiv
    rw [innerProductSpaceMetric_apply, innerProductSpaceMetric_apply, hmf]
    exact (e.inner_map_map u v).symm

end LinearIsometry

/-! ## Pullback metrics and Riemannian immersions
(Petersen §1.1, pullback metric / Riemannian immersion) -/

section Pullback

/-- **Math.** `F : M → M'` is a **smooth immersion** if it is smooth and its
differential is injective at every point. -/
def IsSmoothImmersion (F : M → M') : Prop :=
  ContMDiff I I' ∞ F ∧ ∀ p : M, Function.Injective (mfderiv I I' F p)

/-- **Math.** Petersen §1.1: the **pullback form**
`(F^*g_N)(u, v) = g_N(DF(u), DF(v))` on `T_pM`, obtained by transporting the
target metric `gN` through the differential `DF_p`. -/
def pullbackForm (gN : RiemannianMetric I' M') (F : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I I' F p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := gN.inner (F p)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] in
@[simp]
theorem pullbackForm_apply (gN : RiemannianMetric I' M') (F : M → M') (p : M)
    (u v : TangentSpace I p) :
    pullbackForm gN F p u v =
      gN.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v) :=
  rfl

omit [IsManifold I ∞ M] in
/-- **Math.** The pullback form is symmetric, inherited from the symmetry of `gN`. -/
theorem pullbackForm_symm (gN : RiemannianMetric I' M') (F : M → M') (p : M)
    (u v : TangentSpace I p) :
    pullbackForm gN F p u v = pullbackForm gN F p v u := by
  simp only [pullbackForm_apply]
  exact gN.metricInner_comm _ _ _

omit [IsManifold I ∞ M] in
/-- **Math.** Petersen §1.1: the pullback form is an inner product exactly
because `DF(v) = 0` only for `v = 0` (the immersion condition): for `u ≠ 0`,
`DF(u) ≠ 0`, so `g_N(DF(u), DF(u)) > 0`. -/
theorem pullbackForm_pos (gN : RiemannianMetric I' M') (F : M → M') (p : M)
    (hinj : Function.Injective (mfderiv I I' F p)) (u : TangentSpace I p)
    (hu : u ≠ 0) :
    0 < pullbackForm gN F p u u := by
  rw [pullbackForm_apply]
  refine gN.metricInner_self_pos (F p) _ ?_
  intro h
  exact hu (hinj (by rw [h, map_zero]))

/-- **Math.** On a finite-dimensional inner-product space, a positive-definite
quadratic form `q` is coercive, so the sublevel set `{v | q v v < 1}` is von
Neumann bounded. This supplies the `isVonNBounded` field of a Riemannian
metric from pointwise positivity. -/
theorem isVonNBounded_of_posDef {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : E →L[ℝ] E →L[ℝ] ℝ) (hpos : ∀ v : E, v ≠ 0 → 0 < q v v) :
    Bornology.IsVonNBounded ℝ {v : E | q v v < 1} := by
  rcases subsingleton_or_nontrivial E with hs | hn
  · exact Set.Finite.isVonNBounded (𝕜 := ℝ) (Set.toFinite _)
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : Continuous fun v : E => q v v := q.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  set c := q v₀ v₀ with hc_def
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hv₀mem; norm_num at hv₀mem
  have hc : 0 < c := hpos v₀ hv₀ne
  have hcoer : ∀ v : E, c * ‖v‖ ^ 2 ≤ q v v := by
    intro v; rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      set u := ‖v‖⁻¹ • v with hu
      have hmem : u ∈ Metric.sphere (0 : E) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
      have hqu : c ≤ q u u := hv₀min hmem
      have hexp : q v v = ‖v‖ ^ 2 * q u u := by
        rw [hu]; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; field_simp
      rw [hexp]; nlinarith [hqu, sq_nonneg ‖v‖]
  apply Bornology.IsVonNBounded.subset _ (NormedSpace.isVonNBounded_ball ℝ E (Real.sqrt (1 / c) + 1))
  intro v hv; simp only [Set.mem_setOf_eq] at hv; rw [Metric.mem_ball, dist_zero_right]
  have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hcoer v) hv
  have h2 : ‖v‖ ^ 2 < 1 / c := by rw [lt_div_iff₀ hc]; linarith [mul_comm c (‖v‖^2)]
  have h3 : ‖v‖ < Real.sqrt (1 / c) := by
    rw [show ‖v‖ = Real.sqrt (‖v‖^2) by rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h2
  linarith [Real.sqrt_nonneg (1/c)]

/-- **Math.** The pullback-form section of a smooth map varies smoothly. In
tangent coordinates around `x₀` the section `x ↦ g_N(DF_x ·, DF_x ·)` equals
`ξ ↦ G(F x)(D x ·)(D x ·)`, where `D x` is the differential read in tangent
coordinates (smooth by `ContMDiffAt.mfderiv_const`) and `G` is the target
metric `gN` read in coordinates (smooth by `gN.contMDiff`). This is a
composition of smooth model-space-valued maps, so the coordinate
representation — hence the bundle section — is smooth. -/
theorem pullbackForm_contMDiffAt (gN : RiemannianMetric I' M') {F : M → M'} {x₀ : M}
    (hF : ContMDiffAt I I' ∞ F x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackForm gN F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (F x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : F x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') (F x₀)
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id F (fun x => mfderiv I I' F x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    hF.mfderiv_const (by simp)
  set G : M' → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace I') (E' →L[ℝ] ℝ)
      (fun y => TangentSpace I' y →L[ℝ] ℝ) (F x₀) y (F x₀) y (gN.inner y) with hG
  have hGsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G (F x₀) :=
    ((contMDiffAt_hom_bundle _).mp gN.contMDiff.contMDiffAt).2
  have hΨ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((G (F x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (G (F x)).comp (D x)) x₀ :=
      (hGsmooth.comp x₀ hF).clm_comp hDsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | F x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hF.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp ((G (F x)).comp (D x))) a) b
      = G (F x) (D x a) (D x b) := rfl
  have hkey : ∀ u : E, tT.symm (F x) (D x u) = mfderiv I I' F x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (F x) hfx
        (mfderiv I I' F x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
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
  have htrivM' : trivializationAt ℝ (Bundle.Trivial M' ℝ) (F x₀) = Bundle.Trivial.trivialization M' ℝ :=
    Bundle.Trivial.eq_trivialization M' ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hfx hfx (by simp)]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    pullbackForm_apply, RiemannianMetric.metricInner_apply, ← htT, ← hsT, hkey]

/-- **Math.** The pullback form of a smooth map is a smooth section of the
bundle of bilinear forms (global version; smoothness is a local property, so
this is the pointwise `pullbackForm_contMDiffAt` at every point). -/
theorem pullbackForm_contMDiff (gN : RiemannianMetric I' M') {F : M → M'}
    (hF : ContMDiff I I' ∞ F) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, pullbackForm gN F x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) :=
  fun x₀ => pullbackForm_contMDiffAt gN hF.contMDiffAt

variable [FiniteDimensional ℝ E]

/-- **Math.** Petersen §1.1: **the pullback metric** `g_M = F^*g_N` of an
immersion. If `F : M → M'` is a smooth immersion and `g_N` a Riemannian metric
on `M'`, then `(F^*g_N)(u, v) = g_N(DF(u), DF(v))` defines a Riemannian metric
on `M`: symmetric because `g_N` is, and an inner product because `DF(v) = 0`
only for `v = 0`. Specializing to an embedding (e.g. `Sⁿ(R) ↪ ℝⁿ⁺¹`) gives the
canonical metric of a submanifold. -/
def pullbackMetric (gN : RiemannianMetric I' M') (F : M → M')
    (hF : IsSmoothImmersion (I := I) (I' := I') F) :
    RiemannianMetric I M where
  inner p := pullbackForm gN F p
  symm p u v := pullbackForm_symm gN F p u v
  pos p u hu := pullbackForm_pos gN F p (hF.2 p) u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E) (pullbackForm gN F p) (fun u hu => ?_)
    exact pullbackForm_pos gN F p (hF.2 p) u hu
  contMDiff := pullbackForm_contMDiff gN hF.1

@[simp]
theorem pullbackMetric_apply (gN : RiemannianMetric I' M') (F : M → M')
    (hF : IsSmoothImmersion (I := I) (I' := I') F) (p : M) (u v : TangentSpace I p) :
    (pullbackMetric gN F hF).metricInner p u v =
      gN.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v) :=
  rfl

/-- **Math.** Petersen §1.1: a **Riemannian immersion** (isometric immersion)
is an immersion `F : (M, g_M) → (N, g_N)` with `g_M = F^*g_N`. -/
def IsRiemannianImmersion (gM : RiemannianMetric I M)
    (gN : RiemannianMetric I' M') (F : M → M') : Prop :=
  IsSmoothImmersion (I := I) (I' := I') F ∧ PreservesMetric gM gN F

/-- **Math.** The pullback metric makes an immersion a Riemannian immersion:
`F : (M, F^*g_N) → (N, g_N)` preserves the metric by construction. -/
theorem pullbackMetric_isRiemannianImmersion (gN : RiemannianMetric I' M')
    (F : M → M') (hF : IsSmoothImmersion (I := I) (I' := I') F) :
    IsRiemannianImmersion (pullbackMetric gN F hF) gN F :=
  ⟨hF, fun _ _ _ => rfl⟩

end Pullback

/-! ## Riemannian submersions (Petersen §1.1, Example 1.1.4) -/

section Submersion

/-- **Math.** Petersen §1.1: a **Riemannian submersion**
`F : (M, g_M) → (N, g_N)` is a (smooth) submersion such that at each `p ∈ M`
the differential `DF` restricted to `ker(DF)^⊥` is a linear isometry onto
`T_{F(p)}N`: whenever `u, v ∈ T_pM` are `g_M`-perpendicular to
`ker(DF : T_pM → T_{F(p)}N)`, then `g_M(u, v) = g_N(DF(u), DF(v))`. -/
def IsRiemannianSubmersion (gM : RiemannianMetric I M)
    (gN : RiemannianMetric I' M') (F : M → M') : Prop :=
  ContMDiff I I' ∞ F ∧
  (∀ p : M, Function.Surjective (mfderiv I I' F p)) ∧
  ∀ (p : M) (u v : TangentSpace I p),
    (∀ w : TangentSpace I p, mfderiv I I' F p w = 0 → gM.metricInner p u w = 0) →
    (∀ w : TangentSpace I p, mfderiv I I' F p w = 0 → gM.metricInner p v w = 0) →
    gM.metricInner p u v =
      gN.metricInner (F p) (mfderiv I I' F p u) (mfderiv I I' F p v)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- **Math.** Petersen Example 1.1.4: **orthogonal projections**
`(ℝⁿ, g_{ℝⁿ}) → (ℝᵏ, g_{ℝᵏ})` are Riemannian submersions. Formulated
invariantly: the orthogonal projection of a finite-dimensional inner product
space onto a subspace `K` is a Riemannian submersion for the inner-product
metrics. The kernel of the projection is `K^⊥`, so vectors perpendicular to
the kernel lie in `K = (K^⊥)^⊥` and the projection restricts to the identity
on them. -/
theorem orthogonalProjectionSubmersion (K : Submodule ℝ F) :
    IsRiemannianSubmersion (innerProductSpaceMetric F) (innerProductSpaceMetric K)
      (fun x => (K.orthogonalProjection x : K)) := by
  have hclm : ∀ p : F, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K)
      (fun x => (K.orthogonalProjection x : K)) p = (K.orthogonalProjection : F →L[ℝ] K) := by
    intro p
    rw [mfderiv_eq_fderiv]
    exact (K.orthogonalProjection : F →L[ℝ] K).fderiv
  refine ⟨(K.orthogonalProjection : F →L[ℝ] K).contMDiff, fun p => ?_, fun p u v hu hv => ?_⟩
  · rw [hclm p]
    intro y
    exact ⟨((show K from y) : F),
      Submodule.orthogonalProjection_mem_subspace_eq_self (show K from y)⟩
  · -- vectors g-perpendicular to ker(projection) = K^⊥ lie in K
    have hker : ∀ w : F, (K.orthogonalProjection w : K) = 0 ↔ w ∈ Kᗮ := by
      intro w
      rw [Submodule.orthogonalProjection_eq_zero_iff]
    have hmemK : ∀ w : F,
        (∀ z : F, mfderiv 𝓘(ℝ, F) 𝓘(ℝ, K)
          (fun x => (K.orthogonalProjection x : K)) p z = 0 →
          (innerProductSpaceMetric F).metricInner p w z = 0) → w ∈ K := by
      intro w hw
      rw [← Submodule.orthogonal_orthogonal K]
      intro z hz
      have h0 : (K.orthogonalProjection z : K) = 0 := (hker z).mpr hz
      have := hw z (by rw [hclm p]; exact_mod_cast h0)
      simpa [innerProductSpaceMetric_apply, real_inner_comm] using this
    have huK : u ∈ K := hmemK u hu
    have hvK : v ∈ K := hmemK v hv
    rw [hclm p]
    simp only [innerProductSpaceMetric_apply]
    have hprojU : (K.orthogonalProjection u : K) = ⟨u, huK⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨u, huK⟩ : K)
    have hprojV : (K.orthogonalProjection v : K) = ⟨v, hvK⟩ :=
      Submodule.orthogonalProjection_mem_subspace_eq_self (⟨v, hvK⟩ : K)
    show (inner ℝ u v : ℝ) = inner ℝ (K.orthogonalProjection u : K) (K.orthogonalProjection v : K)
    rw [hprojU, hprojV]
    rfl

end Submersion

/-! ## Pseudo-Riemannian metrics (Petersen §1.1, Example 1.1.6) -/

section PseudoRiemannian

variable (I M) in
/-- **Math.** Petersen §1.1: a **pseudo-Riemannian (semi-Riemannian) metric**
on `M` is a smoothly varying symmetric bilinear form `g` on each tangent
space, assumed **nondegenerate**: for every nonzero `v ∈ T_pM` there is
`w ∈ T_pM` with `g(v, w) ≠ 0`. This generalizes a Riemannian metric, whose
nondegeneracy follows from `g(v, v) > 0` for `v ≠ 0`. -/
structure PseudoRiemannianMetric where
  /-- The bilinear form on each tangent space. -/
  inner : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ
  /-- Symmetry of the form. -/
  symm : ∀ (x : M) (u v : TangentSpace I x), inner x u v = inner x v u
  /-- Nondegeneracy: nonzero vectors pair nontrivially with some vector. -/
  nondegenerate : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → ∃ w, inner x v w ≠ 0
  /-- Smoothness of the section `x ↦ g_x` of the bundle of bilinear forms. -/
  contMDiff : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun x ↦ (⟨x, inner x⟩ :
      Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))

/-- **Math.** A Riemannian metric is in particular pseudo-Riemannian:
positive-definiteness gives nondegeneracy (`w := v` pairs nontrivially). -/
def RiemannianMetric.toPseudoRiemannianMetric (g : RiemannianMetric I M) :
    PseudoRiemannianMetric I M where
  inner x := g.inner x
  symm x u v := g.symm x u v
  nondegenerate x v hv := ⟨v, ne_of_gt (g.pos x v hv)⟩
  contMDiff := g.contMDiff

/-- **Math.** A subspace on which a pseudo-Riemannian metric is negative
definite. -/
def IsNegDefOn (g : PseudoRiemannianMetric I M) (x : M)
    (W : Submodule ℝ (TangentSpace I x)) : Prop :=
  ∀ v ∈ W, v ≠ 0 → g.inner x v v < 0

/-- **Math.** Petersen §1.1: the **index** of a pseudo-Riemannian metric at
`p`, the dimension of a maximal subspace `N ⊂ T_pM` on which `g` is negative
definite. Each tangent space splits `T_pM = P ⊕ N` with `g` positive definite
on `P` and negative definite on `N`; the subspaces are not unique but their
dimensions are well defined, and on a connected manifold the index is
independent of the point. -/
def pseudoRiemannianIndex [FiniteDimensional ℝ E]
    (g : PseudoRiemannianMetric I M) (x : M) : ℕ :=
  sSup {n : ℕ | ∃ W : Submodule ℝ (TangentSpace I x),
    Module.finrank ℝ W = n ∧ IsNegDefOn g x W}

end PseudoRiemannian

end PetersenLib

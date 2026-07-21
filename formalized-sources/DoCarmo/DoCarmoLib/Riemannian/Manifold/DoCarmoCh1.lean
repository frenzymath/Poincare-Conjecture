import DoCarmoLib.Riemannian.Manifold.DoCarmoCh0
import DoCarmoLib.Riemannian.Metric.RiemannianMetric
import DoCarmoLib.Riemannian.TangentBundle.TangentSmooth
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# do Carmo Chapter 1 interface

Thin, checked names for the Riemannian-metric primitives of Chapter 1 that go
beyond the metric algebra already carried by `Riemannian.RiemannianMetric`:
isometries and local isometries (metric-preserving maps), parametrized curves,
their velocity fields, vector fields along a curve, and arc length. Each wraps
the Mathlib manifold API (`mfderiv`, `ContMDiffOn`, `intervalIntegral`) rather
than introducing a parallel formalization.

Reference: do Carmo, *Riemannian Geometry*, §1.2.
-/

open scoped ContDiff Manifold Topology

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Isometries (do Carmo Def. 1.2.2, 1.2.3) -/

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** do Carmo Ch.1 Def. 2.2: a map `f : M → M'` **preserves the metric** if its
differential carries the inner product of `gM` to that of `gN` at every point:
`⟨u, v⟩_p = ⟨df_p u, df_p v⟩_{f p}`. An *isometry* is a diffeomorphism with this
property; the metric-preservation clause is captured here. -/
def DCPreservesMetric (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M')
    (f : M → M') : Prop :=
  ∀ (p : M) (u v : TangentSpace I p),
    gM.metricInner p u v =
      gN.metricInner (f p) (mfderiv I I' f p u) (mfderiv I I' f p v)

/-- **Math.** do Carmo Ch.1 Def. 2.3: `f` is a **local isometry at `p`** if it preserves
the metric on some neighbourhood `U` of `p` on which it restricts to a
diffeomorphism onto its image. The metric-preservation on `U` is captured here. -/
def DCIsLocalIsometryAt (gM : RiemannianMetric I M) (gN : RiemannianMetric I' M')
    (f : M → M') (p : M) : Prop :=
  ∃ U ∈ nhds p, ∀ q ∈ U, ∀ u v : TangentSpace I q,
    gM.metricInner q u v =
      gN.metricInner (f q) (mfderiv I I' f q u) (mfderiv I I' f q v)

/-! ## Parametrized curves (do Carmo Def. 1.2.8, 1.2.9) -/

/-- **Math.** do Carmo Ch.1 Def. 2.8: a **parametrized curve** into `M` is a differentiable
map from an open interval, modelled here as `ContMDiffOn` on the parameter set. -/
def DCIsCurve (c : ℝ → M) (s : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c s

/-- **Math.** do Carmo Ch.1 Def. 2.9: the **velocity field** `dc/dt` of a curve, the image
of the unit tangent `1 ∈ ℝ = T_tℝ` under `dc_t`. -/
def DCVelocity (c : ℝ → M) (t : ℝ) : TangentSpace I (c t) :=
  mfderiv 𝓘(ℝ, ℝ) I c t (1 : ℝ)

/-- **Math.** do Carmo Ch.1 Def. 2.9: a **vector field along a curve** `c` is a
differentiable assignment `V t ∈ T_{c t}M`, expressed as smoothness of the
tangent-bundle section `t ↦ (c t, V t)`. -/
def DCIsVectorFieldAlong (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (s : Set ℝ) :
    Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
    (fun t => (⟨c t, V t⟩ : TangentBundle I M)) s

/-- **Math.** do Carmo Ch.1 Def. 2.9: the **arc length** of the segment `c|[a,b]` for a
metric `g`, `ℓ_a^b(c) = ∫_a^b ⟨dc/dt, dc/dt⟩^{1/2} dt`. -/
def DCArcLength (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (g.metricInner (c t) (DCVelocity c t) (DCVelocity c t))

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- **Math.** The velocity of a composite curve `f ∘ c` is the differential of `f`
applied to the velocity of `c`: `d(f∘c)/dt = df_{c t}(dc/dt)`. This is the chain rule
for the velocity field of do Carmo Def. 2.9. -/
theorem DCVelocity_comp {c : ℝ → M} {f : M → M'} (t : ℝ)
    (hf : MDifferentiableAt I I' f (c t)) (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    DCVelocity (f ∘ c) t = mfderiv I I' f (c t) (DCVelocity c t) :=
  mfderiv_comp_apply t hf hc (1 : ℝ)

/-- **Math.** An isometry (metric-preserving map, do Carmo Def. 2.2) preserves the arc
length of every curve: `ℓ_a^b(f ∘ c) = ℓ_a^b(c)`. This is the raison d'être of Def. 2.2 —
it makes the length functional of Def. 2.9 an invariant of the Riemannian structure. -/
theorem DCPreservesMetric.dcArcLength {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} (hiso : DCPreservesMetric gM gN f)
    {c : ℝ → M} (hf : MDifferentiable I I' f) (hc : MDifferentiable 𝓘(ℝ, ℝ) I c) (a b : ℝ) :
    DCArcLength gN (f ∘ c) a b = DCArcLength gM c a b := by
  simp only [DCArcLength]
  congr 1
  funext t
  rw [DCVelocity_comp t (hf.mdifferentiableAt) (hc.mdifferentiableAt),
    Function.comp_apply, ← hiso (c t) (DCVelocity c t) (DCVelocity c t)]

/-! ## Euclidean space (do Carmo Ex. 1.2.4) -/

section EuclideanMetric

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Math.** do Carmo Ch.1 Ex. 2.4: **Euclidean space**. The vector space `F` with its
ambient inner product `⟨u, v⟩`, viewed as a manifold modelled on itself, is a Riemannian
manifold: each tangent space `T_xF = F` carries that same inner product, and it varies
(analytically, hence) smoothly with `x`. This wraps Mathlib's
`riemannianMetricVectorSpace`, weakening its analytic smoothness to `C^∞`. Taking `F = ℝ^n`
with the standard basis recovers `⟨eᵢ, eⱼ⟩ = δᵢⱼ`. -/
noncomputable def DCEuclideanMetric : RiemannianMetric 𝓘(ℝ, F) F :=
  { riemannianMetricVectorSpace F with
    contMDiff := (riemannianMetricVectorSpace F).contMDiff.of_le le_top }

/-- **Math.** The Euclidean metric of Ex. 2.4 is exactly the ambient inner product of `F`:
`⟨u, v⟩_x = ⟨u, v⟩` on every tangent space `T_xF = F`. -/
theorem DCEuclideanMetric_apply (x : F) (v w : TangentSpace 𝓘(ℝ, F) x) :
    (DCEuclideanMetric (F := F)).metricInner x v w = @inner ℝ F _ v w :=
  rfl

end EuclideanMetric

/-! ## Existence of a Riemannian metric (do Carmo Prop. 1.2.10) -/

section Existence

open Bornology Bundle

/-- **Math.** On a finite-dimensional inner-product space, a positive-definite quadratic form
`q` is coercive, so the sublevel set `{v | q v v < 1}` is von Neumann bounded. This supplies the
`isVonNBounded` field of a Riemannian metric from pointwise positivity. -/
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

omit [IsManifold I ∞ M] in
/-- **Math.** The set of symmetric positive-definite bilinear forms on a tangent space is convex:
a convex combination `a q₁ + b q₂` (with `a, b ≥ 0`, `a + b = 1`) is again symmetric, and
positive-definite as long as at least one weight is strictly positive. This is what lets the
partition-of-unity patching keep the glued form positive-definite. -/
theorem convex_symm_posDef (x : M) :
    Convex ℝ {q : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ |
      (∀ u v, q u v = q v u) ∧ (∀ v, v ≠ 0 → 0 < q v v)} := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro u v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hq₁.1 u v, hq₂.1 u v]
  · intro v hv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have p1 := hq₁.2 v hv; have p2 := hq₂.2 v hv
    have hab' : 0 < a ∨ 0 < b := by
      by_contra h; rw [not_or, not_lt, not_lt] at h
      have : a = 0 ∧ b = 0 := ⟨le_antisymm h.1 ha, le_antisymm h.2 hb⟩
      rw [this.1, this.2] at hab; norm_num at hab
    rcases hab' with ha' | hb'
    · nlinarith [mul_pos ha' p1, mul_nonneg hb p2.le]
    · nlinarith [mul_nonneg ha p1.le, mul_pos hb' p2]

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 1000000 in
/-- **Math.** do Carmo Ch.1 Prop. 2.10: **every (finite-dimensional, second-countable Hausdorff)
differentiable manifold carries a Riemannian metric.** Construction: pull the Euclidean inner
product of the model space `E` back through the tangent-bundle trivialization on each chart to get
a local symmetric positive-definite section, then glue with a smooth partition of unity; convexity
of the symmetric positive-definite cone keeps the glued form a metric. -/
theorem exists_riemannianMetric : Nonempty (Riemannian.RiemannianMetric I M) := by
  set V : M → Type _ := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ with hV
  set t : ∀ x, Set (V x) := fun x =>
    {q | (∀ u v, q u v = q v u) ∧ (∀ v, v ≠ 0 → 0 < q v v)} with ht
  have htconv : ∀ x, Convex ℝ (t x) := fun x => convex_symm_posDef x
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ s_loc : (x : M) → V x,
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (s_loc x)) U ∧
      ∀ y ∈ U, s_loc y ∈ t y := by
    intro x₀
    classical
    -- A fixed symmetric positive-definite form on the model space `E`, obtained by transporting
    -- the Euclidean inner product back through the linear equiv `toEuclidean`.
    set φ : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean : E ≃L[ℝ] _).toContinuousLinearMap with hφ
    set B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).bilinearComp φ φ with hB
    have hB_apply : ∀ u v : E, B u v = @inner ℝ _ _ (φ u) (φ v) := fun u v => rfl
    have hφinj : Function.Injective φ := by
      simpa [hφ] using (toEuclidean : E ≃L[ℝ] _).injective
    have hBsymm : ∀ u v : E, B u v = B v u := fun u v => by
      rw [hB_apply, hB_apply]; exact real_inner_comm _ _
    have hBpos : ∀ w : E, w ≠ 0 → 0 < B w w := fun w hw => by
      rw [hB_apply]; exact real_inner_self_pos.2 (fun h => hw (hφinj (by rw [h, map_zero])))
    set eT := trivializationAt E (TangentSpace I) x₀ with heT
    have hx₀ : x₀ ∈ eT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    -- `s_loc y` transports `B` back through the tangent trivialization's fibre equiv `τ_y`.
    set s_loc : (y : M) → V y := fun y =>
      if hy : y ∈ eT.baseSet then
        ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
          ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
            (ContinuousLinearEquiv.refl ℝ ℝ))) B
      else 0 with hsl
    have hsl_apply : ∀ (y : M) (hy : y ∈ eT.baseSet) (u v : TangentSpace I y),
        s_loc y u v = B (eT.continuousLinearEquivAt ℝ y hy u) (eT.continuousLinearEquivAt ℝ y hy v) := by
      intro y hy u v
      simp only [hsl, dif_pos hy]
      rfl
    refine ⟨eT.baseSet, eT.open_baseSet.mem_nhds hx₀, s_loc, ?_, ?_⟩
    · -- smoothness: reduce to the coordinate representation, which is the constant `B`
      have hbase : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) V x₀).baseSet = eT.baseSet := by
        have htriv0 : (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀) = Bundle.Trivial.trivialization M ℝ :=
          Bundle.Trivial.eq_trivialization M ℝ _
        simp only [hom_trivializationAt_baseSet, ← heT, htriv0, Bundle.Trivial.trivialization,
          Set.inter_univ, Set.inter_self]
      rw [← hbase, Bundle.Trivialization.contMDiffOn_section_baseSet_iff]
      refine (contMDiffOn_const (c := B)).congr ?_
      intro y hy
      rw [hbase] at hy
      -- `(eH ⟨y, s_loc y⟩).2 = B` for `y ∈ eT.baseSet`
      refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      have hy₂ : y ∈ (trivializationAt (E →L[ℝ] ℝ) (fun x => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet := by
        rw [hom_trivializationAt_baseSet]; exact ⟨hy, Set.mem_univ y⟩
      rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt (E →L[ℝ] ℝ) (fun x => TangentSpace I x →L[ℝ] ℝ) x₀) hy₂]
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply, ← heT]
      have htriv : (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀) = Bundle.Trivial.trivialization M ℝ :=
        Bundle.Trivial.eq_trivialization M ℝ _
      simp only [htriv, Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_apply, hsl_apply y hy,
        ← Trivialization.symm_continuousLinearEquivAt_eq' eT hy,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    · -- symmetric positive-definite on baseSet
      intro y hy
      refine ⟨fun u v => ?_, fun v hv => ?_⟩
      · rw [hsl_apply y hy, hsl_apply y hy]; exact hBsymm _ _
      · rw [hsl_apply y hy]
        exact hBpos _ (fun h => hv ((eT.continuousLinearEquivAt ℝ y hy).injective (by rw [h, map_zero])))
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
      (I := I) (n := (⊤ : ℕ∞)) V t htconv hloc
  refine ⟨⟨fun b => s b, fun b v w => (hs b).1 v w, fun b v hv => (hs b).2 v hv, ?_,
    s.contMDiff⟩⟩
  intro b
  exact isVonNBounded_of_posDef (E := E) (s b) (fun v hv => (hs b).2 v hv)

end Existence

/-! ## Induced (pullback) metric of an immersion (do Carmo Ex. 1.2.5) -/

section InducedMetric

open Bornology Bundle

/-- **Math.** do Carmo Ch.1 Ex. 2.5: `f : M → M'` is a **smooth immersion** if it is smooth and
an immersion (differential injective everywhere). We bundle smoothness here since Ch.1 exercises
assume it; Ch.0's `DCIsImmersion` is the bare differential condition. -/
abbrev DCSmoothImmersion (f : M → M') : Prop :=
  ContMDiff I I' ∞ f ∧ DCIsImmersion (I := I) (I' := I') f

/-- **Math.** do Carmo Ch.1 Ex. 2.5: the **pullback form** `⟨u, v⟩_p = ⟨df_p u, df_p v⟩_{f p}`,
the bilinear form on `T_pM` obtained by transporting the target metric `gN` through the
differential `df_p`. -/
noncomputable def DCInducedForm (gN : RiemannianMetric I' M') (f : M → M') (p : M) :
    TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ :=
  let A : E →L[ℝ] E' := mfderiv I I' f p
  let B : E' →L[ℝ] E' →L[ℝ] ℝ := gN.inner (f p)
  (B.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ M] in
@[simp]
theorem DCInducedForm_apply (gN : RiemannianMetric I' M') (f : M → M') (p : M)
    (u v : TangentSpace I p) :
    DCInducedForm gN f p u v =
      gN.metricInner (f p) (mfderiv I I' f p u) (mfderiv I I' f p v) :=
  rfl

omit [IsManifold I ∞ M] in
/-- **Math.** The pullback form is symmetric, inherited from the symmetry of `gN`. -/
theorem DCInducedForm_symm (gN : RiemannianMetric I' M') (f : M → M') (p : M)
    (u v : TangentSpace I p) :
    DCInducedForm gN f p u v = DCInducedForm gN f p v u := by
  simp only [DCInducedForm_apply]
  exact gN.metricInner_comm _ _ _

omit [IsManifold I ∞ M] in
/-- **Math.** The pullback form is positive definite exactly because `df_p` is injective
(the immersion condition): for `u ≠ 0`, `df_p u ≠ 0`, so `⟨df_p u, df_p u⟩_{f p} > 0`. -/
theorem DCInducedForm_pos (gN : RiemannianMetric I' M') (f : M → M') (p : M)
    (hinj : Function.Injective (mfderiv I I' f p)) (u : TangentSpace I p) (hu : u ≠ 0) :
    0 < DCInducedForm gN f p u u := by
  rw [DCInducedForm_apply]
  refine gN.metricInner_self_pos (f p) _ ?_
  intro h
  exact hu (hinj (by rw [h, map_zero]))

/-- **Math.** The pullback-form section of a smooth map varies smoothly. In tangent coordinates
around `x₀` the section `x ↦ ⟨df_x·, df_x·⟩_{f x}` equals
`ξ ↦ G(f x)(D x ·)(D x ·)`, where `D x = inTangentCoordinates I I' id f (df) x₀ x` is the
differential read in tangent coordinates (smooth by `ContMDiffAt.mfderiv_const`) and `G` is the
target metric `gN` read in coordinates (smooth by `gN.contMDiff`). This is a composition of smooth
model-space-valued maps (`clm_comp`/`clm_precomp`), so the coordinate representation — hence the
bundle section — is smooth. This discharges the analytic input of `DCInducedMetric`. -/
theorem DCInducedForm_contMDiff (gN : RiemannianMetric I' M') {f : M → M'}
    (hf : ContMDiff I I' ∞ f) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ (⟨x, DCInducedForm gN f x⟩ :
        Bundle.TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ))) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (f x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') (f x₀)
  -- `D`: the differential read in tangent coordinates, smooth by `mfderiv_const`.
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id f (fun x => mfderiv I I' f x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    hf.contMDiffAt.mfderiv_const (by simp)
  -- `G`: the target metric read in coordinates, smooth from `gN`'s section smoothness.
  set G : M' → (E' →L[ℝ] E' →L[ℝ] ℝ) := fun y =>
    ContinuousLinearMap.inCoordinates E' (TangentSpace I') (E' →L[ℝ] ℝ)
      (fun y => TangentSpace I' y →L[ℝ] ℝ) (f x₀) y (f x₀) y (gN.inner y) with hG
  have hGsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞ G (f x₀) :=
    ((contMDiffAt_hom_bundle _).mp gN.contMDiff.contMDiffAt).2
  -- The smooth model-space map: `Ψ x = ((D x).precomp ℝ) ∘L ((G (f x)) ∘L (D x))`.
  have hΨ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun x => ((D x).precomp ℝ).comp ((G (f x)).comp (D x))) x₀ := by
    have h1 : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E' →L[ℝ] ℝ) ∞
        (fun x => (G (f x)).comp (D x)) x₀ :=
      (hGsmooth.comp x₀ hf.contMDiffAt).clm_comp hDsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hDsmooth).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {x | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x | f x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    hf.continuous.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  -- The right-hand model-space map is definitionally `G (f x) (D x a) (D x b)`.
  have hRHS : (((ContinuousLinearMap.precomp ℝ (D x)).comp ((G (f x)).comp (D x))) a) b
      = G (f x) (D x a) (D x b) := rfl
  -- Key cancellation: the target coordinate change undoes itself through the differential.
  have hkey : ∀ u : E, tT.symm (f x) (D x u) = mfderiv I I' f x (sT.symm x u) := by
    intro u
    have hDu : D x u = tT.continuousLinearEquivAt ℝ (f x) hfx
        (mfderiv I I' f x ((sT.continuousLinearEquivAt ℝ x hx).symm u)) := by
      rw [hD]
      simp only [inTangentCoordinates, id_eq]
      rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
      rfl
    have hcoeT : (tT.symm (f x) : E' → TangentSpace I' (f x))
        = ⇑(tT.continuousLinearEquivAt ℝ (f x) hfx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq tT hfx]; rfl
    have hcoeS : (sT.symm x : E → TangentSpace I x)
        = ⇑(sT.continuousLinearEquivAt ℝ x hx).symm := by
      rw [Trivialization.symm_continuousLinearEquivAt_eq sT hx]; rfl
    rw [hDu, hcoeT, ContinuousLinearEquiv.symm_apply_apply, hcoeS]
  rw [hRHS, hG]
  have htrivM' : trivializationAt ℝ (Bundle.Trivial M' ℝ) (f x₀) = Bundle.Trivial.trivialization M' ℝ :=
    Bundle.Trivial.eq_trivialization M' ℝ _
  have htrivM : trivializationAt ℝ (Bundle.Trivial M ℝ) x₀ = Bundle.Trivial.trivialization M ℝ :=
    Bundle.Trivial.eq_trivialization M ℝ _
  -- collapse the target metric read in coordinates (trivial `ℝ`-bundle acts as identity)
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hfx hfx (by simp)]
  -- collapse the pullback form read in coordinates
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hx hx (by simp)]
  simp only [htrivM', htrivM, Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq,
    DCInducedForm_apply, RiemannianMetric.metricInner_apply, ← htT, ← hsT, hkey]

variable [FiniteDimensional ℝ E]

/-- **Math.** do Carmo Ch.1 Ex. 2.5: **the metric induced by an immersion.** If `f : M → M'` is a
smooth immersion and `gN` is a Riemannian metric on `M'`, then `⟨u, v⟩_p = ⟨df_p u, df_p v⟩_{f p}`
defines a Riemannian metric on `M` — symmetric because `gN` is, positive definite because `df_p` is
injective. Specializing to an inclusion `h^{-1}(q) ↪ M'` gives the canonical metric of a regular
level set (e.g. the round metric on `S^{n-1}`).

Every clause is discharged unconditionally: symmetry `DCInducedForm_symm`, positive-definiteness
`DCInducedForm_pos` (from injectivity of `df_p`), von Neumann boundedness `isVonNBounded_of_posDef`,
and — via `DCInducedForm_contMDiff` — the analytic smoothness of the pullback-form bundle section. -/
noncomputable def DCInducedMetric (gN : RiemannianMetric I' M') (f : M → M')
    (himm : DCSmoothImmersion (I := I) (I' := I') f) :
    RiemannianMetric I M where
  inner p := DCInducedForm gN f p
  symm p u v := DCInducedForm_symm gN f p u v
  pos p u hu := DCInducedForm_pos gN f p (himm.2 p) u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E) (DCInducedForm gN f p) (fun u hu => ?_)
    exact DCInducedForm_pos gN f p (himm.2 p) u hu
  contMDiff := DCInducedForm_contMDiff gN himm.1

end InducedMetric

/-! ## Product metric (do Carmo Ex. 1.2.7) -/

section ProductMetric

open Bornology Bundle

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [IsManifold I₁ ∞ M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [IsManifold I₂ ∞ M₂]

/-- **Math.** do Carmo Ch.1 Ex. 2.7: the **product form** on `M₁ × M₂`,
`⟨u, v⟩_{(p,q)} = ⟨dπ₁ u, dπ₁ v⟩_p + ⟨dπ₂ u, dπ₂ v⟩_q`, the sum of the two factor metrics pulled
back along the projections `π₁, π₂`. It is the sum `DCInducedForm g₁ π₁ + DCInducedForm g₂ π₂` of two
pullback forms in the same bundle over `M₁ × M₂`. -/
noncomputable def DCProductForm (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) :
    TangentSpace (I₁.prod I₂) p →L[ℝ] TangentSpace (I₁.prod I₂) p →L[ℝ] ℝ :=
  DCInducedForm (I := I₁.prod I₂) g₁ Prod.fst p +
    DCInducedForm (I := I₁.prod I₂) g₂ Prod.snd p

/-- **Math.** The product form is symmetric, inherited termwise from `g₁` and `g₂`. -/
theorem DCProductForm_symm (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) (u v : TangentSpace (I₁.prod I₂) p) :
    DCProductForm g₁ g₂ p u v = DCProductForm g₁ g₂ p v u := by
  simp only [DCProductForm, ContinuousLinearMap.add_apply]
  rw [DCInducedForm_symm, DCInducedForm_symm (f := Prod.snd)]

/-- **Math.** The product form is positive definite: for `u ≠ 0` either `dπ₁ u = u.1 ≠ 0` or
`dπ₂ u = u.2 ≠ 0`, so the corresponding summand is strictly positive while the other is `≥ 0`. -/
theorem DCProductForm_self_pos (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    (p : M₁ × M₂) (u : TangentSpace (I₁.prod I₂) p) (hu : u ≠ 0) :
    0 < DCProductForm g₁ g₂ p u u := by
  have hfst : mfderiv (I₁.prod I₂) I₁ Prod.fst p u = u.1 := by rw [mfderiv_fst]; rfl
  have hsnd : mfderiv (I₁.prod I₂) I₂ Prod.snd p u = u.2 := by rw [mfderiv_snd]; rfl
  have e1 : 0 ≤ DCInducedForm (I := I₁.prod I₂) g₁ Prod.fst p u u := by
    rw [DCInducedForm_apply, hfst]; exact g₁.metricInner_self_nonneg _ _
  have e2 : 0 ≤ DCInducedForm (I := I₁.prod I₂) g₂ Prod.snd p u u := by
    rw [DCInducedForm_apply, hsnd]; exact g₂.metricInner_self_nonneg _ _
  have hor : u.1 ≠ 0 ∨ u.2 ≠ 0 := by
    rw [← not_and_or]; exact fun h => hu (Prod.ext h.1 h.2)
  simp only [DCProductForm, ContinuousLinearMap.add_apply]
  rcases hor with h1 | h2
  · have hp1 : 0 < DCInducedForm (I := I₁.prod I₂) g₁ Prod.fst p u u := by
      rw [DCInducedForm_apply, hfst]; exact g₁.metricInner_self_pos _ _ h1
    linarith
  · have hp2 : 0 < DCInducedForm (I := I₁.prod I₂) g₂ Prod.snd p u u := by
      rw [DCInducedForm_apply, hsnd]; exact g₂.metricInner_self_pos _ _ h2
    linarith

/-- **Math.** do Carmo Ch.1 Ex. 2.7: **the product metric** on `M₁ × M₂`. Given Riemannian metrics
`g₁, g₂` on the factors, `⟨u, v⟩_{(p,q)} = ⟨dπ₁ u, dπ₁ v⟩_p + ⟨dπ₂ u, dπ₂ v⟩_q` is a Riemannian
metric: symmetric and bilinear termwise, positive-definite because `u ≠ 0` forces a nonzero
projection, and smooth as the sum of two smooth pullback sections (`DCInducedForm_contMDiff` along the
smooth projections). Taking `S¹ × ⋯ × S¹` recovers the flat torus. -/
noncomputable def DCProductMetric (g₁ : RiemannianMetric I₁ M₁) (g₂ : RiemannianMetric I₂ M₂)
    [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂] :
    RiemannianMetric (I₁.prod I₂) (M₁ × M₂) where
  inner p := DCProductForm g₁ g₂ p
  symm p u v := DCProductForm_symm g₁ g₂ p u v
  pos p u hu := DCProductForm_self_pos g₁ g₂ p u hu
  isVonNBounded p := by
    refine isVonNBounded_of_posDef (E := E₁ × E₂) (DCProductForm g₁ g₂ p) (fun u hu => ?_)
    exact DCProductForm_self_pos g₁ g₂ p u hu
  contMDiff :=
    ContMDiff.add_section (DCInducedForm_contMDiff g₁ contMDiff_fst)
      (DCInducedForm_contMDiff g₂ contMDiff_snd)

end ProductMetric

/-! ## Left-invariant metric on a Lie group (do Carmo Ex. 1.2.6) -/

section LieGroupMetric

open Bundle

variable {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [IsManifold I ∞ G] [LieGroup I ∞ G]

/-- **Math.** do Carmo Ch.1 Ex. 2.6: the **left-invariant form** obtained by transporting a
fixed bilinear form `b` on the Lie algebra `T_eG` back to every tangent space through the
differential of left translation by `x^{-1}`,
`⟨u, v⟩_x = b(d(L_{x^{-1}})_x u, d(L_{x^{-1}})_x v)`. Because `L_{x^{-1}}(x) = e`, the
differential `d(L_{x^{-1}})_x` lands in `T_eG` (all fibres share the model space `E`). This is
formula (2) of do Carmo, and it is left invariant by construction. -/
noncomputable def DCLeftInvariantForm (b : E →L[ℝ] E →L[ℝ] ℝ) (x : G) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  let A : E →L[ℝ] E := mfderiv I I (x⁻¹ * ·) x
  (b.bilinearComp A A : E →L[ℝ] E →L[ℝ] ℝ)

omit [IsManifold I ∞ G] [LieGroup I ∞ G] in
@[simp]
theorem DCLeftInvariantForm_apply (b : E →L[ℝ] E →L[ℝ] ℝ) (x : G) (u v : TangentSpace I x) :
    DCLeftInvariantForm (I := I) b x u v
      = b (mfderiv I I (x⁻¹ * ·) x u) (mfderiv I I (x⁻¹ * ·) x v) :=
  rfl

omit [IsManifold I ∞ G] in
/-- **Math.** The differential of left translation by `x^{-1}` at `x` is injective: `L_x` is its
smooth inverse, so `d(L_x)_e ∘ d(L_{x^{-1}})_x = d(L_x ∘ L_{x^{-1}})_x = d(\mathrm{id})_x = 1`. -/
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
theorem DCLeftInvariantForm_symm (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ u v : E, b u v = b v u) (x : G) (u v : TangentSpace I x) :
    DCLeftInvariantForm (I := I) b x u v = DCLeftInvariantForm (I := I) b x v u := by
  simp only [DCLeftInvariantForm_apply]; exact hb _ _

omit [IsManifold I ∞ G] in
/-- **Math.** The left-invariant form is positive definite when the seed form `b` is, because
`d(L_{x^{-1}})_x` is injective (so `u ≠ 0 ⇒ d(L_{x^{-1}})_x u ≠ 0`). -/
theorem DCLeftInvariantForm_pos (b : E →L[ℝ] E →L[ℝ] ℝ)
    (hb : ∀ u : E, u ≠ 0 → 0 < b u u) (x : G) (u : TangentSpace I x) (hu : u ≠ 0) :
    0 < DCLeftInvariantForm (I := I) b x u u := by
  rw [DCLeftInvariantForm_apply]
  refine hb _ (fun h => hu ?_)
  exact mfderiv_mul_left_inv_injective x (h.trans (map_zero _).symm)

omit [IsManifold I ∞ G] in
/-- **Math.** The left-invariant form varies smoothly. In tangent coordinates around `x₀` the
section `x ↦ ⟨d(L_{x^{-1}})_x·, d(L_{x^{-1}})_x·⟩` equals `ξ ↦ B(D x ·)(D x ·)`, where
`D x = inTangentCoordinates I I id (·⁻¹·) (mfderiv (·⁻¹ * ·)) x₀ x` is the differential of left
translation read in tangent coordinates (smooth by the family lemma `ContMDiffAt.mfderiv`, since
`(x, y) ↦ x⁻¹ * y` is smooth on a Lie group) and `B` is the fixed seed form `b` transported through
the (constant) target coordinate change at `e`. This is a composition of smooth model-space maps,
so the coordinate representation — hence the bundle section — is smooth. -/
theorem DCLeftInvariantForm_contMDiff (b : E →L[ℝ] E →L[ℝ] ℝ) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : G ↦ (⟨x, DCLeftInvariantForm (I := I) b x⟩ :
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
    DCLeftInvariantForm_apply, ← hsT, ContinuousLinearMap.bilinearComp_apply, ← hkey a, ← hkey c]
  rfl

/-- **Math.** do Carmo Ch.1 Ex. 2.6: **the left-invariant metric of a Lie group.** Given any
positive-definite symmetric inner product `b` on the Lie algebra `T_eG`, formula (2)
`⟨u, v⟩_x = b(d(L_{x^{-1}})_x u, d(L_{x^{-1}})_x v)` defines a Riemannian metric on `G` that is left
invariant by construction. It is symmetric (`DCLeftInvariantForm_symm`) and positive definite
(`DCLeftInvariantForm_pos`, via injectivity of `d(L_{x^{-1}})_x`), and smooth
(`DCLeftInvariantForm_contMDiff`, from smoothness of the group multiplication). Every Lie group thus
carries a left-invariant metric (and, if compact, a bi-invariant one). -/
noncomputable def DCLeftInvariantMetric [FiniteDimensional ℝ E]
    (b : E →L[ℝ] E →L[ℝ] ℝ) (hsymm : ∀ u v : E, b u v = b v u)
    (hpos : ∀ u : E, u ≠ 0 → 0 < b u u) :
    RiemannianMetric I G where
  inner x := DCLeftInvariantForm (I := I) b x
  symm x u v := DCLeftInvariantForm_symm b hsymm x u v
  pos x u hu := DCLeftInvariantForm_pos b hpos x u hu
  isVonNBounded x := by
    refine isVonNBounded_of_posDef (E := E) (DCLeftInvariantForm (I := I) b x) (fun u hu => ?_)
    exact DCLeftInvariantForm_pos b hpos x u hu
  contMDiff := DCLeftInvariantForm_contMDiff b

end LieGroupMetric

end Riemannian

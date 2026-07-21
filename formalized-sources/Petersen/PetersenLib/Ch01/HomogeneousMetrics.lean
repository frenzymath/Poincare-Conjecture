import PetersenLib.Ch01.MetricConstructions
import PetersenLib.Foundations.HorizontalLift
import PetersenLib.Ch01.Sphere
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Ball.Action
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Petersen Ch. 1, §1.3.2 — homogeneous quotient metrics and the Fubini–Study metric

Petersen §1.3.2: if a group acts by isometries on a Riemannian manifold
`(M, g)` and the orbit space is a smooth manifold, the quotient map becomes a
Riemannian submersion for a *unique* metric on the quotient
(`homogeneousQuotientMetric`); applied to the isometric scalar action of the
circle `S¹ ⊆ ℂ` on the unit sphere `S^{2n+1} ⊆ ℂ^{n+1}` this produces the
**Fubini–Study metric** on `ℂPⁿ = S^{2n+1}/S¹` (`fubiniStudyMetric`,
Petersen Example 1.3.4).

## Implementation

Mathlib has no quotient-manifold construction, so — exactly as in
`quotientMetric` (`PetersenLib.Ch01.MetricConstructions`) for discrete
coverings — the quotient is represented by hypotheses: a smooth manifold
`M'`, a surjective smooth map `q : M → M'` whose differentials are
surjective, whose fibres are exactly the orbits of the group action, with
the action being by Riemannian isometries.

* `exists_preimage_orthogonal_ker` — the linear-algebra heart of horizontal
  lifting: for a positive-definite continuous bilinear form and a surjective
  continuous linear map, every target vector has a preimage orthogonal to
  the kernel (`T_pM = ker Dq ⊕ (ker Dq)^⊥`).
* `metricInner_eq_of_horizontal_of_smul_isometry` — well-definedness of the
  quotient inner product: horizontal vectors at two points of the same fibre
  with the same pushforward have the same inner products.  This is the
  mathematical content of "the group acts by isometries".
* `IsRiemannianSubmersion.unique` — at most one metric on the base makes a
  fixed surjective map a Riemannian submersion (values are forced on
  horizontal lifts).
* `horizontalLiftAt` / `quotientForm` — the horizontal lift of `Dq_p` and the
  transported form `(u,v) ↦ g_p(L_p u, L_p v)` it induces on the base;
  `quotientForm_contMDiffAt` proves this form is a *smooth* section, using the
  smooth local sections of `exists_localSection_of_mfderiv_surjective` together
  with the smooth dependence of the horizontal lift on `(g_p, Dq_p)`
  (`PetersenLib.contDiffAt_horizontalLift`).
* `homogeneousQuotientMetric` — existence **and** uniqueness of the quotient
  metric (both halves proved).
* `fubiniStudyMetric` — instantiation for the Hopf action of `Circle` on
  `S^{2n+1} ⊆ ℂ^{n+1}`, whose isometry property is *proved*
  (`isRiemannianIsometry_circle_smul_sphere`); the manifold `ℂPⁿ` and the
  projection are hypotheses since Mathlib's `Projectivization` carries no
  smooth structure.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.3.2 and
Example 1.3.4.
-/

open Metric Module Function Bundle
open scoped ContDiff Manifold Topology

noncomputable section

namespace PetersenLib

/-! ## Horizontal lifts: linear algebra

For a Riemannian submersion the inner product on the base is read off from
*horizontal lifts*: preimages under `Dq` that are `g`-orthogonal to
`ker Dq`.  The underlying linear algebra is that a positive-definite form
splits any finite-dimensional space as `K ⊕ K^⊥` for every subspace `K`. -/

section HorizontalLift

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Math.** Petersen §1.3.2 (linear-algebra core of horizontal lifting):
if `B` is a symmetric positive-definite continuous bilinear form on a
finite-dimensional space `V` and `f : V → W` is a surjective continuous
linear map, then every `y ∈ W` has a preimage that is `B`-orthogonal to
`ker f` — a **horizontal lift**.  Positive-definiteness makes the
restriction of `B` to `K = ker f` nondegenerate, so `V = K ⊕ K^⊥_B` and the
`K^⊥_B`-component of any preimage of `y` is again a preimage. -/
theorem exists_preimage_orthogonal_ker
    (B : V →L[ℝ] V →L[ℝ] ℝ) (hsymm : ∀ u v : V, B u v = B v u)
    (hpos : ∀ u : V, u ≠ 0 → 0 < B u u)
    (f : V →L[ℝ] W) (hf : Function.Surjective f) (y : W) :
    ∃ v : V, f v = y ∧ ∀ w : V, f w = 0 → B v w = 0 := by
  classical
  -- the algebraic bilinear form associated with `B`
  set Bl : LinearMap.BilinForm ℝ V :=
    LinearMap.mk₂ ℝ (fun u v => B u v)
      (fun u₁ u₂ v => by simp)
      (fun c u v => by simp)
      (fun u v₁ v₂ => by simp)
      (fun c u v => by simp) with hBl
  have hBl_apply : ∀ u v : V, Bl u v = B u v := fun _ _ => rfl
  have hrefl : Bl.IsRefl := fun u v h => by
    rw [hBl_apply, hsymm]
    exact h
  set K : Submodule ℝ V := LinearMap.ker (f : V →ₗ[ℝ] W) with hK
  -- positive-definiteness makes the restriction of `Bl` to `K` nondegenerate
  have hdiag : ∀ w : K, Bl.restrict K w w = 0 → w = 0 := by
    intro w h0
    have h0' : B (w : V) (w : V) = 0 := by
      simpa [LinearMap.BilinForm.restrict_apply] using h0
    refine Subtype.ext ?_
    by_contra hne
    exact (hpos _ hne).ne' h0'
  have hnd : (Bl.restrict K).Nondegenerate :=
    And.intro (fun w hw => hdiag w (hw w)) (fun w hw => hdiag w (hw w))
  -- hence `V = K ⊕ K^⊥`
  have hcompl : IsCompl K (Bl.orthogonal K) :=
    Bl.isCompl_orthogonal_of_restrict_nondegenerate hrefl hnd
  obtain ⟨v₀, rfl⟩ := hf y
  have hmem : v₀ ∈ K ⊔ Bl.orthogonal K := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨k, hk, h, hh, rfl⟩ := Submodule.mem_sup.mp hmem
  refine ⟨h, ?_, fun w hw => ?_⟩
  · have hk0 : f k = 0 := LinearMap.mem_ker.mp hk
    rw [map_add, hk0, zero_add]
  · have hwh : Bl w h = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hh) w (LinearMap.mem_ker.mpr hw)
    rw [hsymm]
    exact hwh

end HorizontalLift

/-! ## Riemannian submersions onto quotients by isometric group actions
(Petersen §1.3.2) -/

section QuotientSubmersion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** Petersen §1.3.2 (well-definedness of the quotient metric):
suppose a group `G` acts on `(M, g)` by Riemannian isometries and
`q : M → M'` is a smooth map whose fibres are exactly the `G`-orbits.  If
`u, v` are horizontal at `p` (i.e. `g`-orthogonal to `ker Dq_p`), `u', v'`
are horizontal at `p'` in the same fibre, and `Dq_p u = Dq_{p'} u'`,
`Dq_p v = Dq_{p'} v'`, then `g_p(u, v) = g_{p'}(u', v')`.

Writing `p' = a • p`, the differential of the isometry `a • ·` carries
`ker Dq_p` onto `ker Dq_{p'}` (since `q ∘ (a • ·) = q`), hence horizontal
vectors to horizontal vectors; a horizontal preimage of a fixed vector of
`T_{q p}M'` is unique (the difference is horizontal *and* vertical, hence
has `g`-norm zero), so `u' = D(a • ·) u`, `v' = D(a • ·) v` and the claim
follows because `a • ·` preserves `g`.  This is precisely the statement
that the quotient inner product on horizontal lifts does not depend on the
chosen point of the fibre. -/
theorem metricInner_eq_of_horizontal_of_smul_isometry
    {G : Type*} [Group G] [MulAction G M]
    (g : RiemannianMetric I M) (q : M → M')
    (hiso : ∀ a : G, IsRiemannianIsometry g g (a • · : M → M))
    (hq_cont : ContMDiff I I' ∞ q)
    (hfib : ∀ p p' : M, q p = q p' ↔ ∃ a : G, a • p = p')
    (p p' : M) (hpp' : q p = q p')
    {u v : TangentSpace I p} {u' v' : TangentSpace I p'}
    (hu : ∀ w : TangentSpace I p, mfderiv I I' q p w = 0 → g.metricInner p u w = 0)
    (hv : ∀ w : TangentSpace I p, mfderiv I I' q p w = 0 → g.metricInner p v w = 0)
    (hu' : ∀ w : TangentSpace I p', mfderiv I I' q p' w = 0 → g.metricInner p' u' w = 0)
    (hv' : ∀ w : TangentSpace I p', mfderiv I I' q p' w = 0 → g.metricInner p' v' w = 0)
    (huu' : mfderiv I I' q p u = mfderiv I I' q p' u')
    (hvv' : mfderiv I I' q p v = mfderiv I I' q p' v') :
    g.metricInner p u v = g.metricInner p' u' v' := by
  obtain ⟨a, rfl⟩ := (hfib p p').mp hpp'
  obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hiso a
  obtain ⟨⟨Ψ, hΨ⟩, -⟩ := hiso a⁻¹
  have hφc : ContMDiff I I ∞ (a • · : M → M) := by rw [← hΦ]; exact Φ.contMDiff
  have hψc : ContMDiff I I ∞ (a⁻¹ • · : M → M) := by rw [← hΨ]; exact Ψ.contMDiff
  have hφd : ∀ x : M, MDifferentiableAt I I (a • · : M → M) x :=
    fun x => (hφc x).mdifferentiableAt (by simp)
  have hψd : ∀ x : M, MDifferentiableAt I I (a⁻¹ • · : M → M) x :=
    fun x => (hψc x).mdifferentiableAt (by simp)
  have hqd : ∀ x : M, MDifferentiableAt I I' q x :=
    fun x => (hq_cont x).mdifferentiableAt (by simp)
  -- orbits lie in fibres: `q ∘ (a • ·) = q`
  have hqφ : (q ∘ (a • · : M → M)) = q :=
    funext fun x => ((hfib x (a • x)).mpr ⟨a, rfl⟩).symm
  -- the differential of `q` absorbs the differential of the action
  have hDq : ∀ w : TangentSpace I p,
      mfderiv I I' q (a • p) (mfderiv I I (a • · : M → M) p w) = mfderiv I I' q p w := by
    intro w
    have h1 : mfderiv I I' (q ∘ (a • · : M → M)) p w
        = mfderiv I I' q (a • p) (mfderiv I I (a • · : M → M) p w) :=
      mfderiv_comp_apply p (hqd (a • p)) (hφd p) w
    rw [← h1, hqφ]
  -- the differential of the action at `p` is inverted by that of the inverse action
  have hφψ : ((a • ·) ∘ (a⁻¹ • ·) : M → M) = id := funext fun x => smul_inv_smul a x
  have hDφψ : ∀ w' : TangentSpace I (a • p),
      mfderiv I I (a • · : M → M) p
        (mfderiv I I (a⁻¹ • · : M → M) (a • p) w') = w' := by
    intro w'
    have h1 : mfderiv I I ((a • ·) ∘ (a⁻¹ • ·) : M → M) (a • p) w'
        = mfderiv I I (a • · : M → M) p
            (mfderiv I I (a⁻¹ • · : M → M) (a • p) w') :=
      mfderiv_comp_apply_of_eq (a • p) (hφd p) (hψd (a • p)) (inv_smul_smul a p) w'
    rw [← h1, hφψ, mfderiv_id]
    rfl
  -- the pushforward of a horizontal vector is horizontal
  have hpush : ∀ z : TangentSpace I p,
      (∀ w : TangentSpace I p, mfderiv I I' q p w = 0 → g.metricInner p z w = 0) →
      ∀ w' : TangentSpace I (a • p), mfderiv I I' q (a • p) w' = 0 →
        g.metricInner (a • p) (mfderiv I I (a • · : M → M) p z) w' = 0 := by
    intro z hz w' hw'
    have hww' : mfderiv I I (a • · : M → M) p
        (mfderiv I I (a⁻¹ • · : M → M) (a • p) w') = w' := hDφψ w'
    have hker : mfderiv I I' q p (mfderiv I I (a⁻¹ • · : M → M) (a • p) w') = 0 := by
      rw [← hDq (mfderiv I I (a⁻¹ • · : M → M) (a • p) w'), hww']
      exact hw'
    calc g.metricInner (a • p) (mfderiv I I (a • · : M → M) p z) w'
        = g.metricInner (a • p) (mfderiv I I (a • · : M → M) p z)
            (mfderiv I I (a • · : M → M) p
              (mfderiv I I (a⁻¹ • · : M → M) (a • p) w')) := by rw [hww']
      _ = g.metricInner p z (mfderiv I I (a⁻¹ • · : M → M) (a • p) w') :=
          (hpres p z (mfderiv I I (a⁻¹ • · : M → M) (a • p) w')).symm
      _ = 0 := hz _ hker
  -- a horizontal preimage over the fibre is unique: `z' = D(a • ·) z`
  have hlift : ∀ (z : TangentSpace I p) (z' : TangentSpace I (a • p)),
      (∀ w : TangentSpace I p, mfderiv I I' q p w = 0 → g.metricInner p z w = 0) →
      (∀ w' : TangentSpace I (a • p),
        mfderiv I I' q (a • p) w' = 0 → g.metricInner (a • p) z' w' = 0) →
      mfderiv I I' q p z = mfderiv I I' q (a • p) z' →
      mfderiv I I (a • · : M → M) p z = z' := by
    intro z z' hz hz' hzz'
    have hsker : mfderiv I I' q (a • p) (z' - mfderiv I I (a • · : M → M) p z) = 0 := by
      rw [map_sub, hDq z, hzz', sub_self]
    have hcancel : g.metricInner (a • p) (z' - mfderiv I I (a • · : M → M) p z)
        (z' - mfderiv I I (a • · : M → M) p z) = 0 := by
      rw [g.metricInner_sub_left, hz' _ hsker, hpush z hz _ hsker, sub_self]
    have hs0 : z' - mfderiv I I (a • · : M → M) p z = 0 := by
      by_contra hne
      exact absurd hcancel (g.metricInner_self_pos (a • p) _ hne).ne'
    exact (sub_eq_zero.mp hs0).symm
  have hu'' : mfderiv I I (a • · : M → M) p u = u' := hlift u u' hu hu' huu'
  have hv'' : mfderiv I I (a • · : M → M) p v = v' := hlift v v' hv hv' hvv'
  rw [← hu'', ← hv'']
  exact hpres p u v

/-- **Math.** Petersen §1.3.2 (uniqueness of the submersion metric): a
surjective smooth map `q : (M, g) → M'` is a Riemannian submersion for *at
most one* metric on `M'`.  Every tangent vector of `M'` has a horizontal
lift (`exists_preimage_orthogonal_ker` applied to `Dq_p`), and the
submersion property forces
`g_N(Dq u, Dq v) = g(u, v)` on horizontal `u, v` — so all inner products
downstairs are determined by `g`. -/
theorem IsRiemannianSubmersion.unique [FiniteDimensional ℝ E]
    {g : RiemannianMetric I M} {gN gN' : RiemannianMetric I' M'} {q : M → M'}
    (h : IsRiemannianSubmersion g gN q) (h' : IsRiemannianSubmersion g gN' q)
    (hq_surj : Function.Surjective q) : gN = gN' := by
  refine RiemannianMetric.ext_inner fun y => ?_
  obtain ⟨p, rfl⟩ := hq_surj y
  refine ContinuousLinearMap.ext fun u' => ContinuousLinearMap.ext fun v' => ?_
  obtain ⟨u, hu, huH⟩ := exists_preimage_orthogonal_ker (V := E) (W := E') (g.inner p)
    (g.metricInner_comm p) (g.metricInner_self_pos p) (mfderiv I I' q p) (h.2.1 p) u'
  obtain ⟨v, hv, hvH⟩ := exists_preimage_orthogonal_ker (V := E) (W := E') (g.inner p)
    (g.metricInner_comm p) (g.metricInner_self_pos p) (mfderiv I I' q p) (h.2.1 p) v'
  have h1 := h.2.2 p u v huH hvH
  have h2 := h'.2.2 p u v huH hvH
  rw [← hu, ← hv]
  exact h1.symm.trans h2

/-! ### The quotient form

For a submersion `q : (M, g) → M'` the candidate metric downstairs is obtained by
transporting `g` through the **horizontal lift** `L_p` of `Dq_p` — the inverse of
`Dq_p` restricted to `(ker Dq_p)^⊥`.  The linear algebra (including the smooth
dependence of `L_p` on `(g_p, Dq_p)`, which is what makes the quotient metric a
*smooth* section) is in `PetersenLib/Foundations/HorizontalLift.lean`. -/

section QuotientForm

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- **Math.** The **horizontal lift** at `p` of a submersion `q`: the inverse of the
isomorphism `Dq_p : (ker Dq_p)^⊥ → T_{q(p)}M'`.  (`I'` is explicit: it occurs only in
the differential `Dq_p`, so it cannot be inferred from `g`, `q` and `p`.) -/
noncomputable def horizontalLiftAt (I' : ModelWithCorners ℝ E' H')
    [IsManifold I' ∞ M'] (g : RiemannianMetric I M) (q : M → M') (p : M) :
    E' →L[ℝ] E :=
  horizontalLift (E := E) (E' := E') (g.inner p) (mfderiv I I' q p)

/-- **Math.** The horizontal lift is a lift: `Dq_p (L_p u) = u`. -/
theorem mfderiv_horizontalLiftAt (g : RiemannianMetric I M) {q : M → M'} {p : M}
    (hp : Function.Surjective (mfderiv I I' q p)) (u : E') :
    mfderiv I I' q p (horizontalLiftAt I' g q p u) = u :=
  horizontalLift_rightInverse (E := E) (E' := E') (g.metricInner_self_pos p) hp u

/-- **Math.** The horizontal lift is horizontal: `L_p u ⟂ ker Dq_p`. -/
theorem horizontalLiftAt_horizontal (g : RiemannianMetric I M) {q : M → M'} {p : M}
    (hp : Function.Surjective (mfderiv I I' q p)) (u : E') :
    ∀ w : TangentSpace I p, mfderiv I I' q p w = 0 →
      g.metricInner p (horizontalLiftAt I' g q p u) w = 0 :=
  fun _ hw => horizontalLift_horizontal (E := E) (E' := E')
    (g.metricInner_self_pos p) (mfderiv I I' q p) u hw

/-- **Math.** A horizontal vector is the horizontal lift of its image. -/
theorem horizontalLiftAt_mfderiv_of_horizontal (g : RiemannianMetric I M) {q : M → M'} {p : M}
    (hp : Function.Surjective (mfderiv I I' q p)) {u : TangentSpace I p}
    (hu : ∀ w : TangentSpace I p, mfderiv I I' q p w = 0 → g.metricInner p u w = 0) :
    horizontalLiftAt I' g q p (mfderiv I I' q p u) = u :=
  horizontalLift_apply_apply_of_horizontal (E := E) (E' := E')
    (g.metricInner_self_pos p) hp hu

/-- **Math.** The horizontal lift of a nonzero vector is nonzero. -/
theorem horizontalLiftAt_ne_zero (g : RiemannianMetric I M) {q : M → M'} {p : M}
    (hp : Function.Surjective (mfderiv I I' q p)) {u : E'} (hu : u ≠ 0) :
    horizontalLiftAt I' g q p u ≠ 0 :=
  horizontalLift_ne_zero (E := E) (E' := E') (g.metricInner_self_pos p) hp hu

/-- **Math.** The **quotient form** at `p`: the bilinear form on `T_{q(p)}M'` obtained
by transporting `g_p` through the horizontal lift, `(u,v) ↦ g_p(L_p u, L_p v)`.  This
is the value that any metric making `q` a Riemannian submersion must take. -/
noncomputable def quotientForm (I' : ModelWithCorners ℝ E' H')
    [IsManifold I' ∞ M'] (g : RiemannianMetric I M) (q : M → M') (p : M) :
    TangentSpace I' (q p) →L[ℝ] TangentSpace I' (q p) →L[ℝ] ℝ :=
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner p
  let L : E' →L[ℝ] E := horizontalLiftAt I' g q p
  (B.bilinearComp L L : E' →L[ℝ] E' →L[ℝ] ℝ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
@[simp]
theorem quotientForm_apply (g : RiemannianMetric I M) (q : M → M') (p : M) (u v : E') :
    quotientForm I' g q p u v =
      g.metricInner p (horizontalLiftAt I' g q p u) (horizontalLiftAt I' g q p v) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem quotientForm_comm (g : RiemannianMetric I M) (q : M → M') (p : M) (u v : E') :
    quotientForm I' g q p u v = quotientForm I' g q p v u := by
  rw [quotientForm_apply, quotientForm_apply, g.metricInner_comm]

theorem quotientForm_pos (g : RiemannianMetric I M) {q : M → M'} {p : M}
    (hp : Function.Surjective (mfderiv I I' q p)) {u : E'} (hu : u ≠ 0) :
    0 < quotientForm I' g q p u u :=
  g.metricInner_self_pos p _ (horizontalLiftAt_ne_zero g hp hu)

/-- **Math.** **The quotient form is a smooth section of the bilinear-form bundle.**
Read through a smooth local section `s` of the submersion `q`, the field
`y ↦ g_{s y}(L_{s y} ·, L_{s y} ·)` is `C^∞` at `y₀`.

This is the technical heart of the existence of quotient metrics.  In the tangent
trivializations around `p₀ = s y₀` and `y₀`, the data `(g_{s y}, Dq_{s y})` is a
smooth family of (positive-definite form, surjective map) pairs — smooth by
`g.contMDiff` and `ContMDiffAt.mfderiv` respectively — and the horizontal lift
depends smoothly on that pair (`contDiffAt_horizontalLift`).  Naturality of the
horizontal lift under the trivializing isomorphisms (`horizontalLift_congr`)
identifies the coordinate expression with the section we want. -/
theorem quotientForm_contMDiffAt (g : RiemannianMetric I M) {q : M → M'}
    (hq_cont : ContMDiff I I' ∞ q)
    (hq_subm : ∀ p : M, Function.Surjective (mfderiv I I' q p))
    {s : M' → M} {y₀ : M'} (hs : ContMDiffAt I' I ∞ s y₀)
    (hsec : ∀ᶠ y in 𝓝 y₀, q (s y) = y) :
    ContMDiffAt I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y ↦ (⟨y, quotientForm I' g q (s y)⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y ↦ TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))) y₀ := by
  have hqsy₀ : q (s y₀) = y₀ := hsec.self_of_nhds
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  set τ := trivializationAt E (TangentSpace I) (s y₀) with hτ
  set σ := trivializationAt E' (TangentSpace I') y₀ with hσ
  have hp₀mem : s y₀ ∈ τ.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) (s y₀)
  have hy₀mem : y₀ ∈ σ.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') y₀
  -- The tangent trivialization of `M'` used by `inTangentCoordinates` sits at `q (s y₀)`,
  -- which *equals* `y₀` but is not syntactically it.
  have htriv_eq : trivializationAt E' (TangentSpace I') (q (s y₀)) = σ := by
    rw [hσ, hqsy₀]
  -- `D y` is the differential of `q` at `s y`, read in tangent coordinates.
  set D : M' → (E →L[ℝ] E') :=
    inTangentCoordinates I I' s (fun y => q (s y)) (fun y => mfderiv I I' q (s y)) y₀ with hD
  have hDsmooth : ContMDiffAt I' 𝓘(ℝ, E →L[ℝ] E') ∞ D y₀ := by
    have huncurry : ContMDiffAt (I'.prod I) I' ∞
        (Function.uncurry fun (_ : M') (p : M) => q p) (y₀, s y₀) :=
      ContMDiffAt.comp (y₀, s y₀) hq_cont.contMDiffAt contMDiffAt_snd
    exact ContMDiffAt.mfderiv (fun _ p => q p) s huncurry hs (by simp)
  -- `G p` is the metric at `p`, read in the tangent coordinates around `s y₀`.
  set G : M → (E →L[ℝ] E →L[ℝ] ℝ) := fun p =>
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
      (fun p => TangentSpace I p →L[ℝ] ℝ) (s y₀) p (s y₀) p (g.inner p) with hG
  have hGsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ G (s y₀) :=
    ((contMDiffAt_hom_bundle _).mp g.contMDiff.contMDiffAt).2
  have hGs : ContMDiffAt I' 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (fun y => G (s y)) y₀ :=
    hGsmooth.comp y₀ hs
  -- The trivializations conjugate the honest objects into their coordinate versions.
  have hcoeτ : ∀ (p : M) (hp : p ∈ τ.baseSet),
      (τ.symm p : E → TangentSpace I p) = ⇑(τ.continuousLinearEquivAt ℝ p hp).symm := by
    intro p hp
    rw [τ.symm_continuousLinearEquivAt_eq hp]; rfl
  have hGval : ∀ p : M, p ∈ τ.baseSet → ∀ x x' : E,
      G p x x' = g.metricInner p (τ.symm p x) (τ.symm p x') := by
    intro p hp x x'
    rw [hG]
    simp only
    rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M ℝ) hp hp (by simp)]
    simp [Bundle.Trivial.linearMapAt_trivialization, ← hτ]
  have hDval : ∀ y : M', s y ∈ τ.baseSet → q (s y) ∈ σ.baseSet → ∀ x : E,
      σ.symm (q (s y)) (D y x) = mfderiv I I' q (s y) (τ.symm (s y) x) := by
    intro y hsy hqy x
    have hqy₀ : q (s y) ∈ (trivializationAt E' (TangentSpace I') (q (s y₀))).baseSet := by
      rw [htriv_eq]; exact hqy
    have hDx : D y x
        = (trivializationAt E' (TangentSpace I')
              (q (s y₀))).continuousLinearEquivAt ℝ (q (s y)) hqy₀
            (mfderiv I I' q (s y) ((τ.continuousLinearEquivAt ℝ (s y) hsy).symm x)) := by
      rw [hD]
      simp only [inTangentCoordinates]
      rw [ContinuousLinearMap.inCoordinates_eq hsy hqy₀]
      rfl
    have hcoeσ₀ : ((trivializationAt E' (TangentSpace I') (q (s y₀))).symm (q (s y))
          : E' → TangentSpace I' (q (s y)))
        = ⇑((trivializationAt E' (TangentSpace I')
              (q (s y₀))).continuousLinearEquivAt ℝ (q (s y)) hqy₀).symm := by
      rw [Bundle.Trivialization.symm_continuousLinearEquivAt_eq _ hqy₀]; rfl
    have key : (trivializationAt E' (TangentSpace I') (q (s y₀))).symm (q (s y)) (D y x)
        = mfderiv I I' q (s y) (τ.symm (s y) x) := by
      rw [hDx, hcoeσ₀, ContinuousLinearEquiv.symm_apply_apply, hcoeτ (s y) hsy]
    rw [← htriv_eq]
    exact key
  -- Positive-definiteness and surjectivity of the coordinate data at `y₀`.
  have hGpos : ∀ x : E, x ≠ 0 → 0 < G (s y₀) x x := by
    intro x hx
    rw [hGval (s y₀) hp₀mem x x]
    refine g.metricInner_self_pos (s y₀) _ (fun h => hx ?_)
    rw [hcoeτ (s y₀) hp₀mem] at h
    exact (τ.continuousLinearEquivAt ℝ (s y₀) hp₀mem).symm.map_eq_zero_iff.mp h
  have hqmem : q (s y₀) ∈ σ.baseSet := by rw [hqsy₀]; exact hy₀mem
  have hDsurj : Function.Surjective (D y₀) := by
    intro u
    obtain ⟨z, hz⟩ := hq_subm (s y₀) (σ.symm (q (s y₀)) u)
    refine ⟨τ.continuousLinearEquivAt ℝ (s y₀) hp₀mem z, ?_⟩
    have hkey := hDval y₀ hp₀mem hqmem (τ.continuousLinearEquivAt ℝ (s y₀) hp₀mem z)
    rw [hcoeτ (s y₀) hp₀mem, ContinuousLinearEquiv.symm_apply_apply, hz] at hkey
    have hcoeσ : (σ.symm (q (s y₀)) : E' → TangentSpace I' (q (s y₀)))
        = ⇑(σ.continuousLinearEquivAt ℝ (q (s y₀)) hqmem).symm := by
      rw [σ.symm_continuousLinearEquivAt_eq hqmem]; rfl
    rw [hcoeσ] at hkey
    have := congrArg (σ.continuousLinearEquivAt ℝ (q (s y₀)) hqmem) hkey
    rwa [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply] at this
  -- The horizontal lift in coordinates, and its smoothness.
  set L : M' → (E' →L[ℝ] E) := fun y => horizontalLift (E := E) (E' := E') (G (s y)) (D y) with hL
  have hLsmooth : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E) ∞ L y₀ := by
    have hpair : ContMDiffAt I' 𝓘(ℝ, (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E')) ∞
        (fun y => (G (s y), D y)) y₀ := hGs.prodMk_space hDsmooth
    have hcd : ContDiffAt ℝ ∞
        (fun z : (E →L[ℝ] E →L[ℝ] ℝ) × (E →L[ℝ] E') => horizontalLift z.1 z.2)
        (G (s y₀), D y₀) :=
      contDiffAt_horizontalLift contDiff_fst.contDiffAt contDiff_snd.contDiffAt hGpos hDsurj
    simpa [hL, Function.comp_def] using
      hcd.comp_contMDiffAt (f := fun y => (G (s y), D y)) (x := y₀) hpair
  -- The coordinate expression of the section is smooth.
  have hΨ : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ) ∞
      (fun y => ((L y).precomp ℝ).comp ((G (s y)).comp (L y))) y₀ := by
    have h1 : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E →L[ℝ] ℝ) ∞
        (fun y => (G (s y)).comp (L y)) y₀ := hGs.clm_comp hLsmooth
    exact (ContMDiffAt.clm_precomp (F₃ := ℝ) hLsmooth).clm_comp h1
  refine hΨ.congr_of_eventuallyEq ?_
  have hUs : {y : M' | s y ∈ τ.baseSet} ∈ 𝓝 y₀ :=
    hs.continuousAt (τ.open_baseSet.mem_nhds hp₀mem)
  have hUt : {y : M' | y ∈ σ.baseSet} ∈ 𝓝 y₀ := σ.open_baseSet.mem_nhds hy₀mem
  filter_upwards [hsec, hUs, hUt] with y hy hsy hyy
  have hqy : q (s y) ∈ σ.baseSet := by rw [hy]; exact hyy
  -- Naturality: the coordinate horizontal lift *is* the honest one, conjugated.
  have hnat : ∀ a : E', τ.symm (s y) (L y a) = horizontalLiftAt I' g q (s y) (σ.symm y a) := by
    intro a
    -- The trivializing isomorphisms, pinned to the model-space instances.
    set θ : E ≃L[ℝ] E := τ.continuousLinearEquivAt ℝ (s y) hsy with hθ
    set ι : E' ≃L[ℝ] E' := σ.continuousLinearEquivAt ℝ (q (s y)) hqy with hι
    have hcoeσq : (σ.symm (q (s y)) : E' → TangentSpace I' (q (s y)))
        = ⇑(σ.continuousLinearEquivAt ℝ (q (s y)) hqy).symm := by
      rw [σ.symm_continuousLinearEquivAt_eq hqy]; rfl
    have hθsymm : ∀ v : E, (τ.symm (s y) v : E) = θ.symm v := fun v => by
      rw [hθ]; exact congrFun (hcoeτ (s y) hsy) v
    have hιsymm : ∀ w : E', (σ.symm (q (s y)) w : E') = ι.symm w := fun w => by
      rw [hι]; exact congrFun hcoeσq w
    -- The honest data at `s y`, in the model-space instances.
    have hB' : ∀ x x' : E,
        G (s y) x x' = (g.inner (s y) : E →L[ℝ] E →L[ℝ] ℝ) (θ.symm x) (θ.symm x') := by
      intro x x'
      rw [hGval (s y) hsy x x', ← hθsymm x, ← hθsymm x']
      rfl
    have hA' : ∀ x : E,
        D y x = ι ((mfderiv I I' q (s y) : E →L[ℝ] E') (θ.symm x)) := by
      intro x
      have h := hDval y hsy hqy x
      rw [hιsymm (D y x), hθsymm x] at h
      rw [← h, ContinuousLinearEquiv.apply_symm_apply]
    have hcongr := horizontalLift_congr (E := E) (E' := E') (F := E) (F' := E')
      (B := (g.inner (s y) : E →L[ℝ] E →L[ℝ] ℝ))
      (A := (mfderiv I I' q (s y) : E →L[ℝ] E'))
      (g.metricInner_self_pos (s y)) (hq_subm (s y)) θ ι hB' hA' a
    have hσy : (σ.symm y a : E') = ι.symm a := by rw [← hy]; exact hιsymm a
    rw [hL]
    simp only
    rw [hcongr, hθsymm, ContinuousLinearEquiv.symm_apply_apply, horizontalLiftAt, hσy]
  refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
  have hRHS : (((ContinuousLinearMap.precomp ℝ (L y)).comp ((G (s y)).comp (L y))) a) b
      = G (s y) (L y a) (L y b) := rfl
  have htrivM' : trivializationAt ℝ (Bundle.Trivial M' ℝ) y₀
      = Bundle.Trivial.trivialization M' ℝ := Bundle.Trivial.eq_trivialization M' ℝ _
  rw [hRHS, hGval (s y) hsy (L y a) (L y b), hnat a, hnat b]
  rw [inCoordinates_apply_eq₂ (E₃ := Bundle.Trivial M' ℝ) hyy hyy (by simp)]
  simp only [htrivM', Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_coe, id_eq, ← hσ]
  rfl

end QuotientForm

/-- **Math.** Petersen §1.3.2 (Riemannian submersions onto homogeneous
quotients; see also Petersen Thm 5.6.21): let a group `G` act by Riemannian
isometries on `(M, g)` such that the orbit space is a smooth manifold, with
quotient map `q`.  Then there is a **unique Riemannian metric on the
quotient making `q` a Riemannian submersion**.

Petersen's setting is `M = G` a Lie group with a metric invariant under
right translations by a compact subgroup `H`, and `q : G → G/H`; the
right-translation action of `H` is the `MulAction` `h • x = x * h⁻¹` (the
usual left action of `H^{op}`), and compactness of `H` is what guarantees
*mathematically* that the smooth quotient exists.  Mathlib has no
quotient-manifold construction, so — exactly as in `quotientMetric` for
discrete coverings — the quotient is represented by hypotheses: a smooth
manifold `M'` and a surjective smooth map `q` with surjective differentials
whose fibres are exactly the `G`-orbits.

Uniqueness is `IsRiemannianSubmersion.unique`: the values of `gN` are forced on
horizontal lifts.  For existence, `gN` at `y` is the inner product of the
horizontal lifts at any point of the fibre `q⁻¹(y)`,

  `gN_y(u,v) = g_p(L_p u, L_p v)`,  `L_p = (Dq_p|_{(ker Dq_p)^⊥})⁻¹`,

which is well defined by `metricInner_eq_of_horizontal_of_smul_isometry` (this is
exactly where `hiso` and `hfib` are used) and positive definite because `L_p` is
injective.  Smoothness — the whole difficulty — is `quotientForm_contMDiffAt`: near
`y₀` one writes `gN` through a smooth local section `s` of `q`
(`exists_localSection_of_mfderiv_surjective`) and uses that the horizontal lift
depends smoothly on `(g_p, Dq_p)` (`contDiffAt_horizontalLift`).

Note that the covering shortcut does **not** apply here: for a covering
`Ds_y = (Dq_{s y})⁻¹`, so the quotient metric is literally the pullback `s^*g`; for
a genuine submersion `Ds_y u` is a lift of `u` but *not* the horizontal one, so
`gN ≠ s^*g` and one really does need the horizontal distribution `p ↦ (ker Dq_p)^⊥`
to vary smoothly.

Petersen's closing remark, that a *left*-invariant metric on `G` in
addition makes `G` act by isometries on `G/H` (so `G/H` is homogeneous), is
a statement about the metric produced by the existence half and is not
formalized separately here. -/
theorem homogeneousQuotientMetric [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']
    [I.Boundaryless] [I'.Boundaryless]
    {G : Type*} [Group G] [MulAction G M]
    (g : RiemannianMetric I M) (q : M → M')
    (hiso : ∀ a : G, IsRiemannianIsometry g g (a • · : M → M))
    (hq_cont : ContMDiff I I' ∞ q)
    (hq_surj : Function.Surjective q)
    (hq_subm : ∀ p : M, Function.Surjective (mfderiv I I' q p))
    (hfib : ∀ p p' : M, q p = q p' ↔ ∃ a : G, a • p = p') :
    ∃! gN : RiemannianMetric I' M', IsRiemannianSubmersion g gN q := by
  classical
  obtain ⟨gN, hgN⟩ : ∃ gN : RiemannianMetric I' M', IsRiemannianSubmersion g gN q := by
    -- Choose a point over each `y` of the base.
    choose pt hpt using hq_surj
    -- The candidate form is independent of the chosen point of the fibre: the
    -- horizontal lifts at `p` and `p'` of the same vector have the same `g`-inner
    -- products, because the group acts by isometries permuting the fibres.
    have hwd : ∀ p p' : M, q p = q p' → ∀ u v : E',
        quotientForm I' g q p u v = quotientForm I' g q p' u v := by
      intro p p' hpp' u v
      refine metricInner_eq_of_horizontal_of_smul_isometry (G := G) g q hiso hq_cont hfib
        p p' hpp' (horizontalLiftAt_horizontal (I' := I') g (hq_subm p) u)
        (horizontalLiftAt_horizontal (I' := I') g (hq_subm p) v)
        (horizontalLiftAt_horizontal (I' := I') g (hq_subm p') u)
        (horizontalLiftAt_horizontal (I' := I') g (hq_subm p') v) ?_ ?_
      · exact (mfderiv_horizontalLiftAt (I' := I') g (hq_subm p) u).trans
          (mfderiv_horizontalLiftAt (I' := I') g (hq_subm p') u).symm
      · exact (mfderiv_horizontalLiftAt (I' := I') g (hq_subm p) v).trans
          (mfderiv_horizontalLiftAt (I' := I') g (hq_subm p') v).symm
    have hpos : ∀ (p : M) (u : E'), u ≠ 0 → 0 < quotientForm I' g q p u u := fun p u hu =>
      quotientForm_pos (I' := I') g (hq_subm p) hu
    refine ⟨{ inner := fun y => quotientForm I' g q (pt y)
              symm := fun y u v => quotientForm_comm (I' := I') g q (pt y) u v
              pos := fun y u hu => hpos (pt y) u hu
              isVonNBounded := fun y =>
                isVonNBounded_of_posDef (E := E') (quotientForm I' g q (pt y))
                  (fun u hu => hpos (pt y) u hu)
              contMDiff := ?_ }, ?_⟩
    · -- Smoothness: near `y₀`, replace `pt` by a smooth local section of `q`.
      intro y₀
      obtain ⟨s, hs0, hsdiff, hssec, -⟩ :=
        exists_localSection_of_mfderiv_surjective (q := q) (p := pt y₀)
          hq_cont.contMDiffAt (hq_subm (pt y₀))
      rw [hpt y₀] at hs0 hsdiff hssec
      refine (quotientForm_contMDiffAt (I' := I') g hq_cont hq_subm hsdiff hssec).congr_of_eventuallyEq ?_
      filter_upwards [hssec] with y hy
      have hfib' : q (pt y) = q (s y) := by rw [hpt y, hy]
      exact congrArg _ (ContinuousLinearMap.ext fun u => ContinuousLinearMap.ext fun v =>
        hwd (pt y) (s y) hfib' u v)
    · -- `q` is a Riemannian submersion for this metric.
      refine ⟨hq_cont, hq_subm, fun p u v hu hv => ?_⟩
      show g.metricInner p u v = quotientForm I' g q (pt (q p)) _ _
      rw [hwd (pt (q p)) p (hpt (q p)), quotientForm_apply,
        horizontalLiftAt_mfderiv_of_horizontal (I' := I') g (hq_subm p) hu,
        horizontalLiftAt_mfderiv_of_horizontal (I' := I') g (hq_subm p) hv]
  exact ⟨gN, hgN, fun gN' hgN' => hgN'.unique hgN hq_surj⟩

end QuotientSubmersion

/-! ## The Fubini–Study metric (Petersen Example 1.3.4)

The circle `S¹ = {λ ∈ ℂ : |λ| = 1}` (Mathlib's `Circle`) acts on
`S^{2n+1} ⊆ ℂ^{n+1}` by complex scalar multiplication, and the action is by
isometries of the canonical metric.  The quotient is `ℂPⁿ` with the
Fubini–Study metric. -/

section FubiniStudy

/-- **Eng.** `ℂ^{n+1} = EuclideanSpace ℂ (Fin (n + 1))` has real dimension
`2n + 2 = (2n + 1) + 1`; this `Fact` feeds the sphere
`S^{2n+1} ⊆ ℂ^{n+1}` its stereographic charted-space structure over
`EuclideanSpace ℝ (Fin (2n + 1))`. -/
instance fact_finrank_euclideanSpace_complex (n : ℕ) :
    Fact (finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) = 2 * n + 1 + 1) := by
  constructor
  have h : finrank ℝ ℂ * finrank ℂ (EuclideanSpace ℂ (Fin (n + 1)))
      = finrank ℝ (EuclideanSpace ℂ (Fin (n + 1))) :=
    finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin (n + 1)))
  rw [← h, finrank_euclideanSpace, Complex.finrank_real_complex, Fintype.card_fin]
  ring

/-- **Eng.** The scalar action of the circle `S¹ ⊆ ℂ` on the unit sphere of
a complex normed space, `a • x = (a : ℂ) • x` (Mathlib's action of
`sphere (0 : ℂ) 1` on `sphere (0 : E) 1`, transported along the definitional
equality `Circle = sphere (0 : ℂ) 1`). -/
instance instMulActionCircleSphere {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    MulAction Circle (sphere (0 : E) 1) :=
  inferInstanceAs <| MulAction (sphere (0 : ℂ) 1) (sphere (0 : E) 1)

variable {n : ℕ}

/-- Local shorthand for the ambient space `ℂ^{n+1}` carrying `S^{2n+1}`. -/
local notation "𝔼" => EuclideanSpace ℂ (Fin (n + 1))

/-- **Math.** The real inner product of `ℂ^m` (the `L²`-product of the
real inner products `re⟨z, w⟩` of the coordinates) is the real part of the
complex inner product. -/
theorem real_inner_eq_re_inner_euclideanSpace {m : ℕ} (x y : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ x y : ℝ) = Complex.re (inner ℂ x y) := by
  simp only [PiLp.inner_apply, Complex.re_sum]
  rfl

/-- **Math.** Petersen Example 1.3.4: unit complex scalars act by *real*
linear isometries of `ℂ^m`: `⟨λx, λy⟩_ℝ = re⟨λx, λy⟩_ℂ
= re(λ̄λ⟨x, y⟩_ℂ) = re⟨x, y⟩_ℂ = ⟨x, y⟩_ℝ` since `|λ| = 1`. -/
theorem real_inner_circle_smul_smul {m : ℕ} (a : Circle) (x y : EuclideanSpace ℂ (Fin m)) :
    (inner ℝ ((a : ℂ) • x) ((a : ℂ) • y) : ℝ) = inner ℝ x y := by
  rw [real_inner_eq_re_inner_euclideanSpace, real_inner_eq_re_inner_euclideanSpace]
  congr 1
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, Complex.conj_mul', Circle.norm_coe]
  simp

/-- **Math.** Petersen Example 1.3.4: the scalar action of `a ∈ S¹` on the
sphere `S^{2n+1} ⊆ ℂ^{n+1}` is smooth — it is the restriction of the
(real-linear, continuous) scalar multiplication of the ambient space. -/
theorem contMDiff_circle_smul_sphere (a : Circle) :
    ContMDiff (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1)) ∞
      ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) := by
  have hL : ContMDiff 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) ∞ (fun x : 𝔼 => (a : ℂ) • x) :=
    ((a : ℂ) • ContinuousLinearMap.id ℝ 𝔼).contMDiff
  have hmem : ∀ x : sphere (0 : 𝔼) 1, (a : ℂ) • (x : 𝔼) ∈ sphere (0 : 𝔼) 1 :=
    fun x => (a • x : sphere (0 : 𝔼) 1).2
  exact (hL.comp contMDiff_coe_sphere).codRestrict_sphere hmem

/-- **Math.** The differential of the sphere inclusion intertwines the
differential of the circle action on the sphere with the ambient scalar
multiplication: `Dι_{a•p} ∘ D(a • ·)_p = (a • ·) ∘ Dι_p`.  Chain rule for
`ι ∘ (a • ·) = ((a : ℂ) • ·) ∘ ι`, plus the fact that the ambient map is
its own differential (it is continuous and real-linear). -/
theorem mfderiv_coe_circle_smul_sphere (a : Circle)
    (p : sphere (0 : 𝔼) 1)
    (w : TangentSpace (𝓡 (2 * n + 1)) p) :
    mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼)
        ((↑) : sphere (0 : 𝔼) 1 → 𝔼) (a • p)
        (mfderiv (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1))
          ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) p w)
      = ((a : ℂ) • ContinuousLinearMap.id ℝ 𝔼)
          (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼)
            ((↑) : sphere (0 : 𝔼) 1 → 𝔼) p w) := by
  set L : 𝔼 →L[ℝ] 𝔼 := (a : ℂ) • ContinuousLinearMap.id ℝ 𝔼 with hLdef
  have hφd : MDifferentiableAt (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1))
      ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) p :=
    (contMDiff_circle_smul_sphere a p).mdifferentiableAt (by simp)
  have hcoed : ∀ x : sphere (0 : 𝔼) 1,
      MDifferentiableAt (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) x :=
    fun x => (contMDiff_coe_sphere (E := 𝔼) (m := ∞) x).mdifferentiableAt (by simp)
  have hLd : MDifferentiableAt 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) (fun y : 𝔼 => (a : ℂ) • y) (p : 𝔼) :=
    (L.contMDiff (n := ∞)).mdifferentiableAt (by simp)
  -- chain rule on `ι ∘ (a • ·)`
  have h1 : mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼)
      (((↑) : sphere (0 : 𝔼) 1 → 𝔼) ∘ ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1)) p w
      = mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) (a • p)
          (mfderiv (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1))
            ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) p w) :=
    mfderiv_comp_apply p (hcoed (a • p)) hφd w
  -- chain rule on `((a : ℂ) • ·) ∘ ι`
  have h2 : mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼)
      ((fun y : 𝔼 => (a : ℂ) • y) ∘ ((↑) : sphere (0 : 𝔼) 1 → 𝔼)) p w
      = mfderiv 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) (fun y : 𝔼 => (a : ℂ) • y) (p : 𝔼)
          (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) p w) :=
    mfderiv_comp_apply p hLd (hcoed p) w
  -- the two composites agree
  have hcomm : (((↑) : sphere (0 : 𝔼) 1 → 𝔼) ∘
      ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1))
      = ((fun y : 𝔼 => (a : ℂ) • y) ∘ ((↑) : sphere (0 : 𝔼) 1 → 𝔼)) := rfl
  -- the ambient scalar multiplication is its own differential
  have hLm : mfderiv 𝓘(ℝ, 𝔼) 𝓘(ℝ, 𝔼) (fun y : 𝔼 => (a : ℂ) • y) (p : 𝔼) = L := by
    rw [mfderiv_eq_fderiv]
    exact L.fderiv
  rw [← h1, hcomm, h2, hLm]
  rfl

/-- **Math.** Petersen Example 1.3.4: the circle acts by **Riemannian
isometries** on `(S^{2n+1}, canonical metric)`: `a • ·` is a diffeomorphism
of the sphere (with smooth inverse `a⁻¹ • ·`), and it preserves the induced
metric because the ambient scalar multiplication by `a` is a real-linear
isometry of `ℂ^{n+1}`. -/
theorem isRiemannianIsometry_circle_smul_sphere (a : Circle) :
    IsRiemannianIsometry
      (sphereMetricUnit (n := 2 * n + 1) 𝔼)
      (sphereMetricUnit (n := 2 * n + 1) 𝔼)
      ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) := by
  refine ⟨⟨⟨⟨(a • ·), (a⁻¹ • ·), fun x => inv_smul_smul a x, fun x => smul_inv_smul a x⟩,
      contMDiff_circle_smul_sphere a, contMDiff_circle_smul_sphere a⁻¹⟩, rfl⟩, ?_⟩
  intro p u v
  show @inner ℝ 𝔼 _
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) p u)
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) p v)
    = @inner ℝ 𝔼 _
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) (a • p)
        (mfderiv (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1))
          ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) p u))
      (mfderiv (𝓡 (2 * n + 1)) 𝓘(ℝ, 𝔼) ((↑) : sphere (0 : 𝔼) 1 → 𝔼) (a • p)
        (mfderiv (𝓡 (2 * n + 1)) (𝓡 (2 * n + 1))
          ((a • ·) : sphere (0 : 𝔼) 1 → sphere (0 : 𝔼) 1) p v))
  rw [mfderiv_coe_circle_smul_sphere a p u, mfderiv_coe_circle_smul_sphere a p v]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [real_inner_circle_smul_smul]

/-- **Math.** Petersen Example 1.3.4 — **the Fubini–Study metric**.  The
circle `S¹ = {λ ∈ ℂ : |λ| = 1}` acts by isometric complex scalar
multiplication on the unit sphere `S^{2n+1} ⊆ ℂ^{n+1}`
(`isRiemannianIsometry_circle_smul_sphere`), with orbit space
`S^{2n+1}/S¹ = ℂPⁿ`; the unique metric on `ℂPⁿ` making
`S^{2n+1} → ℂPⁿ` a Riemannian submersion is the **Fubini–Study metric**.
For `n = 1` this is the Hopf fibration `S³(1) → ℂP¹ = S²(1/2)` (Petersen
Example 1.1.5, `PetersenLib.hopfMap`).

Mathlib's `Projectivization` has no smooth structure, so — exactly as in
`homogeneousQuotientMetric` — the complex projective space is represented
by hypotheses: a smooth manifold `P` together with a surjective smooth map
`q : S^{2n+1} → P` with surjective differentials whose fibres are the
`S¹`-orbits.  The isometry hypothesis of `homogeneousQuotientMetric` is
discharged by proof, so both existence and uniqueness of the Fubini–Study
metric are obtained outright. -/
theorem fubiniStudyMetric
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {H'' : Type*} [TopologicalSpace H''] {J : ModelWithCorners ℝ F H''}
    {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold J ∞ P]
    [J.Boundaryless]
    (q : sphere (0 : 𝔼) 1 → P)
    (hq_cont : ContMDiff (𝓡 (2 * n + 1)) J ∞ q)
    (hq_surj : Function.Surjective q)
    (hq_subm : ∀ p : sphere (0 : 𝔼) 1,
      Function.Surjective (mfderiv (𝓡 (2 * n + 1)) J q p))
    (hfib : ∀ p p' : sphere (0 : 𝔼) 1,
      q p = q p' ↔ ∃ a : Circle, a • p = p') :
    ∃! gFS : RiemannianMetric J P,
      IsRiemannianSubmersion (sphereMetricUnit (n := 2 * n + 1) 𝔼) gFS q :=
  homogeneousQuotientMetric (sphereMetricUnit (n := 2 * n + 1) 𝔼) q
    (fun a => isRiemannianIsometry_circle_smul_sphere a) hq_cont hq_surj hq_subm hfib

end FubiniStudy

end PetersenLib

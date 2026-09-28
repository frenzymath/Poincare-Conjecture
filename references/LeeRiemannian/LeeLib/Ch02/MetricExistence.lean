/-
Chapter 2, "Riemannian Metrics", §2 "Riemannian Metrics": existence.

Lee's Proposition 2.4 asserts that every smooth manifold admits a Riemannian
metric, and Exercise 2.5 asks for the proof: use a partition of unity.  The
argument is the standard one, and it is the reason Riemannian geometry is a
theory about *all* smooth manifolds rather than about a select few:

* on a chart domain, transport the Euclidean inner product of the model space
  `E` back through the tangent-bundle trivialization; this gives a local smooth
  symmetric positive definite `2`-tensor field;
* glue these local metrics with a smooth partition of unity subordinate to the
  cover by chart domains.

The only thing that has to be checked for the gluing is that the property
"symmetric and positive definite" is preserved by convex combinations — a
convex combination `a q₁ + b q₂` is symmetric, and positive definite as soon as
one of the weights is strictly positive.  That is exactly the hypothesis of
mathlib's `exists_contMDiffSection_forall_mem_convex_of_local`, which packages
the partition-of-unity gluing for sections of a vector bundle valued in a
family of convex sets; here the bundle is the bundle of bilinear forms on the
tangent bundle.

The hypotheses are Lee's standing conventions made explicit: `M` is Hausdorff
and σ-compact (Lee builds second countability and Hausdorffness into "smooth
manifold", and second countable + locally compact Hausdorff gives σ-compact),
and the model space is finite dimensional.  Note that no boundarylessness is
needed, matching Lee's remark that the statement and proof work verbatim for
manifolds with boundary.

Provenance: this construction is vendored from the shared DoCarmoLib development
(`DoCarmoLib/Riemannian/Manifold/DoCarmoCh1.lean`, do Carmo Ch. 1 Prop. 2.10),
where it was first developed; PetersenLib vendored the same block for Petersen
Exercise 1.6.26 (`PetersenLib/Ch01/ArcLength.lean`).  The three books share the
statement because all three alias mathlib's `Bundle.ContMDiffRiemannianMetric`.
It is copied rather than imported because the Lee project deliberately carries
no lakefile dependency on its sibling projects — the shared substrate is
mathlib itself at this pin, and cross-project `lake` builds are known to corrupt
each other's `.lake/build` (workspace issue I-0109).
-/
import LeeLib.Ch02.RiemannianMetric
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection

namespace LeeLib.Ch02

open Bornology Bundle Manifold
open scoped Manifold ContDiff Topology

section Existence

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Coercivity of a positive definite form** (Lee, §2.1): on a finite
dimensional space a positive definite quadratic form `q` is coercive, so the
sublevel set `{v | q v v < 1}` is von Neumann bounded.

Lee never states this separately — for him "positive definite" already means the
sublevel sets are bounded, because he works on `ℝⁿ` where the equivalence of all
inner product norms is taken for granted.  In Lean it is a real obligation: it is
the `isVonNBounded` field of `Bundle.ContMDiffRiemannianMetric`, which records
that the inner product induces the *given* topology on each fiber.  The proof is
Lee's implicit one: `v ↦ q v v` attains a positive minimum `c` on the unit
sphere, whence `c ‖v‖² ≤ q v v`. -/
theorem isVonNBounded_of_posDef {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (q : F →L[ℝ] F →L[ℝ] ℝ) (hpos : ∀ v : F, v ≠ 0 → 0 < q v v) :
    Bornology.IsVonNBounded ℝ {v : F | q v v < 1} := by
  rcases subsingleton_or_nontrivial F with hs | hn
  · exact Set.Finite.isVonNBounded (𝕜 := ℝ) (Set.toFinite _)
  have hcompact : IsCompact (Metric.sphere (0 : F) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : F) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : Continuous fun v : F => q v v := q.continuous.clm_apply continuous_id
  obtain ⟨v₀, hv₀mem, hv₀min⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  set c := q v₀ v₀ with hc_def
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [mem_sphere_iff_norm, sub_zero, h, norm_zero] at hv₀mem; norm_num at hv₀mem
  have hc : 0 < c := hpos v₀ hv₀ne
  have hcoer : ∀ v : F, c * ‖v‖ ^ 2 ≤ q v v := by
    intro v; rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have hnv : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      set u := ‖v‖⁻¹ • v with hu
      have hmem : u ∈ Metric.sphere (0 : F) 1 := by
        rw [mem_sphere_iff_norm, sub_zero, hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv]
      have hqu : c ≤ q u u := hv₀min hmem
      have hexp : q v v = ‖v‖ ^ 2 * q u u := by
        rw [hu]; simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; field_simp
      rw [hexp]; nlinarith [hqu, sq_nonneg ‖v‖]
  apply Bornology.IsVonNBounded.subset _ (NormedSpace.isVonNBounded_ball ℝ F (Real.sqrt (1 / c) + 1))
  intro v hv; simp only [Set.mem_setOf_eq] at hv; rw [Metric.mem_ball, dist_zero_right]
  have h1 : c * ‖v‖ ^ 2 < 1 := lt_of_le_of_lt (hcoer v) hv
  have h2 : ‖v‖ ^ 2 < 1 / c := by rw [lt_div_iff₀ hc]; linarith [mul_comm c (‖v‖^2)]
  have h3 : ‖v‖ < Real.sqrt (1 / c) := by
    rw [show ‖v‖ = Real.sqrt (‖v‖^2) by rw [Real.sqrt_sq (norm_nonneg _)]]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h2
  linarith [Real.sqrt_nonneg (1/c)]

omit [IsManifold I ∞ M] in
/-- **Inner products form a convex set** (Lee, Exercise 2.5): the set of
symmetric positive definite bilinear forms on a tangent space is convex, since a
convex combination `a q₁ + b q₂` (with `a, b ≥ 0` and `a + b = 1`) is again
symmetric, and is positive definite because at least one weight is strictly
positive.

This convexity is the whole content of the partition-of-unity argument: it is
what guarantees that averaging the local metrics against a partition of unity
leaves a metric rather than a merely symmetric tensor. -/
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
/-- **Every smooth manifold admits a Riemannian metric** (Lee, Proposition 2.4;
proof by partition of unity, Lee Exercise 2.5).

This is what makes Riemannian geometry a theory of all smooth manifolds: the
metric is never an obstruction, only a choice.  Contrast Lee's later remark that
*pseudo*-Riemannian metrics of a prescribed signature need not exist (a Lorentz
metric on a compact manifold forces Euler characteristic zero) — the proof below
breaks there precisely because indefinite forms of a fixed signature do not form
a convex set, so the partition-of-unity averaging is unavailable.

Construction: transport the Euclidean inner product of the model space `E` back
through the tangent-bundle trivialization over a chart to get a local smooth
symmetric positive definite section, then glue with a smooth partition of unity;
`convex_symm_posDef` keeps the glued form positive definite. -/
theorem exists_riemannianMetric : Nonempty (RiemannianMetric I M) := by
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
    -- A fixed symmetric positive definite form on the model space `E`, obtained by transporting
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
    -- `s_loc y` transports `B` back through the tangent trivialization's fibre equiv.
    set s_loc : (y : M) → V y := fun y =>
      if hy : y ∈ eT.baseSet then
        ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
          ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
            (ContinuousLinearEquiv.refl ℝ ℝ))) B
      else 0 with hsl
    have hsl_apply : ∀ (y : M) (hy : y ∈ eT.baseSet) (u v : TangentSpace I y),
        s_loc y u v
          = B (eT.continuousLinearEquivAt ℝ y hy u) (eT.continuousLinearEquivAt ℝ y hy v) := by
      intro y hy u v
      simp only [hsl, dif_pos hy]
      rfl
    refine ⟨eT.baseSet, eT.open_baseSet.mem_nhds hx₀, s_loc, ?_, ?_⟩
    · -- smoothness: reduce to the coordinate representation, which is the constant `B`
      have hbase : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) V x₀).baseSet = eT.baseSet := by
        have htriv0 :
            (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀) = Bundle.Trivial.trivialization M ℝ :=
          Bundle.Trivial.eq_trivialization M ℝ _
        simp only [hom_trivializationAt_baseSet, ← heT, htriv0, Bundle.Trivial.trivialization,
          Set.inter_univ, Set.inter_self]
      rw [← hbase, Bundle.Trivialization.contMDiffOn_section_baseSet_iff]
      refine (contMDiffOn_const (c := B)).congr ?_
      intro y hy
      rw [hbase] at hy
      refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      have hy₂ :
          y ∈ (trivializationAt (E →L[ℝ] ℝ) (fun x => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet := by
        rw [hom_trivializationAt_baseSet]; exact ⟨hy, Set.mem_univ y⟩
      rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt (E →L[ℝ] ℝ) (fun x => TangentSpace I x →L[ℝ] ℝ) x₀) hy₂]
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply, ← heT]
      have htriv :
          (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀) = Bundle.Trivial.trivialization M ℝ :=
        Bundle.Trivial.eq_trivialization M ℝ _
      simp only [htriv, Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_apply, hsl_apply y hy,
        ← Trivialization.symm_continuousLinearEquivAt_eq' eT hy,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    · -- symmetric and positive definite on the base set
      intro y hy
      refine ⟨fun u v => ?_, fun v hv => ?_⟩
      · rw [hsl_apply y hy, hsl_apply y hy]; exact hBsymm _ _
      · rw [hsl_apply y hy]
        exact hBpos _
          (fun h => hv ((eT.continuousLinearEquivAt ℝ y hy).injective (by rw [h, map_zero])))
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
      (I := I) (n := (⊤ : ℕ∞)) V t htconv hloc
  refine ⟨⟨fun b => s b, fun b v w => (hs b).1 v w, fun b v hv => (hs b).2 v hv, ?_,
    s.contMDiff⟩⟩
  intro b
  exact isVonNBounded_of_posDef (F := E) (s b) (fun v hv => (hs b).2 v hv)

/-- **Riemannian manifolds exist in abundance** (Lee, Proposition 2.4), stated as
an instance-free choice of metric on any smooth manifold satisfying Lee's
standing hypotheses. -/
noncomputable def someRiemannianMetric : RiemannianMetric I M :=
  (exists_riemannianMetric (I := I) (M := M)).some

end Existence

end LeeLib.Ch02

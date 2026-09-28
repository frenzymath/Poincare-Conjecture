/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Submanifolds": the normal
space of a pseudo-Riemannian submanifold and its local frames.

Lee's Corollary 2.73: the normal spaces of a pseudo-Riemannian submanifold
assemble into a smooth vector subbundle of the ambient tangent bundle along `M`,
"proved in the same way as Proposition 2.16".  The normal space `N_x M` is defined
through the ambient pseudo-metric, and the members of the adapted orthonormal frame
of Proposition 2.72 lying above the cut are shown to be a local frame for it; the
subbundle criterion `LeeLib.AppendixA.SubbundleCriterion` (Lee's Lemma A.34) then
applies.

The one addition to Proposition 2.16's argument is an auxiliary metric.  A.34 *as
formalized* departs from Lee: Lee proves it for a bare smooth vector bundle, whereas
the formalization assumes the ambient bundle is Riemannian
(`IsContMDiffRiemannianBundle`) and normalizes local frames by Gram-Schmidt.  A
pseudo-Riemannian ambient metric supplies no such structure — an indefinite form
induces no `InnerProductSpace` on the fibres — so Proposition 2.16's move of feeding
A.34 the ambient metric itself is unavailable.

The way through is that A.34 never asks its fibre metric to be related to the family
of subspaces it is handed: the metric only normalizes frames.  So an *arbitrary*
Riemannian metric on `M̃`, unrelated to `g̃`, is supplied as scaffolding, and one
always exists (`exists_riemannianMetric_ambient`) under Lee's standing convention
that manifolds are Hausdorff and second countable.  Generalizing A.34 to bare bundles
would remove the scaffolding, and nothing else here would change.

The normal space is *not* defined as an orthogonal complement `(T_xM)ᗮ` in the
mathlib sense, which would need the fibrewise inner product; it is defined directly
by orthogonality against `g̃`, exactly as in `LeeLib.Ch02.NormalBundle` and for the
same reason.
-/

import LeeLib.Ch02.PseudoAdaptedFrame
import LeeLib.Ch02.NormalBundle

namespace LeeLib.Ch02

open Bundle Module Submodule
open scoped Manifold ContDiff

/-! ### The normal space of a pseudo-Riemannian submanifold -/

section PseudoNormalSpace

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable {g' : PseudoRiemannianMetric I' M'} {f : C^∞⟮I, M; I', M'⟯} {x : M}

variable (g' f x) in
/-- **The normal space** `N_x M ⊆ T_{F x} M̃` of a pseudo-Riemannian submanifold: the vectors of
the ambient tangent space at `F x` that are `g̃`-orthogonal to every vector tangent to `M`.

Lee's definition is verbatim the Riemannian one (`LeeLib.Ch02.normalSpace`) with an indefinite
`g̃`; what changes is not the definition but what may be concluded from it.  In the Riemannian
case `T_xM ⊕ N_xM = T_{Fx}M̃` always; here that splitting holds precisely because the induced
metric is nondegenerate, which is the submanifold hypothesis. -/
def pseudoNormalSpace :
    Submodule ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) where
  carrier := {v | ∀ w ∈ tangentRange f x, g'.form (f x) v w = 0}
  add_mem' := by
    intro a b ha hb w hw
    have key : (g'.form (f x)) (a + b) = (g'.form (f x)) a + (g'.form (f x)) b :=
      (g'.form (f x)).map_add a b
    rw [key, ContinuousLinearMap.add_apply, ha w hw, hb w hw, add_zero]
  zero_mem' := by
    intro w _
    have key : (g'.form (f x))
        (0 : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) = 0 := map_zero _
    rw [key, ContinuousLinearMap.zero_apply]
  smul_mem' := by
    intro c a ha w hw
    have key : (g'.form (f x)) (c • a) = c • (g'.form (f x)) a :=
      (g'.form (f x)).map_smul c a
    rw [key, ContinuousLinearMap.smul_apply, ha w hw, smul_zero]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
@[simp]
theorem mem_pseudoNormalSpace {v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x} :
    v ∈ pseudoNormalSpace g' f x ↔ ∀ w ∈ tangentRange f x, g'.form (f x) v w = 0 :=
  Iff.rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- A vector `g̃`-orthogonal to every member of a set is orthogonal to its whole span. -/
theorem form_span_eq_zero (v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x)
    (S : Set (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x))
    (h : ∀ z ∈ S, g'.form (f x) v z = 0) :
    ∀ w ∈ span ℝ S, g'.form (f x) v w = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => exact (g'.form (f x) v).map_zero
  | add a b _ _ ha hb =>
      have key : (g'.form (f x) v) (a + b) = (g'.form (f x) v) a + (g'.form (f x) v) b :=
        (g'.form (f x) v).map_add a b
      rw [key, ha, hb, add_zero]
  | smul c a _ ha =>
      have key : (g'.form (f x) v) (c • a) = c • (g'.form (f x) v) a :=
        (g'.form (f x) v).map_smul c a
      rw [key, ha, smul_zero]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E'] in
/-- Bilinearity of `g̃` in its second argument over a finite sum, stated for vectors of the
*pullback* fibre.  See `LeeLib.Ch02.PullbackBundle` on the instance diamond that makes this
`have`-shaped rather than a `simp` call. -/
theorem form_sum_right {ι : Type*} [Fintype ι]
    (v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) (c : ι → ℝ)
    (Z : ι → ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) :
    g'.form (f x) v (∑ b, c b • Z b) = ∑ b, c b * g'.form (f x) v (Z b) := by
  have hsum : (g'.form (f x) v) (∑ b, c b • Z b) = ∑ b, (g'.form (f x) v) (c b • Z b) :=
    map_sum (g'.form (f x) v) _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsmul : (g'.form (f x) v) (c b • Z b) = c b • (g'.form (f x) v) (Z b) :=
    (g'.form (f x) v).map_smul (c b) (Z b)
  rw [hsmul, smul_eq_mul]

end PseudoNormalSpace

/-! ### Local frames for the normal space -/

section PseudoNormalFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Local frames for the normal space of a pseudo-Riemannian submanifold** — the frame half of
Lee's Corollary 2.73, and the hypothesis its proof hands to Lemma A.34.

If `F : M → M̃` presents `M` as a pseudo-Riemannian submanifold of `(M̃, g̃)`, every `p ∈ M` has a
neighbourhood `v` carrying `m - n` smooth sections of the ambient tangent bundle `F *ᵖ T M̃` that
are orthonormal — hence linearly independent — at each `x ∈ v` and span the normal space
`N_x M` there.

The sections are the members of the adapted orthonormal frame of Proposition 2.72 lying above
the cut.  That they are normal is immediate from orthonormality; that they span `N_xM` is the
substantive half, and is where nondegeneracy is used: a normal vector is expanded in the
adapted frame and its coefficients below the cut are shown to vanish, which needs each
`⟪b_a, b_a⟫` to be invertible — true in the indefinite case only because orthonormality gives
`±1` rather than a possible `0`. -/
theorem exists_pseudo_localFrame_normalSpace (g : PseudoRiemannianMetric I M)
    (g' : PseudoRiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (hg : IsPullbackAlong I I' g g' f) (p : M) :
    ∃ (v : Set M) (hn : finrank ℝ E ≤ finrank ℝ E')
      (N : Fin (finrank ℝ E' - finrank ℝ E) → (x : M) →
        ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x),
      IsOpen v ∧ p ∈ v ∧
      (∀ j, ContMDiffOn I (I.prod 𝓘(ℝ, E')) ∞ (fun x => TotalSpace.mk' E' x (N j x)) v) ∧
      (∀ x ∈ v, IsOrthonormal ((g'.pullback f).bilin x) fun j => N j x) ∧
      (∀ x ∈ v, ∀ j, N j x ∈ pseudoNormalSpace g' f x) ∧
      (∀ x ∈ v, span ℝ (Set.range fun j => N j x) = pseudoNormalSpace g' f x) := by
  classical
  obtain ⟨v, Y, hn, hvopen, hpv, hY, hYon, hYtan, hYspan⟩ :=
    exists_adapted_pseudo_orthonormalFrame g g' f hg p
  -- the pairing of the ambient metric along `M` is `g̃` at the image point, definitionally
  have hbilin : ∀ (x : M) (a b : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x),
      (g'.pullback f).bilin x a b = g'.form (f x) a b := fun _ _ _ => rfl
  set N : Fin (finrank ℝ E' - finrank ℝ E) → (x : M) →
      ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x :=
    fun j x => Y (finUpper hn j) x with hN
  -- each is normal: orthogonal to every member below the cut, hence to their span
  have hnormal : ∀ x ∈ v, ∀ j, N j x ∈ pseudoNormalSpace g' f x := by
    intro x hx j w hw
    rw [← hYspan x hx] at hw
    refine form_span_eq_zero (N j x) _ ?_ w hw
    rintro _ ⟨i, rfl⟩
    rw [hN, ← hbilin]
    exact (hYon x hx).1 (finUpper hn j) (Fin.castLE hn i) (castLE_ne_finUpper hn i j).symm
  refine ⟨v, hn, N, hvopen, hpv, fun j => hY.contMDiffOn _, ?_, hnormal, ?_⟩
  · -- orthonormality is inherited from the adapted frame along an injective reindexing
    exact fun x hx => (hYon x hx).comp _ (finUpper_injective hn)
  · intro x hx
    refine le_antisymm ?_ ?_
    · rw [span_le]
      rintro _ ⟨j, rfl⟩
      exact hnormal x hx j
    · -- expand a normal vector in the adapted frame, which is a basis of the fibre
      intro w hw
      have hbasis : ∀ a, (hY.toBasisAt hx) a = Y a x := fun a => hY.toBasisAt_coe hx a
      have hexp : ∑ a, (hY.toBasisAt hx).repr w a • Y a x = w := by
        conv_rhs => rw [← (hY.toBasisAt hx).sum_repr w]
        exact Finset.sum_congr rfl fun a _ => by rw [hbasis a]
      -- `⟪b_a, w⟫ = c_a ⟪b_a, b_a⟫`: the off-diagonal terms of the expansion drop out
      have hrepr : ∀ a, g'.form (f x) (Y a x) w
          = (hY.toBasisAt hx).repr w a * g'.form (f x) (Y a x) (Y a x) := by
        intro a
        have h1 : g'.form (f x) (Y a x) w
            = ∑ b, (hY.toBasisAt hx).repr w b * g'.form (f x) (Y a x) (Y b x) := by
          conv_lhs => rw [← hexp]
          exact form_sum_right _ _ _
        rw [h1, Finset.sum_eq_single a]
        · intro b _ hb
          rw [← hbilin, (hYon x hx).1 a b (Ne.symm hb), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ a) h
      -- below the cut the frame is tangent, so a normal `w` pairs to zero and the
      -- coefficient must vanish — here `⟪b_a, b_a⟫ = ±1 ≠ 0` is what makes the division legal
      have hlow : ∀ i : Fin (finrank ℝ E), (hY.toBasisAt hx).repr w (Fin.castLE hn i) = 0 := by
        intro i
        have hself : g'.form (f x) (Y (Fin.castLE hn i) x) (Y (Fin.castLE hn i) x) ≠ 0 := by
          rw [← hbilin]
          exact (hYon x hx).apply_self_ne_zero _
        have hzero : g'.form (f x) (Y (Fin.castLE hn i) x) w = 0 := by
          rw [g'.symm (f x)]
          exact hw _ (hYtan x hx i)
        rw [hrepr] at hzero
        exact (mul_eq_zero.mp hzero).resolve_right hself
      rw [← hexp]
      refine Submodule.sum_mem _ fun a _ => ?_
      by_cases ha : a.val < finrank ℝ E
      · have hcast : a = Fin.castLE hn ⟨a.val, ha⟩ := Fin.ext rfl
        rw [hcast, hlow, zero_smul]
        exact Submodule.zero_mem _
      · obtain ⟨j, rfl⟩ := exists_finUpper hn a (by omega)
        exact Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

end PseudoNormalFrame

/-! ### Lee's Corollary 2.73: the normal bundle -/

section PseudoNormalBundle

open LeeLib.AppendixA

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **The hypothesis of Lemma A.34 holds for the normal spaces of a pseudo-Riemannian
submanifold.**

The auxiliary Riemannian metric `h` is the point of this statement.  Lemma A.34 as formalized
builds the subbundle's trivializations out of *orthonormal* local frames, so it needs a
Riemannian fibre metric on the ambient bundle — and the ambient pseudo-metric `g̃` is not one.
But A.34 never asks that the fibre metric be related to the family `D` of subspaces it is
handed: any Riemannian metric on the ambient bundle will normalize the frames.  So `h` is taken
to be an arbitrary Riemannian metric on `M̃`, unrelated to `g̃`, and used only as scaffolding;
`exists_riemannianMetric_ambient` records that one always exists.

The normal spaces themselves, and the frames spanning them, remain defined by `g̃` alone. -/
theorem hasLocalSubframes_pseudoNormalSpace (g : PseudoRiemannianMetric I M)
    (g' : PseudoRiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (hg : IsPullbackAlong I I' g g' f) (h : RiemannianMetric I' M') :
    letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
      ⟨(h.pullback f).toRiemannianMetric⟩
    HasLocalSubframes I E' ∞ (finrank ℝ E' - finrank ℝ E) (pseudoNormalSpace g' f) := by
  letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
    ⟨(h.pullback f).toRiemannianMetric⟩
  refine ⟨fun p => ?_⟩
  obtain ⟨v, -, N, hvopen, hpv, hNsmooth, hNon, -, hNspan⟩ :=
    exists_pseudo_localFrame_normalSpace g g' f hg p
  refine ⟨v, N, hvopen, hpv, ?_⟩
  -- linear independence is read off the indefinite orthonormality of the frame, with no
  -- reference to `h`: an orthonormal tuple for *any* nondegenerate form is independent
  exact { toIsLocalIndepOn := ⟨fun {x} hx => (hNon x hx).linearIndependent, hNsmooth⟩
          span_eq := fun {x} hx => hNspan x hx }

/-- **Lee's Corollary 2.73.**  If `F : M → M̃` presents `M` as a pseudo-Riemannian submanifold of
a pseudo-Riemannian `m`-manifold `(M̃, g̃)`, then the normal bundle `NM = ⨆_x N_x M` is a smooth
rank-`(m - n)` vector subbundle of the ambient tangent bundle `T M̃|_M = F *ᵖ T M̃`.

Lee says this "is proved in the same way as Proposition 2.16", and it is, with one addition.
Proposition 2.16 feeds Lemma A.34 the ambient metric itself, which is there Riemannian; here the
ambient metric is indefinite and A.34 cannot consume it, so an auxiliary Riemannian metric `h`
on `M̃` is supplied as scaffolding instead (see `hasLocalSubframes_pseudoNormalSpace`).  The
resulting smooth structure is the one A.34 builds from `h`-orthonormal frames.

As in the Riemannian case the conclusion is the bundle structure itself rather than a
`subbundle` predicate, mathlib having no notion of a smooth vector subbundle. -/
theorem contMDiffVectorBundle_pseudoNormalSpace (g : PseudoRiemannianMetric I M)
    (g' : PseudoRiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (hg : IsPullbackAlong I I' g g' f) (h : RiemannianMetric I' M') :
    letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
      ⟨(h.pullback f).toRiemannianMetric⟩
    letI hs := hasLocalSubframes_pseudoNormalSpace g g' f hg h
    letI := subTotalSpaceTopology hs
    letI := subFiberBundle hs
    letI := subVectorBundle hs
    ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (finrank ℝ E' - finrank ℝ E)))
      (fun x => ↥(pseudoNormalSpace g' f x)) I := by
  letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
    ⟨(h.pullback f).toRiemannianMetric⟩
  exact subContMDiffVectorBundle (F := E') (hasLocalSubframes_pseudoNormalSpace g g' f hg h)

/-- The scaffolding of Corollary 2.73 is always available: every smooth manifold admits a
Riemannian metric, so the auxiliary `h` of `contMDiffVectorBundle_pseudoNormalSpace` costs
nothing beyond Lee's standing convention that manifolds are Hausdorff and second countable.

This is the sense in which the normal bundle of a pseudo-Riemannian submanifold exists
unconditionally, as Lee asserts: the choice of `h` affects the construction, not the conclusion's
availability. -/
theorem exists_riemannianMetric_ambient [T2Space M'] [SigmaCompactSpace M'] :
    Nonempty (RiemannianMetric I' M') :=
  exists_riemannianMetric

end PseudoNormalBundle

end LeeLib.Ch02

/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": the normal space along a submanifold, and its local orthonormal
frames.

Lee's Proposition 2.16 asserts two things about `NM`, the union of the normal
spaces `N_p M = (T_p M)^⊥ ⊆ T_p M̃` along a submanifold `M ⊆ M̃`:

1. every point of `M` has a neighbourhood carrying a smooth local orthonormal
   frame for `NM` — the last `m - n` members of an adapted orthonormal frame;
2. therefore, by Lemma A.34 (the local frame criterion for subbundles), `NM` is
   a smooth rank-`(m - n)` subbundle of `T M̃|_M`, and the tangential and normal
   projections are smooth bundle maps.

This file establishes (1), which is exactly the hypothesis Lemma A.34 consumes.
Statement (2) additionally needs A.34 itself — the construction of a vector
bundle structure on a family of subspaces — and mathlib has no notion of a
smooth vector subbundle, so `prop:normal-bundle` remains open.

As everywhere in this chapter a submanifold is presented by a smooth immersion
`F : M → M̃`, and the ambient tangent bundle along `M` is the pullback
`F *ᵖ T M̃`.  Lee's `T_p M ⊆ T_p M̃` is `tangentRange F x = range (dF_x)` and his
`N_p M` is `normalSpace g' F x`.

`normalSpace` is defined by the vanishing condition `⟪v, w⟫ = 0` for every
`w ∈ tangentRange F x`, spelled out through `g̃` itself rather than as
`(tangentRange F x)ᗮ`.  Both say the same thing, but `ᗮ` would force the
statement to mention the `RiemannianBundle` instance that installs the fibrewise
inner product, whereas the `g̃`-form needs no instance at all — the same choice
`exists_adapted_orthonormalFrame` makes for orthonormality, and for the same
reason.

The frame is read off Proposition 2.14: run it to get an adapted orthonormal
frame `(E_1, …, E_m)` whose first `n` members span `T_x M`, and keep the last
`m - n`.  That these lie in `N_x M` is orthonormality — each is orthogonal to
every `E_i` with `i ≤ n`, hence to their span, which is `T_x M`.  That they
*span* `N_x M` is the converse and is where the frame being a *basis* is used:
expanding a normal vector `w` in the basis `(E_a)_a`, the coefficient of `E_a`
is `⟪w, E_a⟫` by orthonormality, and this vanishes for `a ≤ n` precisely because
`w` is normal, so only the last `m - n` terms survive.  Neither a dimension
count nor any orthogonal-complement API is needed.

A note on instances.  The fibre of the pullback carries two definitionally equal
but syntactically distinct `AddCommMonoid`/`Module` structures (the pullback's
own and the tangent space's), so `rw`/`simp` cannot match `map_add`, `map_smul`
or `map_sum` against a goal stated in the pullback fibre: the `+` in the goal is
not the `+` the lemma expects.  Every use of bilinearity below therefore states
the instance of linearity as an explicitly *type-ascribed* `have`, which forces
elaboration in the goal's instance context and lets `rw` fire.  `innerAt_span_eq_zero`
and `innerAt_sum_right` package the two places this is needed so the pattern
appears once each.  This is the same diamond recorded in I-0253/I-0254.
-/
import LeeLib.AppendixA.SubbundleCriterion
import LeeLib.Ch02.AdaptedFrame

namespace LeeLib.Ch02

open Bundle InnerProductSpace Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace Topology

section NormalSpace

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable {g' : RiemannianMetric I' M'} {f : C^∞⟮I, M; I', M'⟯} {x : M}

/-- Bilinearity of `g̃` in its second argument over a finite sum, stated so that it applies to
vectors of the *pullback* fibre.  See the file header on the instance diamond. -/
theorem innerAt_sum_right {ι : Type*} [Fintype ι]
    (v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) (c : ι → ℝ)
    (Z : ι → ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) :
    g'.inner (f x) v (∑ b, c b • Z b) = ∑ b, c b * g'.inner (f x) v (Z b) := by
  have hsum : (g'.inner (f x) v) (∑ b, c b • Z b) = ∑ b, (g'.inner (f x) v) (c b • Z b) :=
    map_sum (g'.inner (f x) v) _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hsmul : (g'.inner (f x) v) (c b • Z b) = c b • (g'.inner (f x) v) (Z b) :=
    (g'.inner (f x) v).map_smul (c b) (Z b)
  rw [hsmul, smul_eq_mul]

/-- A vector orthogonal to every member of a set is orthogonal to its whole span. -/
theorem innerAt_span_eq_zero (v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x)
    (S : Set (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x))
    (h : ∀ z ∈ S, g'.inner (f x) v z = 0) :
    ∀ w ∈ span ℝ S, g'.inner (f x) v w = 0 := by
  intro w hw
  induction hw using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => exact (g'.inner (f x) v).map_zero
  | add a b _ _ ha hb =>
      have key : (g'.inner (f x) v) (a + b) = (g'.inner (f x) v) a + (g'.inner (f x) v) b :=
        (g'.inner (f x) v).map_add a b
      rw [key, ha, hb, add_zero]
  | smul c a _ ha =>
      have key : (g'.inner (f x) v) (c • a) = c • (g'.inner (f x) v) a :=
        (g'.inner (f x) v).map_smul c a
      rw [key, ha, smul_zero]

variable (g' f x) in
/-- **Lee's normal space** `N_x M ⊆ T_{F x} M̃`: the vectors of the ambient tangent space at
`F x` that are `g̃`-orthogonal to every vector tangent to `M`.

Stated through `g̃` rather than as `(tangentRange f x)ᗮ` so that it does not depend on the
`RiemannianBundle` instance installing the fibrewise inner product. -/
noncomputable def normalSpace :
    Submodule ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) where
  carrier := {v | ∀ w ∈ tangentRange f x, g'.inner (f x) v w = 0}
  add_mem' := by
    intro a b ha hb w hw
    have key : (g'.inner (f x)) (a + b) = (g'.inner (f x)) a + (g'.inner (f x)) b :=
      (g'.inner (f x)).map_add a b
    rw [key, ContinuousLinearMap.add_apply, ha w hw, hb w hw, add_zero]
  zero_mem' := by
    intro w _
    have key : (g'.inner (f x))
        (0 : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) = 0 := map_zero _
    rw [key, ContinuousLinearMap.zero_apply]
  smul_mem' := by
    intro c a ha w hw
    have key : (g'.inner (f x)) (c • a) = c • (g'.inner (f x)) a :=
      (g'.inner (f x)).map_smul c a
    rw [key, ContinuousLinearMap.smul_apply, ha w hw, smul_zero]

@[simp]
theorem mem_normalSpace {v : ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x} :
    v ∈ normalSpace g' f x ↔ ∀ w ∈ tangentRange f x, g'.inner (f x) v w = 0 :=
  Iff.rfl

end NormalSpace

/-! ### Splitting `Fin m` at `n` -/

section FinSplit

/-- The index of the `j`-th slot above the cut, when `Fin n` sits inside `Fin m` as the first
`n` slots via `Fin.castLE`. -/
def finUpper {n m : ℕ} (hn : n ≤ m) (j : Fin (m - n)) : Fin m :=
  ⟨n + j.val, by omega⟩

@[simp]
theorem finUpper_val {n m : ℕ} (hn : n ≤ m) (j : Fin (m - n)) :
    (finUpper hn j).val = n + j.val := rfl

theorem castLE_ne_finUpper {n m : ℕ} (hn : n ≤ m) (i : Fin n) (j : Fin (m - n)) :
    Fin.castLE hn i ≠ finUpper hn j := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.coe_castLE, finUpper_val] at hv
  omega

theorem finUpper_injective {n m : ℕ} (hn : n ≤ m) : Function.Injective (finUpper hn) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [finUpper_val] at hv
  exact Fin.ext (by omega)

/-- Every index at or above the cut is `finUpper` of something. -/
theorem exists_finUpper {n m : ℕ} (hn : n ≤ m) (a : Fin m) (ha : n ≤ a.val) :
    ∃ j : Fin (m - n), finUpper hn j = a := by
  refine ⟨⟨a.val - n, by omega⟩, ?_⟩
  exact Fin.ext (by simp only [finUpper_val]; omega)

end FinSplit

/-! ### Lee's Proposition 2.16, frame half: local orthonormal frames for the normal space -/

section NormalFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Existence of local orthonormal frames for the normal space** — the frame half of Lee's
Proposition 2.16.

If `F : M → M̃` is a smooth immersion into a Riemannian manifold `(M̃, g̃)`, every `p ∈ M` has a
neighbourhood `v` carrying `m - n` smooth sections of the ambient tangent bundle `F *ᵖ T M̃`
whose values at each `x ∈ v` form an orthonormal basis of the normal space `N_x M`.

This is exactly the hypothesis that Lemma A.34 (the local frame criterion for subbundles)
consumes in order to conclude that `NM` is a smooth rank-`(m - n)` subbundle.  A.34 itself is
not yet formalized, so Proposition 2.16 is not yet closed. -/
theorem exists_orthonormalFrame_normalSpace (g' : RiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ x : M, Function.Injective (mfderiv I I' f x)) (p : M) :
    ∃ (v : Set M) (hn : finrank ℝ E ≤ finrank ℝ E')
      (N : Fin (finrank ℝ E' - finrank ℝ E) → (x : M) →
        ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x),
      IsOpen v ∧ p ∈ v ∧
      (∀ j, ContMDiffOn I (I.prod 𝓘(ℝ, E')) ∞ (fun x => TotalSpace.mk' E' x (N j x)) v) ∧
      (∀ x ∈ v, ∀ i j, g'.inner (f x) (N i x) (N j x) = if i = j then 1 else 0) ∧
      (∀ x ∈ v, ∀ j, N j x ∈ normalSpace g' f x) ∧
      (∀ x ∈ v, span ℝ (Set.range fun j => N j x) = normalSpace g' f x) := by
  classical
  obtain ⟨v, Y, hn, hvopen, hpv, hY, hYon, hYtan, hYspan⟩ :=
    exists_adapted_orthonormalFrame g' f himm p
  -- the last `m - n` members of the adapted frame
  set N : Fin (finrank ℝ E' - finrank ℝ E) → (x : M) →
      ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x :=
    fun j x => Y (finUpper hn j) x with hN
  -- each of them is normal: it is orthogonal to every member below the cut, hence to their span
  have hnormal : ∀ x ∈ v, ∀ j, N j x ∈ normalSpace g' f x := by
    intro x hx j w hw
    rw [← hYspan x hx] at hw
    refine innerAt_span_eq_zero (N j x) _ ?_ w hw
    rintro _ ⟨i, rfl⟩
    rw [hN, hYon x hx (finUpper hn j) (Fin.castLE hn i),
      if_neg (castLE_ne_finUpper hn i j).symm]
  refine ⟨v, hn, N, hvopen, hpv, fun j => hY.contMDiffOn _, ?_, hnormal, ?_⟩
  · -- orthonormality is inherited from the adapted frame
    intro x hx i j
    rw [hN, hYon x hx (finUpper hn i) (finUpper hn j)]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij (finUpper_injective hn h))]
  · -- they span the normal space
    intro x hx
    refine le_antisymm ?_ ?_
    · rw [span_le]
      rintro _ ⟨j, rfl⟩
      exact hnormal x hx j
    · -- expand a normal vector in the orthonormal basis `(Y a x)`
      intro w hw
      have hbasis : ∀ a, (hY.toBasisAt hx) a = Y a x := fun a => hY.toBasisAt_coe hx a
      have hexp : ∑ a, (hY.toBasisAt hx).repr w a • Y a x = w := by
        conv_rhs => rw [← (hY.toBasisAt hx).sum_repr w]
        exact Finset.sum_congr rfl fun a _ => by rw [hbasis a]
      -- the coefficient of `Y a x` is `⟪Y a x, w⟫`, by orthonormality
      have hrepr : ∀ a, g'.inner (f x) (Y a x) w = (hY.toBasisAt hx).repr w a := by
        intro a
        have h1 : g'.inner (f x) (Y a x) w
            = ∑ b, (hY.toBasisAt hx).repr w b * g'.inner (f x) (Y a x) (Y b x) := by
          conv_lhs => rw [← hexp]
          exact innerAt_sum_right _ _ _
        rw [h1, Finset.sum_eq_single a]
        · rw [hYon x hx a a, if_pos rfl, mul_one]
        · intro b _ hb
          rw [hYon x hx a b, if_neg (Ne.symm hb), mul_zero]
        · intro h
          exact absurd (Finset.mem_univ a) h
      -- the coefficients below the cut vanish, because `w` is normal
      have hlow : ∀ i : Fin (finrank ℝ E), (hY.toBasisAt hx).repr w (Fin.castLE hn i) = 0 := by
        intro i
        rw [← hrepr, ← g'.symm (f x)]
        exact hw _ (hYtan x hx i)
      -- so only the upper members survive in the expansion
      rw [← hexp]
      refine Submodule.sum_mem _ fun a _ => ?_
      by_cases ha : a.val < finrank ℝ E
      · have hcast : a = Fin.castLE hn ⟨a.val, ha⟩ := Fin.ext rfl
        rw [hcast, hlow, zero_smul]
        exact Submodule.zero_mem _
      · obtain ⟨j, rfl⟩ := exists_finUpper hn a (by omega)
        exact Submodule.smul_mem _ _ (subset_span ⟨j, rfl⟩)

end NormalFrame

/-! ### Lee's Proposition 2.16: the normal bundle

The frame half above is exactly the hypothesis of Lemma A.34, so the subbundle half is now a
matter of handing it over.  The only work is translating between the two idioms for
orthonormality: `exists_orthonormalFrame_normalSpace` states it through `g̃` itself (so that
using it needs no instance), whereas `IsOrthonormalSubframeOn` states it as `Orthonormal` for
the fibrewise inner product installed by the `RiemannianBundle` instance.  The two agree
definitionally — `⟪·,·⟫` on the fibre of `f *ᵖ T M̃` unfolds to `g̃.inner (f x)`. -/

section NormalBundle

open LeeLib.AppendixA

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **The hypothesis of Lemma A.34 holds for the normal spaces.**

This is Proposition 2.16's frame half (`exists_orthonormalFrame_normalSpace`) repackaged: the
last `m - n` members of an adapted orthonormal frame are `m - n` smooth sections of the ambient
tangent bundle forming an orthonormal — in particular linearly independent — basis of `N_x M` at
every point of a neighbourhood. -/
theorem hasLocalSubframes_normalSpace (g' : RiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ x : M, Function.Injective (mfderiv I I' f x)) :
    letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
      ⟨(g'.pullback f).toRiemannianMetric⟩
    HasLocalSubframes I E' ∞ (finrank ℝ E' - finrank ℝ E) (normalSpace g' f) := by
  letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
    ⟨(g'.pullback f).toRiemannianMetric⟩
  refine ⟨fun p => ?_⟩
  obtain ⟨v, hn, N, hvopen, hpv, hNsmooth, hNon, _hNmem, hNspan⟩ :=
    exists_orthonormalFrame_normalSpace g' f himm p
  refine ⟨v, N, hvopen, hpv, ?_⟩
  refine { toIsLocalIndepOn := ⟨fun {x} hx => ?_, hNsmooth⟩, span_eq := fun {x} hx => hNspan x hx }
  -- `g̃`-orthonormality *is* orthonormality for the fibrewise inner product, by `rfl`
  have hbridge : ∀ i j, ⟪N i x, N j x⟫_ℝ = if i = j then (1 : ℝ) else 0 := hNon x hx
  refine Orthonormal.linearIndependent ⟨fun i => ?_, fun {i j} hij => ?_⟩
  · have h1 : ‖N i x‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simpa using hbridge i i
    nlinarith [norm_nonneg (N i x)]
  · simpa [hij] using hbridge i j

/-- **Lee's Proposition 2.16.**  If `F : M → M̃` presents an `n`-manifold as an immersed
submanifold of a Riemannian `m`-manifold `(M̃, g̃)`, then the normal bundle
`NM = ⨆_{x} N_x M` is a smooth rank-`(m - n)` vector subbundle of the ambient tangent bundle
`T M̃|_M = F *ᵖ T M̃`.

The conclusion is the bundle structure itself rather than a `subbundle` predicate, because
mathlib has no notion of a smooth vector subbundle; see `LeeLib.AppendixA.SubbundleCriterion`.
The topology, `FiberBundle` and `VectorBundle` structures on `NM` are
`subTotalSpaceTopology`, `subFiberBundle`, `subVectorBundle` applied to
`hasLocalSubframes_normalSpace`; this is the remaining smoothness statement about them.

That the rank is `m - n` is visible in the model fibre `EuclideanSpace ℝ (Fin (m - n))`.  The
tangential and normal projections `π^⊤`, `π^⊥` of Lee's statement are not part of this theorem;
they are the orthogonal projections of the fibrewise splitting `T_x M̃ = T_x M ⊕ N_x M` and
remain to be built. -/
theorem contMDiffVectorBundle_normalSpace (g' : RiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ x : M, Function.Injective (mfderiv I I' f x)) :
    letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
      ⟨(g'.pullback f).toRiemannianMetric⟩
    letI h := hasLocalSubframes_normalSpace g' f himm
    letI := subTotalSpaceTopology h
    letI := subFiberBundle h
    letI := subVectorBundle h
    ContMDiffVectorBundle ∞ (EuclideanSpace ℝ (Fin (finrank ℝ E' - finrank ℝ E)))
      (fun x => ↥(normalSpace g' f x)) I := by
  letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
    ⟨(g'.pullback f).toRiemannianMetric⟩
  exact subContMDiffVectorBundle (F := E') (hasLocalSubframes_normalSpace g' f himm)

end NormalBundle

end LeeLib.Ch02

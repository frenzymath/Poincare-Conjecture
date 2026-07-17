/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Submanifolds": adapted
orthonormal frames along a pseudo-Riemannian submanifold.

Lee's Proposition 2.72: if `M` sits inside a pseudo-Riemannian manifold `(M̃, g̃)` as a
*pseudo-Riemannian submanifold* — meaning the induced tensor `ι^* g̃` is again nondegenerate —
then every point of `M` has a neighbourhood carrying a smooth orthonormal frame for the ambient
tangent bundle whose first `dim M` members span `T M`.

The shape of the statement.  The submanifold hypothesis is carried by a *second* metric
`g : PseudoRiemannianMetric I M` together with `hg : g = f^* g̃` (`IsPullbackAlong`), rather
than by a predicate asserting that `f^* g̃` is nondegenerate.  The two say the same thing —
`PseudoRiemannianMetric` is by
definition a nondegenerate symmetric form field — but the present shape is the one a caller can
discharge: nondegeneracy of a pullback is not something one checks, it is something one
*constructs*, and whoever constructs it holds the resulting metric.  Lee's own examples supply
`g` this way (a Riemannian submanifold via `pullbackMetric`, a level set via Corollary 2.71).

That hypothesis is genuinely needed and is not implied by `f` being an immersion: the diagonal
in `ℝ^{1,1}` is an embedded line on which `ι^* g̃` vanishes identically.  Conversely it *implies*
`f` is an immersion (`injective_mfderiv_of_isPullbackAlong`), so no separate immersion
hypothesis appears.

The route.  The Riemannian case (`exists_adapted_orthonormalFrame`, Lee 2.14) pushes a chart
frame of `TM` forward into the ambient fibres, extends it to a frame, and orthonormalizes.
Any frame will do there, because Gram-Schmidt accepts any linearly independent input.

Indefinitely it will not: Gram-Schmidt's denominators are the leading Gram minors, so the input
must be a *nondegenerate tuple*, and a pushed-forward chart frame need not be one — a chart
frame of a Lorentz manifold can consist entirely of null vectors.  This is why the submanifold
metric `g` enters the proof and not just the statement: the tangential half of the frame is
taken to be an orthonormal frame *of `(M, g)`* (Proposition 2.66), which pushes forward to an
orthonormal — hence nondegenerate — tuple in the ambient fibres precisely because `g = f^* g̃`.
The rest is Lee's argument verbatim: complete at the point (Lemma 2.62), spread to sections,
propagate nondegeneracy to a neighbourhood, and run the indefinite Gram-Schmidt.
-/

import LeeLib.Ch02.AdaptedFrame
import LeeLib.Ch02.PseudoOrthonormalFrame

namespace LeeLib.Ch02

open Bundle Module Submodule
open scoped Manifold ContDiff

/-! ### Extending a nondegenerate family of sections to a nondegenerate frame -/

section Extend

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [IsManifold IB ∞ B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V IB]

omit [IsManifold IB ∞ B] in
/-- **A nondegenerate family of sections extends to a nondegenerate frame near a point**
— the indefinite counterpart of `exists_isLocalFrameOn_extend`, and the tool Lee's
Proposition 2.72 needs where Proposition 2.14 needed that one.

The difference from the Riemannian case is where the extension vectors come from.  There, any
completion of `X|_{x₀}` to a basis of the fibre serves, because linear independence is all
Gram-Schmidt asks and it is preserved by continuity.  Here the enlarged tuple must be
*nondegenerate*, and an arbitrary basis completion is not: adding a null vector orthogonal to
everything already chosen destroys the property.  So the completion is made by Lee's Lemma 2.62
(`exists_isNondegenerateTuple_basis`), which is exactly the statement that a nondegenerate tuple
can be extended *staying* nondegenerate.

The extension vectors are then spread to sections through `exists_contMDiffOn_section_eq_basis`,
which prescribes their values at `x₀` only; nondegeneracy therefore holds at `x₀` alone, and
`exists_isLocalNondegenerateOn_nhds` propagates it to a neighbourhood.  That shrinking is why
the conclusion is local even though the hypothesis holds on all of `u`. -/
theorem exists_isLocalNondegenerateOn_extend (g : Bundle.ContMDiffPseudoMetric IB ∞ F V)
    {k : ℕ} {X : Fin k → (x : B) → V x} {u : Set B} {x₀ : B}
    (hX : IsLocalNondegenerateOn IB F ∞ g X u) (hu : IsOpen u) (hx₀ : x₀ ∈ u) :
    ∃ (v : Set B) (Y : Fin (finrank ℝ F) → (x : B) → V x) (hk : k ≤ finrank ℝ F),
      IsOpen v ∧ x₀ ∈ v ∧ v ⊆ u ∧ IsLocalNondegenerateOn IB F ∞ g Y v ∧
        ∀ (i : Fin k) (x : B), x ∈ v → Y (Fin.castLE hk i) x = X i x := by
  classical
  haveI : ∀ x : B, FiniteDimensional ℝ (V x) := fun x => finiteDimensional_fibre (F := F) x
  have hrank : finrank ℝ (V x₀) = finrank ℝ F := finrank_fibre (F := F) (V := V) x₀
  -- the family at `x₀` is a nondegenerate tuple, hence independent, hence not too long
  have h0 : IsNondegenerateTuple (g.bilin x₀) (fun i => X i x₀) := hX.nondegenerateTuple hx₀
  have hk : k ≤ finrank ℝ F := by
    simpa [hrank] using h0.linearIndependent.fintype_card_le_finrank
  -- complete it to a nondegenerate basis of the fibre (Lee's Lemma 2.62)
  obtain ⟨w, hw, hwX⟩ :=
    exists_isNondegenerateTuple_basis (g.bilin_isSymm x₀) (g.bilin_nondegenerate x₀)
      (fun i => X i x₀) h0 (by omega)
  -- transport the index type across `finrank ℝ (V x₀) = finrank ℝ F`
  set w' : Fin (finrank ℝ F) → V x₀ := fun j => w (Fin.cast hrank.symm j) with hw'def
  have hw' : IsNondegenerateTuple (g.bilin x₀) w' := by
    have hdet := (isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero (g.bilin x₀) w).mp hw
    refine (isNondegenerateTuple_iff_forall_det_gramMatrix_ne_zero (g.bilin x₀) w').mpr ?_
    intro j hj
    have hj' : j ≤ finrank ℝ (V x₀) := by omega
    have hcomp : (w' ∘ Fin.castLE hj) = w ∘ Fin.castLE hj' := by
      funext i; simp [hw'def]
    rw [hcomp]
    exact hdet j hj'
  -- spread the completion to smooth sections near `x₀`
  obtain ⟨v₁, W, hv₁open, hx₀v₁, hWsmooth, hWeq⟩ :=
    LeeLib.AppendixA.exists_contMDiffOn_section_eq_basis (F := F) (V := V) IB ∞ x₀
      (hw'.basis hrank.symm)
  have hWval : ∀ j, W j x₀ = w' j := fun j => by rw [hWeq j]; simp
  -- glue: keep `X` below the cut, take the spread completion above it
  set Y : Fin (finrank ℝ F) → (x : B) → V x :=
    fun j x => if h : (j : ℕ) < k then X ⟨(j : ℕ), h⟩ x else W j x with hYdef
  have hYX : ∀ (i : Fin k) (x : B), Y (Fin.castLE hk i) x = X i x := by
    intro i x
    simp only [hYdef, Fin.val_castLE, dif_pos i.isLt, Fin.eta]
  -- at `x₀` the glued family *is* the nondegenerate basis `w'`
  have hYx₀ : (fun j => Y j x₀) = w' := by
    funext j
    by_cases h : (j : ℕ) < k
    · have hval : w' j = X ⟨(j : ℕ), h⟩ x₀ := by
        rw [hw'def, ← hwX ⟨(j : ℕ), h⟩]
        congr 1
      simp only [hYdef, dif_pos h, hval]
    · simp only [hYdef, dif_neg h, hWval j]
  have hYnd : IsNondegenerateTuple (g.bilin x₀) (fun j => Y j x₀) := by rw [hYx₀]; exact hw'
  -- smooth on the intersection, where both halves are defined
  have hYsmooth : ∀ j, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) ∞ (T% (Y j)) (u ∩ v₁) := by
    intro j
    by_cases h : (j : ℕ) < k
    · exact ((hX.contMDiffOn ⟨(j : ℕ), h⟩).mono Set.inter_subset_left).congr
        fun x _ => by simp only [hYdef, dif_pos h]
    · exact ((hWsmooth j).mono Set.inter_subset_right).congr
        fun x _ => by simp only [hYdef, dif_neg h]
  -- nondegeneracy at `x₀` propagates to a neighbourhood
  obtain ⟨v, hvopen, hx₀v, hvsub, hnd⟩ :=
    exists_isLocalNondegenerateOn_nhds g (hu.inter hv₁open) hYsmooth ⟨hx₀, hx₀v₁⟩ hYnd
  exact ⟨v, Y, hk, hvopen, hx₀v, fun x hx => (hvsub hx).1, hnd, fun i x _ => hYX i x⟩

end Extend

/-! ### Lee's Proposition 2.72 -/

section Adapted

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable (I I') in
/-- **`g` is the tensor induced on `M` by `g̃` along `f`** — Lee's `g = ι^* g̃`.

Read with `g` a `PseudoRiemannianMetric`, this is Lee's definition of a *pseudo-Riemannian
submanifold*: the pullback tensor is nondegenerate, that nondegeneracy being carried by `g`'s
own structure rather than asserted here. -/
def IsPullbackAlong (g : PseudoRiemannianMetric I M) (g' : PseudoRiemannianMetric I' M')
    (f : C^∞⟮I, M; I', M'⟯) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x),
    g.form x v w = g'.form (f x) (mfderiv I I' f x v) (mfderiv I I' f x w)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- **A pseudo-Riemannian submanifold is immersed** — Lee's observation that nondegeneracy of
the induced tensor is the substantive hypothesis, and that it subsumes immersion.

If `df_x` killed a nonzero `v`, then `g_x(v, ·) = g̃(df_x v, df_x ·) = g̃(0, ·) = 0` would make
`v` a nonzero vector in the radical of `g_x`, contradicting nondegeneracy of `g`.  This is why
`exists_adapted_pseudo_orthonormalFrame` needs no immersion hypothesis, unlike its Riemannian
counterpart, where the pullback of a positive definite form is nondegenerate *only* under one
(`pullbackForm_posDef_iff_immersion`). -/
theorem injective_mfderiv_of_isPullbackAlong {g : PseudoRiemannianMetric I M}
    {g' : PseudoRiemannianMetric I' M'} {f : C^∞⟮I, M; I', M'⟯}
    (hg : IsPullbackAlong I I' g g' f) (x : M) : Function.Injective (mfderiv I I' f x) := by
  intro a b hab
  have hzero : mfderiv I I' f x (a - b) = 0 := by rw [map_sub, hab, sub_self]
  refine sub_eq_zero.mp (g.bilin_separatingLeft x (a - b) fun w => ?_)
  rw [ContMDiffPseudoMetric.bilin_apply, hg x (a - b) w, hzero]
  simp

omit [FiniteDimensional ℝ E'] in
/-- **A Riemannian submanifold is a pseudo-Riemannian submanifold**: the metric that Lee's
Lemma 2.11 induces on an immersed `M` *is* the pullback tensor, by definition of `pullbackForm`.

This discharges `IsPullbackAlong` for the case Lee cares about most, and so confirms that the
hypothesis of `exists_adapted_pseudo_orthonormalFrame` is one a caller can actually supply:
Lee's Proposition 2.72 covers both the Riemannian and the properly indefinite submanifold,
and this is the bridge for the former. -/
theorem isPullbackAlong_pullbackMetric (g' : RiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ p : M, Function.Injective (mfderiv I I' f p)) :
    IsPullbackAlong I I' (pullbackMetric g' f f.contMDiff himm).toPseudoRiemannianMetric
      g'.toPseudoRiemannianMetric f :=
  fun _ _ _ => rfl

/-- **Existence of adapted orthonormal frames on a pseudo-Riemannian submanifold**
(Lee, Proposition 2.72).

Let `(M̃, g̃)` be a pseudo-Riemannian manifold and let `f : M → M̃` present `M` as a
pseudo-Riemannian submanifold, the induced metric being `g`.  Every `p ∈ M` has a neighbourhood
`v` carrying a smooth frame `(E_1, …, E_m)` for the ambient tangent bundle `T M̃|_M = f *ᵖ T M̃`
that is orthonormal for `g̃` in Lee's indefinite `±1` sense, and whose first `n = dim M` members
span `T_x M` at every point of `v` — Lee's "adapted to `M`".

Orthonormality is stated through `g̃`'s pullback to the ambient bundle along `M`, since an
indefinite form induces no fibrewise `InnerProductSpace` to state it through; compare
`exists_adapted_orthonormalFrame`, whose Riemannian conclusion is phrased with `g'.inner`.

Slice coordinates play no part, so — as in the Riemannian case — `f` need only be a pseudo-
Riemannian *immersion*, not an embedding. -/
theorem exists_adapted_pseudo_orthonormalFrame (g : PseudoRiemannianMetric I M)
    (g' : PseudoRiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (hg : IsPullbackAlong I I' g g' f) (p : M) :
    ∃ (v : Set M) (Y : Fin (finrank ℝ E') → (x : M) →
        ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) (hn : finrank ℝ E ≤ finrank ℝ E'),
      IsOpen v ∧ p ∈ v ∧ IsLocalFrameOn I E' ∞ Y v ∧
      (∀ x ∈ v, IsOrthonormal ((g'.pullback f).bilin x) fun j => Y j x) ∧
      (∀ x ∈ v, ∀ i : Fin (finrank ℝ E), Y (Fin.castLE hn i) x ∈ tangentRange f x) ∧
      (∀ x ∈ v, span ℝ (Set.range fun i : Fin (finrank ℝ E) => Y (Fin.castLE hn i) x)
        = tangentRange f x) := by
  classical
  set V := ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) with hV
  set G : Bundle.ContMDiffPseudoMetric I ∞ E' V := g'.pullback f with hG
  haveI : ∀ x : M, FiniteDimensional ℝ (V x) := fun x => finiteDimensional_fibre (F := E') x
  have himm := injective_mfderiv_of_isPullbackAlong hg
  -- an orthonormal frame for `(M, g)` near `p` — Lee's Proposition 2.66.  This, rather than a
  -- chart frame, is the tangential input: it is what pushes forward to a *nondegenerate* tuple
  obtain ⟨u, X, huopen, hpu, hXframe, hXon⟩ := exists_pseudo_orthonormalFrame_nhds g p
  -- push it into the ambient fibres; the pairing is unchanged because `g = f^* g̃`
  set Z : Fin (finrank ℝ E) → (x : M) → V x := fun i x => pushforward f (X i) x with hZdef
  have hZon : ∀ x ∈ u, IsOrthonormal (G.bilin x) fun i => Z i x := by
    intro x hx
    have hpair : ∀ i j, G.bilin x (Z i x) (Z j x) = g.bilin x (X i x) (X j x) := by
      intro i j
      rw [ContMDiffPseudoMetric.bilin_apply, ContMDiffPseudoMetric.bilin_apply, hG,
        Bundle.ContMDiffPseudoMetric.pullback_form, hg x (X i x) (X j x)]
      rfl
    exact ⟨fun i j hij => by rw [hpair i j]; exact (hXon x hx).1 i j hij,
      fun i => by rw [hpair i i]; exact (hXon x hx).2 i⟩
  have hZ : IsLocalNondegenerateOn I E' ∞ G Z u :=
    { nondegenerateTuple := fun {x} hx => (hZon x hx).isNondegenerateTuple
      contMDiffOn := fun i => contMDiffOn_pushforward huopen (hXframe.contMDiffOn i) }
  -- extend to a nondegenerate frame of the ambient bundle near `p`
  obtain ⟨v, Y₀, hn, hvopen, hpv, hvsub, hY₀, hY₀Z⟩ :=
    exists_isLocalNondegenerateOn_extend (IB := I) (F := E') (V := V) G hZ huopen hpu
  -- members below the cut are pushforwards, hence tangent to `M`
  have hY₀tan : ∀ x ∈ v, ∀ i : Fin (finrank ℝ E), Y₀ (Fin.castLE hn i) x ∈ tangentRange f x :=
    fun x hx i => by rw [hY₀Z i x hx]; exact pushforward_mem_tangentRange f (X i) x
  -- Gram-Schmidt preserves the flag, so members below the cut stay inside the span of the
  -- tangential ones.  This is the whole reason the *ordered* extension mattered.
  have hGStan : ∀ x ∈ v, ∀ i : Fin (finrank ℝ E),
      pseudoGramSchmidtFrame G Y₀ (Fin.castLE hn i) x ∈ tangentRange f x := by
    intro x hx i
    have hi : ((Fin.castLE hn i : Fin (finrank ℝ E')) : ℕ) + 1 ≤ finrank ℝ E' :=
      (Fin.castLE hn i).isLt
    have hmem : pseudoGramSchmidtFrame G Y₀ (Fin.castLE hn i) x
        ∈ prefixSpan (fun j => pseudoGramSchmidtFrame G Y₀ j x) ((i : ℕ) + 1) := by
      refine subset_span ⟨Fin.castLE hn i, ?_, rfl⟩
      simp
    rw [prefixSpan_pseudoGramSchmidtFrame G hY₀ hx _ (by omega)] at hmem
    refine span_le.2 ?_ hmem
    rintro _ ⟨j, hj, rfl⟩
    have hjlt : (j : ℕ) < finrank ℝ E := by
      simp only [Set.mem_setOf_eq] at hj; omega
    have hjeq : j = Fin.castLE hn ⟨(j : ℕ), hjlt⟩ := by ext; simp
    rw [hjeq]
    exact hY₀tan x hx ⟨(j : ℕ), hjlt⟩
  have hGSon : ∀ x ∈ v, IsOrthonormal (G.bilin x) fun j => pseudoGramSchmidtFrame G Y₀ j x :=
    fun x hx => pseudoGramSchmidtFrame_isOrthonormal G hY₀ hx
  refine ⟨v, pseudoGramSchmidtFrame G Y₀, hn, hvopen, hpv, ?_, hGSon, hGStan, ?_⟩
  · -- an orthonormal tuple of the right length is a frame
    exact ⟨fun {x} hx => (hGSon x hx).linearIndependent,
      fun {x} hx => ((hGSon x hx).linearIndependent.span_eq_top_of_card_eq_finrank'
        (by simp [finrank_fibre (F := E') (V := V) x])).ge,
      contMDiffOn_pseudoGramSchmidtFrame G hY₀⟩
  · -- `n` independent tangent vectors inside the `n`-dimensional `tangentRange` span it
    intro x hx
    have hli : LinearIndependent ℝ
        (fun i : Fin (finrank ℝ E) => pseudoGramSchmidtFrame G Y₀ (Fin.castLE hn i) x) :=
      (hGSon x hx).linearIndependent.comp _ (Fin.castLE_injective hn)
    have hle : span ℝ (Set.range fun i : Fin (finrank ℝ E) =>
        pseudoGramSchmidtFrame G Y₀ (Fin.castLE hn i) x) ≤ tangentRange f x := by
      rw [span_le]; rintro _ ⟨i, rfl⟩; exact hGStan x hx i
    have h₁ : finrank ℝ (tangentRange f x) = finrank ℝ E := finrank_tangentRange f (himm x)
    have h₂ : finrank ℝ (span ℝ (Set.range fun i : Fin (finrank ℝ E) =>
        pseudoGramSchmidtFrame G Y₀ (Fin.castLE hn i) x)) = finrank ℝ E := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact Submodule.eq_of_le_of_finrank_le hle (le_of_eq (h₁.trans h₂.symm))

end Adapted

end LeeLib.Ch02

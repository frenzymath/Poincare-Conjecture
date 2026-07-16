/-
Chapter 2, "Riemannian Metrics", §"Pseudo-Riemannian Submanifolds": the pointwise
linear algebra behind Lee's Proposition 2.70.

Lee 2.70 is a statement about a hypersurface `M` in a pseudo-Riemannian manifold
`(M̃, g̃)`, but its whole content is discharged on a single tangent space `T_p M̃`,
the manifold playing no role beyond supplying that scalar product space.  This file
is that pointwise core; what remains for the manifold statement is a
`PseudoRiemannianMetric` structure, which the pinned mathlib does not have (see
inbox item I-0263).

The setting throughout is Lee's: `B` a scalar product on `V` (a nondegenerate
symmetric bilinear form), `W ⊆ V` a hyperplane — the tangent space `T_p M` — and
`W⊥` its normal line `N_p M`.  Lee's proposition has two halves, and both are proved
here:

* *Nondegeneracy.*  `ι*g̃` is nondegenerate at `p` iff every nonzero normal vector is
  non-null.  Lee gets this from Lemma 2.60 (`W` nondegenerate ↔ `W⊥` nondegenerate,
  already in `ScalarProduct.lean`); the new ingredient is that for a *line* — and
  only for a line — nondegeneracy is the same as having no nonzero null vector
  (`restrict_nondegenerate_iff_of_finrank_eq_one`).  That equivalence is special to
  dimension `1`: in higher dimension "no nonzero null vector" says the restriction is
  *definite*, which is strictly stronger than nondegenerate, so the equivalence is no
  longer a theorem — the hyperbolic plane `ξ² - τ²` is nondegenerate yet has null
  vectors.  This is exactly why Lee states the proposition for hypersurfaces.

* *Signature.*  If the normal vector is positive, the signature drops from `(r,s)` to
  `(r-1,s)`; if negative, to `(r,s-1)`.  Lee's argument is to take an orthonormal
  basis adapted to the normal line (`exists_isOrthonormal_prefixSpan_one_eq_span`,
  Lee 2.63), observe that its tail spans `T_p M`, and then count signs.  The counting
  is done here against mathlib's `sigPos`/`sigNeg`, which by Sylvester's law
  (`IsOrthonormal.sigPos_eq_ncard`, Lee 2.65) is what makes "the" signature well
  defined in the first place.

The one step Lee passes over in silence is that the tail of the adapted basis spans
`W`.  He writes "It follows that span(b₂,…,bₙ) = T_pM".  It does follow, but in two
stages.  First, `span(b₂,…,bₙ) = ⟨b₁⟩⊥`: the tail is visibly *contained* in the
orthogonal complement of the head, and equality is forced by a dimension count using
Lee 2.59(a); that is `span_range_succ_eq_orthogonal`.  Second, `⟨b₁⟩⊥` is `T_p M` on
the nose, which is `(W⊥)⊥ = W` — Lee 2.59(b); that is `orthogonal_span_singleton_eq`.
The two are combined in `sigPos_sigNeg_restrict_of_mem_orthogonal`, which states the
signature count about a hyperplane and a normal vector, as Lee does.
-/
import LeeLib.Ch02.ScalarProduct

namespace LeeLib.Ch02

open Module Submodule
open LinearMap (BilinForm)
open QuadraticMap QuadraticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

section Counting

/-- Splitting a count over `Fin (m+1)` into its `0`-th index and the successors: the
bookkeeping behind "the signature drops by one in the direction of the normal".

This is `Fin.card_filter_univ_succ'` transported from `Finset.card` to `Set.ncard`, which
is the form Sylvester's law is stated in (`IsOrthonormal.sigPos_eq_ncard`). -/
theorem ncard_setOf_fin_succ {m : ℕ} (p : Fin (m + 1) → Prop) [DecidablePred p] :
    {i : Fin (m + 1) | p i}.ncard = (if p 0 then 1 else 0) + {i : Fin m | p i.succ}.ncard := by
  classical
  rw [Set.ncard_eq_toFinset_card', Set.ncard_eq_toFinset_card']
  simp only [Set.toFinset_setOf]
  exact Fin.card_filter_univ_succ' p

end Counting

section NondegenerateLine

variable [FiniteDimensional ℝ V] {B : BilinForm ℝ V}

/-- **A line is nondegenerate exactly when its nonzero vectors are non-null.**

This is the linear-algebra fact that makes the nondegeneracy half of Lee 2.70 work, and
it is special to dimension `1`: in higher dimension "no nonzero null vector" means the
restriction is *definite*, strictly stronger than nondegenerate (the hyperbolic plane
`⟪·,·⟫ = ξ² - τ²` is nondegenerate yet has null vectors `ξ = ±τ`).  Note that neither
symmetry nor nondegeneracy of the ambient `B` is needed. -/
theorem restrict_nondegenerate_iff_of_finrank_eq_one {L : Submodule ℝ V}
    (hL : finrank ℝ L = 1) :
    (B.restrict L).Nondegenerate ↔ ∀ v ∈ L, v ≠ 0 → B v v ≠ 0 := by
  constructor
  · -- A nonzero null `v ∈ L` spans `L`, so it is `B`-orthogonal to all of `L`.
    rintro ⟨hsep, -⟩ v hv hv0 hvv
    have hspan : Submodule.span ℝ {v} = L :=
      Submodule.eq_of_le_of_finrank_eq
        ((Submodule.span_singleton_le_iff_mem _ _).2 hv)
        (by rw [finrank_span_singleton hv0, hL])
    refine hv0 (congrArg Subtype.val (hsep ⟨v, hv⟩ fun w => ?_))
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c • v = (w : V) :=
      Submodule.mem_span_singleton.1 (by rw [hspan]; exact w.2)
    show B v (w : V) = 0
    rw [← hc, map_smul, smul_eq_mul, hvv, mul_zero]
  · -- Conversely, a vector `B`-orthogonal to all of `L` is in particular null.
    intro h
    exact ⟨fun v hvw => by_contra fun hv0 =>
        h (v : V) v.2 (fun hh => hv0 (Subtype.ext hh)) (hvw v),
      fun v hvw => by_contra fun hv0 =>
        h (v : V) v.2 (fun hh => hv0 (Subtype.ext hh)) (hvw v)⟩

/-- **Lee, Proposition 2.70, nondegeneracy half** (pointwise core): for a hyperplane `W`
in a scalar product space — the tangent space `T_p M` of a hypersurface — the restriction
`B|_W` is nondegenerate if and only if every nonzero normal vector is non-null.

Lee: "Lemma 2.60 shows that `T_p M` is a nondegenerate subspace of `T_p M̃` if and only if
the one-dimensional subspace `(T_p M)⊥ = N_p M` is nondegenerate, which is the case if and
only if every nonzero `v ∈ N_p M` satisfies `g̃(v,v) ≠ 0`."  The codimension hypothesis is
what makes the second "if and only if" true; see
`restrict_nondegenerate_iff_of_finrank_eq_one`. -/
theorem restrict_nondegenerate_iff_forall_orthogonal (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {W : Submodule ℝ V} (hW : finrank ℝ W + 1 = finrank ℝ V) :
    (B.restrict W).Nondegenerate ↔ ∀ v ∈ B.orthogonal W, v ≠ 0 → B v v ≠ 0 := by
  refine ((restrict_nondegenerate_tfae hB hnd W).out 0 1).trans ?_
  refine restrict_nondegenerate_iff_of_finrank_eq_one ?_
  have := finrank_add_finrank_orthogonal_eq_finrank hnd W
  omega

end NondegenerateLine

section AdaptedTail

variable [FiniteDimensional ℝ V] {B : BilinForm ℝ V}

/-- **The tail of an orthonormal basis spans the orthogonal complement of its head.**

Lee states this in one clause — "It follows that `span(b₂,…,bₙ) = T_pM`" — but the
inclusion `⊆` and the equality have different proofs.  Containment is immediate from
orthogonality; equality is a dimension count, `dim span(b₂,…,bₙ) = n-1 = dim ⟨b₁⟩⊥`,
which is where nondegeneracy of `B` enters (Lee 2.59a). -/
theorem span_range_succ_eq_orthogonal (hnd : B.Nondegenerate) {m : ℕ} {b : Fin (m + 1) → V}
    (hbon : IsOrthonormal B b) (hspan : Submodule.span ℝ (Set.range b) = ⊤) :
    Submodule.span ℝ (Set.range fun i : Fin m => b i.succ)
      = B.orthogonal (Submodule.span ℝ {b 0}) := by
  have hb0 : b 0 ≠ 0 := fun h => hbon.apply_self_ne_zero 0 (by rw [h]; simp)
  have hli : LinearIndependent ℝ (fun i : Fin m => b i.succ) :=
    hbon.linearIndependent.comp _ (Fin.succ_injective m)
  -- Containment: each tail vector is orthogonal to the head, hence to the line it spans.
  have hle : Submodule.span ℝ (Set.range fun i : Fin m => b i.succ)
      ≤ B.orthogonal (Submodule.span ℝ {b 0}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hn
    show B (c • b 0) (b i.succ) = 0
    rw [map_smul, LinearMap.smul_apply, hbon.1 0 i.succ (Fin.succ_ne_zero i).symm, smul_zero]
  -- Equality by dimension: both sides have dimension `m`.
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  have hV : finrank ℝ V = m + 1 := by
    rw [Module.finrank_eq_card_basis
      (Basis.mk hbon.linearIndependent (le_of_eq hspan.symm)), Fintype.card_fin]
  have hperp := finrank_add_finrank_orthogonal_eq_finrank hnd (Submodule.span ℝ {b 0})
  rw [finrank_span_singleton hb0] at hperp
  rw [finrank_span_eq_card hli, Fintype.card_fin]
  omega

/-- **The tail of an adapted orthonormal basis is an orthonormal basis of the normal
line's orthogonal complement** — that is, of `T_p M`.

This packages `span_range_succ_eq_orthogonal` into the form the signature count needs:
an honest `Basis` of `W = ⟨b₀⟩⊥` indexed by `Fin m`, orthonormal for `B|_W`, whose
vectors are the `b i.succ`.  Sylvester's law (`IsOrthonormal.sigPos_eq_ncard`) can then
be applied on `W` exactly as it is on `V`. -/
theorem exists_basis_isOrthonormal_orthogonal_span_singleton (hnd : B.Nondegenerate) {m : ℕ}
    {b : Fin (m + 1) → V} (hbon : IsOrthonormal B b)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) :
    ∃ b' : Basis (Fin m) ℝ (B.orthogonal (Submodule.span ℝ {b 0})),
      IsOrthonormal (B.restrict (B.orthogonal (Submodule.span ℝ {b 0})))
        (b' : Fin m → B.orthogonal (Submodule.span ℝ {b 0})) ∧
      ∀ i, (b' i : V) = b i.succ := by
  have htail := span_range_succ_eq_orthogonal hnd hbon hspan
  have hmem : ∀ i : Fin m, b i.succ ∈ B.orthogonal (Submodule.span ℝ {b 0}) := fun i => by
    rw [← htail]
    exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨Basis.mk (v := fun i : Fin m => (⟨b i.succ, hmem i⟩ :
    B.orthogonal (Submodule.span ℝ {b 0}))) ?_ ?_, ⟨?_, ?_⟩, fun i => by rw [Basis.coe_mk]⟩
  · exact LinearIndependent.of_comp (B.orthogonal (Submodule.span ℝ {b 0})).subtype
      (hbon.linearIndependent.comp _ (Fin.succ_injective m))
  · -- `span (range b') = ⊤` in `W`, pushed forward along the injective inclusion `W → V`.
    refine le_of_eq (Submodule.map_injective_of_injective
      (B.orthogonal (Submodule.span ℝ {b 0})).subtype_injective ?_).symm
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top]
    exact htail
  · intro i j hij
    rw [Basis.coe_mk]
    exact hbon.1 i.succ j.succ fun h => hij (Fin.succ_injective m h)
  · intro i
    rw [Basis.coe_mk]
    exact hbon.2 i.succ

end AdaptedTail

section Signature

variable [FiniteDimensional ℝ V] {B : BilinForm ℝ V}

/-- The signature of `B|_{⟨b₀⟩⊥}` counted against the tail of the adapted orthonormal
basis: the same count as for `B`, with the `0`-th index removed. -/
theorem sigPos_sigNeg_restrict_orthogonal_eq_ncard (hnd : B.Nondegenerate) {m : ℕ}
    {b : Fin (m + 1) → V} (hbon : IsOrthonormal B b)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) :
    sigPos (LinearMap.BilinMap.toQuadraticMap
        (B.restrict (B.orthogonal (Submodule.span ℝ {b 0}))))
        = {i : Fin m | B (b i.succ) (b i.succ) = 1}.ncard ∧
      sigNeg (LinearMap.BilinMap.toQuadraticMap
        (B.restrict (B.orthogonal (Submodule.span ℝ {b 0}))))
        = {i : Fin m | B (b i.succ) (b i.succ) = -1}.ncard := by
  obtain ⟨b', hb'on, hb'coe⟩ := exists_basis_isOrthonormal_orthogonal_span_singleton hnd hbon hspan
  have hval : ∀ i : Fin m,
      (B.restrict (B.orthogonal (Submodule.span ℝ {b 0}))) (b' i) (b' i)
        = B (b i.succ) (b i.succ) := fun i => by
    simp [LinearMap.BilinForm.restrict_apply, hb'coe i]
  constructor
  · rw [hb'on.sigPos_eq_ncard]
    congr 1
    ext i
    simp only [Set.mem_setOf_eq, hval i]
  · rw [hb'on.sigNeg_eq_ncard]
    congr 1
    ext i
    simp only [Set.mem_setOf_eq, hval i]

/-- **Lee, Proposition 2.70, signature half** (pointwise core), stated against an adapted
orthonormal basis: passing from `V` to the orthogonal complement of the line `⟨b₀⟩` drops
exactly the sign carried by `b₀`. -/
theorem sigPos_sigNeg_restrict_orthogonal_of_head (hnd : B.Nondegenerate) {m : ℕ}
    {b : Fin (m + 1) → V} (hbon : IsOrthonormal B b)
    (hspan : Submodule.span ℝ (Set.range b) = ⊤) :
    sigPos (LinearMap.BilinMap.toQuadraticMap B)
        = (if B (b 0) (b 0) = 1 then 1 else 0) +
          sigPos (LinearMap.BilinMap.toQuadraticMap
            (B.restrict (B.orthogonal (Submodule.span ℝ {b 0})))) ∧
      sigNeg (LinearMap.BilinMap.toQuadraticMap B)
        = (if B (b 0) (b 0) = -1 then 1 else 0) +
          sigNeg (LinearMap.BilinMap.toQuadraticMap
            (B.restrict (B.orthogonal (Submodule.span ℝ {b 0})))) := by
  classical
  obtain ⟨hpos, hneg⟩ := sigPos_sigNeg_restrict_orthogonal_eq_ncard hnd hbon hspan
  have hbasis : IsOrthonormal B ((Basis.mk hbon.linearIndependent (le_of_eq hspan.symm) :
      Basis (Fin (m + 1)) ℝ V) : Fin (m + 1) → V) := by
    rw [Basis.coe_mk]; exact hbon
  constructor
  · rw [hbasis.sigPos_eq_ncard, hpos]
    simp only [Basis.coe_mk]
    exact ncard_setOf_fin_succ fun i => B (b i) (b i) = 1
  · rw [hbasis.sigNeg_eq_ncard, hneg]
    simp only [Basis.coe_mk]
    exact ncard_setOf_fin_succ fun i => B (b i) (b i) = -1

/-- **An orthonormal basis adapted to a non-null line**, indexed so that the line is
spanned by the `0`-th vector.

This is `exists_isOrthonormal_prefixSpan_one_eq_span` (Lee 2.63 applied to the `1`-tuple
`(x)`) with two cosmetic additions that the signature count needs: the tuple is recorded
as *spanning* `V` — automatic, an orthonormal tuple of `finrank ℝ V` vectors being a basis
— and it is reindexed from `Fin (finrank ℝ V)` to `Fin (m+1)`, which is what exposes the
head/tail split `0 :: Fin.succ`. -/
theorem exists_isOrthonormal_head_span_eq (hB : B.IsSymm) (hnd : B.Nondegenerate) {x : V}
    (hx : B x x ≠ 0) :
    ∃ (m : ℕ) (b : Fin (m + 1) → V), IsOrthonormal B b ∧
      Submodule.span ℝ (Set.range b) = ⊤ ∧
      Submodule.span ℝ {b 0} = Submodule.span ℝ {x} := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h]; simp)
  have hV1 : 1 ≤ finrank ℝ V := by
    have := Submodule.finrank_le (Submodule.span ℝ {x})
    rw [finrank_span_singleton hx0] at this
    omega
  obtain ⟨b, hbon, hb1⟩ := exists_isOrthonormal_prefixSpan_one_eq_span hB hnd hx hV1
  obtain ⟨m, hm⟩ : ∃ m, finrank ℝ V = m + 1 := ⟨finrank ℝ V - 1, by omega⟩
  refine ⟨m, b ∘ (finCongr hm.symm), hbon.comp_equiv _, ?_, ?_⟩
  · have hsp : Submodule.span ℝ (Set.range b) = ⊤ :=
      Submodule.eq_top_of_finrank_eq
        (by rw [finrank_span_eq_card hbon.linearIndependent, Fintype.card_fin])
    rwa [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  · rw [← hb1, prefixSpan_one b hV1]
    congr 2

/-- **The orthogonal complement of a non-null line is a hyperplane.**

Besides being the pointwise form of `dim T_pM = dim T_p M̃ - 1`, this is what discharges the
codimension hypothesis of `restrict_nondegenerate_iff_forall_orthogonal` for the subspaces it
is meant to be applied to, confirming that hypothesis is not vacuous. -/
theorem finrank_orthogonal_span_singleton (hnd : B.Nondegenerate) {x : V} (hx0 : x ≠ 0) :
    finrank ℝ (B.orthogonal (Submodule.span ℝ {x})) + 1 = finrank ℝ V := by
  have h := finrank_add_finrank_orthogonal_eq_finrank hnd (Submodule.span ℝ {x})
  rw [finrank_span_singleton hx0] at h
  omega

/-- **The orthogonal complement of a non-null line is itself a scalar product space.**

This is what entitles one to speak of *the signature* of the induced form on `T_p M` at all,
and it is the pointwise content of Lee's "`M` is a pseudo-Riemannian submanifold": the
induced form is nondegenerate.  It is the nondegeneracy half of Lee 2.70 specialized to the
normal line, obtained from Lee 2.60 rather than from
`restrict_nondegenerate_iff_forall_orthogonal`, which would be circular here. -/
theorem restrict_orthogonal_span_singleton_nondegenerate (hB : B.IsSymm)
    (hnd : B.Nondegenerate) {x : V} (hx : B x x ≠ 0) :
    (B.restrict (B.orthogonal (Submodule.span ℝ {x}))).Nondegenerate := by
  have hline : (B.restrict (Submodule.span ℝ {x})).Nondegenerate := by
    have h := (isNondegenerateTuple_singleton hB hnd hx) 1 le_rfl
    rw [prefixSpan_singleton] at h
    exact h.2
  exact ((restrict_nondegenerate_tfae hB hnd (Submodule.span ℝ {x})).out 0 1).mp hline

/-- **Lee, Proposition 2.70, signature half** (pointwise core), in the form Lee applies it:
at a point `p` of a hypersurface `M ⊆ M̃` with non-null normal vector `x`, the tangent space
`T_p M = ⟨x⟩⊥` carries the induced scalar product, and its signature is that of `T_p M̃` with
one positive sign removed if `x` is positive, one negative sign removed if `x` is negative.

Lee: "`g̃_p` has a basis representation of the form `(β¹)² ± (β²)² ± ⋯ ± (βⁿ)²`, with a total
of `r` positive terms and `s` negative ones, and with a positive sign on the first term.
Therefore `ι*g̃_p = ±(β²)² ± ⋯ ± (βⁿ)²` has signature `(r-1,s)`." -/
theorem sigPos_sigNeg_restrict_orthogonal_span_singleton (hB : B.IsSymm)
    (hnd : B.Nondegenerate) {x : V} (hx : B x x ≠ 0) :
    (0 < B x x →
      sigPos (LinearMap.BilinMap.toQuadraticMap
          (B.restrict (B.orthogonal (Submodule.span ℝ {x})))) + 1
          = sigPos (LinearMap.BilinMap.toQuadraticMap B) ∧
        sigNeg (LinearMap.BilinMap.toQuadraticMap
          (B.restrict (B.orthogonal (Submodule.span ℝ {x}))))
          = sigNeg (LinearMap.BilinMap.toQuadraticMap B)) ∧
    (B x x < 0 →
      sigPos (LinearMap.BilinMap.toQuadraticMap
          (B.restrict (B.orthogonal (Submodule.span ℝ {x}))))
          = sigPos (LinearMap.BilinMap.toQuadraticMap B) ∧
        sigNeg (LinearMap.BilinMap.toQuadraticMap
          (B.restrict (B.orthogonal (Submodule.span ℝ {x})))) + 1
          = sigNeg (LinearMap.BilinMap.toQuadraticMap B)) := by
  classical
  obtain ⟨m, b, hbon, hspan, hline⟩ := exists_isOrthonormal_head_span_eq hB hnd hx
  obtain ⟨hp, hn⟩ := sigPos_sigNeg_restrict_orthogonal_of_head hnd hbon hspan
  rw [hline] at hp hn
  -- `b 0` spans the same line as `x`, so `b 0 = c • x` with `c ≠ 0` and the two norms
  -- `⟪b₀,b₀⟫ = c²⟪x,x⟫` have the same sign.
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c • x = b 0 :=
    Submodule.mem_span_singleton.1 (hline ▸ Submodule.mem_span_singleton_self (b 0))
  have hcx : B (b 0) (b 0) = c ^ 2 * B x x := by
    rw [← hc]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hbon.apply_self_ne_zero 0 (by rw [hcx]; ring)
  have hcsq : 0 < c ^ 2 := by positivity
  constructor
  · intro hxpos
    have h0 : B (b 0) (b 0) = 1 := by
      rcases hbon.2 0 with h | h
      · exact h
      · exact absurd (hcx ▸ h) (by nlinarith)
    rw [h0] at hp hn
    norm_num at hp hn
    omega
  · intro hxneg
    have h0 : B (b 0) (b 0) = -1 := by
      rcases hbon.2 0 with h | h
      · exact absurd (hcx ▸ h) (by nlinarith)
      · exact h
    rw [h0] at hp hn
    norm_num at hp hn
    omega

/-- **A hyperplane's normal line is spanned by any nonzero normal vector.**

Pointwise: `N_p M = ⟨x⟩` for any nonzero `x` normal to `M`, because `N_p M` is a line. -/
theorem span_singleton_eq_orthogonal (hnd : B.Nondegenerate) {W : Submodule ℝ V}
    (hW : finrank ℝ W + 1 = finrank ℝ V) {x : V} (hx : x ∈ B.orthogonal W) (hx0 : x ≠ 0) :
    Submodule.span ℝ {x} = B.orthogonal W := by
  have hdim : finrank ℝ (B.orthogonal W) = 1 := by
    have := finrank_add_finrank_orthogonal_eq_finrank hnd W
    omega
  exact Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
    (by rw [finrank_span_singleton hx0, hdim])

/-- **A hyperplane is the orthogonal complement of its own normal line**: `T_p M = (N_p M)⊥`.

This is the other half of Lee's silent step "It follows that `span(b₂,…,bₙ) = T_pM`".
`span_range_succ_eq_orthogonal` gets as far as `span(b₂,…,bₙ) = ⟨b₁⟩⊥`; what identifies `⟨b₁⟩⊥`
with `T_p M` itself is `(W⊥)⊥ = W`, Lee 2.59(b). -/
theorem orthogonal_span_singleton_eq (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {W : Submodule ℝ V} (hW : finrank ℝ W + 1 = finrank ℝ V) {x : V}
    (hx : x ∈ B.orthogonal W) (hx0 : x ≠ 0) :
    B.orthogonal (Submodule.span ℝ {x}) = W := by
  rw [span_singleton_eq_orthogonal hnd hW hx hx0, orthogonal_orthogonal_eq_self hB hnd]

/-- **Lee, Proposition 2.70** (pointwise core), stated about the hyperplane itself — the form in
which Lee states his conclusion, and the form in which the two halves of the proposition speak
about the same subspace.

`sigPos_sigNeg_restrict_orthogonal_span_singleton` computes the signature of `⟨x⟩⊥`; this says
the same thing about a hyperplane `W` given a nonzero normal `x ∈ W⊥`, which is Lee's `T_p M`
and his `v ∈ N_p M`.  The two are identified by `(W⊥)⊥ = W` (Lee 2.59b).

Together with `restrict_nondegenerate_iff_forall_orthogonal`, which is stated about the same
`W`, this is the whole of Lee 2.70 at a point: `ι*g̃_p` is nondegenerate exactly when the normals
are non-null, and then `T_p M` has signature `(r-1,s)` or `(r,s-1)` according to their sign. -/
theorem sigPos_sigNeg_restrict_of_mem_orthogonal (hB : B.IsSymm) (hnd : B.Nondegenerate)
    {W : Submodule ℝ V} (hW : finrank ℝ W + 1 = finrank ℝ V) {x : V}
    (hx : x ∈ B.orthogonal W) (hx0 : x ≠ 0) :
    (0 < B x x →
      sigPos (LinearMap.BilinMap.toQuadraticMap (B.restrict W)) + 1
          = sigPos (LinearMap.BilinMap.toQuadraticMap B) ∧
        sigNeg (LinearMap.BilinMap.toQuadraticMap (B.restrict W))
          = sigNeg (LinearMap.BilinMap.toQuadraticMap B)) ∧
    (B x x < 0 →
      sigPos (LinearMap.BilinMap.toQuadraticMap (B.restrict W))
          = sigPos (LinearMap.BilinMap.toQuadraticMap B) ∧
        sigNeg (LinearMap.BilinMap.toQuadraticMap (B.restrict W)) + 1
          = sigNeg (LinearMap.BilinMap.toQuadraticMap B)) := by
  have hWeq : B.orthogonal (Submodule.span ℝ {x}) = W :=
    orthogonal_span_singleton_eq hB hnd hW hx hx0
  constructor
  · intro hxpos
    have h := (sigPos_sigNeg_restrict_orthogonal_span_singleton hB hnd hxpos.ne').1 hxpos
    rwa [hWeq] at h
  · intro hxneg
    have h := (sigPos_sigNeg_restrict_orthogonal_span_singleton hB hnd hxneg.ne).2 hxneg
    rwa [hWeq] at h

end Signature

end LeeLib.Ch02

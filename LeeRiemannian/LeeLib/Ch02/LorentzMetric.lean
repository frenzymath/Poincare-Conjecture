/-
Chapter 2, "Riemannian Metrics", §7 "Pseudo-Riemannian Metrics": the
**sufficiency half of Theorem 2.69** — a smooth manifold carrying a rank-1
tangent distribution carries a Lorentz metric.

Lee's Theorem 2.69 is an "if and only if"; this file does the direction that is
constructive.  The recipe is Lee's own (Problem 2-34(a)): choose any Riemannian
metric `g`, and flip its sign along the distribution.  Concretely, if `u_x` is a
`g`-unit vector spanning the line `D_x`, set

  `ḡ_x(v, w) = g_x(v, w) - 2 g_x(v, u_x) g_x(w, u_x)`,

which is `-g` on `D_x` and `g` on `D_x^⊥`, hence of signature `(n, 1)`.

Two things make this work, and both are already in place:

* **`u_x` is only determined up to sign, and that is exactly the ambiguity the
  formula cannot see.**  `u` occurs twice, so `LeeLib.Ch02.lorentzForm_neg` says
  `ḡ` does not change under `u ↦ -u`.  A line contains precisely two unit
  vectors, so `ḡ` is well defined *globally* even though `D` need not admit any
  global unit section — the Möbius band is the standard example, and the whole
  point of the theorem.  No orientability, and no `g`-orthogonal projection onto
  `D`, is needed anywhere.
* **The pointwise linear algebra is `LeeLib.Ch02.LorentzForm`**, which already
  proves this form symmetric, nondegenerate, and of signature `(n, 1)` via
  Sylvester's law.

What was missing was the *smoothness* of the resulting field of forms, and it
does not factor through `LeeLib.Ch02.contMDiffAt_bilinearCompOf`: that lemma
transports a form by a linear family in **both** slots, and the reflection
`R w = w - 2 g(w, u) u` is a `g`-isometry, so `g(Rv, Rw) = g(v, w)` gives back
`g` rather than the flipped form.  The route taken here reads `ḡ` as
`g - 2 (g u) ⊗ (g u)`, an algebraic combination of the smooth section `g` with
the tensor square of the smooth 1-form `g(u, ·)`; the new ingredient is
`Bundle.contMDiffAt_formProduct`, which is where the real analytic work lives.

Smoothness is then local, so the sign ambiguity never has to be resolved
globally: near any point `D` has a smooth nonvanishing local section `X`, and
`X/|X|_g` is a smooth local unit section, which the well-definedness above lets
us substitute for the globally-chosen `u`.

The converse (a Lorentz metric yields a rank-1 distribution) is
`prop:rank-one-distribution-of-lorentz-metric` in the blueprint and is *not*
done here: it needs smooth selection of the simple negative eigenvalue and its
eigenline of a smoothly-varying `g`-self-adjoint operator, which is neither in
this development nor in mathlib.
-/
import LeeLib.AppendixA.SubbundleCriterion
import LeeLib.Ch02.FormProduct
import LeeLib.Ch02.LorentzForm
import LeeLib.Ch02.MetricExistence
import LeeLib.Ch02.PseudoRiemannianMetric
import Mathlib.Geometry.Manifold.Algebra.Structures

namespace Bundle

open Bundle Manifold
open scoped Manifold ContDiff Topology

section FlipForm

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : ℕ∞ω}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)]
  [∀ b, TopologicalSpace (E b)] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

/-- **A field of bilinear forms with its sign flipped along a field of vectors**:

  `(flipFormOf b u)_x (v, w) = b_x(v, w) - 2 b_x(u_x, v) b_x(u_x, w)`.

For a `b`-unit `u_x` this is `-b` on `span{u_x}` and `b` on `u_x^⊥`; it is the
bundle-level form of `LeeLib.Ch02.lorentzForm`.  Written as `b - 2 (b u) ⊗ (b u)`
so that its smoothness is `Bundle.contMDiffAt_formProduct` plus the section
combinators, rather than a fresh `inCoordinates` computation.

Nothing here needs `b` symmetric, positive, or nondegenerate, and `u` need not be
a unit vector; those enter only when the result is identified with `lorentzForm`. -/
noncomputable def flipFormOf (b : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ) (u : ∀ x : B, E x) :
    ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ :=
  b - (2 : ℝ) • formProduct (fun y ↦ b y (u y)) (fun y ↦ b y (u y))

omit [TopologicalSpace B] [∀ b, IsTopologicalAddGroup (E b)]
  [∀ b, ContinuousConstSMul ℝ (E b)] in
@[simp] theorem flipFormOf_apply (b : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ) (u : ∀ x : B, E x) (x : B)
    (v w : E x) :
    flipFormOf b u x v w = b x v w - 2 * (b x (u x) v) * (b x (u x) w) := by
  simp [flipFormOf, mul_assoc]

omit [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)] in
/-- **The sign-flipped field of forms is smooth.**

`b - 2 (b u) ⊗ (b u)`: the 1-form `b(u, ·)` is smooth by `clm_bundle_apply`, its
tensor square is smooth by `contMDiffAt_formProduct`, and the section combinators
`sub_section`/`const_smul_section` assemble the result. -/
theorem contMDiffAt_flipFormOf {b : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ} {u : ∀ x : B, E x} {x₀ : B}
    (hb : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x (b x)) x₀)
    (hu : ContMDiffAt IB (IB.prod 𝓘(ℝ, F)) n (fun x ↦ TotalSpace.mk' F x (u x)) x₀) :
    ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun x ↦ E x →L[ℝ] E x →L[ℝ] ℝ) x (flipFormOf b u x)) x₀ := by
  have hα : ContMDiffAt IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun x ↦ E x →L[ℝ] Bundle.Trivial B ℝ x) x (b x (u x))) x₀ :=
    hb.clm_bundle_apply hu
  exact hb.sub_section (contMDiffAt_formProduct hα hα).const_smul_section

omit [TopologicalSpace B] [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousConstSMul ℝ (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] [TopologicalSpace (TotalSpace F E)] in
/-- **The flipped form sees `u` only up to sign** — the bundle-level form of
`LeeLib.Ch02.lorentzForm_neg`, and the reason the construction of Theorem 2.69 is
well defined.

`u` occurs twice in `b - 2 (b u) ⊗ (b u)`, so the two sign changes cancel.  The
statement is pointwise in `x`, and deliberately so: a rank-1 distribution's local
unit section agrees with a globally chosen one only up to a sign that varies from
point to point, and no continuous choice of that sign need exist. -/
theorem flipFormOf_apply_congr {b : ∀ x : B, E x →L[ℝ] E x →L[ℝ] ℝ} {u u' : ∀ x : B, E x} {x : B}
    (h : u' x = u x ∨ u' x = -(u x)) : flipFormOf b u' x = flipFormOf b u x := by
  refine ContinuousLinearMap.ext fun v ↦ ContinuousLinearMap.ext fun w ↦ ?_
  rcases h with h | h <;> simp [h]

end FlipForm

end Bundle

namespace LeeLib.Ch02

open Bundle Manifold Module Submodule
open scoped Manifold ContDiff Topology RealInnerProductSpace

section Distribution

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable (I M) in
/-- A **rank-1 tangent distribution** (Lee, Theorem 2.69: "a rank-1 subbundle of `TM`"):
a field of lines in the tangent spaces that is spanned, near every point, by a smooth
nowhere-vanishing vector field.

This is Lee's own definition of a smooth distribution specialized to rank 1, in its
local-frame form.  Stating it that way rather than as a bundle is deliberate:

* it is what the *hypothesis* of Theorem 2.69 actually supplies and what its proof
  actually consumes — a smooth local section to normalize;
* it needs no auxiliary metric, whereas making `D` into a bundle does
  (`LeeLib.AppendixA.subContMDiffVectorBundle`, Lee's Lemma A.34, Gram-Schmidts the
  local subframe against one, so `HasLocalSubframes` carries an
  `IsContMDiffRiemannianBundle` hypothesis that the notion of a distribution should not).

Nothing is lost by not saying "subbundle": `hasLocalSubframes_of_isRankOneDistribution`
below turns this into the input of A.34, which then makes `D` an honest rank-1 smooth
vector bundle.  Theorem 2.69 itself never needs that, only the local sections.

The spanning condition `span {X x} = D x` together with `X x ≠ 0` forces `D x` to be a
line, so no separate rank hypothesis is needed. -/
structure IsRankOneDistribution (D : ∀ x : M, Submodule ℝ (TangentSpace I x)) : Prop where
  /-- Every point has a neighbourhood on which `D` is spanned by one smooth
  nowhere-vanishing vector field. -/
  exists_localSpan (p : M) : ∃ (v : Set M) (X : ∀ x : M, TangentSpace I x),
    IsOpen v ∧ p ∈ v ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x ↦ TotalSpace.mk' E x (X x)) v ∧
      ∀ x ∈ v, X x ≠ 0 ∧ span ℝ {X x} = D x

/-! ### Normalizing against a Riemannian metric

Lee's `U = X/|X|_g`.  Kept separate from the fibrewise `InnerProductSpace` that
`Bundle.RiemannianBundle` installs, so that it can be used in statements that do not
mention that instance — in particular in the `contMDiff` field of the metric built below. -/

/-- **`g`-normalization** `v ↦ v/|v|_g`, written with `g.inner` rather than a norm so
that it needs no fibrewise `InnerProductSpace` instance. -/
noncomputable def gNormalize (g : RiemannianMetric I M) {x : M} (v : TangentSpace I x) :
    TangentSpace I x :=
  (Real.sqrt (g.inner x v v))⁻¹ • v

/-- The `g`-normalization of a nonzero vector is a `g`-unit vector. -/
theorem gNormalize_inner_self (g : RiemannianMetric I M) {x : M} {v : TangentSpace I x}
    (hv : v ≠ 0) : g.inner x (gNormalize g v) (gNormalize g v) = 1 := by
  have hq : 0 < g.inner x v v := g.pos x v hv
  have hs : Real.sqrt (g.inner x v v) ≠ 0 := Real.sqrt_ne_zero'.2 hq
  simp only [gNormalize, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp
  exact (Real.sq_sqrt hq.le).symm

/-- Normalizing does not change the line spanned. -/
theorem span_gNormalize (g : RiemannianMetric I M) {x : M} {v : TangentSpace I x} (hv : v ≠ 0) :
    span ℝ {gNormalize g v} = span ℝ {v} :=
  span_singleton_smul_eq
    (isUnit_iff_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 (g.pos x v hv)))) v

variable {D : ∀ x : M, Submodule ℝ (TangentSpace I x)}

/-- Each fibre of a rank-1 distribution contains a nonzero vector — the pointwise
consequence of the local spanning condition, read off at the point itself. -/
theorem IsRankOneDistribution.exists_ne_zero (hD : IsRankOneDistribution I M D) (x : M) :
    ∃ v, v ∈ D x ∧ v ≠ 0 := by
  obtain ⟨v, X, -, hxv, -, hspan⟩ := hD.exists_localSpan x
  obtain ⟨hne, hsp⟩ := hspan x hxv
  exact ⟨X x, hsp ▸ mem_span_singleton_self (X x), hne⟩

/-- Each fibre of a rank-1 distribution is a line. -/
theorem IsRankOneDistribution.finrank_eq_one (hD : IsRankOneDistribution I M D) (x : M) :
    finrank ℝ (D x) = 1 := by
  obtain ⟨v, X, -, hxv, -, hspan⟩ := hD.exists_localSpan x
  obtain ⟨hne, hsp⟩ := hspan x hxv
  rw [← hsp, finrank_span_singleton hne]

/-- **A rank-1 distribution lives in a tangent space of positive dimension.**  Used to
write `dim M = n + 1`, which is how Lee states the signature `(n, 1)`. -/
theorem IsRankOneDistribution.one_le_finrank [FiniteDimensional ℝ E]
    (hD : IsRankOneDistribution I M D) (x : M) : 1 ≤ finrank ℝ E := by
  have h : finrank ℝ (D x) ≤ finrank ℝ (TangentSpace I x) := Submodule.finrank_le (D x)
  rw [hD.finrank_eq_one x] at h
  exact h

/-- **A rank-1 distribution has a smooth `g`-unit local section near every point** — Lee's
"shrinking the neighbourhood, `X` is nowhere zero, so `U = X/|X|_g` is a smooth local
`g`-unit section spanning `D`".

No shrinking is actually needed: the local section supplied by
`IsRankOneDistribution` is already nowhere zero on its domain, so `|X|_g` is smooth and
strictly positive there and the quotient is smooth outright.  The normalization follows
`LeeLib.Ch02.contMDiffOn_gramSchmidtFrame`: `⟨X, X⟩_g` is smooth by the pairing lemma,
positive by definiteness, hence `⟨X,X⟩_g^{-1/2}` is smooth under `Real.sqrt`.

Note the section produced is total (defined at every point of `M`); only its smoothness
and unit length are asserted on the neighbourhood.  That is what
`Bundle.contMDiffAt_flipFormOf` consumes. -/
theorem IsRankOneDistribution.exists_localUnitSection (g : RiemannianMetric I M)
    (hD : IsRankOneDistribution I M D) (p : M) :
    ∃ (v : Set M) (U : ∀ x : M, TangentSpace I x), IsOpen v ∧ p ∈ v ∧
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (fun x ↦ TotalSpace.mk' E x (U x)) v ∧
      ∀ x ∈ v, g.inner x (U x) (U x) = 1 ∧ span ℝ {U x} = D x := by
  obtain ⟨v, X, hv, hpv, hX, hspan⟩ := hD.exists_localSpan p
  have hpos : ∀ x ∈ v, 0 < g.inner x (X x) (X x) := fun x hx => g.pos x (X x) (hspan x hx).1
  refine ⟨v, fun x ↦ gNormalize g (X x), hv, hpv, ?_, ?_⟩
  · -- smoothness: a positive smooth function under a square root, then `smul_section`
    have hq : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x ↦ g.inner x (X x) (X x)) v :=
      g.toPseudoRiemannianMetric.contMDiffOn_pairing (b := id) contMDiffOn_id hX hX
    have hinv : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
        (fun x ↦ (Real.sqrt (g.inner x (X x) (X x)))⁻¹) v := by
      have hsqrt : ContMDiffOn I 𝓘(ℝ, ℝ) ∞
          (fun x ↦ Real.sqrt (g.inner x (X x) (X x))) v := fun x hx =>
        ContDiffAt.comp_contMDiffWithinAt (g := Real.sqrt)
          (Real.contDiffAt_sqrt (hpos x hx).ne') (hq x hx)
      exact hsqrt.inv₀ fun x hx => Real.sqrt_ne_zero'.2 (hpos x hx)
    exact hinv.smul_section hX
  · intro x hx
    obtain ⟨hne, hsp⟩ := hspan x hx
    exact ⟨gNormalize_inner_self g hne, (span_gNormalize g hne).trans hsp⟩

/-- Any nonzero vector of a fibre of a rank-1 distribution spans that fibre — the fibre is
a line, so a single nonzero vector already exhausts it. -/
theorem IsRankOneDistribution.span_singleton_eq [FiniteDimensional ℝ E]
    (hD : IsRankOneDistribution I M D) {x : M} {v : TangentSpace I x} (hv : v ∈ D x)
    (hv0 : v ≠ 0) : span ℝ {v} = D x := by
  refine Submodule.eq_of_le_of_finrank_eq ((span_singleton_le_iff_mem v (D x)).2 hv) ?_
  rw [finrank_span_singleton hv0, hD.finrank_eq_one x]

/-- **A rank-1 distribution is a rank-1 subbundle** — the `k = 1` case of the hypothesis of
Lee's Lemma A.34 (`LeeLib.AppendixA.HasLocalSubframes`), which
`LeeLib.AppendixA.subContMDiffVectorBundle` turns into an honest smooth vector bundle
structure on `D`.

This is what justifies reading `IsRankOneDistribution` as Theorem 2.69's "rank-1 subbundle
of `TM`": the local-frame definition and the subbundle are the same notion.  A single
section is linearly independent exactly when it is nonzero, and the range of a `Fin 1`-family
is the singleton, so there is nothing to prove beyond bookkeeping.

The auxiliary metric is A.34's, not the distribution's: it Gram-Schmidts the local subframe
to make the coordinate change a smooth Gram matrix.  It costs nothing here, since every
smooth manifold has one (`exists_riemannianMetric`), but it is why `IsRankOneDistribution`
is *not* defined this way — a distribution should not have to mention a metric. -/
theorem hasLocalSubframes_of_isRankOneDistribution (g : RiemannianMetric I M)
    (hD : IsRankOneDistribution I M D) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    LeeLib.AppendixA.HasLocalSubframes I E ∞ 1 D := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  refine ⟨fun p ↦ ?_⟩
  obtain ⟨v, X, hv, hpv, hX, hspan⟩ := hD.exists_localSpan p
  refine ⟨v, fun _ ↦ X, hv, hpv, ⟨fun {x} hx ↦ ?_, fun _ ↦ hX⟩, fun {x} hx ↦ ?_⟩
  · exact linearIndependent_unique_iff.2 (hspan x hx).1
  · rw [Set.range_const]
    exact (hspan x hx).2

/-- **Two `g`-unit vectors spanning the same line agree up to sign.**

This is the second half of Lee's "the fibre `D_x` is a line in `T_xM`, so it contains
exactly two `g`-unit vectors, `±u_x`".  Together with `Bundle.flipFormOf_apply_congr` it
is what makes the flipped form independent of the choice, hence globally well defined.

No Cauchy–Schwarz is needed: membership in the span gives `u' = c • u` outright, and
`⟨u',u'⟩ = 1` then forces `c² = 1`. -/
theorem eq_or_eq_neg_of_span_eq (g : RiemannianMetric I M) {x : M} {u u' : TangentSpace I x}
    (hu : g.inner x u u = 1) (hu' : g.inner x u' u' = 1) (h : span ℝ {u'} = span ℝ {u}) :
    u' = u ∨ u' = -u := by
  obtain ⟨c, hc⟩ := mem_span_singleton.mp (h ▸ mem_span_singleton_self u')
  have hcc : c * c = 1 := by
    rw [← hc] at hu'
    simpa [map_smul, hu] using hu'
  rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
  · exact Or.inl (by simpa using hc.symm)
  · exact Or.inr (by simpa using hc.symm)

end Distribution

section Existence

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

open QuadraticMap QuadraticForm

variable (I M) in
/-- **Lee's Theorem 2.69, sufficiency half**: a smooth manifold carrying a rank-1 tangent
distribution carries a Lorentz metric.

The construction is Lee's (Problem 2-34(a)): pick any Riemannian metric `g`
(`exists_riemannianMetric` — every smooth manifold has one), pick a `g`-unit vector `u_x`
spanning each line `D_x`, and flip the sign of `g` along `u`:

  `ḡ_x(v, w) = g_x(v, w) - 2 g_x(v, u_x) g_x(w, u_x)`.

The two subtleties are both handled by lemmas above.

*Well-definedness.*  `u_x` is only determined up to sign, and no continuous choice of
sign need exist — the Möbius band's line field is the standard obstruction, and if a
global unit section always existed the theorem would be vacuous.  But `u` occurs twice in
the formula, so `Bundle.flipFormOf_apply_congr` says the form cannot see the choice.  The
selection below is therefore made with `Classical.choose`, pointwise and with no
continuity whatsoever, and the resulting *form* is still smooth.

*Smoothness.*  A local question.  Near any point `D` has a smooth `g`-unit section `U`
(`IsRankOneDistribution.exists_localUnitSection`), which agrees with the chosen `u` up to
sign at every nearby point (`eq_or_eq_neg_of_span_eq`); so the chosen form agrees near `p`
with `Bundle.flipFormOf g.inner U`, which is smooth by `Bundle.contMDiffAt_flipFormOf`.

The index is `1` and the signature `(n, 1)` with `n + 1 = dim M` by the pointwise linear
algebra of `LeeLib.Ch02.LorentzForm`, applied fibrewise through the `InnerProductSpace`
that `Bundle.RiemannianBundle` installs from `g`.  Note `dim M ≥ 1` is not a hypothesis:
a rank-1 distribution forces it, and `IsRankOneDistribution.one_le_finrank` extracts it. -/
theorem exists_isLorentzMetric_of_isRankOneDistribution
    {D : ∀ x : M, Submodule ℝ (TangentSpace I x)} (hD : IsRankOneDistribution I M D) :
    ∃ gL : PseudoRiemannianMetric I M, IsLorentzMetric gL := by
  obtain ⟨g⟩ := exists_riemannianMetric (I := I) (M := M)
  -- The chosen unit section.  Pointwise, non-continuous, and that is fine.
  set u : ∀ x : M, TangentSpace I x :=
    fun x ↦ gNormalize g (Classical.choose (hD.exists_ne_zero x)) with hudef
  have hu_unit : ∀ x : M, g.inner x (u x) (u x) = 1 := fun x ↦
    gNormalize_inner_self g (Classical.choose_spec (hD.exists_ne_zero x)).2
  have hu_span : ∀ x : M, span ℝ {u x} = D x := fun x ↦
    (span_gNormalize g (Classical.choose_spec (hD.exists_ne_zero x)).2).trans
      (hD.span_singleton_eq (Classical.choose_spec (hD.exists_ne_zero x)).1
        (Classical.choose_spec (hD.exists_ne_zero x)).2)
  -- Symmetry, from symmetry of `g`.
  have hsymm : ∀ (x : M) (v w : TangentSpace I x),
      Bundle.flipFormOf (fun y ↦ g.inner y) u x v w
        = Bundle.flipFormOf (fun y ↦ g.inner y) u x w v := by
    intro x v w
    simp only [Bundle.flipFormOf_apply]
    rw [g.symm x v w]
    ring
  -- Smoothness, proved *before* any fibrewise inner product is installed.
  have hsmooth : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        (Bundle.flipFormOf (fun y ↦ g.inner y) u x)) := by
    intro p
    obtain ⟨v, U, hv, hpv, hU, hUprop⟩ := hD.exists_localUnitSection g p
    have hUat : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (fun x ↦ TotalSpace.mk' E x (U x)) p :=
      hU.contMDiffAt (hv.mem_nhds hpv)
    refine (Bundle.contMDiffAt_flipFormOf (F := E) (E := (TangentSpace I : M → Type _))
      g.contMDiff.contMDiffAt hUat).congr_of_eventuallyEq ?_
    filter_upwards [hv.mem_nhds hpv] with x hx
    refine congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x) ?_
    exact Bundle.flipFormOf_apply_congr (eq_or_eq_neg_of_span_eq g (hUprop x hx).1 (hu_unit x)
      ((hu_span x).trans (hUprop x hx).2.symm))
  -- The fibrewise inner product coming from `g`, for the pointwise linear algebra only.
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hbridge : ∀ (x : M) (v w : TangentSpace I x),
      Bundle.flipFormOf (fun y ↦ g.inner y) u x v w = lorentzForm (u x) v w := by
    intro x v w
    have h1 : (⟪v, w⟫ : ℝ) = g.inner x v w := rfl
    have h2 : (⟪v, u x⟫ : ℝ) = g.inner x v (u x) := rfl
    have h3 : (⟪w, u x⟫ : ℝ) = g.inner x w (u x) := rfl
    simp only [Bundle.flipFormOf_apply, lorentzForm_apply, h1, h2, h3]
    rw [g.symm x (u x) v, g.symm x (u x) w]
  have hnorm : ∀ x : M, ‖u x‖ = 1 := by
    intro x
    have h : (⟪u x, u x⟫ : ℝ) = 1 := hu_unit x
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith [norm_nonneg (u x)]
  have hnondeg : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      ∃ w, Bundle.flipFormOf (fun y ↦ g.inner y) u x v w ≠ 0 := by
    intro x v hv
    by_contra hc
    push Not at hc
    exact hv (lorentzForm_separatingLeft (hnorm x) v fun w ↦ by
      rw [← hbridge x v w]; exact hc w)
  set gL : PseudoRiemannianMetric I M :=
    { form := Bundle.flipFormOf (fun y ↦ g.inner y) u
      symm := hsymm
      nondegenerate := hnondeg
      contMDiff := hsmooth } with hgLdef
  have hbil : ∀ p : M, gL.bilin p = lorentzForm (u p) := by
    intro p
    ext v w
    exact hbridge p v w
  refine ⟨gL, finrank ℝ E - 1, fun p ↦ ?_⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, finrank ℝ E = n + 1 :=
    ⟨finrank ℝ E - 1, by have := hD.one_le_finrank p; omega⟩
  have hdim : finrank ℝ (TangentSpace I p) = n + 1 := hn
  obtain ⟨-, -, hpos, hneg⟩ := lorentzForm_isSymm_nondegenerate_signature (hnorm p) hdim
  rw [PseudoRiemannianMetric.sigPosAt, PseudoRiemannianMetric.sigNegAt, hbil p]
  exact ⟨by rw [hpos, hn]; omega, hneg⟩

end Existence

end LeeLib.Ch02

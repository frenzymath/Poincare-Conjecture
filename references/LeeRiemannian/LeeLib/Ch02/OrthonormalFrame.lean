/-
Chapter 2, "Riemannian Metrics", §2 "Local Representations for Metrics":
existence of smooth local orthonormal frames.

Lee's Proposition 2.8: if `(M, g)` is a Riemannian `n`-manifold and `(X_i)` is
any smooth local frame for `TM` over an open set `U`, then there is a smooth
*orthonormal* frame `(E_j)` over `U` with

  `span (E_1|_p, …, E_k|_p) = span (X_1|_p, …, X_k|_p)`   for each `k` and each `p ∈ U`,

so in particular every point of `M` has a neighbourhood carrying a smooth
orthonormal frame.  This is the workhorse of the rest of the chapter: Lee's
Propositions 2.9 (unit tangent bundle), 2.14 (adapted frames), 2.16 (the normal
bundle) and 2.17 (the outward normal) are all proved by choosing one.

Lee's proof is "apply Gram-Schmidt at each `p`, and note the formulas are smooth
because the denominators never vanish".  The formalization follows it literally,
and the point of the file is that *both halves are already in mathlib* once the
right instance is in place:

* mathlib's `RiemannianBundle` mechanism turns the metric into an honest
  `InnerProductSpace ℝ (V x)` structure on each fibre.  So `gramSchmidtNormed ℝ`
  — mathlib's Gram-Schmidt — can be applied *fibrewise*, and the algebraic half
  of Lee's proposition is exactly `gramSchmidtNormed_orthonormal` together with
  `span_gramSchmidtNormed` / `span_gramSchmidt_Iic`.  In particular Lee's initial
  span condition comes for free, rather than being re-proved.
* the analytic half — that `x ↦ gramSchmidtNormed ℝ (X · x) j` is a *smooth
  section* — is the new content, and is `contMDiffOn_gramSchmidtFrame` below.
  It is a well-founded induction along `j` over the Gram-Schmidt recursion
  `gramSchmidt_def''`, whose only non-formal step is Lee's own remark: the
  denominators `⟪u_i, u_i⟫` are nowhere zero on `U`, because linear independence
  of the frame keeps the Gram-Schmidt vectors nonzero, so the quotients are
  smooth.  `ContMDiffWithinAt.inner_bundle` supplies the fact that the metric
  pairing of two smooth sections is a smooth function, and the section
  combinators (`sub_section`, `smul_section`, `sum_section`) do the rest.

Everything is stated for a general Riemannian vector bundle `V → B` rather than
just for `TM`: Lee's proof never uses that `V` is the tangent bundle, and the
extra generality is what Lee's §2.3 needs later, where the same argument is
applied to the ambient tangent bundle `T M̃|_M` restricted to a submanifold
(Prop. 2.14) and to the normal bundle (Prop. 2.16).  `exists_orthonormalFrame`
at the end of the file is Lee's Proposition 2.8 verbatim, for `TM` and a
`RiemannianMetric`.

Note on prior art: the sibling DoCarmoLib (do Carmo) development contains a
`smoothOrthoFrame`, but it is a different statement — a hand-rolled Gram-Schmidt
recursion against the metric, applied to *the chart-induced frame* and cut off by
a bump function, with no initial-span condition and no arbitrary input frame.  It
is therefore not vendored here: Lee's Proposition 2.8 takes an arbitrary smooth
local frame as input and asserts the flag condition, and going through mathlib's
own `gramSchmidtNormed` proves the stronger statement in a fraction of the space.
-/
import LeeLib.Ch02.RiemannianMetric
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

namespace LeeLib.Ch02

open Bundle InnerProductSpace Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace

section BundleFrame

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [IsContMDiffRiemannianBundle IB n F V]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
  {X : ι → (x : B) → V x} {u : Set B}

variable (IB F n) in
/-- A family of sections of `V → B` that is `C^n` on `u` and **linearly independent at each
point of `u`** — but not necessarily spanning.

This is mathlib's `IsLocalFrameOn` with the `generating` field dropped, and it is exactly what
Gram-Schmidt needs: `gramSchmidtNormed` orthonormalizes any linearly independent family, whether
or not it is a basis.  The distinction is not idle bookkeeping.  Lee's §2.3 applies Gram-Schmidt
to the `n` pushed-forward tangent fields `dF(∂_1), …, dF(∂_n)` *inside* the `m`-dimensional fibre
of the ambient bundle `T M̃|_M`, with `n < m`; that family is linearly independent (because `F` is
an immersion) but spans only the tangent subspace, so it is an `IsLocalIndepOn` and not an
`IsLocalFrameOn`.  Producing the adapted frame of Lee's Proposition 2.14 is precisely the work of
enlarging such a family back to a full frame (`exists_isLocalFrameOn_extend`). -/
structure IsLocalIndepOn (X : ι → (x : B) → V x) (u : Set B) where
  linearIndependent {x : B} (hx : x ∈ u) : LinearIndependent ℝ (X · x)
  contMDiffOn (i : ι) : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (X i)) u

omit [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- A local frame is in particular a pointwise linearly independent family of smooth sections. -/
theorem _root_.IsLocalFrameOn.isLocalIndepOn (hX : IsLocalFrameOn IB F n X u) :
    IsLocalIndepOn IB F n X u where
  linearIndependent hx := hX.linearIndependent hx
  contMDiffOn i := hX.contMDiffOn i

omit [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι] [VectorBundle ℝ F V]
  [IsContMDiffRiemannianBundle IB n F V] in
/-- Restriction of a pointwise linearly independent family to a smaller set. -/
theorem IsLocalIndepOn.mono {u' : Set B} (hX : IsLocalIndepOn IB F n X u) (h : u' ⊆ u) :
    IsLocalIndepOn IB F n X u' where
  linearIndependent hx := hX.linearIndependent (h hx)
  contMDiffOn i := (hX.contMDiffOn i).mono h

/-- The **unnormalized fibrewise Gram-Schmidt** of a family of sections: at each
point `x`, mathlib's `gramSchmidt` applied to the vectors `X i x` in the fibre
`V x`, using the inner product that the Riemannian bundle structure puts there.

This is the family Lee calls `(2.5)`; `gramSchmidtFrame` is its normalization. -/
noncomputable def gramSchmidtFrameAux (X : ι → (x : B) → V x) (j : ι) (x : B) : V x :=
  gramSchmidt ℝ (fun i => X i x) j

/-- The **fibrewise Gram-Schmidt orthonormalization** of a family of sections
(Lee, `(2.6)`): at each point, mathlib's `gramSchmidtNormed` in the fibre.

For a smooth local frame `X` on an open set `u` this is again a smooth local
frame on `u` (`isLocalFrameOn_gramSchmidtFrame`), it is orthonormal at every
point of `u` (`gramSchmidtFrame_orthonormal`), and it spans the same flag
(`span_gramSchmidtFrame_Iic`) — which together are Lee's Proposition 2.8. -/
noncomputable def gramSchmidtFrame (X : ι → (x : B) → V x) (j : ι) (x : B) : V x :=
  gramSchmidtNormed ℝ (fun i => X i x) j

/-! ### The algebraic half: orthonormality and the initial spans

At a point of `u` the frame vectors are linearly independent, so mathlib's
Gram-Schmidt theory applies verbatim in the fibre. -/

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- On `u` the Gram-Schmidt vectors are nonzero — the fact Lee uses to say that
"the vectors whose norms appear in the denominators are nowhere vanishing". -/
theorem gramSchmidtFrameAux_ne_zero (hX : IsLocalIndepOn IB F n X u) {x : B} (hx : x ∈ u) (j : ι) :
    gramSchmidtFrameAux X j x ≠ 0 :=
  gramSchmidt_ne_zero j (hX.linearIndependent hx)

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- The Gram-Schmidt denominators `⟪u_j, u_j⟫` are strictly positive on `u`. -/
theorem gramSchmidtFrameAux_inner_self_pos (hX : IsLocalIndepOn IB F n X u) {x : B} (hx : x ∈ u)
    (j : ι) : 0 < ⟪gramSchmidtFrameAux X j x, gramSchmidtFrameAux X j x⟫_ℝ :=
  real_inner_self_pos.2 (gramSchmidtFrameAux_ne_zero hX hx j)

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- **Orthonormality** (Lee, Prop. 2.8): at each point of `u` the orthonormalized
frame is an orthonormal family in the fibre. -/
theorem gramSchmidtFrame_orthonormal (hX : IsLocalIndepOn IB F n X u) {x : B} (hx : x ∈ u) :
    Orthonormal ℝ (fun j => gramSchmidtFrame X j x) :=
  gramSchmidtNormed_orthonormal (hX.linearIndependent hx)

omit [TopologicalSpace B] in
/-- **The initial span condition** (Lee, Prop. 2.8):
`span (E_1|_x, …, E_k|_x) = span (X_1|_x, …, X_k|_x)` for every `k`. -/
theorem span_gramSchmidtFrame_Iic (X : ι → (x : B) → V x) (x : B) (k : ι) :
    span ℝ ((fun j => gramSchmidtFrame X j x) '' Set.Iic k)
      = span ℝ ((fun j => X j x) '' Set.Iic k) := by
  simpa only [gramSchmidtFrame] using
    (span_gramSchmidtNormed (𝕜 := ℝ) (fun i => X i x) (Set.Iic k)).trans
      (span_gramSchmidt_Iic ℝ (fun i => X i x) k)

omit [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB n F V] in
/-- The orthonormalized frame is linearly independent at each point of `u`. -/
theorem gramSchmidtFrame_linearIndependent (hX : IsLocalIndepOn IB F n X u) {x : B} (hx : x ∈ u) :
    LinearIndependent ℝ (fun j => gramSchmidtFrame X j x) :=
  gramSchmidtNormed_linearIndependent (hX.linearIndependent hx)

/-! ### The analytic half: smoothness of the Gram-Schmidt sections

This is the content of Lee's remark that the Gram-Schmidt formulas define
*smooth* vector fields.  The induction is along the recursion `gramSchmidt_def''`

  `u_j = X_j - ∑_{i < j} (⟪u_i, X_j⟫ / ⟪u_i, u_i⟫) • u_i`,

in which every ingredient is smooth: `X_j` by hypothesis, `u_i` for `i < j` by
the inductive hypothesis, the inner products by `inner_bundle`, and the
quotients because the denominators are positive on `u`. -/

omit [TopologicalSpace B] in
/-- The Gram-Schmidt recursion, with the denominator written as an inner product
rather than a norm — the form in which the smoothness induction needs it. -/
theorem gramSchmidtFrameAux_eq (X : ι → (x : B) → V x) (j : ι) (x : B) :
    gramSchmidtFrameAux X j x = X j x -
      ∑ i ∈ Finset.Iio j, (⟪gramSchmidtFrameAux X i x, X j x⟫_ℝ /
        ⟪gramSchmidtFrameAux X i x, gramSchmidtFrameAux X i x⟫_ℝ) • gramSchmidtFrameAux X i x := by
  simp only [gramSchmidtFrameAux, real_inner_self_eq_norm_sq]
  rw [eq_sub_iff_add_eq]
  exact (gramSchmidt_def'' ℝ (fun i => X i x) j).symm

/-- **Smoothness of the unnormalized Gram-Schmidt sections.**  Well-founded
induction over the recursion; the denominators are nonvanishing on `u`, which is
what makes the quotients smooth. -/
theorem contMDiffOn_gramSchmidtFrameAux (hX : IsLocalIndepOn IB F n X u) (j : ι) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (gramSchmidtFrameAux X j)) u := by
  induction j using WellFoundedLT.induction with
  | _ j IH =>
    -- the coefficient `c i = ⟪u_i, X_j⟫ / ⟪u_i, u_i⟫` of the recursion
    have hc : ∀ i ∈ Finset.Iio j, ContMDiffOn IB 𝓘(ℝ, ℝ) n
        (fun x => ⟪gramSchmidtFrameAux X i x, X j x⟫_ℝ /
          ⟪gramSchmidtFrameAux X i x, gramSchmidtFrameAux X i x⟫_ℝ) u := by
      intro i hi
      have hui := IH i (Finset.mem_Iio.mp hi)
      exact ContMDiffOn.div₀ (hui.inner_bundle (hX.contMDiffOn j)) (hui.inner_bundle hui)
        fun x hx => (gramSchmidtFrameAux_inner_self_pos hX hx i).ne'
    -- each summand `c i • u_i` is a smooth section, hence so is the sum
    have hsum : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
        (T% (fun x => ∑ i ∈ Finset.Iio j, (⟪gramSchmidtFrameAux X i x, X j x⟫_ℝ /
          ⟪gramSchmidtFrameAux X i x, gramSchmidtFrameAux X i x⟫_ℝ) •
            gramSchmidtFrameAux X i x)) u :=
      ContMDiffOn.sum_section fun i hi => (hc i hi).smul_section (IH i (Finset.mem_Iio.mp hi))
    refine ((hX.contMDiffOn j).sub_section hsum).congr fun x hx => ?_
    exact congrArg (TotalSpace.mk' F x) (gramSchmidtFrameAux_eq X j x)

/-- **Smoothness of the orthonormalized frame** — the analytic content of Lee's
Proposition 2.8.  Normalization divides by `‖u_j‖ = √⟪u_j, u_j⟫`, which is smooth
and nonzero on `u` because `⟪u_j, u_j⟫` is smooth and strictly positive there. -/
theorem contMDiffOn_gramSchmidtFrame (hX : IsLocalIndepOn IB F n X u) (j : ι) :
    ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (gramSchmidtFrame X j)) u := by
  have hu := contMDiffOn_gramSchmidtFrameAux hX j
  have hq : ContMDiffOn IB 𝓘(ℝ, ℝ) n
      (fun x => ⟪gramSchmidtFrameAux X j x, gramSchmidtFrameAux X j x⟫_ℝ) u :=
    hu.inner_bundle hu
  -- `x ↦ ‖u_j x‖⁻¹` is smooth on `u`: a positive smooth function under a square root
  have hnorm : ContMDiffOn IB 𝓘(ℝ, ℝ) n (fun x => (‖gramSchmidtFrameAux X j x‖ : ℝ)⁻¹) u := by
    have hsqrt : ContMDiffOn IB 𝓘(ℝ, ℝ) n
        (fun x => Real.sqrt ⟪gramSchmidtFrameAux X j x, gramSchmidtFrameAux X j x⟫_ℝ) u := by
      intro x hx
      exact ContDiffAt.comp_contMDiffWithinAt (g := Real.sqrt)
        (f := fun y => ⟪gramSchmidtFrameAux X j y, gramSchmidtFrameAux X j y⟫_ℝ)
        (Real.contDiffAt_sqrt (gramSchmidtFrameAux_inner_self_pos hX hx j).ne') (hq x hx)
    refine (hsqrt.inv₀ fun x hx => ?_).congr fun x hx => ?_
    · exact Real.sqrt_ne_zero'.2 (gramSchmidtFrameAux_inner_self_pos hX hx j)
    · rw [norm_eq_sqrt_real_inner]
  refine (hnorm.smul_section hu).congr fun x hx => ?_
  exact congrArg (TotalSpace.mk' F x) rfl

/-- The fibrewise Gram-Schmidt orthonormalization of a pointwise linearly independent family of
smooth sections is again one — the form of Lee's Proposition 2.8 that survives dropping the
spanning condition, and the one §2.3 uses on the `n` tangent directions inside the
`m`-dimensional ambient fibre. -/
theorem isLocalIndepOn_gramSchmidtFrame (hX : IsLocalIndepOn IB F n X u) :
    IsLocalIndepOn IB F n (gramSchmidtFrame X) u where
  linearIndependent hx := gramSchmidtFrame_linearIndependent hX hx
  contMDiffOn j := contMDiffOn_gramSchmidtFrame hX j

/-- **Lee's Proposition 2.8 for a Riemannian vector bundle**: the fibrewise
Gram-Schmidt orthonormalization of a smooth local frame is again a smooth local
frame on the same set. -/
theorem isLocalFrameOn_gramSchmidtFrame (hX : IsLocalFrameOn IB F n X u) :
    IsLocalFrameOn IB F n (gramSchmidtFrame X) u where
  linearIndependent hx := gramSchmidtFrame_linearIndependent hX.isLocalIndepOn hx
  generating := fun {x} hx => by
    have hspan : span ℝ (Set.range (fun j => gramSchmidtFrame X j x))
        = span ℝ (Set.range (fun j => X j x)) := by
      simpa only [gramSchmidtFrame] using
        (span_gramSchmidtNormed_range (𝕜 := ℝ) (fun i => X i x)).trans
          (span_gramSchmidt ℝ (fun i => X i x))
    rw [hspan]
    exact hX.generating hx
  contMDiffOn j := contMDiffOn_gramSchmidtFrame hX.isLocalIndepOn j

end BundleFrame

section TangentFrame

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι] [WellFoundedLT ι]

/-- **Existence of orthonormal frames** (Lee, Proposition 2.8).

If `(X_i)` is any smooth local frame for `TM` over an open subset `U ⊆ M`, then
there is a smooth orthonormal frame `(E_j)` over `U` such that

  `span (E_1|_p, …, E_k|_p) = span (X_1|_p, …, X_k|_p)`

for each `k` and each `p ∈ U`.  Orthonormality is stated through `g` itself —
`⟨E_i, E_j⟩_g = δ_ij`, Lee's own phrasing — so that using the proposition does
not require the caller to install the fibrewise inner product structure.

Combined with the existence of *some* smooth local frame around any point (a
chart frame), this gives Lee's last sentence: every `p ∈ M` has a neighbourhood
carrying a smooth orthonormal frame. -/
theorem exists_orthonormalFrame (g : RiemannianMetric I M) {X : ι → (x : M) → TangentSpace I x}
    {u : Set M} (hX : IsLocalFrameOn I E ∞ X u) :
    ∃ Y : ι → (x : M) → TangentSpace I x, IsLocalFrameOn I E ∞ Y u ∧
      (∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0) ∧
      (∀ x : M, ∀ k : ι, span ℝ ((fun j => Y j x) '' Set.Iic k)
        = span ℝ ((fun j => X j x) '' Set.Iic k)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  refine ⟨gramSchmidtFrame (V := (TangentSpace I : M → Type _)) X, ?_, ?_, ?_⟩
  · exact isLocalFrameOn_gramSchmidtFrame (IB := I) (F := E)
      (V := (TangentSpace I : M → Type _)) hX
  · intro x hx i j
    have hon := gramSchmidtFrame_orthonormal (IB := I) (F := E)
      (V := (TangentSpace I : M → Type _)) hX.isLocalIndepOn hx
    -- the fibrewise inner product installed by `RiemannianBundle` *is* `g.inner`
    show ⟪gramSchmidtFrame (V := (TangentSpace I : M → Type _)) X i x,
        gramSchmidtFrame (V := (TangentSpace I : M → Type _)) X j x⟫_ℝ = _
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, real_inner_self_eq_norm_sq, hon.1 i, one_pow]
    · rw [if_neg hij]
      exact hon.2 hij
  · intro x k
    exact span_gramSchmidtFrame_Iic (V := (TangentSpace I : M → Type _)) X x k

/-- **Every point has a neighbourhood carrying a smooth orthonormal frame** — the
last sentence of Lee's Proposition 2.8.

The input frame is the one induced on the base set of a tangent-bundle
trivialization around `p` by a basis of the model space `E`; Gram-Schmidt against
`g` then makes it orthonormal without shrinking the domain.  Note that no
`(∂_i)` is claimed to be orthonormal — see Lee's warning after the proposition
(`rem:coordinate-frame-warning`): the frame produced here is in general *not* a
coordinate frame. -/
theorem exists_orthonormalFrame_nhds [FiniteDimensional ℝ E] (g : RiemannianMetric I M) (p : M) :
    ∃ (u : Set M) (Y : Fin (finrank ℝ E) → (x : M) → TangentSpace I x),
      IsOpen u ∧ p ∈ u ∧ IsLocalFrameOn I E ∞ Y u ∧
        ∀ x ∈ u, ∀ i j, g.inner x (Y i x) (Y j x) = if i = j then 1 else 0 := by
  set e := trivializationAt E (TangentSpace I) p with he
  have hX : IsLocalFrameOn I E ∞ (e.localFrame (Module.finBasis ℝ E)) e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ (Module.finBasis ℝ E)
  obtain ⟨Y, hY, hon, -⟩ := exists_orthonormalFrame g hX
  exact ⟨e.baseSet, Y, e.open_baseSet, mem_baseSet_trivializationAt E (TangentSpace I) p, hY, hon⟩

end TangentFrame

end LeeLib.Ch02

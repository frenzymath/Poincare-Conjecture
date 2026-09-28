/-
Chapter 2, "Riemannian Metrics", §"Riemannian Submersions", **Theorem 2.28**.

Lee: *let `(M, g)` be a Riemannian manifold, `π : M → M'` a surjective smooth
submersion, and `G` a group acting on `M`.  If the action is isometric, vertical,
and transitive on fibres, then there is a unique Riemannian metric on `M'` making
`π` a Riemannian submersion.*

This is the hub of the section: Lee's Corollary 2.29 (quotient by a free proper
isometric Lie group action), Example 2.30 (the Fubini–Study metric), and
Propositions 2.31/2.32 (Riemannian coverings) all reduce to it.  Lee defers the
proof to Problem 2-6.

## The construction

The metric on `M'` can only be `g'_y(u, v) = g_x(L_x u, L_x v)` for `x` any point
of the fibre over `y`, where `L_x` is the horizontal lift of
`LeeLib.Ch02.horizontalLiftAt` — that is forced, and is exactly what
`isRiemannianSubmersion_unique` below says.  Three things must then be checked.

* **Well-definedness.**  Two points of a fibre differ by some `a ∈ G`.  Since the
  action is vertical, `dπ ∘ d(a • ·) = dπ`, so `d(a • ·)` carries `V_x` onto
  `V_{a • x}` (using the inverse `a⁻¹` for surjectivity) and hence `H_x` onto
  `H_{a • x}`; since it also preserves `g`, it carries `L_x` to `L_{a • x}`.
  `submersionInner_smul` is this step, and it is the only place the group
  hypotheses are used.

* **Positive definiteness.**  `L_x` is injective (it is a right inverse of `dπ_x`),
  so `g_x(L_x u, L_x u) > 0` for `u ≠ 0`.

* **Smoothness.**  This is what needs `LeeLib.AppendixA.exists_localSection`:
  near `y₀`, choose a smooth local section `σ` of `π`, and then
  `g'_y = g_{σ y}(L_{σ y} ·, L_{σ y} ·)` by well-definedness, which is smooth
  because `σ` is smooth and `contMDiffAt_horizontalLift` says the lift depends
  smoothly on the data.  Without a local section there is no way to choose the
  fibre point smoothly, and mathlib has no rank theorem — hence Appendix A.17.

## Relation to the sibling projects

`PetersenLib.homogeneousQuotientMetric` (Petersen `Ch01/HomogeneousMetrics.lean`)
is the same theorem, and the proof strategy here is ported from it.  It cannot be
imported: cross-project `lake` dependencies are banned in this workspace, so each
project vendors its own copy.  Two things differ.  Lee's `horizontalLiftAt` is a
*formula* (`B⁻¹Aᵗ(AB⁻¹Aᵗ)⁻¹`) with a uniqueness characterisation, where
Petersen's horizontal lift is existential, so the well-definedness step here goes
through `horizontalLiftAt_unique` rather than a hand-rolled cancellation.  And
Lee's local section theorem needs only the *source* model to be boundaryless,
so `I'.Boundaryless` is not assumed here.
-/
import LeeLib.AppendixA.LocalSection
import LeeLib.Ch02.PullbackMetric
import LeeLib.Ch02.RiemannianSubmersion

namespace LeeLib.Ch02

open Set Filter
open Manifold
open scoped Manifold ContDiff Topology

section Defs

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Riemannian submersion** (Lee, §"Riemannian Submersions"): a smooth
submersion `π` such that `dπ_x` restricts to a linear isometry from `H_x` onto
`T_{π x}M'`.

Surjectivity of `dπ_x|_{H_x}` is automatic from `IsSubmersion` together with
`horizontalSpace_eq_range`, so only the isometry condition is recorded, in the
form Lee states it: `g_x(v, w) = g'_{π x}(dπ_x v, dπ_x w)` for horizontal
`v, w`. -/
def IsRiemannianSubmersion (g : RiemannianMetric I M) (g' : RiemannianMetric I' M')
    (π : C^∞⟮I, M; I', M'⟯) : Prop :=
  IsSubmersion π ∧
    ∀ (x : M) (v w : TangentSpace I x), v ∈ horizontalSpace g π x →
      w ∈ horizontalSpace g π x →
        g'.inner (π x) (mfderiv I I' π x v) (mfderiv I I' π x w) = g.inner x v w

/-- **The inner product a Riemannian submersion must have on the base.**  For
`u, v ∈ T_{π x}M'` this is `g_x(L_x u, L_x v)`, the metric of the horizontal
lifts at `x`.  Theorem 2.28 is the statement that this is independent of the
choice of `x` in the fibre, and smooth. -/
noncomputable def submersionInner (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯) (x : M) :
    TangentSpace I' (π x) →L[ℝ] TangentSpace I' (π x) →L[ℝ] ℝ :=
  -- `TangentSpace` carries no norm, so both types must be pinned to the model spaces,
  -- for which they are definitionally equal; this is the `pullbackForm` idiom.
  let L : E' →L[ℝ] E := horizontalLiftAt g π x
  let B : E →L[ℝ] E →L[ℝ] ℝ := g.inner x
  (B.bilinearComp L L : E' →L[ℝ] E' →L[ℝ] ℝ)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
@[simp]
theorem submersionInner_apply (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯) (x : M)
    (u v : TangentSpace I' (π x)) :
    submersionInner g π x u v = g.inner x (horizontalLiftAt g π x u) (horizontalLiftAt g π x v) :=
  rfl

/-- A Riemannian submersion's base metric *is* `submersionInner`: on horizontal
vectors `dπ_x` is inverted by `L_x`. -/
theorem IsRiemannianSubmersion.inner_eq {g : RiemannianMetric I M} {g' : RiemannianMetric I' M'}
    {π : C^∞⟮I, M; I', M'⟯} (h : IsRiemannianSubmersion g g' π) (x : M) :
    g'.inner (π x) = submersionInner g π x := by
  ext u v
  rw [submersionInner_apply,
    ← h.2 x _ _ (horizontalLiftAt_mem g π x u) (horizontalLiftAt_mem g π x v),
    mfderiv_horizontalLiftAt g π h.1 x u, mfderiv_horizontalLiftAt g π h.1 x v]

/-- **Lee, Theorem 2.28, uniqueness half**: *a surjective submersion is a
Riemannian submersion for at most one metric on the base.*

No group action is needed: the value of `g'` at `π x` is forced to be
`submersionInner g π x`, because every tangent vector upstairs of `π x` is
`dπ_x` of its horizontal lift. -/
theorem isRiemannianSubmersion_unique {g : RiemannianMetric I M}
    {g₁ g₂ : RiemannianMetric I' M'} {π : C^∞⟮I, M; I', M'⟯}
    (h₁ : IsRiemannianSubmersion g g₁ π) (h₂ : IsRiemannianSubmersion g g₂ π)
    (hsurj : Function.Surjective π) : g₁ = g₂ := by
  refine RiemannianMetric.ext_inner fun y => ?_
  obtain ⟨x, rfl⟩ := hsurj y
  rw [h₁.inner_eq x, h₂.inner_eq x]

end Defs

/-! ## The group action

Lee's hypotheses on the `G`-action, stated separately as he states them.  The
action enters the proof only through `submersionInner_smul`: it is what makes the
inner product on the base independent of the chosen point of the fibre. -/

section Action

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {G : Type*} [Group G] [MulAction G M]

variable (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯)

/-- **The action is by isometries** (Lee, §"Riemannian Submersions"): each
`x ↦ a • x` is smooth and its differential preserves `g`.

Lee phrases this as "the map `x ↦ φ · x` is an isometry for each `φ ∈ G`".  Being
a group action by smooth maps, each `a • ·` is automatically a diffeomorphism
(with inverse `a⁻¹ • ·`), so no invertibility need be assumed — it is derived in
`IsIsometricAction.mfderiv_smul_inv_smul`. -/
structure IsIsometricAction : Prop where
  /-- Each group element acts smoothly. -/
  contMDiff : ∀ a : G, ContMDiff I I ∞ (fun x : M => a • x)
  /-- Each group element preserves the metric. -/
  inner_smul : ∀ (a : G) (x : M) (v w : TangentSpace I x),
    g.inner (a • x) (mfderiv I I (fun y : M => a • y) x v)
      (mfderiv I I (fun y : M => a • y) x w) = g.inner x v w

/-- **The action is vertical** (Lee): every element takes each fibre to itself. -/
def IsVerticalAction : Prop := ∀ (a : G) (x : M), π (a • x) = π x

/-- **The action is transitive on fibres** (Lee). -/
def IsFibreTransitiveAction : Prop := ∀ x y : M, π x = π y → ∃ a : G, a • x = y

variable {g π}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- Each `a • ·` is `MDifferentiable`. -/
theorem IsIsometricAction.mdifferentiableAt (h : IsIsometricAction (G := G) g) (a : G) (x : M) :
    MDifferentiableAt I I (fun y : M => a • y) x :=
  (h.contMDiff a x).mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- **The differentials of `a • ·` and `a⁻¹ • ·` are mutually inverse.**  This is
the chain rule applied to `(a • ·) ∘ (a⁻¹ • ·) = id`, and it is what makes
`d(a • ·)` carry `V_x` *onto* `V_{a • x}` rather than merely into it. -/
theorem IsIsometricAction.mfderiv_smul_inv_smul (h : IsIsometricAction (G := G) g) (a : G) (x : M)
    (w : TangentSpace I (a • x)) :
    mfderiv I I (fun y : M => a • y) x
        (mfderiv I I (fun y : M => a⁻¹ • y) (a • x) w) = w := by
  have hcomp : ((fun y : M => a • y) ∘ (fun y : M => a⁻¹ • y)) = id :=
    funext fun y => smul_inv_smul a y
  have h1 := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := I) (x := a • x)
    (g := fun y : M => a • y) (f := fun y : M => a⁻¹ • y)
    (h.mdifferentiableAt a x) (h.mdifferentiableAt a⁻¹ (a • x)) (inv_smul_smul a x) w
  rw [← h1, hcomp, mfderiv_id]
  rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- **The differential of `π` absorbs the differential of the action**:
`dπ_{a • x} ∘ d(a • ·)_x = dπ_x`, because `π ∘ (a • ·) = π`. -/
theorem mfderiv_comp_smul (h : IsIsometricAction (G := G) g) (hvert : IsVerticalAction π (G := G))
    (a : G) (x : M) (v : TangentSpace I x) :
    mfderiv I I' π (a • x) (mfderiv I I (fun y : M => a • y) x v) = mfderiv I I' π x v := by
  have hcomp : ((fun y : M => π y) ∘ (fun y : M => a • y)) = fun y : M => π y :=
    funext fun y => hvert a y
  have hπd : ∀ z : M, MDifferentiableAt I I' (fun y : M => π y) z :=
    fun z => (π.contMDiff z).mdifferentiableAt (by simp)
  have h1 := mfderiv_comp_apply (I := I) (I' := I) (I'' := I') (x := x)
    (g := fun y : M => π y) (f := fun y : M => a • y)
    (hπd (a • x)) (h.mdifferentiableAt a x) v
  rw [← h1, hcomp]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- `d(a • ·)_x` carries the vertical space at `x` onto the vertical space at
`a • x`: this is `mfderiv_comp_smul` for `⊆`, and the inverse action for `⊇`. -/
theorem verticalSpace_smul_surj (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (a : G) (x : M)
    {w : TangentSpace I (a • x)} (hw : w ∈ verticalSpace π (a • x)) :
    ∃ z ∈ verticalSpace π x, mfderiv I I (fun y : M => a • y) x z = w := by
  refine ⟨mfderiv I I (fun y : M => a⁻¹ • y) (a • x) w, ?_, h.mfderiv_smul_inv_smul a x w⟩
  rw [mem_verticalSpace_iff]
  rw [← mfderiv_comp_smul h hvert a x (mfderiv I I (fun y : M => a⁻¹ • y) (a • x) w),
    h.mfderiv_smul_inv_smul a x w]
  exact hw

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- `d(a • ·)_x` carries horizontal vectors to horizontal vectors: it preserves
`g` and carries `V_x` onto `V_{a • x}`. -/
theorem horizontalSpace_smul (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (a : G) (x : M)
    {v : TangentSpace I x} (hv : v ∈ horizontalSpace g π x) :
    mfderiv I I (fun y : M => a • y) x v ∈ horizontalSpace g π (a • x) := by
  intro w hw
  obtain ⟨z, hz, rfl⟩ := verticalSpace_smul_surj h hvert a x hw
  rw [h.inner_smul a x v z]
  exact hv z hz

omit [IsManifold I' ∞ M'] in
/-- **Well-definedness of the quotient inner product** — the mathematical heart of
Lee's Theorem 2.28.

`d(a • ·)_x` carries `L_x` to `L_{a • x}` (by the uniqueness of the horizontal
lift), and it preserves `g`, so the inner product of horizontal lifts is the same
at `x` and at `a • x`.  Both sides are stated at the model space `E'`, to which
`TangentSpace I' (π (a • x))` and `TangentSpace I' (π x)` are definitionally
equal — `hvert` makes them propositionally equal but not syntactically so. -/
theorem submersionInner_smul (hπ : IsSubmersion π) (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (a : G) (x : M) :
    ((submersionInner g π (a • x) : _) : E' →L[ℝ] E' →L[ℝ] ℝ)
      = ((submersionInner g π x : _) : E' →L[ℝ] E' →L[ℝ] ℝ) := by
  -- `L_{a • x} = d(a • ·)_x ∘ L_x`, by uniqueness of the horizontal lift at `a • x`.
  have key : ∀ u : E', ((horizontalLiftAt g π (a • x) u : _) : E)
      = mfderiv I I (fun y : M => a • y) x (horizontalLiftAt g π x u) := by
    have huniq := (horizontalLiftAt_unique g π hπ (a • x)
      (L := ((mfderiv I I (fun y : M => a • y) x : _) : E →L[ℝ] E).comp
        ((horizontalLiftAt g π x : _) : E' →L[ℝ] E))
      (fun u => by
        show mfderiv I I' π (a • x)
          (mfderiv I I (fun y : M => a • y) x (horizontalLiftAt g π x u)) = u
        rw [mfderiv_comp_smul h hvert a x]
        exact mfderiv_horizontalLiftAt g π hπ x u)
      (fun u => horizontalSpace_smul h hvert a x (horizontalLiftAt_mem g π x u))).symm
    exact fun u => congrArg (fun L => L u) huniq
  ext u v
  show g.inner (a • x) (horizontalLiftAt g π (a • x) u) (horizontalLiftAt g π (a • x) v)
    = g.inner x (horizontalLiftAt g π x u) (horizontalLiftAt g π x v)
  rw [show (horizontalLiftAt g π (a • x) u : TangentSpace I (a • x))
        = mfderiv I I (fun y : M => a • y) x (horizontalLiftAt g π x u) from key u,
    show (horizontalLiftAt g π (a • x) v : TangentSpace I (a • x))
        = mfderiv I I (fun y : M => a • y) x (horizontalLiftAt g π x v) from key v]
  exact h.inner_smul a x _ _

end Action

/-! ## Theorem 2.28: existence of the quotient metric

Everything above is in place: `submersionInner` is the only candidate
(`isRiemannianSubmersion_unique`), and `submersionInner_smul` says it does not
depend on which point of the fibre computes it.  What remains is to turn that
into a `RiemannianMetric` on `M'` — to choose a point in each fibre, and to check
that the resulting field is symmetric, positive definite and *smooth*.

The choice is `Function.surjInv`, which is where surjectivity of `π` is used; the
choice is harmless precisely by `submersionInner_congr`.  Smoothness is the only
analytic step, and it is the reason Appendix A.17 exists: `surjInv` is not
smooth — it is not even continuous — so it cannot be differentiated.  Instead one
replaces it, *near each point*, by a smooth local section `σ`, which represents
the same field because the fibre point does not matter, and then

  `g'_y = g_{σ y}(L_{σ y} ·, L_{σ y} ·)`

is a composite of smooth things: `σ` is smooth, `g` is a smooth 2-tensor field,
and `x ↦ L_x` is smooth in tangent coordinates
(`contMDiffAt_horizontalLiftAt_inTangentCoordinates`).  Assembling those three is
`contMDiffAt_bilinearCompOf`, whose generality — an *arbitrary* smooth family of
linear maps rather than a differential — exists exactly for this: `L` is not the
differential of any map.

`I.Boundaryless` is inherited from `LeeLib.AppendixA.exists_localSection`, and is
needed only upstairs; `M'` may have boundary. -/

section Existence

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  {G : Type*} [Group G] [MulAction G M]

variable {g : RiemannianMetric I M} {π : C^∞⟮I, M; I', M'⟯}

omit [I.Boundaryless] [IsManifold I' ∞ M'] in
/-- **`β` is constant on the fibres of `π`** — Theorem 2.28's well-definedness
step, restated for two arbitrary points of a fibre rather than for a group
translate.  This is `submersionInner_smul` plus transitivity on fibres. -/
theorem submersionInner_congr (hπ : IsSubmersion π) (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (htrans : IsFibreTransitiveAction π (G := G))
    {x y : M} (hxy : π x = π y) :
    ((submersionInner g π y : _) : E' →L[ℝ] E' →L[ℝ] ℝ)
      = ((submersionInner g π x : _) : E' →L[ℝ] E' →L[ℝ] ℝ) := by
  obtain ⟨a, rfl⟩ := htrans x y hxy
  exact submersionInner_smul hπ h hvert a x

omit [I.Boundaryless] [IsManifold I' ∞ M'] in
/-- `β_x` is positive definite: `L_x` is injective, being a right inverse of `dπ_x`. -/
theorem submersionInner_pos (hπ : IsSubmersion π) (x : M) (u : TangentSpace I' (π x))
    (hu : u ≠ 0) : 0 < submersionInner g π x u u := by
  rw [submersionInner_apply]
  refine g.pos x _ fun hL => hu ?_
  have hmf := mfderiv_horizontalLiftAt g π hπ x u
  rw [hL, map_zero] at hmf
  exact hmf.symm

variable (g π) in
/-- **The quotient inner product on the base.**  `β_x` for `x` the point of the
fibre over `y` selected by `Function.surjInv`.

The selection is an arbitrary choice with no regularity whatsoever, and that is
fine: `quotientInner_eq_submersionInner` says *any* point of the fibre computes
the same form, so the choice never has to be differentiated. -/
noncomputable def quotientInner (hsurj : Function.Surjective π) (y : M') :
    TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ :=
  ((submersionInner g π (Function.surjInv hsurj y) : _) : E' →L[ℝ] E' →L[ℝ] ℝ)

omit [I.Boundaryless] [IsManifold I' ∞ M'] in
/-- **The choice of fibre point does not matter**: `g'_{π x} = β_x` for *every*
`x`, not just for the selected one. -/
theorem quotientInner_eq_submersionInner (hπ : IsSubmersion π) (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (htrans : IsFibreTransitiveAction π (G := G))
    (hsurj : Function.Surjective π) {x : M} {y : M'} (hx : π x = y) :
    ((quotientInner g π hsurj y : _) : E' →L[ℝ] E' →L[ℝ] ℝ)
      = ((submersionInner g π x : _) : E' →L[ℝ] E' →L[ℝ] ℝ) :=
  submersionInner_congr hπ h hvert htrans
    (show π x = π (Function.surjInv hsurj y) by rw [Function.surjInv_eq hsurj y]; exact hx)

omit [FiniteDimensional ℝ E] [I.Boundaryless] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The quotient inner product is symmetric, inherited from `g`. -/
theorem quotientInner_symm (hsurj : Function.Surjective π) (y : M')
    (u v : TangentSpace I' y) :
    quotientInner g π hsurj y u v = quotientInner g π hsurj y v u :=
  g.symm _ _ _

omit [I.Boundaryless] [IsManifold I' ∞ M'] in
/-- The quotient inner product is positive definite, by `submersionInner_pos`. -/
theorem quotientInner_pos (hπ : IsSubmersion π) (hsurj : Function.Surjective π) (y : M')
    (u : TangentSpace I' y) (hu : u ≠ 0) : 0 < quotientInner g π hsurj y u u :=
  submersionInner_pos hπ (Function.surjInv hsurj y) u hu

/-- **Theorem 2.28, the analytic step: the quotient inner product is smooth.**

Fix `y₀` and a point `x₀` of its fibre.  `LeeLib.AppendixA.exists_localSection`
gives a section `σ` of `π` smooth at `y₀` with `σ y₀ = x₀`.  For `y` near `y₀`
we have `π (σ y) = y`, so `quotientInner_eq_submersionInner` rewrites the field
as `y ↦ g_{σ y}(L_{σ y} ·, L_{σ y} ·)` there — and *that* is smooth by
`contMDiffAt_bilinearCompOf`, applied with the local section as the base map and
the horizontal lift as the transporting family. -/
theorem contMDiff_quotientInner (hπ : IsSubmersion π) (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (htrans : IsFibreTransitiveAction π (G := G))
    (hsurj : Function.Surjective π) :
    ContMDiff I' (I'.prod 𝓘(ℝ, E' →L[ℝ] E' →L[ℝ] ℝ)) ∞
      (fun y => (⟨y, quotientInner g π hsurj y⟩ :
        Bundle.TotalSpace (E' →L[ℝ] E' →L[ℝ] ℝ)
          (fun y => TangentSpace I' y →L[ℝ] TangentSpace I' y →L[ℝ] ℝ))) := by
  intro y₀
  obtain ⟨x₀, hx₀⟩ := hsurj y₀
  obtain ⟨σ, hσ, hσx, hσπ⟩ := LeeLib.AppendixA.exists_localSection (I := I) (I' := I')
    (f := fun x => π x) π.contMDiff (x := x₀) (hπ x₀)
  rw [hx₀] at hσ hσx hσπ
  -- `L` along the section, as a family of maps `T_y M' → T_{σ y} M` covering `σ`.
  have hA : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E) ∞
      (inTangentCoordinates I' I id σ
        (fun y : M' => ((horizontalLiftAt g π (σ y) : _) : E' →L[ℝ] E)) y₀) y₀ := by
    have hcomp : ContMDiffAt I' 𝓘(ℝ, E' →L[ℝ] E) ∞
        (fun y => inTangentCoordinates I' I (fun x => π x) id
          (fun x => horizontalLiftAt g π x) x₀ (σ y)) y₀ :=
      ContMDiffAt.comp_of_eq (I := I') (I' := I) (I'' := 𝓘(ℝ, E' →L[ℝ] E))
        (contMDiffAt_horizontalLiftAt_inTangentCoordinates g π hπ x₀) hσ hσx
    refine hcomp.congr_of_eventuallyEq ?_
    filter_upwards [hσπ] with y hy
    simp only [inTangentCoordinates, id_eq, hx₀, hσx]
    -- `π (σ y) = y` cannot be rewritten by `simp`: it occurs as the base point of the
    -- source fibre, so the rewrite is dependent.  It is harmless because `TangentSpace I' p`
    -- is defeq to `E'` for *every* `p`, which is exactly what makes this motive type-correct.
    exact congrArg (fun p : M' => ContinuousLinearMap.inCoordinates E' (TangentSpace I') E
      (TangentSpace I) y₀ p x₀ (σ y) (horizontalLiftAt g π (σ y))) hy.symm
  refine (contMDiffAt_bilinearCompOf (I := I') (I' := I) (fun x : M => g.inner x)
    g.contMDiff hσ
    (fun y : M' => ((horizontalLiftAt g π (σ y) : _) :
      TangentSpace I' y →L[ℝ] TangentSpace I (σ y))) hA).congr_of_eventuallyEq ?_
  filter_upwards [hσπ] with y hy
  exact congrArg (Bundle.TotalSpace.mk y)
    (quotientInner_eq_submersionInner hπ h hvert htrans hsurj hy)

variable (g π) in
/-- **The quotient metric** of Lee's Theorem 2.28: the unique Riemannian metric on
the base making `π` a Riemannian submersion. -/
noncomputable def quotientMetric (hπ : IsSubmersion π) (h : IsIsometricAction (G := G) g)
    (hvert : IsVerticalAction π (G := G)) (htrans : IsFibreTransitiveAction π (G := G))
    (hsurj : Function.Surjective π) : RiemannianMetric I' M' where
  inner y := quotientInner g π hsurj y
  symm y u v := quotientInner_symm hsurj y u v
  pos y u hu := quotientInner_pos hπ hsurj y u hu
  isVonNBounded y :=
    isVonNBounded_of_posDef (F := E') (quotientInner g π hsurj y)
      (fun u hu => quotientInner_pos hπ hsurj y u hu)
  contMDiff := contMDiff_quotientInner hπ h hvert htrans hsurj

/-- The quotient metric does make `π` a Riemannian submersion: on horizontal
vectors `L_x` inverts `dπ_x`, so `g'_{π x}(dπ_x v, dπ_x w) = β_x(dπ_x v, dπ_x w)
= g_x(v, w)`. -/
theorem isRiemannianSubmersion_quotientMetric (hπ : IsSubmersion π)
    (h : IsIsometricAction (G := G) g) (hvert : IsVerticalAction π (G := G))
    (htrans : IsFibreTransitiveAction π (G := G)) (hsurj : Function.Surjective π) :
    IsRiemannianSubmersion g (quotientMetric g π hπ h hvert htrans hsurj) π := by
  refine ⟨hπ, fun x v w hv hw => ?_⟩
  show quotientInner g π hsurj (π x) (mfderiv I I' π x v) (mfderiv I I' π x w) = g.inner x v w
  have hq := quotientInner_eq_submersionInner hπ h hvert htrans hsurj (x := x) rfl
  rw [show (quotientInner g π hsurj (π x) : TangentSpace I' (π x) →L[ℝ] _)
      = submersionInner g π x from hq, submersionInner_apply,
    horizontalLiftAt_mfderiv_of_mem g π hπ hv, horizontalLiftAt_mfderiv_of_mem g π hπ hw]

/-- **Lee, Theorem 2.28.**  *Let `(M, g)` be a Riemannian manifold, `π : M → M'` a
surjective smooth submersion, and `G` a group acting on `M`.  If the action is
isometric, vertical and transitive on fibres, then there is a unique Riemannian
metric on `M'` making `π` a Riemannian submersion.*

Existence is `quotientMetric`; uniqueness is `isRiemannianSubmersion_unique`, and
needs no group action. -/
theorem existsUnique_isRiemannianSubmersion_metric (hπ : IsSubmersion π)
    (h : IsIsometricAction (G := G) g) (hvert : IsVerticalAction π (G := G))
    (htrans : IsFibreTransitiveAction π (G := G)) (hsurj : Function.Surjective π) :
    ∃! g' : RiemannianMetric I' M', IsRiemannianSubmersion g g' π :=
  ⟨quotientMetric g π hπ h hvert htrans hsurj,
    isRiemannianSubmersion_quotientMetric hπ h hvert htrans hsurj,
    fun _ hg' => isRiemannianSubmersion_unique hg'
      (isRiemannianSubmersion_quotientMetric hπ h hvert htrans hsurj) hsurj⟩

end Existence

end LeeLib.Ch02

/-
Chapter 2, "Riemannian Metrics", §"Riemannian Submersions".

Let `π : M → M'` be a smooth submersion and `g` a Riemannian metric on `M`.
Lee defines, at each `x ∈ M`, the **vertical** tangent space `V x = ker dπ_x`
(the tangent space to the fibre through `x`, which needs no metric) and the
**horizontal** tangent space `H x = (V x)^⊥` (which does).  He then records, as
Proposition 2.25, the three facts that make the theory usable:

* (a) every smooth vector field `W` on `M` splits uniquely as `W = W^H + W^V`
  with `W^H` horizontal, `W^V` vertical, and both smooth;
* (b) every smooth vector field on `M'` has a unique smooth horizontal lift;
* (c) every horizontal vector at a point is the value there of such a lift.

This file develops the pointwise content of all three, and then proves (b) in
full, smoothness included.

The pointwise half is the two subspaces, their complementarity
`T_x M = H_x ⊕ V_x`, the projections `W ↦ W^H` and `W ↦ W^V`, and the horizontal
lift of a single tangent vector characterized as the unique horizontal right
inverse of `dπ_x`.

The smoothness half is the assertion that the horizontal distribution
`x ↦ (ker dπ_x)^⊥` varies smoothly, and it is what
`LeeLib.Ch02.contDiffAt_horizontalLift` was set up to supply.  It is carried out
in the last two sections: `contMDiffAt_horizontalLift` ports that lemma from a
normed-space parameter to a manifold one, and `contMDiffAt_horizontalLiftField`
feeds it the metric and the differential read in local trivializations, giving
Lee's Proposition 2.25(b) as `exists_unique_horizontalLift`.

What is *not* done here is the smoothness half of (a) — that `W^H` and `W^V` are
smooth for a smooth `W` on the total space.  The same trivialization argument
applies (the extra ingredient being that `x ↦ dπ_x (W x)` is smooth in
coordinates), but it is not written.  Part (c) is likewise complete only
pointwise (`horizontalLiftAt_mfderiv_of_mem`); the remaining step is to extend a
single tangent vector `dπ_x v` to a vector field on `M'`.

## The submersion hypothesis

Mathlib has no notion of submersion at all: a grep over the pinned
`Mathlib/Geometry/` finds `IsImmersionAt` (whose `mfderiv` API is entirely TODO)
and nothing else — no regular value theorem, no constant rank theorem, no local
normal form.  So `IsSubmersion` is defined here, directly as surjectivity of
every differential, which is the form Lee actually uses and the form the
horizontal lift needs.  This mirrors the house style of
`LeeLib.Ch02.NormalBundle`, which carries injectivity of `mfderiv` as its
immersion hypothesis for the same reason.

Consequently the fibres are *not* known here to be embedded submanifolds (that
is Lee's appeal to the submersion level set theorem, Corollary A.25), and
`verticalSpace` is defined as `ker dπ_x` rather than as the tangent space to the
fibre.  The two agree, and only the kernel is used below.

## Design

`horizontalSpace` is spelled by the vanishing condition `⟪v, w⟫ = 0` for every
vertical `w`, through `g` itself, rather than as `(verticalSpace π x)ᗮ` — the
same choice `LeeLib.Ch02.NormalBundle.normalSpace` makes, and for the same
reason: `ᗮ` would force every statement to mention the `RiemannianBundle`
instance that installs the fibrewise inner product, whereas the `g`-form needs
no instance at all.

`TangentSpace I x` carries no `NormedAddCommGroup` instance — mathlib withholds
one deliberately, since a norm on the tangent space is exactly the choice of a
metric, and supplying one would create a diamond with `RiemannianBundle`.  But
`LeeLib.Ch02.horizontalLift` needs the model space to be a finite-dimensional
normed space.  The two are reconciled by the definitional equality
`TangentSpace I x = E` (the same "abuse of definitional equality" mathlib itself
relies on in `NormedSpace.fromTangentSpace`): every application of a
`horizontalLift` lemma below pins `(E := E) (E' := E')` so that unification
cannot instead pick `TangentSpace I x`, for which the normed instances do not
exist.  Dropping a pin does not give a wrong theorem, it gives an instance
synthesis failure.
-/
import LeeLib.Ch02.HorizontalLift
import LeeLib.Ch02.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace LeeLib.Ch02

-- `Bundle` is deliberately *not* opened: its scoped `π` notation for the bundle
-- projection would shadow Lee's name for the submersion itself.
open Manifold
open scoped Manifold ContDiff

section Pointwise

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Smooth submersion** (Lee, §"Riemannian Submersions"): a smooth map whose
differential is surjective at every point.

Mathlib has no submersion predicate, so this is stated directly in the form Lee
uses.  Note this is the pointwise-surjectivity definition, not a chart normal
form; the two agree, but only the former is available here, since mathlib has no
constant rank theorem. -/
def IsSubmersion (π : C^∞⟮I, M; I', M'⟯) : Prop :=
  ∀ x : M, Function.Surjective (mfderiv I I' π x)

variable (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯)

/-- **The vertical tangent space** `V_x = ker dπ_x` (Lee, §"Riemannian
Submersions"): the tangent space to the fibre through `x`.  It is well defined
for every submersion, because it does not refer to the metric. -/
noncomputable def verticalSpace (x : M) : Submodule ℝ (TangentSpace I x) :=
  LinearMap.ker (mfderiv I I' π x : TangentSpace I x →ₗ[ℝ] TangentSpace I' (π x))

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
@[simp] theorem mem_verticalSpace_iff {x : M} {v : TangentSpace I x} :
    v ∈ verticalSpace π x ↔ mfderiv I I' π x v = 0 := Iff.rfl

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [FiniteDimensional ℝ E']
  [IsManifold I' ∞ M'] in
/-- **The fibres of an equidimensional submersion are discrete**, infinitesimally:
if `dπ_x` is injective there is nothing to be tangent to a fibre.  This is the
pointwise reason a Riemannian submersion between manifolds of the same dimension
is a local isometry. -/
theorem verticalSpace_eq_bot {x : M} (hinj : Function.Injective (mfderiv I I' π x)) :
    verticalSpace π x = ⊥ := by
  ext v
  simp only [mem_verticalSpace_iff, Submodule.mem_bot]
  refine ⟨fun hv => hinj (by simpa using hv), ?_⟩
  rintro rfl
  simp

/-- **The horizontal tangent space** `H_x = (V_x)^⊥` (Lee, §"Riemannian
Submersions"): the orthogonal complement of the vertical space.  Unlike the
vertical space, it depends on the metric. -/
def horizontalSpace (x : M) : Submodule ℝ (TangentSpace I x) where
  carrier := {v | ∀ w ∈ verticalSpace π x, g.inner x v w = 0}
  add_mem' := fun ha hb w hw => by simp [ha w hw, hb w hw]
  zero_mem' := fun w _ => by simp
  smul_mem' := fun c _ ha w hw => by simp [ha w hw]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
theorem mem_horizontalSpace_iff {x : M} {v : TangentSpace I x} :
    v ∈ horizontalSpace g π x ↔ ∀ w ∈ verticalSpace π x, g.inner x v w = 0 := Iff.rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- **Everything is horizontal when `dπ_x` is injective.**  Horizontality is a
condition against the vertical space, and by `verticalSpace_eq_bot` there is none. -/
theorem horizontalSpace_eq_top {x : M} (hinj : Function.Injective (mfderiv I I' π x)) :
    horizontalSpace g π x = ⊤ := by
  ext v
  simp only [Submodule.mem_top, iff_true, mem_horizontalSpace_iff]
  intro w hw
  rw [verticalSpace_eq_bot π hinj, Submodule.mem_bot] at hw
  subst hw
  simp

omit [FiniteDimensional ℝ E] in
/-- Positive definiteness of `g` at `x`, in the unbundled shape that every lemma
of `LeeLib.Ch02.HorizontalLift` takes as its hypothesis `hB`. -/
theorem inner_pos (x : M) : ∀ v : E, v ≠ 0 → 0 < (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x) v v :=
  fun v hv => g.pos x v hv

/-- **The horizontal lift of a tangent vector** (Lee, §"Riemannian
Submersions"): the unique horizontal preimage of `u` under `dπ_x`.

This is `LeeLib.Ch02.horizontalLift` applied fibrewise with `B = g|_x` and
`A = dπ_x`.  Its two defining properties are `mfderiv_horizontalLiftAt` and
`horizontalLiftAt_mem`, and they characterize it (`horizontalLiftAt_unique`). -/
noncomputable def horizontalLiftAt (x : M) : TangentSpace I' (π x) →L[ℝ] TangentSpace I x :=
  horizontalLift (E := E) (E' := E') (show E →L[ℝ] E →L[ℝ] ℝ from g.inner x)
    (show E →L[ℝ] E' from mfderiv I I' π x)

omit [IsManifold I' ∞ M'] in
/-- The horizontal lift is a right inverse of `dπ_x`: it is `π`-related to `u`. -/
theorem mfderiv_horizontalLiftAt (hπ : IsSubmersion π) (x : M) (u : TangentSpace I' (π x)) :
    mfderiv I I' π x (horizontalLiftAt g π x u) = u :=
  horizontalLift_rightInverse (E := E) (E' := E') (inner_pos g x) (hπ x) u

omit [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The horizontal lift is horizontal. -/
theorem horizontalLiftAt_mem (x : M) (u : TangentSpace I' (π x)) :
    horizontalLiftAt g π x u ∈ horizontalSpace g π x :=
  fun _ hw => horizontalLift_horizontal (E := E) (E' := E') (inner_pos g x) _ u hw

omit [IsManifold I' ∞ M'] in
/-- **The horizontal lift is the unique horizontal right inverse of `dπ_x`.** -/
theorem horizontalLiftAt_unique (hπ : IsSubmersion π) (x : M)
    {L : TangentSpace I' (π x) →L[ℝ] TangentSpace I x}
    (h1 : ∀ u, mfderiv I I' π x (L u) = u)
    (h2 : ∀ u, L u ∈ horizontalSpace g π x) :
    L = horizontalLiftAt g π x :=
  horizontalLift_unique (E := E) (E' := E') (inner_pos g x) (hπ x) h1 fun u _ hw => h2 u _ hw

omit [IsManifold I' ∞ M'] in
/-- **A horizontal vector is recovered from its image**: on `H_x` the lift
inverts `dπ_x`.  This is the pointwise content of Lee's Proposition 2.25(c) —
what remains of (c) is to extend `dπ_x v` to a vector field on `M'`. -/
theorem horizontalLiftAt_mfderiv_of_mem (hπ : IsSubmersion π) {x : M} {v : TangentSpace I x}
    (hv : v ∈ horizontalSpace g π x) :
    horizontalLiftAt g π x (mfderiv I I' π x v) = v :=
  horizontalLift_apply_apply_of_horizontal (E := E) (E' := E') (inner_pos g x) (hπ x)
    fun _ hw => hv _ hw

omit [IsManifold I' ∞ M'] in
/-- `dπ_x` restricts to a bijection `H_x → T_{π x} M'`; this is its injectivity. -/
theorem horizontalSpace_injOn_mfderiv (hπ : IsSubmersion π) {x : M}
    {v w : TangentSpace I x} (hv : v ∈ horizontalSpace g π x) (hw : w ∈ horizontalSpace g π x)
    (h : mfderiv I I' π x v = mfderiv I I' π x w) : v = w := by
  rw [← horizontalLiftAt_mfderiv_of_mem g π hπ hv, ← horizontalLiftAt_mfderiv_of_mem g π hπ hw, h]

omit [IsManifold I' ∞ M'] in
/-- The horizontal space is exactly the range of the horizontal lift. -/
theorem horizontalSpace_eq_range (hπ : IsSubmersion π) (x : M) :
    horizontalSpace g π x = LinearMap.range (horizontalLiftAt g π x).toLinearMap := by
  apply le_antisymm
  · intro v hv
    exact ⟨mfderiv I I' π x v, horizontalLiftAt_mfderiv_of_mem g π hπ hv⟩
  · rintro _ ⟨u, rfl⟩
    exact horizontalLiftAt_mem g π x u

/-! ## The orthogonal splitting `T_x M = H_x ⊕ V_x`

Lee's Proposition 2.25(a), pointwise: every tangent vector splits uniquely as a
horizontal plus a vertical vector.  The projections are `W^H = L_x ∘ dπ_x` and
`W^V = id - W^H`. -/

/-- **The horizontal projection** `W ↦ W^H` (Lee, Proposition 2.25(a)). -/
noncomputable def horizontalProj (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  (horizontalLiftAt g π x).comp (mfderiv I I' π x)

/-- **The vertical projection** `W ↦ W^V = W - W^H` (Lee, Proposition 2.25(a)). -/
noncomputable def verticalProj (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x :=
  ContinuousLinearMap.id ℝ (TangentSpace I x) - horizontalProj g π x

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
theorem horizontalProj_apply (x : M) (v : TangentSpace I x) :
    horizontalProj g π x v = horizontalLiftAt g π x (mfderiv I I' π x v) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
theorem verticalProj_apply (x : M) (v : TangentSpace I x) :
    verticalProj g π x v = v - horizontalProj g π x v := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The two projections reconstruct the vector: `W = W^H + W^V`. -/
theorem horizontalProj_add_verticalProj (x : M) (v : TangentSpace I x) :
    horizontalProj g π x v + verticalProj g π x v = v := by
  rw [verticalProj_apply]; abel

omit [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- `W^H` is horizontal. -/
theorem horizontalProj_mem (x : M) (v : TangentSpace I x) :
    horizontalProj g π x v ∈ horizontalSpace g π x :=
  horizontalLiftAt_mem g π x _

omit [IsManifold I' ∞ M'] in
/-- `W^V` is vertical. -/
theorem verticalProj_mem (hπ : IsSubmersion π) (x : M) (v : TangentSpace I x) :
    verticalProj g π x v ∈ verticalSpace π x := by
  rw [mem_verticalSpace_iff, verticalProj_apply, map_sub, horizontalProj_apply,
    mfderiv_horizontalLiftAt g π hπ, sub_self]

omit [IsManifold I' ∞ M'] in
/-- The horizontal projection is the identity on horizontal vectors. -/
theorem horizontalProj_of_mem (hπ : IsSubmersion π) {x : M} {v : TangentSpace I x}
    (hv : v ∈ horizontalSpace g π x) : horizontalProj g π x v = v :=
  horizontalLiftAt_mfderiv_of_mem g π hπ hv

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The horizontal projection kills vertical vectors. -/
theorem horizontalProj_of_mem_verticalSpace {x : M} {v : TangentSpace I x}
    (hv : v ∈ verticalSpace π x) : horizontalProj g π x v = 0 := by
  rw [horizontalProj_apply, (mem_verticalSpace_iff (I' := I') (π := π)).mp hv, map_zero]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The horizontal and vertical spaces intersect trivially: a vector that is
both horizontal and vertical is `g`-orthogonal to itself, hence zero. -/
theorem horizontalSpace_inf_verticalSpace (x : M) :
    horizontalSpace g π x ⊓ verticalSpace π x = ⊥ := by
  apply le_antisymm _ bot_le
  intro v hv
  obtain ⟨hvh, hvv⟩ := Submodule.mem_inf.mp hv
  rw [Submodule.mem_bot]
  by_contra hne
  exact absurd (hvh v hvv) (inner_pos g x v hne).ne'

omit [IsManifold I' ∞ M'] in
/-- The horizontal and vertical spaces span, since `v = v^H + v^V`. -/
theorem horizontalSpace_sup_verticalSpace (hπ : IsSubmersion π) (x : M) :
    horizontalSpace g π x ⊔ verticalSpace π x = ⊤ := by
  apply le_antisymm le_top
  intro v _
  rw [← horizontalProj_add_verticalProj g π x v]
  exact Submodule.add_mem_sup (horizontalProj_mem g π x v) (verticalProj_mem g π hπ x v)

omit [IsManifold I' ∞ M'] in
/-- **The tangent space splits as `T_x M = H_x ⊕ V_x`** (Lee, §"Riemannian
Submersions"): the horizontal and vertical spaces are complementary. -/
theorem isCompl_horizontalSpace_verticalSpace (hπ : IsSubmersion π) (x : M) :
    IsCompl (horizontalSpace g π x) (verticalSpace π x) :=
  ⟨disjoint_iff.mpr (horizontalSpace_inf_verticalSpace g π x),
    codisjoint_iff.mpr (horizontalSpace_sup_verticalSpace g π hπ x)⟩

omit [IsManifold I' ∞ M'] in
/-- **Proposition 2.25(a), pointwise**: every tangent vector is uniquely the sum
of a horizontal and a vertical vector. -/
theorem existsUnique_horizontal_add_vertical (hπ : IsSubmersion π) (x : M)
    (v : TangentSpace I x) :
    ∃! p : TangentSpace I x × TangentSpace I x,
      p.1 ∈ horizontalSpace g π x ∧ p.2 ∈ verticalSpace π x ∧ v = p.1 + p.2 := by
  refine ⟨(horizontalProj g π x v, verticalProj g π x v),
    ⟨horizontalProj_mem g π x v, verticalProj_mem g π hπ x v,
      (horizontalProj_add_verticalProj g π x v).symm⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  -- Applying the horizontal projection to `v = a + b` fixes `a` and kills `b`.
  have h1 : horizontalProj g π x v = a := by
    rw [hab, map_add, horizontalProj_of_mem g π hπ ha,
      horizontalProj_of_mem_verticalSpace g π hb, add_zero]
  have h2 : verticalProj g π x v = b := by
    rw [verticalProj_apply, h1, hab]; abel
  simp [h1, h2]

end Pointwise

/-! ## Smooth dependence of the horizontal lift on the data

`LeeLib.Ch02.contDiffAt_horizontalLift` says that `horizontalLift (B x) (A x)`
depends smoothly on `x` when `x` ranges over a *normed space*.  The horizontal
lift of a submersion needs `x` to range over the total space `M`, a *manifold*,
so that lemma cannot be applied directly.

`contMDiffAt_horizontalLift` below is the port.  Its proof is the same four
lines — the formula `L = B⁻¹Aᵗ(AB⁻¹Aᵗ)⁻¹` together with smoothness of operator
inversion at invertible operators — with each `ContDiffAt` combinator replaced
by its `ContMDiffAt` counterpart (`ContMDiffAt.clm_comp`, and
`ContDiffAt.comp_contMDiffAt` for the two inversions, whose outer function is a
map of normed spaces even when the parameter is not).  It is strictly more
general than the normed-space version, which is the case `X = EX`, `IX = 𝓘(ℝ, EX)`.

This is the statement that the horizontal distribution `x ↦ (ker dπ_x)^⊥` varies
smoothly, expressed in a trivialization: `B` and `A` are the metric and the
differential read in local trivializations of the tangent bundles, and
`horizontalLift_congr` is what says the lift of the trivialized data is the
trivialized lift. -/

section Smoothness

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {EX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners ℝ EX HX}
  {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]

set_option quotPrecheck false in
local notation "transposeCLM" => (ContinuousLinearMap.compL ℝ E E' ℝ).flip

/-- **Smooth dependence of the horizontal lift on the data, over a manifold
parameter.**  If `x ↦ B x` and `x ↦ A x` are `C^∞` at `x₀`, `B x₀` is positive
definite and `A x₀` is surjective, then `x ↦ horizontalLift (B x) (A x)` is `C^∞`
at `x₀`.

This is `LeeLib.Ch02.contDiffAt_horizontalLift` with the parameter allowed to
range over a manifold rather than a normed space, which is what a Riemannian
submersion needs. -/
theorem contMDiffAt_horizontalLift
    {B : X → (E →L[ℝ] E →L[ℝ] ℝ)} {A : X → (E →L[ℝ] E')} {x₀ : X}
    (hBd : ContMDiffAt IX 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ B x₀)
    (hAd : ContMDiffAt IX 𝓘(ℝ, E →L[ℝ] E') ∞ A x₀)
    (hB : ∀ v : E, v ≠ 0 → 0 < B x₀ v v) (hA : Function.Surjective (A x₀)) :
    ContMDiffAt IX 𝓘(ℝ, E' →L[ℝ] E) ∞ (fun x => horizontalLift (B x) (A x)) x₀ := by
  -- `x ↦ Aᵗ x` is smooth, being a continuous linear image of `A`.
  have htr : ContMDiffAt IX 𝓘(ℝ, (E' →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ)) ∞
      (fun x => transposeCLM (A x)) x₀ :=
    ContDiff.comp_contMDiffAt (ContinuousLinearMap.contDiff _) hAd
  -- `x ↦ (B x)⁻¹` is smooth at `x₀` because `B x₀` is invertible.
  have hBinv : ContMDiffAt IX 𝓘(ℝ, (E →L[ℝ] ℝ) →L[ℝ] E) ∞
      (fun x => ContinuousLinearMap.inverse (B x : E →L[ℝ] (E →L[ℝ] ℝ))) x₀ := by
    have h := ((isInvertible_of_posDef hB).contDiffAt_map_inverse (n := ∞)).comp_contMDiffAt hBd
    simpa [Function.comp_def] using h
  -- hence `x ↦ raisedTranspose (B x) (A x)` is smooth.
  have hS : ContMDiffAt IX 𝓘(ℝ, (E' →L[ℝ] ℝ) →L[ℝ] E) ∞
      (fun x => raisedTranspose (B x) (A x)) x₀ := hBinv.clm_comp htr
  -- `x ↦ A x ∘ raisedTranspose (B x) (A x)` is smooth and invertible at `x₀`.
  have hAS : ContMDiffAt IX 𝓘(ℝ, (E' →L[ℝ] ℝ) →L[ℝ] E') ∞
      (fun x => (A x).comp (raisedTranspose (B x) (A x))) x₀ := hAd.clm_comp hS
  have hASinv : ContMDiffAt IX 𝓘(ℝ, E' →L[ℝ] (E' →L[ℝ] ℝ)) ∞
      (fun x => ContinuousLinearMap.inverse ((A x).comp (raisedTranspose (B x) (A x)))) x₀ := by
    -- `f` must be pinned: unification would otherwise take it to be the constant `f x₀`.
    have h := ContDiffAt.comp_contMDiffAt (x := x₀) (g := ContinuousLinearMap.inverse)
      (f := fun x => (A x).comp (raisedTranspose (B x) (A x)))
      ((isInvertible_comp_raisedTranspose hB hA).contDiffAt_map_inverse (n := ∞)) hAS
    simpa [Function.comp_def] using h
  exact hS.clm_comp hASinv

end Smoothness

/-! ## Proposition 2.25(b): the horizontal lift of a smooth vector field is smooth

The pieces are now in place.  Fix `x₀ : M`.  Smoothness of a section is a
statement about a local trivialization (`Bundle.contMDiffAt_section`), so write
both the metric and the differential in the trivializations of `T M` at `x₀` and
of `T M'` at `π x₀`:

* `metricInCoordinates g x₀` is `g` so read; it is smooth because that is exactly
  what the `contMDiff` field of a `ContMDiffRiemannianMetric` says, and
  `metricInCoordinates_apply` identifies it as `g` conjugated by the fibre
  trivialization;
* `inTangentCoordinates I I' id π (mfderiv π) x₀` is `dπ` so read, and mathlib's
  `ContMDiffAt.mfderiv_const` says it is smooth — this is the one place where the
  smoothness of `x ↦ dπ_x` enters.

`horizontalLift_congr` then says the lift of this trivialized data *is* the
trivialized lift, and `contMDiffAt_horizontalLift` says the former is smooth.
-/

section VectorFieldLift

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

variable (g : RiemannianMetric I M) (π : C^∞⟮I, M; I', M'⟯)

/-- **The metric read in the trivialization of `T M` at `x₀`.**  This is the
analogue for `g` of mathlib's `inTangentCoordinates` for `mfderiv`. -/
noncomputable def metricInCoordinates (x₀ : M) (x : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ)
    (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ) x₀ ⟨x, g.inner x⟩).2

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- On the chart source, the metric in coordinates is `g` conjugated by the fibre
trivialization: `B x a b = g|_x (θ_x⁻¹ a, θ_x⁻¹ b)`. -/
theorem metricInCoordinates_apply (x₀ x : M) (hx : x ∈ (chartAt H x₀).source) (a b : E) :
    metricInCoordinates g x₀ x a b
      = g.inner x ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x a)
          ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x b) := by
  have hx' : x ∈ (trivializationAt (E →L[ℝ] ℝ) (fun y => TangentSpace I y →L[ℝ] ℝ) x₀).baseSet := by
    simp [hom_trivializationAt_baseSet, hx]
  simp [metricInCoordinates, hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    Bundle.Trivialization.coe_linearMapAt_of_mem _ hx']

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] [IsManifold I' ∞ M'] in
/-- The metric in coordinates is smooth — this *is* the `contMDiff` field of a
`ContMDiffRiemannianMetric`, repackaged through `Bundle.contMDiffAt_section`. -/
theorem contMDiffAt_metricInCoordinates (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (metricInCoordinates g x₀) x₀ :=
  (Bundle.contMDiffAt_section (F := E →L[ℝ] E →L[ℝ] ℝ)
    (E := fun b : M => TangentSpace I b →L[ℝ] TangentSpace I b →L[ℝ] ℝ)
    (IB := I) (n := ∞) (s := fun b => g.inner b) x₀).mp g.contMDiff.contMDiffAt

/-- **The differential read in tangent coordinates at `x₀`.** -/
noncomputable def mfderivInCoordinates (x₀ : M) : M → (E →L[ℝ] E') :=
  inTangentCoordinates I I' id (fun x => π x) (fun x => mfderiv I I' π x) x₀

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
theorem mfderivInCoordinates_apply (x₀ x : M) (a : E) :
    mfderivInCoordinates π x₀ x a
      = (trivializationAt E' (TangentSpace I') (π x₀)).continuousLinearMapAt ℝ (π x)
          (mfderiv I I' π x ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x a)) := rfl

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The differential in coordinates is smooth (mathlib's `ContMDiffAt.mfderiv_const`). -/
theorem contMDiffAt_mfderivInCoordinates (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ (mfderivInCoordinates π x₀) x₀ :=
  ContMDiffAt.mfderiv_const (I := I) (I' := I') (f := fun x => π x) (x₀ := x₀)
    π.contMDiff.contMDiffAt (by simp)

/-- **The horizontal lift, read in tangent coordinates, is smooth.**

`x ↦ L_x` is a family of linear maps `T_{π x}M' → T_x M` covering `π`, so its
smoothness is a statement about local trivializations of the two tangent bundles.
Read there it is the lift of the trivialized data — that is `horizontalLift_congr`
— which is smooth by `contMDiffAt_horizontalLift`.

This is the form Lee's Theorem 2.28 needs: it hands `L` to
`LeeLib.Ch02.contMDiffAt_bilinearCompOf` as an abstract smooth family of linear
maps, the point being that `L` is *not* the differential of any map, so
`ContMDiffAt.mfderiv_const` does not apply to it. -/
theorem contMDiffAt_horizontalLiftAt_inTangentCoordinates (hπ : IsSubmersion π) (x₀ : M) :
    ContMDiffAt I 𝓘(ℝ, E' →L[ℝ] E) ∞
      (inTangentCoordinates I' I (fun x => π x) id (fun x => horizontalLiftAt g π x) x₀) x₀ := by
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simp
  have hy₀ : π x₀ ∈ (trivializationAt E' (TangentSpace I') (π x₀)).baseSet := by simp
  -- The trivialized metric is still positive definite: `θ` is an isomorphism.
  have hBpos : ∀ v : E, v ≠ 0 → 0 < metricInCoordinates g x₀ x₀ v v := by
    intro v hv
    rw [metricInCoordinates_apply g x₀ x₀ (mem_chart_source H x₀)]
    refine g.pos x₀ _ ?_
    exact fun h => hv (by
      rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hx₀] at h
      exact (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x₀
        hx₀).symm.map_eq_zero_iff.mp h))
  -- The trivialized differential is still surjective: it is `dπ` between two isomorphisms.
  have hAsurj : Function.Surjective (mfderivInCoordinates π x₀ x₀) := by
    intro w
    set ι₀ := (trivializationAt E' (TangentSpace I') (π x₀)).continuousLinearEquivAt ℝ (π x₀) hy₀
    set θ₀ := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x₀ hx₀
    obtain ⟨s, hs⟩ := hπ x₀ (ι₀.symm w)
    refine ⟨θ₀ s, ?_⟩
    rw [mfderivInCoordinates_apply]
    have hθ : (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ (θ₀ s) = s := by
      rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hx₀]
      exact θ₀.symm_apply_apply s
    rw [hθ, hs, ← Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hy₀]
    exact ι₀.apply_symm_apply w
  -- Near `x₀`, the lift in tangent coordinates is the lift of the trivialized data.
  have key : (inTangentCoordinates I' I (fun x => π x) id (fun x => horizontalLiftAt g π x) x₀)
      =ᶠ[nhds x₀] (fun x => horizontalLift (metricInCoordinates g x₀ x)
        (mfderivInCoordinates π x₀ x)) := by
    filter_upwards [((chartAt H x₀).open_source).mem_nhds (mem_chart_source H x₀),
      π.contMDiff.continuous.continuousAt.preimage_mem_nhds
        (((chartAt H' (π x₀)).open_source).mem_nhds (mem_chart_source H' (π x₀)))]
      with x hx hy
    have hxb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
    have hyb : π x ∈ (trivializationAt E' (TangentSpace I') (π x₀)).baseSet := by simpa using hy
    set θ := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hxb
    set ι := (trivializationAt E' (TangentSpace I') (π x₀)).continuousLinearEquivAt ℝ (π x) hyb
    have hB' : ∀ a b : E, metricInCoordinates g x₀ x a b = g.inner x (θ.symm a) (θ.symm b) := by
      intro a b
      rw [metricInCoordinates_apply g x₀ x hx,
        ← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hxb]
      rfl
    have hA' : ∀ a : E, mfderivInCoordinates π x₀ x a = ι (mfderiv I I' π x (θ.symm a)) := by
      intro a
      rw [mfderivInCoordinates_apply,
        ← Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hyb,
        ← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hxb]
      rfl
    ext u
    rw [horizontalLift_congr (E := E) (E' := E') (F := E) (F' := E')
      (inner_pos g x) (hπ x) θ ι hB' hA' u]
    show inTangentCoordinates I' I (fun x => π x) id (fun x => horizontalLiftAt g π x) x₀ x u = _
    simp only [inTangentCoordinates, id_eq]
    rw [ContinuousLinearMap.inCoordinates_eq hyb hxb]
    rfl
  rw [key.contMDiffAt_iff]
  exact contMDiffAt_horizontalLift (contMDiffAt_metricInCoordinates g x₀)
    (contMDiffAt_mfderivInCoordinates π x₀) hBpos hAsurj

/-- **The horizontal lift of a smooth section along `π` is smooth.**

This is the analytic core of Lee's Proposition 2.25, in the generality both (a)
and (b) need.  A *section along `π`* is a family `X x ∈ T_{π x}M'` — that is, a
section of the pullback bundle `π^*TM'` — and the assertion is that lifting it
fibrewise by `L_x` produces a smooth vector field on `M`.

Stating it for a section along `π` rather than for a vector field on the base is
what makes it serve both halves of 2.25:

* **(b)** is the case `X x = X₀ (π x)` for a vector field `X₀` on `M'`
  (`contMDiffAt_horizontalLiftField` below);
* **(a)** is the case `X x = dπ_x (W x)` for a vector field `W` on `M`, which is
  *not* of the form `X₀ ∘ π` — the vector `dπ_x (W x)` genuinely depends on `x`
  and not merely on `π x`, since `W` need not be `π`-related to anything.

The proof is unchanged from the vector-field version: only the hypothesis moves,
from `Bundle.contMDiffAt_totalSpace` applied to `X ∘ π` to the same lemma applied
to `X` directly.  `Bundle.contMDiffAt_totalSpace` is stated for an arbitrary base
map, so a section along `π` costs nothing over a section over `M'`. -/
theorem contMDiffAt_horizontalLiftAlong (hπ : IsSubmersion π)
    {X : ∀ x : M, TangentSpace I' (π x)} (x₀ : M)
    (hX : ContMDiffAt I (I'.prod 𝓘(ℝ, E')) ∞
      (fun x => Bundle.TotalSpace.mk' E' (π x) (X x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => Bundle.TotalSpace.mk' E x (horizontalLiftAt g π x (X x))) x₀ := by
  rw [Bundle.contMDiffAt_section]
  have hx₀ : x₀ ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simp
  have hy₀ : π x₀ ∈ (trivializationAt E' (TangentSpace I') (π x₀)).baseSet := by simp
  -- The section along `π`, read in the trivialization of `T M'` at `π x₀`.
  set u : M → E' := fun x => (trivializationAt E' (TangentSpace I') (π x₀) ⟨π x, X x⟩).2 with hu
  have hus : ContMDiffAt I 𝓘(ℝ, E') ∞ u x₀ := by
    rw [Bundle.contMDiffAt_totalSpace] at hX
    exact hX.2
  -- The trivialized metric is still positive definite: `θ` is an isomorphism.
  have hBpos : ∀ v : E, v ≠ 0 → 0 < metricInCoordinates g x₀ x₀ v v := by
    intro v hv
    rw [metricInCoordinates_apply g x₀ x₀ (mem_chart_source H x₀)]
    refine g.pos x₀ _ ?_
    exact fun h => hv (by
      rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hx₀] at h
      exact (((trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x₀
        hx₀).symm.map_eq_zero_iff.mp h))
  -- The trivialized differential is still surjective: it is `dπ` between two isomorphisms.
  have hAsurj : Function.Surjective (mfderivInCoordinates π x₀ x₀) := by
    intro w
    set ι₀ := (trivializationAt E' (TangentSpace I') (π x₀)).continuousLinearEquivAt ℝ (π x₀) hy₀
    set θ₀ := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x₀ hx₀
    obtain ⟨s, hs⟩ := hπ x₀ (ι₀.symm w)
    refine ⟨θ₀ s, ?_⟩
    rw [mfderivInCoordinates_apply]
    have hθ : (trivializationAt E (TangentSpace I) x₀).symmL ℝ x₀ (θ₀ s) = s := by
      rw [← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hx₀]
      exact θ₀.symm_apply_apply s
    rw [hθ, hs, ← Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hy₀]
    exact ι₀.apply_symm_apply w
  -- Near `x₀`, the trivialized lift is the lift of the trivialized data.
  have key : (fun x => (trivializationAt E (TangentSpace I) x₀
        ⟨x, horizontalLiftAt g π x (X x)⟩).2)
      =ᶠ[nhds x₀] (fun x => horizontalLift (metricInCoordinates g x₀ x)
        (mfderivInCoordinates π x₀ x) (u x)) := by
    filter_upwards [((chartAt H x₀).open_source).mem_nhds (mem_chart_source H x₀),
      π.contMDiff.continuous.continuousAt.preimage_mem_nhds
        (((chartAt H' (π x₀)).open_source).mem_nhds (mem_chart_source H' (π x₀)))]
      with x hx hy
    have hxb : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by simpa using hx
    have hyb : π x ∈ (trivializationAt E' (TangentSpace I') (π x₀)).baseSet := by simpa using hy
    set θ := (trivializationAt E (TangentSpace I) x₀).continuousLinearEquivAt ℝ x hxb
    set ι := (trivializationAt E' (TangentSpace I') (π x₀)).continuousLinearEquivAt ℝ (π x) hyb
    have hB' : ∀ a b : E, metricInCoordinates g x₀ x a b = g.inner x (θ.symm a) (θ.symm b) := by
      intro a b
      rw [metricInCoordinates_apply g x₀ x hx,
        ← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hxb]
      rfl
    have hA' : ∀ a : E, mfderivInCoordinates π x₀ x a = ι (mfderiv I I' π x (θ.symm a)) := by
      intro a
      rw [mfderivInCoordinates_apply,
        ← Bundle.Trivialization.coe_continuousLinearEquivAt_eq (R := ℝ) _ hyb,
        ← Bundle.Trivialization.symm_continuousLinearEquivAt_eq' (R := ℝ) _ hxb]
      rfl
    rw [horizontalLift_congr (E := E) (E' := E') (F := E) (F' := E')
      (inner_pos g x) (hπ x) θ ι hB' hA' (u x)]
    have hiu : ι.symm (u x) = X x := ι.symm_apply_apply _
    show θ (horizontalLiftAt g π x (X x)) = _
    rw [← hiu]
    rfl
  rw [key.contMDiffAt_iff]
  exact (contMDiffAt_horizontalLift (contMDiffAt_metricInCoordinates g x₀)
    (contMDiffAt_mfderivInCoordinates π x₀) hBpos hAsurj).clm_apply hus

/-- **Lee, Proposition 2.25(b)**, the analytic half: *the horizontal lift of a
smooth vector field is smooth*.

Given a smooth vector field `X` on the base `M'`, the field
`x ↦ horizontalLiftAt g π x (X (π x))` is a smooth vector field on `M`.  Together
with `mfderiv_horizontalLiftAt` (it is `π`-related to `X`),
`horizontalLiftAt_mem` (it is horizontal) and `horizontalLiftAt_unique` (nothing
else is both), this is the whole of Lee's Proposition 2.25(b).

This is `contMDiffAt_horizontalLiftAlong` for the section along `π` given by
`X ∘ π`, which is smooth because `π` is. -/
theorem contMDiffAt_horizontalLiftField (hπ : IsSubmersion π)
    {X : ∀ y : M', TangentSpace I' y}
    (hX : ContMDiff I' (I'.prod 𝓘(ℝ, E')) ∞ (fun y => Bundle.TotalSpace.mk' E' y (X y)))
    (x₀ : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => Bundle.TotalSpace.mk' E x (horizontalLiftAt g π x (X (π x)))) x₀ :=
  contMDiffAt_horizontalLiftAlong g π hπ x₀ ((hX (π x₀)).comp x₀ π.contMDiff.contMDiffAt)

/-- **Lee, Proposition 2.25(b)**: *every smooth vector field on the base of a
Riemannian submersion has a unique smooth horizontal lift.*

Existence is `horizontalLiftAt`, which is smooth by `contMDiffAt_horizontalLiftField`,
horizontal by `horizontalLiftAt_mem`, and `π`-related to `X` by
`mfderiv_horizontalLiftAt`; uniqueness is `horizontalLiftAt_unique`, applied
pointwise. -/
theorem contMDiff_horizontalLiftField (hπ : IsSubmersion π)
    {X : ∀ y : M', TangentSpace I' y}
    (hX : ContMDiff I' (I'.prod 𝓘(ℝ, E')) ∞ (fun y => Bundle.TotalSpace.mk' E' y (X y))) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
      (fun x => Bundle.TotalSpace.mk' E x (horizontalLiftAt g π x (X (π x)))) :=
  fun x₀ => contMDiffAt_horizontalLiftField g π hπ hX x₀

/-- **Lee, Proposition 2.25(b)**, assembled: the horizontal lift of `X` is a
smooth vector field which is horizontal at every point and `π`-related to `X`,
and it is the only vector field with those two properties. -/
theorem exists_unique_horizontalLift (hπ : IsSubmersion π)
    {X : ∀ y : M', TangentSpace I' y}
    (hX : ContMDiff I' (I'.prod 𝓘(ℝ, E')) ∞ (fun y => Bundle.TotalSpace.mk' E' y (X y))) :
    ∃ Y : ∀ x : M, TangentSpace I x,
      ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (fun x => Bundle.TotalSpace.mk' E x (Y x)) ∧
      (∀ x, Y x ∈ horizontalSpace g π x) ∧
      (∀ x, mfderiv I I' π x (Y x) = X (π x)) ∧
      (∀ Z : ∀ x : M, TangentSpace I x, (∀ x, Z x ∈ horizontalSpace g π x) →
        (∀ x, mfderiv I I' π x (Z x) = X (π x)) → ∀ x, Z x = Y x) := by
  refine ⟨fun x => horizontalLiftAt g π x (X (π x)), contMDiff_horizontalLiftField g π hπ hX,
    fun x => horizontalLiftAt_mem g π x _, fun x => mfderiv_horizontalLiftAt g π hπ x _, ?_⟩
  intro Z hZh hZrel x
  -- Two horizontal vectors with the same image under `dπ_x` coincide.
  exact horizontalSpace_injOn_mfderiv g π hπ (hZh x) (horizontalLiftAt_mem g π x _)
    (by rw [hZrel x, mfderiv_horizontalLiftAt g π hπ x])

end VectorFieldLift

end LeeLib.Ch02

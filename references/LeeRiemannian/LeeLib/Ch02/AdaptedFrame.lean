/-
Chapter 2, "Riemannian Metrics", §3 "Methods for Constructing Riemannian
Metrics": adapted orthonormal frames along a submanifold.

Lee's Proposition 2.14: if `M ⊆ M̃` is an embedded submanifold of a Riemannian
manifold, every `p ∈ M` has a neighbourhood carrying a smooth orthonormal frame
for `M̃` whose first `n` vector fields are tangent to `M`.  Lee proves it by
taking a coordinate frame in *slice coordinates* and running Gram-Schmidt.

Slice coordinates are not needed, and this file does not use them.  As
everywhere else in this chapter a submanifold is presented by a smooth immersion
`F : M → M̃` (Lee's Lemma 2.11, `LeeLib.Ch02.pullbackMetric`), and the bundle in
which an adapted frame lives is the ambient tangent bundle along `M`, i.e. the
pullback `F *ᵖ T M̃` (`Bundle.ContMDiffRiemannianMetric.pullback`).  The
role played by slice coordinates in Lee's proof — supplying a frame of `T M̃`
whose first `n` members are tangent to `M` — is played here by the *pushforward*
of a frame of `TM`:

  `x ↦ dF_x (X_i|_x)`,   `i = 1, …, n`,

which is a family of smooth sections of `F *ᵖ T M̃` (`contMDiffOn_pushforward`),
linearly independent at each point exactly because `F` is an immersion, and
spanning `range dF_x` — Lee's `T_x M` viewed inside `T_{F x} M̃` — by
construction.  Gram-Schmidt against the ambient metric then does the rest.  The
route is shorter than Lee's, and it applies verbatim to an immersed submanifold,
where slice coordinates are unavailable.

Three pieces of infrastructure are missing upstream and are supplied here.  None
is specific to the tangent bundle; all are stated for a general `C^n` vector
bundle.

* `exists_linearIndependent_castAdd` — linear algebra: a linearly independent
  family of `k` vectors extends to one of `k + d` vectors, the original family
  occupying the first `k` slots.  mathlib has `Basis.sumExtend`, but it is
  indexed by `ι ⊕ sumExtendIndex` with no equation for its restriction to `ι`,
  which is precisely the information an *ordered* extension needs; the induction
  on `d` via `Fin.snoc` is shorter than reindexing it would be.

* `exists_isLocalIndepOn_nhds` — **linear independence of smooth sections is an
  open condition**.  This is the analytic crux, and it is what makes "extend a
  partial frame" a *local* statement: read in a trivialization the sections
  become a continuous family of tuples in `F`, and mathlib's
  `LinearIndependent.eventually` says linear independence persists nearby.

* `exists_isLocalFrameOn_extend` — the two combined: a pointwise linearly
  independent family of smooth sections is the first `k` members of a genuine
  local frame, on a possibly smaller neighbourhood.  The extra sections are
  constant in a trivialization, which is where the neighbourhood shrinks.

mathlib has no notion of a smooth vector *subbundle*, and its `IsImmersionAt`
carries no `mfderiv` API, so neither is used: "tangent to `M`" is spelled out as
membership in `tangentRange F x = range (mfderiv I I' F x)`, which is what Lee's
identification of `T_x M` with its image under `dF_x` amounts to.

Proposition 2.14 itself is `exists_adapted_orthonormalFrame` at the end of the
file.  Given the above the assembly is short — push a chart frame forward;
`IsLocalIndepOn` because `F` is an immersion; `exists_isLocalFrameOn_extend`;
`isLocalFrameOn_gramSchmidtFrame`, whose flag condition is what keeps the first
`n` members inside `tangentRange` — and the two facts about the resulting frame
that Lee states are read off it: orthonormality from `gramSchmidtFrame_orthonormal`,
adaptedness from `span_gramSchmidtFrame_Iic`.  That the first `n` members *span*
`T_x M`, rather than merely lying in it, is a dimension count: `n` independent
vectors inside the `n`-dimensional `tangentRange f x` (`finrank_tangentRange`).

It needed `VectorBundle ℝ E' (F *ᵖ T M̃)` and `IsContMDiffRiemannianBundle` on the
pullback to hold *simultaneously*, which for a long time they did not; the
instance diamond responsible, and the reason mathlib's `RiemannianBundle` is the
way out of it, are recorded in the header of `LeeLib.Ch02.PullbackBundle`.
-/
import LeeLib.Ch02.PullbackBundle
import LeeLib.Ch02.PullbackMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

namespace LeeLib.Ch02

open Bundle InnerProductSpace Module Submodule
open scoped Manifold ContDiff RealInnerProductSpace Topology

/-! ### Extending a linearly independent family, in a fixed order -/

section Extend

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- A linearly independent family of `k` vectors extends to a linearly independent family of
`k + d` vectors, provided `k + d` does not exceed the dimension, **with the original family in
the first `k` slots**.

mathlib's `Basis.sumExtend` extends a linearly independent family to a basis, but indexes the
result by `ι ⊕ sumExtendIndex` and proves no equation for the restriction to the `ι` summand, so
it cannot deliver the ordering.  The ordering is the whole point here: Gram-Schmidt preserves the
flag of initial spans, so putting the tangent directions first is exactly what makes the resulting
orthonormal frame *adapted*. -/
theorem exists_linearIndependent_castAdd :
    ∀ (d k : ℕ) (c : Fin k → F), LinearIndependent ℝ c → k + d ≤ finrank ℝ F →
      ∃ w : Fin (k + d) → F, LinearIndependent ℝ w ∧ ∀ i : Fin k, w (Fin.castAdd d i) = c i := by
  intro d
  induction d with
  | zero =>
    intro k c hc _
    exact ⟨fun j => c (Fin.cast (Nat.add_zero k) j),
      hc.comp _ (finCongr (Nat.add_zero k)).injective, fun _ => rfl⟩
  | succ d ih =>
    intro k c hc h
    -- `span c` has dimension `k < finrank F`, so it is proper and misses some `y`
    have hspan : span ℝ (Set.range c) ≠ ⊤ := by
      intro htop
      have hk : finrank ℝ (span ℝ (Set.range c)) = Fintype.card (Fin k) := finrank_span_eq_card hc
      rw [htop, finrank_top, Fintype.card_fin] at hk
      omega
    obtain ⟨y, hy⟩ : ∃ y, y ∉ span ℝ (Set.range c) := by
      by_contra hcon
      exact hspan (eq_top_iff'.2 (by push Not at hcon; exact hcon))
    -- append `y` and recurse
    obtain ⟨w, hw, hwc⟩ :=
      ih (k + 1) (Fin.snoc c y) (linearIndependent_finSnoc.2 ⟨hc, hy⟩) (by omega)
    refine ⟨fun j => w (Fin.cast (by omega) j),
      hw.comp _ (finCongr (show k + (d + 1) = k + 1 + d by omega)).injective, fun i => ?_⟩
    have hcast : (Fin.cast (show k + (d + 1) = k + 1 + d by omega) (Fin.castAdd (d + 1) i))
        = Fin.castAdd d (Fin.castSucc i) := by ext; simp
    simp only [hcast, hwc, Fin.snoc_castSucc]

end Extend

/-! ### Linear independence of smooth sections is an open condition -/

section Fibre

/- The fibrewise dimension facts below hold for *any* real vector bundle: they read a
trivialization as a linear equivalence onto the model fibre and use nothing else.  In particular
they must not be stated in the inner-product context of `section Openness`, since the indefinite
development (`LeeLib.Ch02.PseudoAdaptedFrame`) needs them for bundles whose fibres carry no
inner product at all. -/
variable
  {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

/-- Every fibre of a vector bundle has the dimension of the model fibre: a trivialization around
the point is a linear equivalence onto `F`. -/
theorem finrank_fibre (x : B) : finrank ℝ (V x) = finrank ℝ F :=
  ((trivializationAt F V x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)).toLinearEquiv.finrank_eq

/-- Fibres of a vector bundle with finite-dimensional model fibre are finite-dimensional.  Not an
instance: `F` cannot be recovered from `V x`. -/
theorem finiteDimensional_fibre [FiniteDimensional ℝ F] (x : B) : FiniteDimensional ℝ (V x) :=
  ((trivializationAt F V x).continuousLinearEquivAt ℝ x
    (mem_baseSet_trivializationAt F V x)).toLinearEquiv.symm.finiteDimensional

end Fibre

section Openness

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]

variable {ι : Type*} [Finite ι] {X : ι → (x : B) → V x} {u : Set B} {x₀ : B}

/-- Reading a section in a trivialization: the fibre component of `e ⟨x, s x⟩` is the image of
`s x` under the fibrewise linear equivalence. -/
theorem trivializationAt_snd_eq (e : Trivialization F (π F V)) [e.IsLinear ℝ] {x : B}
    (hx : x ∈ e.baseSet) (v : V x) : (e ⟨x, v⟩).2 = e.continuousLinearEquivAt ℝ x hx v := by
  rw [e.apply_eq_prod_continuousLinearEquivAt ℝ x hx v]

/-- **Linear independence of smooth sections is an open condition.**

If a finite family of sections is `C^n` on an open set `u` and is linearly independent *at one
point* `x₀ ∈ u`, then it is linearly independent on a whole neighbourhood of `x₀`.

Read in a trivialization around `x₀` the family becomes a continuous map `x ↦ (c x i)ᵢ` into
`ι → F`, and mathlib's `LinearIndependent.eventually` says that linear independence of a tuple
survives small perturbations.  This is the only genuinely analytic ingredient in the construction
of an adapted frame; everything else is Gram-Schmidt and bookkeeping. -/
theorem exists_isLocalIndepOn_nhds
    (hsm : ∀ i, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (X i)) u) (hu : IsOpen u) (hx₀ : x₀ ∈ u)
    (hli : LinearIndependent ℝ (X · x₀)) :
    ∃ v, IsOpen v ∧ x₀ ∈ v ∧ v ⊆ u ∧ IsLocalIndepOn IB F n X v := by
  set e := trivializationAt F V x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  -- the family read in the trivialization at `x₀`
  set c : B → (ι → F) := fun x i => (e ⟨x, X i x⟩).2 with hc
  have hcont : ContinuousAt c x₀ := by
    refine continuousAt_pi.2 fun i => ?_
    have h := (hsm i).contMDiffAt (hu.mem_nhds hx₀)
    rw [contMDiffAt_section] at h
    exact h.continuousAt
  have hcli : LinearIndependent ℝ (c x₀) := by
    have hcomp : c x₀ = ⇑(e.continuousLinearEquivAt ℝ x₀ hx₀e).toLinearEquiv.toLinearMap
        ∘ (X · x₀) := funext fun i => trivializationAt_snd_eq e hx₀e (X i x₀)
    rw [hcomp]
    exact hli.map' _ (LinearMap.ker_eq_bot_of_injective
      (e.continuousLinearEquivAt ℝ x₀ hx₀e).injective)
  -- linear independence persists near `x₀`, and so do membership in `u` and in the base set
  have hev : ∀ᶠ x in 𝓝 x₀, LinearIndependent ℝ (c x) ∧ x ∈ u ∧ x ∈ e.baseSet := by
    refine (hcont.eventually hcli.eventually).and (Filter.Eventually.and ?_ ?_)
    · exact hu.mem_nhds hx₀
    · exact e.open_baseSet.mem_nhds hx₀e
  obtain ⟨v, hvsub, hvopen, hx₀v⟩ := mem_nhds_iff.1 hev
  refine ⟨v, hvopen, hx₀v, fun x hx => (hvsub hx).2.1, ?_⟩
  refine ⟨fun {x} hx => ?_, fun i => (hsm i).mono fun x hx => (hvsub hx).2.1⟩
  obtain ⟨hcx, -, hxe⟩ := hvsub hx
  -- transport independence back through the fibrewise equivalence
  have hcomp : c x = ⇑(e.continuousLinearEquivAt ℝ x hxe).toLinearEquiv.toLinearMap ∘ (X · x) :=
    funext fun i => trivializationAt_snd_eq e hxe (X i x)
  rw [hcomp] at hcx
  exact hcx.of_comp _

/-- A pointwise linearly independent family with as many members as the fibre has dimensions is a
local frame: independence forces spanning. -/
theorem IsLocalIndepOn.isLocalFrameOn [Fintype ι] [FiniteDimensional ℝ F]
    (hX : IsLocalIndepOn IB F n X u) (hcard : Fintype.card ι = finrank ℝ F) :
    IsLocalFrameOn IB F n X u where
  linearIndependent hx := hX.linearIndependent hx
  contMDiffOn i := hX.contMDiffOn i
  generating := fun {x} hx => by
    haveI := finiteDimensional_fibre (F := F) (V := V) x
    exact ((hX.linearIndependent hx).span_eq_top_of_card_eq_finrank'
      (by rw [hcard, finrank_fibre (F := F) (V := V) x])).ge

end Openness

/-! ### Extending a partial frame of smooth sections -/

section FrameExtension

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V IB]

/-- **A partial frame extends to a full local frame.**

If `X_1, …, X_k` are smooth sections of `V` on an open `u`, linearly independent at every point of
`u`, then near any `x₀ ∈ u` they are the *first `k` members* of a genuine smooth local frame
`Y_1, …, Y_m` (`m = rank V`).

This is the tool Lee's Proposition 2.14 needs and mathlib does not have.  The extra sections are
taken constant in a trivialization around `x₀` — that is why the conclusion is local even though
the hypothesis holds on all of `u` — and linear independence of the enlarged family, which holds
at `x₀` by construction, propagates to a neighbourhood by `exists_isLocalIndepOn_nhds`. -/
theorem exists_isLocalFrameOn_extend {k : ℕ} {X : Fin k → (x : B) → V x} {u : Set B} {x₀ : B}
    (hX : IsLocalIndepOn IB F n X u) (hu : IsOpen u) (hx₀ : x₀ ∈ u) :
    ∃ (v : Set B) (Y : Fin (finrank ℝ F) → (x : B) → V x) (hk : k ≤ finrank ℝ F),
      IsOpen v ∧ x₀ ∈ v ∧ v ⊆ u ∧ IsLocalFrameOn IB F n Y v ∧
        ∀ (i : Fin k) (x : B), x ∈ v → Y (Fin.castLE hk i) x = X i x := by
  classical
  haveI := finiteDimensional_fibre (F := F) (V := V) x₀
  set m := finrank ℝ F with hm
  set e := trivializationAt F V x₀ with he
  have hx₀e : x₀ ∈ e.baseSet := mem_baseSet_trivializationAt F V x₀
  set Φ := e.continuousLinearEquivAt ℝ x₀ hx₀e with hΦ
  -- the family, read in the trivialization at `x₀`
  set c : Fin k → F := fun i => Φ (X i x₀) with hcdef
  have hc : LinearIndependent ℝ c :=
    (hX.linearIndependent hx₀).map' Φ.toLinearEquiv.toLinearMap
      (LinearMap.ker_eq_bot_of_injective Φ.injective)
  have hk : k ≤ m := by
    simpa using hc.fintype_card_le_finrank
  -- extend it to a basis of `F`, keeping `c` in the first `k` slots
  obtain ⟨w, hw, hwc⟩ :=
    exists_linearIndependent_castAdd (F := F) (m - k) k c hc (by omega)
  set w' : Fin m → F := fun j => w (Fin.cast (by omega) j) with hw'def
  have hw' : LinearIndependent ℝ w' :=
    hw.comp _ (finCongr (show m = k + (m - k) by omega)).injective
  have hw'c : ∀ i : Fin k, w' (Fin.castLE hk i) = c i := fun i => by
    have : (Fin.cast (show m = k + (m - k) by omega) (Fin.castLE hk i))
        = Fin.castAdd (m - k) i := by ext; simp
    simp only [hw'def, this, hwc]
  set b : Basis (Fin m) ℝ F :=
    Basis.mk hw' (hw'.span_eq_top_of_card_eq_finrank' (by simp [hm])).ge with hbdef
  have hb : ∀ j, b j = w' j := fun j => Basis.mk_apply _ _ j
  -- the enlarged family: `X` where it exists, constant-in-`e` sections beyond
  set Y : Fin m → (x : B) → V x :=
    fun j x => if h : (j : ℕ) < k then X ⟨j, h⟩ x else e.localFrame b j x with hYdef
  -- `Y` restricted to the first `k` slots is `X`
  have hYX : ∀ (i : Fin k) (x : B), Y (Fin.castLE hk i) x = X i x := fun i x => by
    simp only [hYdef, Fin.coe_castLE, dif_pos i.isLt, Fin.eta]
  -- at `x₀` every `Y j` is the `e`-preimage of `w' j`, so `Y · x₀` is independent
  have hYx₀ : ∀ j, Y j x₀ = Φ.symm (w' j) := fun j => by
    by_cases h : (j : ℕ) < k
    · have hj : Fin.castLE hk ⟨(j : ℕ), h⟩ = j := by ext; simp
      rw [← hj, hYX ⟨(j : ℕ), h⟩ x₀, hw'c ⟨(j : ℕ), h⟩, hcdef]
      simp
    · simp only [hYdef, dif_neg h, e.localFrame_apply_of_mem_baseSet b hx₀e,
        Trivialization.basisAt, Basis.map_apply, hb j]
      rfl
  have hYli : LinearIndependent ℝ (Y · x₀) := by
    have : (Y · x₀) = ⇑Φ.symm.toLinearEquiv.toLinearMap ∘ w' := funext hYx₀
    rw [this]
    exact hw'.map' _ (LinearMap.ker_eq_bot_of_injective Φ.symm.injective)
  -- `Y` is smooth on `u ∩ e.baseSet`
  have hYsm : ∀ j, ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n (T% (Y j)) (u ∩ e.baseSet) := fun j => by
    by_cases h : (j : ℕ) < k
    · exact ((hX.contMDiffOn ⟨(j : ℕ), h⟩).mono Set.inter_subset_left).congr
        fun x _ => by simp only [hYdef, dif_pos h]
    · exact ((e.contMDiffOn_localFrame_baseSet n b j).mono Set.inter_subset_right).congr
        fun x _ => by simp only [hYdef, dif_neg h]
  obtain ⟨v, hvopen, hx₀v, hvsub, hvindep⟩ :=
    exists_isLocalIndepOn_nhds hYsm (hu.inter e.open_baseSet) ⟨hx₀, hx₀e⟩ hYli
  exact ⟨v, Y, hk, hvopen, hx₀v, fun x hx => (hvsub hx).1,
    hvindep.isLocalFrameOn (by simp [hm]), fun i x _ => hYX i x⟩

end FrameExtension

/-! ### Pushing a vector field forward into the ambient tangent bundle -/

section Pushforward

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **The pushforward of a vector field along a smooth map**, as a section of the ambient tangent
bundle `F *ᵖ T M̃` along `M`.

`(F_* X)_x = dF_x (X_x) ∈ T_{F x} M̃`.  This is a section of the *pullback* bundle and not of
`T M̃` itself, which is the whole reason Lee's `T M̃|_M` is the right home for it: `X` is a field on
`M`, so `dF_x(X_x)` varies over `x ∈ M` while living in the fibres of `T M̃` over the image.

When `F` is an immersion these sections span `range dF_x`, Lee's copy of `T_x M` inside
`T_{F x} M̃` — that is what makes the frame they generate *adapted*. -/
noncomputable def pushforward (f : C^∞⟮I, M; I', M'⟯) (X : (x : M) → TangentSpace I x) (x : M) :
    ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x :=
  mfderiv I I' f x (X x)

@[simp] theorem pushforward_apply (f : C^∞⟮I, M; I', M'⟯) (X : (x : M) → TangentSpace I x) (x : M) :
    pushforward f X x = mfderiv I I' f x (X x) := rfl

/-- **Lee's `T_x M`, viewed inside the ambient tangent space** `T_{F x} M̃` — the image of `dF_x`,
as a subspace of the fibre of `T M̃|_M = F *ᵖ T M̃` at `x`.

This is the identification Lee makes silently: "because we usually identify `T_p M` with its image
in `T_p M̃` under `dι_p`, and think of `dι_p` as an inclusion map".  The fibre `(F *ᵖ T M̃) x` *is*
`T_{F x} M̃`, so no transport is involved; the ascription below only tells the elaborator so. -/
noncomputable def tangentRange (f : C^∞⟮I, M; I', M'⟯) (x : M) :
    Submodule ℝ (((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) :=
  LinearMap.range (show TangentSpace I x →ₗ[ℝ]
    ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x from (mfderiv I I' f x).toLinearMap)

theorem pushforward_mem_tangentRange (f : C^∞⟮I, M; I', M'⟯) (X : (x : M) → TangentSpace I x)
    (x : M) : pushforward f X x ∈ tangentRange f x :=
  ⟨X x, rfl⟩

/-- Where `F` is an immersion, Lee's `T_x M` viewed inside `T_{F x} M̃` has the dimension of `M`:
`dF_x` is injective, so its range is a faithful copy of `T_x M`. -/
theorem finrank_tangentRange [FiniteDimensional ℝ E] (f : C^∞⟮I, M; I', M'⟯) {x : M}
    (himm : Function.Injective (mfderiv I I' f x)) :
    finrank ℝ (tangentRange f x) = finrank ℝ E :=
  LinearMap.finrank_range_of_inj (f := show TangentSpace I x →ₗ[ℝ]
    ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x from (mfderiv I I' f x).toLinearMap) himm

/-- **The pushforward of a smooth vector field is a smooth section** of `F *ᵖ T M̃`.

Read in trivializations at `x₀` and `F x₀`, the section is `x ↦ D x (ξ x)`, where `D` is the
differential of `F` in tangent coordinates — smooth by `ContMDiffAt.mfderiv_const` because `F` is
smooth — and `ξ` is `X` read in the trivialization, smooth because `X` is a smooth section.  A
continuous-linear-map application of two smooth maps is smooth, and the trivialization of the
pullback bundle at `x₀` is by definition the one of `T M̃` at `F x₀` (`trivializationAt_pullback`),
which is what lets the two readings be compared. -/
theorem contMDiffAt_pushforward {f : C^∞⟮I, M; I', M'⟯} {X : (x : M) → TangentSpace I x} {x₀ : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞ (T% X) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E')) ∞
      (fun x => TotalSpace.mk' E' x (pushforward f X x)) x₀ := by
  rw [contMDiffAt_section]
  set sT := trivializationAt E (TangentSpace I) x₀ with hsT
  set tT := trivializationAt E' (TangentSpace I') (f x₀) with htT
  have hx₀ : x₀ ∈ sT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
  have hfx₀ : f x₀ ∈ tT.baseSet := mem_baseSet_trivializationAt E' (TangentSpace I') (f x₀)
  set D : M → (E →L[ℝ] E') := inTangentCoordinates I I' id f (fun x => mfderiv I I' f x) x₀ with hD
  have hDsmooth : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E') ∞ D x₀ :=
    ContMDiffAt.mfderiv_const f.contMDiff.contMDiffAt (by simp)
  -- `X` read in the trivialization at `x₀`
  have hξ : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun x => (sT ⟨x, X x⟩).2) x₀ := (contMDiffAt_section x₀).1 hX
  refine ((hDsmooth.clm_apply hξ).congr_of_eventuallyEq ?_)
  have hUs : {x : M | x ∈ sT.baseSet} ∈ 𝓝 x₀ := sT.open_baseSet.mem_nhds hx₀
  have hUt : {x : M | f x ∈ tT.baseSet} ∈ 𝓝 x₀ :=
    f.contMDiff.continuous.continuousAt (tT.open_baseSet.mem_nhds hfx₀)
  filter_upwards [hUs, hUt] with x hx hfx
  -- both sides are `dF_x (X_x)` read in the trivialization at `F x₀`
  have hDu : ∀ w : E, D x w = tT.continuousLinearEquivAt ℝ (f x) hfx
      (mfderiv I I' f x ((sT.continuousLinearEquivAt ℝ x hx).symm w)) := by
    intro w
    rw [hD]
    simp only [inTangentCoordinates, id_eq]
    rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
    rfl
  -- the trivialization of `f *ᵖ T M̃` at `x₀` *is* the one of `T M̃` at `F x₀`, read along `f`
  show (tT ⟨f x, mfderiv I I' f x (X x)⟩).2 = D x ((sT ⟨x, X x⟩).2)
  rw [hDu]
  -- reading `X x` in `sT` and undoing it returns `X x`
  have hsymm : (sT.continuousLinearEquivAt ℝ x hx).symm ((sT ⟨x, X x⟩).2) = X x := by
    rw [sT.apply_eq_prod_continuousLinearEquivAt ℝ x hx]
    exact (sT.continuousLinearEquivAt ℝ x hx).symm_apply_apply (X x)
  rw [hsymm, tT.apply_eq_prod_continuousLinearEquivAt ℝ (f x) hfx]

/-- `contMDiffAt_pushforward`, on an open set. -/
theorem contMDiffOn_pushforward {f : C^∞⟮I, M; I', M'⟯} {X : (x : M) → TangentSpace I x}
    {u : Set M} (hu : IsOpen u) (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E')) ∞
      (fun x => TotalSpace.mk' E' x (pushforward f X x)) u := fun x hx =>
  (contMDiffAt_pushforward (hX.contMDiffAt (hu.mem_nhds hx))).contMDiffWithinAt

/-- The pushforwards of a local frame of `TM` are linearly independent in the ambient fibre
exactly where `F` is an immersion: `dF_x` injective carries an independent family to an
independent family. -/
theorem linearIndependent_pushforward {f : C^∞⟮I, M; I', M'⟯} {ι : Type*}
    {X : ι → (x : M) → TangentSpace I x} {x : M} (himm : Function.Injective (mfderiv I I' f x))
    (hX : LinearIndependent ℝ (X · x)) :
    LinearIndependent ℝ (fun i => pushforward f (X i) x) :=
  hX.map' (show TangentSpace I x →ₗ[ℝ]
      ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x from (mfderiv I I' f x).toLinearMap)
    (LinearMap.ker_eq_bot_of_injective himm)

/-- The pushforwards of a *frame* of `TM` span `tangentRange f x` — Lee's `T_x M` seen inside
`T_{F x} M̃`.  This is what makes the first `n` members of the adapted frame span the tangent
directions and nothing more. -/
theorem span_pushforward_range {f : C^∞⟮I, M; I', M'⟯} {ι : Type*}
    {X : ι → (x : M) → TangentSpace I x} {x : M} (hspan : span ℝ (Set.range (X · x)) = ⊤) :
    span ℝ (Set.range fun i => pushforward f (X i) x) = tangentRange f x := by
  have hmap : (Set.range fun i => pushforward f (X i) x)
      = (show TangentSpace I x →ₗ[ℝ]
          ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x from (mfderiv I I' f x).toLinearMap)
        '' (Set.range (X · x)) := by
    rw [← Set.range_comp]; rfl
  rw [hmap, ← Submodule.map_span, hspan, tangentRange, Submodule.map_top]

end Pushforward

/-! ### Lee's Proposition 2.14: existence of adapted orthonormal frames -/

section Adapted

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Existence of adapted orthonormal frames** (Lee, Proposition 2.14).

Let `(M̃, g̃)` be a Riemannian manifold and let `F : M → M̃` present a submanifold as a smooth
immersion.  Every `p ∈ M` has a neighbourhood `v` carrying a smooth orthonormal frame
`(E_1, …, E_m)` for the ambient tangent bundle `T M̃|_M = F *ᵖ T M̃` whose first `n = dim M`
members span `T_x M` — Lee's `tangentRange f x` — at every point of `v`.  That last clause is
exactly Lee's "adapted to `M`".

Lee proves this by running Gram-Schmidt on a coordinate frame in *slice coordinates*.  Slice
coordinates are not used here and are not needed: the role they play — supplying a frame of
`T M̃` whose first `n` members are tangent to `M` — is played by the pushforward `dF(∂_i)` of a
chart frame of `TM`, which is linearly independent precisely because `F` is an immersion and
spans `tangentRange f x` by construction.  The route therefore also covers *immersed*
submanifolds, where slice coordinates are unavailable.

Orthonormality is stated through `g̃` itself, so using the proposition does not require the
caller to install the fibrewise inner product structure on the pullback. -/
theorem exists_adapted_orthonormalFrame (g' : RiemannianMetric I' M') (f : C^∞⟮I, M; I', M'⟯)
    (himm : ∀ x : M, Function.Injective (mfderiv I I' f x)) (p : M) :
    ∃ (v : Set M) (Y : Fin (finrank ℝ E') → (x : M) →
        ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) x) (hn : finrank ℝ E ≤ finrank ℝ E'),
      IsOpen v ∧ p ∈ v ∧ IsLocalFrameOn I E' ∞ Y v ∧
      (∀ x ∈ v, ∀ i j, g'.inner (f x) (Y i x) (Y j x) = if i = j then 1 else 0) ∧
      (∀ x ∈ v, ∀ i : Fin (finrank ℝ E), Y (Fin.castLE hn i) x ∈ tangentRange f x) ∧
      (∀ x ∈ v, span ℝ (Set.range fun i : Fin (finrank ℝ E) => Y (Fin.castLE hn i) x)
        = tangentRange f x) := by
  classical
  -- the ambient metric makes `T M̃|_M` a Riemannian bundle, so Gram-Schmidt runs in its fibres
  letI : Bundle.RiemannianBundle ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) :=
    ⟨(g'.pullback f).toRiemannianMetric⟩
  set V := ((f : M → M') *ᵖ (TangentSpace I' : M' → Type _)) with hV
  -- a chart frame for `TM` around `p`
  set e := trivializationAt E (TangentSpace I) p with he
  have hpe : p ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) p
  set X := e.localFrame (Module.finBasis ℝ E) with hXdef
  have hX : IsLocalFrameOn I E ∞ X e.baseSet :=
    e.isLocalFrameOn_localFrame_baseSet I ∞ (Module.finBasis ℝ E)
  -- push it forward into the ambient bundle: `n` independent smooth sections of `V`
  set Z : Fin (finrank ℝ E) → (x : M) → V x := fun i x => pushforward f (X i) x with hZdef
  have hZ : IsLocalIndepOn I E' ∞ Z e.baseSet :=
    { linearIndependent := fun {x} hx =>
        linearIndependent_pushforward (himm x) (hX.linearIndependent hx)
      contMDiffOn := fun i => contMDiffOn_pushforward e.open_baseSet (hX.contMDiffOn i) }
  -- extend them to a full frame of `V` near `p`
  obtain ⟨v, Y₀, hn, hvopen, hpv, hvsub, hY₀, hY₀Z⟩ :=
    exists_isLocalFrameOn_extend (IB := I) (F := E') (V := V) hZ e.open_baseSet hpe
  -- every member of `Y₀` below the cut is a pushforward, hence tangent to `M`
  have hY₀tan : ∀ x ∈ v, ∀ i : Fin (finrank ℝ E), Y₀ (Fin.castLE hn i) x ∈ tangentRange f x :=
    fun x hx i => by
      rw [hY₀Z i x hx]; exact pushforward_mem_tangentRange f (X i) x
  -- Gram-Schmidt preserves the flag, so `GS_k` stays inside the span of `Y₀_1, …, Y₀_k`;
  -- for `k` below the cut those are all tangent, and the span of a set of tangent vectors is
  -- tangent.  This is the whole reason the *ordered* extension mattered.
  have hGStan : ∀ x ∈ v, ∀ i : Fin (finrank ℝ E),
      gramSchmidtFrame (V := V) Y₀ (Fin.castLE hn i) x ∈ tangentRange f x := by
    intro x hx i
    have hmem : gramSchmidtFrame (V := V) Y₀ (Fin.castLE hn i) x
        ∈ span ℝ ((fun j => gramSchmidtFrame (V := V) Y₀ j x) '' Set.Iic (Fin.castLE hn i)) :=
      subset_span (Set.mem_image_of_mem _ (Set.mem_Iic.2 le_rfl))
    refine span_le.2 ?_
      ((span_gramSchmidtFrame_Iic (V := V) Y₀ x (Fin.castLE hn i)).le hmem)
    rintro _ ⟨j, hj, rfl⟩
    have hjlt : (j : ℕ) < finrank ℝ E := lt_of_le_of_lt hj i.isLt
    have hjeq : j = Fin.castLE hn ⟨(j : ℕ), hjlt⟩ := by ext; simp
    rw [hjeq]
    exact hY₀tan x hx ⟨(j : ℕ), hjlt⟩
  refine ⟨v, gramSchmidtFrame (V := V) Y₀, hn, hvopen, hpv,
    isLocalFrameOn_gramSchmidtFrame (IB := I) (F := E') (V := V) hY₀, ?_, hGStan, ?_⟩
  · -- orthonormality, read back through `g̃`
    intro x hx i j
    have hon := gramSchmidtFrame_orthonormal (IB := I) (F := E') (V := V) hY₀.isLocalIndepOn hx
    show ⟪gramSchmidtFrame (V := V) Y₀ i x, gramSchmidtFrame (V := V) Y₀ j x⟫_ℝ = _
    rcases eq_or_ne i j with rfl | hij
    · rw [if_pos rfl, real_inner_self_eq_norm_sq, hon.1 i, one_pow]
    · rw [if_neg hij]; exact hon.2 hij
  · -- `n` independent tangent vectors inside the `n`-dimensional `tangentRange` span it
    intro x hx
    haveI : FiniteDimensional ℝ (V x) := finiteDimensional_fibre (F := E') (V := V) x
    have hli : LinearIndependent ℝ
        (fun i : Fin (finrank ℝ E) => gramSchmidtFrame (V := V) Y₀ (Fin.castLE hn i) x) :=
      (gramSchmidtFrame_linearIndependent (IB := I) (F := E') (V := V)
        hY₀.isLocalIndepOn hx).comp _ (Fin.castLE_injective hn)
    have hle : span ℝ (Set.range fun i : Fin (finrank ℝ E) =>
        gramSchmidtFrame (V := V) Y₀ (Fin.castLE hn i) x) ≤ tangentRange f x := by
      rw [span_le]; rintro _ ⟨i, rfl⟩; exact hGStan x hx i
    have h₁ : finrank ℝ (tangentRange f x) = finrank ℝ E := finrank_tangentRange f (himm x)
    have h₂ : finrank ℝ (span ℝ (Set.range fun i : Fin (finrank ℝ E) =>
        gramSchmidtFrame (V := V) Y₀ (Fin.castLE hn i) x)) = finrank ℝ E := by
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    exact Submodule.eq_of_le_of_finrank_le hle (le_of_eq (h₁.trans h₂.symm))

end Adapted

end LeeLib.Ch02

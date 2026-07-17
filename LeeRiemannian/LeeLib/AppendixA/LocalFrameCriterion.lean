/-
Appendix A, "Review of Smooth Manifolds", §"Vector Bundles": the local frame
criterion for smoothness.

Lee's Lemma A.33: if `(σ_i)` is a smooth local frame for a smooth vector bundle
`E → M` over an open `U ⊆ M`, a rough section `τ` is smooth on `U` **iff** its
component functions with respect to `(σ_i)` are smooth.

Mathlib has one direction for an arbitrary smooth local frame
(`IsLocalFrameOn.contMDiffOn_of_coeff`: smooth components ⇒ smooth section), and
it has *both* directions for the special frames induced by a trivialization
(`Bundle.Trivialization.contMDiffAt_iff_localFrame_coeff`).  The remaining
direction — a smooth section has smooth components in an **arbitrary** smooth
local frame — is missing, and it is the one that carries content.  Mathlib's own
`LocalFrame.lean` flags the gap in a docstring ("In many contexts, this
statement holds for *any* local frame ... as is proven in `OrthonormalFrame.lean`"),
but no such file exists in the pin.  This file supplies it.

The proof compares the given frame `σ` with the frame induced by a trivialization
`e` around the point.  Both are frames, so the change of basis between them is
invertible; the content is that its inverse varies smoothly.  Rather than
computing that inverse as an adjugate over a determinant — which would drag in
smoothness of `Matrix.det` and of every cofactor — we package the change of basis
as a *continuous linear map*

  `frameCLM e σ y : (ι → 𝕜) →L[𝕜] F`,  `c ↦ ∑ j, c j • (e ⟨y, σ j y⟩).2`,

read the defining identity `τ y = ∑ j, c_j(y) • σ_j(y)` through `e` as

  `frameCLM e σ y (c y) = (e ⟨y, τ y⟩).2`,

and invert it with `ContinuousLinearMap.inverse`, whose smoothness at an
invertible point is mathlib's `contDiffAt_map_inverse`.  So

  `c y = inverse (frameCLM e σ y) ((e ⟨y, τ y⟩).2)`,

a composition of smooth maps.  `frameCLM` is smooth in `y` because each
`y ↦ (e ⟨y, σ j y⟩).2` is (that is `Trivialization.contMDiffAt_section_iff`
applied to the frame section `σ j`) and `smulRight` is continuous-linear in that
argument.  Invertibility at the base point is exactly the statement that both
`(σ_j y)` and `e` present `V y`; no determinant is ever computed.

The `CompleteSpace 𝕜` and `FiniteDimensional 𝕜 F` hypotheses are the ones
mathlib's trivialization-frame version already carries; `Fintype ι` is forced by
`IsLocalFrameOn` (`fintypeOfFiniteDimensional`) but is taken as a hypothesis so
that the norm on `ι → 𝕜` is not built from a derived instance.

`IsLocalFrameOn.contMDiffAt_coeff` is the pointwise form and
`IsLocalFrameOn.contMDiffOn_iff_coeff` the iff on an open set — the faithful
reading of Lemma A.33.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

open Bundle Filter Function Module Topology
open scoped Bundle Manifold ContDiff

namespace LeeLib.AppendixA

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {I : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)] [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {ι : Type*} [Fintype ι] [DecidableEq ι]
  {n : ℕ∞ω} {s : ι → (x : M) → V x} {t : (x : M) → V x} {u : Set M} {x : M}

/-! ### The change of basis from a local frame to a trivialization, as a bundled map -/

section FrameCLM

variable (𝕜)
variable (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))

/-- The frame `(σ_j)` read in the trivialization `e` at the point `y`, as a continuous linear
map `(ι → 𝕜) →L[𝕜] F` sending a coefficient vector `c` to `∑ j, c j • (e ⟨y, σ j y⟩).2`.

This is the change of basis from `(σ_j y)` to the basis of `V y` that `e` induces, except that
it is stated without ever mentioning either basis: on the nose it is a map out of the
coefficient space `ι → 𝕜`.  Where `(σ_j y)` is a basis of `V y` it is invertible
(`frameCLM_bijective`), and it is smooth in `y` for a smooth frame
(`contMDiffAt_frameCLM`). -/
noncomputable def frameCLM (s : ι → (x : M) → V x) (y : M) : (ι → 𝕜) →L[𝕜] F :=
  ∑ j : ι, ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) F
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) j) (e ⟨y, s j y⟩).2

@[simp]
theorem frameCLM_apply (s : ι → (x : M) → V x) (y : M) (c : ι → 𝕜) :
    frameCLM 𝕜 e s y c = ∑ j : ι, c j • (e ⟨y, s j y⟩).2 := by
  simp [frameCLM, ContinuousLinearMap.sum_apply]

/-- On the base set of `e`, `frameCLM 𝕜 e s y` is the coefficient-space presentation of the
map `c ↦ ∑ j, c j • s j y` into `V y`, read through `e`. -/
theorem frameCLM_eq_linearEquivAt [MemTrivializationAtlas e] (s : ι → (x : M) → V x) {y : M}
    (hy : y ∈ e.baseSet) (c : ι → 𝕜) :
    frameCLM 𝕜 e s y c = e.linearEquivAt 𝕜 y hy (∑ j : ι, c j • s j y) := by
  rw [frameCLM_apply, map_sum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [map_smul, Trivialization.linearEquivAt_apply]

end FrameCLM

/-! ### Lee's Lemma A.33: the missing direction -/

section Criterion

variable [ContMDiffVectorBundle n F V I]

/-- Where the frame is a basis of the fibre, the change of basis is bijective: it is the
composite of the coefficient isomorphism of that basis with the trivialization. -/
theorem frameCLM_bijective
    {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
    (hs : IsLocalFrameOn I F n s u) (hx : x ∈ u) (hxe : x ∈ e.baseSet) :
    Function.Bijective (frameCLM 𝕜 e s x) := by
  have key : (frameCLM 𝕜 e s x : (ι → 𝕜) → F)
      = fun c => (e.linearEquivAt 𝕜 x hxe) ((hs.toBasisAt hx).equivFun.symm c) := by
    funext c
    rw [frameCLM_eq_linearEquivAt 𝕜 e s hxe, Basis.equivFun_symm_apply]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by rw [hs.toBasisAt_coe hx j]
  rw [key]
  exact (e.linearEquivAt 𝕜 x hxe).bijective.comp (hs.toBasisAt hx).equivFun.symm.bijective

/-- `frameCLM` of a `C^n` local frame is `C^n` in the base point. -/
theorem contMDiffAt_frameCLM
    {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x ∈ u) (hxe : x ∈ e.baseSet) :
    ContMDiffAt I 𝓘(𝕜, (ι → 𝕜) →L[𝕜] F) n (frameCLM 𝕜 e s) x := by
  refine ContMDiffAt.sum (t := Finset.univ) fun j _ => ?_
  -- `y ↦ (e ⟨y, s j y⟩).2` is `C^n` because `s j` is a `C^n` section
  have hsec : ContMDiffAt I 𝓘(𝕜, F) n (fun y => (e ⟨y, s j y⟩).2) x :=
    (e.contMDiffAt_section_iff hxe).1 (hs.contMDiffAt hu hx j)
  -- and `smulRight` is continuous-linear in that argument
  exact (ContinuousLinearMap.smulRightL 𝕜 (ι → 𝕜) F
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : ι => 𝕜) j)).contMDiff.contMDiffAt.comp x hsec

/-- **Lee's Lemma A.33, the direction missing from mathlib**: the components of a `C^n` section
with respect to an *arbitrary* `C^n` local frame are `C^n`.

Mathlib proves this only for the frame induced by a trivialization
(`Bundle.Trivialization.contMDiffAt_localFrame_coeff`); the general statement is obtained from
it by inverting the change of basis, which is smooth by `contDiffAt_map_inverse`. -/
theorem _root_.IsLocalFrameOn.contMDiffAt_coeff
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) (hx : x ∈ u)
    (ht : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (t y)) x) (i : ι) :
    ContMDiffAt I 𝓘(𝕜) n (fun y => hs.coeff i y (t y)) x := by
  classical
  set e := trivializationAt F V x with he
  have hxe : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  -- `frameCLM 𝕜 e s y` carries the coefficient vector of `t y` to `t y` read in `e`,
  -- on all of `u ∩ e.baseSet`
  have hkey : ∀ y ∈ u ∩ e.baseSet,
      frameCLM 𝕜 e s y (fun j => hs.coeff j y (t y)) = (e ⟨y, t y⟩).2 := by
    rintro y ⟨hyu, hye⟩
    rw [frameCLM_eq_linearEquivAt 𝕜 e s hye, ← hs.coeff_sum_eq t hyu,
      Trivialization.linearEquivAt_apply]
  -- `inverse (frameCLM e s ·)` is `C^n` at `x`, since `frameCLM 𝕜 e s x` is invertible
  have hinv : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] (ι → 𝕜)) n
      (fun y => ContinuousLinearMap.inverse (frameCLM 𝕜 e s y)) x := by
    have hΦ : ContDiffAt 𝕜 n (ContinuousLinearMap.inverse : ((ι → 𝕜) →L[𝕜] F) → _)
        (frameCLM 𝕜 e s x) := by
      have hbij := frameCLM_bijective hs hx hxe
      have : ((LinearEquiv.ofBijective (frameCLM 𝕜 e s x : (ι → 𝕜) →ₗ[𝕜] F)
          hbij).toContinuousLinearEquiv : (ι → 𝕜) →L[𝕜] F) = frameCLM 𝕜 e s x := by
        ext c; rfl
      rw [← this]
      exact contDiffAt_map_inverse _
    exact (contMDiffAt_iff_contDiffAt.2 hΦ).comp x (contMDiffAt_frameCLM hs hu hx hxe)
  -- `y ↦ (e ⟨y, t y⟩).2` is `C^n`
  have hsec : ContMDiffAt I 𝓘(𝕜, F) n (fun y => (e ⟨y, t y⟩).2) x :=
    (e.contMDiffAt_section_iff hxe).1 ht
  -- so the whole coefficient vector is `C^n` at `x`, once we know it equals the
  -- composite near `x`
  have hcv : ContMDiffAt I 𝓘(𝕜, ι → 𝕜) n (fun y => fun j => hs.coeff j y (t y)) x := by
    refine (hinv.clm_apply hsec).congr_of_eventuallyEq ?_
    filter_upwards [(hu.inter e.open_baseSet).mem_nhds ⟨hx, hxe⟩] with y hy
    rw [← hkey y hy]
    have hbijy := frameCLM_bijective hs hy.1 hy.2
    set Φy := (LinearEquiv.ofBijective (frameCLM 𝕜 e s y : (ι → 𝕜) →ₗ[𝕜] F)
      hbijy).toContinuousLinearEquiv with hΦy
    have hΦycoe : (Φy : (ι → 𝕜) →L[𝕜] F) = frameCLM 𝕜 e s y := by ext c; rfl
    rw [← hΦycoe, ContinuousLinearMap.inverse_equiv]
    exact (Φy.symm_apply_apply _).symm
  exact contMDiffAt_pi_space.1 hcv i

/-- **Lee's Lemma A.33**, on an open set: a rough section is `C^n` on `u` iff its components
with respect to a `C^n` local frame on `u` are `C^n` on `u`.

The `←` direction is mathlib's `IsLocalFrameOn.contMDiffOn_of_coeff`; the `→` direction is
`IsLocalFrameOn.contMDiffAt_coeff` above. -/
theorem _root_.IsLocalFrameOn.contMDiffOn_iff_coeff
    (hs : IsLocalFrameOn I F n s u) (hu : IsOpen u) :
    ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun y => TotalSpace.mk' F y (t y)) u ↔
      ∀ i, ContMDiffOn I 𝓘(𝕜) n (fun y => hs.coeff i y (t y)) u := by
  refine ⟨fun ht i y hy => ?_, fun h => hs.contMDiffOn_of_coeff (t := t) h⟩
  exact (hs.contMDiffAt_coeff hu hy (ht.contMDiffAt (hu.mem_nhds hy)) i).contMDiffWithinAt

end Criterion

/-! ### Smooth local sections through a prescribed basis of one fibre

A basis of a *single* fibre `V x₀` extends to a family of sections, smooth near `x₀`, taking
those prescribed values at `x₀`.  The sections are the ones that are constant when read in a
trivialization around `x₀`.

Mathlib has the construction — `Bundle.Trivialization.localFrame`, together with its
smoothness — but only for a basis of the *model* fibre `F`, which prescribes nothing at any
particular point.  The gap is exactly the prescribed value, and it is closed by feeding
`localFrame` the pushforward `w.map (e.linearEquivAt 𝕜 x₀ hx₀)`: the round trip through `e`
at `x₀` then collapses to `Trivialization.symm_apply_apply_mk`. -/

section PrescribedBasis

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [Fintype ι] [DecidableEq ι]

variable (I n)

/-- **Smooth sections through a prescribed basis** (Lee, the lemma behind Proposition 2.66):
given a basis `(w_i)` of the fibre `V x₀`, there are an open `v ∋ x₀` and sections `(Y_i)` of
`V`, `C^n` on `v`, with `Y_i x₀ = w_i`.

`LeeLib.Ch02.PseudoOrthonormalFrame` uses this to turn a *nondegenerate* basis of `T_p M` —
which is what the indefinite Gram-Schmidt requires as input, and which an arbitrary frame need
not provide — into a family of vector fields near `p`. -/
theorem exists_contMDiffOn_section_eq_basis [ContMDiffVectorBundle n F V I]
    (x₀ : M) (w : Basis ι 𝕜 (V x₀)) :
    ∃ (v : Set M) (Y : ι → (x : M) → V x), IsOpen v ∧ x₀ ∈ v ∧
      (∀ i, ContMDiffOn I (I.prod 𝓘(𝕜, F)) n (fun x => TotalSpace.mk' F x (Y i x)) v) ∧
      ∀ i, Y i x₀ = w i := by
  set e := trivializationAt F V x₀ with he
  have hx₀ : x₀ ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x₀
  refine ⟨e.baseSet, e.localFrame (w.map (e.linearEquivAt 𝕜 x₀ hx₀)), e.open_baseSet, hx₀,
    fun i => e.contMDiffOn_localFrame_baseSet n _ i, fun i => ?_⟩
  rw [e.localFrame_apply_of_mem_baseSet _ hx₀]
  simp only [Trivialization.basisAt, Basis.map_apply, Trivialization.linearEquivAt_apply,
    Trivialization.linearEquivAt_symm_apply]
  exact e.symm_apply_apply_mk hx₀ (w i)

end PrescribedBasis

end LeeLib.AppendixA

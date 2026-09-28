import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3

/-!
# Parametrized-surface regularity

This file supplies an order-graded, backward-compatible refinement of the
parametrized-surface interface in `DoCarmoCh3`.  The legacy predicate remains
the order-one map-regularity component.  A separate extended predicate records
the connected planar domain, its open core, and the open-neighborhood extension
used by do Carmo's definition.

The book's remaining boundary clause (a piecewise differentiable boundary with
non-straight vertex angles) needs an explicit boundary parametrization and
vertex data.  Neither is carried by the legacy surface type, so that clause is
not silently approximated here.
-/

open Manifold Set
open scoped ContDiff Manifold Topology ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The order-graded map-regularity component of do Carmo Ch. 3,
Definition 3.3.  At order one this is definitionally the legacy
`IsParametrizedSurface` predicate. -/
def IsParametrizedSurfaceOfOrder (I : ModelWithCorners ℝ E H) (r : ℕ∞ω)
    (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I r s A

/-- **Math.** A parametrized surface smooth to every finite order on its
parameter set. -/
abbrev IsSmoothParametrizedSurface (I : ModelWithCorners ℝ E H)
    (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop :=
  IsParametrizedSurfaceOfOrder I ∞ A s

namespace IsParametrizedSurfaceOfOrder

variable {r r' : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

/-- **Math.** A surface of order `r` is a surface of every lower order. -/
theorem of_le (hs : IsParametrizedSurfaceOfOrder I r A s) (hrr' : r' ≤ r) :
    IsParametrizedSurfaceOfOrder I r' A s :=
  _root_.ContMDiffOn.of_le hs hrr'

/-- **Math.** Forgetting regularity above `C¹` gives the legacy Ch. 3
parametrized-surface predicate. -/
theorem isParametrizedSurface (hs : IsParametrizedSurfaceOfOrder I r A s)
    (hr : (1 : ℕ∞ω) ≤ r) : IsParametrizedSurface (I := I) A s :=
  _root_.ContMDiffOn.of_le hs hr

end IsParametrizedSurfaceOfOrder

namespace IsParametrizedSurface

variable {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

/-- **Math.** The legacy parametrized-surface predicate is exactly the
order-one member of the graded hierarchy. -/
theorem isParametrizedSurfaceOfOrderOne (hs : IsParametrizedSurface (I := I) A s) :
    IsParametrizedSurfaceOfOrder I 1 A s :=
  hs

end IsParametrizedSurface

/-- **Math.** The encodable planar-domain clauses in do Carmo Ch. 3,
Definition 3.3: `A` is connected and contains an open core whose closure
contains `A`.

The inclusions are non-strict, as is standard for the book's notation
`U ⊂ A ⊂ closure U`; this also admits the important case where `A` itself is
open. -/
structure ParametrizedSurfaceDomain (A : Set (ℝ × ℝ)) : Prop where
  connected : IsConnected A
  exists_openCore : ∃ U : Set (ℝ × ℝ), IsOpen U ∧ U ⊆ A ∧ A ⊆ closure U

namespace ParametrizedSurfaceDomain

variable {A : Set (ℝ × ℝ)}

/-- **Math.** A connected open set is a valid surface domain, with itself as
its open core. -/
theorem of_isOpen (hA : IsOpen A) (hconnected : IsConnected A) :
    ParametrizedSurfaceDomain A :=
  ⟨hconnected, A, hA, Subset.rfl, subset_closure⟩

end ParametrizedSurfaceDomain

/-- **Math.** The domain-and-extension portion of do Carmo Ch. 3,
Definition 3.3 at differentiability order `r`.  The globally represented map
`s` must be `C^r` on an open neighborhood of `A`, making its ambient partial
derivatives meaningful even at boundary points. -/
structure IsExtendedParametrizedSurfaceOfOrder (I : ModelWithCorners ℝ E H)
    (r : ℕ∞ω) (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop where
  domain : ParametrizedSurfaceDomain A
  exists_extension : ∃ U : Set (ℝ × ℝ),
    IsOpen U ∧ A ⊆ U ∧ ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I r s U

/-- **Math.** A smooth parametrized surface with the connected-domain and
open-extension data of do Carmo's definition. -/
abbrev IsSmoothExtendedParametrizedSurface (I : ModelWithCorners ℝ E H)
    (A : Set (ℝ × ℝ)) (s : ℝ × ℝ → M) : Prop :=
  IsExtendedParametrizedSurfaceOfOrder I ∞ A s

namespace IsExtendedParametrizedSurfaceOfOrder

variable {r r' : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

/-- **Math.** Restricting the open extension to `A` recovers the graded
map-regularity predicate. -/
theorem regularOn (hs : IsExtendedParametrizedSurfaceOfOrder I r A s) :
    IsParametrizedSurfaceOfOrder I r A s := by
  rcases hs.exists_extension with ⟨U, _hU, hAU, hsU⟩
  exact hsU.mono hAU

/-- **Math.** An extended surface may be viewed at every lower
differentiability order without changing its domain or extension. -/
theorem of_le (hs : IsExtendedParametrizedSurfaceOfOrder I r A s) (hrr' : r' ≤ r) :
    IsExtendedParametrizedSurfaceOfOrder I r' A s := by
  refine ⟨hs.domain, ?_⟩
  rcases hs.exists_extension with ⟨U, hU, hAU, hsU⟩
  exact ⟨U, hU, hAU, _root_.ContMDiffOn.of_le hsU hrr'⟩

/-- **Math.** Forgetting the domain and extension data, and all regularity
above `C¹`, gives the legacy parametrized-surface predicate. -/
theorem isParametrizedSurface (hs : IsExtendedParametrizedSurfaceOfOrder I r A s)
    (hr : (1 : ℕ∞ω) ≤ r) : IsParametrizedSurface (I := I) A s :=
  hs.regularOn.isParametrizedSurface hr

/-- **Math.** A regular map on a connected open parameter set is an extended
parametrized surface, using that set both as core and extension neighborhood. -/
theorem of_isOpen (hA : IsOpen A) (hconnected : IsConnected A)
    (hs : IsParametrizedSurfaceOfOrder I r A s) :
    IsExtendedParametrizedSurfaceOfOrder I r A s :=
  ⟨ParametrizedSurfaceDomain.of_isOpen hA hconnected,
    ⟨A, hA, Subset.rfl, hs⟩⟩

/-- **Math.** The open extension is differentiable at every point of the
surface domain as soon as its order is at least one. -/
theorem mdifferentiableAt (hs : IsExtendedParametrizedSurfaceOfOrder I r A s)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ A) :
    MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I s q := by
  rcases hs.exists_extension with ⟨U, hU, hAU, hsU⟩
  have hsU1 : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 s U :=
    _root_.ContMDiffOn.of_le hsU hr
  exact (hsU1.mdifferentiableOn one_ne_zero q (hAU hq)).mdifferentiableAt
    (hU.mem_nhds (hAU hq))

end IsExtendedParametrizedSurfaceOfOrder

/-- **Math.** The `u`-slice through a two-parameter map. -/
def surfaceSliceU (s : ℝ × ℝ → M) (v : ℝ) : ℝ → M :=
  fun u ↦ s (u, v)

/-- **Math.** The `v`-slice through a two-parameter map. -/
def surfaceSliceV (s : ℝ × ℝ → M) (u : ℝ) : ℝ → M :=
  fun v ↦ s (u, v)

namespace IsParametrizedSurfaceOfOrder

variable {r : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

/-- **Math.** Every fixed-`v` slice inherits the full regularity order of the
surface on the corresponding section of its parameter set. -/
theorem surfaceSliceU_contMDiffOn (hs : IsParametrizedSurfaceOfOrder I r A s)
    (v : ℝ) : ContMDiffOn 𝓘(ℝ, ℝ) I r (surfaceSliceU s v)
      {u : ℝ | (u, v) ∈ A} := by
  have hι : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) r
      (fun u : ℝ ↦ (u, v)) {u : ℝ | (u, v) ∈ A} :=
    contMDiffOn_id.prodMk_space contMDiffOn_const
  have hmap : {u : ℝ | (u, v) ∈ A} ⊆ (fun u : ℝ ↦ (u, v)) ⁻¹' A :=
    fun _ hu ↦ hu
  change ContMDiffOn 𝓘(ℝ, ℝ) I r (s ∘ fun u : ℝ => (u, v)) {u : ℝ | (u, v) ∈ A}
  exact hs.comp hι hmap

/-- **Math.** Every fixed-`u` slice inherits the full regularity order of the
surface on the corresponding section of its parameter set. -/
theorem surfaceSliceV_contMDiffOn (hs : IsParametrizedSurfaceOfOrder I r A s)
    (u : ℝ) : ContMDiffOn 𝓘(ℝ, ℝ) I r (surfaceSliceV s u)
      {v : ℝ | (u, v) ∈ A} := by
  have hι : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) r
      (fun v : ℝ ↦ (u, v)) {v : ℝ | (u, v) ∈ A} :=
    contMDiffOn_const.prodMk_space contMDiffOn_id
  have hmap : {v : ℝ | (u, v) ∈ A} ⊆ (fun v : ℝ ↦ (u, v)) ⁻¹' A :=
    fun _ hv ↦ hv
  change ContMDiffOn 𝓘(ℝ, ℝ) I r (s ∘ fun v : ℝ => (u, v)) {v : ℝ | (u, v) ∈ A}
  exact hs.comp hι hmap

end IsParametrizedSurfaceOfOrder

namespace IsExtendedParametrizedSurfaceOfOrder

variable {r : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

/-- **Math.** At a point of an extended surface, the ambient `u`-partial is
the derivative of the fixed-`v` slice. -/
theorem partialU_eq_slice_mfderiv
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ A) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I s q (1, 0) =
      mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceU s q.2) q.1 1 := by
  have hsAt : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I s q := hs.mdifferentiableAt hr hq
  have hι : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun u : ℝ ↦ (u, q.2)) q.1 :=
    (contMDiff_id.prodMk_space contMDiff_const).mdifferentiableAt one_ne_zero
  have hι_one : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun u : ℝ ↦ (u, q.2)) q.1 1 = (1, 0) := by
    have hι_deriv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun u : ℝ ↦ (u, q.2)) q.1 = ContinuousLinearMap.inl ℝ ℝ ℝ :=
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) q.1 q.2).hasMFDerivAt.mfderiv
    rw [hι_deriv]
    rfl
  have hchain := mfderiv_comp_apply q.1 hsAt hι (1 : ℝ)
  rw [hι_one] at hchain
  change mfderiv 𝓘(ℝ, ℝ × ℝ) I s q (1, 0) =
    mfderiv 𝓘(ℝ, ℝ) I (s ∘ fun u : ℝ => (u, q.2)) q.1 1
  exact hchain.symm

/-- **Math.** At a point of an extended surface, the ambient `v`-partial is
the derivative of the fixed-`u` slice. -/
theorem partialV_eq_slice_mfderiv
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ A) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) I s q (0, 1) =
      mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceV s q.1) q.2 1 := by
  have hsAt : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I s q := hs.mdifferentiableAt hr hq
  have hι : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun v : ℝ ↦ (q.1, v)) q.2 :=
    (contMDiff_const.prodMk_space contMDiff_id).mdifferentiableAt one_ne_zero
  have hι_one : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
      (fun v : ℝ ↦ (q.1, v)) q.2 1 = (0, 1) := by
    have hι_deriv : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ)
        (fun v : ℝ ↦ (q.1, v)) q.2 = ContinuousLinearMap.inr ℝ ℝ ℝ :=
      (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2).hasMFDerivAt.mfderiv
    rw [hι_deriv]
    rfl
  have hchain := mfderiv_comp_apply q.2 hsAt hι (1 : ℝ)
  rw [hι_one] at hchain
  change mfderiv 𝓘(ℝ, ℝ × ℝ) I s q (0, 1) =
    mfderiv 𝓘(ℝ, ℝ) I (s ∘ fun v : ℝ => (q.1, v)) q.2 1
  exact hchain.symm

end IsExtendedParametrizedSurfaceOfOrder

namespace ParametrizedSurface

variable {r : ℕ∞ω}

/-- **Math.** The legacy bundled `partialU` agrees with the derivative of the
fixed-`v` slice whenever the surface has an order-at-least-one open extension. -/
theorem partialU_eq_slice_mfderiv (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) :
    S.partialU q = mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceU S.toFun q.2) q.1 1 :=
  hS.partialU_eq_slice_mfderiv hr hq

/-- **Math.** The legacy bundled `partialV` agrees with the derivative of the
fixed-`u` slice whenever the surface has an order-at-least-one open extension. -/
theorem partialV_eq_slice_mfderiv (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) :
    S.partialV q = mfderiv 𝓘(ℝ, ℝ) I (surfaceSliceV S.toFun q.1) q.2 1 :=
  hS.partialV_eq_slice_mfderiv hr hq

end ParametrizedSurface

end Geodesic
end Riemannian

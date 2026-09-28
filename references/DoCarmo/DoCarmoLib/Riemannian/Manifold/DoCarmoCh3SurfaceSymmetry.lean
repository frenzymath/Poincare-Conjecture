import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3SurfaceReadback
import DoCarmoLib.Riemannian.Geodesic.SymmetryLemma

/-!
# The symmetry lemma for a Definition 3.3 surface (do Carmo Ch. 3, Lemma 3.4)

`SymmetryLemma.lean` proves Lemma 3.4 in chart coordinates, against *explicitly
supplied* derivative data: `hc : ∀ᶠ y in 𝓝 x, HasFDerivAt c (Dc y) y` and
`hc2 : HasFDerivAt Dc D2c x`.  Every downstream consumer (the Gauss lemma, the
variation formulas) therefore builds its surface by hand as a chart map into `E`
and supplies that data itself, which is why the Definition 3.3 predicates of
`DoCarmoCh3SurfaceRegularity` had no consumers at all.

This file closes that gap in the direction that matters: it *derives* the
derivative data from the book's hypothesis.  Given a surface `s : ℝ × ℝ → M`
that is `C^r` (`r ≥ 2`) on an open neighborhood of its parameter set — do
Carmo's own hypothesis, since his "differentiable" is `C^∞` — the chart reading
`F = φ_α ∘ s` automatically has a first derivative near each interior parameter
and a second derivative at it.  Composing with the symmetry lemma gives Lemma
3.4 as a statement whose only hypothesis is that `s` is a parametrized surface.

* `IsExtendedParametrizedSurfaceOfOrder.eventually_hasFDerivAt_extChartAt` —
  the chart reading is differentiable near an interior parameter.
* `IsExtendedParametrizedSurfaceOfOrder.hasFDerivAt_fderiv_extChartAt` — its
  derivative is itself differentiable there.
* `covariant_sndFDeriv_symm_of_surface` — Lemma 3.4 for such a surface, with the
  derivative data supplied by the predicate rather than by the caller.
* `ParametrizedSurface.chartPartialU_eq_partialU` /
  `chartPartialV_eq_partialV` — the coordinate partials appearing in that
  identity are the chart readings of the book's `∂s/∂u`, `∂s/∂v`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 3, Definition 3.3 and Lemma 3.4.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian
namespace Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! `I.Boundaryless` is introduced per-section rather than as a blanket section
variable, so that each declaration's need for it is visible.  It is genuinely
load-bearing wherever it appears: the chart-reading regularity lemmas below go
through mathlib's `contMDiffOn_extChartAt`, which requires a boundaryless model,
and `covariant_sndFDeriv_symm_of_surface` inherits it from those.  (The engine
`covariant_sndFDeriv_symm_of_eventually` itself does *not* need it — the
requirement enters only with deriving the derivative data from the surface
predicate, which is worth knowing if the boundary case is ever wanted: it needs a
boundary-tolerant replacement for that step, not a weaker symmetry lemma.) -/

namespace IsExtendedParametrizedSurfaceOfOrder

variable {r : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart reading of a parametrized surface is `C^r` on an open
neighborhood of every parameter whose image lies in the chart source at `α`.

This is the two-parameter analogue of `contDiffOn_extChartAt_comp`, with the
open neighborhood produced by intersecting the surface's own extension domain
with the preimage of the chart source. -/
theorem exists_isOpen_contDiffOn_extChartAt_comp
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s) {m : ℕ} (hm : (m : ℕ∞ω) ≤ r)
    {q : ℝ × ℝ} (hq : q ∈ A)
    {α : M} (hsrc : s q ∈ (chartAt H α).source) :
    ∃ V : Set (ℝ × ℝ), IsOpen V ∧ q ∈ V ∧
      ContDiffOn ℝ m (fun p => extChartAt I α (s p)) V := by
  obtain ⟨U, hU, hAU, hsU⟩ := hs.exists_extension
  refine ⟨U ∩ s ⁻¹' (chartAt H α).source, ?_, ⟨hAU hq, hsrc⟩, ?_⟩
  · exact hsU.continuousOn.isOpen_inter_preimage hU (chartAt H α).open_source
  · rw [← contMDiffOn_iff_contDiffOn]
    exact ((contMDiffOn_extChartAt (n := (∞ : ℕ∞ω)) (x := α)).of_le
        (by exact_mod_cast le_top)).comp
      ((hsU.of_le hm).mono inter_subset_left) fun p hp => hp.2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart reading of a `C^r` surface (`r ≥ 1`) is differentiable at
every parameter *near* an interior one, which is the `∀ᶠ` hypothesis the
symmetry lemma asks for. -/
theorem eventually_hasFDerivAt_extChartAt
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s) (hr : (1 : ℕ∞ω) ≤ r)
    {q : ℝ × ℝ} (hq : q ∈ A) {α : M} (hsrc : s q ∈ (chartAt H α).source) :
    ∀ᶠ p in 𝓝 q, HasFDerivAt (fun p' => extChartAt I α (s p'))
      (fderiv ℝ (fun p' => extChartAt I α (s p')) p) p := by
  obtain ⟨V, hV, hqV, hsV⟩ :=
    hs.exists_isOpen_contDiffOn_extChartAt_comp (m := 1) (by exact_mod_cast hr) hq hsrc
  filter_upwards [hV.mem_nhds hqV] with p hp
  exact ((hsV.differentiableOn (by norm_num) p hp).differentiableAt
    (hV.mem_nhds hp)).hasFDerivAt

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The derivative of the chart reading of a `C^r` surface (`r ≥ 2`) is
itself differentiable at an interior parameter — the second-derivative
hypothesis of the symmetry lemma.  `C^2` is exactly what Lemma 3.4 needs, and it
is available because do Carmo's surfaces are `C^∞`. -/
theorem hasFDerivAt_fderiv_extChartAt
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s) (hr : (2 : ℕ∞ω) ≤ r)
    {q : ℝ × ℝ} (hq : q ∈ A) {α : M} (hsrc : s q ∈ (chartAt H α).source) :
    HasFDerivAt (fun p => fderiv ℝ (fun p' => extChartAt I α (s p')) p)
      (fderiv ℝ (fun p => fderiv ℝ (fun p' => extChartAt I α (s p')) p) q) q := by
  obtain ⟨V, hV, hqV, hsV⟩ :=
    hs.exists_isOpen_contDiffOn_extChartAt_comp (m := 2) (by exact_mod_cast hr) hq hsrc
  have h2 : ContDiffAt ℝ 2 (fun p' => extChartAt I α (s p')) q :=
    (hsV.contDiffWithinAt hqV).contDiffAt (hV.mem_nhds hqV)
  have hone : ContDiffAt ℝ 1
      (fun p => fderiv ℝ (fun p' => extChartAt I α (s p')) p) q :=
    ContDiffAt.fderiv_right_succ (n := 1) (h2.of_le (by norm_num))
  exact (hone.differentiableAt (by norm_num)).hasFDerivAt

end IsExtendedParametrizedSurfaceOfOrder

/-- **Math.** **Symmetry lemma (do Carmo Ch. 3, Lemma 3.4) for a parametrized
surface.**  Let `s : ℝ × ℝ → M` be a Definition 3.3 parametrized surface of
order `r ≥ 2` on `A` (do Carmo's own hypothesis: his "differentiable" is
`C^∞`), let `q ∈ A` with `s q` in the chart source at `α`, and write
`F = φ_α ∘ s` for the chart reading.  Then for all directions `v, w`,

`D²F·v·w + Γ_α(DF·v, DF·w)(F q) = D²F·w·v + Γ_α(DF·w, DF·v)(F q)`,

which is `D/∂v (∂s/∂u) = D/∂u (∂s/∂v)` read in the chart at `α`.

Unlike `covariant_sndFDeriv_symm_of_eventually`, the derivative data is *not* a
hypothesis: `DF` and `D²F` are the actual Fréchet derivatives of the chart
reading, and their existence is derived from the surface predicate.  This makes
Definition 3.3 the hypothesis of Lemma 3.4, as in the book. -/
theorem covariant_sndFDeriv_symm_of_surface (g : RiemannianMetric I M) (α : M)
    {r : ℕ∞ω} {A : Set (ℝ × ℝ)} {s : ℝ × ℝ → M}
    (hs : IsExtendedParametrizedSurfaceOfOrder I r A s) (hr : (2 : ℕ∞ω) ≤ r)
    {q : ℝ × ℝ} (hq : q ∈ A) (hsrc : s q ∈ (chartAt H α).source)
    (v w : ℝ × ℝ) :
    letI F : ℝ × ℝ → E := fun p => extChartAt I α (s p)
    letI DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E) := fun p => fderiv ℝ F p
    letI D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E := fderiv ℝ DF q
    D2F v w + chartChristoffelContraction (I := I) g α (DF q v) (DF q w) (F q)
      = D2F w v + chartChristoffelContraction (I := I) g α (DF q w) (DF q v) (F q) :=
  covariant_sndFDeriv_symm_of_eventually g α
    (hs.eventually_hasFDerivAt_extChartAt (le_trans (by norm_num) hr) hq hsrc)
    (hs.hasFDerivAt_fderiv_extChartAt hr hq hsrc) v w

namespace ParametrizedSurface

variable {r : ℕ∞ω}

/-! The two readback bridges below go through
`partialU_eq_of_hasFDerivAt_extChartAt`, which needs a boundaryless model. -/
variable [I.Boundaryless]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The `(1,0)` coordinate partial of the chart reading is the chart
reading of the book's `∂s/∂u`, so the `DF·v` appearing in
`covariant_sndFDeriv_symm_of_surface` at `v = (1,0)` really is Definition 3.3's
`u`-partial. -/
theorem chartPartialU_eq_partialU (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) {α : M}
    (hsrc : S.toFun q ∈ (chartAt H α).source) :
    S.partialU q = tangentCoordChange I α (S.toFun q) (S.toFun q)
      (fderiv ℝ (fun p => extChartAt I α (S.toFun p)) q (1, 0)) := by
  obtain ⟨V, hV, hqV, hsV⟩ :=
    hS.exists_isOpen_contDiffOn_extChartAt_comp (m := 1) (by exact_mod_cast hr) hq hsrc
  exact S.partialU_eq_of_hasFDerivAt_extChartAt hS hr hq
    ((hS.mdifferentiableAt hr hq).continuousAt) hsrc
    ((hsV.differentiableOn (by norm_num) q hqV).differentiableAt (hV.mem_nhds hqV)).hasFDerivAt

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The `(0,1)` coordinate partial of the chart reading is the chart
reading of the book's `∂s/∂v`. -/
theorem chartPartialV_eq_partialV (S : ParametrizedSurface (I := I) (M := M))
    (hS : IsExtendedParametrizedSurfaceOfOrder I r S.domain S.toFun)
    (hr : (1 : ℕ∞ω) ≤ r) {q : ℝ × ℝ} (hq : q ∈ S.domain) {α : M}
    (hsrc : S.toFun q ∈ (chartAt H α).source) :
    S.partialV q = tangentCoordChange I α (S.toFun q) (S.toFun q)
      (fderiv ℝ (fun p => extChartAt I α (S.toFun p)) q (0, 1)) := by
  obtain ⟨V, hV, hqV, hsV⟩ :=
    hS.exists_isOpen_contDiffOn_extChartAt_comp (m := 1) (by exact_mod_cast hr) hq hsrc
  exact S.partialV_eq_of_hasFDerivAt_extChartAt hS hr hq
    ((hS.mdifferentiableAt hr hq).continuousAt) hsrc
    ((hsV.differentiableOn (by norm_num) q hqV).differentiableAt (hV.mem_nhds hqV)).hasFDerivAt

end ParametrizedSurface

end Geodesic
end Riemannian

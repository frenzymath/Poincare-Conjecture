import DoCarmoLib.Riemannian.Jacobi.JacobiManifold
import DoCarmoLib.Riemannian.Jacobi.JacobiChartTransfer

/-!
# The covariant derivative `D/dt` of a field along a curve — manifold level

do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.2 (the operator `D/dt`), in the
form Ch. 9 needs it.

Every formula of do Carmo Ch. 9 §2 — the first variation `prop:dc-ch9-2-4`, the
characterization of geodesics `prop:dc-ch9-2-5`, the second variation
`prop:dc-ch9-2-8`, formula (5) `rem:dc-ch9-2-9` and the index form
`rem:dc-ch9-2-10` — is written in terms of `D V/dt` for a field `V` along a curve
`c`.  DoCarmoLib's only covariant derivative along a curve,
`Riemannian.covariantDerivCoord` (`Geodesic/CovariantDerivative.lean`), is
**chart-fixed**: it reads the curve as `u = φ_α ∘ c : ℝ → E` and the field as
`V : ℝ → E` in one chart at a basepoint `α`, so it cannot even be *stated* for a
curve that leaves that chart.

The library's established answer — used by `IsParallelFieldAlongOn`
(`Jacobi/ParallelFieldAlong.lean`) and `IsJacobiFieldAlongOn`
(`Jacobi/JacobiManifold.lean`) — is to carry `D/dt` not as an applied operator but
as a **second field** `DV`, constrained by a *chart-local predicate*: near every
time there is some chart in which the readings of `V` and `DV` satisfy the
coordinate equation.  Chart-locality is what lets the notion survive a curve
leaving every single chart.  This file writes that predicate in its **general**
form, of which the two existing ones are the special cases `DV = 0` (parallel) and
`∇DV = -ℛ(V, γ')γ'` (Jacobi, in the Morgan–Tian curvature convention `ℛ` those
files use — see `Jacobi/PairJacobiField.lean`).

## Contents

* `IsCovariantDerivSolOn g α u V DV a b` — the chart-level certificate `∇V = DV`,
  i.e. `V' = DV - Γ(u̇, V)(u)` on `[a, b]` (one-sided derivatives at the
  endpoints).  This is exactly `IsJacobiFieldOn.hasDerivWithinAt_fst` with `DV`
  unconstrained.
* `IsCovariantDerivSolOn.covariantDerivCoord_eq` — at interior times the
  certificate says precisely `covariantDerivCoord g α u V t = DV t`.
* `IsCovariantDerivSolOn.transfer` — **chart-change covariance**.  The
  inhomogeneous second-derivative term of the transition map produced by the
  product rule cancels against the transformation law of the Christoffel
  contraction (`chartChristoffelContraction_change`).  Unlike
  `IsParallelSolOn.transfer` / `IsJacobiFieldOn.transfer`, this is stated for an
  **arbitrary** curve — only differentiability of the chart curve is assumed, not
  the geodesic equation.  That generality is essential for Ch. 9: the transversals
  of a variation are not geodesics.
* `IsCovariantDerivFieldAlongOn g γ V DV a b` — the manifold-level predicate.
* `IsCovariantDerivFieldAlongOn.isCovariantDerivSolOn_of_mem_source` —
  localization into a single chart on a subinterval.
* `IsJacobiFieldOn.isCovariantDerivSolOn` /
  `IsJacobiFieldAlongOn.isCovariantDerivFieldAlongOn` — the Jacobi bridges: a Jacobi
  field is an instance of the general predicate.  (The parallel case is **not**
  bridged here; see the note below on the `[MetricSpace M]` / `[TopologicalSpace M]`
  mismatch.)
* `IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner` — **metric compatibility /
  the Leibniz rule** `d/dt ⟨V, W⟩ = ⟨DV, W⟩ + ⟨V, DW⟩` at the manifold level (do
  Carmo Ch. 2, Prop. 3.2).  This is the analytic workhorse behind every Ch. 9
  variation formula, and generalizes `IsParallelFieldAlongOn.metricInner_const`
  (the case `DV = DW = 0`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.2 and Prop. 3.2;
Ch. 9, §2.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The chart-level certificate `∇V = DV` -/

/-- **Math.** do Carmo Ch. 2, Prop. 2.2.  **The chart-level certificate that `DV`
is the covariant derivative of `V` along `u`.**  In the chart at `α`, along the
chart curve `u`, the coordinate fields `V`, `DV` satisfy
`V'(t) = DV(t) - Γ(u̇(t), V(t))(u(t))` on `[a, b]` — i.e. `DV = V' + Γ(u̇, V)(u)`,
which is do Carmo's formula (1) for `DV/dt`.

This is `IsJacobiFieldOn.hasDerivWithinAt_fst` with `DV` left free, and
`IsParallelSolOn` is the case `DV = 0`. -/
def IsCovariantDerivSolOn (g : RiemannianMetric I M) (α : M) (u V DV : ℝ → E)
    (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt V
    (DV t - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
    (Icc a b) t

namespace IsCovariantDerivSolOn

variable {g : RiemannianMetric I M} {α : M} {u V DV : ℝ → E} {a b a' b' : ℝ}

/-- **Math.** Restriction of the certificate to a subinterval. -/
theorem mono (h : IsCovariantDerivSolOn (I := I) g α u V DV a b)
    (ha : a ≤ a') (hb : b' ≤ b) :
    IsCovariantDerivSolOn (I := I) g α u V DV a' b' :=
  fun t ht => (h t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)

/-- **Math.** The certificate propagates along a `𝓝[Icc a b]`-neighbourhood: a
family of local certificates glues, by locality of `HasDerivWithinAt`. -/
theorem mono_of_mem_nhdsWithin
    (h : IsCovariantDerivSolOn (I := I) g α u V DV a' b') {t : ℝ}
    (ht : t ∈ Icc a' b') (hnbhd : Icc a' b' ∈ 𝓝[Icc a b] t) :
    HasDerivWithinAt V
      (DV t - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
      (Icc a b) t :=
  (h t ht).mono_of_mem_nhdsWithin hnbhd

/-- **Math.** `V` is continuous on `[a, b]`: it is differentiable there. -/
theorem continuousOn (h : IsCovariantDerivSolOn (I := I) g α u V DV a b) :
    ContinuousOn V (Icc a b) :=
  fun t ht => (h t ht).continuousWithinAt

/-- **Math.** At interior times the certificate says exactly that `DV` **is** the
coordinate covariant derivative of `V` along `u`: `DV/dt = DV`. -/
theorem covariantDerivCoord_eq (h : IsCovariantDerivSolOn (I := I) g α u V DV a b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    covariantDerivCoord (I := I) g α u V t = DV t := by
  have hd := (h t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  rw [covariantDerivCoord_def, hd.deriv]
  abel

/-- **Math.** At interior times `V` is differentiable. -/
theorem differentiableAt (h : IsCovariantDerivSolOn (I := I) g α u V DV a b)
    {t : ℝ} (ht : t ∈ Ioo a b) : DifferentiableAt ℝ V t :=
  ((h t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).differentiableAt

/-- **Math.** The certificate only depends on the values of the fields on the
interval. -/
theorem congr (h : IsCovariantDerivSolOn (I := I) g α u V DV a b)
    {V' DV' : ℝ → E} (hV : ∀ t ∈ Icc a b, V' t = V t)
    (hDV : ∀ t ∈ Icc a b, DV' t = DV t) :
    IsCovariantDerivSolOn (I := I) g α u V' DV' a b := by
  intro t ht
  rw [hV t ht, hDV t ht]
  exact (h t ht).congr (fun y hy => hV y hy) (hV t ht)

end IsCovariantDerivSolOn

/-! ### The Jacobi chart certificate is a special case

A Jacobi field's *first* equation is exactly `∇J = DJ`; its second equation
constrains `DJ` further.

The parallel case `DV = 0` is **not** bridged here, and no such bridge exists yet
anywhere: `ParallelFieldAlong.lean` is stated over `[MetricSpace M]`, which cannot
be mixed into this file's more general `[TopologicalSpace M]` block without
creating a topology diamond.  Generalizing `ParallelFieldAlong.lean` to
`[TopologicalSpace M]` is the prerequisite for one. -/

/-- **Math.** A Jacobi field's first equation *is* the statement that `DJ` is the
covariant derivative of `J`: `∇J = DJ`.  Definitional. -/
theorem _root_.Riemannian.Jacobi.IsJacobiFieldOn.isCovariantDerivSolOn
    {g : RiemannianMetric I M} {α : M}
    {u J DJ : ℝ → E} {a b : ℝ} (h : IsJacobiFieldOn (I := I) g α u J DJ a b) :
    IsCovariantDerivSolOn (I := I) g α u J DJ a b :=
  fun t ht => h.hasDerivWithinAt_fst t ht

/-! ### Chart-change covariance -/

section Transfer

variable [I.Boundaryless]

/-- **Math.** **Chart-change covariance of the covariant derivative.** Along a
curve `γ` lying in the sources of two charts `α`, `β`, a chart-`α` certificate for
the own-foot pair `(V, DV)` yields the chart-`β` certificate.  The inhomogeneous
second-derivative term of the transition map produced by the product rule cancels
against the transformation law of the Christoffel contraction
(`chartChristoffelContraction_change`) — this cancellation is exactly the statement
that `D/dt` is a well-defined geometric operator.

Unlike `IsParallelSolOn.transfer` and `IsJacobiFieldOn.transfer`, **no geodesic
hypothesis** is needed: those two use `IsGeodesicOn` only to produce
differentiability of the chart curve, which we assume directly (`hdiff`).  do
Carmo Ch. 9's variations have non-geodesic transversals, so this generality is
what makes the predicate usable there. -/
theorem IsCovariantDerivSolOn.transfer
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV : ℝ → E} {α β : M} {a b : ℝ}
    (hdiff : ∀ τ ∈ Icc a b,
      DifferentiableAt ℝ (fun σ => extChartAt I α (γ σ)) τ)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrcα : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H α).source)
    (hsrcβ : ∀ τ ∈ Icc a b, γ τ ∈ (chartAt H β).source)
    (h : IsCovariantDerivSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α V) (chartVectorRep (I := I) γ α DV) a b) :
    IsCovariantDerivSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β V) (chartVectorRep (I := I) γ β DV) a b := by
  intro τ hτ
  have hxα := hsrcα τ hτ
  have hxβ := hsrcβ τ hτ
  have hcτ := hγc τ hτ
  have hyT : extChartAt I α (γ τ) ∈ chartTransitionSource (I := I) (M := M) α β :=
    extChartAt_mem_chartTransitionSource (I := I) hxα hxβ
  have hsymm : (extChartAt I α).symm (extChartAt I α (γ τ)) = γ τ :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hxα)
  have hu : HasDerivAt (fun σ => extChartAt I α (γ σ))
      (deriv (fun σ => extChartAt I α (γ σ)) τ) τ := (hdiff τ hτ).hasDerivAt
  have hTd : HasFDerivAt (chartTransition (I := I) α β)
      (tangentCoordChange I α β (γ τ)) (extChartAt I α (γ τ)) := by
    have h0 := hasFDerivAt_chartTransition (I := I) hyT
    rwa [hsymm] at h0
  have hev_mem : ∀ᶠ σ in 𝓝 τ,
      γ σ ∈ (chartAt H α).source ∧ γ σ ∈ (chartAt H β).source := by
    have h₁ : γ ⁻¹' (chartAt H α).source ∈ 𝓝 τ :=
      hcτ.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hxα)
    have h₂ : γ ⁻¹' (chartAt H β).source ∈ 𝓝 τ :=
      hcτ.preimage_mem_nhds ((chartAt H β).open_source.mem_nhds hxβ)
    filter_upwards [h₁, h₂] with σ h1 h2
    exact ⟨h1, h2⟩
  -- The chart-`β` reading of any own-foot field is the transition differential
  -- applied to its chart-`α` reading, near `τ`.
  have hrep : ∀ Z : ℝ → E, chartVectorRep (I := I) γ β Z =ᶠ[𝓝 τ]
      fun σ => fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α Z σ) := by
    intro Z
    filter_upwards [hev_mem] with σ hσ
    have hyσ : extChartAt I α (γ σ)
        ∈ chartTransitionSource (I := I) (M := M) α β :=
      extChartAt_mem_chartTransitionSource (I := I) hσ.1 hσ.2
    have hsymmσ : (extChartAt I α).symm (extChartAt I α (γ σ)) = γ σ :=
      (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hσ.1)
    have hfdσ : fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)) = tangentCoordChange I α β (γ σ) := by
      rw [fderiv_chartTransition (I := I) hyσ, hsymmσ]
    show chartVectorRep (I := I) γ β Z σ
      = fderiv ℝ (chartTransition (I := I) α β)
          (extChartAt I α (γ σ)) (chartVectorRep (I := I) γ α Z σ)
    rw [hfdσ, chartVectorRep_apply, chartVectorRep_apply]
    exact (tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) (γ σ),
        by rw [extChartAt_source]; exact hσ.1⟩,
        by rw [extChartAt_source]; exact hσ.2⟩).symm
  have hC' : HasDerivAt (fun σ => fderiv ℝ (chartTransition (I := I) α β)
        (extChartAt I α (γ σ)))
      (fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
        (extChartAt I α (γ τ))
        (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ :=
    (hasFDerivAt_fderiv_chartTransition (I := I) hyT).comp_hasDerivAt τ hu
  have huβ : HasDerivAt (fun σ => extChartAt I β (γ σ))
      (tangentCoordChange I α β (γ τ)
        (deriv (fun σ => extChartAt I α (γ σ)) τ)) τ := by
    have hcomp := hTd.comp_hasDerivAt τ hu
    have hcong : (fun σ => extChartAt I β (γ σ)) =ᶠ[𝓝 τ]
        fun σ => chartTransition (I := I) α β (extChartAt I α (γ σ)) := by
      filter_upwards [hev_mem] with σ hσ
      exact (chartTransition_extChartAt (I := I) hσ.1).symm
    exact hcomp.congr_of_eventuallyEq hcong
  have hfd : fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
      = tangentCoordChange I α β (γ τ) := hTd.fderiv
  have hVτ : chartVectorRep (I := I) γ β V τ
      = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ) := (hrep V).self_of_nhds
  have hDVτ : chartVectorRep (I := I) γ β DV τ
      = fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α DV τ) := (hrep DV).self_of_nhds
  have hval := (hC'.hasDerivWithinAt.clm_apply (h τ hτ)).congr_of_eventuallyEq
    ((hrep V).filter_mono nhdsWithin_le_nhds) ((hrep V).self_of_nhds)
  have heq : chartVectorRep (I := I) γ β DV τ
        - Geodesic.chartChristoffelContraction (I := I) g β
            (deriv (fun σ => extChartAt I β (γ σ)) τ)
            (chartVectorRep (I := I) γ β V τ) (extChartAt I β (γ τ))
      = fderiv ℝ (fderiv ℝ (chartTransition (I := I) α β))
          (extChartAt I α (γ τ))
          (deriv (fun σ => extChartAt I α (γ σ)) τ)
          (chartVectorRep (I := I) γ α V τ)
        + fderiv ℝ (chartTransition (I := I) α β) (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α DV τ
            - Geodesic.chartChristoffelContraction (I := I) g α
                (deriv (fun σ => extChartAt I α (γ σ)) τ)
                (chartVectorRep (I := I) γ α V τ)
                (extChartAt I α (γ τ))) := by
    rw [hfd, map_sub,
      chartChristoffelContraction_change (I := I) g β α hxβ hxα
        (deriv (fun σ => extChartAt I α (γ σ)) τ)
        (chartVectorRep (I := I) γ α V τ),
      huβ.deriv, hDVτ, hVτ, hfd]
    abel
  rw [heq]
  exact hval

/-- **Math.** **Chart-differentiability of a curve is chart-independent.** If the
reading of `γ` in the chart at `α` is differentiable at `τ`, so is its reading in
any other chart at `β` around `γ τ` — the two readings differ by the transition
map, which is smooth.  (The `IsGeodesicOn` hypothesis of
`IsParallelSolOn.transfer` is only ever used to produce this differentiability.) -/
theorem differentiableAt_extChartAt_of_chart {γ : ℝ → M} {α β : M} {τ : ℝ}
    (hcτ : ContinuousAt γ τ)
    (hxα : γ τ ∈ (chartAt H α).source) (hxβ : γ τ ∈ (chartAt H β).source)
    (hdiff : DifferentiableAt ℝ (fun σ => extChartAt I α (γ σ)) τ) :
    DifferentiableAt ℝ (fun σ => extChartAt I β (γ σ)) τ := by
  have hyT : extChartAt I α (γ τ) ∈ chartTransitionSource (I := I) (M := M) α β :=
    extChartAt_mem_chartTransitionSource (I := I) hxα hxβ
  have hsymm : (extChartAt I α).symm (extChartAt I α (γ τ)) = γ τ :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hxα)
  have hTd : HasFDerivAt (chartTransition (I := I) α β)
      (tangentCoordChange I α β (γ τ)) (extChartAt I α (γ τ)) := by
    have h0 := hasFDerivAt_chartTransition (I := I) hyT
    rwa [hsymm] at h0
  have hev_mem : ∀ᶠ σ in 𝓝 τ, γ σ ∈ (chartAt H α).source := by
    exact hcτ.preimage_mem_nhds ((chartAt H α).open_source.mem_nhds hxα)
  have hcomp := hTd.comp_hasDerivAt τ hdiff.hasDerivAt
  have hcong : (fun σ => extChartAt I β (γ σ)) =ᶠ[𝓝 τ]
      fun σ => chartTransition (I := I) α β (extChartAt I α (γ σ)) := by
    filter_upwards [hev_mem] with σ hσ
    exact (chartTransition_extChartAt (I := I) hσ).symm
  exact (hcomp.congr_of_eventuallyEq hcong).differentiableAt

end Transfer

/-! ### The manifold-level predicate -/

/-- **Math.** do Carmo Ch. 2, Prop. 2.2, manifold form.  **`DV` is the covariant
derivative of `V` along `γ` on `[a, b]`.**  Both `V` and `DV` are own-foot fields
`ℝ → E` (each `V τ` read as an element of `T_{γ τ} M`).  The condition is
chart-local: near every time `t₀ ∈ [a, b]` there are a chart basepoint `α` and a
subinterval `[a', b'] ∋ t₀` whose `γ`-image lies in the chart at `α`, on which the
chart readings satisfy the coordinate equation `∇V = DV` (`IsCovariantDerivSolOn`).

Because the notion is chart-local it is meaningful for a curve that leaves every
single chart, and by `IsCovariantDerivSolOn.transfer` it does not depend on which
charts are chosen.  `IsParallelFieldAlongOn` is the case `DV = 0` and
`IsJacobiFieldAlongOn` is the case where `DV` additionally solves the Jacobi
equation. -/
def IsCovariantDerivFieldAlongOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (V DV : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t₀ ∈ Icc a b, ∃ (α : M) (a' b' : ℝ), a' < b' ∧ t₀ ∈ Icc a' b' ∧
    Icc a' b' ⊆ Icc a b ∧ Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
    (∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α).source) ∧
    IsCovariantDerivSolOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α V) (chartVectorRep (I := I) γ α DV) a' b'

/-- **Math.** A Jacobi field along `γ` carries its covariant derivative: the pair
`(J, DJ)` of `IsJacobiFieldAlongOn` satisfies `∇J = DJ`.  The chart witnesses are
literally the same data. -/
theorem _root_.Riemannian.Jacobi.IsJacobiFieldAlongOn.isCovariantDerivFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ a b) :
    IsCovariantDerivFieldAlongOn (I := I) g γ J DJ a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub', hnbhd', hsrc', hJ'⟩ := h t₀ ht₀
  exact ⟨α, a', b', hab', ht', hsub', hnbhd', hsrc', hJ'.isCovariantDerivSolOn⟩

/-! ### Curves that are differentiable in charts

The manifold results below need the chart readings of `γ` to be differentiable.
By `differentiableAt_extChartAt_of_chart` this does not depend on the chart, so a
witness in a single chart around each time suffices
(`isChartDifferentiableOn_of_forall_mem`). -/

/-- **Math.** The curve `γ` is **differentiable read in charts** on `[a, b]`: its
reading in every chart around it is differentiable.  By
`differentiableAt_extChartAt_of_chart` this holds as soon as it holds in one chart
at each time. -/
def IsChartDifferentiableOn (γ : ℝ → M) (a b : ℝ) : Prop :=
  ∀ τ ∈ Icc a b, ∀ α : M, γ τ ∈ (chartAt H α).source →
    DifferentiableAt ℝ (fun σ => extChartAt I α (γ σ)) τ

/-- **Math.** One chart per time suffices: chart-differentiability transfers to
every other chart (`differentiableAt_extChartAt_of_chart`). -/
theorem isChartDifferentiableOn_of_forall_mem [I.Boundaryless] {γ : ℝ → M} {a b : ℝ}
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (h : ∀ τ ∈ Icc a b, ∃ α : M, γ τ ∈ (chartAt H α).source ∧
      DifferentiableAt ℝ (fun σ => extChartAt I α (γ σ)) τ) :
    IsChartDifferentiableOn (I := I) γ a b := by
  intro τ hτ β hxβ
  obtain ⟨α, hxα, hdα⟩ := h τ hτ
  exact differentiableAt_extChartAt_of_chart (I := I) (hγc τ hτ) hxα hxβ hdα

/-- **Math.** A geodesic is differentiable read in charts. -/
theorem IsGeodesicOn.isChartDifferentiableOn [I.Boundaryless]
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ}
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsChartDifferentiableOn (I := I) γ a b :=
  fun τ hτ _α hxα => hgeo.differentiableAt_extChartAt hτ (hγc τ hτ) hxα

/-! ### Localization into a single chart -/

section Localize

variable [I.Boundaryless]

/-- **Math.** **Localization.** A manifold covariant-derivative pair restricts, on
any subinterval whose `γ`-image lies in the source of one chart `β`, to a chart-`β`
certificate on the whole subinterval: each chart-local witness transfers to `β`
(`IsCovariantDerivSolOn.transfer`) and the certificates glue by locality of
`HasDerivWithinAt`.  This is what makes the chart-local definition usable. -/
theorem IsCovariantDerivFieldAlongOn.isCovariantDerivSolOn_of_mem_source
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV : ℝ → E} {a b : ℝ}
    (h : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {β : M} {c d : ℝ} (hsub : Icc c d ⊆ Icc a b)
    (hsrcβ : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H β).source) :
    IsCovariantDerivSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
      (chartVectorRep (I := I) γ β V) (chartVectorRep (I := I) γ β DV) c d := by
  have key : ∀ t ∈ Icc c d, ∃ a' b' : ℝ, t ∈ Icc a' b' ∧
      Icc a' b' ⊆ Icc c d ∧ Icc a' b' ∈ 𝓝[Icc c d] t ∧
      IsCovariantDerivSolOn (I := I) g β (fun τ => extChartAt I β (γ τ))
        (chartVectorRep (I := I) γ β V) (chartVectorRep (I := I) γ β DV) a' b' := by
    intro t ht
    obtain ⟨α', a₁, b₁, _hab₁, ht₁, hsub₁, hnbhd₁, hsrc₁, h₁⟩ := h t (hsub ht)
    refine ⟨max a₁ c, min b₁ d, ⟨max_le ht₁.1 ht.1, le_min ht₁.2 ht.2⟩, ?_, ?_, ?_⟩
    · exact Icc_subset_Icc (le_max_right _ _) (min_le_right _ _)
    · obtain ⟨U, hUopen, htU, hUsub⟩ := mem_nhdsWithin.1 hnbhd₁
      refine mem_nhdsWithin.2 ⟨U, hUopen, htU, fun σ hσ => ?_⟩
      have hσ₁ : σ ∈ Icc a₁ b₁ := hUsub ⟨hσ.1, hsub hσ.2⟩
      exact ⟨max_le hσ₁.1 hσ.2.1, le_min hσ₁.2 hσ.2.2⟩
    · have hmemab : ∀ τ ∈ Icc (max a₁ c) (min b₁ d), τ ∈ Icc a b := fun τ hτ =>
        hsub ⟨le_trans (le_max_right _ _) hτ.1, le_trans hτ.2 (min_le_right _ _)⟩
      have hsrcα' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H α').source :=
        fun τ hτ => hsrc₁ τ ⟨le_trans (le_max_left _ _) hτ.1,
          le_trans hτ.2 (min_le_left _ _)⟩
      have hdiff' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          DifferentiableAt ℝ (fun σ => extChartAt I α' (γ σ)) τ :=
        fun τ hτ => hdiff τ (hmemab τ hτ) α' (hsrcα' τ hτ)
      have hγc' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d), ContinuousAt γ τ :=
        fun τ hτ => hγc τ (hmemab τ hτ)
      have hsrcβ' : ∀ τ ∈ Icc (max a₁ c) (min b₁ d),
          γ τ ∈ (chartAt H β).source :=
        fun τ hτ => hsrcβ τ ⟨le_trans (le_max_right _ _) hτ.1,
          le_trans hτ.2 (min_le_right _ _)⟩
      exact (h₁.mono (le_max_left _ _) (min_le_left _ _)).transfer
        hdiff' hγc' hsrcα' hsrcβ'
  intro t ht
  obtain ⟨a', b', ht', _hsub', hnbhd', hcert⟩ := key t ht
  exact (hcert t ht').mono_of_mem_nhdsWithin hnbhd'

end Localize

/-! ### Metric compatibility: the Leibniz rule at the manifold level -/

section Leibniz

variable [I.Boundaryless]

/-- **Math.** The pairing `t ↦ ⟨V(t), W(t)⟩` of two covariant-derivative pairs along `γ`
is **continuous on the closed interval** `[a, b]` — endpoints included.

Note the contrast with `hasDerivAt_metricInner` below, which gives a derivative only at
*interior* times: differentiability degrades at the endpoints, continuity does not.  The
reason is in `IsCovariantDerivSolOn`'s own shape: it demands `HasDerivWithinAt V _ (Icc a
b) t` for **every** `t ∈ Icc a b`, over the *closed* window, so `IsCovariantDerivSolOn.continuousOn`
already reaches the endpoints, and the chart pairing is continuous in all three of its
arguments (`continuousOn_chartMetricInner_pairing`).

This is what the fundamental theorem of calculus needs on `[a, b]` when the derivative is
only available on `(a, b)`, and it is why the first variation formula's integration by
parts (`Variation/FirstVariation.lean`) carries no continuity hypothesis. -/
theorem IsCovariantDerivFieldAlongOn.continuousOn_metricInner
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV W DW : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g γ W DW a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    ContinuousOn
      (fun s => g.metricInner (γ s) (V s : TangentSpace I (γ s)) (W s)) (Icc a b) := by
  intro t ht
  -- work in the chart window `IsCovariantDerivFieldAlongOn` supplies around `t`
  obtain ⟨α, a', b', _hab', ht', hsub, hnbhd, hsrc, _⟩ := hV t ht
  have hVloc := hV.isCovariantDerivSolOn_of_mem_source hdiff hγc hsub hsrc (β := α)
  have hWloc := hW.isCovariantDerivSolOn_of_mem_source hdiff hγc hsub hsrc (β := α)
  have hu : ContinuousOn (fun τ => extChartAt I α (γ τ)) (Icc a' b') := fun τ hτ =>
    (hdiff τ (hsub hτ) α (hsrc τ hτ)).continuousAt.continuousWithinAt
  have hmem : ∀ τ ∈ Icc a' b', (fun σ => extChartAt I α (γ σ)) τ ∈ (extChartAt I α).target :=
    fun τ hτ => (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc τ hτ)
  -- on that window the intrinsic pairing *is* the chart Gram pairing of the readings
  have hpair : ContinuousOn
      (fun s => g.metricInner (γ s) (V s : TangentSpace I (γ s)) (W s)) (Icc a' b') :=
    (continuousOn_chartMetricInner_pairing (I := I) g α hu hmem
      hVloc.continuousOn hWloc.continuousOn).congr
      fun σ hσ => metricInner_eq_chartMetricInner_rep (I := I) g (hsrc σ hσ) V W
  exact (hpair t ht').mono_of_mem_nhdsWithin hnbhd

/-- **Math.** do Carmo Ch. 2, Prop. 3.2 (metric compatibility of the Levi-Civita
connection), manifold form along a curve:
$$\frac{d}{dt}\langle V, W\rangle = \Big\langle \frac{DV}{dt}, W\Big\rangle
  + \Big\langle V, \frac{DW}{dt}\Big\rangle.$$

This is the analytic workhorse of do Carmo Ch. 9: every variation formula
(`prop:dc-ch9-2-4`, `prop:dc-ch9-2-8`, `rem:dc-ch9-2-9`) differentiates a pairing
of fields along a curve using exactly this rule, and the index form
`rem:dc-ch9-2-10` is assembled from it by integration by parts.

`IsParallelFieldAlongOn.metricInner_const` is the special case `DV = DW = 0`
(both sides vanish, so the pairing is constant).

Chart-locally the intrinsic pairing is the chart Gram pairing of the two chart
readings (`metricInner_eq_chartMetricInner_rep`), whose derivative is given by the
coordinate product rule `hasDerivAt_chartMetricInner_along`; the certificates
identify the two coordinate covariant derivatives with the readings of `DV`, `DW`. -/
theorem IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV W DW : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hW : IsCovariantDerivFieldAlongOn (I := I) g γ W DW a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (V s : TangentSpace I (γ s)) (W s))
      (g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)
        + g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t)) t := by
  classical
  have hsmem : t ∈ Icc a b := Ioo_subset_Icc_self ht
  obtain ⟨α, a', b', _hab', ht', hsub, hnbhd, hsrc, _⟩ := hV t hsmem
  have hVloc := hV.isCovariantDerivSolOn_of_mem_source hdiff hγc hsub hsrc (β := α)
  have hWloc := hW.isCovariantDerivSolOn_of_mem_source hdiff hγc hsub hsrc (β := α)
  -- the chart window is a full neighbourhood of the interior time `t`
  have hnbhd_full : Icc a' b' ∈ 𝓝 t := by
    rwa [nhdsWithin_eq_nhds.2 (Icc_mem_nhds ht.1 ht.2)] at hnbhd
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu_def
  have hVd : HasDerivAt (chartVectorRep (I := I) γ α V)
      (chartVectorRep (I := I) γ α DV t
        - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
          (chartVectorRep (I := I) γ α V t) (u t)) t :=
    (hVloc t ht').hasDerivAt hnbhd_full
  have hWd : HasDerivAt (chartVectorRep (I := I) γ α W)
      (chartVectorRep (I := I) γ α DW t
        - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
          (chartVectorRep (I := I) γ α W t) (u t)) t :=
    (hWloc t ht').hasDerivAt hnbhd_full
  have hu_diff : DifferentiableAt ℝ u t := hdiff t hsmem α (hsrc t ht')
  have hmemT : u t ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht')
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t) :=
    fun i j => differentiableAt_chartGramOnE (I := I) g α hmemT i j
  have hbase : (extChartAt I α).symm (u t)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_extChartAt_mem_baseSet (I := I) (hsrc t ht')
  -- the certificates say the coordinate covariant derivatives are the readings of `DV`, `DW`
  have hcV : covariantDerivCoord (I := I) g α u (chartVectorRep (I := I) γ α V) t
      = chartVectorRep (I := I) γ α DV t := by
    rw [covariantDerivCoord_def, hVd.deriv]; abel
  have hcW : covariantDerivCoord (I := I) g α u (chartVectorRep (I := I) γ α W) t
      = chartVectorRep (I := I) γ α DW t := by
    rw [covariantDerivCoord_def, hWd.deriv]; abel
  have hmain := hasDerivAt_chartMetricInner_along (I := I) g α u
    (chartVectorRep (I := I) γ α V) (chartVectorRep (I := I) γ α W)
    hu_diff hVd.differentiableAt hWd.differentiableAt hG hbase
  rw [hcV, hcW] at hmain
  -- the intrinsic pairing agrees with the chart pairing near `t`
  have hcong : (fun s => g.metricInner (γ s) (V s : TangentSpace I (γ s)) (W s)) =ᶠ[𝓝 t]
      fun σ => chartMetricInner (I := I) g α (u σ)
        (chartVectorRep (I := I) γ α V σ) (chartVectorRep (I := I) γ α W σ) := by
    filter_upwards [hnbhd_full] with σ hσ
    exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc σ hσ) V W
  have hrhs : chartMetricInner (I := I) g α (u t)
        (chartVectorRep (I := I) γ α DV t) (chartVectorRep (I := I) γ α W t)
      + chartMetricInner (I := I) g α (u t)
        (chartVectorRep (I := I) γ α V t) (chartVectorRep (I := I) γ α DW t)
      = g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (W t)
        + g.metricInner (γ t) (V t : TangentSpace I (γ t)) (DW t) := by
    rw [← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht') DV W,
      ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht') V DW]
  rw [← hrhs]
  exact hmain.congr_of_eventuallyEq hcong

/-- **Math.** The `V = W` case of the Leibniz rule (do Carmo Ch. 2, Prop. 3.2):
`d/dt ⟨V, V⟩ = 2⟨DV/dt, V⟩`, along any curve `γ` and chart-free.  The factor `2` is the
symmetry of the metric, which collapses the two Leibniz terms into one. -/
theorem IsCovariantDerivFieldAlongOn.hasDerivAt_metricInner_self
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV : ℝ → E} {a b : ℝ}
    (hV : IsCovariantDerivFieldAlongOn (I := I) g γ V DV a b)
    (hdiff : IsChartDifferentiableOn (I := I) γ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun s => g.metricInner (γ s) (V s : TangentSpace I (γ s)) (V s))
      (2 * g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (V t)) t := by
  have h := hV.hasDerivAt_metricInner hV hdiff hγc ht
  rw [g.metricInner_comm (γ t) (V t) (DV t)] at h
  convert h using 1
  ring

end Leibniz

end Riemannian.Variation

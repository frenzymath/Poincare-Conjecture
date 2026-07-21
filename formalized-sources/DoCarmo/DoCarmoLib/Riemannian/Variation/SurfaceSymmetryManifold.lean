import DoCarmoLib.Riemannian.Variation.CovariantField
import DoCarmoLib.Riemannian.Variation.SurfaceSymmetry
import DoCarmoLib.Riemannian.Geodesic.HopfRinow.CurveReadback

/-!
# The symmetry lemma at the manifold level: `D/∂s ∂f/∂t = D/∂t ∂f/∂s`

do Carmo, *Riemannian Geometry*, Ch. 3, Lemma 3.4, read on a parametrized surface
`f : ℝ × ℝ → M` **valued in the manifold** — the form Ch. 9 §2 uses at the step
"using the symmetry of the Riemannian connection", in the proofs of the first
variation formula (`prop:dc-ch9-2-4`) and the second (`prop:dc-ch9-2-8`).

`Variation/SurfaceSymmetry.lean` proves the same identity for a surface `f : ℝ × ℝ → E`
read in one fixed chart, with `D/∂s`, `D/∂t` the coordinate operators
`Jacobi.surfaceCovariantDerivS` / `surfaceCovariantDerivT` and `α : M` a chart selector
rather than a point of the surface.  This file carries that identity across to objects
that do not mention a chart in their statement: the surface is `f : ℝ × ℝ → M`, the two
velocity fields are `mfderiv`-based, and the two covariant derivatives are presented as
`IsCovariantDerivFieldAlongOn` pairs — the chart-free predicate of
`Variation/CovariantField.lean` — along the two slice curves.

## The route, and where each piece comes from

The identity is transported, not reproved.  Four steps:

1. **Localize** both slice pairs into one common chart at an `α` with
   `f (s₀, t₀) ∈ (chartAt H α).source`, via
   `IsCovariantDerivFieldAlongOn.isCovariantDerivSolOn_of_mem_source`.
2. **Turn the predicate into the operator**: at interior times
   `IsCovariantDerivSolOn.covariantDerivCoord_eq` says the chart reading of the pair's
   second component *is* `covariantDerivCoord`.
3. **Recognize the two operators.** With `F = φ_α ∘ f` the chart reading of the surface,
   `Jacobi.surfaceCovariantDerivS`/`surfaceCovariantDerivT` of `F` are by definition
   `covariantDerivCoord` along the two slices, so step 2's outputs are literally them —
   and `surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst` applies.
4. **Cancel the chart**: `tangentCoordChange I x α x` is injective
   (`Jacobi.tangentCoordChange_eq_zero_iff`), so an equation between chart readings at
   the common foot `x = f (s₀, t₀)` is an equation between the intrinsic vectors.

The join in step 3 is what makes the transport a transport: the two sides are the same
`covariantDerivCoord` term, reached from opposite directions.

The bridge relating the intrinsic velocities to the chart velocities `∂F/∂t = DF(0,1)`,
`∂F/∂s = DF(1,0)` is `Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt`, which asks only for
continuity of the slice curve, membership of its foot in the chart source, and
differentiability of its chart reading.  It does not constrain the slice curves further,
which matters here: do Carmo's transversals `σ ↦ f (σ, t₀)` are *not* geodesics.

## Scope — what is hypothesised

Everything is at the single point `(s₀, t₀)`, and the hypotheses are read off the four
steps above rather than packaged:

* a chart selector `α` is **supplied**, together with the two slice windows `[a, b] ∋ s₀`
  and `[c, d] ∋ t₀` on which the corresponding slice of `f` stays in
  `(chartAt H α).source`, is continuous, and has a differentiable chart-`α` reading.
  Both windows are asked to contain their point in the **interior** (`s₀ ∈ Ioo a b`,
  `t₀ ∈ Ioo c d`), because step 2 produces the operator at interior times only.  This is
  a restriction relative to a statement quantified over an arbitrary surface: it demands
  that the two slice curves through `(s₀, t₀)` stay in one chart on their whole window.
  It does **not** demand this of the two-parameter surface, nor of any other slice.
* the regularity of the surface is carried in the `HasFDerivAt`-with-explicit-`DF`/`D2F`
  shape inherited from `surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst`, on the
  chart reading `F = φ_α ∘ f`: `DF` a *function* eventually differentiating `F` near
  `(s₀, t₀)`, and `D2F` a single continuous linear map differentiating `DF` at
  `(s₀, t₀)`.  Continuity of `f` near `(s₀, t₀)` is hypothesised separately
  (`hfc`), since the velocity bridge consumes it on slices through nearby points.
* the two velocity fields are pinned to the intrinsic slice velocities by `hT`, `hS`,
  which are asked to hold *near* `(s₀, t₀)` — a neighbourhood is needed, not just the
  point, because step 2's `covariantDerivCoord` differentiates the field along the slice.

Reference: do Carmo, *Riemannian Geometry*, Ch. 3, Lemma 3.4; used at Ch. 9 §2 in the
proofs of `prop:dc-ch9-2-4` and `prop:dc-ch9-2-8`.
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
  [I.Boundaryless]

/-! ### Two small tools -/

/-- **Math.** `covariantDerivCoord g α u V t` depends on `V` only through its germ at
`t`: it is built from `deriv V t` and `V t`. -/
theorem covariantDerivCoord_congr_of_eventuallyEq (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {V W : ℝ → E} {t : ℝ} (h : V =ᶠ[𝓝 t] W) :
    covariantDerivCoord (I := I) g α u V t = covariantDerivCoord (I := I) g α u W t := by
  rw [covariantDerivCoord_def, covariantDerivCoord_def, h.deriv_eq, h.self_of_nhds]

/-- **Math.** Reading a tangent vector at `x` into the chart at `α` and back into the
chart at `x` is the identity: the two tangent coordinate changes compose to
`tangentCoordChange I α α x = id`. -/
theorem tangentCoordChange_readback {α x : M} (hx : x ∈ (chartAt H α).source) (v : E) :
    tangentCoordChange I x α x (tangentCoordChange I α x x v) = v := by
  have hα : x ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hx
  have hself : x ∈ (extChartAt I x).source := mem_extChartAt_source (I := I) x
  rw [tangentCoordChange_comp (I := I) ⟨⟨hα, hself⟩, hα⟩,
    tangentCoordChange_self (I := I) hα]

/-! ### The symmetry lemma, manifold level -/

/-- **Math.** do Carmo Ch. 3, Lemma 3.4 (**the symmetry of the Riemannian connection**,
on a parametrized surface valued in the manifold `M`):
$$\frac{D}{\partial s}\frac{\partial f}{\partial t}(s_0, t_0)
  = \frac{D}{\partial t}\frac{\partial f}{\partial s}(s_0, t_0).$$

The data.  `T` and `S` are the two velocity fields of `f`, pinned near `(s₀, t₀)` to the
intrinsic slice velocities `∂f/∂t` and `∂f/∂s` by `hT` and `hS`.  `DsT` is presented as
`D/∂s` of `T` by the covariant pair `(T, DsT)` along the **transversal** `σ ↦ f (σ, t₀)`
(`hDsT`), and `DtS` as `D/∂t` of `S` by the pair `(S, DtS)` along the **curve in the
variation** `τ ↦ f (s₀, τ)` (`hDtS`), both in the chart-free language of
`IsCovariantDerivFieldAlongOn`.  `DsT` and `DtS` are constrained only along their own
slice line through `(s₀, t₀)`; `T` and `S` are constrained on a two-dimensional
neighbourhood of `(s₀, t₀)`, since `hT`, `hS` quantify over `p` near `(s₀, t₀)` — the
proof reads them only on the two slice lines, so this is more than it consumes.  The
conclusion is at the single point.

The restrictions.  A chart selector `α : M` is supplied together with the two slice
windows `[a, b] ∋ s₀` and `[c, d] ∋ t₀`, and each slice curve is required to stay in
`(chartAt H α).source` on its **whole** window (`hsrcS`, `hsrcT`), to be continuous
there (`hcontS`, `hcontT`), and to have a differentiable chart-`α` reading there
(`hdiffS`, `hdiffT`).  Both windows contain their point in the interior, as the
covariant derivative is extracted at interior times.  The surface's own regularity is
`HasFDerivAt`-with-explicit-derivatives on the chart reading `F = φ_α ∘ f`, matching
`surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst`: `hF` gives `DF` as an
eventual derivative of `F` near `(s₀, t₀)` and `hF2` gives `D2F` as a derivative of `DF`
at `(s₀, t₀)`; `hfc` gives continuity of `f` near `(s₀, t₀)`.

The proof transports `surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst` — the
chart-level identity — through `IsCovariantDerivFieldAlongOn.isCovariantDerivSolOn_of_mem_source`
and `IsCovariantDerivSolOn.covariantDerivCoord_eq`, using
`Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt` to identify the chart readings of `T`, `S`
with the chart velocities `DF(0,1)`, `DF(1,0)`, and cancels the injective
`tangentCoordChange` at the common foot `f (s₀, t₀)`.  No curvature appears: this is
Ch. 3, Lemma 3.4, not the Ricci identity `lem:dc-ch4-4-1`. -/
theorem covariantDerivS_velT_eq_covariantDerivT_velS
    (g : RiemannianMetric I M) (f : ℝ × ℝ → M) (α : M) (T S DsT DtS : ℝ × ℝ → E)
    (DF : ℝ × ℝ → ((ℝ × ℝ) →L[ℝ] E)) (D2F : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) →L[ℝ] E)
    {s₀ t₀ a b c d : ℝ}
    (hs₀ : s₀ ∈ Ioo a b) (ht₀ : t₀ ∈ Ioo c d)
    (hfc : ∀ᶠ p in 𝓝 (s₀, t₀), ContinuousAt f p)
    (hF : ∀ᶠ p in 𝓝 (s₀, t₀), HasFDerivAt (fun q => extChartAt I α (f q)) (DF p) p)
    (hF2 : HasFDerivAt DF D2F (s₀, t₀))
    (hT : ∀ᶠ p in 𝓝 (s₀, t₀), T p = mfderiv 𝓘(ℝ, ℝ) I (fun τ => f (p.1, τ)) p.2 1)
    (hS : ∀ᶠ p in 𝓝 (s₀, t₀), S p = mfderiv 𝓘(ℝ, ℝ) I (fun σ => f (σ, p.2)) p.1 1)
    (hsrcS : ∀ σ ∈ Icc a b, f (σ, t₀) ∈ (chartAt H α).source)
    (hcontS : ∀ σ ∈ Icc a b, ContinuousAt (fun σ' => f (σ', t₀)) σ)
    (hdiffS : ∀ σ ∈ Icc a b, DifferentiableAt ℝ (fun σ' => extChartAt I α (f (σ', t₀))) σ)
    (hsrcT : ∀ τ ∈ Icc c d, f (s₀, τ) ∈ (chartAt H α).source)
    (hcontT : ∀ τ ∈ Icc c d, ContinuousAt (fun τ' => f (s₀, τ')) τ)
    (hdiffT : ∀ τ ∈ Icc c d, DifferentiableAt ℝ (fun τ' => extChartAt I α (f (s₀, τ'))) τ)
    (hDsT : IsCovariantDerivFieldAlongOn (I := I) g (fun σ => f (σ, t₀))
      (fun σ => T (σ, t₀)) (fun σ => DsT (σ, t₀)) a b)
    (hDtS : IsCovariantDerivFieldAlongOn (I := I) g (fun τ => f (s₀, τ))
      (fun τ => S (s₀, τ)) (fun τ => DtS (s₀, τ)) c d) :
    DsT (s₀, t₀) = DtS (s₀, t₀) := by
  have hxsrc : f (s₀, t₀) ∈ (chartAt H α).source := hsrcS s₀ (Ioo_subset_Icc_self hs₀)
  -- the two slice curves are differentiable read in charts
  have hchdS : IsChartDifferentiableOn (I := I) (fun σ => f (σ, t₀)) a b :=
    isChartDifferentiableOn_of_forall_mem hcontS
      (fun σ hσ => ⟨α, hsrcS σ hσ, hdiffS σ hσ⟩)
  have hchdT : IsChartDifferentiableOn (I := I) (fun τ => f (s₀, τ)) c d :=
    isChartDifferentiableOn_of_forall_mem hcontT
      (fun τ hτ => ⟨α, hsrcT τ hτ, hdiffT τ hτ⟩)
  -- ## step 1+2 : localize into the chart at `α` and read off the operator
  have hAS := (hDsT.isCovariantDerivSolOn_of_mem_source hchdS hcontS
    (β := α) Subset.rfl hsrcS).covariantDerivCoord_eq hs₀
  have hAT := (hDtS.isCovariantDerivSolOn_of_mem_source hchdT hcontT
    (β := α) Subset.rfl hsrcT).covariantDerivCoord_eq ht₀
  -- ## the velocity bridge, on each slice
  have htendS : Filter.Tendsto (fun σ : ℝ => (σ, t₀)) (𝓝 s₀) (𝓝 (s₀, t₀)) :=
    (continuous_id.prodMk continuous_const).tendsto s₀
  have htendT : Filter.Tendsto (fun τ : ℝ => (s₀, τ)) (𝓝 t₀) (𝓝 (s₀, t₀)) :=
    (continuous_const.prodMk continuous_id).tendsto t₀
  have hevS : chartVectorRep (I := I) (fun σ => f (σ, t₀)) α (fun σ => T (σ, t₀))
      =ᶠ[𝓝 s₀] fun σ => DF (σ, t₀) (0, 1) := by
    have hIcc : ∀ᶠ σ in 𝓝 s₀, σ ∈ Icc a b := by
      filter_upwards [Ioo_mem_nhds hs₀.1 hs₀.2] with σ hσ using Ioo_subset_Icc_self hσ
    filter_upwards [htendS.eventually hfc, htendS.eventually hF, htendS.eventually hT,
      hIcc] with σ hcσ hFσ hTσ hσI
    have hcs : ContinuousAt (fun τ => f (σ, τ)) t₀ :=
      hcσ.comp (by fun_prop)
    have hd : HasDerivAt (fun τ => extChartAt I α (f (σ, τ))) (DF (σ, t₀) (0, 1)) t₀ :=
      hasDerivAt_comp_snd hFσ
    have hbridge := Riemannian.Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
      (γ := fun τ => f (σ, τ)) (α := α) hcs (hsrcS σ hσI) hd
    show tangentCoordChange I (f (σ, t₀)) α (f (σ, t₀)) (T (σ, t₀)) = DF (σ, t₀) (0, 1)
    have hTσ' : T (σ, t₀) = tangentCoordChange I α (f (σ, t₀)) (f (σ, t₀))
        (DF (σ, t₀) (0, 1)) := hTσ.trans hbridge
    rw [hTσ', tangentCoordChange_readback (I := I) (hsrcS σ hσI)]
  have hevT : chartVectorRep (I := I) (fun τ => f (s₀, τ)) α (fun τ => S (s₀, τ))
      =ᶠ[𝓝 t₀] fun τ => DF (s₀, τ) (1, 0) := by
    have hIcc : ∀ᶠ τ in 𝓝 t₀, τ ∈ Icc c d := by
      filter_upwards [Ioo_mem_nhds ht₀.1 ht₀.2] with τ hτ using Ioo_subset_Icc_self hτ
    filter_upwards [htendT.eventually hfc, htendT.eventually hF, htendT.eventually hS,
      hIcc] with τ hcτ hFτ hSτ hτI
    have hcs : ContinuousAt (fun σ => f (σ, τ)) s₀ := by
      have hpair : ContinuousAt (fun σ : ℝ => (σ, τ)) s₀ := by fun_prop
      exact ContinuousAt.comp (g := f) (f := fun σ : ℝ => (σ, τ)) (x := s₀) hcτ hpair
    have hd : HasDerivAt (fun σ => extChartAt I α (f (σ, τ))) (DF (s₀, τ) (1, 0)) s₀ :=
      hasDerivAt_comp_fst hFτ
    have hbridge := Riemannian.Geodesic.mfderiv_eq_of_hasDerivAt_extChartAt (I := I)
      (γ := fun σ => f (σ, τ)) (α := α) hcs (hsrcT τ hτI) hd
    show tangentCoordChange I (f (s₀, τ)) α (f (s₀, τ)) (S (s₀, τ)) = DF (s₀, τ) (1, 0)
    have hSτ' : S (s₀, τ) = tangentCoordChange I α (f (s₀, τ)) (f (s₀, τ))
        (DF (s₀, τ) (1, 0)) := hSτ.trans hbridge
    rw [hSτ', tangentCoordChange_readback (I := I) (hsrcT τ hτI)]
  -- ## step 3 : the localized operators are the surface operators of the chart reading
  have hCS : covariantDerivCoord (I := I) g α (fun σ => extChartAt I α (f (σ, t₀)))
      (chartVectorRep (I := I) (fun σ => f (σ, t₀)) α (fun σ => T (σ, t₀))) s₀
      = surfaceCovariantDerivS (I := I) g α (fun p => extChartAt I α (f p))
        (fun p => DF p (0, 1)) (s₀, t₀) :=
    covariantDerivCoord_congr_of_eventuallyEq (I := I) g α _ hevS
  have hCT : covariantDerivCoord (I := I) g α (fun τ => extChartAt I α (f (s₀, τ)))
      (chartVectorRep (I := I) (fun τ => f (s₀, τ)) α (fun τ => S (s₀, τ))) t₀
      = surfaceCovariantDerivT (I := I) g α (fun p => extChartAt I α (f p))
        (fun p => DF p (1, 0)) (s₀, t₀) :=
    covariantDerivCoord_congr_of_eventuallyEq (I := I) g α _ hevT
  -- ## step 4 : the chart-level symmetry lemma, then cancel the chart
  have hsymm := surfaceCovariantDerivS_snd_eq_surfaceCovariantDerivT_fst (I := I) g α
    (fun p => extChartAt I α (f p)) DF D2F s₀ t₀ hF hF2
  -- the chain closes on `chartVectorRep`, which is definitionally the chart reading
  have hkey : tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (DsT (s₀, t₀))
      = tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀)) (DtS (s₀, t₀)) :=
    hAS.symm.trans (hCS.trans (hsymm.trans (hCT.symm.trans hAT)))
  have hzero : tangentCoordChange I (f (s₀, t₀)) α (f (s₀, t₀))
      (DsT (s₀, t₀) - DtS (s₀, t₀)) = 0 := by
    rw [map_sub, hkey, sub_self]
  exact sub_eq_zero.1 ((tangentCoordChange_eq_zero_iff (I := I) hxsrc).1 hzero)

end Riemannian.Variation

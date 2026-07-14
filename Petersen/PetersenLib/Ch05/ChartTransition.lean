import PetersenLib.Ch05.MixedPartials
import PetersenLib.Ch05.GeodesicLocal

/-!
# Petersen Ch. 5, §5.1–§5.2 — chart transitions for the geodesic equation

The chart-transition law for Petersen's acceleration: the coordinate
Christoffel correction transforms under a change of chart exactly so that the
geodesic equation is chart-independent.  This is the consequence of the §5.1
mixed-partials machinery (`thm:pet-ch5-mixed-partials-existence`) that unlocks
the chart-global statements of §5.2 (Lemma 5.2.4, uniform short-time
existence, Corollary 5.2.5, Lemma 5.2.6).

Contents:

* `chartTransition g α β` — the transition map
  `τ = φ_β ∘ φ_α⁻¹ : E → E` between the extended charts at `α` and `β`, with
  its natural domain `chartTransitionDomain α β` (an open set when the model
  is boundaryless), smoothness (`contDiffAt_chartTransition`), and derivative
  `fderiv ℝ τ = tangentCoordChange I α β` (`hasFDerivAt_chartTransition`).
* `chartMetricInner_eq_inner` — the chart Gram pairing at a chart point is the
  intrinsic metric of the pulled-back tangent vectors.
* `chartMetricInner_tangentCoordChange` — the **two-chart Gram identity**:
  `⟨Dτ a, Dτ b⟩_β^{τ y} = ⟨a, b⟩_α^y`.
* `mixedPartialCoord_slice` — slice-naturality of the coordinate mixed
  partial for arbitrary two-variable extensions.
* `gramLineDeriv_chartTransition` — the first-partial Koszul data is
  chart-independent.
* `tangentCoordChange_chartChristoffelContraction` — the **Christoffel
  transformation law** `Dτ(Γ_α(v, w)(y)) = D²τ(v, w) + Γ_β(Dτ v, Dτ w)(τ y)`,
  in the form `Dτ(Γ_α(v, w)(y)) = ∂²τ/∂v∂w` (the coordinate mixed partial of
  `τ` itself).  Petersen's §5.1 axioms force this: `τ` is an isometry between
  the two chart pictures of the same metric, so its mixed partial — computed
  by the Koszul formula from first-partial data only — must be the transport
  of the Christoffel correction.
* `chartReading_geodesicODE_transfer` — the geodesic ODE transfers between
  the chart readings of a curve in two overlapping charts.
* `isGeodesicOn_of_isChartGeodesicOn` / `isChartGeodesicOn_of_isGeodesicOn` —
  the moving-foot geodesic equation on an open time set is equivalent to the
  fixed-chart coordinate ODE in any chart containing the feet (the latter
  direction for curves that are continuous, as Petersen's curves are).
* `geodesic_global_uniqueness` — **Petersen Lemma 5.2.4**
  (`lem:pet-ch5-global-uniqueness`): global uniqueness of geodesics, by the
  clopen/connectedness argument over the local uniqueness of Theorem 5.2.2.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## The chart transition map and its calculus -/

/-- **Math.** The **chart transition map** `τ = φ_β ∘ φ_α⁻¹ : E → E` between the
extended charts at `α` and `β` (junk outside the natural domain
`chartTransitionDomain α β`). -/
def chartTransition (I : ModelWithCorners ℝ E H) [ChartedSpace H M] (α β : M) : E → E :=
  fun y => extChartAt I β ((extChartAt I α).symm y)

@[simp] lemma chartTransition_def (α β : M) (y : E) :
    chartTransition (M := M) I α β y = extChartAt I β ((extChartAt I α).symm y) := rfl

/-- **Math.** The natural domain of the chart transition map `φ_β ∘ φ_α⁻¹`: chart-α
images of points lying in both chart sources. -/
def chartTransitionDomain (I : ModelWithCorners ℝ E H) [ChartedSpace H M] (α β : M) :
    Set E :=
  (extChartAt I α).target ∩
    (extChartAt I α).symm ⁻¹' ((extChartAt I α).source ∩ (extChartAt I β).source)

lemma mem_chartTransitionDomain {α β x : M} (hα : x ∈ (extChartAt I α).source)
    (hβ : x ∈ (extChartAt I β).source) :
    extChartAt I α x ∈ chartTransitionDomain (M := M) I α β := by
  refine ⟨(extChartAt I α).map_source hα, ?_⟩
  rw [mem_preimage, (extChartAt I α).left_inv hα]
  exact ⟨hα, hβ⟩

lemma chartTransitionDomain_spec {α β : M} {y : E}
    (hy : y ∈ chartTransitionDomain (M := M) I α β) :
    y ∈ (extChartAt I α).target ∧
      (extChartAt I α).symm y ∈ (extChartAt I α).source ∧
      (extChartAt I α).symm y ∈ (extChartAt I β).source ∧
      extChartAt I α ((extChartAt I α).symm y) = y :=
  ⟨hy.1, hy.2.1, hy.2.2, (extChartAt I α).right_inv hy.1⟩

section Boundaryless

variable [I.Boundaryless]

lemma isOpen_chartTransitionDomain (α β : M) :
    IsOpen (chartTransitionDomain (M := M) I α β) :=
  (continuousOn_extChartAt_symm α).isOpen_inter_preimage (isOpen_extChartAt_target α)
    ((isOpen_extChartAt_source α).inter (isOpen_extChartAt_source β))

/-- **Math.** The chart transition map is `C^∞` on its natural domain. -/
lemma contDiffAt_chartTransition {α β : M} {y : E}
    (hy : y ∈ chartTransitionDomain (M := M) I α β) :
    ContDiffAt ℝ ∞ (chartTransition (M := M) I α β) y := by
  have hy' : y ∈ ((extChartAt I α).symm ≫ extChartAt I β).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hy.1, hy.2.2⟩
  have h := contDiffWithinAt_ext_coord_change (I := I) (n := ∞) β α hy'
  rw [I.range_eq_univ, contDiffWithinAt_univ] at h
  exact h

/-- **Math.** The derivative of the chart transition map at a chart-α point is the
tangent-bundle coordinate change `tangentCoordChange I α β`. -/
lemma hasFDerivAt_chartTransition {α β x : M} (hα : x ∈ (extChartAt I α).source)
    (hβ : x ∈ (extChartAt I β).source) :
    HasFDerivAt (chartTransition (M := M) I α β) (tangentCoordChange I α β x)
      (extChartAt I α x) := by
  have h := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hα, hβ⟩
  rw [I.range_eq_univ, hasFDerivWithinAt_univ] at h
  exact h

lemma fderiv_chartTransition {α β x : M} (hα : x ∈ (extChartAt I α).source)
    (hβ : x ∈ (extChartAt I β).source) :
    fderiv ℝ (chartTransition (M := M) I α β) (extChartAt I α x)
      = tangentCoordChange I α β x :=
  (hasFDerivAt_chartTransition hα hβ).fderiv

end Boundaryless

lemma chartTransition_extChartAt {α β x : M} (hα : x ∈ (extChartAt I α).source) :
    chartTransition (M := M) I α β (extChartAt I α x) = extChartAt I β x := by
  rw [chartTransition_def, (extChartAt I α).left_inv hα]

/-! ## The two-chart Gram identity -/

/-- **Math.** The chart Gram pairing at a chart point is the intrinsic metric of
the pulled-back tangent vectors: for `x` in the chart source at `α`,
`⟨a, b⟩_α^{φ_α x} = g_x(D a, D b)` where `D = tangentCoordChange I α x x` sends
chart-α coordinates to the tangent space at `x` (read in its own chart). -/
theorem chartMetricInner_eq_inner (g : RiemannianMetric I M) {α x : M}
    (hx : x ∈ (extChartAt I α).source) (a b : E) :
    chartMetricInner (I := I) g α (extChartAt I α x) a b
      = g.inner x (tangentCoordChange I α x x a) (tangentCoordChange I α x x b) := by
  classical
  have hx' : x ∈ (chartAt H α).source := by
    rwa [extChartAt_source I] at hx
  -- the Gram entries at the chart point are metric inner products of the
  -- chart-basis vectors
  have hgram : ∀ i j, chartGramOnE (I := I) g α i j (extChartAt I α x)
      = g.inner x (chartBasisVecFiber (I := I) α i x)
          (chartBasisVecFiber (I := I) α j x) := by
    intro i j
    rw [chartGramOnE_def, (extChartAt I α).left_inv hx, chartGramMatrix_apply]
  -- the coordinate change agrees with the (linear) inverse trivialization at `x`
  have hsymmL : ∀ v : E, (trivializationAt E (TangentSpace I) α).symmL ℝ x v
      = tangentCoordChange I α x x v := by
    intro v
    rw [TangentBundle.symmL_trivializationAt_eq_core hx']
    rfl
  -- expand the coordinate-change vector in the chart-basis frame, inside `T_x M`
  have htcc : ∀ v : E, (tangentCoordChange I α x x v : TangentSpace I x)
      = ∑ i, Geodesic.chartCoord (E := E) i v • chartBasisVecFiber (I := I) α i x := by
    intro v
    rw [← hsymmL v]
    conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    congr 1
  rw [htcc a, htcc b, chartMetricInner_def]
  -- bilinear expansion of the metric inner product
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hgram j i]
  ring

/-- **Math.** The **two-chart Gram identity**: the chart Gram pairings of the same
metric in two overlapping charts are intertwined by the coordinate change
`Dτ = tangentCoordChange I α β x` of the transition map,
`⟨Dτ a, Dτ b⟩_β^{φ_β x} = ⟨a, b⟩_α^{φ_α x}`.  Both sides equal the intrinsic
inner product `g_x` of the corresponding tangent vectors at `x`. -/
theorem chartMetricInner_tangentCoordChange (g : RiemannianMetric I M) {α β x : M}
    (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source) (a b : E) :
    chartMetricInner (I := I) g β (extChartAt I β x)
        (tangentCoordChange I α β x a) (tangentCoordChange I α β x b)
      = chartMetricInner (I := I) g α (extChartAt I α x) a b := by
  rw [chartMetricInner_eq_inner g hβ, chartMetricInner_eq_inner g hα]
  have hcomp : ∀ v : E, tangentCoordChange I β x x (tangentCoordChange I α β x v)
      = tangentCoordChange I α x x v := fun v =>
    tangentCoordChange_comp (I := I) ⟨⟨hα, hβ⟩, mem_extChartAt_source (I := I) x⟩ (v := v)
  rw [hcomp a, hcomp b]

/-! ## Slice-naturality of the coordinate mixed partial -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Math.** **Slice-naturality of the coordinate mixed partial**: for any `C²`
two-variable map `c' : ℝ × F → E`, the mixed partial at `(0, x)` in the slice
directions `(0, v)`, `(0, w)` is the mixed partial of the time-zero slice
`z ↦ c'(0, z)` at `x` in the directions `v, w`.  (Generalizes
`mixedPartialCoord_prodExtension_slice` from Petersen's `c + t·ξ` extensions
to arbitrary two-variable maps.) -/
theorem mixedPartialCoord_slice (g : RiemannianMetric I M) (β : M)
    {c' : ℝ × F → E} {x : F} (hc' : ContDiffAt ℝ 2 c' ((0 : ℝ), x)) (v w : F) :
    mixedPartialCoord (I := I) g β c' ((0 : ℝ), x) ((0 : ℝ), v) ((0 : ℝ), w)
      = mixedPartialCoord (I := I) g β (fun z => c' ((0 : ℝ), z)) x v w := by
  have hcdiff : DifferentiableAt ℝ c' ((0 : ℝ), x) := hc'.differentiableAt (by norm_num)
  have hfd : DifferentiableAt ℝ (fderiv ℝ c') ((0 : ℝ), x) :=
    (hc'.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  set ι : F →L[ℝ] ℝ × F := ContinuousLinearMap.inr ℝ ℝ F with hι
  have hι_apply : ∀ z : F, ι z = ((0 : ℝ), z) := fun z => rfl
  -- first partials of the slice are slice-direction first partials
  have hslice_fderiv : ∀ {z : F}, DifferentiableAt ℝ c' ((0 : ℝ), z) → ∀ u : F,
      fderiv ℝ (fun z' => c' ((0 : ℝ), z')) z u = fderiv ℝ c' ((0 : ℝ), z) ((0 : ℝ), u) := by
    intro z hz u
    have hcomp : HasFDerivAt (fun z' => c' ((0 : ℝ), z'))
        ((fderiv ℝ c' ((0 : ℝ), z)).comp ι) z :=
      HasFDerivAt.comp z hz.hasFDerivAt ι.hasFDerivAt
    rw [hcomp.fderiv]
    rfl
  -- the `w`-slice of the slice derivative agrees with the slice of the
  -- `(0, w)`-derivative near `x`
  have hev : (fun z => fderiv ℝ (fun z' => c' ((0 : ℝ), z')) z w)
      =ᶠ[𝓝 x] fun z => fderiv ℝ c' ((0 : ℝ), z) ((0 : ℝ), w) := by
    have hcont : Continuous fun z : F => ((0 : ℝ), z) :=
      continuous_const.prodMk continuous_id
    have hnear : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ c' ((0 : ℝ), z) := by
      have h1 : ∀ᶠ q in 𝓝 ((0 : ℝ), x), ContDiffAt ℝ 2 c' q := hc'.eventually (by simp)
      exact (hcont.tendsto x).eventually
        (h1.mono fun q hq => hq.differentiableAt (by norm_num))
    filter_upwards [hnear] with z hz
    exact hslice_fderiv hz w
  -- second-derivative slice
  have hgw : DifferentiableAt ℝ (fun q : ℝ × F => fderiv ℝ c' q ((0 : ℝ), w))
      ((0 : ℝ), x) := hfd.clm_apply (differentiableAt_const _)
  have hkey : fderiv ℝ (fun z => fderiv ℝ (fun z' => c' ((0 : ℝ), z')) z w) x v
      = fderiv ℝ (fun q : ℝ × F => fderiv ℝ c' q ((0 : ℝ), w)) ((0 : ℝ), x) ((0 : ℝ), v) := by
    rw [hev.fderiv_eq]
    have hcomp : HasFDerivAt (fun z => fderiv ℝ c' ((0 : ℝ), z) ((0 : ℝ), w))
        ((fderiv ℝ (fun q : ℝ × F => fderiv ℝ c' q ((0 : ℝ), w)) ((0 : ℝ), x)).comp ι) x :=
      HasFDerivAt.comp x hgw.hasFDerivAt ι.hasFDerivAt
    rw [hcomp.fderiv]
    rfl
  rw [mixedPartialCoord_def, mixedPartialCoord_def, hkey,
    hslice_fderiv hcdiff v, hslice_fderiv hcdiff w]

/-! ## Chart-independence of the Koszul first-partial data -/

section Boundaryless

variable [I.Boundaryless]

/-- **Math.** The Koszul first-partial data is **chart-independent**: composing a
map into the chart-α target with the chart transition `τ = φ_β ∘ φ_α⁻¹` leaves
every `gramLineDeriv` unchanged, because pointwise the chart metric pairings of
first partials agree by the two-chart Gram identity and the chain rule. -/
theorem gramLineDeriv_chartTransition (g : RiemannianMetric I M) {α β x : M}
    (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source)
    {c : F → E} {q : F} (hc : ContDiffAt ℝ 2 c q) (hcq : c q = extChartAt I α x)
    (z d e : F) :
    gramLineDeriv (I := I) g β (fun r => chartTransition (M := M) I α β (c r)) q z d e
      = gramLineDeriv (I := I) g α c q z d e := by
  rw [gramLineDeriv_def, gramLineDeriv_def]
  refine Filter.EventuallyEq.deriv_eq ?_
  -- the two integrands agree for parameters near 0
  have hline : Continuous fun s : ℝ => q + s • z :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hUq : c q ∈ chartTransitionDomain (M := M) I α β := by
    rw [hcq]; exact mem_chartTransitionDomain hα hβ
  have hnear_dom : ∀ᶠ r in 𝓝 q, c r ∈ chartTransitionDomain (M := M) I α β :=
    (hc.continuousAt).eventually_mem
      ((isOpen_chartTransitionDomain α β).mem_nhds hUq)
  have hnear_diff : ∀ᶠ r in 𝓝 q, DifferentiableAt ℝ c r := by
    have h1 : ∀ᶠ r in 𝓝 q, ContDiffAt ℝ 2 c r := hc.eventually (by simp)
    exact h1.mono fun r hr => hr.differentiableAt (by norm_num)
  have hs0 : Filter.Tendsto (fun s : ℝ => q + s • z) (𝓝 0) (𝓝 q) :=
    hline.tendsto' 0 q (by simp)
  filter_upwards [hs0.eventually hnear_dom, hs0.eventually hnear_diff] with s hdom hdiff
  set r : F := q + s • z
  -- notation for the point and its chart data
  obtain ⟨htarget, hsrcα, hsrcβ, hright⟩ := chartTransitionDomain_spec hdom
  set xr : M := (extChartAt I α).symm (c r) with hxr
  -- the transition map is differentiable at `c r` with derivative the
  -- tangent coordinate change at `xr`
  have hτ : HasFDerivAt (chartTransition (M := M) I α β)
      (tangentCoordChange I α β xr) (c r) := by
    have h := hasFDerivAt_chartTransition (M := M) (α := α) (β := β) hsrcα hsrcβ
    rwa [hright] at h
  -- chain rule for the composed first partials
  have hchain : ∀ u : F, fderiv ℝ (fun r' => chartTransition (M := M) I α β (c r')) r u
      = tangentCoordChange I α β xr (fderiv ℝ c r u) := by
    intro u
    have hcomp : HasFDerivAt (fun r' => chartTransition (M := M) I α β (c r'))
        ((tangentCoordChange I α β xr).comp (fderiv ℝ c r)) r :=
      hτ.comp r hdiff.hasFDerivAt
    rw [hcomp.fderiv]
    rfl
  -- foot of the composed curve
  have hfoot : chartTransition (M := M) I α β (c r) = extChartAt I β xr := rfl
  rw [hfoot, hchain d, hchain e]
  -- conclude by the two-chart Gram identity at `xr`
  have hGram := chartMetricInner_tangentCoordChange (I := I) g hsrcα hsrcβ
    (fderiv ℝ c r d) (fderiv ℝ c r e)
  rw [hGram]
  rw [hright]

/-! ## The Christoffel transformation law -/

/-- **Math.** **The Christoffel transformation law** (the chart-transition
consequence of Petersen §5.1, Lemma 5.1.1/Theorem 5.1.2).  For a point `x` in
two chart sources and `y = φ_α x` its chart-α image, the coordinate change
`Dτ = tangentCoordChange I α β x` of the transition map `τ = φ_β ∘ φ_α⁻¹`
transports the chart-α Christoffel correction onto the coordinate mixed
partial of `τ` itself:
$$D\tau\big(\Gamma_\alpha(v, w)(y)\big) = \frac{\partial^2 \tau}{\partial v \, \partial w}(y)
  = D^2\tau(y)(v, w) + \Gamma_\beta(D\tau v, D\tau w)(\tau y).$$
Petersen's proof: `τ` reads the *same* metric in two coordinate systems, so
its mixed partial — determined by the Koszul formula from first-partial data
that is chart-independent (`gramLineDeriv_chartTransition`) — must be the
transport of `Γ_α`.  Formally we run the §5.1 extension trick `c̃ = id + t·ξ`
through both charts and use nondegeneracy of the chart metric. -/
theorem tangentCoordChange_chartChristoffelContraction (g : RiemannianMetric I M)
    {α β x : M} (hα : x ∈ (extChartAt I α).source) (hβ : x ∈ (extChartAt I β).source)
    (v w : E) :
    tangentCoordChange I α β x
        (Geodesic.chartChristoffelContraction (I := I) g α v w (extChartAt I α x))
      = mixedPartialCoord (I := I) g β (chartTransition (M := M) I α β)
          (extChartAt I α x) v w := by
  classical
  set y : E := extChartAt I α x with hy
  set τ : E → E := chartTransition (M := M) I α β with hτdef
  have hyU : y ∈ chartTransitionDomain (M := M) I α β := mem_chartTransitionDomain hα hβ
  have hymemα : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hα
  have hτy : τ y = extChartAt I β x := chartTransition_extChartAt hα
  have hymemβ : τ y ∈ (extChartAt I β).target := by
    rw [hτy]; exact (extChartAt I β).map_source hβ
  -- the pairing identity against arbitrary test coordinates
  have key : ∀ ξ : E,
      chartMetricInner (I := I) g β (τ y)
          (tangentCoordChange I α β x
            (Geodesic.chartChristoffelContraction (I := I) g α v w y))
          (tangentCoordChange I α β x ξ)
        = chartMetricInner (I := I) g β (τ y)
            (mixedPartialCoord (I := I) g β τ y v w)
            (tangentCoordChange I α β x ξ) := by
    intro ξ
    -- Petersen's extension of the identity map by `ξ` in the time direction
    set ct : ℝ × E → E := fun p => p.2 + p.1 • ξ with hct
    have hct2 : ContDiffAt ℝ 2 ct ((0 : ℝ), y) := by
      have := contDiffAt_prodExtension (c := fun z : E => z) (x := y)
        contDiff_id.contDiffAt ξ
      simpa using this
    have hct0 : ct ((0 : ℝ), y) = y := by simp [hct]
    have hctd : ∀ p : ℝ × E, DifferentiableAt ℝ ct p := by
      intro p
      have h1 : DifferentiableAt ℝ (fun p : ℝ × E => p.2) p := differentiable_snd.differentiableAt
      have h2 : DifferentiableAt ℝ (fun p : ℝ × E => p.1 • ξ) p :=
        (differentiable_fst.smul_const ξ).differentiableAt
      exact h1.add h2
    -- first partials of the extension
    have hct_fderiv : ∀ (p : ℝ × E) (s : ℝ) (u : E),
        fderiv ℝ ct p (s, u) = u + s • ξ := by
      intro p s u
      have := fderiv_prodExtension_apply (c := fun z : E => z) (y := p.2)
        differentiableAt_id ξ p.1 s u
      simpa [hct] using this
    have hmemα' : ct ((0 : ℝ), y) ∈ (extChartAt I α).target := by rw [hct0]; exact hymemα
    -- the composed extension through the transition map
    have hτ2 : ContDiffAt ℝ 2 τ y :=
      (contDiffAt_chartTransition hyU).of_le (by norm_cast)
    have hτct2 : ContDiffAt ℝ 2 (fun p => τ (ct p)) ((0 : ℝ), y) := by
      have := (hct0 ▸ hτ2).comp ((0 : ℝ), y) hct2
      exact this
    have hmemβ' : (fun p => τ (ct p)) ((0 : ℝ), y) ∈ (extChartAt I β).target := by
      show τ (ct ((0 : ℝ), y)) ∈ (extChartAt I β).target
      rw [hct0]; exact hymemβ
    -- Koszul formula in both charts, in the directions `(0,v), (0,w), (1,0)`
    have hKα := mixedPartialCoord_koszul (I := I) g α hct2 hmemα'
      ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : E))
    have hKβ := mixedPartialCoord_koszul (I := I) g β hτct2 hmemβ'
      ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : E))
    -- the right-hand sides agree: the Koszul data is chart-independent
    have hRHS : ∀ z d e : ℝ × E,
        gramLineDeriv (I := I) g β (fun p => τ (ct p)) ((0 : ℝ), y) z d e
          = gramLineDeriv (I := I) g α ct ((0 : ℝ), y) z d e := fun z d e =>
      gramLineDeriv_chartTransition (I := I) g hα hβ hct2 (hct0.trans hy) z d e
    rw [hRHS _ _ _, hRHS _ _ _, hRHS _ _ _] at hKβ
    -- identify the α-side: the mixed partial of the affine extension is `Γ_α`
    have hct_mp : mixedPartialCoord (I := I) g α ct ((0 : ℝ), y)
        ((0 : ℝ), v) ((0 : ℝ), w)
        = Geodesic.chartChristoffelContraction (I := I) g α v w y := by
      rw [mixedPartialCoord_def]
      have hconst : (fun p : ℝ × E => fderiv ℝ ct p ((0 : ℝ), w)) = fun _ => w := by
        funext p; rw [hct_fderiv p 0 w]; simp
      rw [hconst]
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.zero_apply,
        hct_fderiv _ 0 v, hct_fderiv _ 0 w, hct0]
      simp
    have hct_z : fderiv ℝ ct ((0 : ℝ), y) ((1 : ℝ), (0 : E)) = ξ := by
      rw [hct_fderiv _ 1 0]; simp
    rw [hct_mp, hct_z, hct0] at hKα
    -- identify the β-side: slice-naturality and the chain rule
    have hτct_slice : mixedPartialCoord (I := I) g β (fun p => τ (ct p)) ((0 : ℝ), y)
        ((0 : ℝ), v) ((0 : ℝ), w) = mixedPartialCoord (I := I) g β τ y v w := by
      rw [mixedPartialCoord_slice (I := I) g β hτct2 v w]
      congr 1
      funext z
      simp [hct]
    have hτ_fderiv : HasFDerivAt τ (tangentCoordChange I α β x) y :=
      hasFDerivAt_chartTransition hα hβ
    have hτct_z : fderiv ℝ (fun p => τ (ct p)) ((0 : ℝ), y) ((1 : ℝ), (0 : E))
        = tangentCoordChange I α β x ξ := by
      have hcomp : HasFDerivAt (fun p => τ (ct p))
          ((tangentCoordChange I α β x).comp (fderiv ℝ ct ((0 : ℝ), y))) ((0 : ℝ), y) :=
        (hct0 ▸ hτ_fderiv).comp ((0 : ℝ), y) (hctd _).hasFDerivAt
      rw [hcomp.fderiv]
      show tangentCoordChange I α β x (fderiv ℝ ct ((0 : ℝ), y) ((1 : ℝ), (0 : E))) = _
      rw [hct_z]
    rw [hτct_slice, hτct_z, hct0] at hKβ
    -- transport the α-side pairing through the two-chart Gram identity
    have hGram := chartMetricInner_tangentCoordChange (I := I) g hα hβ
      (Geodesic.chartChristoffelContraction (I := I) g α v w y) ξ
    have h2 : (2 : ℝ) * chartMetricInner (I := I) g β (τ y)
        (tangentCoordChange I α β x
          (Geodesic.chartChristoffelContraction (I := I) g α v w y))
        (tangentCoordChange I α β x ξ)
        = 2 * chartMetricInner (I := I) g β (τ y)
            (mixedPartialCoord (I := I) g β τ y v w)
            (tangentCoordChange I α β x ξ) := by
      rw [hτy] at hKβ ⊢
      rw [hGram, ← hy, hKα, hKβ]
    linarith [h2]
  -- surjectivity of the coordinate change plus nondegeneracy finish
  have hsurj : ∀ η : E, ∃ ξ : E, tangentCoordChange I α β x ξ = η := by
    intro η
    refine ⟨tangentCoordChange I β α x η, ?_⟩
    have h1 := tangentCoordChange_comp (I := I)
      ⟨⟨hβ, hα⟩, hβ⟩ (v := η)
    have h2 := tangentCoordChange_self (I := I) (x := β) (z := x) (v := η) hβ
    rw [h1, h2]
  have hsub : tangentCoordChange I α β x
      (Geodesic.chartChristoffelContraction (I := I) g α v w y)
      - mixedPartialCoord (I := I) g β τ y v w = 0 := by
    refine chartMetricInner_nondegenerate (I := I) g β hymemβ fun η => ?_
    obtain ⟨ξ, rfl⟩ := hsurj η
    rw [chartMetricInner_sub_left, key ξ, sub_self]
  exact sub_eq_zero.mp hsub

/-! ## Transfer of the geodesic ODE between chart readings -/

/-- **Math.** **The geodesic ODE transfers between charts.**  Let `γ` be a curve
whose feet lie, for times near `t`, in the sources of the charts at `α` and at
`β`.  If the chart-α reading `u = φ_α ∘ γ` is differentiable near `t`, twice
differentiable at `t`, and satisfies the geodesic equation
`ü(t) + Γ_α(u̇(t), u̇(t))(u(t)) = 0`, then the chart-β reading
`w = φ_β ∘ γ` has the same regularity at `t` and satisfies the chart-β
geodesic equation; moreover the velocities are related by the coordinate
change, `ẇ(t) = Dτ_{αβ}(γ t)(u̇(t))`.

This is the computation `w = τ ∘ u`, `ẇ = Dτ(u)·u̇`,
`ẅ = D²τ(u̇, u̇) + Dτ(ü)`, combined with the Christoffel transformation law
(`tangentCoordChange_chartChristoffelContraction`). -/
theorem chartReading_geodesicODE_transfer (g : RiemannianMetric I M)
    {γ : ℝ → M} {t : ℝ} {α β : M}
    (hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source ∩ (extChartAt I β).source)
    (hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I α (γ s'))
      (deriv (fun s' => extChartAt I α (γ s')) s) s)
    {a : E} (hu2 : HasDerivAt (deriv (fun s' => extChartAt I α (γ s'))) a t)
    (heq : a + Geodesic.chartChristoffelContraction (I := I) g α
      (deriv (fun s' => extChartAt I α (γ s')) t)
      (deriv (fun s' => extChartAt I α (γ s')) t) (extChartAt I α (γ t)) = 0) :
    (∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I β (γ s'))
      (deriv (fun s' => extChartAt I β (γ s')) s) s) ∧
    deriv (fun s' => extChartAt I β (γ s')) t
      = tangentCoordChange I α β (γ t) (deriv (fun s' => extChartAt I α (γ s')) t) ∧
    HasDerivAt (deriv (fun s' => extChartAt I β (γ s')))
      (- Geodesic.chartChristoffelContraction (I := I) g β
        (deriv (fun s' => extChartAt I β (γ s')) t)
        (deriv (fun s' => extChartAt I β (γ s')) t) (extChartAt I β (γ t))) t := by
  classical
  set u : ℝ → E := fun s' => extChartAt I α (γ s') with hu_def
  set B : ℝ → E := fun s' => extChartAt I β (γ s') with hB_def
  set τ : E → E := chartTransition (M := M) I α β with hτ_def
  have hmem_t : γ t ∈ (extChartAt I α).source ∩ (extChartAt I β).source :=
    hev.self_of_nhds
  -- near `t`, the β-reading is the transition map applied to the α-reading
  have hEq : ∀ᶠ s in 𝓝 t, B s = τ (u s) := by
    filter_upwards [hev] with s hs
    exact (chartTransition_extChartAt (β := β) hs.1).symm
  -- the β-reading is differentiable near `t`, with the transported velocity
  have hw' : ∀ᶠ s in 𝓝 t, HasDerivAt B (tangentCoordChange I α β (γ s) (deriv u s)) s := by
    filter_upwards [eventually_eventually_nhds.mpr hev, hu1] with s hsev hs1
    have hτs : HasFDerivAt τ (tangentCoordChange I α β (γ s)) (u s) :=
      hasFDerivAt_chartTransition hsev.self_of_nhds.1 hsev.self_of_nhds.2
    have hτu : HasDerivAt (fun s' => τ (u s')) (tangentCoordChange I α β (γ s)
        (deriv u s)) s := hτs.comp_hasDerivAt s hs1
    refine hτu.congr_of_eventuallyEq ?_
    filter_upwards [hsev] with r hr
    exact (chartTransition_extChartAt (β := β) hr.1).symm
  have hderivB : ∀ᶠ s in 𝓝 t, deriv B s = tangentCoordChange I α β (γ s) (deriv u s) :=
    hw'.mono fun s hs => hs.deriv
  have hvel : deriv B t = tangentCoordChange I α β (γ t) (deriv u t) :=
    hderivB.self_of_nhds
  refine ⟨?_, hvel, ?_⟩
  · filter_upwards [hw', hderivB] with s h1 h2
    rw [h2]
    exact h1
  -- second derivative: differentiate `s ↦ Dτ(u s)(u̇ s)` at `t`
  have hyU : u t ∈ chartTransitionDomain (M := M) I α β :=
    mem_chartTransitionDomain hmem_t.1 hmem_t.2
  have hτ_smooth : ContDiffAt ℝ ∞ τ (u t) := contDiffAt_chartTransition hyU
  have hτ_fd : DifferentiableAt ℝ (fderiv ℝ τ) (u t) :=
    (hτ_smooth.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have hφB : deriv B =ᶠ[𝓝 t] fun s => (fderiv ℝ τ (u s)) (deriv u s) := by
    filter_upwards [hderivB, hev] with s h1 h2
    rw [h1, fderiv_chartTransition h2.1 h2.2]
  have hc : HasDerivAt (fun s => fderiv ℝ τ (u s))
      (fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t)) t :=
    hτ_fd.hasFDerivAt.comp_hasDerivAt t hu1.self_of_nhds
  have hΦ : HasDerivAt (fun s => (fderiv ℝ τ (u s)) (deriv u s))
      (fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t) + (fderiv ℝ τ (u t)) a) t :=
    hc.clm_apply hu2
  have hB2 : HasDerivAt (deriv B)
      (fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t) + (fderiv ℝ τ (u t)) a) t :=
    hΦ.congr_of_eventuallyEq hφB
  -- identify the value with the transported geodesic equation
  have ha_eq : a = - Geodesic.chartChristoffelContraction (I := I) g α
      (deriv u t) (deriv u t) (u t) := by
    have := heq
    linear_combination (norm := module) this
  have hmp : mixedPartialCoord (I := I) g β τ (u t) (deriv u t) (deriv u t)
      = fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t)
        + Geodesic.chartChristoffelContraction (I := I) g β
            (tangentCoordChange I α β (γ t) (deriv u t))
            (tangentCoordChange I α β (γ t) (deriv u t)) (τ (u t)) := by
    rw [mixedPartialCoord_def, fderiv_fderiv_apply hτ_fd,
      fderiv_chartTransition hmem_t.1 hmem_t.2]
  have hΓ := tangentCoordChange_chartChristoffelContraction (I := I) g
    hmem_t.1 hmem_t.2 (deriv u t) (deriv u t)
  have hτut : τ (u t) = extChartAt I β (γ t) := chartTransition_extChartAt hmem_t.1
  -- assemble: `ẅ(t) = D²τ(u̇,u̇) − Dτ(Γ_α) = −Γ_β(ẇ, ẇ)(w t)`
  have hval : fderiv ℝ (fderiv ℝ τ) (u t) (deriv u t) (deriv u t) + (fderiv ℝ τ (u t)) a
      = - Geodesic.chartChristoffelContraction (I := I) g β
          (deriv B t) (deriv B t) (extChartAt I β (γ t)) := by
    rw [ha_eq, fderiv_chartTransition hmem_t.1 hmem_t.2, map_neg, hΓ, hmp, hvel, hτut]
    linear_combination (norm := module)
  rw [← hval]
  exact hB2

/-! ## The moving-foot equation vs the fixed-chart coordinate ODE -/

/-- **Math.** A chart geodesic is continuous on its time set: the curve is the
chart inverse of its (differentiable, hence continuous) chart reading. -/
theorem IsChartGeodesicOn.continuousOn {g : RiemannianMetric I M} {β : M}
    {γ : ℝ → M} {J : Set ℝ} (h : IsChartGeodesicOn (I := I) g β γ J) :
    ContinuousOn γ J := by
  obtain ⟨hmem, hd1, -⟩ := h
  intro t ht
  have hsrc : γ t ∈ (extChartAt I β).source := by
    rw [extChartAt_source I]; exact hmem t ht
  have hread : ContinuousAt (fun s => (extChartAt I β).symm (extChartAt I β (γ s))) t := by
    refine ContinuousAt.comp ?_ (hd1 t ht).continuousAt
    refine (continuousOn_extChartAt_symm β).continuousAt ?_
    exact (isOpen_extChartAt_target β).mem_nhds ((extChartAt I β).map_source hsrc)
  refine hread.continuousWithinAt.congr (fun s hs => ?_) ?_
  · exact ((extChartAt I β).left_inv (by rw [extChartAt_source I]; exact hmem s hs)).symm
  · exact ((extChartAt I β).left_inv hsrc).symm

/-- **Math.** A chart geodesic is a geodesic: on an open time set, the fixed-chart
coordinate geodesic ODE in the chart at `β` implies the intrinsic moving-foot
geodesic equation at every time of the set.  (The transfer target at each time
`t` is the canonical chart at the foot `γ t`; the required eventual chart
membership follows from continuity of the chart reading.) -/
theorem isGeodesicOn_of_isChartGeodesicOn (g : RiemannianMetric I M) {β : M}
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (h : IsChartGeodesicOn (I := I) g β γ J) :
    Geodesic.IsGeodesicOn (I := I) g γ J := by
  obtain ⟨hmem, hd1, hd2⟩ := h
  intro t ht
  have hevJ : ∀ᶠ s in 𝓝 t, s ∈ J := hJ.mem_nhds ht
  -- continuity of the curve at `t`, through the chart-β reading
  have hcont : ContinuousAt γ t := by
    have hBc : ContinuousAt (fun s => (extChartAt I β).symm (extChartAt I β (γ s))) t := by
      refine ContinuousAt.comp ?_ (hd1 t ht).continuousAt
      refine (continuousOn_extChartAt_symm β).continuousAt ?_
      exact (isOpen_extChartAt_target β).mem_nhds
        ((extChartAt I β).map_source (by rw [extChartAt_source I]; exact hmem t ht))
    refine hBc.congr ?_
    filter_upwards [hevJ] with s hs
    exact (extChartAt I β).left_inv (by rw [extChartAt_source I]; exact hmem s hs)
  have hβsrc : γ t ∈ (extChartAt I β).source := by
    rw [extChartAt_source I]; exact hmem t ht
  have hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I β).source ∩ (extChartAt I (γ t)).source := by
    refine (hcont.eventually_mem ?_)
    exact Filter.inter_mem
      ((isOpen_extChartAt_source β).mem_nhds hβsrc)
      ((isOpen_extChartAt_source (γ t)).mem_nhds (mem_extChartAt_source (I := I) (γ t)))
  have hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I β (γ s'))
      (deriv (fun s' => extChartAt I β (γ s')) s) s := by
    filter_upwards [hevJ] with s hs
    exact hd1 s hs
  have heq : - Geodesic.chartChristoffelContraction (I := I) g β
      (deriv (fun s' => extChartAt I β (γ s')) t)
      (deriv (fun s' => extChartAt I β (γ s')) t) (extChartAt I β (γ t))
      + Geodesic.chartChristoffelContraction (I := I) g β
        (deriv (fun s' => extChartAt I β (γ s')) t)
        (deriv (fun s' => extChartAt I β (γ s')) t) (extChartAt I β (γ t)) = 0 :=
    neg_add_cancel _
  obtain ⟨hev', hvel, hB2⟩ := chartReading_geodesicODE_transfer (I := I) g
    hev hu1 (hd2 t ht) heq
  exact ⟨deriv (fun s' => extChartAt I (γ t) (γ s')) t,
    - Geodesic.chartChristoffelContraction (I := I) g (γ t)
      (deriv (fun s' => extChartAt I (γ t) (γ s')) t)
      (deriv (fun s' => extChartAt I (γ t) (γ s')) t) (extChartAt I (γ t) (γ t)),
    hev'.self_of_nhds, hev', hB2, neg_add_cancel _⟩

/-- **Math.** A continuous geodesic is a chart geodesic in every chart containing
its feet: on an open time set `J`, if the curve is continuous on `J`, its feet
lie in the chart source at `β`, and the intrinsic moving-foot geodesic
equation holds on `J`, then the chart-β reading solves the coordinate geodesic
ODE on `J`.  (Continuity is automatic for Petersen's geodesics, which are
smooth curves; it is required here because the moving-foot equation constrains
the chart readings only at the foot's own chart.) -/
theorem isChartGeodesicOn_of_isGeodesicOn (g : RiemannianMetric I M) {β : M}
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hmem : ∀ t ∈ J, γ t ∈ (chartAt H β).source) (hcont : ContinuousOn γ J)
    (h : Geodesic.IsGeodesicOn (I := I) g γ J) :
    IsChartGeodesicOn (I := I) g β γ J := by
  -- pointwise transfer from the chart at the foot to the chart at `β`
  have key : ∀ t ∈ J,
      (∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I β (γ s'))
        (deriv (fun s' => extChartAt I β (γ s')) s) s) ∧
      HasDerivAt (deriv (fun s' => extChartAt I β (γ s')))
        (- Geodesic.chartChristoffelContraction (I := I) g β
          (deriv (fun s' => extChartAt I β (γ s')) t)
          (deriv (fun s' => extChartAt I β (γ s')) t) (extChartAt I β (γ t))) t := by
    intro t ht
    obtain ⟨v, a, hv, hev, ha, heq⟩ := h t ht
    have hct : ContinuousAt γ t := hcont.continuousAt (hJ.mem_nhds ht)
    have hβsrc : γ t ∈ (extChartAt I β).source := by
      rw [extChartAt_source I]; exact hmem t ht
    have hevsrc : ∀ᶠ s in 𝓝 t,
        γ s ∈ (extChartAt I (γ t)).source ∩ (extChartAt I β).source :=
      hct.eventually_mem (Filter.inter_mem
        ((isOpen_extChartAt_source (γ t)).mem_nhds (mem_extChartAt_source (I := I) (γ t)))
        ((isOpen_extChartAt_source β).mem_nhds hβsrc))
    have heq' : a + Geodesic.chartChristoffelContraction (I := I) g (γ t)
        (deriv (fun s' => extChartAt I (γ t) (γ s')) t)
        (deriv (fun s' => extChartAt I (γ t) (γ s')) t) (extChartAt I (γ t) (γ t)) = 0 := by
      have hvd : deriv (fun s' => extChartAt I (γ t) (γ s')) t = v := hv.deriv
      rw [hvd]
      exact heq
    obtain ⟨hev', hvel, hB2⟩ := chartReading_geodesicODE_transfer (I := I) g
      hevsrc hev ha heq'
    exact ⟨hev', hB2⟩
  exact ⟨hmem, fun t ht => ((key t ht).1).self_of_nhds, fun t ht => (key t ht).2⟩

/-! ## Petersen Lemma 5.2.4: global uniqueness of geodesics -/

/-- **Math.** Petersen Ch. 5, Lemma 5.2.4 (`lem:pet-ch5-global-uniqueness`):
**global uniqueness of geodesics.**  Two (continuous) geodesics
`γ₁ : J₁ → M`, `γ₂ : J₂ → M` on open order-connected time sets that agree at a
common time `t₀` together with their velocities (read in the chart at the
common point `γ₁ t₀`) agree on all of `J₁ ∩ J₂`.

The proof is Petersen's connectedness argument: the set of times of local
agreement is open by definition, nonempty and closed by local uniqueness
(Thm. 5.2.2) applied in a fixed chart around each accumulation point — the
passage from the moving-foot geodesic equation to the fixed-chart ODE being
the chart-transition law (`isChartGeodesicOn_of_isGeodesicOn`), the
consequence of the §5.1 mixed-partials machinery
(`thm:pet-ch5-mixed-partials-existence`).  The continuity hypotheses are
implicit in Petersen (geodesics are smooth curves); they are needed here
because the moving-foot geodesic equation constrains each chart reading only
at the foot's own chart.  The Hausdorff hypothesis is likewise implicit in
Petersen's definition of a manifold, and genuinely necessary: on the line
with two origins, two geodesics can agree on a half-line and then branch. -/
theorem geodesic_global_uniqueness (g : RiemannianMetric I M) [T2Space M]
    {γ₁ γ₂ : ℝ → M} {J₁ J₂ : Set ℝ} {t₀ : ℝ}
    (hJ₁ : IsOpen J₁) (hJ₁c : J₁.OrdConnected)
    (hJ₂ : IsOpen J₂) (hJ₂c : J₂.OrdConnected)
    (hc₁ : ContinuousOn γ₁ J₁) (hc₂ : ContinuousOn γ₂ J₂)
    (h₁ : Geodesic.IsGeodesicOn (I := I) g γ₁ J₁)
    (h₂ : Geodesic.IsGeodesicOn (I := I) g γ₂ J₂)
    (ht₀ : t₀ ∈ J₁ ∩ J₂) (heq : γ₁ t₀ = γ₂ t₀)
    (hvel : deriv (Geodesic.chartLocalCurve (I := I) γ₁ t₀) t₀ =
      deriv (fun s => extChartAt I (γ₁ t₀) (γ₂ s)) t₀) :
    Set.EqOn γ₁ γ₂ (J₁ ∩ J₂) := by
  classical
  set O : Set ℝ := J₁ ∩ J₂ with hO_def
  have hO : IsOpen O := hJ₁.inter hJ₂
  -- local agreement propagates from any time where positions and velocities
  -- agree, by local uniqueness (Thm. 5.2.2) in the chart at the common point
  have local_agree : ∀ t₁ ∈ O, γ₁ t₁ = γ₂ t₁ →
      deriv (fun s => extChartAt I (γ₁ t₁) (γ₁ s)) t₁
        = deriv (fun s => extChartAt I (γ₁ t₁) (γ₂ s)) t₁ →
      γ₁ =ᶠ[𝓝 t₁] γ₂ := by
    intro t₁ ht₁ hpos hvel₁
    set δ : M := γ₁ t₁ with hδ_def
    have hδ₁ : γ₁ t₁ ∈ (chartAt H δ).source := mem_chart_source H (γ₁ t₁)
    have hδ₂ : γ₂ t₁ ∈ (chartAt H δ).source := hpos ▸ hδ₁
    have hcγ₁ : ContinuousAt γ₁ t₁ := hc₁.continuousAt (hJ₁.mem_nhds ht₁.1)
    have hcγ₂ : ContinuousAt γ₂ t₁ := hc₂.continuousAt (hJ₂.mem_nhds ht₁.2)
    have h_ev : ∀ᶠ s in 𝓝 t₁, s ∈ O ∧ γ₁ s ∈ (chartAt H δ).source ∧
        γ₂ s ∈ (chartAt H δ).source := by
      filter_upwards [hO.mem_nhds ht₁,
        hcγ₁.eventually_mem ((chartAt H δ).open_source.mem_nhds hδ₁),
        hcγ₂.eventually_mem ((chartAt H δ).open_source.mem_nhds hδ₂)] with s hs h1 h2
      exact ⟨hs, h1, h2⟩
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp h_ev
    set J' : Set ℝ := Metric.ball t₁ ε with hJ'_def
    have hJ'o : IsOpen J' := Metric.isOpen_ball
    have hJ'c : J'.OrdConnected := by
      rw [hJ'_def, Real.ball_eq_Ioo]; exact Set.ordConnected_Ioo
    have hJ'O : J' ⊆ O := fun s hs => (hball s hs).1
    have ht₁J' : t₁ ∈ J' := Metric.mem_ball_self hε
    have hcg₁ : IsChartGeodesicOn (I := I) g δ γ₁ J' :=
      isChartGeodesicOn_of_isGeodesicOn g hJ'o (fun s hs => (hball s hs).2.1)
        (hc₁.mono fun s hs => (hJ'O hs).1) (h₁.mono fun s hs => (hJ'O hs).1)
    have hcg₂ : IsChartGeodesicOn (I := I) g δ γ₂ J' :=
      isChartGeodesicOn_of_isGeodesicOn g hJ'o (fun s hs => (hball s hs).2.2)
        (hc₂.mono fun s hs => (hJ'O hs).2) (h₂.mono fun s hs => (hJ'O hs).2)
    have hEqOn : Set.EqOn γ₁ γ₂ (J' ∩ J') :=
      geodesic_local_uniqueness (I := I) g δ hJ'o hJ'c hJ'o hJ'c hcg₁ hcg₂
        ⟨ht₁J', ht₁J'⟩ hpos hvel₁
    rw [Set.inter_self] at hEqOn
    filter_upwards [hJ'o.mem_nhds ht₁J'] with s hs
    exact hEqOn hs
  -- the set of times of local agreement, inside the overlap
  have hOc : IsPreconnected O := (hJ₁c.inter hJ₂c).isPreconnected
  haveI : PreconnectedSpace ↥O := isPreconnected_iff_preconnectedSpace.mp hOc
  set A : Set ↥O := {t : ↥O | γ₁ =ᶠ[𝓝 (t : ℝ)] γ₂} with hA_def
  have hA_nonempty : A.Nonempty :=
    ⟨⟨t₀, ht₀⟩, local_agree t₀ ht₀ heq hvel⟩
  have hA_open : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have h' : ∀ᶠ s in 𝓝 (t : ℝ), γ₁ =ᶠ[𝓝 s] γ₂ := ht.eventually_nhds
    exact ContinuousAt.preimage_mem_nhds continuous_subtype_val.continuousAt h'
  have hA_closed : IsClosed A := by
    refine isClosed_of_closure_subset ?_
    intro t ht
    obtain ⟨u, huA, hulim⟩ := mem_closure_iff_seq_limit.mp ht
    by_cases hne : ∃ n, u n = t
    · obtain ⟨n, rfl⟩ := hne
      exact huA n
    have hseq : Filter.Tendsto (fun n => ((u n : ↥O) : ℝ)) atTop (𝓝 (t : ℝ)) :=
      (continuous_subtype_val.tendsto t).comp hulim
    -- position agreement at the limit time, by continuity
    have hposn : ∀ n, γ₁ ((u n : ↥O) : ℝ) = γ₂ ((u n : ↥O) : ℝ) := fun n =>
      (huA n).self_of_nhds
    have hcγ₁ : ContinuousAt γ₁ (t : ℝ) := hc₁.continuousAt (hJ₁.mem_nhds t.2.1)
    have hcγ₂ : ContinuousAt γ₂ (t : ℝ) := hc₂.continuousAt (hJ₂.mem_nhds t.2.2)
    have hpos : γ₁ (t : ℝ) = γ₂ (t : ℝ) := by
      have h1 : Filter.Tendsto (fun n => γ₁ ((u n : ↥O) : ℝ)) atTop (𝓝 (γ₁ (t : ℝ))) :=
        hcγ₁.tendsto.comp hseq
      have h2 : Filter.Tendsto (fun n => γ₁ ((u n : ↥O) : ℝ)) atTop (𝓝 (γ₂ (t : ℝ))) :=
        Filter.Tendsto.congr (fun n => (hposn n).symm) (hcγ₂.tendsto.comp hseq)
      exact tendsto_nhds_unique h1 h2
    -- velocity agreement at the limit time, by the difference-quotient
    -- characterisation of the derivative along the agreement sequence
    obtain ⟨v₁, a₁, hv₁, -, -, -⟩ := h₁ (t : ℝ) t.2.1
    obtain ⟨v₂, a₂, hv₂', -, -, -⟩ := h₂ (t : ℝ) t.2.2
    have hv₁' : HasDerivAt (fun s => extChartAt I (γ₁ (t : ℝ)) (γ₁ s)) v₁ (t : ℝ) := hv₁
    have hv₂ : HasDerivAt (fun s => extChartAt I (γ₁ (t : ℝ)) (γ₂ s)) v₂ (t : ℝ) := by
      rw [hpos]
      exact hv₂'
    have hφ : HasDerivAt (fun s => extChartAt I (γ₁ (t : ℝ)) (γ₁ s)
        - extChartAt I (γ₁ (t : ℝ)) (γ₂ s)) (v₁ - v₂) (t : ℝ) := hv₁'.sub hv₂
    have hslope := hasDerivAt_iff_tendsto_slope.mp hφ
    have hpunct : Filter.Tendsto (fun n => ((u n : ↥O) : ℝ)) atTop (𝓝[≠] (t : ℝ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hseq, Filter.Eventually.of_forall fun n h => ?_⟩
      exact hne ⟨n, Subtype.coe_injective h⟩
    have hzero : ∀ n, slope (fun s => extChartAt I (γ₁ (t : ℝ)) (γ₁ s)
        - extChartAt I (γ₁ (t : ℝ)) (γ₂ s)) (t : ℝ) ((u n : ↥O) : ℝ) = 0 := by
      intro n
      rw [slope_def_module]
      simp [hposn n, hpos]
    have hlim0 : Filter.Tendsto (fun _ : ℕ => (0 : E)) atTop (𝓝 (v₁ - v₂)) := by
      refine Filter.Tendsto.congr (fun n => hzero n) ?_
      exact hslope.comp hpunct
    have hv_eq : v₁ = v₂ := by
      have h0 := tendsto_nhds_unique hlim0 tendsto_const_nhds
      exact sub_eq_zero.mp h0
    -- conclude by local propagation of the agreement
    refine local_agree (t : ℝ) t.2 hpos ?_
    rw [hv₁'.deriv, hv₂.deriv, hv_eq]
  -- clopen in the preconnected overlap: agreement everywhere
  have hA_univ : A = Set.univ := IsClopen.eq_univ ⟨hA_closed, hA_open⟩ hA_nonempty
  intro t ht
  have : (⟨t, ht⟩ : ↥O) ∈ A := hA_univ ▸ Set.mem_univ _
  exact this.self_of_nhds

end Boundaryless

end PetersenLib

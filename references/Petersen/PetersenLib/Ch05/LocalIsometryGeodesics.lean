import PetersenLib.Ch05.LocalIsometry
import PetersenLib.Ch05.ChartTransition
import PetersenLib.Ch05.GeodesicCompleteness
import PetersenLib.Foundations.LocalSection

/-!
# Petersen Ch. 5, §5.6.1 — a local isometry maps geodesics to geodesics

Parts (1) and (2) of `prop:pet-ch5-local-isometry-properties` (Petersen
Prop. 5.6.1).  Parts (3) and (4) — the metric half — are in
`PetersenLib/Ch05/LocalIsometry.lean`.

The chart representative of `F : (M, g_M) → (N, g_N)` at `α`,
`Ψ_α = φ'_{Fα} ∘ F ∘ φ_α⁻¹ = writtenInExtChartAt I I' α F`, plays exactly the
role that the chart transition `τ = φ_β ∘ φ_α⁻¹` plays in
`PetersenLib/Ch05/ChartTransition.lean`, and this file mirrors that
development:

* `contDiffAt_writtenInExtChartAt_isom` / `hasFDerivAt_writtenInExtChartAt_isom`
  — the calculus of `Ψ_α` on its natural domain `isomTransitionDomain`.
* `chartMetricInner_writtenInExtChartAt_isom` — the **isometry Gram identity**
  `⟨DΨ_α a, DΨ_α b⟩_{Fα}^{Ψ_α y} = ⟨a, b⟩_α^y`.  This is the only place where
  the isometry hypothesis is used; it replaces the two-chart Gram identity
  `chartMetricInner_tangentCoordChange` of the chart-transition development.
* `gramLineDeriv_writtenInExtChartAt_isom` — the Koszul first-partial data is
  unchanged by `Ψ_α`.
* `mfderiv_chartChristoffelContraction_isom` — the **Christoffel
  transformation law across a local isometry**,
  `DΨ_α(Γ^M_α(v, w)(y)) = ∂²Ψ_α/∂v∂w = D²Ψ_α(v, w) + Γ^N_{Fα}(DΨ_α v, DΨ_α w)(Ψ_α y)`.
* `chartReading_geodesicODE_transfer_isom` — the geodesic ODE transfers along
  `Ψ_α`, giving part (1): `localIsometry_hasGeodesicEquationAt`,
  `localIsometry_mapsGeodesicsToGeodesics`, `localIsometry_isGeodesicOn`.
* `localIsometry_expNaturality` — part (2), naturality of the exponential map,
  stated at the **intrinsic** maximal geodesic (`geodesicMaximalDomain` /
  `geodesicMaximalCurve`) rather than at `expMap` / `expDomain`, as in
  `PetersenLib/Ch05/UniformInjectivityRadius.lean`.

Since `PetersenLib.IsGeodesic` is the moving-foot coordinate ODE
`ü + Γ_{γt}(u̇, u̇)(u) = 0` with `Γ` computed from the metric's chart Gram
matrix, no Levi-Civita connection object enters: the geodesic equation at time
`t` is read in the chart at the foot `γ t` on the source side and at the foot
`F (γ t)` on the target side, and `F (γ t)` is definitionally the foot of
`F ∘ γ` at `t`, so `α := γ t` requires no chart change on either side.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open Bundle Manifold Set Filter

open scoped Manifold Topology ContDiff

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless]

variable {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {F : M → M'}

/-! ## The chart representative `Ψ_α = φ'_{Fα} ∘ F ∘ φ_α⁻¹` and its calculus -/

/-- **Math.** The natural domain of the chart representative
`Ψ_α = φ'_{Fα} ∘ F ∘ φ_α⁻¹`: chart-`α` images of points lying in the chart
source at `α` and mapped by `F` into the chart source at `F α`. -/
def isomTransitionDomain (I : ModelWithCorners ℝ E H) (I' : ModelWithCorners ℝ E' H')
    [ChartedSpace H M] [ChartedSpace H' M'] (F : M → M') (α : M) : Set E :=
  (extChartAt I α).target ∩
    (extChartAt I α).symm ⁻¹' ((extChartAt I α).source ∩ F ⁻¹' (extChartAt I' (F α)).source)

theorem mem_isomTransitionDomain {α x : M} (hα : x ∈ (extChartAt I α).source)
    (hFx : F x ∈ (extChartAt I' (F α)).source) :
    extChartAt I α x ∈ isomTransitionDomain (M := M) (M' := M') I I' F α := by
  refine ⟨(extChartAt I α).map_source hα, ?_⟩
  rw [mem_preimage, (extChartAt I α).left_inv hα]
  exact ⟨hα, hFx⟩

theorem isomTransitionDomain_spec {α : M} {y : E}
    (hy : y ∈ isomTransitionDomain (M := M) (M' := M') I I' F α) :
    y ∈ (extChartAt I α).target ∧
      (extChartAt I α).symm y ∈ (extChartAt I α).source ∧
      F ((extChartAt I α).symm y) ∈ (extChartAt I' (F α)).source ∧
      extChartAt I α ((extChartAt I α).symm y) = y :=
  ⟨hy.1, hy.2.1, hy.2.2, (extChartAt I α).right_inv hy.1⟩

theorem isOpen_isomTransitionDomain (hF : Continuous F) (α : M) :
    IsOpen (isomTransitionDomain (M := M) (M' := M') I I' F α) :=
  (continuousOn_extChartAt_symm α).isOpen_inter_preimage (isOpen_extChartAt_target α)
    ((isOpen_extChartAt_source α).inter ((isOpen_extChartAt_source (F α)).preimage hF))

/-- **Math.** The chart representative `Ψ_α` is `C^∞` on its natural domain.
(From `contMDiff_iff` at the pair of charts `α`, `F α`, plus openness of the
extended-chart target in the boundaryless case.) -/
theorem contDiffAt_writtenInExtChartAt_isom (hF : ContMDiff I I' ∞ F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source) :
    ContDiffAt ℝ ∞ (writtenInExtChartAt I I' α F) (extChartAt I α x) := by
  have hcd := (contMDiff_iff (I := I) (I' := I') (n := ∞) (f := F)).mp hF |>.2 α (F α)
  set S : Set E := (extChartAt I α).target ∩
    (extChartAt I α).symm ⁻¹' F ⁻¹' (extChartAt I' (F α)).source with hS
  have hSopen : IsOpen S :=
    (continuousOn_extChartAt_symm α).isOpen_inter_preimage (isOpen_extChartAt_target α)
      ((isOpen_extChartAt_source (F α)).preimage hF.continuous)
  have hmem : extChartAt I α x ∈ S := by
    refine ⟨(extChartAt I α).map_source hα, ?_⟩
    rw [mem_preimage, (extChartAt I α).left_inv hα]
    exact hFx
  exact hcd.contDiffAt (hSopen.mem_nhds hmem)

theorem differentiableAt_writtenInExtChartAt_isom (hF : ContMDiff I I' ∞ F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source) :
    DifferentiableAt ℝ (writtenInExtChartAt I I' α F) (extChartAt I α x) :=
  (contDiffAt_writtenInExtChartAt_isom hF hα hFx).differentiableAt (by simp)

/-- **Math.** At the **centre** of its chart the representative `Ψ_x` has
derivative the manifold differential `DF_x` itself. -/
theorem hasFDerivAt_writtenInExtChartAt_isom_center (hF : ContMDiff I I' ∞ F) (x : M) :
    HasFDerivAt (writtenInExtChartAt I I' x F) (mfderiv I I' F x) (extChartAt I x x) := by
  have hFdiff : MDifferentiableAt I I' F x := hF.mdifferentiable (by norm_num) x
  have hd : DifferentiableAt ℝ (writtenInExtChartAt I I' x F) (extChartAt I x x) := by
    have h := hFdiff.differentiableWithinAt_writtenInExtChartAt
    rwa [I.range_eq_univ, differentiableWithinAt_univ] at h
  have heq : (mfderiv I I' F x : E →L[ℝ] E')
      = fderiv ℝ (writtenInExtChartAt I I' x F) (extChartAt I x x) :=
    mfderiv_eq_fderiv_writtenInExtChartAt hFdiff
  rw [heq]
  exact hd.hasFDerivAt

/-- **Math.** The derivative of `Ψ_α` at `φ_α x` is `Dτ'_{Fx→Fα} ∘ DF_x ∘ Dτ_{α→x}`:
chart-`α` coordinates at `x` are pushed to the tangent space at `x`, mapped by
`DF_x`, then read back in the chart at `F α`.  (Chain rule for
`Ψ_α = τ'_{Fx→Fα} ∘ Ψ_x ∘ τ_{α→x}` near `φ_α x`.) -/
theorem hasFDerivAt_writtenInExtChartAt_isom (hF : ContMDiff I I' ∞ F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source) :
    HasFDerivAt (writtenInExtChartAt I I' α F)
      ((tangentCoordChange I' (F x) (F α) (F x)).comp
        ((mfderiv I I' F x).comp (tangentCoordChange I α x x)))
      (extChartAt I α x) := by
  classical
  have h1 : HasFDerivAt (chartTransition (M := M) I α x) (tangentCoordChange I α x x)
      (extChartAt I α x) :=
    hasFDerivAt_chartTransition hα (mem_extChartAt_source (I := I) x)
  have h3 : HasFDerivAt (chartTransition (M := M') I' (F x) (F α))
      (tangentCoordChange I' (F x) (F α) (F x)) (extChartAt I' (F x) (F x)) :=
    hasFDerivAt_chartTransition (mem_extChartAt_source (I := I') (F x)) hFx
  have hc1 : chartTransition (M := M) I α x (extChartAt I α x) = extChartAt I x x :=
    chartTransition_extChartAt hα
  have hc2 : writtenInExtChartAt I I' x F (extChartAt I x x) = extChartAt I' (F x) (F x) := by
    simp only [writtenInExtChartAt, Function.comp_apply,
      (extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  have h2 : HasFDerivAt (writtenInExtChartAt I I' x F) (mfderiv I I' F x)
      (extChartAt I x x) := hasFDerivAt_writtenInExtChartAt_isom_center hF x
  have h2' : HasFDerivAt (writtenInExtChartAt I I' x F) (mfderiv I I' F x)
      (chartTransition (M := M) I α x (extChartAt I α x)) := by rw [hc1]; exact h2
  have h12 := h2'.comp (extChartAt I α x) h1
  have h3' : HasFDerivAt (chartTransition (M := M') I' (F x) (F α))
      (tangentCoordChange I' (F x) (F α) (F x))
      (writtenInExtChartAt I I' x F (chartTransition (M := M) I α x (extChartAt I α x))) := by
    rw [hc1, hc2]; exact h3
  have hcomp := h3'.comp (extChartAt I α x) h12
  refine hcomp.congr_of_eventuallyEq ?_
  have hnear : ∀ᶠ y in 𝓝 (extChartAt I α x),
      (extChartAt I α).symm y ∈ (extChartAt I x).source ∧
      F ((extChartAt I α).symm y) ∈ (extChartAt I' (F x)).source := by
    have hcont : ContinuousAt (extChartAt I α).symm (extChartAt I α x) := by
      refine ((continuousOn_extChartAt_symm α).continuousAt ?_)
      exact (isOpen_extChartAt_target α).mem_nhds ((extChartAt I α).map_source hα)
    have e1 : ∀ᶠ y in 𝓝 (extChartAt I α x),
        (extChartAt I α).symm y ∈ (extChartAt I x).source := by
      refine hcont.eventually_mem ((isOpen_extChartAt_source x).mem_nhds ?_)
      rw [(extChartAt I α).left_inv hα]; exact mem_extChartAt_source (I := I) x
    have e2 : ∀ᶠ y in 𝓝 (extChartAt I α x),
        F ((extChartAt I α).symm y) ∈ (extChartAt I' (F x)).source := by
      refine ((hF.continuous.continuousAt).comp hcont).eventually_mem
        ((isOpen_extChartAt_source (F x)).mem_nhds ?_)
      show F ((extChartAt I α).symm (extChartAt I α x)) ∈ _
      rw [(extChartAt I α).left_inv hα]; exact mem_extChartAt_source (I := I') (F x)
    exact e1.and e2
  filter_upwards [hnear] with y hy
  show writtenInExtChartAt I I' α F y
    = chartTransition (M := M') I' (F x) (F α)
      (writtenInExtChartAt I I' x F (chartTransition (M := M) I α x y))
  simp only [chartTransition_def, writtenInExtChartAt, Function.comp_apply]
  rw [(extChartAt I x).left_inv hy.1, (extChartAt I' (F x)).left_inv hy.2]

/-! ## The isometry Gram identity -/

/-- **Math.** The **isometry Gram identity**: the chart representative `Ψ_α`
intertwines the chart Gram pairing of `g_M` at `α` with that of `g_N` at `F α`,
`⟨DΨ_α a, DΨ_α b⟩_{Fα}^{Ψ_α y} = ⟨a, b⟩_α^y`.  Both sides equal an intrinsic
inner product — at `F x` and at `x` respectively — and `PreservesMetric`
bridges them.  This is the only place where the isometry hypothesis enters, and
it is the analogue of the two-chart Gram identity
`chartMetricInner_tangentCoordChange`. -/
theorem chartMetricInner_writtenInExtChartAt_isom
    (hF : IsLocalRiemannianIsometry gM gN F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source)
    (a b : E) :
    chartMetricInner (I := I') gN (F α) (extChartAt I' (F α) (F x))
        (fderiv ℝ (writtenInExtChartAt I I' α F) (extChartAt I α x) a)
        (fderiv ℝ (writtenInExtChartAt I I' α F) (extChartAt I α x) b)
      = chartMetricInner (I := I) gM α (extChartAt I α x) a b := by
  classical
  rw [chartMetricInner_eq_inner (I := I') gN hFx,
    chartMetricInner_eq_inner (I := I) gM hα]
  have hd := (hasFDerivAt_writtenInExtChartAt_isom hF.contMDiff hα hFx).fderiv
  have key : ∀ c : E, tangentCoordChange I' (F α) (F x) (F x)
      (fderiv ℝ (writtenInExtChartAt I I' α F) (extChartAt I α x) c)
      = mfderiv I I' F x (tangentCoordChange I α x x c) := by
    intro c
    rw [hd]
    show tangentCoordChange I' (F α) (F x) (F x)
        (tangentCoordChange I' (F x) (F α) (F x)
          (mfderiv I I' F x (tangentCoordChange I α x x c))) = _
    rw [tangentCoordChange_comp (I := I')
      (w := F x) (x := F α) (y := F x) (z := F x)
      ⟨⟨mem_extChartAt_source (I := I') (F x), hFx⟩, mem_extChartAt_source (I := I') (F x)⟩]
    exact tangentCoordChange_self (I := I') (x := F x) (z := F x)
      (mem_extChartAt_source (I := I') (F x))
  rw [key a, key b]
  exact (hF.preservesMetric x (tangentCoordChange I α x x a)
    (tangentCoordChange I α x x b)).symm

/-- **Math.** `DΨ_α` is **surjective**: this is what the bijectivity of `DF` in
`IsLocalRiemannianIsometry` buys, and it is what the nondegeneracy step of the
Christoffel transformation law needs. -/
theorem surjective_fderiv_writtenInExtChartAt_isom
    (hF : IsLocalRiemannianIsometry gM gN F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source) :
    Function.Surjective (fderiv ℝ (writtenInExtChartAt I I' α F) (extChartAt I α x)) := by
  rw [(hasFDerivAt_writtenInExtChartAt_isom hF.contMDiff hα hFx).fderiv]
  intro η
  refine ⟨tangentCoordChange I x α x
    ((hF.bijective_mfderiv x).2 (tangentCoordChange I' (F α) (F x) (F x) η)).choose, ?_⟩
  show tangentCoordChange I' (F x) (F α) (F x)
      (mfderiv I I' F x (tangentCoordChange I α x x (tangentCoordChange I x α x _))) = η
  rw [tangentCoordChange_comp (I := I) (w := x) (x := α) (y := x) (z := x)
      ⟨⟨mem_extChartAt_source (I := I) x, hα⟩, mem_extChartAt_source (I := I) x⟩,
    tangentCoordChange_self (I := I) (x := x) (z := x) (mem_extChartAt_source (I := I) x),
    ((hF.bijective_mfderiv x).2 (tangentCoordChange I' (F α) (F x) (F x) η)).choose_spec,
    tangentCoordChange_comp (I := I') (w := F α) (x := F x) (y := F α) (z := F x)
      ⟨⟨hFx, mem_extChartAt_source (I := I') (F x)⟩, hFx⟩,
    tangentCoordChange_self (I := I') (x := F α) (z := F x) hFx]

/-! ## Naturality of the Koszul first-partial data -/

/-- **Math.** The Koszul first-partial data is **unchanged by a local isometry**:
composing a map into the chart-`α` target with the chart representative `Ψ_α`
leaves every `gramLineDeriv` unchanged, because pointwise the chart metric
pairings of the first partials agree by the isometry Gram identity and the
chain rule.  (Mirror of `gramLineDeriv_chartTransition`.) -/
theorem gramLineDeriv_writtenInExtChartAt_isom
    (hF : IsLocalRiemannianIsometry gM gN F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source)
    {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {c : D → E} {q : D} (hc : ContDiffAt ℝ 2 c q) (hcq : c q = extChartAt I α x)
    (z d e : D) :
    gramLineDeriv (I := I') gN (F α) (fun r => writtenInExtChartAt I I' α F (c r)) q z d e
      = gramLineDeriv (I := I) gM α c q z d e := by
  rw [gramLineDeriv_def, gramLineDeriv_def]
  refine Filter.EventuallyEq.deriv_eq ?_
  have hline : Continuous fun s : ℝ => q + s • z :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hUq : c q ∈ isomTransitionDomain (M := M) (M' := M') I I' F α := by
    rw [hcq]; exact mem_isomTransitionDomain hα hFx
  have hnear_dom : ∀ᶠ r in 𝓝 q, c r ∈ isomTransitionDomain (M := M) (M' := M') I I' F α :=
    (hc.continuousAt).eventually_mem
      ((isOpen_isomTransitionDomain (I := I) (I' := I') hF.continuous α).mem_nhds hUq)
  have hnear_diff : ∀ᶠ r in 𝓝 q, DifferentiableAt ℝ c r := by
    have h1 : ∀ᶠ r in 𝓝 q, ContDiffAt ℝ 2 c r := hc.eventually (by simp)
    exact h1.mono fun r hr => hr.differentiableAt (by norm_num)
  have hs0 : Filter.Tendsto (fun s : ℝ => q + s • z) (𝓝 0) (𝓝 q) :=
    hline.tendsto' 0 q (by simp)
  filter_upwards [hs0.eventually hnear_dom, hs0.eventually hnear_diff] with s hdom hdiff
  set r : D := q + s • z
  obtain ⟨htarget, hsrcα, hFsrc, hright⟩ := isomTransitionDomain_spec hdom
  set xr : M := (extChartAt I α).symm (c r) with hxr
  have hΨ : HasFDerivAt (writtenInExtChartAt I I' α F)
      (fderiv ℝ (writtenInExtChartAt I I' α F) (c r)) (c r) := by
    have h := differentiableAt_writtenInExtChartAt_isom (α := α) hF.contMDiff hsrcα hFsrc
    rw [hright] at h
    exact h.hasFDerivAt
  have hchain : ∀ u : D, fderiv ℝ (fun r' => writtenInExtChartAt I I' α F (c r')) r u
      = fderiv ℝ (writtenInExtChartAt I I' α F) (c r) (fderiv ℝ c r u) := by
    intro u
    have hcomp : HasFDerivAt (fun r' => writtenInExtChartAt I I' α F (c r'))
        ((fderiv ℝ (writtenInExtChartAt I I' α F) (c r)).comp (fderiv ℝ c r)) r :=
      hΨ.comp r hdiff.hasFDerivAt
    rw [hcomp.fderiv]
    rfl
  have hfoot : writtenInExtChartAt I I' α F (c r) = extChartAt I' (F α) (F xr) := rfl
  rw [hfoot, hchain d, hchain e]
  have hGram := chartMetricInner_writtenInExtChartAt_isom (α := α) hF hsrcα hFsrc
    (fderiv ℝ c r d) (fderiv ℝ c r e)
  rw [hright] at hGram
  rw [hGram]

/-! ## The Christoffel transformation law across a local isometry -/

/-- **Math.** **The Christoffel transformation law across a local isometry.** For
`x` in the chart source at `α` with `F x` in the chart source at `F α`, and
`y = φ_α x`, the derivative of the chart representative
`Ψ_α = φ'_{Fα} ∘ F ∘ φ_α⁻¹` transports the chart-`α` Christoffel correction of
`g_M` onto the coordinate mixed partial of `Ψ_α` itself:
$$D\Psi_\alpha\big(\Gamma^M_\alpha(v, w)(y)\big)
  = \frac{\partial^2 \Psi_\alpha}{\partial v \, \partial w}(y)
  = D^2\Psi_\alpha(y)(v, w) + \Gamma^N_{F\alpha}(D\Psi_\alpha v, D\Psi_\alpha w)(\Psi_\alpha y).$$
Petersen's proof: `Ψ_α` reads the *same* metric on both sides (that is the
isometry hypothesis), so its mixed partial — determined by the Koszul formula
from first-partial data that `Ψ_α` preserves
(`gramLineDeriv_writtenInExtChartAt_isom`) — must be the transport of
`Γ^M_α`.  Formally we run the §5.1 extension trick `c̃ = id + t·ξ` through both
chart pictures and use nondegeneracy of the chart metric together with
surjectivity of `DΨ_α`. -/
theorem mfderiv_chartChristoffelContraction_isom
    (hF : IsLocalRiemannianIsometry gM gN F) {α x : M}
    (hα : x ∈ (extChartAt I α).source) (hFx : F x ∈ (extChartAt I' (F α)).source)
    (v w : E) :
    fderiv ℝ (writtenInExtChartAt I I' α F) (extChartAt I α x)
        (Geodesic.chartChristoffelContraction (I := I) gM α v w (extChartAt I α x))
      = mixedPartialCoord (I := I') gN (F α) (writtenInExtChartAt I I' α F)
          (extChartAt I α x) v w := by
  classical
  set y : E := extChartAt I α x with hy
  have hyU : y ∈ isomTransitionDomain (M := M) (M' := M') I I' F α :=
    mem_isomTransitionDomain hα hFx
  have hymemα : y ∈ (extChartAt I α).target := (extChartAt I α).map_source hα
  have hΨy : writtenInExtChartAt I I' α F y = extChartAt I' (F α) (F x) := by
    simp only [writtenInExtChartAt, Function.comp_apply, hy, (extChartAt I α).left_inv hα]
  have hymemβ : writtenInExtChartAt I I' α F y ∈ (extChartAt I' (F α)).target := by
    rw [hΨy]; exact (extChartAt I' (F α)).map_source hFx
  have hΨ2 : ContDiffAt ℝ 2 (writtenInExtChartAt I I' α F) y :=
    (contDiffAt_writtenInExtChartAt_isom hF.contMDiff hα hFx).of_le (by norm_cast)
  have hΨfd : HasFDerivAt (writtenInExtChartAt I I' α F)
      (fderiv ℝ (writtenInExtChartAt I I' α F) y) y :=
    (differentiableAt_writtenInExtChartAt_isom hF.contMDiff hα hFx).hasFDerivAt
  -- the pairing identity against arbitrary test coordinates
  have key : ∀ ξ : E,
      chartMetricInner (I := I') gN (F α) (writtenInExtChartAt I I' α F y)
          (fderiv ℝ (writtenInExtChartAt I I' α F) y
            (Geodesic.chartChristoffelContraction (I := I) gM α v w y))
          (fderiv ℝ (writtenInExtChartAt I I' α F) y ξ)
        = chartMetricInner (I := I') gN (F α) (writtenInExtChartAt I I' α F y)
            (mixedPartialCoord (I := I') gN (F α) (writtenInExtChartAt I I' α F) y v w)
            (fderiv ℝ (writtenInExtChartAt I I' α F) y ξ) := by
    intro ξ
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
    have hct_fderiv : ∀ (p : ℝ × E) (s : ℝ) (u : E),
        fderiv ℝ ct p (s, u) = u + s • ξ := by
      intro p s u
      have := fderiv_prodExtension_apply (c := fun z : E => z) (y := p.2)
        differentiableAt_id ξ p.1 s u
      simpa [hct] using this
    have hmemα' : ct ((0 : ℝ), y) ∈ (extChartAt I α).target := by rw [hct0]; exact hymemα
    have hΨct2 : ContDiffAt ℝ 2 (fun p => writtenInExtChartAt I I' α F (ct p)) ((0 : ℝ), y) :=
      (hct0 ▸ hΨ2).comp ((0 : ℝ), y) hct2
    have hmemβ' : (fun p => writtenInExtChartAt I I' α F (ct p)) ((0 : ℝ), y)
        ∈ (extChartAt I' (F α)).target := by
      show writtenInExtChartAt I I' α F (ct ((0 : ℝ), y)) ∈ _
      rw [hct0]; exact hymemβ
    -- Koszul formula on both sides, in the directions `(0,v), (0,w), (1,0)`
    have hKα := mixedPartialCoord_koszul (I := I) gM α hct2 hmemα'
      ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : E))
    have hKβ := mixedPartialCoord_koszul (I := I') gN (F α) hΨct2 hmemβ'
      ((0 : ℝ), v) ((0 : ℝ), w) ((1 : ℝ), (0 : E))
    have hRHS : ∀ z d e : ℝ × E,
        gramLineDeriv (I := I') gN (F α) (fun p => writtenInExtChartAt I I' α F (ct p))
            ((0 : ℝ), y) z d e
          = gramLineDeriv (I := I) gM α ct ((0 : ℝ), y) z d e := fun z d e =>
      gramLineDeriv_writtenInExtChartAt_isom hF hα hFx hct2 (hct0.trans hy) z d e
    rw [hRHS _ _ _, hRHS _ _ _, hRHS _ _ _] at hKβ
    -- the mixed partial of the affine extension is `Γ^M_α`
    have hct_mp : mixedPartialCoord (I := I) gM α ct ((0 : ℝ), y)
        ((0 : ℝ), v) ((0 : ℝ), w)
        = Geodesic.chartChristoffelContraction (I := I) gM α v w y := by
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
    -- the `F α`-side: slice-naturality and the chain rule
    have hΨct_slice : mixedPartialCoord (I := I') gN (F α)
        (fun p => writtenInExtChartAt I I' α F (ct p)) ((0 : ℝ), y) ((0 : ℝ), v) ((0 : ℝ), w)
        = mixedPartialCoord (I := I') gN (F α) (writtenInExtChartAt I I' α F) y v w := by
      rw [mixedPartialCoord_slice (I := I') gN (F α) hΨct2 v w]
      congr 1
      funext z
      simp [hct]
    have hΨct_z : fderiv ℝ (fun p => writtenInExtChartAt I I' α F (ct p)) ((0 : ℝ), y)
        ((1 : ℝ), (0 : E)) = fderiv ℝ (writtenInExtChartAt I I' α F) y ξ := by
      have hΨfd' : HasFDerivAt (writtenInExtChartAt I I' α F)
          (fderiv ℝ (writtenInExtChartAt I I' α F) y) (ct ((0 : ℝ), y)) := by
        rw [hct0]; exact hΨfd
      have hcomp : HasFDerivAt (fun p => writtenInExtChartAt I I' α F (ct p))
          ((fderiv ℝ (writtenInExtChartAt I I' α F) y).comp (fderiv ℝ ct ((0 : ℝ), y)))
          ((0 : ℝ), y) := hΨfd'.comp ((0 : ℝ), y) (hctd _).hasFDerivAt
      rw [hcomp.fderiv]
      show fderiv ℝ (writtenInExtChartAt I I' α F) y
        (fderiv ℝ ct ((0 : ℝ), y) ((1 : ℝ), (0 : E))) = _
      rw [hct_z]
    rw [hΨct_slice, hΨct_z, hct0] at hKβ
    -- transport the `α`-side pairing through the isometry Gram identity
    have hGram := chartMetricInner_writtenInExtChartAt_isom hF hα hFx
      (Geodesic.chartChristoffelContraction (I := I) gM α v w y) ξ
    have h2 : (2 : ℝ) * chartMetricInner (I := I') gN (F α) (writtenInExtChartAt I I' α F y)
        (fderiv ℝ (writtenInExtChartAt I I' α F) y
          (Geodesic.chartChristoffelContraction (I := I) gM α v w y))
        (fderiv ℝ (writtenInExtChartAt I I' α F) y ξ)
        = 2 * chartMetricInner (I := I') gN (F α) (writtenInExtChartAt I I' α F y)
            (mixedPartialCoord (I := I') gN (F α) (writtenInExtChartAt I I' α F) y v w)
            (fderiv ℝ (writtenInExtChartAt I I' α F) y ξ) := by
      rw [hΨy] at hKβ ⊢
      rw [← hy] at hGram
      rw [hGram, hKα, hKβ]
    linarith [h2]
  have hsurj := surjective_fderiv_writtenInExtChartAt_isom hF hα hFx
  have hsub : fderiv ℝ (writtenInExtChartAt I I' α F) y
      (Geodesic.chartChristoffelContraction (I := I) gM α v w y)
      - mixedPartialCoord (I := I') gN (F α) (writtenInExtChartAt I I' α F) y v w = 0 := by
    refine chartMetricInner_nondegenerate (I := I') gN (F α) hymemβ fun η => ?_
    obtain ⟨ξ, rfl⟩ := hsurj η
    rw [chartMetricInner_sub_left, key ξ, sub_self]
  exact sub_eq_zero.mp hsub

/-! ## Transfer of the geodesic ODE along a local isometry -/

/-- **Math.** **The geodesic ODE transfers along a local isometry**, at the level
of chart readings.  Let `γ` be a curve whose feet lie, for times near `t`, in
the chart source at `α` and whose `F`-images lie in the chart source at `F α`.
If the chart-`α` reading `u = φ_α ∘ γ` is differentiable near `t`, twice
differentiable at `t`, and satisfies `ü(t) + Γ^M_α(u̇(t), u̇(t))(u(t)) = 0`, then
the reading `w = φ'_{Fα} ∘ F ∘ γ` has the same regularity at `t` and satisfies
the chart-`F α` geodesic equation of `g_N`.

This is the computation `w = Ψ_α ∘ u`, `ẇ = DΨ_α(u)·u̇`,
`ẅ = D²Ψ_α(u̇, u̇) + DΨ_α(ü)`, combined with the Christoffel transformation law
`mfderiv_chartChristoffelContraction_isom`. -/
theorem chartReading_geodesicODE_transfer_isom
    (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M} {t : ℝ} {α : M}
    (hev : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I α).source ∧
      F (γ s) ∈ (extChartAt I' (F α)).source)
    (hu1 : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I α (γ s'))
      (deriv (fun s' => extChartAt I α (γ s')) s) s)
    {a : E} (hu2 : HasDerivAt (deriv (fun s' => extChartAt I α (γ s'))) a t)
    (heq : a + Geodesic.chartChristoffelContraction (I := I) gM α
      (deriv (fun s' => extChartAt I α (γ s')) t)
      (deriv (fun s' => extChartAt I α (γ s')) t) (extChartAt I α (γ t)) = 0) :
    (∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => extChartAt I' (F α) (F (γ s')))
        (deriv (fun s' => extChartAt I' (F α) (F (γ s'))) s) s) ∧
      HasDerivAt (deriv (fun s' => extChartAt I' (F α) (F (γ s'))))
        (- Geodesic.chartChristoffelContraction (I := I') gN (F α)
          (deriv (fun s' => extChartAt I' (F α) (F (γ s'))) t)
          (deriv (fun s' => extChartAt I' (F α) (F (γ s'))) t)
          (extChartAt I' (F α) (F (γ t)))) t := by
  classical
  set u : ℝ → E := fun s' => extChartAt I α (γ s') with hu_def
  set B : ℝ → E' := fun s' => extChartAt I' (F α) (F (γ s')) with hB_def
  have hmem_t : γ t ∈ (extChartAt I α).source ∧ F (γ t) ∈ (extChartAt I' (F α)).source :=
    hev.self_of_nhds
  -- near `t`, the `F α`-reading is `Ψ_α` applied to the `α`-reading
  have hEq : ∀ᶠ s in 𝓝 t, B s = writtenInExtChartAt I I' α F (u s) := by
    filter_upwards [hev] with s hs
    show extChartAt I' (F α) (F (γ s))
      = extChartAt I' (F α) (F ((extChartAt I α).symm (extChartAt I α (γ s))))
    rw [(extChartAt I α).left_inv hs.1]
  -- differentiability near `t`, with the transported velocity
  have hw' : ∀ᶠ s in 𝓝 t,
      HasDerivAt B (fderiv ℝ (writtenInExtChartAt I I' α F) (u s) (deriv u s)) s := by
    filter_upwards [eventually_eventually_nhds.mpr hev, hu1] with s hsev hs1
    have hΨs : HasFDerivAt (writtenInExtChartAt I I' α F)
        (fderiv ℝ (writtenInExtChartAt I I' α F) (u s)) (u s) :=
      (differentiableAt_writtenInExtChartAt_isom (α := α) hF.contMDiff
        hsev.self_of_nhds.1 hsev.self_of_nhds.2).hasFDerivAt
    have hΨu : HasDerivAt (fun s' => writtenInExtChartAt I I' α F (u s'))
        (fderiv ℝ (writtenInExtChartAt I I' α F) (u s) (deriv u s)) s :=
      hΨs.comp_hasDerivAt s hs1
    refine hΨu.congr_of_eventuallyEq ?_
    filter_upwards [hsev] with r hr
    show extChartAt I' (F α) (F (γ r))
      = extChartAt I' (F α) (F ((extChartAt I α).symm (extChartAt I α (γ r))))
    rw [(extChartAt I α).left_inv hr.1]
  have hderivB : ∀ᶠ s in 𝓝 t,
      deriv B s = fderiv ℝ (writtenInExtChartAt I I' α F) (u s) (deriv u s) :=
    hw'.mono fun s hs => hs.deriv
  have hvel : deriv B t = fderiv ℝ (writtenInExtChartAt I I' α F) (u t) (deriv u t) :=
    hderivB.self_of_nhds
  refine ⟨?_, ?_⟩
  · filter_upwards [hw', hderivB] with s h1 h2
    rw [h2]
    exact h1
  -- second derivative: differentiate `s ↦ DΨ_α(u s)·u̇(s)` at `t`
  have hΨ_smooth : ContDiffAt ℝ ∞ (writtenInExtChartAt I I' α F) (u t) :=
    contDiffAt_writtenInExtChartAt_isom hF.contMDiff hmem_t.1 hmem_t.2
  have hΨ_fd : DifferentiableAt ℝ (fderiv ℝ (writtenInExtChartAt I I' α F)) (u t) :=
    (hΨ_smooth.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by norm_num)
  have hφB : deriv B =ᶠ[𝓝 t]
      fun s => (fderiv ℝ (writtenInExtChartAt I I' α F) (u s)) (deriv u s) := hderivB
  have hc : HasDerivAt (fun s => fderiv ℝ (writtenInExtChartAt I I' α F) (u s))
      (fderiv ℝ (fderiv ℝ (writtenInExtChartAt I I' α F)) (u t) (deriv u t)) t :=
    hΨ_fd.hasFDerivAt.comp_hasDerivAt t hu1.self_of_nhds
  have hΦ : HasDerivAt
      (fun s => (fderiv ℝ (writtenInExtChartAt I I' α F) (u s)) (deriv u s))
      (fderiv ℝ (fderiv ℝ (writtenInExtChartAt I I' α F)) (u t) (deriv u t) (deriv u t)
        + (fderiv ℝ (writtenInExtChartAt I I' α F) (u t)) a) t :=
    hc.clm_apply hu2
  have hB2 : HasDerivAt (deriv B)
      (fderiv ℝ (fderiv ℝ (writtenInExtChartAt I I' α F)) (u t) (deriv u t) (deriv u t)
        + (fderiv ℝ (writtenInExtChartAt I I' α F) (u t)) a) t :=
    hΦ.congr_of_eventuallyEq hφB
  have ha_eq : a = - Geodesic.chartChristoffelContraction (I := I) gM α
      (deriv u t) (deriv u t) (u t) := by
    have := heq
    linear_combination (norm := module) this
  have hΨut : writtenInExtChartAt I I' α F (u t) = extChartAt I' (F α) (F (γ t)) := by
    show extChartAt I' (F α) (F ((extChartAt I α).symm (extChartAt I α (γ t)))) = _
    rw [(extChartAt I α).left_inv hmem_t.1]
  have hmp : mixedPartialCoord (I := I') gN (F α) (writtenInExtChartAt I I' α F) (u t)
        (deriv u t) (deriv u t)
      = fderiv ℝ (fderiv ℝ (writtenInExtChartAt I I' α F)) (u t) (deriv u t) (deriv u t)
        + Geodesic.chartChristoffelContraction (I := I') gN (F α)
            (fderiv ℝ (writtenInExtChartAt I I' α F) (u t) (deriv u t))
            (fderiv ℝ (writtenInExtChartAt I I' α F) (u t) (deriv u t))
            (writtenInExtChartAt I I' α F (u t)) := by
    rw [mixedPartialCoord_def, fderiv_fderiv_apply hΨ_fd]
  have hΓ := mfderiv_chartChristoffelContraction_isom hF hmem_t.1 hmem_t.2
    (deriv u t) (deriv u t)
  have hval : fderiv ℝ (fderiv ℝ (writtenInExtChartAt I I' α F)) (u t) (deriv u t) (deriv u t)
        + (fderiv ℝ (writtenInExtChartAt I I' α F) (u t)) a
      = - Geodesic.chartChristoffelContraction (I := I') gN (F α)
          (deriv B t) (deriv B t) (extChartAt I' (F α) (F (γ t))) := by
    rw [ha_eq, map_neg, hΓ, hmp, hvel, hΨut]
    linear_combination (norm := module)
  rw [← hval]
  exact hB2

/-! ## Part (1): a local isometry maps geodesics to geodesics -/

/-- **Math.** Petersen Prop. 5.6.1 (1), pointwise form: if `γ` satisfies the
geodesic equation of `g_M` at `t` and is continuous at `t`, then `F ∘ γ`
satisfies the geodesic equation of `g_N` at `t`.

The foot chart on the source side is the chart at `γ t`, and on the target side
the chart at `F (γ t) = (F ∘ γ) t`, so `α := γ t` requires no chart change.
Continuity at `t` is needed — and is not implied by the moving-foot equation,
which does not control chart-junk values — in order to know that `γ s` stays in
the chart source at `γ t` for `s` near `t`; the library records the same
hypothesis explicitly in `IsGeodesicWithInitialOn`. -/
theorem localIsometry_hasGeodesicEquationAt
    (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M} {t : ℝ}
    (hcont : ContinuousAt γ t)
    (hγ : Geodesic.HasGeodesicEquationAt (I := I) gM γ t) :
    Geodesic.HasGeodesicEquationAt (I := I') gN (F ∘ γ) t := by
  obtain ⟨v, a, hv, hev, ha, heq⟩ := hγ
  have hnear : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I (γ t)).source ∧
      F (γ s) ∈ (extChartAt I' (F (γ t))).source := by
    have e1 : ∀ᶠ s in 𝓝 t, γ s ∈ (extChartAt I (γ t)).source :=
      hcont.eventually_mem ((isOpen_extChartAt_source (γ t)).mem_nhds
        (mem_extChartAt_source (I := I) (γ t)))
    have e2 : ∀ᶠ s in 𝓝 t, F (γ s) ∈ (extChartAt I' (F (γ t))).source :=
      (hF.continuous.continuousAt.comp hcont).eventually_mem
        ((isOpen_extChartAt_source (F (γ t))).mem_nhds
          (mem_extChartAt_source (I := I') (F (γ t))))
    exact e1.and e2
  have hvd : deriv (fun s' => extChartAt I (γ t) (γ s')) t = v := hv.deriv
  obtain ⟨hev', hb⟩ :=
    chartReading_geodesicODE_transfer_isom (α := γ t) hF hnear hev
      (a := a) ha (by rw [hvd]; exact heq)
  exact ⟨deriv (fun s' => extChartAt I' (F (γ t)) (F (γ s'))) t,
    - Geodesic.chartChristoffelContraction (I := I') gN (F (γ t))
      (deriv (fun s' => extChartAt I' (F (γ t)) (F (γ s'))) t)
      (deriv (fun s' => extChartAt I' (F (γ t)) (F (γ s'))) t)
      (extChartAt I' (F (γ t)) (F (γ t))),
    hev'.self_of_nhds, hev', hb, neg_add_cancel _⟩

/-- **Math.** Petersen Prop. 5.6.1 (1): a local Riemannian isometry **maps
geodesics to geodesics**. -/
theorem localIsometry_mapsGeodesicsToGeodesics
    (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M} (hcont : Continuous γ)
    (hγ : IsGeodesic (I := I) gM γ) :
    IsGeodesic (I := I') gN (F ∘ γ) := fun t =>
  localIsometry_hasGeodesicEquationAt hF hcont.continuousAt (hγ t)

/-- **Math.** Petersen Prop. 5.6.1 (1), set form: a local Riemannian isometry maps
a geodesic on an open time set to a geodesic on that set. -/
theorem localIsometry_isGeodesicOn
    (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hcont : ContinuousOn γ J)
    (hγ : Geodesic.IsGeodesicOn (I := I) gM γ J) :
    Geodesic.IsGeodesicOn (I := I') gN (F ∘ γ) J := fun t ht =>
  localIsometry_hasGeodesicEquationAt hF (hcont.continuousAt (hJ.mem_nhds ht)) (hγ t ht)

/-! ## Part (2): naturality of the exponential map -/

/-- **Math.** A local isometry carries an admissible existence interval of the
geodesic initial-value problem `(p, v)` to an admissible existence interval of
`(F p, DF_p v)`, with witness `F ∘ γ`. -/
theorem localIsometry_isGeodesicWithInitialOn
    (hF : IsLocalRiemannianIsometry gM gN F) {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (h0 : (0 : ℝ) ∈ J) {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicWithInitialOn (I := I) gM γ J 0 p v) :
    IsGeodesicWithInitialOn (I := I') gN (F ∘ γ) J 0 (F p) (mfderiv I I' F p v) := by
  obtain ⟨hcont, hval, hvel, hgeo⟩ := hγ
  refine ⟨hF.continuous.comp_continuousOn hcont, by simp [hval], ?_,
    localIsometry_isGeodesicOn hF hJ hcont hgeo⟩
  -- the initial velocity: at the centre of its chart, `DΨ_p = DF_p`
  have hγ0 : ContinuousAt γ 0 := hcont.continuousAt (hJ.mem_nhds h0)
  have hΨ : HasFDerivAt (writtenInExtChartAt I I' p F) (mfderiv I I' F p)
      (extChartAt I p (γ 0)) := by
    rw [hval]
    exact hasFDerivAt_writtenInExtChartAt_isom_center hF.contMDiff p
  have hvel' : HasDerivAt (fun s => extChartAt I p (γ s)) (v : E) 0 := hvel
  have hcomp := hΨ.comp_hasDerivAt 0 hvel'
  refine hcomp.congr_of_eventuallyEq ?_
  have hnear : ∀ᶠ s in 𝓝 (0 : ℝ), γ s ∈ (extChartAt I p).source := by
    refine hγ0.eventually_mem ((isOpen_extChartAt_source p).mem_nhds ?_)
    rw [hval]; exact mem_extChartAt_source (I := I) p
  filter_upwards [hnear] with s hs
  show extChartAt I' (F p) ((F ∘ γ) s)
    = extChartAt I' (F p) (F ((extChartAt I p).symm (extChartAt I p (γ s))))
  rw [(extChartAt I p).left_inv hs]
  rfl

/-- **Math.** Petersen Prop. 5.6.1 (2): a local Riemannian isometry is **natural
with respect to the exponential map**, `F (exp_p v) = exp_{F p} (DF_p v)`
whenever `exp_p v` is defined.

The statement is made at the **intrinsic** maximal geodesic — the maximal
domain of the geodesic initial-value problem and the maximal geodesic through
it — rather than at `PetersenLib.expMap` / `PetersenLib.expDomain`, which are
chart artifacts (they follow an integral curve of the geodesic vector field of
the *single* chart at `p`, which is zeroed off that chart's source) and at
which the naturality statement is false; this is the same choice made in
`PetersenLib/Ch05/UniformInjectivityRadius.lean`.

Every admissible interval `J` for `(p, v)` is admissible for `(F p, DF_p v)`
with witness `F ∘ γ`, which gives the domain inclusion; the pointwise identity
then follows from uniqueness (`geodesicMaximalCurve_eqOn`) applied on both
sides. -/
theorem localIsometry_expNaturality [T2Space M] [T2Space M']
    (hF : IsLocalRiemannianIsometry gM gN F) (p : M) (v : TangentSpace I p) :
    geodesicMaximalDomain (I := I) gM p v ⊆
        geodesicMaximalDomain (I := I') gN (F p) (mfderiv I I' F p v) ∧
      ∀ t ∈ geodesicMaximalDomain (I := I) gM p v,
        F (geodesicMaximalCurve (I := I) gM p v t)
          = geodesicMaximalCurve (I := I') gN (F p) (mfderiv I I' F p v) t := by
  have key : ∀ t ∈ geodesicMaximalDomain (I := I) gM p v,
      t ∈ geodesicMaximalDomain (I := I') gN (F p) (mfderiv I I' F p v) ∧
        F (geodesicMaximalCurve (I := I) gM p v t)
          = geodesicMaximalCurve (I := I') gN (F p) (mfderiv I I' F p v) t := by
    intro t ht
    obtain ⟨γ, J, hJo, hJc, h0J, htJ, hγ⟩ :=
      exists_geodesicWitness_of_mem_maximalDomain (I := I) gM ht
    have hFγ : IsGeodesicWithInitialOn (I := I') gN (F ∘ γ) J 0 (F p)
        (mfderiv I I' F p v) := localIsometry_isGeodesicWithInitialOn hF hJo h0J hγ
    have htD : t ∈ geodesicMaximalDomain (I := I') gN (F p) (mfderiv I I' F p v) :=
      ⟨J, ⟨hJo, hJc, h0J, F ∘ γ, hFγ⟩, htJ⟩
    refine ⟨htD, ?_⟩
    rw [geodesicMaximalCurve_eqOn (I := I) gM hJo hJc h0J hγ htJ,
      geodesicMaximalCurve_eqOn (I := I') gN hJo hJc h0J hFγ htJ]
    rfl
  exact ⟨fun t ht => (key t ht).1, fun t ht => (key t ht).2⟩

end PetersenLib

end

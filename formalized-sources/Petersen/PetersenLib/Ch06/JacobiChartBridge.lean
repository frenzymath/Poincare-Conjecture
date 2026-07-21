import PetersenLib.Ch06.JacobiFields
import PetersenLib.Ch06.CurvatureChartBridgeMoving
import PetersenLib.Riemannian.Jacobi.PairJacobiField

/-!
# Petersen Ch. 6, §6.1 — reading the Jacobi equation in a fixed chart

`Ch06/JacobiFields.lean` states Petersen's Jacobi equation `J̈ + R(J, ċ)ċ = 0`
chart-free, at the *moving foot* `c t`. Every ODE engine, by contrast, wants one
*fixed* chart `α` and a genuine curve `ℝ → E`. This file supplies the dictionary
between the two, which is the step that existence/uniqueness was blocked on.

The obstruction was never the ODE theory — `Riemannian/Jacobi/PairJacobiField.lean`
already carries the whole chart-local pair system `(J, ∇J)` with existence
(`Jacobi.exists_isJacobiFieldOn_Icc_of_curve`) and Grönwall uniqueness
(`Jacobi.IsJacobiFieldOn.eqOn_of_left`). The obstruction was that the curvature term of
`jacobiEquation` is `curvatureTensorAt` evaluated at the *moving* point `c t`, while the
pair system's is `Jacobi.chartCurvature` in the *fixed* chart `α`, and the available
curvature bridge only compared the two when `α = c t`. `Ch06/CurvatureChartBridgeMoving.lean`
removed that restriction; this file spends it.

Main results:

* `tangentCoordChange_deriv_chartReading` — **velocity transfer**: the chart readings of a
  curve in two charts have derivatives related by `tangentCoordChange` (chain rule through
  the transition map);
* `tangentCoordChange_deriv_chartReading_curveVelocity` — its moving-foot specialization,
  identifying `curveVelocity` with the fixed-chart velocity `u̇`;
* `chartFieldRep_derivAlongCurve` — the chart-`α` reading of `V̇` is the coordinate
  covariant derivative `covariantDerivCoord` of the chart-`α` reading of `V`;
* `curvatureTensorAt_eq_chartCurvature_along` — the Jacobi curvature term
  `R(V, ċ)ċ` at the moving foot is the transported chart curvature
  `chartCurvature g α (u t) (V_α t) (u̇ t) (u̇ t)`;
* `IsJacobiFieldAlongOn` — the interval form of `IsJacobiFieldAlong`, which is what a
  chart-local ODE solution can supply and what a gluing argument consumes;
* `isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn` — **transfer**: a chart-`α` pair solution,
  transported to the moving foot, satisfies Petersen's chart-free Jacobi equation on
  `(a, b)`;
* `exists_isJacobiFieldAlongOn_Ioo_of_chart` — **chart-local existence** of a Jacobi field
  along `c` with prescribed initial data, for a curve staying in one chart.

## What is still missing

`exists_isJacobiFieldAlongOn_Ioo_of_chart` requires the curve to stay in a *single* chart.
Petersen's Thm 6.1.3 analogue — existence and uniqueness along an arbitrary geodesic — needs
the chart-covering walk that `Ch06/ParallelGlobal.lean` already performs for the first-order
parallel system (`parallelField_existence_uniqueness_global`): a Lebesgue number for a chart
cover of the compact interval, chart-local uniqueness, and left/right extension by gluing.
The pieces are all present one order down; the missing ingredient specific to Jacobi is a
**chart-change covariance of the pair system** (`Jacobi.IsJacobiFieldOn` transferred between
two overlapping charts), the analogue of DoCarmo's `IsJacobiFieldOn.transfer`. Note that
`covariantDerivCoord_transfer` gives that covariance for the *first* component; the second
component additionally needs the curvature naturality
`chartCurvature_coordChange` (`Ch06/CurvatureChartBridgeMoving.lean`), which is available.
-/

open Set Filter Bundle Manifold
open scoped Manifold Topology ContDiff Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ### Velocity transfer between charts -/

/-- **Math.** Petersen §6.1: **chart-change covariance of the velocity**. The chart-`β` and
chart-`α` readings `u_β = φ_β ∘ c`, `u_α = φ_α ∘ c` of a curve through a point lying in both
chart sources have derivatives related by the tangent coordinate change:
`Dτ(u̇_β) = u̇_α` for the transition `τ = φ_α ∘ φ_β⁻¹`. This is the chain rule through
`chartTransition`, and is the velocity-level companion of
`covariantDerivCoord_transfer` (which is the same statement one order up, with the
Christoffel correction). -/
theorem tangentCoordChange_deriv_chartReading {c : ℝ → M} (β α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hβ : c t ∈ (chartAt H β).source) (hα : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I β (c τ)) t) :
    tangentCoordChange I β α (c t) (deriv (fun τ => extChartAt I β (c τ)) t)
      = deriv (fun τ => extChartAt I α (c τ)) t := by
  have hxβ : c t ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hxα : c t ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hev : ∀ᶠ τ in 𝓝 t, c τ ∈ (extChartAt I β).source :=
    hc.eventually_mem ((isOpen_extChartAt_source (I := I) β).mem_nhds hxβ)
  have hfd : HasFDerivAt (chartTransition (M := M) I β α) (tangentCoordChange I β α (c t))
      (extChartAt I β (c t)) := hasFDerivAt_chartTransition hxβ hxα
  have hcomp : HasDerivAt (fun τ => chartTransition (M := M) I β α (extChartAt I β (c τ)))
      (tangentCoordChange I β α (c t) (deriv (fun τ => extChartAt I β (c τ)) t)) t := by
    have h := hfd.comp_hasDerivAt t hu.hasDerivAt
    rwa [Function.comp_def] at h
  have heq : (fun τ => chartTransition (M := M) I β α (extChartAt I β (c τ)))
      =ᶠ[𝓝 t] fun τ => extChartAt I α (c τ) := by
    filter_upwards [hev] with τ hτ
    exact chartTransition_extChartAt hτ
  exact ((hcomp.congr_of_eventuallyEq heq.symm).deriv).symm

/-- **Math.** Petersen §6.1: the **moving-foot velocity** `ċ(t)` of `Ch06/JacobiFields.lean`
is the transport into `T_{c t}M` of the fixed-chart velocity `u̇_α(t)`, for any chart `α`
around `c t`. Specialization of `tangentCoordChange_deriv_chartReading` to the target chart
`c t`, whose reading of `c` is by definition `Geodesic.chartLocalCurve c t`. -/
theorem tangentCoordChange_deriv_chartReading_curveVelocity {c : ℝ → M} (α : M) {t : ℝ}
    (hc : ContinuousAt c t) (hα : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t) :
    tangentCoordChange I α (c t) (c t) (deriv (fun τ => extChartAt I α (c τ)) t)
      = curveVelocity (I := I) c t :=
  tangentCoordChange_deriv_chartReading (I := I) α (c t) hc hα (mem_chart_source H (c t)) hu

/-! ### The covariant derivative in a fixed chart -/

/-- **Math.** Petersen §6.1: the **chart-`α` reading of `V̇` is the coordinate covariant
derivative of the chart-`α` reading of `V`**, `(V̇)_α = ∇_{u_α} V_α`. This is the working
form of chart-independence for the pair system: it says the pair `(V_α, (V̇)_α)` is exactly
the pair `(J, DJ)` of `Jacobi.IsJacobiFieldOn`. -/
theorem chartFieldRep_derivAlongCurve (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t) (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) :
    chartFieldRep (I := I) c α (fun τ => derivAlongCurve (I := I) g c V τ) t
      = covariantDerivCoord (I := I) g α (fun τ => extChartAt I α (c τ))
          (chartFieldRep (I := I) c α V) t := by
  have hxα : c t ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hfoot : c t ∈ (extChartAt I (c t)).source := mem_extChartAt_source (I := I) (c t)
  rw [chartFieldRep_apply, derivAlongCurve_eq_transfer (I := I) g α hc hsrc hu hV]
  rw [tangentCoordChange_comp (I := I) ⟨⟨hxα, hfoot⟩, hxα⟩]
  exact tangentCoordChange_self (I := I) hxα

/-! ### The curvature term in a fixed chart -/

/-- **Math.** Petersen §6.1: the **Jacobi curvature term at the moving foot**,
`R(V, ċ)ċ ∈ T_{c t}M`, is the transport into `T_{c t}M` of the fixed-chart curvature
`ℛ_α(V_α, u̇_α)u̇_α` evaluated at the chart point `u_α(t)`.

This is the identity the Jacobi ODE needs and that was blocked until
`Ch06/CurvatureChartBridgeMoving.lean`: the abstract `curvatureTensorAt` sits at the moving
point `c t`, the chart curvature sits in the fixed chart `α`, and the earlier bridge only
related the two on the diagonal `α = c t` — useless along a curve that moves. -/
theorem curvatureTensorAt_eq_chartCurvature_along (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t) (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t) :
    (tangentCoordChange I α (c t) (c t)
        (Jacobi.chartCurvature (I := I) g α (extChartAt I α (c t))
          (chartFieldRep (I := I) c α V t)
          (deriv (fun τ => extChartAt I α (c τ)) t)
          (deriv (fun τ => extChartAt I α (c τ)) t)) : TangentSpace I (c t))
      = curvatureTensorAt (g.leviCivita).toAffineConnection (c t)
          (V t) (curveVelocity (I := I) c t) (curveVelocity (I := I) c t) := by
  have hxα : c t ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hfoot : c t ∈ (extChartAt I (c t)).source := mem_extChartAt_source (I := I) (c t)
  have hV : tangentCoordChange I α (c t) (c t) (chartFieldRep (I := I) c α V t) = V t := by
    rw [chartFieldRep_apply, tangentCoordChange_comp (I := I) ⟨⟨hfoot, hxα⟩, hfoot⟩]
    exact tangentCoordChange_self (I := I) hfoot
  have hvel := tangentCoordChange_deriv_chartReading_curveVelocity (I := I) α hc hsrc hu
  rw [chartCurvature_eq_curvatureTensorAt_of_mem (I := I) g hsrc, hV, hvel]

/-! ### Transferring a chart pair solution back to the manifold -/

/-- **Math.** `covariantDerivCoord` is **local in the field**: it is built from `deriv V t`
and `V t`, so two fields agreeing near `t` have the same coordinate covariant derivative
at `t`. -/
theorem covariantDerivCoord_congr (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {V W : ℝ → E} {t : ℝ} (h : V =ᶠ[𝓝 t] W) :
    covariantDerivCoord (I := I) g α u V t = covariantDerivCoord (I := I) g α u W t := by
  rw [covariantDerivCoord_def, covariantDerivCoord_def, h.deriv_eq, h.self_of_nhds]

/-- **Math.** Petersen §6.1, `def:pet-ch6-jacobi-field`, **interval form**: `J` solves the
Jacobi equation `J̈ + R(J, ċ)ċ = 0` at every time of `s`. `Ch06/JacobiFields.lean`'s
`IsJacobiFieldAlong` is the case `s = univ`; the interval form is what a chart-local ODE
solution can supply, and what a gluing argument consumes. -/
def IsJacobiFieldAlongOn (g : RiemannianMetric I M) (c : ℝ → M)
    (J : ∀ t, TangentSpace I (c t)) (s : Set ℝ) : Prop :=
  ∀ t ∈ s, jacobiEquation (I := I) g c J t = 0

theorem isJacobiFieldAlong_iff_isJacobiFieldAlongOn_univ (g : RiemannianMetric I M)
    (c : ℝ → M) (J : ∀ t, TangentSpace I (c t)) :
    IsJacobiFieldAlong (I := I) g c J ↔ IsJacobiFieldAlongOn (I := I) g c J univ :=
  ⟨fun h t _ => h t, fun h t => h t (mem_univ t)⟩

/-- **Math.** Petersen §6.1: **a chart pair solution is a Jacobi field on the manifold**.
If `(J_α, DJ_α)` solves the chart-`α` covariant pair system `Jacobi.IsJacobiFieldOn` along
the chart reading `u_α = φ_α ∘ c` of a curve `c` staying in the chart source, then the
transported field `J t = (tangentCoordChange α → c t) (J_α t)` satisfies Petersen's
chart-free Jacobi equation on the open interval `(a, b)`.

This is the direction that carries **existence** from the ODE engine to the manifold: the
pair system has solutions with arbitrary prescribed `(J_α(a), DJ_α(a))`
(`Jacobi.exists_isJacobiFieldOn_Icc_of_curve`), and this theorem makes each one a genuine
Jacobi field along `c`.

The curvature step is `curvatureTensorAt_eq_chartCurvature_along`, i.e. the moving-point
bridge of `Ch06/CurvatureChartBridgeMoving.lean`; with only the diagonal bridge the chart
`α` would have had to equal `c t` for every `t`, which no single chart can do. -/
theorem isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn (g : RiemannianMetric I M) {c : ℝ → M}
    (α : M) {a b : ℝ} {Jα DJα : ℝ → E}
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (h : Jacobi.IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (c τ)) Jα DJα a b) :
    IsJacobiFieldAlongOn (I := I) g c
      (fun t => (tangentCoordChange I α (c t) (c t) (Jα t) : TangentSpace I (c t))) (Ioo a b) := by
  set J : ∀ t, TangentSpace I (c t) :=
    fun t => (tangentCoordChange I α (c t) (c t) (Jα t) : TangentSpace I (c t)) with hJdef
  -- the chart-`α` reading of the transported field is `Jα` itself, on `[a,b]`
  have hJrep : ∀ t ∈ Icc a b, chartFieldRep (I := I) c α J t = Jα t := by
    intro t ht
    have hxα : c t ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hsrc t ht
    have hfoot : c t ∈ (extChartAt I (c t)).source := mem_extChartAt_source (I := I) (c t)
    rw [chartFieldRep_apply, hJdef, tangentCoordChange_comp (I := I) ⟨⟨hxα, hfoot⟩, hxα⟩]
    exact tangentCoordChange_self (I := I) hxα
  intro t ht
  have htIcc : t ∈ Icc a b := Ioo_subset_Icc_self ht
  have hIoo : Ioo a b ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hIcc : Icc a b ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
  -- `Jα` is differentiable at the interior time `t`
  have hJαdiff : DifferentiableAt ℝ Jα t :=
    ((h.hasDerivWithinAt_fst t htIcc).hasDerivAt hIcc).differentiableAt
  have hDJαdiff : DifferentiableAt ℝ DJα t :=
    ((h.hasDerivWithinAt_snd t htIcc).hasDerivAt hIcc).differentiableAt
  -- `chartFieldRep c α J` agrees with `Jα` near `t`
  have hJev : chartFieldRep (I := I) c α J =ᶠ[𝓝 t] Jα := by
    filter_upwards [hIcc] with τ hτ using hJrep τ hτ
  have hJdiff : DifferentiableAt ℝ (chartFieldRep (I := I) c α J) t :=
    hJαdiff.congr_of_eventuallyEq hJev
  -- first covariant derivative: its chart reading is `DJα`, near `t`
  have hfst : ∀ τ ∈ Ioo a b,
      chartFieldRep (I := I) c α (fun σ => derivAlongCurve (I := I) g c J σ) τ = DJα τ := by
    intro τ hτ
    have hτIcc : t ∈ Icc a b := htIcc
    have hτIcc' : τ ∈ Icc a b := Ioo_subset_Icc_self hτ
    have hIccτ : Icc a b ∈ 𝓝 τ := Icc_mem_nhds hτ.1 hτ.2
    have hJαdiffτ : DifferentiableAt ℝ Jα τ :=
      ((h.hasDerivWithinAt_fst τ hτIcc').hasDerivAt hIccτ).differentiableAt
    have hJevτ : chartFieldRep (I := I) c α J =ᶠ[𝓝 τ] Jα := by
      filter_upwards [hIccτ] with σ hσ using hJrep σ hσ
    have hJdiffτ : DifferentiableAt ℝ (chartFieldRep (I := I) c α J) τ :=
      hJαdiffτ.congr_of_eventuallyEq hJevτ
    rw [chartFieldRep_derivAlongCurve (I := I) g α (hc τ hτIcc') (hsrc τ hτIcc')
      (hu τ hτIcc') hJdiffτ, covariantDerivCoord_congr (I := I) g α _ hJevτ]
    exact h.covariantDerivCoord_fst hτ
  have hDJev : chartFieldRep (I := I) c α (fun σ => derivAlongCurve (I := I) g c J σ)
      =ᶠ[𝓝 t] DJα := by
    filter_upwards [hIoo] with τ hτ using hfst τ hτ
  have hDJdiff : DifferentiableAt ℝ
      (chartFieldRep (I := I) c α (fun σ => derivAlongCurve (I := I) g c J σ)) t :=
    hDJαdiff.congr_of_eventuallyEq hDJev
  -- second covariant derivative, via the chart pair system's second equation
  have hsnd : derivAlongCurve (I := I) g c (fun σ => derivAlongCurve (I := I) g c J σ) t
      = (tangentCoordChange I α (c t) (c t)
          (-(Jacobi.chartCurvature (I := I) g α (extChartAt I α (c t)) (Jα t)
              (deriv (fun τ => extChartAt I α (c τ)) t)
              (deriv (fun τ => extChartAt I α (c τ)) t))) : TangentSpace I (c t)) := by
    rw [derivAlongCurve_eq_transfer (I := I) g α (hc t htIcc) (hsrc t htIcc) (hu t htIcc)
      hDJdiff, covariantDerivCoord_congr (I := I) g α _ hDJev]
    rw [h.covariantDerivCoord_snd ht]
  -- assemble the Jacobi equation
  have key := curvatureTensorAt_eq_chartCurvature_along (I := I) (V := J) g α (hc t htIcc)
    (hsrc t htIcc) (hu t htIcc)
  rw [hJrep t htIcc] at key
  rw [jacobiEquation_def, hsnd, map_neg, key]
  abel

/-! ### Chart-local existence on the manifold -/

/-- **Math.** Petersen §6.1, `thm:pet-ch6-jacobi-existence` (**chart-local half**):
**existence of a Jacobi field along a curve that stays in one chart**, with prescribed
initial data. Running the vendored pair-system existence
(`Jacobi.exists_isJacobiFieldOn_Icc_of_curve`, itself the linear-ODE engine
`LinearODE.exists_hasDerivWithinAt_Icc` instantiated at the Banach space `E × E`) and
transporting the solution back with `isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn`.

The initial data is stated in the chart `α`; `J₀` and `DJ₀` are the chart readings of the
prescribed `J(a)` and `J̇(a)`.

**Scope.** This is *not* Petersen's global Thm 6.1.3 analogue: the curve must stay in a
single chart. Globalizing it needs the chart-covering / gluing walk that
`Ch06/ParallelGlobal.lean` performs for the first-order parallel system — see the route
notes in the module docstring. -/
theorem exists_isJacobiFieldAlongOn_Ioo_of_chart (g : RiemannianMetric I M) {c : ℝ → M}
    (α : M) {a b : ℝ} (hab : a ≤ b)
    (hc : ∀ t ∈ Icc a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Icc a b, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hucont : ContinuousOn (fun τ => extChartAt I α (c τ)) (Icc a b))
    (hu'cont : ContinuousOn (deriv (fun τ => extChartAt I α (c τ))) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, extChartAt I α (c t) ∈ interior (extChartAt I α).target)
    (J₀ DJ₀ : E) :
    ∃ J : ∀ t, TangentSpace I (c t),
      IsJacobiFieldAlongOn (I := I) g c J (Ioo a b)
        ∧ J a = (tangentCoordChange I α (c a) (c a) J₀ : TangentSpace I (c a)) := by
  obtain ⟨Jα, DJα, hJa, _hDJa, hcert⟩ :=
    Jacobi.exists_isJacobiFieldOn_Icc_of_curve (I := I) g α hab hucont hu'cont hmem J₀ DJ₀
  exact ⟨fun t => (tangentCoordChange I α (c t) (c t) (Jα t) : TangentSpace I (c t)),
    isJacobiFieldAlongOn_Ioo_of_isJacobiFieldOn (I := I) g α hc hsrc hu hcert,
    by show (tangentCoordChange I α (c a) (c a) (Jα a) : TangentSpace I (c a)) = _; rw [hJa]⟩

end PetersenLib

end

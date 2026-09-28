import DoCarmoLib.Riemannian.Connection.ChartChristoffelChange
import DoCarmoLib.Riemannian.Connection.ChartFrameBridge
import DoCarmoLib.Riemannian.Geodesic.CovariantDerivative
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh1

/-!
# The intrinsic covariant derivative along a curve

This file supplies the manifold-valued operator missing between do Carmo's
Levi-Civita connection and the existing chart-coordinate geodesic calculus.
For a curve `c : ℝ → M` and a field `V : ∀ t, T_(c t) M`,
`covDerivAlong g c V t` is computed in the chart at the moving foot `c t` and
therefore belongs to `T_(c t) M`.

The fixed-chart theorem `covDerivAlong_eq_chart` is the chart-independence
statement: computation in any chart containing the foot gives the same tangent
vector after the canonical tangent-coordinate change. The algebra laws are do
Carmo Ch. 2, Proposition 2.2 (a) and (b).
-/

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The chart-`α` reading of a tangent field along `c`. -/
def chartFieldRep (c : ℝ → M) (α : M) (V : ∀ t, TangentSpace I (c t)) : ℝ → E :=
  fun t => tangentCoordChange I (c t) α (c t) (V t)

@[simp] theorem chartFieldRep_apply (c : ℝ → M) (α : M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    chartFieldRep (I := I) c α V t = tangentCoordChange I (c t) α (c t) (V t) := rfl

/-- **Math.** At the moving foot, the chart reading is the tangent vector itself. -/
@[simp] theorem chartFieldRep_self (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    chartFieldRep (I := I) c (c t) V t = V t :=
  tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (c t))

/-- **Math.** do Carmo Ch. 2, Prop. 2.2: the intrinsic covariant derivative
`DV/dt` of a tangent field `V` along `c`, induced by the Levi-Civita connection
of `g`. It is the existing coordinate derivative in the canonical chart at the
moving foot. -/
def covDerivAlong (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) : TangentSpace I (c t) :=
  (covariantDerivCoord (I := I) g (c t)
    (fun s => extChartAt I (c t) (c s)) (chartFieldRep (I := I) c (c t) V) t : E)

@[simp] theorem covDerivAlong_def (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    covDerivAlong (I := I) g c V t =
      (covariantDerivCoord (I := I) g (c t)
        (fun s => extChartAt I (c t) (c s)) (chartFieldRep (I := I) c (c t) V) t : E) := rfl

theorem chartFieldRep_add (c : ℝ → M) (α : M)
    (V W : ∀ t, TangentSpace I (c t)) :
    chartFieldRep (I := I) c α (fun s => V s + W s) =
      chartFieldRep (I := I) c α V + chartFieldRep (I := I) c α W := by
  funext t
  exact map_add (tangentCoordChange I (c t) α (c t)) (V t) (W t)

theorem chartFieldRep_smul (c : ℝ → M) (α : M) (f : ℝ → ℝ)
    (V : ∀ t, TangentSpace I (c t)) :
    chartFieldRep (I := I) c α (fun s => f s • V s) = f • chartFieldRep (I := I) c α V := by
  funext t
  exact map_smul (tangentCoordChange I (c t) α (c t)) (f t) (V t)

/-- **Math.** do Carmo Prop. 2.2 (a): `D(V + W)/dt = DV/dt + DW/dt`. -/
theorem covDerivAlong_add (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t) :
    covDerivAlong (I := I) g c (fun s => V s + W s) t =
      covDerivAlong (I := I) g c V t + covDerivAlong (I := I) g c W t := by
  rw [covDerivAlong_def, covDerivAlong_def, covDerivAlong_def, chartFieldRep_add]
  exact covariantDerivCoord_add (I := I) g (c t)
    (fun s => extChartAt I (c t) (c s))
    (chartFieldRep (I := I) c (c t) V) (chartFieldRep (I := I) c (c t) W) hV hW

/-- **Math.** do Carmo Prop. 2.2 (b):
`D(fV)/dt = f' V + f DV/dt`. -/
theorem covDerivAlong_smul (g : RiemannianMetric I M) (c : ℝ → M)
    (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    covDerivAlong (I := I) g c (fun s => f s • V s) t =
      deriv f t • V t + f t • covDerivAlong (I := I) g c V t := by
  rw [covDerivAlong_def, covDerivAlong_def, chartFieldRep_smul]
  set_option backward.isDefEq.respectTransparency false in
    simpa only [chartFieldRep_self] using
      covariantDerivCoord_smul (I := I) g (c t)
        (fun s => extChartAt I (c t) (c s)) f
        (chartFieldRep (I := I) c (c t) V) hf hV

section ChartIndependence

variable [I.Boundaryless]

/-- **Math.** Chart covariance of the coordinate covariant derivative for an arbitrary
tangent field along a curve. -/
theorem covariantDerivCoord_chart_transfer (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (β α : M) {t₀ : ℝ}
    (hc : ContinuousAt c t₀)
    (hsrcβ : c t₀ ∈ (chartAt H β).source)
    (hsrcα : c t₀ ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun t => extChartAt I β (c t)) t₀)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c β V) t₀) :
    tangentCoordChange I β α (c t₀)
        (covariantDerivCoord (I := I) g β (fun t => extChartAt I β (c t))
          (chartFieldRep (I := I) c β V) t₀) =
      covariantDerivCoord (I := I) g α (fun t => extChartAt I α (c t))
        (chartFieldRep (I := I) c α V) t₀ := by
  classical
  set x : M := c t₀
  set uβ : ℝ → E := fun t => extChartAt I β (c t)
  set Vβ : ℝ → E := chartFieldRep (I := I) c β V
  set τ : E → E := chartTransition (I := I) β α
  set y₀ : E := extChartAt I β x
  have hxβ : x ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hxα : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hev : ∀ᶠ t in nhds t₀, c t ∈ (extChartAt I β).source ∩ (extChartAt I α).source :=
    hc.eventually_mem (((isOpen_extChartAt_source (I := I) β).inter
      (isOpen_extChartAt_source (I := I) α)).mem_nhds ⟨hxβ, hxα⟩)
  have hdom : y₀ ∈ chartTransitionSource (I := I) (M := M) β α :=
    extChartAt_mem_chartTransitionSource (I := I) hsrcβ hsrcα
  have hτ₂ : ContDiffAt ℝ 2 τ y₀ := (contDiffAt_chartTransition hdom).of_le (by decide)
  have hτfd : DifferentiableAt ℝ (fderiv ℝ τ) y₀ :=
    (hτ₂.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hτd : DifferentiableAt ℝ τ y₀ := hτ₂.differentiableAt (by norm_num)
  have hA : fderiv ℝ τ y₀ = tangentCoordChange I β α x := by
    rw [show τ = chartTransition (I := I) β α from rfl,
      fderiv_chartTransition (I := I) hdom, (extChartAt I β).left_inv hxβ]
  have huβ : HasDerivAt uβ (deriv uβ t₀) t₀ := hu.hasDerivAt
  have hA' : HasDerivAt (fun t => fderiv ℝ τ (uβ t))
      (fderiv ℝ (fderiv ℝ τ) y₀ (deriv uβ t₀)) t₀ :=
    hτfd.hasFDerivAt.comp_hasDerivAt t₀ huβ
  have hVα_eq : chartFieldRep (I := I) c α V =ᶠ[nhds t₀]
      fun t => fderiv ℝ τ (uβ t) (Vβ t) := by
    filter_upwards [hev] with t ht
    have htβ : c t ∈ (chartAt H β).source := by
      simpa only [extChartAt_source] using ht.1
    have htα : c t ∈ (chartAt H α).source := by
      simpa only [extChartAt_source] using ht.2
    have htdom : uβ t ∈ chartTransitionSource (I := I) (M := M) β α :=
      extChartAt_mem_chartTransitionSource (I := I) htβ htα
    have hder : fderiv ℝ τ (uβ t) = tangentCoordChange I β α (c t) := by
      rw [show τ = chartTransition (I := I) β α from rfl,
        fderiv_chartTransition (I := I) htdom, (extChartAt I β).left_inv ht.1]
    rw [hder]
    exact (tangentCoordChange_comp
      ⟨⟨mem_extChartAt_source (I := I) (c t), ht.1⟩, ht.2⟩).symm
  have huα_eq : (fun t => extChartAt I α (c t)) =ᶠ[nhds t₀] fun t => τ (uβ t) := by
    filter_upwards [hev] with t ht
    have htβ : c t ∈ (chartAt H β).source := by
      simpa only [extChartAt_source] using ht.1
    exact (chartTransition_extChartAt htβ).symm
  have huα' : HasDerivAt (fun t => extChartAt I α (c t))
      (fderiv ℝ τ y₀ (deriv uβ t₀)) t₀ := by
    have hcomp : HasDerivAt (τ ∘ uβ) (fderiv ℝ τ y₀ (deriv uβ t₀)) t₀ :=
      hτd.hasFDerivAt.comp_hasDerivAt t₀ huβ
    exact hcomp.congr_of_eventuallyEq huα_eq
  have hVα' : HasDerivAt (chartFieldRep (I := I) c α V)
      (fderiv ℝ (fderiv ℝ τ) y₀ (deriv uβ t₀) (Vβ t₀)
        + fderiv ℝ τ y₀ (deriv Vβ t₀)) t₀ :=
    (hA'.clm_apply hV.hasDerivAt).congr_of_eventuallyEq hVα_eq
  have hlaw := chartChristoffelContraction_change (I := I) g α β hsrcα hsrcβ
    (deriv uβ t₀) (Vβ t₀)
  have hfoot : chartFieldRep (I := I) c α V t₀ =
      tangentCoordChange I β α x (Vβ t₀) :=
    (tangentCoordChange_comp
      ⟨⟨mem_extChartAt_source (I := I) x, hxβ⟩, hxα⟩).symm
  have huβt : uβ t₀ = y₀ := rfl
  rw [covariantDerivCoord_def, covariantDerivCoord_def, huα'.deriv, hVα'.deriv, hA]
  rw [huβt, map_add, hlaw, hfoot]
  abel

/-- **Math.** Chart independence of `covDerivAlong`: any chart containing the
foot computes the same intrinsic tangent vector after transport back to the
moving-foot chart. -/
theorem covDerivAlong_eq_chart (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I α (c s)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) :
    covDerivAlong (I := I) g c V t =
      tangentCoordChange I α (c t) (c t)
        (covariantDerivCoord (I := I) g α (fun s => extChartAt I α (c s))
          (chartFieldRep (I := I) c α V) t) := by
  rw [covDerivAlong_def]
  exact (covariantDerivCoord_chart_transfer (I := I) g α (c t) hc hsrc
    (mem_chart_source H (c t)) hu hV).symm

/-- **Math.** The tangent coordinate change between charts containing the foot is
injective, with inverse the reverse coordinate change. -/
theorem tangentCoordChange_eq_zero_iff { β α x : M}
    (hβ : x ∈ (extChartAt I β).source) (hα : x ∈ (extChartAt I α).source) (v : E) :
    tangentCoordChange I β α x v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have hcomp := tangentCoordChange_comp (I := I) (w := β) (x := α) (y := β) (z := x) (v := v)
    ⟨⟨hβ, hα⟩, hβ⟩
  rw [h, map_zero, tangentCoordChange_self hβ] at hcomp
  exact hcomp.symm

/-- **Math.** Vanishing of the intrinsic derivative is equivalent to vanishing of its
coordinate value in any chart containing the foot. -/
theorem covDerivAlong_eq_zero_iff_chart (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun s => extChartAt I α (c s)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) :
    covDerivAlong (I := I) g c V t = 0 ↔
      covariantDerivCoord (I := I) g α (fun s => extChartAt I α (c s))
        (chartFieldRep (I := I) c α V) t = 0 := by
  rw [covDerivAlong_eq_chart (I := I) g α hc hsrc hu hV]
  exact tangentCoordChange_eq_zero_iff (I := I) (by rwa [extChartAt_source])
    (mem_extChartAt_source (I := I) (c t)) _

end ChartIndependence

end Riemannian

end

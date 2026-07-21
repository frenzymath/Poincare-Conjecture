import PetersenLib.Ch05.ChartTransition
import PetersenLib.Riemannian.Geodesic.CovariantDerivative

/-!
# Petersen Ch. 6, §6.1 — the connection along a curve (GTM 171, 3rd ed.)

Petersen's §6.1 (pp. 248–253): the covariant derivative `V̇` of a vector field
`V` along a curve `c`, parallel fields, and Theorem 6.1.3 (existence and
uniqueness of parallel fields).  Blueprint nodes
`def:pet-ch6-vector-field-along-curve`, `def:pet-ch6-parallel-field`,
`thm:pet-ch6-parallel-field-existence-uniqueness`.

## Conventions

This file lives on the **chart-Christoffel side** of the project (Petersen's
Ch. 5 world: `Geodesic.chartChristoffelContraction`, `chartLocalCurve`), *not*
on the abstract `AffineConnection`/Koszul side of Ch. 2 where
`curvatureTensor` and `sectionalCurvature` live.  The two are disjoint in this
development and no bridge lemma between them exists.

Following the Ch. 5 house convention (`curveAcceleration`), a vector field
along `c : ℝ → M` is a dependent map `V : ∀ t, TangentSpace I (c t)`, and its
covariant derivative is read **in the canonical chart at the moving foot**
`c t`:

* `chartFieldRep c α V` — the chart-`α` reading of `V`, pushing each `V τ`
  from its own foot chart into the chart at `α` by `tangentCoordChange`.  At
  the moving foot it is the identity (`chartFieldRep_self`).
* `derivAlongCurve g c V t` — Petersen's `V̇(t)`: the Christoffel-corrected
  coordinate derivative `V̇ᵏ + Vⁱ ċʲ Γᵏ_{ij}` of the definition node, read at
  the foot `c t`, i.e. `deriv (chartFieldRep c (c t) V) t + Γ_{c t}(ċ, V)(c t)`.
* `IsParallelAlong g c V` — Petersen's parallel field: `V̇ ≡ 0`.

## What is proved

* `derivAlongCurve_add`, `derivAlongCurve_smul_fun` — the linearity and
  Leibniz clauses claimed by the definition node.
* `hasDerivAt_inner_along` — the **metric product rule**
  `d/dt g(V, W) = g(V̇, W) + g(V, Ẇ)`, the remaining clause of the definition
  node, and `hasDerivAt_inner_eq_zero_of_isParallelAlong` — parallel fields
  neither change length nor relative angle (`def:pet-ch6-parallel-field`).
* `covariantDerivCoord_transfer` — **chart-change covariance**, the technical
  heart of the file: for two charts `β`, `α` around `c t₀`, the chart-`β` and
  chart-`α` coordinate covariant derivatives correspond under
  `tangentCoordChange I β α (c t₀)`.  This is what makes `derivAlongCurve`
  chart-independent, i.e. what makes the definition node's "manifestly
  independent of the coordinate system" claim true.  The proof runs the
  product rule on `V_α = Dτ(u_β) V_β` and cancels the resulting second-order
  term `D²τ(u̇_β, V_β)` against the inhomogeneous term of the Christoffel
  transformation law `tangentCoordChange_chartChristoffelContraction` (§5.1).
* `derivAlongCurve_eq_transfer` / `derivAlongCurve_eq_zero_iff` — `V̇` computed
  from, and vanishing iff it vanishes in, any fixed chart `α` around `c t`.
* `exists_isParallelAlong`, `isParallelAlong_eqOn`, and their combination
  `parallelField_existence_uniqueness` — **Theorem 6.1.3**.  Petersen's proof
  is exactly ours: parallelism is the first-order *linear* system
  `V̇ʲ = −Σᵢ Vⁱ αᵢʲ`, so Picard–Lindelöf plus linearity give a solution with
  prescribed value at any `t₀`, unique on the whole interval.  Existence uses
  the vendored linear-ODE engine (`exists_parallelTransport_spec`, whose flow
  `parallelTransport` is a linear *isomorphism*, which is what lets us
  prescribe the value at an interior `t₀` rather than at an endpoint);
  uniqueness is Grönwall forward and backward from `t₀`
  (`LinearODE.IsSolOn.eqOn_of_left`/`_of_right`).

## What is deferred, and why

* **Single chart.** Theorem 6.1.3 is stated for a curve whose relevant piece
  lies in the source of *one* chart `α`.  Petersen's `I` is arbitrary and a
  curve of any length leaves every chart; removing this restriction needs a
  supremum-walk gluing argument across charts (as in the sibling Poincaré
  project's `exists_isParallelAlongOn`), which `covariantDerivCoord_transfer`
  makes possible but which is a separate piece of work.
* **Open interval.** The conclusion is stated on `Ioo a b` rather than a
  closed interval because `derivAlongCurve` is defined with the two-sided
  `deriv`, which is not the right notion at an endpoint.  This is a faithful
  reading of Petersen, whose `I` is an interval and whose ODE argument is
  interior.
* **Regularity hypotheses are explicit.** `derivAlongCurve` is defined via
  `deriv`, which returns junk `0` off the differentiability locus; so `V̇ = 0`
  alone does *not* imply `V` is `C¹`, and the uniqueness clause must carry the
  differentiability of the competing field `W` as a hypothesis (Petersen
  leaves smoothness of fields implicit).  Likewise the ODE coefficient's
  continuity (`hcont`) and operator-norm bound (`hK`) on the compact `Icc a b`
  are taken as hypotheses: they are exactly the hypotheses of the vendored
  `exists_parallelTransport_spec`, and both hold automatically for a `C¹`
  curve by compactness.
* The higher-partials nodes (`def:pet-ch6-higher-order-partials`, Lemma 6.1.2,
  Example 6.1.1) and the Jacobi-field nodes are not treated here.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff NNReal

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen §6.1 (p. 248): the **chart-`α` reading** of a vector field
`V` along `c`.  Each `V τ` lives in `T_{c τ}M`, coordinatised by the chart at its
own foot `c τ`; this pushes it into the chart at the fixed basepoint `α` by the
tangent coordinate change.  Meaningful when `c τ` lies in the chart source at
`α`; junk off it.  These are Petersen's components `Vᵏ` of `V = Vᵏ ∂ₖ`. -/
def chartFieldRep (c : ℝ → M) (α : M) (V : ∀ t, TangentSpace I (c t)) : ℝ → E :=
  fun τ => tangentCoordChange I (c τ) α (c τ) (V τ)

@[simp] theorem chartFieldRep_apply (c : ℝ → M) (α : M) (V : ∀ t, TangentSpace I (c t)) (τ : ℝ) :
    chartFieldRep (I := I) c α V τ = tangentCoordChange I (c τ) α (c τ) (V τ) := rfl

/-- **Math.** At the moving foot the chart reading is the field itself: the
coordinate change from the chart at `c t` to itself is the identity. -/
@[simp] theorem chartFieldRep_self (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    chartFieldRep (I := I) c (c t) V t = V t :=
  tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) (c t))

/-- **Math.** Petersen §6.1 (pp. 248–249), `def:pet-ch6-vector-field-along-curve`:
the **covariant derivative** `V̇ = dV/dt` of a vector field `V` along the curve
`c`, read in the canonical chart at the moving foot `c t`.  With `u = φ_{c t} ∘ c`
the chart reading of the curve, this is Petersen's coordinate formula
`V̇(t) = V̇ᵏ(t) ∂ₖ + Vⁱ(t) ċʲ(t) Γᵏ_{ij} ∂ₖ`, i.e.
`deriv (chartFieldRep c (c t) V) t + Γ_{c t}(u̇(t), V t)(u(t))`, regarded as a
tangent vector at `c t` (`TangentSpace I (c t)` is definitionally the model space
`E`, coordinatised by the chart at `c t`).  Same moving-foot convention as
Ch. 5's `curveAcceleration`.  Chart-independence — Petersen's "manifestly
independent of the coordinate system" — is `covariantDerivCoord_transfer`. -/
def derivAlongCurve (g : RiemannianMetric I M) (c : ℝ → M) (V : ∀ t, TangentSpace I (c t))
    (t : ℝ) : TangentSpace I (c t) :=
  (deriv (chartFieldRep (I := I) c (c t) V) t
    + Geodesic.chartChristoffelContraction (I := I) g (c t)
        (deriv (Geodesic.chartLocalCurve (I := I) c t) t) (V t)
        (extChartAt I (c t) (c t)) : E)

@[simp] theorem derivAlongCurve_def (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    derivAlongCurve (I := I) g c V t =
      (deriv (chartFieldRep (I := I) c (c t) V) t
        + Geodesic.chartChristoffelContraction (I := I) g (c t)
            (deriv (Geodesic.chartLocalCurve (I := I) c t) t) (V t)
            (extChartAt I (c t) (c t)) : E) := rfl

/-- **Math.** Petersen §6.1 (p. 252), `def:pet-ch6-parallel-field`: `V` is
**parallel along `c`** when its covariant derivative vanishes identically,
`V̇ ≡ 0`. -/
def IsParallelAlong (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) : Prop :=
  ∀ t, derivAlongCurve (I := I) g c V t = 0

/-! ### Linearity of `V ↦ V̇` -/

theorem chartFieldRep_add (c : ℝ → M) (β : M) (V W : ∀ t, TangentSpace I (c t)) :
    chartFieldRep (I := I) c β (fun s => V s + W s)
      = chartFieldRep (I := I) c β V + chartFieldRep (I := I) c β W := by
  funext τ
  exact map_add (tangentCoordChange I (c τ) β (c τ)) (V τ) (W τ)

theorem chartFieldRep_smul_fun (c : ℝ → M) (β : M) (f : ℝ → ℝ)
    (V : ∀ t, TangentSpace I (c t)) :
    chartFieldRep (I := I) c β (fun s => f s • V s) = f • chartFieldRep (I := I) c β V := by
  funext τ
  exact map_smul (tangentCoordChange I (c τ) β (c τ)) (f τ) (V τ)

/-- **Math.** Petersen §6.1 (p. 249): **additivity** of the covariant derivative
along a curve, `d/dt (V + W) = V̇ + Ẇ`, one of the two clauses claimed by
`def:pet-ch6-vector-field-along-curve`. -/
theorem derivAlongCurve_add (g : RiemannianMetric I M) (c : ℝ → M)
    (V W : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) W) t) :
    derivAlongCurve (I := I) g c (fun s => V s + W s) t
      = derivAlongCurve (I := I) g c V t + derivAlongCurve (I := I) g c W t := by
  simp only [derivAlongCurve_def, chartFieldRep_add, deriv_add hV hW]
  rw [show ((V t + W t : TangentSpace I (c t)) : E) = (V t : E) + (W t : E) from rfl,
    Geodesic.chartChristoffelContraction_add_right]
  abel

/-- **Math.** Petersen §6.1 (p. 249): the **Leibniz rule**
`d/dt (λ V) = λ̇ V + λ V̇` for a scalar `λ : I → ℝ`, the second linearity clause
claimed by `def:pet-ch6-vector-field-along-curve`. -/
theorem derivAlongCurve_smul_fun (g : RiemannianMetric I M) (c : ℝ → M)
    (f : ℝ → ℝ) (V : ∀ t, TangentSpace I (c t)) {t : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c (c t) V) t) :
    derivAlongCurve (I := I) g c (fun s => f s • V s) t
      = deriv f t • V t + f t • derivAlongCurve (I := I) g c V t := by
  simp only [derivAlongCurve_def, chartFieldRep_smul_fun, deriv_smul hf hV]
  rw [show ((f t • V t : TangentSpace I (c t)) : E) = f t • (V t : E) from rfl,
    Geodesic.chartChristoffelContraction_smul_right]
  rw [chartFieldRep_self]
  module

section Transfer

variable [I.Boundaryless]

/-- **Math.** Petersen §6.1 (p. 249): **chart-change covariance** of the
coordinate covariant derivative along a curve — the formal content of Petersen's
claim that `V̇` is "manifestly independent ... of the coordinate system".  For two
charts `β`, `α` whose sources contain `c t₀`, the chart-`β` and chart-`α`
coordinate covariant derivatives correspond under `tangentCoordChange I β α (c t₀)`.

Proof: the chart readings are related by `V_α = Dτ(u_β) V_β` for the transition
`τ = φ_α ∘ φ_β⁻¹`, so the product rule contributes a second-order term
`D²τ(u̇_β, V_β)`; this cancels exactly against the inhomogeneous term of the
Christoffel transformation law `tangentCoordChange_chartChristoffelContraction`
(Petersen §5.1), leaving the transport of `Γ_β` alone. -/
theorem covariantDerivCoord_transfer (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (β α : M) {t₀ : ℝ}
    (hc : ContinuousAt c t₀)
    (hsrcβ : c t₀ ∈ (chartAt H β).source)
    (hsrcα : c t₀ ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I β (c τ)) t₀)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c β V) t₀) :
    tangentCoordChange I β α (c t₀)
        (covariantDerivCoord (I := I) g β (fun τ => extChartAt I β (c τ))
          (chartFieldRep (I := I) c β V) t₀)
      = covariantDerivCoord (I := I) g α (fun τ => extChartAt I α (c τ))
          (chartFieldRep (I := I) c α V) t₀ := by
  classical
  set x : M := c t₀ with hx
  set ux : ℝ → E := fun τ => extChartAt I β (c τ) with hux
  set Vx : ℝ → E := chartFieldRep (I := I) c β V with hVx
  set tm : E → E := chartTransition (M := M) I β α with htm
  set y₀ : E := extChartAt I β x with hy₀
  have hxx : x ∈ (extChartAt I β).source := by rwa [extChartAt_source]
  have hxα : x ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  -- the curve stays in both chart sources near `t₀`
  have hev : ∀ᶠ τ in 𝓝 t₀, c τ ∈ (extChartAt I β).source ∩ (extChartAt I α).source :=
    hc.eventually_mem
      (((isOpen_extChartAt_source (I := I) β).inter
        (isOpen_extChartAt_source (I := I) α)).mem_nhds ⟨hxx, hxα⟩)
  -- calculus of the transition map at the foot
  have hdom : y₀ ∈ chartTransitionDomain (M := M) I β α := mem_chartTransitionDomain hxx hxα
  have hτ2 : ContDiffAt ℝ 2 tm y₀ := (contDiffAt_chartTransition hdom).of_le (by decide)
  have hτfd : DifferentiableAt ℝ (fderiv ℝ tm) y₀ :=
    (hτ2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hτd : DifferentiableAt ℝ tm y₀ := hτ2.differentiableAt (by norm_num)
  have hAy : fderiv ℝ tm y₀ = tangentCoordChange I β α x := fderiv_chartTransition hxx hxα
  have hDu : HasDerivAt ux (deriv ux t₀) t₀ := hu.hasDerivAt
  have hA' : HasDerivAt (fun τ => fderiv ℝ tm (ux τ))
      (fderiv ℝ (fderiv ℝ tm) y₀ (deriv ux t₀)) t₀ :=
    hτfd.hasFDerivAt.comp_hasDerivAt t₀ hDu
  -- the chart-`α` readings of the field and of the curve, near `t₀`
  have hVα_eq : chartFieldRep (I := I) c α V =ᶠ[𝓝 t₀] fun τ => fderiv ℝ tm (ux τ) (Vx τ) := by
    filter_upwards [hev] with τ hτ
    have h1 : fderiv ℝ tm (ux τ) = tangentCoordChange I β α (c τ) :=
      fderiv_chartTransition hτ.1 hτ.2
    rw [h1]
    exact (tangentCoordChange_comp
      ⟨⟨mem_extChartAt_source (I := I) (c τ), hτ.1⟩, hτ.2⟩).symm
  have huα_eq : (fun τ => extChartAt I α (c τ)) =ᶠ[𝓝 t₀] fun τ => tm (ux τ) := by
    filter_upwards [hev] with τ hτ
    exact (chartTransition_extChartAt hτ.1).symm
  have huα'0 : HasDerivAt (tm ∘ ux) (fderiv ℝ tm y₀ (deriv ux t₀)) t₀ := by
    have hfd : HasFDerivAt tm (fderiv ℝ tm y₀) (ux t₀) := hτd.hasFDerivAt
    exact hfd.comp_hasDerivAt t₀ hDu
  have huα' : HasDerivAt (fun τ => extChartAt I α (c τ)) (fderiv ℝ tm y₀ (deriv ux t₀)) t₀ :=
    huα'0.congr_of_eventuallyEq huα_eq
  have hVα' : HasDerivAt (chartFieldRep (I := I) c α V)
      (fderiv ℝ (fderiv ℝ tm) y₀ (deriv ux t₀) (Vx t₀)
        + fderiv ℝ tm y₀ (deriv Vx t₀)) t₀ :=
    (hA'.clm_apply hV.hasDerivAt).congr_of_eventuallyEq hVα_eq
  -- the Christoffel transformation law at the foot, contracted with `(u̇, V)`
  have hlaw := tangentCoordChange_chartChristoffelContraction (I := I) g hxx hxα
    (deriv ux t₀) (Vx t₀)
  rw [mixedPartialCoord_def, fderiv_fderiv_apply hτfd] at hlaw
  have htmy₀ : tm y₀ = extChartAt I α x := chartTransition_extChartAt hxx
  -- assemble
  have hfoot : chartFieldRep (I := I) c α V t₀ = tangentCoordChange I β α x (Vx t₀) :=
    (tangentCoordChange_comp ⟨⟨mem_extChartAt_source (I := I) x, hxx⟩, hxα⟩).symm
  have hy0' : ux t₀ = y₀ := rfl
  rw [covariantDerivCoord_def, covariantDerivCoord_def, huα'.deriv, hVα'.deriv, hAy]
  rw [← htm, ← hy₀, hAy, htmy₀] at hlaw
  rw [hy0', map_add, hlaw, hfoot]
  abel

/-- **Math.** Unfolding: the moving-foot derivative `V̇(t)` is literally the
coordinate covariant derivative `covariantDerivCoord` taken in the chart at the
foot `c t`. -/
theorem derivAlongCurve_eq_covariantDerivCoord (g : RiemannianMetric I M) (c : ℝ → M)
    (V : ∀ t, TangentSpace I (c t)) (t : ℝ) :
    derivAlongCurve (I := I) g c V t
      = covariantDerivCoord (I := I) g (c t) (fun τ => extChartAt I (c t) (c τ))
          (chartFieldRep (I := I) c (c t) V) t := by
  rw [derivAlongCurve_def, covariantDerivCoord_def, chartFieldRep_self]
  rfl

/-- **Math.** The tangent coordinate change between two charts whose sources
contain `z` is injective: it is inverted by the reverse coordinate change. -/
theorem tangentCoordChange_eq_zero_iff {β α z : M} (hβ : z ∈ (extChartAt I β).source)
    (hα : z ∈ (extChartAt I α).source) (v : E) :
    tangentCoordChange I β α z v = 0 ↔ v = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, map_zero]⟩
  have hcomp := tangentCoordChange_comp (I := I) (w := β) (x := α) (y := β) (z := z) (v := v)
    ⟨⟨hβ, hα⟩, hβ⟩
  rw [h, map_zero, tangentCoordChange_self hβ] at hcomp
  exact hcomp.symm

/-- **Math.** Petersen §6.1: `V̇(t)` computed from **any fixed chart** `α` whose
source contains `c t`, rather than from the moving-foot chart — the working form
of chart-independence. -/
theorem derivAlongCurve_eq_transfer (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) :
    derivAlongCurve (I := I) g c V t
      = tangentCoordChange I α (c t) (c t)
          (covariantDerivCoord (I := I) g α (fun τ => extChartAt I α (c τ))
            (chartFieldRep (I := I) c α V) t) := by
  rw [derivAlongCurve_eq_covariantDerivCoord]
  exact (covariantDerivCoord_transfer (I := I) g α (c t) hc hsrc
    (mem_chart_source H (c t)) hu hV).symm

/-- **Math.** Petersen §6.1: `V` is parallel at `t` iff its chart-`α` reading
solves the parallel-transport equation at `t`, for any chart `α` around `c t`.
This is what turns `def:pet-ch6-parallel-field` into a linear ODE. -/
theorem derivAlongCurve_eq_zero_iff (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) :
    derivAlongCurve (I := I) g c V t = 0 ↔
      covariantDerivCoord (I := I) g α (fun τ => extChartAt I α (c τ))
        (chartFieldRep (I := I) c α V) t = 0 := by
  rw [derivAlongCurve_eq_transfer (I := I) g α hc hsrc hu hV]
  exact tangentCoordChange_eq_zero_iff (I := I) (by rwa [extChartAt_source])
    (mem_extChartAt_source (I := I) (c t)) _

/-- **Math.** Petersen §6.1 (p. 252): the chart-`α` reading of a field parallel
along `c` solves the **first-order linear parallel-transport system**
`V̇ = −Γ_α(u̇, V)(u)` — Petersen's `V̇ʲ(t) = −Σᵢ Vⁱ(t) αᵢʲ(t)`. -/
theorem hasDerivAt_chartFieldRep_of_parallel (g : RiemannianMetric I M) {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t)
    (hp : derivAlongCurve (I := I) g c V t = 0) :
    HasDerivAt (chartFieldRep (I := I) c α V)
      (-Geodesic.chartChristoffelContraction (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t)
        (chartFieldRep (I := I) c α V t) (extChartAt I α (c t))) t := by
  have h0 := (derivAlongCurve_eq_zero_iff (I := I) g α hc hsrc hu hV).mp hp
  rw [covariantDerivCoord_def] at h0
  have hd : deriv (chartFieldRep (I := I) c α V) t
      = -Geodesic.chartChristoffelContraction (I := I) g α
          (deriv (fun τ => extChartAt I α (c τ)) t)
          (chartFieldRep (I := I) c α V t) (extChartAt I α (c t)) :=
    eq_neg_iff_add_eq_zero.mpr h0
  rw [← hd]
  exact hV.hasDerivAt

end Transfer

section ExistenceUniqueness

variable [I.Boundaryless]

/-- **Math.** Petersen §6.1 (p. 252), Theorem 6.1.3, **uniqueness half**: two
fields parallel along `c` on `Ioo a b` that agree at one time `t₀` agree
throughout.  This is uniqueness for the linear system `V̇ = −Γ_α(u̇, V)(u)`, run
forward and backward from `t₀` by Grönwall
(`LinearODE.IsSolOn.eqOn_of_left`/`_of_right`).

The differentiability hypotheses `hVd`, `hWd` are not removable: `derivAlongCurve`
is defined through `deriv`, which is junk `0` off the differentiability locus, so
`V̇ ≡ 0` alone does not force regularity.  Petersen leaves the smoothness of the
fields implicit. -/
theorem isParallelAlong_eqOn (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} (α : M) {a b t₀ : ℝ} {K : NNReal}
    (ht₀ : t₀ ∈ Ioo a b)
    (hc : ∀ t ∈ Ioo a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Ioo a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hK : ∀ t ∈ Icc a b, ‖chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))‖₊ ≤ K)
    (hVd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t)
    (hWd : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (chartFieldRep (I := I) c α W) t)
    (hVp : ∀ t ∈ Ioo a b, derivAlongCurve (I := I) g c V t = 0)
    (hWp : ∀ t ∈ Ioo a b, derivAlongCurve (I := I) g c W t = 0)
    (h0 : V t₀ = W t₀) :
    ∀ t ∈ Ioo a b, V t = W t := by
  classical
  set u : ℝ → E := fun τ => extChartAt I α (c τ) with hu_def
  set A : ℝ → E →L[ℝ] E :=
    fun t => -chartChristoffelContractionRight (I := I) g α (deriv u t) (u t) with hA
  have hKA : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  have hsol : ∀ (X : ∀ t, TangentSpace I (c t)),
      (∀ t ∈ Ioo a b, DifferentiableAt ℝ (chartFieldRep (I := I) c α X) t) →
      (∀ t ∈ Ioo a b, derivAlongCurve (I := I) g c X t = 0) →
      ∀ t ∈ Ioo a b, HasDerivAt (chartFieldRep (I := I) c α X)
        (A t (chartFieldRep (I := I) c α X t)) t := by
    intro X hXd hXp t ht
    have h := hasDerivAt_chartFieldRep_of_parallel (I := I) g α (hc t ht) (hsrc t ht)
      (hu t ht) (hXd t ht) (hXp t ht)
    rwa [show A t (chartFieldRep (I := I) c α X t)
        = -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (chartFieldRep (I := I) c α X t) (u t) by
      rw [hA]; simp only [ContinuousLinearMap.neg_apply, chartChristoffelContractionRight_apply]]
  have hVs := hsol V hVd hVp
  have hWs := hsol W hWd hWp
  have hrep0 : chartFieldRep (I := I) c α V t₀ = chartFieldRep (I := I) c α W t₀ := by
    simp only [chartFieldRep_apply, h0]
  intro t ht
  have hkey : chartFieldRep (I := I) c α V t = chartFieldRep (I := I) c α W t := by
    rcases le_total t₀ t with h | h
    · have hsub : Icc t₀ t ⊆ Ioo a b :=
        fun s hs => ⟨lt_of_lt_of_le ht₀.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
      have hsubI : Icc t₀ t ⊆ Icc a b :=
        fun s hs => ⟨le_trans ht₀.1.le hs.1, le_trans hs.2 ht.2.le⟩
      exact LinearODE.IsSolOn.eqOn_of_left (fun s hs => hKA s (hsubI hs))
        (fun s hs => (hVs s (hsub hs)).hasDerivWithinAt)
        (fun s hs => (hWs s (hsub hs)).hasDerivWithinAt) hrep0 ⟨h, le_rfl⟩
    · have hsub : Icc t t₀ ⊆ Ioo a b :=
        fun s hs => ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 ht₀.2⟩
      have hsubI : Icc t t₀ ⊆ Icc a b :=
        fun s hs => ⟨le_trans ht.1.le hs.1, le_trans hs.2 ht₀.2.le⟩
      exact LinearODE.IsSolOn.eqOn_of_right (fun s hs => hKA s (hsubI hs))
        (fun s hs => (hVs s (hsub hs)).hasDerivWithinAt)
        (fun s hs => (hWs s (hsub hs)).hasDerivWithinAt) hrep0 ⟨le_rfl, h⟩
  have hzero : tangentCoordChange I (c t) α (c t) ((V t : E) - (W t : E)) = 0 := by
    rw [map_sub]
    simp only [chartFieldRep_apply] at hkey
    rw [hkey, sub_self]
  have hsub0 := (tangentCoordChange_eq_zero_iff (I := I)
    (mem_extChartAt_source (I := I) (c t))
    (by rw [extChartAt_source]; exact hsrc t ht) _).mp hzero
  exact sub_eq_zero.mp hsub0

/-- **Math.** Petersen §6.1 (pp. 252–253), Theorem 6.1.3, **existence half**: for
`t₀ ∈ (a,b)` and `v ∈ T_{c t₀}M` there is a field parallel along `c` on `Ioo a b`
with `V t₀ = v`.

Petersen's argument: parallelism is a first-order *linear* system, so a solution
exists on the whole interval (in contrast to the nonlinear geodesic equation).
We solve in the chart at `α` with the vendored linear-ODE engine and read the
solution back to the feet of `c`.  Because the engine prescribes the value at the
*left endpoint*, we pull `v` back to time `a` through the parallel-transport flow
`parallelTransport`, which is available precisely because that flow is a linear
**isomorphism** (injective endomorphism of a finite-dimensional space).

`hcont` and `hK` are the vendored engine's hypotheses on the ODE coefficient over
the compact `Icc a b`; both hold automatically for a `C¹` curve by compactness. -/
theorem exists_isParallelAlong (g : RiemannianMetric I M) {c : ℝ → M} (α : M)
    {a b t₀ : ℝ} {K : NNReal} (ht₀ : t₀ ∈ Ioo a b)
    (hc : ∀ t ∈ Ioo a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Ioo a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hcont : ContinuousOn (fun t => chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))) (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))‖₊ ≤ K)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      (∀ t ∈ Ioo a b, DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) ∧
      (∀ t ∈ Ioo a b, derivAlongCurve (I := I) g c V t = 0) ∧ V t₀ = v := by
  classical
  set u : ℝ → E := fun τ => extChartAt I α (c τ) with hu_def
  have hab : a ≤ b := le_of_lt (lt_trans ht₀.1 ht₀.2)
  have hat₀ : a ≤ t₀ := ht₀.1.le
  have ht₀b : t₀ ≤ b := ht₀.2.le
  have hsubL : Icc a t₀ ⊆ Icc a b := Icc_subset_Icc le_rfl ht₀b
  have hcontL := hcont.mono hsubL
  have hKL : ∀ t ∈ Icc a t₀, ‖chartChristoffelContractionRight (I := I) g α
      (deriv u t) (u t)‖₊ ≤ K := fun t ht => hK t (hsubL ht)
  set v₀ : E := tangentCoordChange I (c t₀) α (c t₀) v with hv₀
  set P := parallelTransport (I := I) g α u hat₀ hcontL hKL with hP
  set w : E := P.symm v₀ with hw
  obtain ⟨Vα, hVa, -, hVsol⟩ := exists_parallelTransport_spec (I := I) g α u hab hcont hK w
  obtain ⟨VL, hVLa, hVLt₀, hVLsol⟩ :=
    exists_parallelTransport_spec (I := I) g α u hat₀ hcontL hKL w
  have hPw : P w = v₀ := by rw [hw]; exact P.apply_symm_apply v₀
  have heq : EqOn Vα VL (Icc a t₀) :=
    isParallelSol_eqOn_Icc (I := I) g α u hKL
      (fun t ht => (hVsol t (hsubL ht)).mono hsubL) hVLsol (by rw [hVa, hVLa])
  have hVαt₀ : Vα t₀ = v₀ := by
    rw [heq ⟨hat₀, le_rfl⟩, hVLt₀, ← hP, hPw]
  -- read the chart solution back to the feet of `c`
  set Vf : ∀ t, TangentSpace I (c t) :=
    fun t => tangentCoordChange I α (c t) (c t) (Vα t) with hVf
  have hrep : ∀ t ∈ Ioo a b, chartFieldRep (I := I) c α Vf t = Vα t := by
    intro t ht
    have hα' : c t ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hsrc t ht
    have hcc : c t ∈ (extChartAt I (c t)).source := mem_extChartAt_source (I := I) (c t)
    show tangentCoordChange I (c t) α (c t) (tangentCoordChange I α (c t) (c t) (Vα t)) = Vα t
    rw [tangentCoordChange_comp (I := I) (w := α) (x := c t) (y := α) (z := c t)
      ⟨⟨hα', hcc⟩, hα'⟩]
    exact tangentCoordChange_self hα'
  have hev : ∀ t ∈ Ioo a b, chartFieldRep (I := I) c α Vf =ᶠ[𝓝 t] Vα := fun t ht => by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs using hrep s hs
  have hVαd : ∀ t ∈ Ioo a b, HasDerivAt Vα
      (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (Vα t) (u t)) t :=
    fun t ht => (hVsol t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  have hFd : ∀ t ∈ Ioo a b, HasDerivAt (chartFieldRep (I := I) c α Vf)
      (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (Vα t) (u t)) t :=
    fun t ht => (hVαd t ht).congr_of_eventuallyEq (hev t ht)
  refine ⟨Vf, fun t ht => (hFd t ht).differentiableAt, fun t ht => ?_, ?_⟩
  · rw [derivAlongCurve_eq_zero_iff (I := I) g α (hc t ht) (hsrc t ht) (hu t ht)
      ((hFd t ht).differentiableAt), covariantDerivCoord_def, (hFd t ht).deriv, hrep t ht]
    abel
  · show tangentCoordChange I α (c t₀) (c t₀) (Vα t₀) = v
    rw [hVαt₀, hv₀,
      tangentCoordChange_comp (I := I) (w := c t₀) (x := α) (y := c t₀) (z := c t₀)
        ⟨⟨mem_extChartAt_source (I := I) (c t₀),
          by rw [extChartAt_source]; exact hsrc t₀ ht₀⟩,
         mem_extChartAt_source (I := I) (c t₀)⟩]
    exact tangentCoordChange_self (mem_extChartAt_source (I := I) (c t₀))

/-- **Math.** Petersen §6.1 (p. 252), `thm:pet-ch6-parallel-field-existence-uniqueness`
— **Theorem 6.1.3**: if `t₀ ∈ I` and `v ∈ T_{c(t₀)}M`, there is a unique parallel
field `V` along `c`, defined on all of `I`, with `V(t₀) = v`.

Here `I` is the open interval `Ioo a b` and the relevant piece of `c` is assumed
to lie in the source of a single chart `α`; see the module docstring for why both
restrictions are present and what removing them needs.  Uniqueness is stated as
`EqOn` on `Ioo a b` rather than as `∃!` because a field along `c` is unconstrained
off the interval. -/
theorem parallelField_existence_uniqueness (g : RiemannianMetric I M) {c : ℝ → M} (α : M)
    {a b t₀ : ℝ} {K : NNReal} (ht₀ : t₀ ∈ Ioo a b)
    (hc : ∀ t ∈ Ioo a b, ContinuousAt c t)
    (hsrc : ∀ t ∈ Ioo a b, c t ∈ (chartAt H α).source)
    (hu : ∀ t ∈ Ioo a b, DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hcont : ContinuousOn (fun t => chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))) (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖chartChristoffelContractionRight (I := I) g α
        (deriv (fun τ => extChartAt I α (c τ)) t) (extChartAt I α (c t))‖₊ ≤ K)
    (v : TangentSpace I (c t₀)) :
    ∃ V : ∀ t, TangentSpace I (c t),
      (∀ t ∈ Ioo a b, DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t) ∧
      (∀ t ∈ Ioo a b, derivAlongCurve (I := I) g c V t = 0) ∧
      V t₀ = v ∧
      ∀ W : ∀ t, TangentSpace I (c t),
        (∀ t ∈ Ioo a b, DifferentiableAt ℝ (chartFieldRep (I := I) c α W) t) →
        (∀ t ∈ Ioo a b, derivAlongCurve (I := I) g c W t = 0) → W t₀ = v →
        ∀ t ∈ Ioo a b, W t = V t := by
  obtain ⟨V, hVd, hVp, hVt₀⟩ := exists_isParallelAlong (I := I) g α ht₀ hc hsrc hu hcont hK v
  exact ⟨V, hVd, hVp, hVt₀, fun W hWd hWp hWt₀ =>
    isParallelAlong_eqOn (I := I) g α ht₀ hc hsrc hu hK hWd hVd hWp hVp (by rw [hWt₀, hVt₀])⟩

end ExistenceUniqueness

section ProductRule

variable [I.Boundaryless]

/-- **Math.** The chart-`α` reading is inverted by the reverse coordinate change. -/
theorem tangentCoordChange_chartFieldRep (c : ℝ → M) (α : M)
    (V : ∀ t, TangentSpace I (c t)) {τ : ℝ} (h : c τ ∈ (extChartAt I α).source) :
    tangentCoordChange I α (c τ) (c τ) (chartFieldRep (I := I) c α V τ) = V τ := by
  rw [chartFieldRep_apply, tangentCoordChange_comp (I := I) (w := c τ) (x := α) (y := c τ)
    (z := c τ) ⟨⟨mem_extChartAt_source (I := I) (c τ), h⟩, mem_extChartAt_source (I := I) (c τ)⟩]
  exact tangentCoordChange_self (mem_extChartAt_source (I := I) (c τ))

/-- **Math.** Petersen §6.1 (p. 249): the **metric product rule** along a curve,
`d/dt g(V, W) = g(V̇, W) + g(V, Ẇ)` — the clause of
`def:pet-ch6-vector-field-along-curve` expressing metric compatibility of the
Levi-Civita connection along `c`.  Lifted from the chart-level product rule
`hasDerivAt_chartMetricInner_along` (§2 of the vendored do Carmo layer) through
the metric bridge `chartMetricInner_eq_inner` and `derivAlongCurve_eq_transfer`.
`hG` is the differentiability of the chart metric coefficients at the foot,
automatic for a metric smooth on the chart domain. -/
theorem hasDerivAt_inner_along (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c α W) t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α (c t))) :
    HasDerivAt (fun τ => g.inner (c τ) (V τ) (W τ))
      (g.inner (c t) (derivAlongCurve (I := I) g c V t) (W t)
        + g.inner (c t) (V t) (derivAlongCurve (I := I) g c W t)) t := by
  classical
  have hsrc' : c t ∈ (extChartAt I α).source := by rwa [extChartAt_source]
  have hev : ∀ᶠ τ in 𝓝 t, c τ ∈ (extChartAt I α).source :=
    hc.eventually_mem ((isOpen_extChartAt_source (I := I) α).mem_nhds hsrc')
  -- the intrinsic pairing is the chart Gram pairing of the chart readings
  have heq : (fun τ => g.inner (c τ) (V τ) (W τ)) =ᶠ[𝓝 t]
      fun τ => chartMetricInner (I := I) g α (extChartAt I α (c τ))
        (chartFieldRep (I := I) c α V τ) (chartFieldRep (I := I) c α W τ) := by
    filter_upwards [hev] with τ hτ
    rw [chartMetricInner_eq_inner (I := I) g hτ, tangentCoordChange_chartFieldRep (I := I) c α V hτ,
      tangentCoordChange_chartFieldRep (I := I) c α W hτ]
  have hbase : (extChartAt I α).symm (extChartAt I α (c t))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [(extChartAt I α).left_inv hsrc', trivializationAt_baseSet_eq_chartAt_source]
    exact hsrc
  have h := hasDerivAt_chartMetricInner_along (I := I) g α (fun τ => extChartAt I α (c τ))
    (chartFieldRep (I := I) c α V) (chartFieldRep (I := I) c α W) hu hV hW hG hbase
  rw [chartMetricInner_eq_inner (I := I) g hsrc', chartMetricInner_eq_inner (I := I) g hsrc',
    tangentCoordChange_chartFieldRep (I := I) c α V hsrc',
    tangentCoordChange_chartFieldRep (I := I) c α W hsrc',
    ← derivAlongCurve_eq_transfer (I := I) g α hc hsrc hu hV,
    ← derivAlongCurve_eq_transfer (I := I) g α hc hsrc hu hW] at h
  exact h.congr_of_eventuallyEq heq

/-- **Math.** Petersen §6.1 (p. 252): **parallel fields neither change length nor
relative angle** — if `V` and `W` are parallel along `c` then `g(V, W)` is
constant, generalizing parallel translation in Euclidean space. -/
theorem hasDerivAt_inner_eq_zero_of_isParallelAlong (g : RiemannianMetric I M) {c : ℝ → M}
    {V W : ∀ t, TangentSpace I (c t)} (α : M) {t : ℝ}
    (hc : ContinuousAt c t)
    (hsrc : c t ∈ (chartAt H α).source)
    (hu : DifferentiableAt ℝ (fun τ => extChartAt I α (c τ)) t)
    (hV : DifferentiableAt ℝ (chartFieldRep (I := I) c α V) t)
    (hW : DifferentiableAt ℝ (chartFieldRep (I := I) c α W) t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α (c t)))
    (hVp : derivAlongCurve (I := I) g c V t = 0)
    (hWp : derivAlongCurve (I := I) g c W t = 0) :
    HasDerivAt (fun τ => g.inner (c τ) (V τ) (W τ)) 0 t := by
  have h := hasDerivAt_inner_along (I := I) g α hc hsrc hu hV hW hG
  simpa only [hVp, hWp, map_zero, ContinuousLinearMap.zero_apply, zero_add] using h

end ProductRule

end PetersenLib

end

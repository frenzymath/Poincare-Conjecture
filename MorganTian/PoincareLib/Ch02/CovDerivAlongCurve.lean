import OpenGALib.Riemannian.Geodesic.CovariantDerivative
import OpenGALib.Riemannian.Geodesic.InitialVelocity
import OpenGALib.Riemannian.Connection.ChartChristoffelSmooth
import OpenGALib.Riemannian.Manifold.DoCarmoCh4
import OpenGALib.Riemannian.Manifold.DoCarmoCh6Locality
import PoincareLib.Ch01.CurvatureFrameBridge

/-!
# Morgan–Tian Ch. 2 — covariant differentiation along curves, manifold level

Blueprint `lem:covariant-derivative-along-maps` (curve case `m = 1`): the
covariant derivative `DW/dt` of a vector field `W` along a curve
`γ : ℝ → M`, defined intrinsically in the **moving-foot chart** — at each
base time `t₀` the coordinate formula `DW/dt = V̇ + Γ(u̇, V)(u)` is read in
the canonical chart centred at `γ t₀` (the same convention as the geodesic
equation `HasGeodesicEquationAt`). This file provides:

* `chartFieldCoord x γ W` — the chart-`x` coordinate representation of a
  field `W` along `γ` (via the tangent-bundle trivialization at `x`);
* `HasCovDerivAlongAt g γ W Dw t₀` — the moving-foot covariant-derivative
  predicate: `Dw ∈ T_{γ t₀} M` is the value of `DW/dt` at `t₀`;
* uniqueness of the value, `ℝ`-linearity (`add`, `smul`, `sub`, `neg`), and
  the Leibniz rule `smul_fun` — blueprint part (1), algebraic clauses;
* `metricInner_eq_chartMetricInner` — the metric read through the chart
  trivialization is the chart Gram inner product;
* `HasCovDerivAlongAt.hasDerivAt_metricInner` — the metric product rule
  `d/dt ⟨W₁, W₂⟩ = ⟨DW₁/dt, W₂⟩ + ⟨W₁, DW₂/dt⟩` — blueprint part (2);
* `IsParallelAlong` and its consequences: parallel fields have constant
  inner products, and two parallel fields agreeing at one time agree
  everywhere — blueprint part (5).

The chart-level engine is OpenGALib's
`Riemannian.covariantDerivCoord` / `hasDerivAt_chartMetricInner_along`
(do Carmo Ch. 2 §2–§3); this file lifts it to fields along curves in `M`
anchored at the moving foot, which is the form consumed by the
parallel-gradient flow arguments of the splitting theorem
(`lem:parallel-gradient-flow`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:covariant-derivative-along-maps`).
-/

open Set Filter Riemannian Riemannian.Geodesic
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless]

/-! ### Chart coordinates of a field along a curve -/

/-- **Math.** The chart-`x` **coordinate representation** of a vector field `W`
along the curve `γ`: at each time `t` the tangent vector `W t ∈ T_{γ t} M` is
read through the tangent-bundle trivialization at `x`. Meaningful for
`γ t ∈ (chartAt H x).source`; junk off it. -/
def chartFieldCoord (x : M) (γ : ℝ → M) (W : ∀ t, TangentSpace I (γ t)) : ℝ → E :=
  fun t => chartFiberCoord (I := I) x ⟨γ t, W t⟩

@[simp] theorem chartFieldCoord_def (x : M) (γ : ℝ → M)
    (W : ∀ t, TangentSpace I (γ t)) (t : ℝ) :
    chartFieldCoord (I := I) x γ W t = chartFiberCoord (I := I) x ⟨γ t, W t⟩ := rfl

/-- **Math.** At the anchor time, the chart coordinates of the field are the
field itself: the trivialization at `γ t₀` is the identity on the fibre over
`γ t₀`. -/
theorem chartFieldCoord_self (γ : ℝ → M) (W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ) :
    chartFieldCoord (I := I) (γ t₀) γ W t₀ = W t₀ :=
  chartFiberCoord_mk (I := I) (γ t₀) (W t₀)

/-- **Math.** The chart fibre coordinate is additive on each fibre over the base
set: the trivialization is fibrewise linear. -/
theorem chartFiberCoord_add (x : M) {b : M} (hb : b ∈ (chartAt H x).source)
    (v w : TangentSpace I b) :
    chartFiberCoord (I := I) x ⟨b, v + w⟩
      = chartFiberCoord (I := I) x ⟨b, v⟩ + chartFiberCoord (I := I) x ⟨b, w⟩ := by
  have hb' : b ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have h := fun (y : TangentSpace I b) =>
    congrFun (Bundle.Trivialization.continuousLinearEquivAt_apply ℝ
      (trivializationAt E (TangentSpace I) x) b hb') y
  simp only [chartFiberCoord_def, ← h, map_add]

/-- **Math.** The chart fibre coordinate is homogeneous on each fibre over the
base set. -/
theorem chartFiberCoord_smul (x : M) {b : M} (hb : b ∈ (chartAt H x).source)
    (c : ℝ) (v : TangentSpace I b) :
    chartFiberCoord (I := I) x ⟨b, c • v⟩ = c • chartFiberCoord (I := I) x ⟨b, v⟩ := by
  have hb' : b ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  have h := fun (y : TangentSpace I b) =>
    congrFun (Bundle.Trivialization.continuousLinearEquivAt_apply ℝ
      (trivializationAt E (TangentSpace I) x) b hb') y
  simp only [chartFiberCoord_def, ← h, map_smul]

/-- **Math.** The Christoffel contraction is additive in its field slot, here
with the field slot presented as a tangent vector (the additions on
`TangentSpace I b` are definitionally those of `E`, but carry different
instance terms, so the `E`-typed lemma does not `rw`/`simp`-match goals
produced from tangent-space sums). -/
theorem chartChristoffelContraction_add_right_tangent (g : RiemannianMetric I M)
    (x : M) {b : M} (v : E) (w₁ w₂ : TangentSpace I b) (y : E) :
    chartChristoffelContraction (I := I) g x v ((w₁ + w₂ : TangentSpace I b)) y
      = chartChristoffelContraction (I := I) g x v w₁ y
        + chartChristoffelContraction (I := I) g x v w₂ y :=
  chartChristoffelContraction_add_right (I := I) g x v w₁ w₂ y

/-- **Math.** The Christoffel contraction is homogeneous in its field slot,
here with the field slot presented as a tangent vector. -/
theorem chartChristoffelContraction_smul_right_tangent (g : RiemannianMetric I M)
    (x : M) {b : M} (v : E) (c : ℝ) (w : TangentSpace I b) (y : E) :
    chartChristoffelContraction (I := I) g x v ((c • w : TangentSpace I b)) y
      = c • chartChristoffelContraction (I := I) g x v w y :=
  chartChristoffelContraction_smul_right (I := I) g x v c w y

/-- **Math.** Addition on a tangent space is the model-space addition. -/
theorem tangentSpace_add_eq {b : M} (v w : TangentSpace I b) :
    (v + w : TangentSpace I b) = ((v : E) + (w : E) : E) := rfl

/-- **Math.** Scalar action on a tangent space is the model-space action. -/
theorem tangentSpace_smul_eq {b : M} (c : ℝ) (w : TangentSpace I b) :
    (c • w : TangentSpace I b) = (c • (w : E) : E) := rfl

/-! ### The moving-foot covariant derivative along a curve -/

/-- **Math.** Blueprint `lem:covariant-derivative-along-maps`, curve case: the
field `W` along `γ` has **covariant derivative** `Dw` at time `t₀` when, in
the canonical chart at the moving foot `γ t₀`,

* the curve stays in the chart source near `t₀`,
* the chart curve `u = φ_{γ t₀} ∘ γ` has some velocity `v` at `t₀`, and
* the coordinate field `V = chartFieldCoord (γ t₀) γ W` satisfies the
  coordinate covariant-derivative formula `V̇(t₀) + Γ(v, W t₀)(u t₀) = Dw`,
  i.e. `DW/dt = V̇ + Γ(u̇, V)(u)` evaluated at `t₀`.

The value `Dw : E` is the tangent vector `DW/dt(t₀) ∈ T_{γ t₀} M` read in the
moving-foot chart (the tangent space at the foot is definitionally the model
space, and the trivialization at the foot is the identity on its own fibre).
This is the manifold-level, chart-independent notion: the anchor chart is
determined by the foot point itself (same convention as
`HasGeodesicEquationAt`). -/
def HasCovDerivAlongAt (g : RiemannianMetric I M) (γ : ℝ → M)
    (W : ∀ t, TangentSpace I (γ t)) (t₀ : ℝ) (Dw : E) : Prop :=
  (∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source) ∧
  ∃ v dV : E,
    HasDerivAt (chartLocalCurve (I := I) γ t₀) v t₀ ∧
    HasDerivAt (chartFieldCoord (I := I) (γ t₀) γ W) dV t₀ ∧
    dV + chartChristoffelContraction (I := I) g (γ t₀) v (W t₀)
      (extChartAt I (γ t₀) (γ t₀)) = Dw

variable {g : RiemannianMetric I M} {γ : ℝ → M} {t₀ : ℝ}

/-- **Math.** The curve stays in the moving-foot chart source near the base
time (definitional projection). -/
theorem HasCovDerivAlongAt.eventually_mem_source {W : ∀ t, TangentSpace I (γ t)}
    {Dw : E} (h : HasCovDerivAlongAt (I := I) g γ W t₀ Dw) :
    ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source := h.1

/-- **Math.** The covariant derivative value is unique: the chart velocity and
the coordinate-field derivative are unique, hence so is
`DW/dt = V̇ + Γ(u̇, W)(u)`. -/
theorem HasCovDerivAlongAt.unique {W : ∀ t, TangentSpace I (γ t)}
    {D₁ D₂ : E}
    (h₁ : HasCovDerivAlongAt (I := I) g γ W t₀ D₁)
    (h₂ : HasCovDerivAlongAt (I := I) g γ W t₀ D₂) : D₁ = D₂ := by
  obtain ⟨-, v₁, dV₁, hv₁, hdV₁, hEq₁⟩ := h₁
  obtain ⟨-, v₂, dV₂, hv₂, hdV₂, hEq₂⟩ := h₂
  rw [← hEq₁, ← hEq₂, hv₁.unique hv₂, hdV₁.unique hdV₂]

/-- **Math.** Blueprint part (1), additivity: `D(W₁ + W₂)/dt = DW₁/dt + DW₂/dt`. -/
theorem HasCovDerivAlongAt.add {W₁ W₂ : ∀ t, TangentSpace I (γ t)}
    {D₁ D₂ : E}
    (h₁ : HasCovDerivAlongAt (I := I) g γ W₁ t₀ D₁)
    (h₂ : HasCovDerivAlongAt (I := I) g γ W₂ t₀ D₂) :
    HasCovDerivAlongAt (I := I) g γ (fun t => W₁ t + W₂ t) t₀ (D₁ + D₂) := by
  obtain ⟨hmem, v₁, dV₁, hv₁, hdV₁, hEq₁⟩ := h₁
  obtain ⟨-, v₂, dV₂, hv₂, hdV₂, hEq₂⟩ := h₂
  refine ⟨hmem, v₁, dV₁ + dV₂, hv₁, ?_, ?_⟩
  · refine (hdV₁.add hdV₂).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with s hs
    exact chartFiberCoord_add (I := I) (γ t₀) hs (W₁ s) (W₂ s)
  · have hv : v₂ = v₁ := hv₂.unique hv₁
    subst hv
    simp only [chartChristoffelContraction_add_right_tangent, ← hEq₁, ← hEq₂]
    abel

/-- **Math.** Blueprint part (1), homogeneity: `D(c • W)/dt = c • DW/dt`. -/
theorem HasCovDerivAlongAt.const_smul {W : ∀ t, TangentSpace I (γ t)}
    {Dw : E} (c : ℝ)
    (h : HasCovDerivAlongAt (I := I) g γ W t₀ Dw) :
    HasCovDerivAlongAt (I := I) g γ (fun t => c • W t) t₀ (c • Dw) := by
  obtain ⟨hmem, v, dV, hv, hdV, hEq⟩ := h
  refine ⟨hmem, v, c • dV, hv, ?_, ?_⟩
  · refine (hdV.const_smul c).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with s hs
    exact chartFiberCoord_smul (I := I) (γ t₀) hs c (W s)
  · simp only [chartChristoffelContraction_smul_right_tangent, ← hEq]
    exact (smul_add c dV _).symm

/-- **Math.** Negation: `D(−W)/dt = −DW/dt`. -/
theorem HasCovDerivAlongAt.neg {W : ∀ t, TangentSpace I (γ t)}
    {Dw : E}
    (h : HasCovDerivAlongAt (I := I) g γ W t₀ Dw) :
    HasCovDerivAlongAt (I := I) g γ (fun t => -W t) t₀ (-Dw) := by
  have := h.const_smul (-1)
  simpa [neg_smul, one_smul] using this

/-- **Math.** Subtraction: `D(W₁ − W₂)/dt = DW₁/dt − DW₂/dt`. -/
theorem HasCovDerivAlongAt.sub {W₁ W₂ : ∀ t, TangentSpace I (γ t)}
    {D₁ D₂ : E}
    (h₁ : HasCovDerivAlongAt (I := I) g γ W₁ t₀ D₁)
    (h₂ : HasCovDerivAlongAt (I := I) g γ W₂ t₀ D₂) :
    HasCovDerivAlongAt (I := I) g γ (fun t => W₁ t - W₂ t) t₀ (D₁ - D₂) := by
  have := h₁.add h₂.neg
  simpa [sub_eq_add_neg] using this

/-- **Math.** Blueprint part (1), the **Leibniz rule**:
`D(f W)/dt = f'(t₀) W(t₀) + f(t₀) DW/dt` for a scalar `f : ℝ → ℝ`
differentiable at `t₀` (the value `W t₀` appearing in the derivative is
written in its chart-coordinate form `chartFieldCoord (γ t₀) γ W t₀`, which
equals `W t₀` by `chartFieldCoord_self`). -/
theorem HasCovDerivAlongAt.smul_fun {W : ∀ t, TangentSpace I (γ t)}
    {Dw : E} {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' t₀)
    (h : HasCovDerivAlongAt (I := I) g γ W t₀ Dw) :
    HasCovDerivAlongAt (I := I) g γ (fun t => f t • W t) t₀
      (f' • chartFieldCoord (I := I) (γ t₀) γ W t₀ + f t₀ • Dw) := by
  obtain ⟨hmem, v, dV, hv, hdV, hEq⟩ := h
  refine ⟨hmem, v, f t₀ • dV + f' • chartFieldCoord (I := I) (γ t₀) γ W t₀, hv, ?_, ?_⟩
  · refine (hf.smul hdV).congr_of_eventuallyEq ?_
    filter_upwards [hmem] with s hs
    exact chartFiberCoord_smul (I := I) (γ t₀) hs (f s) (W s)
  · simp only [chartChristoffelContraction_smul_right_tangent, ← hEq, smul_add]
    abel

/-! ### The metric through the chart trivialization -/

/-- **Math.** Every tangent vector at a point of the chart source decomposes in
the chart frame, with coefficients the chart-basis coordinates of its fibre
coordinate: `v = ∑ i, (φ v)^i ∂_i|_b` where `φ` is the trivialization at `x`. -/
theorem sum_chartCoord_smul_chartBasisVecFiber (x : M) {b : M}
    (hb : b ∈ (chartAt H x).source) (v : TangentSpace I b) :
    ∑ i, Geodesic.chartCoord (E := E) i (chartFiberCoord (I := I) x ⟨b, v⟩)
        • Tensor.chartBasisVecFiber (I := I) x i b = v := by
  have hb' : b ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rwa [trivializationAt_baseSet_eq_chartAt_source]
  set φ := (trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ b hb' with hφ
  apply φ.injective
  rw [map_sum]
  have hframe : ∀ i, φ (Tensor.chartBasisVecFiber (I := I) x i b)
      = (Module.finBasis ℝ E) i := by
    intro i
    rw [Bundle.Trivialization.continuousLinearEquivAt_apply]
    exact Tensor.trivializationAt_chartBasisVec_snd (I := I) x i hb'
  have hv : φ v = chartFiberCoord (I := I) x ⟨b, v⟩ := by
    rw [Bundle.Trivialization.continuousLinearEquivAt_apply]
    rfl
  simp only [map_smul, hframe, hv]
  exact (Module.finBasis ℝ E).sum_repr (chartFiberCoord (I := I) x ⟨b, v⟩)

/-- **Math.** Bilinear expansion of the metric inner product over two finite
linear combinations of tangent vectors. -/
theorem metricInner_sum_smul_sum_smul (g : RiemannianMetric I M) (b : M)
    (a c : Fin (Module.finrank ℝ E) → ℝ)
    (v w : Fin (Module.finrank ℝ E) → TangentSpace I b) :
    g.metricInner b (∑ i, a i • v i) (∑ j, c j • w j)
      = ∑ i, ∑ j, a i * c j * g.metricInner b (v i) (w j) := by
  simp only [RiemannianMetric.metricInner_apply, map_sum, map_smul,
    ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Math.** **The metric through the chart trivialization**: for `b` in the
chart source at `x`, the inner product of two tangent vectors at `b` is the
chart Gram inner product of their fibre coordinates at the chart image of
`b`. This is the bridge between the manifold-level metric and the
coordinate-level `chartMetricInner` used by the covariant-derivative
product rule. -/
theorem metricInner_eq_chartMetricInner (g : RiemannianMetric I M) (x : M) {b : M}
    (hb : b ∈ (chartAt H x).source) (v w : TangentSpace I b) :
    g.metricInner b v w
      = chartMetricInner (I := I) g x (extChartAt I x b)
          (chartFiberCoord (I := I) x ⟨b, v⟩) (chartFiberCoord (I := I) x ⟨b, w⟩) := by
  conv_lhs => rw [← sum_chartCoord_smul_chartBasisVecFiber (I := I) x hb v,
    ← sum_chartCoord_smul_chartBasisVecFiber (I := I) x hb w]
  rw [metricInner_sum_smul_sum_smul, chartMetricInner_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hbsrc : b ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hgram : chartGramOnE (I := I) g x i j (extChartAt I x b)
      = g.metricInner b (Tensor.chartBasisVecFiber (I := I) x i b)
          (Tensor.chartBasisVecFiber (I := I) x j b) := by
    rw [chartGramOnE_def, (extChartAt I x).left_inv hbsrc]
    rfl
  rw [hgram]
  ring

/-! ### The metric product rule and parallel fields -/

/-- **Math.** Blueprint part (2), the **metric product rule** along a curve:
if `W₁, W₂` have covariant derivatives `D₁, D₂` at `t₀`, then
`t ↦ ⟨W₁(t), W₂(t)⟩` is differentiable at `t₀` with
`d/dt ⟨W₁, W₂⟩ = ⟨DW₁/dt, W₂⟩ + ⟨W₁, DW₂/dt⟩`.
This is metric compatibility of the Levi-Civita connection along curves,
lifted from the chart-level product rule
`hasDerivAt_chartMetricInner_along`. -/
theorem HasCovDerivAlongAt.hasDerivAt_metricInner
    {W₁ W₂ : ∀ t, TangentSpace I (γ t)} {D₁ D₂ : E}
    (h₁ : HasCovDerivAlongAt (I := I) g γ W₁ t₀ D₁)
    (h₂ : HasCovDerivAlongAt (I := I) g γ W₂ t₀ D₂) :
    HasDerivAt (fun t => g.metricInner (γ t) (W₁ t) (W₂ t))
      (g.metricInner (γ t₀) D₁ (W₂ t₀) + g.metricInner (γ t₀) (W₁ t₀) D₂) t₀ := by
  obtain ⟨hmem, v, dV₁, hv, hdV₁, hEq₁⟩ := h₁
  obtain ⟨-, v₂, dV₂, hv₂, hdV₂, hEq₂⟩ := h₂
  have hvv : v₂ = v := hv₂.unique hv
  subst hvv
  have hself : γ t₀ ∈ (chartAt H (γ t₀)).source := mem_chart_source H (γ t₀)
  have hsrc : γ t₀ ∈ (extChartAt I (γ t₀)).source := by rwa [extChartAt_source]
  have hbase : (extChartAt I (γ t₀)).symm (chartLocalCurve (I := I) γ t₀ t₀)
      ∈ (trivializationAt E (TangentSpace I) (γ t₀)).baseSet := by
    rw [chartLocalCurve_def, (extChartAt I (γ t₀)).left_inv hsrc,
      trivializationAt_baseSet_eq_chartAt_source]
    exact hself
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t₀) i j)
      (chartLocalCurve (I := I) γ t₀ t₀) := by
    intro i j
    have hmemT : chartLocalCurve (I := I) γ t₀ t₀ ∈ (extChartAt I (γ t₀)).target := by
      rw [chartLocalCurve_def]
      exact (extChartAt I (γ t₀)).map_source hsrc
    exact ((chartGramOnE_contDiffOn (I := I) g (γ t₀) i j).contDiffAt
      ((isOpen_extChartAt_target (γ t₀)).mem_nhds hmemT)).differentiableAt (by simp)
  have hcore := hasDerivAt_chartMetricInner_along (I := I) g (γ t₀)
    (chartLocalCurve (I := I) γ t₀)
    (chartFieldCoord (I := I) (γ t₀) γ W₁) (chartFieldCoord (I := I) (γ t₀) γ W₂)
    hv.differentiableAt hdV₁.differentiableAt hdV₂.differentiableAt hG hbase
  -- identify the two covariant-derivative coordinates with `D₁`, `D₂`
  have hcov₁ : covariantDerivCoord (I := I) g (γ t₀) (chartLocalCurve (I := I) γ t₀)
      (chartFieldCoord (I := I) (γ t₀) γ W₁) t₀ = D₁ := by
    rw [covariantDerivCoord_def, hdV₁.deriv, hv.deriv, chartFieldCoord_self]
    exact hEq₁
  have hcov₂ : covariantDerivCoord (I := I) g (γ t₀) (chartLocalCurve (I := I) γ t₀)
      (chartFieldCoord (I := I) (γ t₀) γ W₂) t₀ = D₂ := by
    rw [covariantDerivCoord_def, hdV₂.deriv, hv.deriv, chartFieldCoord_self]
    exact hEq₂
  rw [hcov₁, hcov₂, chartFieldCoord_self (I := I) γ W₁ t₀,
    chartFieldCoord_self (I := I) γ W₂ t₀, chartLocalCurve_def] at hcore
  -- convert the chart Gram values at the anchor to metric inner products
  have ha : chartMetricInner (I := I) g (γ t₀) (extChartAt I (γ t₀) (γ t₀))
      D₁ (W₂ t₀) = g.metricInner (γ t₀) D₁ (W₂ t₀) := by
    have hb := metricInner_eq_chartMetricInner (I := I) g (γ t₀) hself
      (D₁ : TangentSpace I (γ t₀)) (W₂ t₀)
    rw [chartFiberCoord_mk (I := I) (γ t₀) D₁,
      chartFiberCoord_mk (I := I) (γ t₀) (W₂ t₀)] at hb
    exact hb.symm
  have hb : chartMetricInner (I := I) g (γ t₀) (extChartAt I (γ t₀) (γ t₀))
      (W₁ t₀) D₂ = g.metricInner (γ t₀) (W₁ t₀) D₂ := by
    have hc := metricInner_eq_chartMetricInner (I := I) g (γ t₀) hself
      (W₁ t₀) (D₂ : TangentSpace I (γ t₀))
    rw [chartFiberCoord_mk (I := I) (γ t₀) (W₁ t₀),
      chartFiberCoord_mk (I := I) (γ t₀) D₂] at hc
    exact hc.symm
  rw [ha, hb] at hcore
  -- transfer the function through the chart
  refine hcore.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with s hs
  exact metricInner_eq_chartMetricInner (I := I) g (γ t₀) hs (W₁ s) (W₂ s)

/-- **Math.** Blueprint part (5): a field `W` along `γ` is **parallel** when its
covariant derivative vanishes at every time. -/
def IsParallelAlong (g : RiemannianMetric I M) (γ : ℝ → M)
    (W : ∀ t, TangentSpace I (γ t)) : Prop :=
  ∀ t, HasCovDerivAlongAt (I := I) g γ W t 0

/-- **Math.** The inner product of two parallel fields has vanishing derivative
at every time. -/
theorem IsParallelAlong.hasDerivAt_metricInner_zero
    {W₁ W₂ : ∀ t, TangentSpace I (γ t)}
    (h₁ : IsParallelAlong (I := I) g γ W₁) (h₂ : IsParallelAlong (I := I) g γ W₂)
    (t : ℝ) :
    HasDerivAt (fun s => g.metricInner (γ s) (W₁ s) (W₂ s)) 0 t := by
  have h := (h₁ t).hasDerivAt_metricInner (h₂ t)
  have hz₁ : g.metricInner (γ t) ((0 : E) : TangentSpace I (γ t)) (W₂ t) = 0 :=
    g.metricInner_zero_left (γ t) (W₂ t)
  have hz₂ : g.metricInner (γ t) (W₁ t) ((0 : E) : TangentSpace I (γ t)) = 0 :=
    g.metricInner_zero_right (γ t) (W₁ t)
  rw [hz₁, hz₂, add_zero] at h
  exact h

/-- **Math.** Blueprint part (5), first clause: the inner product of two
parallel fields along a curve is **constant**. -/
theorem IsParallelAlong.metricInner_eq {W₁ W₂ : ∀ t, TangentSpace I (γ t)}
    (h₁ : IsParallelAlong (I := I) g γ W₁) (h₂ : IsParallelAlong (I := I) g γ W₂)
    (s t : ℝ) :
    g.metricInner (γ s) (W₁ s) (W₂ s) = g.metricInner (γ t) (W₁ t) (W₂ t) := by
  have hder := h₁.hasDerivAt_metricInner_zero (I := I) h₂
  exact is_const_of_deriv_eq_zero
    (fun u => (hder u).differentiableAt) (fun u => (hder u).deriv) s t

/-- **Math.** Blueprint part (5), second clause: two parallel fields along a
curve that agree at one time agree at every time. The difference field is
parallel, so its squared norm is constant, and it vanishes at the common
time; positive-definiteness of the metric forces it to vanish identically. -/
theorem IsParallelAlong.apply_eq {W₁ W₂ : ∀ t, TangentSpace I (γ t)}
    (h₁ : IsParallelAlong (I := I) g γ W₁) (h₂ : IsParallelAlong (I := I) g γ W₂)
    {t₁ : ℝ} (hpt : W₁ t₁ = W₂ t₁) (t : ℝ) :
    W₁ t = W₂ t := by
  have hd : IsParallelAlong (I := I) g γ (fun r => W₁ r - W₂ r) := by
    intro r
    have := (h₁ r).sub (h₂ r)
    simpa using this
  have hnorm := hd.metricInner_eq (I := I) hd t t₁
  rw [hpt, sub_self, g.metricInner_zero_left] at hnorm
  by_contra hne
  have hsub : W₁ t - W₂ t ≠ 0 := sub_ne_zero.mpr hne
  have hpos := g.metricInner_self_pos (γ t) (W₁ t - W₂ t) hsub
  rw [hnorm] at hpos
  exact lt_irrefl _ hpos

/-! ### The velocity field and the geodesic equation -/

/-- **Math.** The **chart velocity** of a curve `γ : ℝ → M` at time `t`: the
derivative of the chart curve at the moving foot `γ t`, as a model-space
vector. -/
def curveVelocityCoord (γ : ℝ → M) (t : ℝ) : E :=
  deriv (chartLocalCurve (I := I) γ t) t

@[simp] theorem curveVelocityCoord_def (γ : ℝ → M) (t : ℝ) :
    curveVelocityCoord (I := I) γ t = deriv (chartLocalCurve (I := I) γ t) t := rfl

/-- **Math.** The **velocity field** of a curve `γ : ℝ → M`: at each time `t`
the derivative of the chart curve at the moving foot `γ t`, read as a tangent
vector at `γ t`. For a differentiable curve this is the intrinsic velocity
`γ'(t) ∈ T_{γ t} M`; junk where `γ` is not differentiable. -/
def curveVelocity (γ : ℝ → M) : ∀ t, TangentSpace I (γ t) :=
  fun t => (curveVelocityCoord (I := I) γ t : E)

@[simp] theorem curveVelocity_def (γ : ℝ → M) (t : ℝ) :
    curveVelocity (I := I) γ t = curveVelocityCoord (I := I) γ t := rfl

/-- **Math.** **Chart transition for curve derivatives**: if the chart curve of
`γ` at anchor `x` has derivative `v` at `s` (with `γ` near `s` in the chart
source at `x`), then the chart curve at any other anchor `y` whose chart
contains `γ s` has derivative `tangentCoordChange I x y (γ s) v` at `s` —
the coordinate change of `v` from the `x`-chart to the `y`-chart. -/
theorem hasDerivAt_extChartAt_comp {x y : M} {γ : ℝ → M} {s : ℝ} {v : E}
    (hmem : ∀ᶠ u in 𝓝 s, γ u ∈ (chartAt H x).source)
    (hy : γ s ∈ (chartAt H y).source)
    (hd : HasDerivAt (fun u => extChartAt I x (γ u)) v s) :
    HasDerivAt (fun u => extChartAt I y (γ u))
      (tangentCoordChange I x y (γ s) v) s := by
  have hsx : γ s ∈ (chartAt H x).source := hmem.self_of_nhds
  have hsx' : γ s ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hsy' : γ s ∈ (extChartAt I y).source := by rwa [extChartAt_source]
  have htrans : HasFDerivAt (extChartAt I y ∘ (extChartAt I x).symm)
      (tangentCoordChange I x y (γ s)) (extChartAt I x (γ s)) := by
    have h := hasFDerivWithinAt_tangentCoordChange (I := I) ⟨hsx', hsy'⟩
    rw [I.range_eq_univ] at h
    exact hasFDerivWithinAt_univ.mp h
  refine (htrans.comp_hasDerivAt s hd).congr_of_eventuallyEq ?_
  filter_upwards [hmem] with u hu
  simp only [Function.comp_apply]
  rw [(extChartAt I x).left_inv (by rwa [extChartAt_source])]

/-- **Math.** The chart-`x` coordinates of the velocity field at time `s` are
the derivative of the chart-`x` curve: for `γ` staying in the `x`-chart near
`s` with chart-curve derivative `v` at `s`,
`(γ')^{x-chart}(s) = d/du (φ_x ∘ γ)(s) = v`. -/
theorem chartFieldCoord_curveVelocity_eq {x : M} {γ : ℝ → M} {s : ℝ} {v : E}
    (hmem : ∀ᶠ u in 𝓝 s, γ u ∈ (chartAt H x).source)
    (hd : HasDerivAt (fun u => extChartAt I x (γ u)) v s) :
    chartFieldCoord (I := I) x γ (curveVelocity (I := I) γ) s = v := by
  have hsx : γ s ∈ (chartAt H x).source := hmem.self_of_nhds
  have hsx' : γ s ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hself' : γ s ∈ (extChartAt I (γ s)).source := by
    rw [extChartAt_source]; exact mem_chart_source H (γ s)
  have hstep := hasDerivAt_extChartAt_comp (I := I) (y := γ s) hmem
    (mem_chart_source H (γ s)) hd
  have hcv : curveVelocity (I := I) γ s = tangentCoordChange I x (γ s) (γ s) v := by
    rw [curveVelocity_def, curveVelocityCoord_def]
    exact hstep.deriv
  show tangentCoordChange I (γ s) x (γ s) (curveVelocity (I := I) γ s) = v
  rw [hcv, tangentCoordChange_comp (I := I) ⟨⟨hsx', hself'⟩, hsx'⟩,
    tangentCoordChange_self (I := I) hsx']

/-- **Math.** Blueprint part (4): a curve satisfies the **geodesic equation** at
`t₀` iff its velocity field is **parallel** at `t₀`, `Dγ'/dt (t₀) = 0`. The
side conditions say that `γ` stays in the moving-foot chart near `t₀` and its
chart curve is differentiable near `t₀` (automatic for the geodesics produced
by the flow, and part of the geodesic-equation data in the forward
direction). -/
theorem hasGeodesicEquationAt_iff_hasCovDerivAlongAt_velocity_zero
    (hmem : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source)
    (hev : ∀ᶠ s in 𝓝 t₀, HasDerivAt (chartLocalCurve (I := I) γ t₀)
      (deriv (chartLocalCurve (I := I) γ t₀) s) s) :
    Geodesic.HasGeodesicEquationAt (I := I) g γ t₀
      ↔ HasCovDerivAlongAt (I := I) g γ (curveVelocity (I := I) γ) t₀ 0 := by
  have hveq : (fun u => chartFieldCoord (I := I) (γ t₀) γ (curveVelocity (I := I) γ) u)
      =ᶠ[𝓝 t₀] fun u => deriv (chartLocalCurve (I := I) γ t₀) u := by
    filter_upwards [hmem.eventually_nhds, hev] with u hu hd
    exact chartFieldCoord_curveVelocity_eq (I := I) hu hd
  constructor
  · rintro ⟨v, a, hv, -, ha, heq⟩
    refine ⟨hmem, v, a, hv, ?_, ?_⟩
    · exact ha.congr_of_eventuallyEq hveq
    · rw [curveVelocity_def, curveVelocityCoord_def, hv.deriv]
      exact heq
  · rintro ⟨-, v, dV, hv, hdV, hEq⟩
    refine ⟨v, dV, hv, hev, ?_, ?_⟩
    · exact hdV.congr_of_eventuallyEq hveq.symm
    · rw [curveVelocity_def, curveVelocityCoord_def, hv.deriv] at hEq
      exact hEq

/-! ### Restriction of a global vector field along a curve -/

/-- **Math.** The chart-`x` coordinate representation of a smooth vector field
`Z` on `M`, as a function on the manifold: `q ↦ Z(q)` read through the
trivialization at `x`. -/
def fieldRep (x : M) (Z : SmoothVectorField I M) : M → E :=
  fun q => chartFiberCoord (I := I) x ⟨q, Z q⟩

@[simp] theorem fieldRep_def (x : M) (Z : SmoothVectorField I M) (q : M) :
    fieldRep (I := I) x Z q = chartFiberCoord (I := I) x ⟨q, Z q⟩ := rfl

/-- **Math.** The chart-`x` coordinate representation of a smooth vector field
`Z`, as a function on the chart target: the composition of `fieldRep` with the
inverse chart. -/
def fieldChartRep (x : M) (Z : SmoothVectorField I M) : E → E :=
  fun y => fieldRep (I := I) x Z ((extChartAt I x).symm y)

@[simp] theorem fieldChartRep_def (x : M) (Z : SmoothVectorField I M) (y : E) :
    fieldChartRep (I := I) x Z y
      = fieldRep (I := I) x Z ((extChartAt I x).symm y) := rfl

/-- **Math.** The coordinate representation of a smooth vector field is smooth
at the anchor point: smoothness of the section read through the
trivialization at `x`. -/
theorem contMDiffAt_fieldRep (x : M) (Z : SmoothVectorField I M) :
    ContMDiffAt I 𝓘(ℝ, E) ∞ (fieldRep (I := I) x Z) x :=
  (Bundle.contMDiffAt_section x).mp Z.smooth.contMDiffAt

/-- **Math.** The chart coordinate representation of a smooth vector field is
differentiable at the chart image of the anchor point. -/
theorem contDiffAt_fieldChartRep (x : M) (Z : SmoothVectorField I M) :
    ContDiffAt ℝ ∞ (fieldChartRep (I := I) x Z) (extChartAt I x x) := by
  have hx : x ∈ (extChartAt I x).source := mem_extChartAt_source x
  have hsymm : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I x).symm (extChartAt I x x) := by
    refine (contMDiffOn_extChartAt_symm (I := I) x).contMDiffAt ?_
    exact (isOpen_extChartAt_target x).mem_nhds ((extChartAt I x).map_source hx)
  have hrep' : ContMDiffAt I 𝓘(ℝ, E) ∞ (fieldRep (I := I) x Z)
      ((extChartAt I x).symm (extChartAt I x x)) := by
    rw [(extChartAt I x).left_inv hx]
    exact contMDiffAt_fieldRep (I := I) x Z
  have hcomp := ContMDiffAt.comp (extChartAt I x x) hrep' hsymm
  exact contMDiffAt_iff_contDiffAt.mp hcomp

/-- **Math.** Blueprint part (1), the **composed-field property**, chart form:
the restriction `Z ∘ γ` of a smooth vector field `Z` along a curve `γ` with
chart velocity `v` at `t₀` has covariant derivative
`D(Z∘γ)/dt (t₀) = ∂_v Z^{chart} + Γ(v, Z(γ t₀))` — the chart covariant
derivative of `Z` at `γ t₀` in the direction `v`. (The identification of this
value with the Levi-Civita `(∇_X Z)(γ t₀)` for a global field `X` with
`X(γ t₀) = γ'(t₀)` is the chart-Christoffel frame bridge, a separate step.) -/
theorem hasCovDerivAlongAt_comp (Z : SmoothVectorField I M)
    (hmem : ∀ᶠ s in 𝓝 t₀, γ s ∈ (chartAt H (γ t₀)).source)
    {v : E} (hv : HasDerivAt (chartLocalCurve (I := I) γ t₀) v t₀) :
    HasCovDerivAlongAt (I := I) g γ (fun t => Z (γ t)) t₀
      (fderiv ℝ (fieldChartRep (I := I) (γ t₀) Z) (extChartAt I (γ t₀) (γ t₀)) v
        + chartChristoffelContraction (I := I) g (γ t₀) v (Z (γ t₀))
            (extChartAt I (γ t₀) (γ t₀))) := by
  refine ⟨hmem, v,
    fderiv ℝ (fieldChartRep (I := I) (γ t₀) Z) (extChartAt I (γ t₀) (γ t₀)) v,
    hv, ?_, rfl⟩
  have hdiff : DifferentiableAt ℝ (fieldChartRep (I := I) (γ t₀) Z)
      (extChartAt I (γ t₀) (γ t₀)) :=
    (contDiffAt_fieldChartRep (I := I) (γ t₀) Z).differentiableAt (by simp)
  have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt t₀ hv
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with s hs
  show chartFieldCoord (I := I) (γ t₀) γ (fun t => Z (γ t)) s
    = fieldChartRep (I := I) (γ t₀) Z (chartLocalCurve (I := I) γ t₀ s)
  have hss : γ s ∈ (extChartAt I (γ t₀)).source := by rwa [extChartAt_source]
  calc chartFieldCoord (I := I) (γ t₀) γ (fun t => Z (γ t)) s
      = fieldRep (I := I) (γ t₀) Z (γ s) := rfl
    _ = fieldRep (I := I) (γ t₀) Z
        ((extChartAt I (γ t₀)).symm (chartLocalCurve (I := I) γ t₀ s)) := by
        rw [chartLocalCurve_def, (extChartAt I (γ t₀)).left_inv hss]
    _ = fieldChartRep (I := I) (γ t₀) Z (chartLocalCurve (I := I) γ t₀ s) := rfl

/-! ### Toward the chart formula for the Levi-Civita covariant derivative

The identification of the chart covariant derivative
`∂_v Ẑ + Γ(v, Z x)` produced by `hasCovDerivAlongAt_comp` with the abstract
`(∇_X Z)(x)` (for `X x` the velocity) is the frame-bridge computation; the
two lemmas below are its pointwise ingredients. -/

/- Germ locality of `∇` in the differentiated slot, `cov_congr_apply_right`,
is provided by `PoincareLib.Ch01.CurvatureFrameBridge` (imported above); the
copy this file used to carry was an exact duplicate and was removed when the
Ch01 file landed. -/

/-- **Math.** At the centre of its own chart, the chart-frame vector is the
corresponding model basis vector: the trivialization at `x` is the identity
on the fibre over `x`. -/
theorem chartBasisVecFiber_self (x : M) (i : Fin (Module.finrank ℝ E)) :
    Tensor.chartBasisVecFiber (I := I) x i x = (Module.finBasis ℝ E) i := by
  have h1 := chartFiberCoord_mk (I := I) x
    (Tensor.chartBasisVecFiber (I := I) x i x)
  have h2 := Tensor.trivializationAt_chartBasisVec_snd (I := I) x i
    (FiberBundle.mem_baseSet_trivializationAt' x)
  rw [← h1]
  exact h2

end PoincareLib

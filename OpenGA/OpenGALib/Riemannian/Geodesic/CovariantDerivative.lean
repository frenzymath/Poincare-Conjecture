import OpenGALib.Riemannian.Geodesic.Equation
import OpenGALib.Riemannian.Geodesic.LinearODE
import Mathlib.Analysis.ODE.Gronwall

/-!
# Covariant derivative of a vector field along a curve (do Carmo Ch. 2, §2)

For a Riemannian metric `g` on `M`, a chart basepoint `α : M`, a coordinate curve
`u : ℝ → E` (the chart image `φ_α ∘ c` of a curve `c : I → M`) and a coordinate
vector field `V : ℝ → E` along it, do Carmo's Proposition 2.2 gives the covariant
derivative `DV/dt` by the coordinate formula (do Carmo (1))
$$\frac{DV}{dt} = \dot V + \Gamma\big(\dot u, V\big)(u),$$
where `Γ(·,·)(y) = chartChristoffelContraction g α · · y` is the Christoffel
contraction already used by the geodesic pipeline (`Geodesic.Equation`).

This file records:

* `Riemannian.covariantDerivCoord g α u V` — the operator `DV/dt` in coordinates.
* `covariantDerivCoord_add` / `covariantDerivCoord_smul` — the two characterizing
  algebraic properties (do Carmo Prop. 2.2 (a) additivity and (b) the Leibniz
  rule), the content that makes `D/dt` a *bona fide* derivative of vector fields
  along curves.
* `Riemannian.IsParallelCoord g α u V` — do Carmo Def. 2.5: `V` is **parallel**
  along the curve when `DV/dt ≡ 0`.
* `covariantDerivCoord_eq_zero_iff` — the parallelism equation in solved ODE form
  `V̇ = −Γ(u̇, V)(u)`, the first-order linear system whose Picard–Lindelöf theory
  yields parallel transport (do Carmo Prop. 2.6).

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 §2, Prop. 2.2, Def. 2.5, Prop. 2.6.
-/

open scoped Manifold Topology ContDiff
open Set

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 2, Prop. 2.2, formula (1). The **covariant derivative**
`DV/dt` of a coordinate vector field `V : ℝ → E` along the coordinate curve
`u : ℝ → E`, read in the fixed chart at `α`:
`DV/dt = V̇ + Γ(u̇, V)(u)`, where `Γ` is `Geodesic.chartChristoffelContraction g α`.
This is the closed expression forced on any operator satisfying do Carmo's
axioms (a)–(c); the file proves it satisfies (a) and (b). -/
def covariantDerivCoord (g : RiemannianMetric I M) (α : M) (u V : ℝ → E) (t : ℝ) : E :=
  deriv V t + Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t)

@[simp] theorem covariantDerivCoord_def (g : RiemannianMetric I M) (α : M)
    (u V : ℝ → E) (t : ℝ) :
    covariantDerivCoord (I := I) g α u V t =
      deriv V t
        + Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t) := rfl

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (a): the covariant derivative along a
curve is **additive** in the vector field, `D/dt (V + W) = DV/dt + DW/dt`. -/
theorem covariantDerivCoord_add (g : RiemannianMetric I M) (α : M) (u V W : ℝ → E)
    {t : ℝ} (hV : DifferentiableAt ℝ V t) (hW : DifferentiableAt ℝ W t) :
    covariantDerivCoord (I := I) g α u (V + W) t
      = covariantDerivCoord (I := I) g α u V t + covariantDerivCoord (I := I) g α u W t := by
  simp only [covariantDerivCoord_def, Pi.add_apply, deriv_add hV hW,
    Geodesic.chartChristoffelContraction_add_right]
  abel

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (b): the **Leibniz rule** for the covariant
derivative along a curve, `D/dt (f · V) = ḟ · V + f · DV/dt`, for a scalar
`f : ℝ → ℝ` differentiable along the curve. -/
theorem covariantDerivCoord_smul (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (f : ℝ → ℝ) (V : ℝ → E) {t : ℝ}
    (hf : DifferentiableAt ℝ f t) (hV : DifferentiableAt ℝ V t) :
    covariantDerivCoord (I := I) g α u (f • V) t
      = deriv f t • V t + f t • covariantDerivCoord (I := I) g α u V t := by
  simp only [covariantDerivCoord_def, Pi.smul_apply', deriv_smul hf hV,
    Geodesic.chartChristoffelContraction_smul_right, smul_add]
  abel

/-- **Math.** do Carmo Ch. 2, Def. 2.5. A coordinate vector field `V : ℝ → E`
along the coordinate curve `u : ℝ → E` is **parallel** (with respect to `g` in the
chart at `α`) when its covariant derivative vanishes identically, `DV/dt ≡ 0`. -/
def IsParallelCoord (g : RiemannianMetric I M) (α : M) (u V : ℝ → E) : Prop :=
  ∀ t, covariantDerivCoord (I := I) g α u V t = 0

/-- **Math.** The parallel-transport ODE in solved form. `V` is parallel along `u`
iff it solves the first-order **linear** system `V̇(t) = −Γ(u̇(t), V(t))(u(t))`
(linear in `V(t)` by `chartChristoffelContraction_add_right` /
`chartChristoffelContraction_smul_right`). This is the equation whose
Picard–Lindelöf theory gives existence and uniqueness of parallel transport
(do Carmo Prop. 2.6). -/
theorem isParallelCoord_iff_hasDerivAt (g : RiemannianMetric I M) (α : M)
    (u V : ℝ → E) (hV : ∀ t, DifferentiableAt ℝ V t) :
    IsParallelCoord (I := I) g α u V ↔
      ∀ t, HasDerivAt V
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t)) t := by
  constructor
  · intro h t
    have hz := h t
    simp only [covariantDerivCoord_def] at hz
    have hd : deriv V t =
        -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t) :=
      eq_neg_iff_add_eq_zero.mpr hz
    rw [← hd]; exact (hV t).hasDerivAt
  · intro h t
    simp only [covariantDerivCoord_def]
    have := (h t).deriv
    rw [this]; abel

/-- **Math.** The **coefficient of the parallel-transport ODE**, packaged as a
continuous linear map. For a fixed velocity `v` and base point `y` read in the
chart at `α`, the map `w ↦ Γ(v, w)(y)` is linear (by
`chartChristoffelContraction_add_right` / `_smul_right`), hence — the model space
`E` being finite-dimensional — continuous. Writing `A(t) = Γ(u̇(t), ·)(u(t))`, a
vector field `V` along `u` is parallel iff it solves the first-order linear system
`V̇ = −A(t) V`; this is the coefficient `A(t)`, whose operator norm is the natural
Lipschitz constant of the right-hand side (see
`lipschitzWith_neg_chartChristoffelContraction`). -/
def chartChristoffelContractionRight (g : RiemannianMetric I M) (α : M) (v y : E) : E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => Geodesic.chartChristoffelContraction (I := I) g α v w y
      map_add' := fun w₁ w₂ =>
        Geodesic.chartChristoffelContraction_add_right (I := I) g α v w₁ w₂ y
      map_smul' := fun a w => by
        simpa using Geodesic.chartChristoffelContraction_smul_right (I := I) g α v a w y }

@[simp] theorem chartChristoffelContractionRight_apply (g : RiemannianMetric I M) (α : M) (v y w : E) :
    chartChristoffelContractionRight (I := I) g α v y w
      = Geodesic.chartChristoffelContraction (I := I) g α v w y := rfl

/-- **Math.** The right-hand side of the parallel-transport ODE is globally
Lipschitz in the vector-field slot, with the operator norm of the coefficient
`chartChristoffelContractionRight g α v y` as an explicit Lipschitz constant. This is the
uniform bound that turns Grönwall's inequality into uniqueness of parallel
transport, and the a-priori estimate underpinning global existence. -/
theorem lipschitzWith_neg_chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (v y : E) :
    LipschitzWith ‖chartChristoffelContractionRight (I := I) g α v y‖₊
      (fun w => -Geodesic.chartChristoffelContraction (I := I) g α v w y) := by
  have h := (chartChristoffelContractionRight (I := I) g α v y).lipschitz.neg
  simpa only [chartChristoffelContractionRight_apply] using h

/-- **Math.** do Carmo Ch. 2, Prop. 2.6 (uniqueness half): **uniqueness of parallel
transport**. On a time interval `[a, b]`, two parallel vector fields along the same
coordinate curve `u` that agree at the left endpoint `a` agree on all of `[a, b]`.

This is the uniqueness of solutions of the first-order linear system
`V̇ = −Γ(u̇, V)(u)` (`isParallelCoord_iff_hasDerivAt`), obtained from Grönwall's
inequality via `ODE_solution_unique_of_mem_Icc_right`. The only hypothesis on the
curve is the clean operator-norm bound `hK` on the ODE coefficient
`chartChristoffelContractionRight g α (u̇ t) (u t)` over `[a, b)`; for a `C¹` curve `u` and
continuous Christoffel symbols such a `K` always exists by compactness of `[a, b]`.
The uniform Lipschitz constant needed by Grönwall is produced internally from `hK`
via `lipschitzWith_neg_chartChristoffelContraction`. -/
theorem isParallelCoord_eqOn_Icc (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {V W : ℝ → E} {a b : ℝ} {K : NNReal}
    (hV : Differentiable ℝ V) (hW : Differentiable ℝ W)
    (hVp : IsParallelCoord (I := I) g α u V) (hWp : IsParallelCoord (I := I) g α u W)
    (hK : ∀ t ∈ Set.Ico a b,
        ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    (ha : V a = W a) :
    Set.EqOn V W (Set.Icc a b) := by
  have hlip : ∀ t ∈ Set.Ico a b, LipschitzOnWith K
      (fun w => -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) w (u t))
      Set.univ := fun t ht =>
    ((lipschitzWith_neg_chartChristoffelContraction (I := I) g α (deriv u t) (u t)).weaken
      (hK t ht)).lipschitzOnWith
  have hVd := (isParallelCoord_iff_hasDerivAt (I := I) g α u V (fun t => hV t)).mp hVp
  have hWd := (isParallelCoord_iff_hasDerivAt (I := I) g α u W (fun t => hW t)).mp hWp
  exact ODE_solution_unique_of_mem_Icc_right
    (v := fun t w => -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) w (u t))
    (s := fun _ => Set.univ) hlip
    hV.continuous.continuousOn
    (fun t _ => (hVd t).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    hW.continuous.continuousOn
    (fun t _ => (hWd t).hasDerivWithinAt) (fun _ _ => Set.mem_univ _) ha

/-- **Math.** do Carmo Ch. 2, Prop. 2.6 (existence half): **existence of parallel transport**.
On a compact time interval `[a, b]`, for any prescribed initial vector `V₀` there is a
coordinate vector field `V` along the coordinate curve `u` with `V a = V₀` that is parallel,
i.e. solves the first-order linear system `V̇ = −Γ(u̇, V)(u)` on `[a, b]`.

This is the existence half of `prop:dc-ch2-2-6`, complementing the uniqueness half
`isParallelCoord_eqOn_Icc`. The parallelism system is the linear ODE `V̇ = A(t) V` with
coefficient `A(t) = −chartChristoffelContractionRight g α (u̇ t) (u t)`, and the solution is
produced by the global linear-ODE existence theorem
`Riemannian.LinearODE.exists_hasDerivWithinAt_Icc` (Picard–Lindelöf on short pieces, glued
across a partition of `[a, b]`). The only hypotheses on the curve are that this coefficient is
continuous and bounded by `K` on `[a, b]`; for a `C¹` curve with continuous Christoffel
symbols both hold by compactness. -/
theorem exists_isParallelCoord_Icc (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) (V₀ : E) {K : NNReal}
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Set.Icc a b))
    (hK : ∀ t ∈ Set.Icc a b,
        ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K) :
    ∃ V : ℝ → E, V a = V₀ ∧
      ∀ t ∈ Set.Icc a b, HasDerivWithinAt V
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
        (Set.Icc a b) t := by
  set A : ℝ → E →L[ℝ] E :=
    fun t => -chartChristoffelContractionRight (I := I) g α (deriv u t) (u t) with hA
  obtain ⟨V, hV0, hVd⟩ := LinearODE.exists_hasDerivWithinAt_Icc hab A V₀ (hcont.neg)
    (fun t ht => by rw [hA]; simpa using hK t ht)
  refine ⟨V, hV0, fun t ht => ?_⟩
  have := hVd t ht
  rwa [hA, ContinuousLinearMap.neg_apply, chartChristoffelContractionRight_apply] at this

/-- **Math.** do Carmo Ch. 2, Prop. 2.6 (uniqueness half), interval-native form matching the
existence output `exists_isParallelCoord_Icc`. Two vector fields solving the parallel-transport
ODE `V̇ = −Γ(u̇, V)(u)` on `[a, b]` (as `HasDerivWithinAt` on `Icc a b`, exactly the shape
produced by existence) that agree at the left endpoint `a` agree on all of `[a, b]`. This is
the specialization of the linear-ODE forward uniqueness `LinearODE.IsSolOn.eqOn_of_left` to the
coefficient `A(t) = −chartChristoffelContractionRight g α (u̇ t) (u t)`, and complements the
global-`IsParallelCoord` uniqueness `isParallelCoord_eqOn_Icc`. -/
theorem isParallelSol_eqOn_Icc (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {a b : ℝ} {K : NNReal}
    (hK : ∀ t ∈ Set.Icc a b,
        ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    {V W : ℝ → E}
    (hV : ∀ t ∈ Set.Icc a b, HasDerivWithinAt V
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
        (Set.Icc a b) t)
    (hW : ∀ t ∈ Set.Icc a b, HasDerivWithinAt W
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (W t) (u t))
        (Set.Icc a b) t)
    (ha : V a = W a) :
    Set.EqOn V W (Set.Icc a b) := by
  set A : ℝ → E →L[ℝ] E :=
    fun t => -chartChristoffelContractionRight (I := I) g α (deriv u t) (u t) with hA
  have hKA : ∀ t ∈ Set.Icc a b, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  have hVsol : LinearODE.IsSolOn A a b V := fun t ht => by
    have h := hV t ht
    rwa [show -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t)
        = A t (V t) by
      rw [hA]; simp only [ContinuousLinearMap.neg_apply, chartChristoffelContractionRight_apply]]
      at h
  have hWsol : LinearODE.IsSolOn A a b W := fun t ht => by
    have h := hW t ht
    rwa [show -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (W t) (u t)
        = A t (W t) by
      rw [hA]; simp only [ContinuousLinearMap.neg_apply, chartChristoffelContractionRight_apply]]
      at h
  exact LinearODE.IsSolOn.eqOn_of_left hKA hVsol hWsol ha

/-- **Math.** do Carmo Ch. 2, Prop. 2.6 (parallel transport map). The **parallel transport**
`P_c : T_{c(a)}M → T_{c(b)}M`, read in the fixed chart at `α`, sending an initial vector `V₀`
at time `a` to the value at time `b` of the unique parallel coordinate vector field `V` along
`u` with `V(a) = V₀`. It is a **linear isomorphism**: linearity and injectivity come from the
linear-ODE flow (`LinearODE.flowMap`, `LinearODE.flowMap_injective`) — the parallelism system
`V̇ = −Γ(u̇, V)(u)` being first-order linear — and an injective linear endomorphism of the
finite-dimensional model space `E` is automatically bijective. This is do Carmo's `P_c`. -/
noncomputable def parallelTransport (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) {K : NNReal}
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Set.Icc a b))
    (hK : ∀ t ∈ Set.Icc a b,
        ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K) :
    E ≃ₗ[ℝ] E := by
  set A : ℝ → E →L[ℝ] E :=
    fun t => -chartChristoffelContractionRight (I := I) g α (deriv u t) (u t) with hA
  have hcontA : ContinuousOn A (Set.Icc a b) := hcont.neg
  have hKA : ∀ t ∈ Set.Icc a b, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  exact LinearEquiv.ofInjectiveEndo (LinearODE.flowMap hab hcontA hKA)
    (LinearODE.flowMap_injective hab hcontA hKA)

/-- **Math.** The parallel transport `P_c V₀` (do Carmo Prop. 2.6) is realized by a genuine
parallel coordinate vector field: there is a curve `V` along `u` with `V(a) = V₀`,
`V(b) = P_c V₀`, solving the parallelism ODE `V̇ = −Γ(u̇, V)(u)` on `[a, b]`. Existence of the
parallel field with the two prescribed endpoint values, packaging
`exists_isParallelCoord_Icc` with the flow definition of `parallelTransport`. -/
theorem exists_parallelTransport_spec (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    {a b : ℝ} (hab : a ≤ b) {K : NNReal}
    (hcont : ContinuousOn
      (fun t => chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)) (Set.Icc a b))
    (hK : ∀ t ∈ Set.Icc a b,
        ‖chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)‖₊ ≤ K)
    (V₀ : E) :
    ∃ V : ℝ → E, V a = V₀ ∧ V b = parallelTransport (I := I) g α u hab hcont hK V₀ ∧
      ∀ t ∈ Set.Icc a b, HasDerivWithinAt V
        (-Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t))
        (Set.Icc a b) t := by
  set A : ℝ → E →L[ℝ] E :=
    fun t => -chartChristoffelContractionRight (I := I) g α (deriv u t) (u t) with hA
  have hcontA : ContinuousOn A (Set.Icc a b) := hcont.neg
  have hKA : ∀ t ∈ Set.Icc a b, ‖A t‖₊ ≤ K := fun t ht => by rw [hA]; simpa using hK t ht
  refine ⟨LinearODE.solOf hab hcontA hKA V₀, LinearODE.solOf_left hab hcontA hKA V₀, rfl,
    fun t ht => ?_⟩
  have h := LinearODE.solOf_isSolOn hab hcontA hKA V₀ t ht
  have hval : ∀ w : E, A t w
      = -Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) w (u t) := fun w => by
    rw [hA]; simp only [ContinuousLinearMap.neg_apply, chartChristoffelContractionRight_apply]
  rwa [hval] at h

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 property (c) / Remark 2.3, coordinate form. The
**coordinate covariant derivative** of a coordinate vector field `Y : E → E` in the direction
`v` at the base point `y`, read in the chart at `α`:
`(∇_v Y)(y) = DY(y)·v + Γ(v, Y(y))(y)`. The first term is the ordinary directional derivative
of the components (do Carmo's `X(y_k)`) and the second the Christoffel correction, matching
Remark 2.3, `∇_X Y = ∑_k(∑_{ij} x_i y_j Γ^k_{ij} + X(y_k)) X_k`. This is `∇_{dc/dt} Y` read in
coordinates, the right-hand side of property (c). -/
def chartCovariantDeriv (g : RiemannianMetric I M) (α : M) (v y : E) (Y : E → E) : E :=
  fderiv ℝ Y y v + Geodesic.chartChristoffelContraction (I := I) g α v (Y y) y

@[simp] theorem chartCovariantDeriv_def (g : RiemannianMetric I M) (α : M) (v y : E) (Y : E → E) :
    chartCovariantDeriv (I := I) g α v y Y
      = fderiv ℝ Y y v + Geodesic.chartChristoffelContraction (I := I) g α v (Y y) y := rfl

/-- **Math.** do Carmo Ch. 2, Prop. 2.2, **property (c)** in coordinates. When the vector field
`V` along the curve `u` is *induced* by a coordinate field `Y : E → E`, i.e. `V(t) = Y(u(t))`,
its covariant derivative along `u` equals the coordinate covariant derivative of `Y` in the
direction `u̇(t)`:
`D(Y∘u)/dt = (∇_{u̇} Y)(u)`.
This is the substantive analytic content of property (c) — do Carmo's key step
`DX_j/dt = ∇_{dc/dt} X_j` — obtained from the chain rule `d/dt Y(u(t)) = DY(u(t))·u̇(t)`, which
turns the plain `V̇` term of the covariant derivative into the directional-derivative term of
the connection while the Christoffel contraction matches on the nose. The one remaining
ingredient of the full (manifold-level) property (c) is the identification of this coordinate
`∇` with the abstract Levi-Civita connection, i.e. the chart-Christoffel bridge
`chartChristoffel = Γ(∇)`. -/
theorem covariantDerivCoord_induced (g : RiemannianMetric I M) (α : M) (u : ℝ → E) (Y : E → E)
    {t : ℝ} (hu : DifferentiableAt ℝ u t) (hY : DifferentiableAt ℝ Y (u t)) :
    covariantDerivCoord (I := I) g α u (fun s => Y (u s)) t
      = chartCovariantDeriv (I := I) g α (deriv u t) (u t) Y := by
  have hcomp : deriv (fun s => Y (u s)) t = fderiv ℝ Y (u t) (deriv u t) :=
    (hY.hasFDerivAt.comp_hasDerivAt t hu.hasDerivAt).deriv
  simp only [covariantDerivCoord_def, chartCovariantDeriv_def, hcomp]

/-! ## Metric compatibility of the covariant derivative along a curve
(do Carmo Ch. 2, §3, Prop. 3.2 / Def. 3.1, coordinate form)

For the Levi-Civita covariant derivative `D/dt` built above from the metric's chart
Christoffel symbols, the chart Gram inner product obeys the product rule
`d/dt⟨V,W⟩ = ⟨DV/dt, W⟩ + ⟨V, DW/dt⟩` (do Carmo eq. (3)); consequently parallel
vector fields have constant inner product (do Carmo Def. 3.1). The analytic heart is
do Carmo's formula (10), `∂_k G_{ij} = ∑_m (G_{mj}Γ^m_{ki} + G_{im}Γ^m_{kj})`
(`partialDeriv_chartGramOnE_eq`), the coordinate form of `∇g = 0`. -/

/-- **Math.** Reindexing helper: a four-fold finite sum is invariant under swapping the
roles of its first and last summation index. -/
theorem sum4_swap14 {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → α) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f d b c a := by
  have key : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.2.2.2 x.2.1 x.2.2.1 x.1 :=
    Fintype.sum_bijective (fun x => (x.2.2.2, x.2.1, x.2.2.1, x.1))
      (Function.Involutive.bijective (fun _ => rfl)) _ _ (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using key

/-- **Math.** Reindexing helper: a four-fold finite sum is invariant under swapping the
roles of its second and last summation index. -/
theorem sum4_swap24 {α : Type*} [AddCommMonoid α] {n : ℕ}
    (f : Fin n → Fin n → Fin n → Fin n → α) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ b, ∑ c, ∑ d, f a d c b := by
  have key : (∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.1 x.2.2.1 x.2.2.2)
      = ∑ x : Fin n × Fin n × Fin n × Fin n, f x.1 x.2.2.2 x.2.2.1 x.2.1 :=
    Fintype.sum_bijective (fun x => (x.1, x.2.2.2, x.2.2.1, x.2.1))
      (Function.Involutive.bijective (fun _ => rfl)) _ _ (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using key

/-- **Math.** Chart coordinate `i` packaged as a continuous linear functional on `E`. -/
noncomputable def Geodesic.chartCoordFunctional (i : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  ((Module.finBasis ℝ E).coord i).toContinuousLinearMap

@[simp] theorem Geodesic.chartCoordFunctional_apply (i : Fin (Module.finrank ℝ E)) (v : E) :
    Geodesic.chartCoordFunctional (E := E) i v = Geodesic.chartCoord (E := E) i v := by
  simp only [Geodesic.chartCoordFunctional, LinearMap.coe_toContinuousLinearMap',
    Module.Basis.coord_apply, Geodesic.chartCoord_def]

/-- **Math.** The chart Gram **inner product** of two coordinate vectors `a, b : E`
at the base point `y`, read in the chart at `α`:
`⟨a, b⟩_y = ∑_{i,j} G_{ij}(y)\, a^i\, b^j`, where `G_{ij} =` `chartGramOnE` and the
components `a^i, b^j` are taken in the chart-model basis. -/
def chartMetricInner (g : RiemannianMetric I M) (α : M) (y a b : E) : ℝ :=
  ∑ i, ∑ j, chartGramOnE (I := I) g α i j y
    * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b

@[simp] theorem chartMetricInner_def (g : RiemannianMetric I M) (α : M) (y a b : E) :
    chartMetricInner (I := I) g α y a b
      = ∑ i, ∑ j, chartGramOnE (I := I) g α i j y
          * Geodesic.chartCoord (E := E) i a * Geodesic.chartCoord (E := E) j b := rfl

/-- **Math.** The chart Gram inner product is additive in its first vector argument. -/
theorem chartMetricInner_add_left (g : RiemannianMetric I M) (α : M) (y a a' b : E) :
    chartMetricInner (I := I) g α y (a + a') b
      = chartMetricInner (I := I) g α y a b + chartMetricInner (I := I) g α y a' b := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Math.** The chart Gram inner product is additive in its second vector argument. -/
theorem chartMetricInner_add_right (g : RiemannianMetric I M) (α : M) (y a b b' : E) :
    chartMetricInner (I := I) g α y a (b + b')
      = chartMetricInner (I := I) g α y a b + chartMetricInner (I := I) g α y a b' := by
  simp only [chartMetricInner_def, Geodesic.chartCoord_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Math.** The `i`-th chart coordinate of the Christoffel contraction
`Γ(v, w)(y)` is the bilinear expression `∑_{a,b} Γ^i_{ab}(y)\, v^a\, w^b`. -/
theorem chartCoord_chartChristoffelContraction (g : RiemannianMetric I M) (α : M)
    (i : Fin (Module.finrank ℝ E)) (v w y : E) :
    Geodesic.chartCoord (E := E) i (Geodesic.chartChristoffelContraction (I := I) g α v w y)
      = ∑ a, ∑ b, chartChristoffel (I := I) g α a b i y
          * Geodesic.chartCoord (E := E) a v * Geodesic.chartCoord (E := E) b w := by
  classical
  rw [← Geodesic.chartCoordFunctional_apply, Geodesic.chartChristoffelContraction_def, map_sum]
  have hb : ∀ k, Geodesic.chartCoordFunctional (E := E) i (Module.finBasis ℝ E k)
      = (if k = i then (1 : ℝ) else 0) := by
    intro k
    rw [Geodesic.chartCoordFunctional_apply, Geodesic.chartCoord_def, Module.Basis.repr_self,
      Finsupp.single_apply]
  simp only [map_smul, smul_eq_mul, hb, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ i]
  simp only [Finset.mem_univ, if_true]

/-- **Math.** Expansion of a directional derivative in the chart-model basis:
`DG(y)·w = ∑_k w^k\, ∂_k G(y)`, the sum of partial derivatives weighted by the
components of the direction `w`. -/
theorem fderiv_apply_eq_sum_partialDeriv (G : E → ℝ) (y w : E) :
    fderiv ℝ G y w = ∑ k, Geodesic.chartCoord (E := E) k w * partialDeriv (E := E) k G y := by
  conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul]
  rfl

/-- **Math.** do Carmo Ch. 2, §3, the algebraic heart of Prop. 3.2 (coordinate
form): the direction-derivative of the chart Gram inner product, expanded through
formula (10) `∇g = 0`, splits exactly into the two Christoffel-correction terms of
the covariant derivative. For every base point `y` in the chart domain,
`∑_{i,j}(∑_k u̇^k ∂_k G_{ij})\, V^i W^j
  = ⟨Γ(u̇,V), W⟩_y + ⟨V, Γ(u̇,W)⟩_y`. -/
theorem chartMetricInner_gram_deriv_balance (g : RiemannianMetric I M) (α : M)
    (y ud Vv Ww : E)
    (hbase : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (∑ i, ∑ j, (∑ k, Geodesic.chartCoord (E := E) k ud
          * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)
      = chartMetricInner (I := I) g α y
            (Geodesic.chartChristoffelContraction (I := I) g α ud Vv y) Ww
        + chartMetricInner (I := I) g α y Vv
            (Geodesic.chartChristoffelContraction (I := I) g α ud Ww y) := by
  classical
  -- substitute formula (10) for each partial derivative of the Gram matrix
  have hL : (∑ i, ∑ j, (∑ k, Geodesic.chartCoord (E := E) k ud
          * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y)
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)
      = (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) k ud
            * chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
            * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)
        + (∑ i, ∑ j, ∑ k, ∑ m, Geodesic.chartCoord (E := E) k ud
            * chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y
            * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [partialDeriv_chartGramOnE_eq (I := I) g α i j k y hbase, Finset.mul_sum,
      Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  rw [hL]
  -- expand the two target inner products via `chartCoord` of the contraction
  have hR1 : chartMetricInner (I := I) g α y
        (Geodesic.chartChristoffelContraction (I := I) g α ud Vv y) Ww
      = ∑ i, ∑ j, ∑ a, ∑ b, chartGramOnE (I := I) g α i j y
          * chartChristoffel (I := I) g α a b i y
          * Geodesic.chartCoord (E := E) a ud * Geodesic.chartCoord (E := E) b Vv
          * Geodesic.chartCoord (E := E) j Ww := by
    simp only [chartMetricInner_def, chartCoord_chartChristoffelContraction,
      Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hR2 : chartMetricInner (I := I) g α y Vv
        (Geodesic.chartChristoffelContraction (I := I) g α ud Ww y)
      = ∑ i, ∑ j, ∑ a, ∑ b, chartGramOnE (I := I) g α i j y
          * chartChristoffel (I := I) g α a b j y
          * Geodesic.chartCoord (E := E) a ud * Geodesic.chartCoord (E := E) b Ww
          * Geodesic.chartCoord (E := E) i Vv := by
    simp only [chartMetricInner_def, chartCoord_chartChristoffelContraction,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hR1, hR2]
  congr 1
  · -- SL1 = R1 : swap the first (V-index) and last (Gram/Christoffel-upper) indices
    rw [sum4_swap14 (fun i j k m => Geodesic.chartCoord (E := E) k ud
        * chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  · -- SL2 = R2 : swap the second (W-index) and last (Gram/Christoffel-upper) indices
    rw [sum4_swap24 (fun i j k m => Geodesic.chartCoord (E := E) k ud
        * chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y
        * Geodesic.chartCoord (E := E) i Vv * Geodesic.chartCoord (E := E) j Ww)]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- **Math.** do Carmo Ch. 2, §3, Prop. 3.2 (coordinate form / do Carmo eq. (3)):
the Levi-Civita covariant derivative along a curve is **compatible with the
metric**. For a coordinate curve `u` staying in the chart domain and coordinate
vector fields `V, W` along it, the chart Gram inner product obeys the product rule
`d/dt⟨V, W⟩ = ⟨DV/dt, W⟩ + ⟨V, DW/dt⟩`, with `D/dt = covariantDerivCoord`. The `hG`
hypothesis is the differentiability of the chart metric coefficients along the
curve (automatic for a curve in the chart domain, the metric being smooth there).
The proof combines the product/chain rule with do Carmo's formula (10)
(`chartMetricInner_gram_deriv_balance`). -/
theorem hasDerivAt_chartMetricInner_along (g : RiemannianMetric I M) (α : M)
    (u V W : ℝ → E) {t : ℝ}
    (hu : DifferentiableAt ℝ u t) (hV : DifferentiableAt ℝ V t) (hW : DifferentiableAt ℝ W t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
      (chartMetricInner (I := I) g α (u t) (covariantDerivCoord (I := I) g α u V t) (W t)
        + chartMetricInner (I := I) g α (u t) (V t) (covariantDerivCoord (I := I) g α u W t)) t := by
  classical
  have ha : ∀ i j, HasDerivAt (fun s => chartGramOnE (I := I) g α i j (u s))
      (fderiv ℝ (chartGramOnE (I := I) g α i j) (u t) (deriv u t)) t :=
    fun i j => (hG i j).hasFDerivAt.comp_hasDerivAt t hu.hasDerivAt
  have hv : ∀ i, HasDerivAt (fun s => Geodesic.chartCoord (E := E) i (V s))
      (Geodesic.chartCoord (E := E) i (deriv V t)) t := by
    intro i
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) i).hasFDerivAt.comp_hasDerivAt t hV.hasDerivAt
  have hw : ∀ j, HasDerivAt (fun s => Geodesic.chartCoord (E := E) j (W s))
      (Geodesic.chartCoord (E := E) j (deriv W t)) t := by
    intro j
    simpa only [Geodesic.chartCoordFunctional_apply, Function.comp_def] using
      (Geodesic.chartCoordFunctional (E := E) j).hasFDerivAt.comp_hasDerivAt t hW.hasDerivAt
  -- derivative of the along-curve inner product, via product rule on each `G_{ij} V^i W^j`
  have hsum : HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
      (∑ i, ∑ j, ((fderiv ℝ (chartGramOnE (I := I) g α i j) (u t) (deriv u t)
              * Geodesic.chartCoord (E := E) i (V t)
            + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (deriv V t))
          * Geodesic.chartCoord (E := E) j (W t)
        + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (V t)
          * Geodesic.chartCoord (E := E) j (deriv W t))) t := by
    have hfun : (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s))
        = ∑ i, ∑ j, fun s => chartGramOnE (I := I) g α i j (u s)
            * Geodesic.chartCoord (E := E) i (V s) * Geodesic.chartCoord (E := E) j (W s) := by
      funext s; simp only [chartMetricInner_def, Finset.sum_apply]
    rw [hfun]
    apply HasDerivAt.sum
    intro i _
    apply HasDerivAt.sum
    intro j _
    exact ((ha i j).mul (hv i)).mul (hw j)
  -- identify that derivative with the covariant-derivative expression
  have hbalance := chartMetricInner_gram_deriv_balance (I := I) g α (u t) (deriv u t) (V t) (W t) hbase
  refine hsum.congr_deriv ?_
  rw [covariantDerivCoord_def, covariantDerivCoord_def, chartMetricInner_add_left,
    chartMetricInner_add_right]
  -- rewrite each `G_{ij}` direction-derivative through its partial derivatives, then formula (10)
  have hGram : (∑ i, ∑ j, ((fderiv ℝ (chartGramOnE (I := I) g α i j) (u t) (deriv u t)
              * Geodesic.chartCoord (E := E) i (V t)
            + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (deriv V t))
          * Geodesic.chartCoord (E := E) j (W t)
        + chartGramOnE (I := I) g α i j (u t) * Geodesic.chartCoord (E := E) i (V t)
          * Geodesic.chartCoord (E := E) j (deriv W t)))
      = (∑ i, ∑ j, (∑ k, Geodesic.chartCoord (E := E) k (deriv u t)
            * partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) (u t))
          * Geodesic.chartCoord (E := E) i (V t) * Geodesic.chartCoord (E := E) j (W t))
        + chartMetricInner (I := I) g α (u t) (deriv V t) (W t)
        + chartMetricInner (I := I) g α (u t) (V t) (deriv W t) := by
    simp only [chartMetricInner_def, fderiv_apply_eq_sum_partialDeriv,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hGram, hbalance]
  ring

/-- **Math.** do Carmo Ch. 2, §3, Def. 3.1 (coordinate form): the Levi-Civita
connection is **compatible with the metric** in do Carmo's original sense — any two
**parallel** coordinate vector fields `V, W` along a curve `u` (in the chart domain,
with `hG` the metric-coefficient differentiability) have **constant** chart Gram
inner product `⟨V, W⟩`. This is immediate from the product rule
(`hasDerivAt_chartMetricInner_along`): both covariant derivatives vanish, so the
derivative of `t ↦ ⟨V(t), W(t)⟩` is identically zero. -/
theorem hasDerivAt_chartMetricInner_eq_zero_of_isParallelCoord
    (g : RiemannianMetric I M) (α : M) (u V W : ℝ → E) {t : ℝ}
    (hu : DifferentiableAt ℝ u t) (hV : DifferentiableAt ℝ V t) (hW : DifferentiableAt ℝ W t)
    (hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) (u t))
    (hbase : (extChartAt I α).symm (u t) ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hVp : IsParallelCoord (I := I) g α u V) (hWp : IsParallelCoord (I := I) g α u W) :
    HasDerivAt (fun s => chartMetricInner (I := I) g α (u s) (V s) (W s)) 0 t := by
  refine (hasDerivAt_chartMetricInner_along (I := I) g α u V W hu hV hW hG hbase).congr_deriv ?_
  rw [hVp t, hWp t]
  simp [chartMetricInner_def]

/-- **Math.** do Carmo Ch. 3, §2, the geodesic definition's **constant-speed**
property. If `γ` satisfies the geodesic equation at `t` — read in the moving-foot
chart at `γ t` via `HasGeodesicEquationAt` — then the chart Gram squared speed
`s ↦ ⟨u'(s), u'(s)⟩`, where `u = chartLocalCurve γ t` is the chart image of `γ`
at the foot `γ t` and `⟨·,·⟩ = chartMetricInner g (γ t)`, has vanishing derivative
at `s = t`. This is do Carmo's computation
`d/dt⟨γ',γ'⟩ = 2⟨Dγ'/dt, γ'⟩ = 0`: it holds at each base time because the
covariant acceleration `Dγ'/dt = covariantDerivCoord g (γ t) u u'` of a geodesic
vanishes there, so the metric-compatibility product rule
`hasDerivAt_chartMetricInner_along` yields a zero derivative. -/
theorem hasDerivAt_chartMetricInner_geodesic_speed_zero
    (g : RiemannianMetric I M) [I.Boundaryless] {γ : ℝ → M} {t : ℝ}
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) :
    HasDerivAt (fun s => chartMetricInner (I := I) g (γ t)
        (Geodesic.chartLocalCurve (I := I) γ t s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)) 0 t := by
  classical
  set u : ℝ → E := Geodesic.chartLocalCurve (I := I) γ t with hu_def
  obtain ⟨v, a, hv_deriv, _h_ev, ha_deriv, hgeo_eq⟩ := hgeo
  -- regularity of the chart curve and its velocity at `t`
  have hu : DifferentiableAt ℝ u t := hv_deriv.differentiableAt
  have hV : DifferentiableAt ℝ (deriv u) t := ha_deriv.differentiableAt
  have hderiv_u : deriv u t = v := hv_deriv.deriv
  have hderiv2_u : deriv (deriv u) t = a := ha_deriv.deriv
  have hut : u t = extChartAt I (γ t) (γ t) := by
    rw [hu_def, Geodesic.chartLocalCurve_def]
  -- differentiability of the Gram coefficients at the base point
  have hy : extChartAt I (γ t) (γ t) ∈ (extChartAt I (γ t)).target :=
    (extChartAt I (γ t)).map_source (mem_extChartAt_source (I := I) (γ t))
  have hG : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g (γ t) i j) (u t) := by
    intro i j
    rw [hut]
    exact ((chartGramOnE_contDiffOn (I := I) g (γ t) i j).contDiffAt
      (extChartAt_target_mem_nhds' (I := I) hy)).differentiableAt (by norm_num)
  -- base-set membership for the metric-compatibility product rule
  have hbase : (extChartAt I (γ t)).symm (u t) ∈
      (trivializationAt E (TangentSpace I) (γ t)).baseSet := by
    rw [hut, (extChartAt I (γ t)).left_inv (mem_extChartAt_source (I := I) (γ t))]
    exact FiberBundle.mem_baseSet_trivializationAt' (γ t)
  -- covariant acceleration of the geodesic vanishes at `t`
  have hcov : covariantDerivCoord (I := I) g (γ t) u (deriv u) t = 0 := by
    rw [covariantDerivCoord_def, hderiv2_u, hderiv_u, hut]
    exact hgeo_eq
  -- metric-compatibility product rule with `V = W = u'`, whose derivative reduces to
  -- `⟨Du'/dt, u'⟩ + ⟨u', Du'/dt⟩ = 0`
  refine (hasDerivAt_chartMetricInner_along (I := I) g (γ t) u (deriv u) (deriv u)
    hu hV hV hG hbase).congr_deriv ?_
  rw [hcov]
  simp [chartMetricInner_def]

/-! ## Uniqueness of the covariant derivative along a curve (do Carmo Prop. 2.2)

do Carmo's Proposition 2.2 asserts that the covariant derivative `D/dt` is the
*unique* correspondence on vector fields along a curve satisfying (a) additivity,
(b) the Leibniz rule, and (c) the induced-field rule `D(Y∘u)/dt = (∇_{u̇}Y)(u)`. The
existence half is `covariantDerivCoord` together with `covariantDerivCoord_add` (a),
`covariantDerivCoord_smul` (b) and `covariantDerivCoord_induced` (c). The theorem
below is the uniqueness half: any operator `D` obeying (a), (b), (c) is forced to be
`covariantDerivCoord`, which is do Carmo's formula (1). -/

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (uniqueness half / formula (1)). Let `D` be
any operator sending a coordinate vector field along `u` to another such field,
satisfying do Carmo's three axioms:
* (a) additivity `D(V + W) = D V + D W`;
* (b) the Leibniz rule `D(f • V) = ḟ • V + f • D V` for scalar `f : ℝ → ℝ`;
* (c) the induced-field rule `D(Y ∘ u) = (∇_{u̇} Y)(u) = chartCovariantDeriv`.
Then `D V = covariantDerivCoord g α u V` for every differentiable `V`, i.e. `D` is
forced to be the covariant derivative of formula (1). This is the uniqueness
statement of do Carmo Prop. 2.2, obtained by expanding `V = ∑_k V^k e_k` in the
chart-model basis and applying (a), (b) to the components and (c) to each constant
frame field. -/
theorem covariantDerivCoord_unique (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (D : (ℝ → E) → ℝ → E)
    (hadd : ∀ V W : ℝ → E, (∀ t, DifferentiableAt ℝ V t) → (∀ t, DifferentiableAt ℝ W t) →
      D (V + W) = D V + D W)
    (hsmul : ∀ (f : ℝ → ℝ) (V : ℝ → E), (∀ t, DifferentiableAt ℝ f t) →
      (∀ t, DifferentiableAt ℝ V t) →
      D (f • V) = fun t => deriv f t • V t + f t • D V t)
    (hc : ∀ (Y : E → E), (∀ y, DifferentiableAt ℝ Y y) →
      D (fun s => Y (u s)) = fun t => chartCovariantDeriv (I := I) g α (deriv u t) (u t) Y)
    (V : ℝ → E) (hV : ∀ t, DifferentiableAt ℝ V t) :
    D V = covariantDerivCoord (I := I) g α u V := by
  classical
  -- component functions `c k = V^k` and constant frame fields `e k`
  set c : Fin (Module.finrank ℝ E) → ℝ → ℝ :=
    fun k s => Geodesic.chartCoord (E := E) k (V s) with hc_def
  set e : Fin (Module.finrank ℝ E) → ℝ → E :=
    fun k _ => Module.finBasis ℝ E k with he_def
  set F : Fin (Module.finrank ℝ E) → ℝ → E := fun k => c k • e k with hF_def
  -- component functions are differentiable (linear image of `V`)
  have hck : ∀ k, ∀ t, DifferentiableAt ℝ (c k) t := by
    intro k t
    exact (Geodesic.chartCoordFunctional (E := E) k).differentiableAt.comp t (hV t)
  have hek : ∀ k, ∀ t, DifferentiableAt ℝ (e k) t := fun k t => differentiableAt_const _
  have hFk : ∀ k, ∀ t, DifferentiableAt ℝ (F k) t := by
    intro k t
    exact ((hck k t).smul (hek k t))
  -- derivative of a component: `(c k)' = k-th coordinate of V'`
  have hderiv_ck : ∀ k t, deriv (c k) t = Geodesic.chartCoord (E := E) k (deriv V t) := by
    intro k t
    have hd : HasDerivAt (c k) (Geodesic.chartCoordFunctional (E := E) k (deriv V t)) t := by
      simpa only [hc_def, Function.comp_def] using
        (Geodesic.chartCoordFunctional (E := E) k).hasFDerivAt.comp_hasDerivAt t (hV t).hasDerivAt
    rw [hd.deriv, Geodesic.chartCoordFunctional_apply]
  -- each summand `F k s = V^k(s) • e_k`
  have hFks : ∀ k s, F k s = Geodesic.chartCoord (E := E) k (V s) • Module.finBasis ℝ E k := by
    intro k s; rw [hF_def]; simp only [hc_def, he_def, Pi.smul_apply']
  -- `V = ∑ k, F k`
  have hVrepr : V = ∑ k, F k := by
    funext s
    rw [Finset.sum_apply]
    have hr : (∑ k, Geodesic.chartCoord (E := E) k (V s) • Module.finBasis ℝ E k) = V s := by
      simpa only [Geodesic.chartCoord_def] using (Module.finBasis ℝ E).sum_repr (V s)
    rw [← hr]
    exact Finset.sum_congr rfl fun k _ => (hFks k s).symm
  -- `D 0 = 0`
  have hD0 : D (0 : ℝ → E) = 0 := by
    have h := hsmul (fun _ => (0 : ℝ)) V (fun _ => differentiableAt_const _) hV
    have hz : ((fun _ => (0 : ℝ)) : ℝ → ℝ) • V = (0 : ℝ → E) := by funext s; simp
    rw [hz] at h
    rw [h]; funext t; simp
  -- finite additivity of `D` over a Finset sum of differentiable fields
  have hDsum : ∀ (s : Finset (Fin (Module.finrank ℝ E))),
      D (∑ k ∈ s, F k) = ∑ k ∈ s, D (F k) := by
    intro s
    induction s using Finset.induction with
    | empty => simpa using hD0
    | insert a s ha ih =>
        have hsumdiff : ∀ t, DifferentiableAt ℝ (∑ k ∈ s, F k) t := by
          intro t
          have := DifferentiableAt.sum (u := s) (fun k _ => (hFk k t))
          simpa only [Finset.sum_apply] using this
        rw [Finset.sum_insert ha, Finset.sum_insert ha,
          hadd (F a) (∑ k ∈ s, F k) (hFk a) hsumdiff, ih]
  -- value of `D` on each constant frame field, via property (c)
  have hDe : ∀ k, D (e k) = fun t => Geodesic.chartChristoffelContraction (I := I) g α
      (deriv u t) (Module.finBasis ℝ E k) (u t) := by
    intro k
    have hek_eq : e k = fun s => (fun _ : E => Module.finBasis ℝ E k) (u s) := by rw [he_def]
    rw [hek_eq, hc (fun _ => Module.finBasis ℝ E k) (fun _ => differentiableAt_const _)]
    funext t
    rw [chartCovariantDeriv_def, (hasFDerivAt_const (Module.finBasis ℝ E k) (u t)).fderiv,
      ContinuousLinearMap.zero_apply, zero_add]
  -- value of `D` on each summand, via the Leibniz rule (b)
  have hDF : ∀ k, D (F k) = fun t => deriv (c k) t • Module.finBasis ℝ E k
      + c k t • Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
          (Module.finBasis ℝ E k) (u t) := by
    intro k
    rw [hF_def]
    simp only
    rw [hsmul (c k) (e k) (hck k) (hek k), hDe k]
  -- assemble
  have hDV : D V = ∑ k, D (F k) := by rw [hVrepr]; exact hDsum Finset.univ
  rw [hDV]
  funext t
  rw [Finset.sum_apply]
  have hDFt : ∀ k, D (F k) t = deriv (c k) t • Module.finBasis ℝ E k
      + c k t • Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
          (Module.finBasis ℝ E k) (u t) := fun k => congrFun (hDF k) t
  simp_rw [hDFt]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ k, deriv (c k) t • Module.finBasis ℝ E k) = deriv V t := by
    have hrepr := (Module.finBasis ℝ E).sum_repr (deriv V t)
    calc (∑ k, deriv (c k) t • Module.finBasis ℝ E k)
        = ∑ k, Geodesic.chartCoord (E := E) k (deriv V t) • Module.finBasis ℝ E k := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hderiv_ck k t]
      _ = deriv V t := by
          simpa only [Geodesic.chartCoord_def] using hrepr
  have h2 : (∑ k, c k t • Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
        (Module.finBasis ℝ E k) (u t))
      = Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t) := by
    have hVt : V t = ∑ k, c k t • Module.finBasis ℝ E k := by
      have hr : (∑ k, Geodesic.chartCoord (E := E) k (V t) • Module.finBasis ℝ E k) = V t := by
        simpa only [Geodesic.chartCoord_def] using (Module.finBasis ℝ E).sum_repr (V t)
      rw [hc_def]; exact hr.symm
    calc (∑ k, c k t • Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (Module.finBasis ℝ E k) (u t))
        = ∑ k, chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)
            (c k t • Module.finBasis ℝ E k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_smul, chartChristoffelContractionRight_apply]
      _ = chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)
            (∑ k, c k t • Module.finBasis ℝ E k) := by rw [map_sum]
      _ = Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (V t) (u t) := by
          rw [← hVt, chartChristoffelContractionRight_apply]
  rw [h1, h2, covariantDerivCoord_def]

/-! ## Metric compatibility (do Carmo Ch. 2, §3, Def. 3.1) -/

/-- **Math.** do Carmo Ch. 2, §3, Def. 3.1 (coordinate form). An affine connection,
read in the chart at `α` through its covariant derivative along curves
`covariantDerivCoord`, is **compatible with the metric** when, for every coordinate
curve `u` and every pair of **parallel** coordinate vector fields `V, W` along `u`,
the chart Gram inner product `⟨V, W⟩` is *constant* along `u`. This is do Carmo's
original definition of metric compatibility (Def. 3.1), as opposed to the equivalent
product-rule form (eq. (4), `AffineConnection.IsMetricCompatible`). -/
def IsMetricCompatibleCoord (g : RiemannianMetric I M) (α : M) : Prop :=
  ∀ (u V W : ℝ → E), IsParallelCoord (I := I) g α u V → IsParallelCoord (I := I) g α u W →
    ∀ s t, chartMetricInner (I := I) g α (u s) (V s) (W s)
         = chartMetricInner (I := I) g α (u t) (V t) (W t)

/-! ## do Carmo Ch. 2, §3, Prop. 3.2: compatibility ⟺ the product rule

do Carmo's Proposition 3.2 is the equivalence, for an affine connection `∇` on a
Riemannian manifold, between metric compatibility (Def. 3.1: parallel fields have
constant inner product) and the product rule (eq. (3),
`d/dt⟨V,W⟩ = ⟨DV/dt,W⟩ + ⟨V,DW/dt⟩`). We record it abstractly in coordinates: a
connection read along a curve is a continuous coefficient `A : ℝ → E →L[ℝ] E`
(`DV/dt = V̇ + A(t)V`), the metric read along the curve is a curve of bilinear forms
`G : ℝ → E →L[ℝ] E →L[ℝ] ℝ`, and the equivalence holds provided parallel transport is
surjective onto each fibre (do Carmo Prop. 2.6, the hypothesis do Carmo's own proof
invokes to build a parallel orthonormal frame). -/

/-- **Math.** General coordinate covariant derivative along a curve for a connection
coefficient `A : ℝ → E →L[ℝ] E`: `DV/dt = V̇(t) + A(t)·V(t)`. Specializes to
`covariantDerivCoord` for the Levi-Civita coefficient `A(t) = Γ(u̇(t),·)(u(t))`. -/
def covDerivGen (A : ℝ → E →L[ℝ] E) (V : ℝ → E) (t : ℝ) : E := deriv V t + A t (V t)

/-- **Math.** do Carmo Def. 2.5 (general coefficient form). `V` is **parallel** for the
connection coefficient `A` when `V̇ = −A V`, i.e. `DV/dt ≡ 0`. -/
def IsParallelGen (A : ℝ → E →L[ℝ] E) (V : ℝ → E) : Prop := ∀ t, HasDerivAt V (-(A t) (V t)) t

/-- **Math.** do Carmo §3, Def. 3.1 (general coefficient form). The connection `A` is
**compatible** with the metric curve `G` when any two parallel fields have constant
inner product `t ↦ G t (V t) (W t)`. -/
def CompatibleGen (A : ℝ → E →L[ℝ] E) (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ V W : ℝ → E, IsParallelGen A V → IsParallelGen A W →
    ∀ s t, G s (V s) (W s) = G t (V t) (W t)

/-- **Math.** do Carmo §3, eq. (3) (general coefficient form). The **product rule**:
for all fields `V, W` along the curve,
`d/dt (G(V,W)) = G(DV/dt, W) + G(V, DW/dt)`. -/
def ProductRuleGen (A : ℝ → E →L[ℝ] E) (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ V W : ℝ → E, (∀ t, DifferentiableAt ℝ V t) → (∀ t, DifferentiableAt ℝ W t) →
    ∀ t, HasDerivAt (fun s => G s (V s) (W s))
      (G t (covDerivGen A V t) (W t) + G t (V t) (covDerivGen A W t)) t

/-- **Math.** Product rule for the bilinear pairing `t ↦ G t (V t) (W t)` of a curve
of bilinear forms `G` with two vector curves `V, W`: its derivative is
`Ġ(V,W) + G(V̇,W) + G(V,Ẇ)`, obtained by applying `HasDerivAt.clm_apply` twice. -/
theorem hasDerivAt_bilin_along (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (hG : Differentiable ℝ G)
    (V W : ℝ → E) {t : ℝ} (hV : DifferentiableAt ℝ V t) (hW : DifferentiableAt ℝ W t) :
    HasDerivAt (fun s => G s (V s) (W s))
      (deriv G t (V t) (W t) + G t (deriv V t) (W t) + G t (V t) (deriv W t)) t := by
  have hGV : HasDerivAt (fun s => G s (V s)) (deriv G t (V t) + G t (deriv V t)) t :=
    (hG t).hasDerivAt.clm_apply hV.hasDerivAt
  have h2 := hGV.clm_apply hW.hasDerivAt
  simpa only [ContinuousLinearMap.add_apply, add_assoc] using h2

/-- **Math.** The pointwise metric-connection compatibility identity
`Ġ(a,b) = G(A a, b) + G(a, A b)`, do Carmo's coordinate form of `∇g = 0`. Both metric
compatibility (Def. 3.1) and the product rule (eq. (3)) are equivalent to this. -/
def PointwiseCompatGen (A : ℝ → E →L[ℝ] E) (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ) : Prop :=
  ∀ t a b, deriv G t a b = G t (A t a) b + G t a (A t b)

/-- **Math.** The product rule (eq. (3)) is equivalent to the pointwise compatibility
identity `Ġ(a,b) = G(Aa,b) + G(a,Ab)`: the derivative of `G(V,W)` computed by
`hasDerivAt_bilin_along` matches `G(DV,W) + G(V,DW)` iff the `Ġ` term equals the two
Christoffel terms, tested against constant fields to reach every pair `(a,b)`. -/
theorem productRuleGen_iff_pointwise (A : ℝ → E →L[ℝ] E) (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hG : Differentiable ℝ G) :
    ProductRuleGen A G ↔ PointwiseCompatGen A G := by
  constructor
  · intro hPR t a b
    have hV : ∀ s, DifferentiableAt ℝ (fun _ : ℝ => a) s := fun s => differentiableAt_const _
    have hW : ∀ s, DifferentiableAt ℝ (fun _ : ℝ => b) s := fun s => differentiableAt_const _
    have hpr := hPR (fun _ => a) (fun _ => b) hV hW t
    have hbil := hasDerivAt_bilin_along G hG (fun _ => a) (fun _ => b) (hV t) (hW t)
    have hda : deriv (fun _ : ℝ => a) t = 0 := deriv_const t a
    have hdb : deriv (fun _ : ℝ => b) t = 0 := deriv_const t b
    have hcov : covDerivGen A (fun _ => a) t = A t a := by
      simp only [covDerivGen, hda, zero_add]
    have hcov' : covDerivGen A (fun _ => b) t = A t b := by
      simp only [covDerivGen, hdb, zero_add]
    rw [hcov, hcov'] at hpr
    have huniq := hbil.unique hpr
    simpa only [hda, hdb, map_zero, ContinuousLinearMap.zero_apply, add_zero, zero_add]
      using huniq
  · intro hPC V W hV hW t
    have hbil := hasDerivAt_bilin_along G hG V W (hV t) (hW t)
    refine hbil.congr_deriv ?_
    have h := hPC t (V t) (W t)
    simp only [covDerivGen, map_add, ContinuousLinearMap.add_apply]
    rw [h]
    ring

/-- **Math.** Metric compatibility (Def. 3.1) is equivalent to the pointwise identity,
given surjectivity of parallel transport onto each fibre (do Carmo Prop. 2.6): every
value `a` at every time `t` is realized by a parallel field. The forward direction is
do Carmo's argument that constancy of `G(P,P')` along parallel `P, P'` forces
`Ġ = G(A·,·) + G(·,A·)`; the reverse says a vanishing derivative gives constancy. -/
theorem compatibleGen_iff_pointwise (A : ℝ → E →L[ℝ] E) (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ)
    (hG : Differentiable ℝ G)
    (hpar : ∀ t a, ∃ P, IsParallelGen A P ∧ P t = a) :
    CompatibleGen A G ↔ PointwiseCompatGen A G := by
  constructor
  · intro hCompat t a b
    obtain ⟨P, hP, hPa⟩ := hpar t a
    obtain ⟨Q, hQ, hQb⟩ := hpar t b
    have hPd : ∀ s, DifferentiableAt ℝ P s := fun s => (hP s).differentiableAt
    have hQd : ∀ s, DifferentiableAt ℝ Q s := fun s => (hQ s).differentiableAt
    have hbil := hasDerivAt_bilin_along G hG P Q (hPd t) (hQd t)
    have hconst : (fun s => G s (P s) (Q s)) = fun _ => G t (P t) (Q t) :=
      funext fun s => hCompat P Q hP hQ s t
    have hzero : HasDerivAt (fun s => G s (P s) (Q s)) 0 t := by
      rw [hconst]; exact hasDerivAt_const t _
    have huniq := hbil.unique hzero
    have hdP : deriv P t = -(A t) (P t) := (hP t).deriv
    have hdQ : deriv Q t = -(A t) (Q t) := (hQ t).deriv
    rw [hdP, hdQ, hPa, hQb] at huniq
    simp only [map_neg, ContinuousLinearMap.neg_apply] at huniq
    linarith [huniq]
  · intro hPC V W hVp hWp s t
    have hVd : ∀ r, DifferentiableAt ℝ V r := fun r => (hVp r).differentiableAt
    have hWd : ∀ r, DifferentiableAt ℝ W r := fun r => (hWp r).differentiableAt
    have hderiv0 : ∀ r, HasDerivAt (fun x => G x (V x) (W x)) 0 r := by
      intro r
      have hbil := hasDerivAt_bilin_along G hG V W (hVd r) (hWd r)
      refine hbil.congr_deriv ?_
      have h := hPC r (V r) (W r)
      have hdV : deriv V r = -(A r) (V r) := (hVp r).deriv
      have hdW : deriv W r = -(A r) (W r) := (hWp r).deriv
      rw [hdV, hdW, h]
      simp only [map_neg, ContinuousLinearMap.neg_apply]
      ring
    have hdiff : Differentiable ℝ (fun x => G x (V x) (W x)) := fun r => (hderiv0 r).differentiableAt
    have : (fun x => G x (V x) (W x)) s = (fun x => G x (V x) (W x)) t :=
      is_const_of_deriv_eq_zero hdiff (fun r => (hderiv0 r).deriv) s t
    exact this

/-- **Math.** do Carmo Ch. 2, §3, Prop. 3.2 (coordinate form). A connection `A` on a
Riemannian manifold, read along curves, is **compatible with the metric** `G`
(Def. 3.1: parallel fields have constant inner product) **if and only if** the
**product rule** (eq. (3)) `d/dt G(V,W) = G(DV/dt,W) + G(V,DW/dt)` holds for all fields
`V, W`. The hypothesis `hpar` is do Carmo's parallel-transport existence (Prop. 2.6),
which his proof uses to extend an orthonormal basis to a parallel frame. -/
theorem compatibleGen_iff_productRuleGen (A : ℝ → E →L[ℝ] E)
    (G : ℝ → E →L[ℝ] E →L[ℝ] ℝ) (hG : Differentiable ℝ G)
    (hpar : ∀ t a, ∃ P, IsParallelGen A P ∧ P t = a) :
    CompatibleGen A G ↔ ProductRuleGen A G := by
  rw [compatibleGen_iff_pointwise A G hG hpar, productRuleGen_iff_pointwise A G hG]

end Riemannian

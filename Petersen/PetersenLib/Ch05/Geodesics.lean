import OpenGALib.Riemannian.Geodesic.MaximalInterval
import OpenGALib.Riemannian.Geodesic.Homogeneity
import OpenGALib.Riemannian.Geodesic.InitialVelocity
import OpenGALib.Riemannian.Geodesic.CovariantDerivative

/-!
# Petersen Ch. 5, §5.2 — Geodesics (GTM 171, 3rd ed.)

Petersen's definitions for §5.2: the acceleration of a curve, the geodesic
equation in coordinates, geodesics, and geodesic completeness
(`def:pet-ch5-acceleration`, `def:pet-ch5-geodesic`,
`def:pet-ch5-geodesically-complete`).

The chapter's convention (following the chart-local pipeline vendored from the
do Carmo project in `PetersenLib/Vendored/OpenGA/Geodesic/`) represents a curve
as a total map `γ : ℝ → M`, restricted to a set of times where a property is
asserted. At each base time `t` the acceleration is read in the canonical chart
centred at the foot point `γ t`:

* `curveAcceleration g γ t` — Petersen's `c̈`: the coordinate second derivative
  of the chart reading `u = φ_{γ t} ∘ γ` corrected by the Christoffel
  contraction, `ü(t) + Γ_{γ t}(u̇(t), u̇(t))(u(t))`, viewed in
  `TangentSpace I (γ t)`. This is Petersen's coordinate formula
  `c̈ = (d²cᵏ/dt² + (dcˡ/dt)(dcʲ/dt) Γᵏ_{lj}) ∂ₖ` at the foot chart.
* `geodesicCoordinateEquation g γ t` — the second-order geodesic ODE
  `ü(t) = -Γ_{γ t}(u̇(t), u̇(t))(u(t))` of Petersen (5.2).
* `IsGeodesic g γ` — Petersen's geodesic: the moving-foot geodesic equation
  `Geodesic.HasGeodesicEquationAt g γ t` (which packages the C² regularity of
  the chart reading at `t` together with the vanishing of the acceleration)
  holds at every time.  The interval-restricted variant is
  `Geodesic.IsGeodesicOn g γ s`.
* `IsGeodesicallyComplete g` — Petersen's geodesic completeness: every initial
  datum `(p, v)` is realised by a geodesic defined on all of `ℝ`
  (equivalently, by uniqueness, every maximal geodesic is defined on all of
  `ℝ`).

The bridges `hasGeodesicEquationAt_iff_curveAcceleration` and
`curveAcceleration_eq_zero_iff` record that these definitions agree with the
vendored spray pipeline, and `isGeodesic_constant_speed_deriv` is the
constant-speed property from `def:pet-ch5-geodesic`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace PetersenLib

open Riemannian Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-acceleration`): the **acceleration**
`c̈` of a curve `γ : ℝ → M` at time `t`, read in the canonical chart at the foot
point `γ t`.  With `u := φ_{γ t} ∘ γ` the chart reading of the curve, the
acceleration is the Christoffel-corrected coordinate second derivative
`ü(t) + Γ_{γ t}(u̇(t), u̇(t))(u(t))`, Petersen's
`c̈ = (d²cᵏ/dt² + (dcˡ/dt)(dcʲ/dt)Γᵏ_{lj}) ∂ₖ`, regarded as a tangent vector at
`γ t` via the chart-`γ t` trivialisation (`TangentSpace I (γ t)` is
definitionally `E`, coordinatised by the chart at `γ t`). -/
def curveAcceleration (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    TangentSpace I (γ t) :=
  (deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t +
    Geodesic.chartChristoffelContraction (I := I) g (γ t)
      (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
      (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
      (extChartAt I (γ t) (γ t)) : E)

@[simp] lemma curveAcceleration_def (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    curveAcceleration (I := I) g γ t =
      (deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t +
        Geodesic.chartChristoffelContraction (I := I) g (γ t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (extChartAt I (γ t) (γ t)) : E) := rfl

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-geodesic`): the **geodesic equation in
local coordinates** at base time `t`, `ü(t) = -Γ_{γ t}(u̇(t), u̇(t))(u(t))` for
the chart reading `u = φ_{γ t} ∘ γ` at the foot point — Petersen's second-order
system `c̈ᵏ(t) = -ċˡ(t) ċʲ(t) Γᵏ_{lj}|_{c(t)}`. -/
def geodesicCoordinateEquation (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : Prop :=
  deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t =
    - Geodesic.chartChristoffelContraction (I := I) g (γ t)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
        (extChartAt I (γ t) (γ t))

/-- **Math.** The acceleration of a curve vanishes at `t` iff the coordinate
geodesic equation holds at `t`: `c̈ = 0 ↔ ü = -Γ(u̇, u̇)(u)`. -/
lemma curveAcceleration_eq_zero_iff (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    curveAcceleration (I := I) g γ t = 0 ↔
      geodesicCoordinateEquation (I := I) g γ t := by
  rw [geodesicCoordinateEquation]
  constructor
  · intro h
    have h' : deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t +
        Geodesic.chartChristoffelContraction (I := I) g (γ t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (extChartAt I (γ t) (γ t)) = (0 : E) := h
    linear_combination (norm := module) h'
  · intro h
    show deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t +
        Geodesic.chartChristoffelContraction (I := I) g (γ t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (extChartAt I (γ t) (γ t)) = (0 : E)
    rw [h]
    simp

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-geodesic`): a curve `γ : ℝ → M` is a
**geodesic** when it has vanishing acceleration, `c̈ = 0`, at every time — in the
form of the moving-foot geodesic equation `Geodesic.HasGeodesicEquationAt g γ t`
(which packages the required C² regularity of the chart reading at `t` together
with the vanishing of `curveAcceleration`; see
`hasGeodesicEquationAt_iff_curveAcceleration`).  The interval-restricted variant
is `Geodesic.IsGeodesicOn g γ s`. -/
def IsGeodesic (g : RiemannianMetric I M) (γ : ℝ → M) : Prop :=
  ∀ t : ℝ, Geodesic.HasGeodesicEquationAt (I := I) g γ t

lemma isGeodesic_iff (g : RiemannianMetric I M) (γ : ℝ → M) :
    IsGeodesic (I := I) g γ ↔ Geodesic.IsGeodesic (I := I) g γ :=
  Iff.rfl

/-- **Math.** The moving-foot geodesic equation at `t` holds iff the chart reading
`u = φ_{γ t} ∘ γ` is C²-regular at `t` (differentiable near `t`, with `u̇`
differentiable at `t`) and the acceleration vanishes at `t`.  This identifies
Petersen's definition (vanishing acceleration of a `C^∞` curve) with the
vendored spray pipeline's `Geodesic.HasGeodesicEquationAt`. -/
lemma hasGeodesicEquationAt_iff_curveAcceleration
    (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    Geodesic.HasGeodesicEquationAt (I := I) g γ t ↔
      ((∀ᶠ s in 𝓝 t, HasDerivAt (Geodesic.chartLocalCurve (I := I) γ t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) s) s) ∧
        DifferentiableAt ℝ (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t) ∧
      curveAcceleration (I := I) g γ t = 0 := by
  constructor
  · rintro ⟨v, a, hv, hev, ha, heq⟩
    refine ⟨⟨hev, ha.differentiableAt⟩, ?_⟩
    show deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t +
        Geodesic.chartChristoffelContraction (I := I) g (γ t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (deriv (Geodesic.chartLocalCurve (I := I) γ t) t)
          (extChartAt I (γ t) (γ t)) = (0 : E)
    rw [ha.deriv, hv.deriv]
    exact heq
  · rintro ⟨⟨hev, hd⟩, hacc⟩
    exact ⟨deriv (Geodesic.chartLocalCurve (I := I) γ t) t,
      deriv (deriv (Geodesic.chartLocalCurve (I := I) γ t)) t,
      hev.self_of_nhds, hev, hd.hasDerivAt, hacc⟩

/-- **Math.** A geodesic has vanishing acceleration at every time (projection of
the definition through `hasGeodesicEquationAt_iff_curveAcceleration`). -/
lemma IsGeodesic.curveAcceleration_eq_zero {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (t : ℝ) :
    curveAcceleration (I := I) g γ t = 0 :=
  ((hasGeodesicEquationAt_iff_curveAcceleration (I := I) g γ t).mp (hγ t)).2

/-- **Math.** A geodesic satisfies the coordinate geodesic equation at every time. -/
lemma IsGeodesic.geodesicCoordinateEquation {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (t : ℝ) :
    geodesicCoordinateEquation (I := I) g γ t :=
  (curveAcceleration_eq_zero_iff (I := I) g γ t).mp (hγ.curveAcceleration_eq_zero t)

/-- **Math.** The moving-foot geodesic equation at `t` is **local**: it transfers
between curves that agree near `t`.  (The equation at `t` only reads the curve
through the chart at its own foot on a neighbourhood of `t`.) -/
theorem hasGeodesicEquationAt_congr {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M}
    {t : ℝ} (heq : γ₁ =ᶠ[𝓝 t] γ₂)
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ₁ t) :
    Geodesic.HasGeodesicEquationAt (I := I) g γ₂ t := by
  obtain ⟨v, a, hv, hev, ha, hgeo⟩ := h
  have hpt : γ₁ t = γ₂ t := heq.self_of_nhds
  have hcurve : Geodesic.chartLocalCurve (I := I) γ₁ t =ᶠ[𝓝 t]
      Geodesic.chartLocalCurve (I := I) γ₂ t := by
    filter_upwards [heq] with s hs
    show extChartAt I (γ₁ t) (γ₁ s) = extChartAt I (γ₂ t) (γ₂ s)
    rw [hs, hpt]
  have hderiv : deriv (Geodesic.chartLocalCurve (I := I) γ₁ t) =ᶠ[𝓝 t]
      deriv (Geodesic.chartLocalCurve (I := I) γ₂ t) := hcurve.deriv
  refine ⟨v, a, hv.congr_of_eventuallyEq hcurve.symm, ?_,
    ha.congr_of_eventuallyEq hderiv.symm, ?_⟩
  · filter_upwards [hev, hcurve.eventually_nhds, hderiv] with s h1 h2 h3
    have h2' : Geodesic.chartLocalCurve (I := I) γ₁ t =ᶠ[𝓝 s]
        Geodesic.chartLocalCurve (I := I) γ₂ t := h2
    rw [← h3]
    exact h1.congr_of_eventuallyEq h2'.symm
  · rw [← hpt]
    exact hgeo

/-- **Math.** The geodesic property on an open time set transfers between curves
that agree on it. -/
theorem isGeodesicOn_congr_of_eqOn {g : RiemannianMetric I M} {γ₁ γ₂ : ℝ → M}
    {J : Set ℝ} (hJ : IsOpen J) (heq : Set.EqOn γ₁ γ₂ J)
    (h : Geodesic.IsGeodesicOn (I := I) g γ₁ J) :
    Geodesic.IsGeodesicOn (I := I) g γ₂ J := fun t ht =>
  hasGeodesicEquationAt_congr
    (Filter.eventuallyEq_of_mem (hJ.mem_nhds ht) heq) (h t ht)

/-- **Math.** Petersen Ch. 5, §5.2: `γ` is a geodesic on `J` **with initial data
`(p, v)` attained at time `t₀`** — the initial-value-problem format of Petersen's
`c(t₀) = q`, `ċ(t₀) = v`: the curve is continuous on `J` (Petersen's curves are
smooth maps; the moving-foot geodesic equation alone does not control the
chart-junk values, so continuity is recorded explicitly), passes through `p` at
`t₀` with velocity `v` (read in the chart at `p`), and satisfies the geodesic
equation on `J`. -/
def IsGeodesicWithInitialOn (g : RiemannianMetric I M) (γ : ℝ → M) (J : Set ℝ)
    (t₀ : ℝ) (p : M) (v : TangentSpace I p) : Prop :=
  ContinuousOn γ J ∧ γ t₀ = p ∧ HasDerivAt (fun s => extChartAt I p (γ s)) (v : E) t₀ ∧
    Geodesic.IsGeodesicOn (I := I) g γ J

/-- **Math.** The initial-value-problem format restricts to smaller time sets. -/
lemma IsGeodesicWithInitialOn.mono {g : RiemannianMetric I M} {γ : ℝ → M}
    {J J' : Set ℝ} {t₀ : ℝ} {p : M} {v : TangentSpace I p}
    (h : IsGeodesicWithInitialOn (I := I) g γ J t₀ p v) (hJ' : J' ⊆ J) :
    IsGeodesicWithInitialOn (I := I) g γ J' t₀ p v :=
  ⟨h.1.mono hJ', h.2.1, h.2.2.1, h.2.2.2.mono hJ'⟩

section ConstantSpeed

variable [I.Boundaryless]

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-geodesic`, constant-speed clause): along
a curve satisfying the geodesic equation at `t`, the squared speed
`s ↦ g(u̇(s), u̇(s))` — read in the chart at the foot `γ t` via the chart Gram
pairing `chartMetricInner` — has vanishing derivative at `s = t`.  This is
Petersen's computation `d/dt g(ċ, ċ) = 2 g(c̈, ċ) = 0`: a geodesic is
parametrised proportionally to arc length. -/
theorem IsGeodesic.constantSpeed_deriv {g : RiemannianMetric I M} {γ : ℝ → M}
    (hγ : IsGeodesic (I := I) g γ) (t : ℝ) :
    HasDerivAt (fun s => chartMetricInner (I := I) g (γ t)
        (Geodesic.chartLocalCurve (I := I) γ t s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)
        (deriv (Geodesic.chartLocalCurve (I := I) γ t) s)) 0 t :=
  hasDerivAt_chartMetricInner_geodesic_speed_zero (I := I) g (hγ t)

end ConstantSpeed

section Completeness

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-geodesically-complete`): a Riemannian
manifold `(M, g)` is **geodesically complete** when every geodesic is defined
for all time; equivalently (via uniqueness of geodesics), every initial datum
`(p, v)` is realised by a (continuous) geodesic `γ : ℝ → M` with `γ 0 = p` and
initial velocity `v` — read in the chart at `p` — defined on all of `ℝ`. -/
def IsGeodesicallyComplete (g : RiemannianMetric I M) : Prop :=
  ∀ (p : M) (v : TangentSpace I p), ∃ γ : ℝ → M, Continuous γ ∧ γ 0 = p ∧
    HasDerivAt (fun s => extChartAt I p (γ s)) (v : E) 0 ∧
    IsGeodesic (I := I) g γ

end Completeness

section Homogeneity

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-exponential-map`, homogeneity property —
equation-level core): the geodesic equation is covariant under affine
reparametrisation `s ↦ a s`.  If `γ` satisfies the moving-foot geodesic equation
at time `a * t`, then `s ↦ γ (a * s)` satisfies it at time `t`: velocities scale
by `a`, accelerations and the (quadratic) Christoffel term by `a²`.  This is the
computational heart of `c_{a v}(t) = c_v(a t)`. -/
theorem hasGeodesicEquationAt_comp_const_mul (g : RiemannianMetric I M)
    {γ : ℝ → M} (a : ℝ) {t : ℝ}
    (hγ : Geodesic.HasGeodesicEquationAt (I := I) g γ (a * t)) :
    Geodesic.HasGeodesicEquationAt (I := I) g (fun s => γ (a * s)) t := by
  obtain ⟨v, b, hv, hev, hb, heq⟩ := hγ
  -- the chart at the foot of the reparametrised curve at `t` is the chart at
  -- `γ (a * t)`, so the chart reading is `u ∘ (a * ·)` for `u` the chart reading
  -- of `γ` at base time `a * t`
  set u : ℝ → E := Geodesic.chartLocalCurve (I := I) γ (a * t) with hu_def
  have hcurve : Geodesic.chartLocalCurve (I := I) (fun s => γ (a * s)) t =
      fun s => u (a * s) := rfl
  have hlin : ∀ s : ℝ, HasDerivAt (fun y : ℝ => a * y) a s := fun s => by
    simpa using (hasDerivAt_id s).const_mul a
  -- eventual differentiability of the rescaled chart reading, with derivative
  -- `a • u̇ (a s)`
  have hev' : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => u (a * s'))
      (a • deriv u (a * s)) s := by
    have hcont : Continuous fun s : ℝ => a * s := continuous_const.mul continuous_id
    have hmem : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u (a * s)) (a * s) :=
      (hcont.tendsto t).eventually hev
    filter_upwards [hmem] with s hs
    exact hs.scomp s (hlin s)
  -- identify the genuine derivative function of the rescaled reading
  have hderiv_eq : ∀ᶠ s in 𝓝 t, deriv (fun s' => u (a * s')) s =
      a • deriv u (a * s) := by
    filter_upwards [hev'] with s hs using hs.deriv
  refine ⟨a • v, (a * a) • b, ?_, ?_, ?_, ?_⟩
  · -- first derivative at `t`
    rw [hcurve]
    exact hv.scomp t (hlin t)
  · -- eventual differentiability with its own `deriv`
    rw [hcurve]
    filter_upwards [hev'] with s hs
    have h := hs
    rwa [← hs.deriv] at h
  · -- second derivative at `t`
    rw [hcurve]
    have hbb : HasDerivAt (fun s => a • deriv u (a * s)) ((a * a) • b) t := by
      have hb' : HasDerivAt (fun s => deriv u (a * s)) (a • b) t :=
        hb.scomp t (hlin t)
      simpa [smul_smul] using hb'.const_smul a
    exact hbb.congr_of_eventuallyEq hderiv_eq
  · -- the geodesic equation, using bilinearity of the Christoffel contraction
    show (a * a) • b + Geodesic.chartChristoffelContraction (I := I) g (γ (a * t))
        (a • v) (a • v) (extChartAt I (γ (a * t)) (γ (a * t))) = 0
    rw [Geodesic.chartChristoffelContraction_smul_smul (I := I) g (γ (a * t)) a v
      (extChartAt I (γ (a * t)) (γ (a * t))), ← smul_add, heq, smul_zero]

/-- **Math.** The geodesic equation is covariant under **time translation**
`s ↦ s - c`: if `γ` satisfies the moving-foot geodesic equation at time `t - c`,
then `s ↦ γ (s - c)` satisfies it at time `t`.  (Petersen §5.2: geodesics are
preserved by affine reparametrisation; the translation part.) -/
theorem hasGeodesicEquationAt_comp_sub_const (g : RiemannianMetric I M)
    {γ : ℝ → M} (c : ℝ) {t : ℝ}
    (hγ : Geodesic.HasGeodesicEquationAt (I := I) g γ (t - c)) :
    Geodesic.HasGeodesicEquationAt (I := I) g (fun s => γ (s - c)) t := by
  obtain ⟨v, b, hv, hev, hb, heq⟩ := hγ
  set u : ℝ → E := Geodesic.chartLocalCurve (I := I) γ (t - c) with hu_def
  have hcurve : Geodesic.chartLocalCurve (I := I) (fun s => γ (s - c)) t =
      fun s => u (s - c) := rfl
  have hlin : ∀ s : ℝ, HasDerivAt (fun y : ℝ => y - c) 1 s := fun s =>
    (hasDerivAt_id s).sub_const c
  have hev' : ∀ᶠ s in 𝓝 t, HasDerivAt (fun s' => u (s' - c))
      (deriv u (s - c)) s := by
    have hcont : Continuous fun s : ℝ => s - c := continuous_id.sub continuous_const
    have hmem : ∀ᶠ s in 𝓝 t, HasDerivAt u (deriv u (s - c)) (s - c) :=
      (hcont.tendsto t).eventually hev
    filter_upwards [hmem] with s hs
    simpa using hs.scomp s (hlin s)
  have hderiv_eq : ∀ᶠ s in 𝓝 t, deriv (fun s' => u (s' - c)) s =
      deriv u (s - c) := by
    filter_upwards [hev'] with s hs using hs.deriv
  refine ⟨v, b, ?_, ?_, ?_, ?_⟩
  · rw [hcurve]
    simpa using hv.scomp t (hlin t)
  · rw [hcurve]
    filter_upwards [hev', hderiv_eq] with s hs hs'
    rwa [← hs'] at hs
  · rw [hcurve]
    have hbb : HasDerivAt (fun s => deriv u (s - c)) b t := by
      simpa using hb.scomp t (hlin t)
    exact hbb.congr_of_eventuallyEq hderiv_eq
  · exact heq

/-- **Math.** **Time translation of geodesics with initial data**: if `γ` is a
geodesic on `J` with initial data `(p, v)` at time `t₀`, then `s ↦ γ (s - c)`
is a geodesic on the translated time set `{s | s - c ∈ J}` with the same
initial data at time `t₀ + c`. -/
theorem IsGeodesicWithInitialOn.shift {g : RiemannianMetric I M} {γ : ℝ → M}
    {J : Set ℝ} {t₀ : ℝ} {p : M} {v : TangentSpace I p}
    (hγ : IsGeodesicWithInitialOn g γ J t₀ p v) (c : ℝ) :
    IsGeodesicWithInitialOn g (fun s => γ (s - c)) {s | s - c ∈ J} (t₀ + c) p v := by
  obtain ⟨hcont, hstart, hvel, hgeo⟩ := hγ
  have hsub : t₀ + c - c = t₀ := by ring
  refine ⟨?_, by simp [hsub, hstart], ?_, fun t ht => ?_⟩
  · exact hcont.comp ((continuous_id.sub continuous_const).continuousOn)
      fun s hs => hs
  · have hlin : HasDerivAt (fun y : ℝ => y - c) 1 (t₀ + c) :=
      (hasDerivAt_id (t₀ + c)).sub_const c
    have hvel' : HasDerivAt (fun s => extChartAt I p (γ s)) (v : E) (t₀ + c - c) := by
      rw [hsub]; exact hvel
    simpa using hvel'.scomp (t₀ + c) hlin
  · exact hasGeodesicEquationAt_comp_sub_const (I := I) g c (hgeo (t - c) ht)

/-- **Math.** Petersen Ch. 5 (`def:pet-ch5-exponential-map`, homogeneity property):
**homogeneity of geodesics**, `c_{a v}(t) = c_v(a t)`.  If `γ` is a geodesic on
`J` with initial data `(p, v)` at time `0`, then `s ↦ γ (a s)` is a geodesic on
`{s | a s ∈ J}` with initial data `(p, a • v)` at time `0`. -/
theorem geodesicHomogeneity (g : RiemannianMetric I M) {γ : ℝ → M} {J : Set ℝ}
    {p : M} {v : TangentSpace I p} (a : ℝ)
    (hγ : IsGeodesicWithInitialOn g γ J 0 p v) :
    IsGeodesicWithInitialOn g (fun s => γ (a * s)) {s | a * s ∈ J} 0 p (a • v) := by
  obtain ⟨hcont, hstart, hvel, hgeo⟩ := hγ
  refine ⟨?_, by simpa using hstart, ?_, fun t ht => ?_⟩
  · exact hcont.comp ((continuous_const.mul continuous_id).continuousOn)
      fun s hs => hs
  · have hlin : HasDerivAt (fun y : ℝ => a * y) a (0 : ℝ) := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul a
    have hvel' : HasDerivAt (fun s => extChartAt I p (γ s)) (v : E) (a * 0) := by
      simpa using hvel
    exact hvel'.scomp 0 hlin
  · exact hasGeodesicEquationAt_comp_const_mul (I := I) g a (hgeo (a * t) ht)

end Homogeneity

end PetersenLib

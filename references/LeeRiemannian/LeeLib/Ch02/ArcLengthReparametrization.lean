/-
Chapter 2, "Riemannian Metrics", §"The Riemannian Distance Function": Lee's
Proposition 2.49(a).

Lee's Proposition 2.49 states that every regular curve `γ` (a curve with
nowhere-vanishing velocity) in a Riemannian manifold admits a **unit-speed
forward reparametrization**: there is an increasing diffeomorphism onto its
image after which the curve has constant speed `1` and is parametrized by
arclength.

The whole point of this file is that the speed of a curve is an *intrinsic*
quantity, `|γ̇(t)|² = ⟨γ̇(t), γ̇(t)⟩_g`, so the three facts the reparametrization
argument needs come out cleanly, with no chart bookkeeping:

* `curveSpeedSq_nonneg` — the squared speed is nonnegative (positive
  semidefiniteness of the metric).
* `contDiffAt_curveSpeedSq` — the squared speed of a curve that is `C^∞` on an
  open time set is `C^∞` there.  This is `ContMDiff.inner_bundle` applied to the
  smooth velocity lift `t ↦ (γ t, γ̇ t)` into the tangent bundle, read through
  the model-space identification `ContMDiffAt ↔ ContDiffAt`.
* `curveSpeedSq_reparam` — the scaling law `|d(γ∘φ)/dt|² = φ'(t)² · |γ̇(φ t)|²`,
  by bilinearity of the metric and the chain rule `velocity_reparam`.

`intervalIntegrable_sqrt_curveSpeedSq` records that the arclength integrand
`t ↦ √|γ̇(t)|` is interval-integrable inside the open smoothness window
(continuity plus compactness), and `regularCurve_arclengthReparametrization` is
Lee's Proposition 2.49(a) itself: the arclength function `φ(t) = L(γ)|_a^t` is
`C^∞` and strictly increasing near `[a, b]` with `φ' = |γ̇| > 0`, so it admits a
`C^∞` inverse `ψ` (inverse function theorem, its derivative `1/|γ̇|∘ψ`
bootstrapping the smoothness degree), and the chain rule gives
`|d(γ∘ψ)/ds| = |γ̇(ψ s)| · ψ'(s) = 1`.

Lee's "with or without boundary" is faithfully modeled here by the boundaryless
case: the material lives in the scope of `[I.Boundaryless]`.

Reference: John M. Lee, *Introduction to Riemannian Manifolds* (2nd ed., GTM
176), Proposition 2.49.
-/
import LeeLib.Ch02.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter Metric MeasureTheory
open scoped Manifold Topology ContDiff

namespace LeeLib.Ch02

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Velocity, squared speed, and length of a curve -/

/-- **Math.** The **velocity field** `γ̇ = dγ/dt` of a curve `γ : ℝ → M`, the
image of the unit tangent `1 ∈ ℝ = T_tℝ` under the differential `dγ_t`. -/
def velocity (γ : ℝ → M) (t : ℝ) : TangentSpace I (γ t) :=
  mfderiv 𝓘(ℝ, ℝ) I γ t (1 : ℝ)

/-- **Math.** The **squared speed** `|γ̇(t)|² = ⟨γ̇(t), γ̇(t)⟩_g` of a curve at
time `t`: the metric length of its velocity, an intrinsic quantity requiring no
chart. -/
def curveSpeedSq (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t)

/-- **Math.** The **length** of `γ` on `[a, b]`,
`L(γ) = ∫_a^b |γ̇(t)| dt = ∫_a^b √⟨γ̇, γ̇⟩_g dt`. -/
def curveLength (g : RiemannianMetric I M) (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (curveSpeedSq (I := I) g γ t)

@[simp] theorem curveSpeedSq_def (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    curveSpeedSq (I := I) g γ t
      = g.inner (γ t) (velocity (I := I) γ t) (velocity (I := I) γ t) := rfl

/-- **Math.** A degenerate curve `γ|_{[a,a]}` has zero length. -/
@[simp] theorem curveLength_self (g : RiemannianMetric I M) (γ : ℝ → M) (a : ℝ) :
    curveLength (I := I) g γ a a = 0 :=
  intervalIntegral.integral_same

/-- **Math.** The squared speed of any curve is nonnegative: it is the diagonal
value `⟨v, v⟩_g` of the positive-semidefinite metric pairing. -/
theorem curveSpeedSq_nonneg (g : RiemannianMetric I M) (γ : ℝ → M) (t : ℝ) :
    0 ≤ curveSpeedSq (I := I) g γ t :=
  g.innerAt_self_nonneg (γ t) (velocity (I := I) γ t)

/-- **Math.** Chain rule for a real reparametrization: for `φ : ℝ → ℝ`,
`d(γ∘φ)/dt = φ'(t) · γ̇(φ(t))`. -/
theorem velocity_reparam {γ : ℝ → M} {φ : ℝ → ℝ} (t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    velocity (I := I) (γ ∘ φ) t = deriv φ t • velocity γ (φ t) := by
  have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t (1 : ℝ) = deriv φ t • (1 : ℝ) := by
    rw [mfderiv_eq_fderiv]
    show deriv φ t = deriv φ t • (1 : ℝ)
    rw [smul_eq_mul, mul_one]
  calc velocity (I := I) (γ ∘ φ) t
      = mfderiv 𝓘(ℝ, ℝ) I γ (φ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t (1 : ℝ)) :=
        mfderiv_comp_apply t hγ hφ.mdifferentiableAt (1 : ℝ)
    _ = mfderiv 𝓘(ℝ, ℝ) I γ (φ t) (deriv φ t • (1 : ℝ)) := by rw [h2]
    _ = deriv φ t • velocity γ (φ t) :=
        (mfderiv 𝓘(ℝ, ℝ) I γ (φ t)).map_smul (deriv φ t) (1 : ℝ)

/-- **Math.** The **scaling law for the squared speed** under a real
reparametrization: `|d(γ∘φ)/dt|² = φ'(t)² · |γ̇(φ t)|²`.  Immediate from the
chain rule `velocity_reparam` and bilinearity of the metric. -/
theorem curveSpeedSq_reparam (g : RiemannianMetric I M) {γ : ℝ → M} {φ : ℝ → ℝ}
    (t : ℝ) (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    curveSpeedSq (I := I) g (γ ∘ φ) t
      = (deriv φ t) ^ 2 * curveSpeedSq (I := I) g γ (φ t) := by
  have hvel : velocity (I := I) (γ ∘ φ) t = deriv φ t • velocity γ (φ t) :=
    velocity_reparam t hγ hφ
  have key : g.inner (γ (φ t)) (deriv φ t • velocity γ (φ t)) (deriv φ t • velocity γ (φ t))
      = (deriv φ t) ^ 2 * g.inner (γ (φ t)) (velocity γ (φ t)) (velocity γ (φ t)) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  show g.inner ((γ ∘ φ) t) (velocity (γ ∘ φ) t) (velocity (γ ∘ φ) t) = _
  rw [hvel]
  exact key

/-! ## Smoothness of the velocity lift and of the squared speed -/

/-- **Eng.** The canonical lift `t ↦ (t, 1)` of the line into its tangent bundle
is smooth: over the model space `ℝ` the tangent trivialization is the identity,
so both components of the coordinate representation are affine. -/
theorem contMDiff_tangentLift_one :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
  intro t₀
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
  filter_upwards with t
  rw [trivializationAt_model_space_apply]

/-- **Math.** The **velocity lift** `t ↦ (γ t, γ̇ t)` of a curve that is `C^∞` on
an open time set `J` is smooth on `J`: it is the composite of the (smooth)
bundled derivative `tangentMapWithin` of `γ` on `J` with the canonical lift
`t ↦ (t, 1)`, and on the open set `J` that bundled derivative agrees with the
intrinsic velocity. -/
theorem contMDiffOn_velocity_lift {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) :
    ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun t => (⟨γ t, velocity γ t⟩ : TangentBundle I M)) J := by
  have htm := hγ.contMDiffOn_tangentMapWithin (m := ∞) (by simp) hJ.uniqueMDiffOn
  have hline : ContMDiffOn 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) J :=
    contMDiff_tangentLift_one.contMDiffOn
  have hcomp := htm.comp hline (fun t ht => ht)
  refine hcomp.congr ?_
  intro t ht
  show (⟨γ t, velocity γ t⟩ : TangentBundle I M)
      = tangentMapWithin 𝓘(ℝ, ℝ) I γ J (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)
  rw [tangentMapWithin_eq_tangentMap (hJ.uniqueMDiffWithinAt ht)
    ((hγ.contMDiffAt (hJ.mem_nhds ht)).mdifferentiableAt (by simp))]
  rfl

/-- **Math.** The velocity lift is smooth at each time of an open smoothness
window. -/
theorem contMDiffAt_velocity_lift {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) {t : ℝ} (ht : t ∈ J) :
    ContMDiffAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun s => (⟨γ s, velocity γ s⟩ : TangentBundle I M)) t :=
  (contMDiffOn_velocity_lift hJ hγ).contMDiffAt (hJ.mem_nhds ht)

/-- **Math.** The squared speed of a curve that is `C^∞` on an open time set `J`
is `C^∞` at every `t ∈ J`.  This is `ContMDiffAt.inner_bundle`, pairing the
smooth velocity lift with itself, transported through the model-space
identification `ContMDiffAt ↔ ContDiffAt`.  No chart Gram computation is
needed. -/
theorem contDiffAt_curveSpeedSq (g : RiemannianMetric I M) {γ : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) {t : ℝ} (ht : t ∈ J) :
    ContDiffAt ℝ ∞ (curveSpeedSq (I := I) g γ) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  have hv := contMDiffAt_velocity_lift hJ hγ ht
  -- Fix the model-space goal type first, so typeclass synthesis picks the fibre
  -- norm coming from `letI` before it can be unified with `g`'s.
  have hpair : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (curveSpeedSq (I := I) g γ) t :=
    ContMDiffAt.inner_bundle (IM := 𝓘(ℝ, ℝ)) (IB := I) (F := E)
      (E := (TangentSpace I : M → Type _)) (n := ∞) (b := γ)
      (v := fun s => velocity γ s) (w := fun s => velocity γ s) hv hv
  exact hpair.contDiffAt

/-- **Math.** On an open smoothness window `J`, the arclength integrand
`t ↦ √|γ̇(t)|` is interval-integrable between any two points whose closed
interval lies in `J`: the squared speed is continuous on `J`, hence so is its
square root, and continuity on the compact `[s, t] ⊆ J` gives integrability. -/
theorem intervalIntegrable_sqrt_curveSpeedSq (g : RiemannianMetric I M) {γ : ℝ → M}
    {J : Set ℝ} (hJ : IsOpen J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J) {s t : ℝ}
    (hsub : uIcc s t ⊆ J) :
    IntervalIntegrable (fun τ => Real.sqrt (curveSpeedSq (I := I) g γ τ)) volume s t := by
  have hspeed : ContinuousOn (curveSpeedSq (I := I) g γ) J := fun r hr =>
    (contDiffAt_curveSpeedSq (I := I) g hJ hγ hr).continuousAt.continuousWithinAt
  have hcont : ContinuousOn (fun τ => Real.sqrt (curveSpeedSq (I := I) g γ τ)) J :=
    Real.continuous_sqrt.comp_continuousOn hspeed
  exact (hcont.mono hsub).intervalIntegrable

/-! ## Arclength reparametrization of a regular curve (Lee Prop. 2.49(a)) -/

/-- **Math.** John M. Lee, *Introduction to Riemannian Manifolds*, Proposition
2.49(a): **every regular curve has a unit-speed forward reparametrization**.

Let `γ` be `C^∞` on an open time set `J ⊇ [a, b]` with nonvanishing speed on
`[a, b]`.  Then the arclength function `φ(t) = L(γ)|_a^t` admits an inverse `ψ`
with `ψ(L(γ)|_a^t) = t` on `[a, b]` (and `ψ` maps `[0, L(γ)|_a^b]` back into
`[a, b]`), and the reparametrized curve `γ ∘ ψ : [0, L(γ)|_a^b] → M` is `C^∞`,
runs from `γ a` to `γ b`, has **unit speed**, and is **parametrized by
arclength**: `L(γ ∘ ψ)|_0^s = s`.

The proof: `φ' = |γ̇| > 0` near `[a, b]` (fundamental theorem of calculus, using
`contDiffAt_curveSpeedSq` for continuity of the speed), so `φ` is strictly
increasing and `C^∞` there; the inverse `ψ` is `C^∞` by the inverse function
theorem (its derivative `1 / |γ̇| ∘ ψ` bootstraps the smoothness degree), and the
scaling law `curveSpeedSq_reparam` gives
`|d(γ∘ψ)/ds|² = ψ'(s)² · |γ̇(ψ s)|² = 1`. -/
theorem regularCurve_arclengthReparametrization (g : RiemannianMetric I M)
    {γ : ℝ → M} {J : Set ℝ} (hJ : IsOpen J) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ γ J)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ J)
    (hreg : ∀ t ∈ Icc a b, curveSpeedSq (I := I) g γ t ≠ 0) :
    ∃ ψ : ℝ → ℝ,
      (∀ t ∈ Icc a b, ψ (curveLength (I := I) g γ a t) = t) ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b), ψ s ∈ Icc a b) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (γ ∘ ψ) (Icc 0 (curveLength (I := I) g γ a b)) ∧
      (γ ∘ ψ) 0 = γ a ∧ (γ ∘ ψ) (curveLength (I := I) g γ a b) = γ b ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b),
        curveSpeedSq (I := I) g (γ ∘ ψ) s = 1) ∧
      (∀ s ∈ Icc (0 : ℝ) (curveLength (I := I) g γ a b),
        curveLength (I := I) g (γ ∘ ψ) 0 s = s) := by
  classical
  -- ### The open interval `J' ⊇ [a, b]` where `γ` is smooth and regular
  have hVopen : IsOpen {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} := by
    have hc : ContinuousOn (curveSpeedSq (I := I) g γ) J := fun t ht =>
      (contDiffAt_curveSpeedSq (I := I) g hJ hγ ht).continuousAt.continuousWithinAt
    have : {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0}
        = J ∩ (curveSpeedSq (I := I) g γ) ⁻¹' ({0}ᶜ) := rfl
    rw [this]
    exact hc.isOpen_inter_preimage hJ isOpen_compl_singleton
  have haV : a ∈ {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} :=
    ⟨hsub (left_mem_Icc.mpr hab), hreg a (left_mem_Icc.mpr hab)⟩
  have hbV : b ∈ {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} :=
    ⟨hsub (right_mem_Icc.mpr hab), hreg b (right_mem_Icc.mpr hab)⟩
  obtain ⟨εa, hεa, hballa⟩ := Metric.isOpen_iff.mp hVopen a haV
  obtain ⟨εb, hεb, hballb⟩ := Metric.isOpen_iff.mp hVopen b hbV
  set δ : ℝ := min εa εb / 2 with hδ_def
  have hδ_pos : 0 < δ := by
    rw [hδ_def]
    have := lt_min hεa hεb
    positivity
  set J' : Set ℝ := Ioo (a - δ) (b + δ) with hJ'_def
  have hJ'_open : IsOpen J' := isOpen_Ioo
  have hJ'_sub : J' ⊆ {t | t ∈ J ∧ curveSpeedSq (I := I) g γ t ≠ 0} := by
    intro t ht
    obtain ⟨ht1, ht2⟩ := ht
    have hδεa : δ ≤ εa :=
      le_trans (half_le_self (lt_min hεa hεb).le) (min_le_left εa εb)
    have hδεb : δ ≤ εb :=
      le_trans (half_le_self (lt_min hεa hεb).le) (min_le_right εa εb)
    rcases lt_or_ge t a with hta | hta
    · refine hballa ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith
    rcases le_or_gt t b with htb | htb
    · exact ⟨hsub ⟨hta, htb⟩, hreg t ⟨hta, htb⟩⟩
    · refine hballb ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor
      · linarith
      · linarith
  have hJ'J : J' ⊆ J := fun t ht => (hJ'_sub ht).1
  have hIccJ' : Icc a b ⊆ J' := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have haJ' : a ∈ J' := hIccJ' (left_mem_Icc.mpr hab)
  have hbJ' : b ∈ J' := hIccJ' (right_mem_Icc.mpr hab)
  have hJ'_ord : ∀ s ∈ J', ∀ t ∈ J', Icc s t ⊆ J' := fun s hs t ht r hr =>
    ⟨lt_of_lt_of_le hs.1 hr.1, lt_of_le_of_lt hr.2 ht.2⟩
  -- ### The pointwise speed `h = √(g(γ̇, γ̇))`: positive and `C^∞` on `J'`
  have hsp_pos : ∀ t ∈ J', 0 < curveSpeedSq (I := I) g γ t := fun t ht =>
    lt_of_le_of_ne (curveSpeedSq_nonneg (I := I) g γ t) (Ne.symm (hJ'_sub ht).2)
  have hh_smooth : ∀ t ∈ J', ContDiffAt ℝ ∞
      (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) t := fun t ht =>
    ContDiffAt.sqrt (contDiffAt_curveSpeedSq (I := I) g hJ hγ (hJ'J ht))
      (hJ'_sub ht).2
  have hh_pos : ∀ t ∈ J', 0 < Real.sqrt (curveSpeedSq (I := I) g γ t) := fun t ht =>
    Real.sqrt_pos.mpr (hsp_pos t ht)
  have hh_cont : ContinuousOn (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) J' :=
    fun t ht => (hh_smooth t ht).continuousAt.continuousWithinAt
  -- interval integrability of the speed inside `J'`
  have hInt : ∀ s ∈ J', ∀ t ∈ J', IntervalIntegrable
      (fun τ => Real.sqrt (curveSpeedSq (I := I) g γ τ)) volume s t := by
    intro s hs t ht
    refine intervalIntegrable_sqrt_curveSpeedSq (I := I) g hJ hγ ?_
    rcases le_total s t with h | h
    · rw [uIcc_of_le h]; exact (hJ'_ord s hs t ht).trans hJ'J
    · rw [uIcc_of_ge h]; exact (hJ'_ord t ht s hs).trans hJ'J
  -- ### The arclength function `φ` and its properties on `J'`
  set φ : ℝ → ℝ := fun t => curveLength (I := I) g γ a t with hφ_def
  have hφ_deriv : ∀ t ∈ J', HasDerivAt φ
      (Real.sqrt (curveSpeedSq (I := I) g γ t)) t := by
    intro t ht
    exact intervalIntegral.integral_hasDerivAt_right (hInt a haJ' t ht)
      (hh_cont.stronglyMeasurableAtFilter hJ'_open t ht)
      ((hh_smooth t ht).continuousAt)
  have hφ_add : ∀ s ∈ J', ∀ t ∈ J', φ t = φ s
      + ∫ τ in s..t, Real.sqrt (curveSpeedSq (I := I) g γ τ) := by
    intro s hs t ht
    have := intervalIntegral.integral_add_adjacent_intervals (hInt a haJ' s hs)
      (hInt s hs t ht)
    show (∫ τ in a..t, Real.sqrt (curveSpeedSq (I := I) g γ τ))
      = (∫ τ in a..s, Real.sqrt (curveSpeedSq (I := I) g γ τ)) + _
    rw [← this]
  have hφ_mono : StrictMonoOn φ J' := by
    intro s hs t ht hst
    have hkey := hφ_add s hs t ht
    have hpos : 0 < ∫ τ in s..t, Real.sqrt (curveSpeedSq (I := I) g γ τ) :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hInt s hs t ht)
        (fun τ hτ => hh_pos τ (hJ'_ord s hs t ht (Ioo_subset_Icc_self hτ))) hst
    rw [hkey]
    linarith
  have hφ_smooth : ContDiffOn ℝ ∞ φ J' := by
    rw [contDiffOn_infty_iff_deriv_of_isOpen hJ'_open]
    refine ⟨fun t ht => (hφ_deriv t ht).differentiableAt.differentiableWithinAt, ?_⟩
    have heq : EqOn (deriv φ) (fun s => Real.sqrt (curveSpeedSq (I := I) g γ s)) J' :=
      fun t ht => (hφ_deriv t ht).deriv
    exact ContDiffOn.congr (fun t ht => (hh_smooth t ht).contDiffWithinAt) heq
  have hφ_inj : InjOn φ J' := hφ_mono.injOn
  -- ### The inverse `ψ` and the open image `W = φ(J')`
  set ψ : ℝ → ℝ := Function.invFunOn φ J' with hψ_def
  have hleft : ∀ t ∈ J', ψ (φ t) = t := fun t ht => hφ_inj.leftInvOn_invFunOn ht
  set W : Set ℝ := φ '' J' with hW_def
  -- the local package at a point of `W`: `ψ` is a local inverse with derivative
  have hψ_deriv : ∀ t₀ ∈ J', HasDerivAt ψ
      (Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ (φ t₀) ∧ W ∈ 𝓝 (φ t₀) := by
    intro t₀ ht₀
    have hd_ne : Real.sqrt (curveSpeedSq (I := I) g γ t₀) ≠ 0 := (hh_pos t₀ ht₀).ne'
    have hcda : ContDiffAt ℝ ∞ φ t₀ := hφ_smooth.contDiffAt (hJ'_open.mem_nhds ht₀)
    have hstrict : HasStrictDerivAt φ
        (Real.sqrt (curveSpeedSq (I := I) g γ t₀)) t₀ := by
      have h1 := hcda.hasStrictDerivAt (by simp)
      rwa [(hφ_deriv t₀ ht₀).deriv] at h1
    set ζ : ℝ → ℝ := hstrict.localInverse φ _ t₀ hd_ne with hζ_def
    have hζ_strict : HasStrictDerivAt ζ
        (Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ (φ t₀) :=
      hstrict.to_localInverse hd_ne
    have hζ_cont : ContinuousAt ζ (φ t₀) := hζ_strict.hasDerivAt.continuousAt
    have hζ_t₀ : ζ (φ t₀) = t₀ :=
      (hstrict.eventually_left_inverse hd_ne).self_of_nhds
    have hζ_mem : ∀ᶠ s in 𝓝 (φ t₀), ζ s ∈ J' := by
      have : J' ∈ 𝓝 (ζ (φ t₀)) := by
        rw [hζ_t₀]
        exact hJ'_open.mem_nhds ht₀
      exact hζ_cont.eventually_mem this
    have hev : ψ =ᶠ[𝓝 (φ t₀)] ζ := by
      filter_upwards [hstrict.eventually_right_inverse hd_ne, hζ_mem]
        with s hrs hsJ'
      have hex : ∃ u ∈ J', φ u = s := ⟨ζ s, hsJ', hrs⟩
      have h1 : φ (Function.invFunOn φ J' s) = s := Function.invFunOn_eq hex
      have h2 : Function.invFunOn φ J' s ∈ J' := Function.invFunOn_mem hex
      exact hφ_inj h2 hsJ' (h1.trans hrs.symm)
    refine ⟨hζ_strict.hasDerivAt.congr_of_eventuallyEq hev, ?_⟩
    -- `W` is a neighbourhood of `φ t₀`
    have hmap := hstrict.map_nhds_eq hd_ne
    rw [← hmap]
    exact mem_map.mpr (mem_of_superset (hJ'_open.mem_nhds ht₀)
      (subset_preimage_image φ J'))
  have hW_open : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    rintro s₀ ⟨t₀, ht₀, rfl⟩
    exact (hψ_deriv t₀ ht₀).2
  have hψ_mem : ∀ s ∈ W, ψ s ∈ J' := by
    rintro s ⟨t₀, ht₀, rfl⟩
    rw [hleft t₀ ht₀]
    exact ht₀
  have hψ_hasDeriv : ∀ s ∈ W, HasDerivAt ψ
      (Real.sqrt (curveSpeedSq (I := I) g γ (ψ s)))⁻¹ s := by
    rintro s ⟨t₀, ht₀, rfl⟩
    rw [hleft t₀ ht₀]
    exact (hψ_deriv t₀ ht₀).1
  -- ### `ψ` is `C^∞` on `W`, by bootstrapping through its derivative
  have hψ_diff : DifferentiableOn ℝ ψ W := fun s hs =>
    (hψ_hasDeriv s hs).differentiableAt.differentiableWithinAt
  have hψ_derivEq : EqOn (deriv ψ)
      (fun s => (Real.sqrt (curveSpeedSq (I := I) g γ (ψ s)))⁻¹) W :=
    fun s hs => (hψ_hasDeriv s hs).deriv
  have hψ_smooth : ContDiffOn ℝ ∞ ψ W := by
    rw [contDiffOn_infty]
    intro n
    induction n with
    | zero =>
      rw [Nat.cast_zero, contDiffOn_zero]
      exact fun s hs => (hψ_hasDeriv s hs).continuousAt.continuousWithinAt
    | succ n ih =>
      have hcast : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by
        push_cast
        rfl
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen hW_open]
      refine ⟨hψ_diff, ?_, ?_⟩
      · intro hω
        exact absurd hω (by simp)
      · refine ContDiffOn.congr ?_ hψ_derivEq
        have hsp_n : ContDiffOn ℝ n (fun s =>
            Real.sqrt (curveSpeedSq (I := I) g γ (ψ s))) W := by
          intro s hs
          have hψs := hψ_mem s hs
          have hsqrt : ContDiffAt ℝ n
              (fun r => Real.sqrt (curveSpeedSq (I := I) g γ r)) (ψ s) :=
            (hh_smooth (ψ s) hψs).of_le (by exact_mod_cast le_top)
          exact (hsqrt.comp_contDiffWithinAt s (ih s hs))
        refine hsp_n.inv ?_
        intro s hs
        exact (hh_pos (ψ s) (hψ_mem s hs)).ne'
  -- ### Assembling the statement
  have hφa : φ a = 0 := curveLength_self (I := I) g γ a
  have hφcont : ContinuousOn φ (Icc a b) :=
    (hφ_smooth.mono hIccJ').continuousOn
  have hIVT : Icc (0 : ℝ) (curveLength (I := I) g γ a b) ⊆ φ '' Icc a b := by
    have := intermediate_value_Icc hab hφcont
    rwa [hφa] at this
  have hIccW : Icc (0 : ℝ) (curveLength (I := I) g γ a b) ⊆ W := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := hIVT hs
    exact ⟨t, hIccJ' ht, rfl⟩
  -- ### Unit speed of the reparametrized curve, everywhere on `W`
  have hunit : ∀ s ∈ W, curveSpeedSq (I := I) g (γ ∘ ψ) s = 1 := by
    intro s hsW
    obtain ⟨t₀, ht₀J', hst₀⟩ := id hsW
    have hψs : ψ s = t₀ := by rw [← hst₀, hleft t₀ ht₀J']
    have hψ_ds : HasDerivAt ψ (Real.sqrt (curveSpeedSq (I := I) g γ t₀))⁻¹ s := by
      have := hψ_hasDeriv s hsW
      rwa [hψs] at this
    have hγ_md : MDifferentiableAt 𝓘(ℝ, ℝ) I γ (ψ s) :=
      (hγ.contMDiffAt (hJ.mem_nhds (hJ'J (hψ_mem s hsW)))).mdifferentiableAt (by simp)
    rw [curveSpeedSq_reparam (I := I) g s hγ_md hψ_ds.differentiableAt,
      hψ_ds.deriv, hψs]
    have hsp_pos' : 0 < curveSpeedSq (I := I) g γ t₀ := hsp_pos t₀ ht₀J'
    rw [inv_pow, Real.sq_sqrt hsp_pos'.le]
    exact inv_mul_cancel₀ hsp_pos'.ne'
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- left-inverse property on `[a, b]`
  · intro t ht
    exact hleft t (hIccJ' ht)
  -- the inverse maps `[0, L]` back into `[a, b]`
  · intro s hs
    obtain ⟨t, ht, rfl⟩ := hIVT hs
    rw [hleft t (hIccJ' ht)]
    exact ht
  -- smoothness of the reparametrized curve
  · intro s hs
    have hsW : s ∈ W := hIccW hs
    have hψs : ψ s ∈ J' := hψ_mem s hsW
    have hγ_at : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ (ψ s) :=
      hγ.contMDiffAt (hJ.mem_nhds (hJ'J hψs))
    have hψ_at : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ ψ s :=
      (hψ_smooth.contDiffAt (hW_open.mem_nhds hsW)).contMDiffAt
    exact (hγ_at.comp s hψ_at).contMDiffWithinAt
  -- initial point
  · show γ (ψ 0) = γ a
    rw [← hφa, hleft a haJ']
  -- terminal point
  · show γ (ψ (curveLength (I := I) g γ a b)) = γ b
    rw [show curveLength (I := I) g γ a b = φ b from rfl, hleft b hbJ']
  -- unit speed on `[0, L]`
  · exact fun s hs => hunit s (hIccW hs)
  -- parametrization by arclength
  · intro s hs
    have hone : EqOn (fun τ => Real.sqrt (curveSpeedSq (I := I) g (γ ∘ ψ) τ))
        (fun _ => (1 : ℝ)) (uIcc 0 s) := by
      intro τ hτ
      rw [uIcc_of_le hs.1] at hτ
      have hτW : τ ∈ W := hIccW ⟨hτ.1, hτ.2.trans hs.2⟩
      show Real.sqrt (curveSpeedSq (I := I) g (γ ∘ ψ) τ) = 1
      rw [hunit τ hτW, Real.sqrt_one]
    show (∫ τ in (0 : ℝ)..s, Real.sqrt (curveSpeedSq (I := I) g (γ ∘ ψ) τ)) = s
    rw [intervalIntegral.integral_congr hone]
    simp

end LeeLib.Ch02

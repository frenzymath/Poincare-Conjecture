import PetersenLib.Ch01.RiemannianManifolds
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Petersen Ch. 1 — arc length of curves

Infrastructure for the arc-length exercises 1.6.16–1.6.21 of Petersen §1.6:
the velocity field of a curve (`velocity`), vector fields along a curve
(`IsVectorFieldAlong`), the arc length `arcLength g c a b = ∫ₐᵇ |ċ| dt`, the
chain rules `velocity_comp` and `velocity_reparam`, invariance of arc length
under metric-preserving maps (`PreservesMetric.arcLength` — the heart of
Exercise 1.6.17), invariance under monotone smooth reparametrization
(`arcLength_reparam` — part (1) of Exercise 1.6.16), smoothness of the
velocity lift into the tangent bundle and continuity of the speed
(`contMDiff_velocity_lift`, `continuous_sqrt_metricInner_velocity`), and the
identification of `arcLength` with `∫ₐᵇ ‖c'(t)‖ dt` on an inner product space
(`arcLength_eq_integral_norm_deriv`).

The final section vendors do Carmo's Prop. 1.2.10 (`exists_riemannianMetric`:
every finite-dimensional, σ-compact Hausdorff manifold carries a Riemannian
metric), which Exercise 1.6.26 quotes as the first half of the averaging
argument.

Curve/velocity/arc-length definitions and `PreservesMetric.arcLength` are
vendored from the shared OpenGALib development
(`OpenGALib/Riemannian/Manifold/DoCarmoCh1.lean`: `DCVelocity`,
`DCIsVectorFieldAlong`, `DCArcLength`, `DCVelocity_comp`,
`DCPreservesMetric.dcArcLength`, `convex_symm_posDef`,
`exists_riemannianMetric`), renamed into the `PetersenLib` namespace.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.6, Exercises
1.6.16–1.6.21 and 1.6.26; do Carmo, *Riemannian Geometry*, §1.2.
-/

open Bundle Bornology Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-! ## Velocity, vector fields along a curve, and arc length -/

/-- **Math.** Petersen §1.6, Exercise 1.6.16: the **velocity field** `ċ = dc/dt`
of a curve `c : ℝ → M`, the image of the unit tangent `1 ∈ ℝ = T_tℝ` under the
differential `dc_t`. -/
def velocity (c : ℝ → M) (t : ℝ) : TangentSpace I (c t) :=
  mfderiv 𝓘(ℝ, ℝ) I c t (1 : ℝ)

/-- **Math.** A **vector field along a curve** `c` is a differentiable
assignment `V t ∈ T_{c t}M`, expressed as smoothness of the tangent-bundle
section `t ↦ (c t, V t)` on the parameter set `s`. -/
def IsVectorFieldAlong (c : ℝ → M) (V : ∀ t, TangentSpace I (c t)) (s : Set ℝ) :
    Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
    (fun t => (⟨c t, V t⟩ : TangentBundle I M)) s

/-- **Math.** Petersen §1.6, Exercise 1.6.16: the **arc length** of the segment
`c|[a,b]` for a metric `g`, `L(c) = ∫_a^b |ċ| dt = ∫_a^b ⟨ċ, ċ⟩^{1/2} dt`. -/
def arcLength (g : RiemannianMetric I M) (c : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt (g.metricInner (c t) (velocity c t) (velocity c t))

omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
/-- **Math.** Chain rule for the velocity field: the velocity of a composite
curve `f ∘ c` is the differential of `f` applied to the velocity of `c`,
`d(f∘c)/dt = df_{c t}(ċ(t))`. -/
theorem velocity_comp {c : ℝ → M} {f : M → M'} (t : ℝ)
    (hf : MDifferentiableAt I I' f (c t)) (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t) :
    velocity (f ∘ c) t = mfderiv I I' f (c t) (velocity c t) :=
  mfderiv_comp_apply t hf hc (1 : ℝ)

omit [IsManifold I ∞ M] in
/-- **Math.** Chain rule for a real reparametrization: for `φ : ℝ → ℝ`,
`d(c∘φ)/dt = φ'(t) · ċ(φ(t))`. -/
theorem velocity_reparam {c : ℝ → M} {φ : ℝ → ℝ} (t : ℝ)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    velocity (I := I) (c ∘ φ) t = deriv φ t • velocity c (φ t) := by
  have h2 : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t (1 : ℝ) = deriv φ t • (1 : ℝ) := by
    rw [mfderiv_eq_fderiv]
    show deriv φ t = deriv φ t • (1 : ℝ)
    rw [smul_eq_mul, mul_one]
  calc velocity (I := I) (c ∘ φ) t
      = mfderiv 𝓘(ℝ, ℝ) I c (φ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t (1 : ℝ)) :=
        mfderiv_comp_apply t hc hφ.mdifferentiableAt (1 : ℝ)
    _ = mfderiv 𝓘(ℝ, ℝ) I c (φ t) (deriv φ t • (1 : ℝ)) := by rw [h2]
    _ = deriv φ t • velocity c (φ t) :=
        (mfderiv 𝓘(ℝ, ℝ) I c (φ t)).map_smul (deriv φ t) (1 : ℝ)

/-- **Math.** On a normed space, viewed as a manifold over itself, the velocity
field of a curve is its ordinary derivative: `ċ(t) = c'(t)`. -/
theorem velocity_eq_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ → F) (t : ℝ) :
    velocity (I := 𝓘(ℝ, F)) c t = deriv c t := by
  show mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, F) c t (1 : ℝ) = deriv c t
  rw [mfderiv_eq_fderiv]
  rfl

/-- **Math.** Petersen §1.6, Exercise 1.6.17 (core): a metric-preserving map
(`F^*g_N = g_M`) preserves the arc length of every curve:
`L(f ∘ c) = L(c)`. Together with the chain rule `velocity_comp`, this is what
makes the length functional an invariant of the Riemannian structure. -/
theorem PreservesMetric.arcLength {gM : RiemannianMetric I M}
    {gN : RiemannianMetric I' M'} {f : M → M'} (hiso : PreservesMetric gM gN f)
    {c : ℝ → M} (hf : MDifferentiable I I' f) (hc : MDifferentiable 𝓘(ℝ, ℝ) I c)
    (a b : ℝ) :
    arcLength gN (f ∘ c) a b = arcLength gM c a b := by
  simp only [PetersenLib.arcLength]
  congr 1
  funext t
  rw [velocity_comp t (hf.mdifferentiableAt) (hc.mdifferentiableAt),
    Function.comp_apply, ← hiso (c t) (velocity c t) (velocity c t)]

/-- **Math.** The speed transforms under a real reparametrization by the factor
`|φ'(t)|`: `|d(c∘φ)/dt| = |φ'(t)| · |ċ(φ(t))|`. -/
theorem sqrt_metricInner_velocity_reparam (g : RiemannianMetric I M)
    {c : ℝ → M} {φ : ℝ → ℝ} (t : ℝ)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c (φ t)) (hφ : DifferentiableAt ℝ φ t) :
    Real.sqrt (g.metricInner ((c ∘ φ) t) (velocity (c ∘ φ) t) (velocity (c ∘ φ) t))
      = |deriv φ t| *
        Real.sqrt (g.metricInner (c (φ t)) (velocity c (φ t)) (velocity c (φ t))) := by
  have hval : g.metricInner (c (φ t)) (velocity (c ∘ φ) t) (velocity (c ∘ φ) t)
      = deriv φ t ^ 2
        * g.metricInner (c (φ t)) (velocity c (φ t)) (velocity c (φ t)) := by
    rw [velocity_reparam t hc hφ]
    show g.metricInner (c (φ t)) (deriv φ t • velocity c (φ t))
        (deriv φ t • velocity c (φ t)) = _
    rw [g.metricInner_smul_left, g.metricInner_smul_right, ← mul_assoc, ← sq]
  show Real.sqrt (g.metricInner (c (φ t)) (velocity (c ∘ φ) t) (velocity (c ∘ φ) t)) = _
  rw [hval, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-! ## Reparametrization invariance of arc length
(Exercise 1.6.16, part (1)) -/

/-- **Math.** Petersen §1.6, Exercise 1.6.16 (1): **arc length is independent of
(monotone) parametrization**. For a smooth curve `c` and a smooth
reparametrization `φ` that is monotone on `[a, b]`,
`L(c ∘ φ)|_a^b = L(c)|_{φ(a)}^{φ(b)}`. Change of variables `u = φ(t)`:
`|d(c∘φ)/dt| = φ'(t) |ċ(φ(t))|` since `φ' ≥ 0`, and the substitution rule for
monotone `φ` converts the integral. -/
theorem arcLength_reparam (g : RiemannianMetric I M) {c : ℝ → M} {φ : ℝ → ℝ}
    (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) (hφ : ContDiff ℝ ∞ φ) (a b : ℝ)
    (hmono : MonotoneOn φ (Set.uIcc a b)) :
    arcLength g (c ∘ φ) a b = arcLength g c (φ a) (φ b) := by
  rcases eq_or_ne a b with rfl | hab
  · simp only [PetersenLib.arcLength, intervalIntegral.integral_same]
  have hminlt : min a b < max a b := min_lt_max.mpr hab
  have hφdiff : ∀ t : ℝ, DifferentiableAt ℝ φ t :=
    fun t => (hφ.differentiable (by simp)).differentiableAt
  have hnneg : ∀ t ∈ Set.uIcc a b, 0 ≤ deriv φ t := by
    intro t ht
    have h2 : 0 ≤ derivWithin φ (Set.Icc (min a b) (max a b)) t :=
      hmono.derivWithin_nonneg (x := t)
    rwa [(hφdiff t).derivWithin ((uniqueDiffOn_Icc hminlt) t ht)] at h2
  have hpt : Set.EqOn
      (fun t => Real.sqrt (g.metricInner ((c ∘ φ) t) (velocity (c ∘ φ) t)
        (velocity (c ∘ φ) t)))
      (fun t => deriv φ t •
        Real.sqrt (g.metricInner (c (φ t)) (velocity c (φ t)) (velocity c (φ t))))
      (Set.uIcc a b) := by
    intro t ht
    have hsp := sqrt_metricInner_velocity_reparam g t
      ((hc (φ t)).mdifferentiableAt (by simp)) (hφdiff t)
    simpa [abs_of_nonneg (hnneg t ht)] using hsp
  calc arcLength g (c ∘ φ) a b
      = ∫ t in a..b, deriv φ t •
          Real.sqrt (g.metricInner (c (φ t)) (velocity c (φ t)) (velocity c (φ t))) :=
        intervalIntegral.integral_congr hpt
    _ = ∫ s in φ a..φ b,
          Real.sqrt (g.metricInner (c s) (velocity c s) (velocity c s)) :=
        intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
          (g := fun s =>
            Real.sqrt (g.metricInner (c s) (velocity c s) (velocity c s)))
          (hφ.continuous.continuousOn)
          (fun t _ => (hφdiff t).hasDerivAt)
          (fun t ht => hnneg t (Set.Ioo_subset_Icc_self ht))
    _ = arcLength g c (φ a) (φ b) := rfl

/-! ## Smoothness of the velocity lift, continuity of the speed -/

/-- **Eng.** The canonical lift `t ↦ (t, 1)` of the line into its tangent
bundle is smooth: over the model space `ℝ` the tangent trivialization is the
identity, so both components of the coordinate representation are affine. -/
theorem contMDiff_tangentLift_one :
    ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := by
  intro t₀
  rw [contMDiffAt_totalSpace]
  refine ⟨contMDiffAt_id, ?_⟩
  refine (contMDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
  filter_upwards with t
  rw [trivializationAt_model_space_apply]

/-- **Math.** The **velocity lift** `t ↦ (c t, ċ(t))` of a smooth curve into
the tangent bundle is smooth: it is the composite of the (smooth) bundled
derivative `tangentMap` of `c` with the canonical lift `t ↦ (t, 1)`. -/
theorem contMDiff_velocity_lift {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) :
    ContMDiff 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E)) ∞
      (fun t => (⟨c t, velocity c t⟩ : TangentBundle I M)) := by
  have htm : ContMDiff (𝓘(ℝ, ℝ)).tangent I.tangent ∞ (tangentMap 𝓘(ℝ, ℝ) I c) :=
    hc.contMDiff_tangentMap (by simp)
  have heq : (fun t : ℝ => (⟨c t, velocity c t⟩ : TangentBundle I M))
      = tangentMap 𝓘(ℝ, ℝ) I c ∘
        (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) := rfl
  rw [heq]
  exact htm.comp contMDiff_tangentLift_one

/-- **Math.** The **speed** `t ↦ |ċ(t)| = ⟨ċ(t), ċ(t)⟩^{1/2}` of a smooth curve
is continuous (indeed the squared speed is smooth, by smoothness of the metric
and of the velocity lift). Supplies integrability of the arc-length
integrand. -/
theorem continuous_sqrt_metricInner_velocity (g : RiemannianMetric I M)
    {c : ℝ → M} (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c) :
    Continuous fun t =>
      Real.sqrt (g.metricInner (c t) (velocity c t) (velocity c t)) := by
  have hinner : Continuous fun t => g.metricInner (c t) (velocity c t) (velocity c t) := by
    letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hv := contMDiff_velocity_lift hc
    have h := ContMDiff.inner_bundle (IB := I) (F := E)
      (E := (TangentSpace I : M → Type _)) (b := c)
      (v := fun t => velocity c t) (w := fun t => velocity c t)
      (IM := 𝓘(ℝ, ℝ)) hv hv
    exact h.continuous
  exact Real.continuous_sqrt.comp hinner

/-! ## Arc length in an inner product space -/

/-- **Math.** In an inner product space with its canonical metric
(Petersen Example 1.1.2), arc length is the elementary formula
`L(c) = ∫_a^b ‖c'(t)‖ dt`. -/
theorem arcLength_eq_integral_norm_deriv {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (c : ℝ → F) (a b : ℝ) :
    arcLength (innerProductSpaceMetric F) c a b = ∫ t in a..b, ‖deriv c t‖ := by
  simp only [PetersenLib.arcLength]
  congr 1
  funext t
  rw [innerProductSpaceMetric_apply, velocity_eq_deriv,
    real_inner_self_eq_norm_mul_norm, Real.sqrt_mul_self (norm_nonneg _)]

/-- **Math.** In an inner product space with its canonical metric, the arc
length of a smooth curve bounds the distance between its endpoints:
`|c(b) − c(a)| = |∫ ċ| ≤ ∫ |ċ| = L(c)|_a^b`. This is the first half of
Petersen Exercise 1.6.19 (straight lines minimize length), factored out here
because the isometry-group computations of §1.3 also rest on it. -/
theorem dist_le_arcLength {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {c : ℝ → F}
    (hc : ContDiff ℝ ∞ c) {a b : ℝ} (hab : a ≤ b) :
    dist (c a) (c b) ≤ arcLength (innerProductSpaceMetric F) c a b := by
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hderiv_cont : Continuous (deriv c) := hc.continuous_deriv (by simp)
  have hFTC : ∫ s in a..b, deriv c s = c b - c a :=
    intervalIntegral.integral_deriv_eq_sub (fun s _ => hcd s)
      (hderiv_cont.intervalIntegrable a b)
  rw [arcLength_eq_integral_norm_deriv, dist_eq_norm, norm_sub_rev, ← hFTC]
  exact intervalIntegral.norm_integral_le_integral_norm hab

/-! ## Existence of Riemannian metrics (do Carmo Prop. 1.2.10; quoted by
Exercise 1.6.26)

Vendored from the shared OpenGALib development
(`OpenGALib/Riemannian/Manifold/DoCarmoCh1.lean`). -/

section Existence

omit [IsManifold I ∞ M] in
/-- **Math.** The set of symmetric positive-definite bilinear forms on a tangent
space is convex: a convex combination `a q₁ + b q₂` (with `a, b ≥ 0`,
`a + b = 1`) is again symmetric, and positive-definite as long as at least one
weight is strictly positive. This is what lets the partition-of-unity patching
keep the glued form positive-definite. -/
theorem convex_symm_posDef (x : M) :
    Convex ℝ {q : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ |
      (∀ u v, q u v = q v u) ∧ (∀ v, v ≠ 0 → 0 < q v v)} := by
  intro q₁ hq₁ q₂ hq₂ a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro u v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hq₁.1 u v, hq₂.1 u v]
  · intro v hv
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have p1 := hq₁.2 v hv; have p2 := hq₂.2 v hv
    have hab' : 0 < a ∨ 0 < b := by
      by_contra h; rw [not_or, not_lt, not_lt] at h
      have : a = 0 ∧ b = 0 := ⟨le_antisymm h.1 ha, le_antisymm h.2 hb⟩
      rw [this.1, this.2] at hab; norm_num at hab
    rcases hab' with ha' | hb'
    · nlinarith [mul_pos ha' p1, mul_nonneg hb p2.le]
    · nlinarith [mul_nonneg ha p1.le, mul_pos hb' p2]

variable [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M]

set_option maxHeartbeats 1000000 in
/-- **Math.** do Carmo Ch.1 Prop. 2.10 (quoted by Petersen Exercise 1.6.26):
**every (finite-dimensional, σ-compact Hausdorff) differentiable manifold
carries a Riemannian metric.** Construction: pull the Euclidean inner product
of the model space `E` back through the tangent-bundle trivialization on each
chart to get a local symmetric positive-definite section, then glue with a
smooth partition of unity; convexity of the symmetric positive-definite cone
keeps the glued form a metric. -/
theorem exists_riemannianMetric : Nonempty (RiemannianMetric I M) := by
  set V : M → Type _ := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ with hV
  set t : ∀ x, Set (V x) := fun x =>
    {q | (∀ u v, q u v = q v u) ∧ (∀ v, v ≠ 0 → 0 < q v v)} with ht
  have htconv : ∀ x, Convex ℝ (t x) := fun x => convex_symm_posDef x
  have hloc : ∀ x₀ : M, ∃ U ∈ 𝓝 x₀, ∃ s_loc : (x : M) → V x,
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
        (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (s_loc x)) U ∧
      ∀ y ∈ U, s_loc y ∈ t y := by
    intro x₀
    classical
    -- A fixed symmetric positive-definite form on the model space `E`, obtained by transporting
    -- the Euclidean inner product back through the linear equiv `toEuclidean`.
    set φ : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
      (toEuclidean : E ≃L[ℝ] _).toContinuousLinearMap with hφ
    set B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).bilinearComp φ φ with hB
    have hB_apply : ∀ u v : E, B u v = @inner ℝ _ _ (φ u) (φ v) := fun u v => rfl
    have hφinj : Function.Injective φ := by
      simpa [hφ] using (toEuclidean : E ≃L[ℝ] _).injective
    have hBsymm : ∀ u v : E, B u v = B v u := fun u v => by
      rw [hB_apply, hB_apply]; exact real_inner_comm _ _
    have hBpos : ∀ w : E, w ≠ 0 → 0 < B w w := fun w hw => by
      rw [hB_apply]; exact real_inner_self_pos.2 (fun h => hw (hφinj (by rw [h, map_zero])))
    set eT := trivializationAt E (TangentSpace I) x₀ with heT
    have hx₀ : x₀ ∈ eT.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x₀
    -- `s_loc y` transports `B` back through the tangent trivialization's fibre equiv `τ_y`.
    set s_loc : (y : M) → V y := fun y =>
      if hy : y ∈ eT.baseSet then
        ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
          ((eT.continuousLinearEquivAt ℝ y hy).symm.arrowCongr
            (ContinuousLinearEquiv.refl ℝ ℝ))) B
      else 0 with hsl
    have hsl_apply : ∀ (y : M) (hy : y ∈ eT.baseSet) (u v : TangentSpace I y),
        s_loc y u v = B (eT.continuousLinearEquivAt ℝ y hy u)
          (eT.continuousLinearEquivAt ℝ y hy v) := by
      intro y hy u v
      simp only [hsl, dif_pos hy]
      rfl
    refine ⟨eT.baseSet, eT.open_baseSet.mem_nhds hx₀, s_loc, ?_, ?_⟩
    · -- smoothness: reduce to the coordinate representation, which is the constant `B`
      have hbase : (trivializationAt (E →L[ℝ] E →L[ℝ] ℝ) V x₀).baseSet = eT.baseSet := by
        have htriv0 : (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀)
            = Bundle.Trivial.trivialization M ℝ :=
          Bundle.Trivial.eq_trivialization M ℝ _
        simp only [hom_trivializationAt_baseSet, ← heT, htriv0, Bundle.Trivial.trivialization,
          Set.inter_univ, Set.inter_self]
      rw [← hbase, Bundle.Trivialization.contMDiffOn_section_baseSet_iff]
      refine (contMDiffOn_const (c := B)).congr ?_
      intro y hy
      rw [hbase] at hy
      -- `(eH ⟨y, s_loc y⟩).2 = B` for `y ∈ eT.baseSet`
      refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply]
      have hy₂ : y ∈ (trivializationAt (E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] ℝ) x₀).baseSet := by
        rw [hom_trivializationAt_baseSet]; exact ⟨hy, Set.mem_univ y⟩
      rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ
        (trivializationAt (E →L[ℝ] ℝ) (fun x => TangentSpace I x →L[ℝ] ℝ) x₀) hy₂]
      simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
        ContinuousLinearMap.comp_apply, ← heT]
      have htriv : (trivializationAt ℝ (Bundle.Trivial M ℝ) x₀)
          = Bundle.Trivial.trivialization M ℝ :=
        Bundle.Trivial.eq_trivialization M ℝ _
      simp only [htriv, Bundle.Trivial.continuousLinearMapAt_trivialization,
        ContinuousLinearMap.id_apply, hsl_apply y hy,
        ← Trivialization.symm_continuousLinearEquivAt_eq' eT hy,
        ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
    · -- symmetric positive-definite on baseSet
      intro y hy
      refine ⟨fun u v => ?_, fun v hv => ?_⟩
      · rw [hsl_apply y hy, hsl_apply y hy]; exact hBsymm _ _
      · rw [hsl_apply y hy]
        exact hBpos _ (fun h => hv
          ((eT.continuousLinearEquivAt ℝ y hy).injective (by rw [h, map_zero])))
  obtain ⟨s, hs⟩ := exists_contMDiffSection_forall_mem_convex_of_local
      (I := I) (n := (⊤ : ℕ∞)) V t htconv hloc
  refine ⟨⟨fun b => s b, fun b v w => (hs b).1 v w, fun b v hv => (hs b).2 v hv, ?_,
    s.contMDiff⟩⟩
  intro b
  exact isVonNBounded_of_posDef (E := E) (s b) (fun v hv => (hs b).2 v hv)

end Existence

end PetersenLib

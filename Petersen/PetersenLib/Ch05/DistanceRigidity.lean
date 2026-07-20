import PetersenLib.Ch05.DistanceSegments
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique

/-!
# Petersen Ch. 5, §5.3 — rigidity of the distance-function length bound

`rem:pet-ch5-distance-function-rigidity` — the equality case of Petersen's
Lemma 5.3.2 bound `r(c(b)) − r(c(a)) ≤ L(c)|_a^b`.

The bound is the integrated form of the fibrewise Cauchy–Schwarz inequality
`(r ∘ c)'(s) = g(∇r, ċ(s)) ≤ |∇r|·|ċ(s)| = |ċ(s)|`.  Equality of the two
integrals over `[a,b]` therefore forces equality of the two *integrands* at
every `s ∈ [a,b]` (`integrand_eq_of_integral_eq`), and the equality case of
Cauchy–Schwarz then pins the direction of the velocity
(`velocity_eq_speed_smul_gradient_of_deriv_eq_speed`):

`distanceFunction_velocity_eq_speed_smul_gradient_of_curveLength_eq` —
a curve in `U` realising `L(c)|_a^b = r(c(b)) − r(c(a))` satisfies
`ċ(s) = |ċ(s)| ∇r(c(s))` for every `s ∈ [a,b]`.

`distanceFunction_minimizer_eq_integralCurve_comp` — the remark's second clause:
such a `c` *is* the integral curve `σ` of `∇r` through `c(a)`, reparametrised by
the arclength `φ(s) = ∫_a^s |ċ| = L(c)|_a^s`.  Both `c` and `σ ∘ φ` solve the
first-order **non-autonomous** ODE `y'(s) = |ċ(s)| ∇r(y(s))` with the same value
at `s = a`; the field is Lipschitz in the space variable and merely continuous in
time, which is all Grönwall needs.  `eqOn_Icc_of_hasMFDerivAt_smul` is the
corresponding manifold uniqueness statement for a time-scaled smooth vector
field `(s, y) ↦ f(s) • X(y)`, proved by reading the curves in a chart
(`hasDerivAt_extChartAt_comp_of_hasMFDerivAt`), applying Grönwall there
(`ODE_solution_unique_of_eventually`, `ODE_solution_unique_of_mem_Icc_right`) and
propagating along `[a,b]` by an open–closed argument.

Note that `φ` need not be strictly monotone — `c` may rest on a subinterval and
still realise the bound — so the conclusion is *not* obtained by reparametrising
`c` by arclength; the non-autonomous field absorbs the zeros of `|ċ|`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set Filter MeasureTheory
open scoped Manifold Topology ContDiff

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable [I.Boundaryless]

/-! ## The fibrewise Cauchy–Schwarz equality case -/

/-- **Math.** The equality case of the pointwise bound
`g(∇r, ċ(t)) ≤ |∇r|·|ċ(t)| = |ċ(t)|` underlying Petersen's Lemma 5.3.2:
if `g(∇r, ċ(t))` attains the speed `|ċ(t)|`, then `ċ(t) = |ċ(t)| ∇r(c(t))`,
i.e. the velocity is a nonnegative multiple of the unit gradient. -/
theorem velocity_eq_speed_smul_gradient_of_deriv_eq_speed
    {g : RiemannianMetric I M} {U : Set M} {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {t : ℝ} (hmem : c t ∈ U)
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c t)
    (heq : g.metricInner (c t) (gradient g r (c t)) (velocity (I := I) c t)
             = Real.sqrt (curveSpeedSq (I := I) g c t)) :
    velocity (I := I) c t
      = Real.sqrt (curveSpeedSq (I := I) g c t) • gradient g r (c t) := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hnu : ‖(gradient g r (c t) : TangentSpace I (c t))‖ = 1 := by
    rw [norm_tangent_eq_sqrt_metricInner g (c t), hr.2 (c t) hmem, Real.sqrt_one]
  have hnv : ‖(velocity (I := I) c t : TangentSpace I (c t))‖
      = Real.sqrt (curveSpeedSq (I := I) g c t) := by
    rw [norm_tangent_eq_sqrt_metricInner g (c t),
      curveSpeedSq_eq_metricInner_velocity g hc]
  have hip : (inner ℝ (gradient g r (c t) : TangentSpace I (c t))
        (velocity (I := I) c t : TangentSpace I (c t)) : ℝ)
      = ‖(gradient g r (c t) : TangentSpace I (c t))‖
        * ‖(velocity (I := I) c t : TangentSpace I (c t))‖ := by
    rw [hnu, one_mul, hnv]
    exact heq
  have hkey := inner_eq_norm_mul_iff_real.mp hip
  rw [hnu, one_smul, hnv] at hkey
  exact hkey.symm

/-! ## Equality of integrals forces equality of the integrands -/

/-- **Math.** Two continuous integrands with `D ≤ S` on `[a,b]` and equal
integrals over `[a,b]` agree at every point of `[a,b]`.

`G t = ∫_a^t (S − D)` and `∫_t^b (S − D)` are both nonnegative and sum to `0`,
so `G ≡ 0` on `[a,b]`; the fundamental theorem of calculus identifies `G'` with
`S − D` on `Ioo a b`, and continuity extends the conclusion to `Icc a b`. -/
theorem integrand_eq_of_integral_eq
    {D S : ℝ → ℝ} {a b : ℝ} (hab : a < b) {V : Set ℝ} (hV : IsOpen V) (hsub : Icc a b ⊆ V)
    (hDc : ContinuousOn D V) (hSc : ContinuousOn S V)
    (hDi : IntervalIntegrable D volume a b) (hSi : IntervalIntegrable S volume a b)
    (hle : ∀ t ∈ Icc a b, D t ≤ S t)
    (hint : ∫ s in a..b, D s = ∫ s in a..b, S s) :
    ∀ t ∈ Icc a b, D t = S t := by
  set F : ℝ → ℝ := fun t => S t - D t with hF
  have hFnonneg : ∀ t ∈ Icc a b, 0 ≤ F t := fun t ht => sub_nonneg.mpr (hle t ht)
  have hFcont : ContinuousOn F V := hSc.sub hDc
  have hFi : IntervalIntegrable F volume a b := hSi.sub hDi
  have hFint : ∫ s in a..b, F s = 0 := by
    rw [intervalIntegral.integral_sub hSi hDi, hint, sub_self]
  have hGzero : ∀ t ∈ Icc a b, (∫ s in a..t, F s) = 0 := by
    intro t ht
    have h1 : IntervalIntegrable F volume a t := hFi.mono_set (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1]; exact Icc_subset_Icc le_rfl ht.2)
    have h2 : IntervalIntegrable F volume t b := hFi.mono_set (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.2]; exact Icc_subset_Icc ht.1 le_rfl)
    have hadd : (∫ s in a..t, F s) + (∫ s in t..b, F s) = ∫ s in a..b, F s :=
      intervalIntegral.integral_add_adjacent_intervals h1 h2
    have hn1 : 0 ≤ ∫ s in a..t, F s :=
      intervalIntegral.integral_nonneg ht.1 (fun u hu =>
        hFnonneg u ⟨hu.1, hu.2.trans ht.2⟩)
    have hn2 : 0 ≤ ∫ s in t..b, F s :=
      intervalIntegral.integral_nonneg ht.2 (fun u hu =>
        hFnonneg u ⟨ht.1.trans hu.1, hu.2⟩)
    rw [hFint] at hadd
    linarith
  have hIoo : ∀ t ∈ Ioo a b, F t = 0 := by
    intro t ht
    have htV : t ∈ V := hsub ⟨ht.1.le, ht.2.le⟩
    have hca : ContinuousAt F t := hFcont.continuousAt (hV.mem_nhds htV)
    have h1 : IntervalIntegrable F volume a t := hFi.mono_set (by
      rw [uIcc_of_le hab.le, uIcc_of_le ht.1.le]; exact Icc_subset_Icc le_rfl ht.2.le)
    have hmeas : StronglyMeasurableAtFilter F (𝓝 t) :=
      hFcont.stronglyMeasurableAtFilter hV t htV
    have hFTC1 : HasDerivAt (fun u => ∫ s in a..u, F s) (F t) t :=
      intervalIntegral.integral_hasDerivAt_right h1 hmeas hca
    have hev : (fun u => ∫ s in a..u, F s) =ᶠ[𝓝 t] (fun _ => (0 : ℝ)) := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
      exact hGzero u ⟨hu.1.le, hu.2.le⟩
    have := hFTC1.congr_of_eventuallyEq hev.symm
    simpa using this.unique (hasDerivAt_const t (0 : ℝ))
  have hclos : EqOn F (fun _ => (0 : ℝ)) (Icc a b) := by
    have h1 : closure (Ioo a b) = Icc a b := closure_Ioo (ne_of_lt hab)
    have h2 : EqOn F (fun _ => (0 : ℝ)) (Ioo a b) := fun t ht => hIoo t ht
    exact h2.of_subset_closure (hFcont.mono hsub) continuousOn_const
      (Ioo_subset_Icc_self) (by rw [h1])
  intro t ht
  have h := hclos ht
  simp only [hF] at h
  linarith [h]

/-! ## The rigidity statement -/

/-- **Math.** Petersen **Ch. 5, remark on Lemma 5.3.2** (rigidity).  A smooth
curve `c` staying in the domain `U` of a smooth distance function `r` and
realising the length bound with equality, `L(c)|_a^b = r(c(b)) − r(c(a))`, has
velocity everywhere parallel to the gradient: `ċ(s) = |ċ(s)| ∇r(c(s))` for all
`s ∈ [a,b]`.

Equality of the integrals `∫_a^b g(∇r, ċ) = ∫_a^b |ċ|` forces equality of the
integrands pointwise, which is the Cauchy–Schwarz equality case. -/
theorem distanceFunction_velocity_eq_speed_smul_gradient_of_curveLength_eq
    {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    {c : ℝ → M} {a b : ℝ} (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (heq : curveLength (I := I) g c a b = r (c b) - r (c a)) :
    ∀ t ∈ Icc a b, velocity (I := I) c t
      = Real.sqrt (curveSpeedSq (I := I) g c t) • gradient g r (c t) := by
  set D : ℝ → ℝ :=
    fun s => g.metricInner (c s) (gradient g r (c s)) (velocity (I := I) c s) with hD
  set S : ℝ → ℝ := fun s => Real.sqrt (curveSpeedSq (I := I) g c s) with hS
  have hderiv : ∀ s ∈ Set.uIcc a b, HasDerivAt (fun s => r (c s)) (D s) s := by
    intro s hs
    rw [Set.uIcc_of_le hab.le] at hs
    exact hasDerivAt_distanceFunction_comp hU hr (hcU s hs) (hc.mdifferentiableAt (by norm_num))
  have hSi : IntervalIntegrable S volume a b :=
    (continuous_sqrt_curveSpeedSq g hc).intervalIntegrable a b
  have hVopen : IsOpen (c ⁻¹' U) := hU.preimage hc.continuous
  have hVsub : Icc a b ⊆ c ⁻¹' U := fun s hs => hcU s hs
  have hDcont : ContinuousOn D (c ⁻¹' U) := by
    have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s => r (c s)) (c ⁻¹' U) :=
      hr.1.comp hc.contMDiffOn (fun s hs => hs)
    have hcd : ContDiffOn ℝ ∞ (fun s => r (c s)) (c ⁻¹' U) := hcomp.contDiffOn
    have hdw : ContinuousOn (derivWithin (fun s => r (c s)) (c ⁻¹' U)) (c ⁻¹' U) :=
      hcd.continuousOn_derivWithin hVopen.uniqueDiffOn (by norm_num)
    have hderivcont : ContinuousOn (deriv (fun s => r (c s))) (c ⁻¹' U) :=
      hdw.congr (fun s hs => (derivWithin_of_mem_nhds (hVopen.mem_nhds hs)).symm)
    refine hderivcont.congr (fun s hs => ?_)
    exact ((hasDerivAt_distanceFunction_comp hU hr (show c s ∈ U from hs)
      (hc.mdifferentiableAt (by norm_num))).deriv).symm
  have hDi : IntervalIntegrable D volume a b := by
    refine (hDcont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le hab.le]; exact hVsub
  have hFTC : ∫ s in a..b, D s = r (c b) - r (c a) := by
    simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hDi
  have hSint : ∫ s in a..b, S s = curveLength (I := I) g c a b := (curveLength_def ..).symm
  have hint : ∫ s in a..b, D s = ∫ s in a..b, S s := by rw [hFTC, hSint, heq]
  have hle : ∀ t ∈ Icc a b, D t ≤ S t := fun t ht =>
    distanceFunction_deriv_le_speed hr (hcU t ht) (hc.mdifferentiableAt (by norm_num))
  have hpt := integrand_eq_of_integral_eq hab hVopen hVsub hDcont
    ((continuous_sqrt_curveSpeedSq g hc).continuousOn) hDi hSi hle hint
  intro t ht
  exact velocity_eq_speed_smul_gradient_of_deriv_eq_speed hr (hcU t ht)
    (hc.mdifferentiableAt (by norm_num)) (hpt t ht)

/-! ## Uniqueness for time-scaled vector fields -/

set_option backward.isDefEq.respectTransparency false in
/-- **Eng.** A curve whose differential at `t` is `1 ↦ w` has chart reading
`φ_p ∘ γ` with ordinary derivative the chart transfer `tangentCoordChange` of `w`,
provided `γ t` lies in the chart source at `p`. -/
theorem hasDerivAt_extChartAt_comp_of_hasMFDerivAt {γ : ℝ → M} {t : ℝ} {p : M}
    {w : TangentSpace I (γ t)}
    (hγ : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight w))
    (hsrc : γ t ∈ (extChartAt I p).source) :
    HasDerivAt (↑(extChartAt I p) ∘ γ) (tangentCoordChange I (γ t) p (γ t) w) t := by
  replace hsrc := extChartAt_source I p ▸ hsrc
  rw [hasDerivAt_iff_hasFDerivAt, ← hasMFDerivAt_iff_hasFDerivAt]
  apply (HasMFDerivAt.comp t (hasMFDerivAt_extChartAt (I := I) hsrc) hγ).congr_mfderiv
  rw [ContinuousLinearMap.ext_iff]
  intro a
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply, map_smul,
    ← ContinuousLinearMap.one_apply (R₁ := ℝ) a, ← ContinuousLinearMap.smulRight_apply,
    mfderiv_chartAt_eq_tangentCoordChange hsrc]
  rfl

/-- **Math.** Local uniqueness for the **time-scaled** field `(s, y) ↦ f(s) • X(y)`:
two curves solving `y'(s) = f(s) • X(y(s))` near `t₀` and agreeing at `t₀` agree
near `t₀`.  `X` is `C¹` at the common foot, hence Lipschitz in a chart, and `f` is
merely continuous — Grönwall requires Lipschitz dependence only in the space
variable. -/
theorem eventuallyEq_of_hasMFDerivAt_smul
    {X : Π x : M, TangentSpace I x} {f : ℝ → ℝ} {γ γ' : ℝ → M} {t₀ : ℝ}
    (hf : ContinuousAt f t₀)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) (γ t₀))
    (hγ : ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ t))))
    (hγ' : ∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I γ' t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ' t))))
    (h : γ t₀ = γ' t₀) : γ =ᶠ[𝓝 t₀] γ' := by
  set p : M := γ t₀ with hp
  set X' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I p).symm x) p ((extChartAt I p).symm x)
      (X ((extChartAt I p).symm x)) with hX'
  have hint : I.IsInteriorPoint p := BoundarylessManifold.isInteriorPoint
  rw [contMDiffAt_iff] at hX
  obtain ⟨_, hXd⟩ := hX
  obtain ⟨K, S, hS, hlip⟩ : ∃ K, ∃ S ∈ 𝓝 _, LipschitzOnWith K X' S :=
    (hXd.contDiffAt (range_mem_nhds_isInteriorPoint hint)).snd.exists_lipschitzOnWith
  set C : NNReal := ‖f t₀‖₊ + 1 with hC
  have hfle : ∀ᶠ t in 𝓝 t₀, ‖f t‖₊ ≤ C := by
    have h1 : ∀ᶠ t in 𝓝 t₀, ‖f t‖ < ‖f t₀‖ + 1 :=
      (hf.norm).eventually_lt_const (lt_add_one _)
    filter_upwards [h1] with t ht
    rw [← NNReal.coe_le_coe]
    push_cast
    exact ht.le
  have hlipev : ∀ᶠ t in 𝓝 t₀, LipschitzOnWith (C * K) (fun x ↦ f t • X' x) S := by
    filter_upwards [hfle] with t ht
    intro x hx y hy
    have h1 : edist (f t • X' x) (f t • X' y) = (‖f t‖₊ : ENNReal) * edist (X' x) (X' y) := by
      rw [edist_smul₀]; simp [ENNReal.smul_def]
    rw [h1]
    calc (‖f t‖₊ : ENNReal) * edist (X' x) (X' y)
        ≤ (C : ENNReal) * ((K : ENNReal) * edist x y) := by
          gcongr
          exact hlip hx hy
      _ = ((C * K : NNReal) : ENNReal) * edist x y := by push_cast; ring
  have hdrv : ∀ {g : ℝ → M},
      (∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I g t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (g t)))) → g t₀ = p →
      ∀ᶠ t in 𝓝 t₀, HasDerivAt (↑(extChartAt I p) ∘ g)
        ((fun t x ↦ f t • X' x) t ((↑(extChartAt I p) ∘ g) t)) t ∧
        (↑(extChartAt I p) ∘ g) t ∈ S := by
    intro g hg h'
    have hgc : ContinuousAt g t₀ := hg.self_of_nhds.mdifferentiableAt.continuousAt
    have hsrcev : ∀ᶠ t in 𝓝 t₀, g t ∈ (extChartAt I p).source := by
      refine hgc.preimage_mem_nhds ?_
      rw [h']
      exact extChartAt_source_mem_nhds p
    have hSev : ∀ᶠ t in 𝓝 t₀, (↑(extChartAt I p) ∘ g) t ∈ S := by
      have hcc : ContinuousAt (↑(extChartAt I p) ∘ g) t₀ := by
        refine ContinuousAt.comp ?_ hgc
        rw [h']; exact continuousAt_extChartAt p
      refine hcc.preimage_mem_nhds ?_
      simp only [Function.comp_apply, h']
      exact hS
    filter_upwards [hg, hsrcev, hSev] with t ht hts htS
    refine ⟨?_, htS⟩
    have hd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt (p := p) ht hts
    refine hd.congr_deriv ?_
    simp only [hX', Function.comp_apply, ← map_smul]
    congr <;> rw [PartialEquiv.left_inv _ hts]
  have hcomp : (↑(extChartAt I p) ∘ γ) =ᶠ[𝓝 t₀] (↑(extChartAt I p) ∘ γ') := by
    refine ODE_solution_unique_of_eventually hlipev (hdrv hγ rfl) (hdrv hγ' h.symm) ?_
    simp only [Function.comp_apply]
    exact congrArg _ h
  have hback : ∀ {g : ℝ → M},
      (∀ᶠ t in 𝓝 t₀, HasMFDerivAt 𝓘(ℝ, ℝ) I g t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (g t)))) → g t₀ = p →
      g =ᶠ[𝓝 t₀] (extChartAt I p).symm ∘ ↑(extChartAt I p) ∘ g := by
    intro g hg h'
    have hgc : ContinuousAt g t₀ := hg.self_of_nhds.mdifferentiableAt.continuousAt
    have hsrcev : ∀ᶠ t in 𝓝 t₀, g t ∈ (extChartAt I p).source := by
      refine hgc.preimage_mem_nhds ?_
      rw [h']
      exact extChartAt_source_mem_nhds p
    filter_upwards [hsrcev] with t ht
    simp only [Function.comp_apply, PartialEquiv.left_inv _ ht]
  exact (hback hγ rfl).trans
    ((hcomp.fun_comp (extChartAt I p).symm).trans (hback hγ' h.symm).symm)

/-- **Math.** Uniqueness for `y'(s) = f(s) • X(y(s))` on an open interval: the
agreement set is open by the local statement and relatively closed by continuity,
so preconnectedness of `Ioo a b` propagates agreement from a single `t₀`. -/
theorem eqOn_Ioo_of_hasMFDerivAt_smul [T2Space M]
    {X : Π x : M, TangentSpace I x} {f : ℝ → ℝ} {γ γ' : ℝ → M} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo a b) (hf : ContinuousOn f (Ioo a b))
    (hX : ∀ t ∈ Ioo a b, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) (γ t))
    (hγ : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ t))))
    (hγ' : ∀ t ∈ Ioo a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ' t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ' t))))
    (h : γ t₀ = γ' t₀) : EqOn γ γ' (Ioo a b) := by
  set s := {t | γ t = γ' t} ∩ Ioo a b with hs
  suffices hsub : Ioo a b ⊆ s from fun t ht ↦ mem_setOf.mp ((subset_def ▸ hsub) t ht).1
  have hcγ : ∀ t ∈ Ioo a b, ContinuousAt γ t := fun t ht =>
    (hγ t ht).mdifferentiableAt.continuousAt
  have hcγ' : ∀ t ∈ Ioo a b, ContinuousAt γ' t := fun t ht =>
    (hγ' t ht).mdifferentiableAt.continuousAt
  apply isPreconnected_Ioo.subset_of_closure_inter_subset (s := Ioo a b) (u := s) _
    ⟨t₀, ⟨ht₀, ⟨h, ht₀⟩⟩⟩
  · rw [hs, inter_comm, ← Subtype.image_preimage_val, inter_comm, ← Subtype.image_preimage_val,
      image_subset_image_iff Subtype.val_injective, preimage_setOf_eq]
    intro t ht
    rw [mem_preimage, ← closure_subtype] at ht
    revert ht t
    apply IsClosed.closure_subset (isClosed_eq _ _)
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      exact ContinuousAt.comp (hcγ _ ht) continuousAt_subtype_val
    · rw [continuous_iff_continuousAt]
      rintro ⟨_, ht⟩
      exact ContinuousAt.comp (hcγ' _ ht) continuousAt_subtype_val
  · rw [isOpen_iff_mem_nhds]
    intro t₁ ht₁
    have hmem := Ioo_mem_nhds ht₁.2.1 ht₁.2.2
    have heq : γ =ᶠ[𝓝 t₁] γ' := by
      refine eventuallyEq_of_hasMFDerivAt_smul (hf.continuousAt hmem) (hX _ ht₁.2)
        ?_ ?_ ht₁.1
      · filter_upwards [hmem] with t ht using hγ t ht
      · filter_upwards [hmem] with t ht using hγ' t ht
    exact (heq.and hmem).mono fun _ ht ↦ ht

/-- **Math.** Uniqueness for `y'(s) = f(s) • X(y(s))` to the right of the initial
time `a`: on a short interval `[a, b']` a single chart holds both curves, and
Grönwall (`ODE_solution_unique_of_mem_Icc_right`) identifies their chart readings.
This seeds an interior agreement point for `eqOn_Ioo_of_hasMFDerivAt_smul`. -/
theorem exists_eqOn_Icc_right_of_hasMFDerivAt_smul
    {X : Π x : M, TangentSpace I x} {f : ℝ → ℝ} {γ γ' : ℝ → M} {a b : ℝ} (hab : a < b)
    (hf : ContinuousAt f a)
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) (γ a))
    (hγ : ∀ t ∈ Ico a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ t))))
    (hγ' : ∀ t ∈ Ico a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ' t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ' t))))
    (h : γ a = γ' a) : ∃ b' ∈ Ioo a b, EqOn γ γ' (Icc a b') := by
  set p : M := γ a with hp
  set X' : E → E := fun x ↦
    tangentCoordChange I ((extChartAt I p).symm x) p ((extChartAt I p).symm x)
      (X ((extChartAt I p).symm x)) with hX'
  have hint : I.IsInteriorPoint p := BoundarylessManifold.isInteriorPoint
  rw [contMDiffAt_iff] at hX
  obtain ⟨_, hXd⟩ := hX
  obtain ⟨K, S, hS, hlip⟩ : ∃ K, ∃ S ∈ 𝓝 _, LipschitzOnWith K X' S :=
    (hXd.contDiffAt (range_mem_nhds_isInteriorPoint hint)).snd.exists_lipschitzOnWith
  set C : NNReal := ‖f a‖₊ + 1 with hC
  have hγa : ContinuousAt γ a := (hγ a ⟨le_rfl, hab⟩).mdifferentiableAt.continuousAt
  have hγ'a : ContinuousAt γ' a := (hγ' a ⟨le_rfl, hab⟩).mdifferentiableAt.continuousAt
  -- the good set: all the pointwise side conditions hold near `a`
  have hW : ∀ᶠ t in 𝓝 a, ‖f t‖₊ ≤ C ∧ γ t ∈ (extChartAt I p).source ∧
      γ' t ∈ (extChartAt I p).source ∧
      (↑(extChartAt I p) ∘ γ) t ∈ S ∧ (↑(extChartAt I p) ∘ γ') t ∈ S := by
    have h1 : ∀ᶠ t in 𝓝 a, ‖f t‖₊ ≤ C := by
      have := (hf.norm).eventually_lt_const (lt_add_one ‖f a‖)
      filter_upwards [this] with t ht
      rw [← NNReal.coe_le_coe]; push_cast; exact ht.le
    have h2 : ∀ᶠ t in 𝓝 a, γ t ∈ (extChartAt I p).source :=
      hγa.preimage_mem_nhds (extChartAt_source_mem_nhds p)
    have h3 : ∀ᶠ t in 𝓝 a, γ' t ∈ (extChartAt I p).source := by
      refine hγ'a.preimage_mem_nhds ?_
      rw [← h]
      exact extChartAt_source_mem_nhds p
    have h4 : ∀ᶠ t in 𝓝 a, (↑(extChartAt I p) ∘ γ) t ∈ S := by
      have hcc : ContinuousAt (↑(extChartAt I p) ∘ γ) a :=
        ContinuousAt.comp (continuousAt_extChartAt p) hγa
      exact hcc.preimage_mem_nhds hS
    have h5 : ∀ᶠ t in 𝓝 a, (↑(extChartAt I p) ∘ γ') t ∈ S := by
      have hcc : ContinuousAt (↑(extChartAt I p) ∘ γ') a := by
        refine ContinuousAt.comp ?_ hγ'a
        rw [← h]; exact continuousAt_extChartAt p
      refine hcc.preimage_mem_nhds ?_
      simp only [Function.comp_apply, ← h]
      exact hS
    filter_upwards [h1, h2, h3, h4, h5] with t u1 u2 u3 u4 u5 using ⟨u1, u2, u3, u4, u5⟩
  obtain ⟨l, u, hau, hWsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hW
  set b' : ℝ := min ((a + b) / 2) ((a + u) / 2) with hb'
  have hab' : a < b' := lt_min (by linarith) (by linarith [hau.2])
  have hb'b : b' < b := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hb'u : b' < u := lt_of_le_of_lt (min_le_right _ _) (by linarith [hau.2])
  have hsub : Icc a b' ⊆ {t | ‖f t‖₊ ≤ C ∧ γ t ∈ (extChartAt I p).source ∧
      γ' t ∈ (extChartAt I p).source ∧
      (↑(extChartAt I p) ∘ γ) t ∈ S ∧ (↑(extChartAt I p) ∘ γ') t ∈ S} := fun t ht =>
    hWsub ⟨lt_of_lt_of_le hau.1 ht.1, lt_of_le_of_lt ht.2 hb'u⟩
  have hIco : Ico a b' ⊆ Ico a b := Ico_subset_Ico le_rfl hb'b.le
  have hIcc : Icc a b' ⊆ Ico a b := fun t ht => ⟨ht.1, lt_of_le_of_lt ht.2 hb'b⟩
  refine ⟨b', ⟨hab', hb'b⟩, ?_⟩
  -- the two chart readings solve the same chart ODE on `[a, b']`
  have hlipev : ∀ t ∈ Ico a b', LipschitzOnWith (C * K) ((fun t x ↦ f t • X' x) t) S := by
    intro t ht
    have hft : ‖f t‖₊ ≤ C := (hsub ⟨ht.1, ht.2.le⟩).1
    intro x hx y hy
    have h1 : edist (f t • X' x) (f t • X' y) = (‖f t‖₊ : ENNReal) * edist (X' x) (X' y) := by
      rw [edist_smul₀]; simp [ENNReal.smul_def]
    rw [h1]
    calc (‖f t‖₊ : ENNReal) * edist (X' x) (X' y)
        ≤ (C : ENNReal) * ((K : ENNReal) * edist x y) := by
          gcongr
          exact hlip hx hy
      _ = ((C * K : NNReal) : ENNReal) * edist x y := by push_cast; ring
  have hdrv : ∀ {g : ℝ → M}, (∀ t ∈ Ico a b, HasMFDerivAt 𝓘(ℝ, ℝ) I g t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (g t)))) →
      (∀ t ∈ Icc a b', g t ∈ (extChartAt I p).source) →
      ∀ t ∈ Ico a b', HasDerivWithinAt (↑(extChartAt I p) ∘ g)
        ((fun t x ↦ f t • X' x) t ((↑(extChartAt I p) ∘ g) t)) (Ici t) t := by
    intro g hg hsrc t ht
    have hts : g t ∈ (extChartAt I p).source := hsrc t ⟨ht.1, ht.2.le⟩
    have hd := hasDerivAt_extChartAt_comp_of_hasMFDerivAt (p := p) (hg t (hIco ht)) hts
    refine (hd.congr_deriv ?_).hasDerivWithinAt
    simp only [hX', Function.comp_apply, ← map_smul]
    congr <;> rw [PartialEquiv.left_inv _ hts]
  have hcont : ∀ {g : ℝ → M}, (∀ t ∈ Ico a b, HasMFDerivAt 𝓘(ℝ, ℝ) I g t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (g t)))) →
      (∀ t ∈ Icc a b', g t ∈ (extChartAt I p).source) →
      ContinuousOn (↑(extChartAt I p) ∘ g) (Icc a b') := by
    intro g hg hsrc t ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.comp ?_ (hg t (hIcc ht)).mdifferentiableAt.continuousAt
    exact continuousAt_extChartAt' (hsrc t ht)
  have hsrcγ : ∀ t ∈ Icc a b', γ t ∈ (extChartAt I p).source := fun t ht => (hsub ht).2.1
  have hsrcγ' : ∀ t ∈ Icc a b', γ' t ∈ (extChartAt I p).source := fun t ht => (hsub ht).2.2.1
  have key : EqOn (↑(extChartAt I p) ∘ γ) (↑(extChartAt I p) ∘ γ') (Icc a b') :=
    ODE_solution_unique_of_mem_Icc_right (s := fun _ => S) hlipev
      (hcont hγ hsrcγ) (hdrv hγ hsrcγ) (fun t ht => (hsub ⟨ht.1, ht.2.le⟩).2.2.2.1)
      (hcont hγ' hsrcγ') (hdrv hγ' hsrcγ') (fun t ht => (hsub ⟨ht.1, ht.2.le⟩).2.2.2.2)
      (by simp only [Function.comp_apply]; exact congrArg _ h)
  intro t ht
  have h1 := key ht
  simp only [Function.comp_apply] at h1
  rw [← PartialEquiv.left_inv _ (hsrcγ t ht), h1, PartialEquiv.left_inv _ (hsrcγ' t ht)]


/-- **Math.** Uniqueness for `y'(s) = f(s) • X(y(s))` on `[a,b]` with the initial
condition at the **endpoint** `a`: the right-local statement produces agreement at
an interior `b'`, the open-interval statement propagates it over `Ioo a b`, and
continuity closes up the endpoints. -/
theorem eqOn_Icc_of_hasMFDerivAt_smul [T2Space M]
    {X : Π x : M, TangentSpace I x} {f : ℝ → ℝ} {γ γ' : ℝ → M} {a b : ℝ} (hab : a < b)
    (hf : Continuous f)
    (hX : ∀ t ∈ Icc a b, ContMDiffAt I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle I M)) (γ t))
    (hγ : ∀ t ∈ Icc a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ t))))
    (hγ' : ∀ t ∈ Icc a b, HasMFDerivAt 𝓘(ℝ, ℝ) I γ' t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (f t • X (γ' t))))
    (h : γ a = γ' a) : EqOn γ γ' (Icc a b) := by
  have hIco : Ico a b ⊆ Icc a b := Ico_subset_Icc_self
  have hIoo : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
  obtain ⟨b', hb'mem, hEq1⟩ := exists_eqOn_Icc_right_of_hasMFDerivAt_smul hab hf.continuousAt
    (hX a ⟨le_rfl, hab.le⟩) (fun t ht => hγ t (hIco ht)) (fun t ht => hγ' t (hIco ht)) h
  have hbase : γ b' = γ' b' := hEq1 ⟨hb'mem.1.le, le_rfl⟩
  have hIooEq : EqOn γ γ' (Ioo a b) :=
    eqOn_Ioo_of_hasMFDerivAt_smul hb'mem hf.continuousOn
      (fun t ht => hX t (hIoo ht)) (fun t ht => hγ t (hIoo ht))
      (fun t ht => hγ' t (hIoo ht)) hbase
  refine hIooEq.of_subset_closure ?_ ?_ hIoo (by rw [closure_Ioo hab.ne])
  · exact fun t ht => (hγ t ht).mdifferentiableAt.continuousAt.continuousWithinAt
  · exact fun t ht => (hγ' t ht).mdifferentiableAt.continuousAt.continuousWithinAt

/-- **Eng.** The differential of a curve `γ : ℝ → M` at `t` is `x ↦ x • ċ(t)`. -/
theorem hasMFDerivAt_smulRight_velocity {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I γ t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (velocity (I := I) γ t)) := by
  have h1 : HasMFDerivAt 𝓘(ℝ, ℝ) I γ t (mfderiv 𝓘(ℝ, ℝ) I γ t) := hγ.hasMFDerivAt
  convert h1 using 1
  ext
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, velocity,
    ← ContinuousLinearMap.map_smul, one_smul]
  rfl

/-- **Eng.** Chain rule for a real reparametrisation: `(σ ∘ φ)˙(t) = φ'(t) • σ̇(φ t)`. -/
theorem hasMFDerivAt_smulRight_velocity_comp {σ : ℝ → M} {φ : ℝ → ℝ} {t : ℝ} {d : ℝ}
    (hσ : MDifferentiableAt 𝓘(ℝ, ℝ) I σ (φ t)) (hφ : HasDerivAt φ d t) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I (fun s ↦ σ (φ s)) t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (d • velocity (I := I) σ (φ t))) := by
  have hf : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) φ t ((1 : ℝ →L[ℝ] ℝ).smulRight d) := by
    have h2 := (hφ.differentiableAt.mdifferentiableAt
      (𝕜 := ℝ) (E := ℝ) (E' := ℝ)).hasMFDerivAt
    rw [mfderiv_eq_fderiv, (hasDerivAt_iff_hasFDerivAt.mp hφ).fderiv] at h2
    exact h2
  have hcomp := HasMFDerivAt.comp t (hasMFDerivAt_smulRight_velocity hσ) hf
  refine hcomp.congr_mfderiv ?_
  ext
  show ((1 : ℝ →L[ℝ] ℝ) ((1 : ℝ →L[ℝ] ℝ) 1 • d)) • velocity (I := I) σ (φ t)
      = ((1 : ℝ →L[ℝ] ℝ) 1) • (d • velocity (I := I) σ (φ t))
  simp

/-- **Math.** Petersen **Ch. 5, remark on Lemma 5.3.2** (second clause).  A smooth
curve `c` in the domain `U` of a smooth distance function `r` realising
`L(c)|_a^b = r(c(b)) − r(c(a))` **is** the integral curve `σ` of `∇r` through
`c(a)`, reparametrised by arclength: `c(s) = σ(φ(s))` with `φ(s) = L(c)|_a^s`.

By the rigidity clause `ċ(s) = |ċ(s)| ∇r(c(s))`, and `φ'(s) = |ċ(s)|`, so both `c`
and `σ ∘ φ` solve `y'(s) = |ċ(s)| ∇r(y(s))` and agree at `s = a`; Grönwall
uniqueness for the time-scaled field concludes. -/
theorem distanceFunction_minimizer_eq_integralCurve_comp [T2Space M]
    {g : RiemannianMetric I M}
    {U : Set M} (hU : IsOpen U) {r : M → ℝ} (hr : IsDistanceFunction g U r)
    (hgrad : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1
      (fun x ↦ (⟨x, gradient g r x⟩ : TangentBundle I M)) U)
    {c : ℝ → M} {a b : ℝ} (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I ∞ c)
    (hcU : ∀ t ∈ Icc a b, c t ∈ U)
    (heq : curveLength (I := I) g c a b = r (c b) - r (c a))
    {σ : ℝ → M} (hσ : ContMDiff 𝓘(ℝ, ℝ) I ∞ σ) (hσ0 : σ 0 = c a)
    (hσint : ∀ u ∈ Icc 0 (curveLength (I := I) g c a b),
      velocity (I := I) σ u = gradient g r (σ u)) :
    ∀ s ∈ Icc a b, c s = σ (curveLength (I := I) g c a s) := by
  set f : ℝ → ℝ := fun s ↦ Real.sqrt (curveSpeedSq (I := I) g c s) with hfdef
  have hfc : Continuous f := continuous_sqrt_curveSpeedSq g hc
  set φ : ℝ → ℝ := fun s ↦ curveLength (I := I) g c a s with hφdef
  have hφ : ∀ s, HasDerivAt φ (f s) s := by
    intro s
    simp only [hφdef, curveLength_def]
    exact intervalIntegral.integral_hasDerivAt_right (hfc.intervalIntegrable a s)
      (hfc.stronglyMeasurable.stronglyMeasurableAtFilter) hfc.continuousAt
  have hL : ∀ s ∈ Icc a b, φ s ∈ Icc 0 (curveLength (I := I) g c a b) := by
    intro s hs
    refine ⟨curveLength_nonneg g c hs.1, ?_⟩
    have hadd := curveLength_additive (I := I) g c (a := a) (c := s) (b := b)
      (hfc.intervalIntegrable a s) (hfc.intervalIntegrable s b)
    have h2 : 0 ≤ curveLength (I := I) g c s b := curveLength_nonneg g c hs.2
    simp only [hφdef]
    linarith
  have hvel := distanceFunction_velocity_eq_speed_smul_gradient_of_curveLength_eq
    hU hr hab hc hcU heq
  have key : EqOn c (fun s ↦ σ (φ s)) (Icc a b) := by
    refine eqOn_Icc_of_hasMFDerivAt_smul (X := gradient g r) hab hfc ?_ ?_ ?_ ?_
    · exact fun t ht ↦ hgrad.contMDiffAt (hU.mem_nhds (hcU t ht))
    · intro t ht
      have h1 := hasMFDerivAt_smulRight_velocity (γ := c) (t := t)
        (hc.mdifferentiableAt (by norm_num))
      rw [hvel t ht] at h1
      exact h1
    · intro t ht
      have h1 := hasMFDerivAt_smulRight_velocity_comp (σ := σ) (φ := φ) (t := t)
        (hσ.mdifferentiableAt (by norm_num)) (hφ t)
      rw [hσint (φ t) (hL t ht)] at h1
      exact h1
    · simp only [hφdef, curveLength_self, hσ0]
  exact fun s hs ↦ key hs

end PetersenLib

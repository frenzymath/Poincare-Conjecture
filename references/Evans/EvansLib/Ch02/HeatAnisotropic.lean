import EvansLib.Ch02.HeatMaxPrinciple

/-!
# Evans, Ch. 2 - anisotropic regularity for the weak heat maximum principle

Evans's class `C^2_1` controls one time derivative and two spatial derivatives,
but does not require mixed space-time or second time derivatives.  The original
maximum-principle API in `HeatMaxPrinciple` assumes joint `C^2` regularity.  This
file isolates the one-dimensional sections actually used by the proof and proves
the perturbed core step under pointwise anisotropic hypotheses.
-/

open Metric Set Filter Function
open scoped Topology

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The time-coordinate line through a space-time point. -/
def heatTimeLine (u : SpaceTime n → ℝ) (p : SpaceTime n) : ℝ → ℝ :=
  fun s => u (p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))

/-- The line through a space-time point in the `j`-th spatial direction. -/
def heatSpaceLine (u : SpaceTime n → ℝ) (p : SpaceTime n) (j : Fin n) : ℝ → ℝ :=
  fun s => u (p + s • EuclideanSpace.single j.succ (1 : ℝ))

/-- The time derivative, expressed without requiring a joint Fréchet derivative. -/
def heatTimeLineDeriv (u : SpaceTime n → ℝ) (p : SpaceTime n) : ℝ :=
  deriv (heatTimeLine u p) 0

/-- The pure second spatial derivative along the `j`-th coordinate line. -/
def heatSpaceLineDeriv2 (u : SpaceTime n → ℝ) (p : SpaceTime n) (j : Fin n) : ℝ :=
  deriv (deriv (heatSpaceLine u p j)) 0

/-- Pointwise regularity sufficient for the weak heat maximum principle: one time
derivative and two derivatives on every pure spatial coordinate line.  In
particular, no mixed derivative or second time derivative is assumed. -/
def HasAnisotropicHeatRegularityAt (u : SpaceTime n → ℝ) (p : SpaceTime n) : Prop :=
  DifferentiableAt ℝ (heatTimeLine u p) 0 ∧
    ∀ j : Fin n, ContDiffAt ℝ 2 (heatSpaceLine u p j) 0

/-- The heat equation written using the anisotropic line derivatives. -/
def SolvesHeatAnisotropicAt (u : SpaceTime n → ℝ) (p : SpaceTime n) : Prop :=
  heatTimeLineDeriv u p = ∑ j : Fin n, heatSpaceLineDeriv2 u p j

lemma HasAnisotropicHeatRegularityAt.sub {u v : SpaceTime n → ℝ} {p : SpaceTime n}
    (hu : HasAnisotropicHeatRegularityAt u p)
    (hv : HasAnisotropicHeatRegularityAt v p) :
    HasAnisotropicHeatRegularityAt (fun q => u q - v q) p := by
  constructor
  · have heq : heatTimeLine (fun q => u q - v q) p =
        heatTimeLine u p - heatTimeLine v p := by
      funext s
      rfl
    rw [heq]
    exact hu.1.sub hv.1
  · intro j
    change ContDiffAt ℝ 2 (heatSpaceLine u p j - heatSpaceLine v p j) 0
    exact (hu.2 j).sub (hv.2 j)

lemma heatTimeLineDeriv_sub {u v : SpaceTime n → ℝ} {p : SpaceTime n}
    (hu : DifferentiableAt ℝ (heatTimeLine u p) 0)
    (hv : DifferentiableAt ℝ (heatTimeLine v p) 0) :
    heatTimeLineDeriv (fun q => u q - v q) p =
      heatTimeLineDeriv u p - heatTimeLineDeriv v p := by
  unfold heatTimeLineDeriv
  change deriv (heatTimeLine u p - heatTimeLine v p) 0 =
    deriv (heatTimeLine u p) 0 - deriv (heatTimeLine v p) 0
  exact deriv_sub hu hv

private lemma differentiableAt_deriv_of_contDiffAt_two {f : ℝ → ℝ} {x : ℝ}
    (hf : ContDiffAt ℝ 2 f x) : DifferentiableAt ℝ (deriv f) x := by
  have hFd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  simpa only [fderiv_apply_one_eq_deriv] using
    hFd.clm_apply (differentiableAt_const (c := (1 : ℝ)))

lemma heatSpaceLineDeriv2_sub {u v : SpaceTime n → ℝ} {p : SpaceTime n} (j : Fin n)
    (hu : ContDiffAt ℝ 2 (heatSpaceLine u p j) 0)
    (hv : ContDiffAt ℝ 2 (heatSpaceLine v p j) 0) :
    heatSpaceLineDeriv2 (fun q => u q - v q) p j =
      heatSpaceLineDeriv2 u p j - heatSpaceLineDeriv2 v p j := by
  let fu := heatSpaceLine u p j
  let fv := heatSpaceLine v p j
  have hevu : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ fu x :=
    (hu.eventually (by simp)).mono fun _ hx => hx.differentiableAt (by norm_num)
  have hevv : ∀ᶠ x in 𝓝 (0 : ℝ), DifferentiableAt ℝ fv x :=
    (hv.eventually (by simp)).mono fun _ hx => hx.differentiableAt (by norm_num)
  have hev : deriv (fu - fv) =ᶠ[𝓝 (0 : ℝ)] fun x => deriv fu x - deriv fv x := by
    filter_upwards [hevu, hevv] with x hux hvx
    exact deriv_sub hux hvx
  have hdu : DifferentiableAt ℝ (deriv fu) 0 :=
    differentiableAt_deriv_of_contDiffAt_two hu
  have hdv : DifferentiableAt ℝ (deriv fv) 0 :=
    differentiableAt_deriv_of_contDiffAt_two hv
  change deriv (deriv (fu - fv)) 0 = deriv (deriv fu) 0 - deriv (deriv fv) 0
  rw [hev.deriv_eq]
  convert deriv_sub hdu hdv using 1
  rfl

variable {U : Set (EuclideanSpace ℝ (Fin n))} {T T' : ℝ} {u : SpaceTime n → ℝ}

/-- **Anisotropic core of the weak parabolic maximum principle.**  For `ε > 0`,
the perturbed function `u - ε t` attains its maximum on the parabolic boundary of
each shorter cylinder.  The proof only differentiates the time coordinate once
and each spatial coordinate twice. -/
theorem exists_parabolicBoundary_isMaxOn_sub_mul_time_anisotropic
    (hU : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hT' : 0 < T') (hT'T : T' < T)
    (hcont : ContinuousOn u (closure (parabolicCylinder U T)))
    (hreg : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      HasAnisotropicHeatRegularityAt u p)
    (hheat : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      SolvesHeatAnisotropicAt u p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ z ∈ parabolicBoundary U T', ∀ p ∈ closure (parabolicCylinder U T'),
      u p - ε * p 0 ≤ u z - ε * z 0 := by
  set v : SpaceTime n → ℝ := fun p => u p - ε * p 0 with hv
  have hsubcl : closure (parabolicCylinder U T') ⊆ closure (parabolicCylinder U T) :=
    closure_mono (parabolicCylinder_subset hT'T.le)
  have hcomp : IsCompact (closure (parabolicCylinder U T')) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_parabolicCylinder hUbdd hT').closure
  have hne : (closure (parabolicCylinder U T')).Nonempty := by
    obtain ⟨x, hx⟩ := hUne
    refine ⟨toSpaceTime T' x, subset_closure ⟨?_, ?_⟩⟩
    · rw [spacePart_toSpaceTime]
      exact hx
    · rw [toSpaceTime_timeCoord]
      exact ⟨hT', le_rfl⟩
  have hvcont : ContinuousOn v (closure (parabolicCylinder U T')) :=
    (hcont.mono hsubcl).sub (Continuous.continuousOn (by fun_prop))
  obtain ⟨q, hqmem, hqmax⟩ := hcomp.exists_isMaxOn hne hvcont
  rw [isMaxOn_iff] at hqmax
  by_cases hqC : q ∈ parabolicCylinder U T'
  swap
  · exact ⟨q, ⟨hqmem, hqC⟩, fun p hp => hqmax p hp⟩
  exfalso
  obtain ⟨hqU, hqt⟩ := hqC
  have hqtT : q 0 ∈ Ioo 0 T := ⟨hqt.1, hqt.2.trans_lt hT'T⟩
  have hregq := hreg q hqU hqtT
  have hheatq := hheat q hqU hqtT
  have hspatial : ∀ j : Fin n, heatSpaceLineDeriv2 u q j ≤ 0 := by
    intro j
    apply deriv_deriv_nonpos_of_isLocalMax
    · have hcs : Continuous fun s : ℝ =>
          spacePart q + s • EuclideanSpace.single j (1 : ℝ) := by fun_prop
      have h0 : spacePart q + (0 : ℝ) • EuclideanSpace.single j (1 : ℝ) ∈ U := by
        simpa using hqU
      have hopen : ∀ᶠ s in 𝓝 (0 : ℝ),
          spacePart q + s • EuclideanSpace.single j (1 : ℝ) ∈ U :=
        hcs.continuousAt.eventually_mem (hU.mem_nhds h0)
      filter_upwards [hopen] with s hs
      have hmax := hqmax
        (q + s • EuclideanSpace.single j.succ (1 : ℝ))
        (subset_closure ⟨by rwa [spacePart_add_smul_single_succ],
          by rwa [timeCoord_add_smul_single_succ]⟩)
      simpa [heatSpaceLine, hv, timeCoord_add_smul_single_succ] using hmax
    · exact (hregq.2 j).continuousAt
  have htimeDeriv : HasDerivAt (heatTimeLine v q) (heatTimeLineDeriv u q - ε) 0 := by
    have huDeriv : HasDerivAt (heatTimeLine u q) (heatTimeLineDeriv u q) 0 := by
      exact hregq.1.hasDerivAt
    have hlin : HasDerivAt (fun s : ℝ => ε * (q 0 + s)) ε 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (q 0)).const_mul ε
    have heq : heatTimeLine v q = fun s => heatTimeLine u q s - ε * (q 0 + s) := by
      funext s
      simp [heatTimeLine, hv]
    rw [heq]
    exact huDeriv.sub hlin
  have htime : 0 ≤ heatTimeLineDeriv u q - ε := by
    apply deriv_nonneg_of_eventually_le_left htimeDeriv
    have hIoo : Ioo (-(q 0)) 0 ∈ 𝓝[<] (0 : ℝ) := by
      refine mem_nhdsWithin.2 ⟨Ioi (-(q 0)), isOpen_Ioi, by simpa using hqt.1, ?_⟩
      rintro s ⟨hs1, hs2⟩
      exact ⟨hs1, hs2⟩
    filter_upwards [hIoo] with s hs
    have hmax := hqmax
      (q + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))
      (subset_closure ⟨by rwa [spacePart_add_smul_single_zero], by
        rw [timeCoord_add_smul_single_zero]
        exact ⟨by linarith [hs.1], by linarith [hs.2, hqt.2]⟩⟩)
    simpa [heatTimeLine] using hmax
  have hsum : ∑ j : Fin n, heatSpaceLineDeriv2 u q j ≤ 0 :=
    Finset.sum_nonpos fun j _ => hspatial j
  unfold SolvesHeatAnisotropicAt at hheatq
  linarith [hheatq, hsum, htime, hε]

/-- **Weak maximum principle with anisotropic regularity.**  A continuous heat
solution on a bounded parabolic cylinder attains its maximum on the parabolic
boundary.  Compared with `exists_parabolicBoundary_isMaxOn`, this version assumes
only the time and pure spatial line derivatives used by the proof. -/
theorem exists_parabolicBoundary_isMaxOn_anisotropic
    (hU : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) (hT : 0 < T)
    (hcont : ContinuousOn u (closure (parabolicCylinder U T)))
    (hreg : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      HasAnisotropicHeatRegularityAt u p)
    (hheat : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      SolvesHeatAnisotropicAt u p) :
    ∃ z ∈ parabolicBoundary U T, ∀ p ∈ closure (parabolicCylinder U T), u p ≤ u z := by
  have hΓcomp : IsCompact (parabolicBoundary U T) :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_parabolicBoundary hU)
      (((isBounded_parabolicCylinder hUbdd hT).closure).subset diff_subset)
  have hΓne := parabolicBoundary_nonempty (U := U) hUne hT
  obtain ⟨zb, hzbΓ, hzbmax⟩ :=
    hΓcomp.exists_isMaxOn hΓne (hcont.mono diff_subset)
  rw [isMaxOn_iff] at hzbmax
  refine ⟨zb, hzbΓ, ?_⟩
  have hstep1 : ∀ T', 0 < T' → T' < T →
      ∀ p ∈ closure (parabolicCylinder U T'), u p ≤ u zb := by
    intro T' hT'0 hT'T p hp
    have hp0 : 0 ≤ p 0 ∧ p 0 ≤ T' := by
      have hslab := closure_parabolicCylinder_subset U T' hp
      exact ⟨hslab.2.1, hslab.2.2⟩
    have hbound : ∀ ε > (0 : ℝ), u p ≤ u zb + ε * T := by
      intro ε hε
      obtain ⟨z, hzΓ', hzmax⟩ :=
        exists_parabolicBoundary_isMaxOn_sub_mul_time_anisotropic
          hU hUbdd hUne hT'0 hT'T hcont hreg hheat hε
      have hz0 : 0 ≤ z 0 :=
        (closure_parabolicCylinder_subset U T' hzΓ'.1).2.1
      have hzΓ : z ∈ parabolicBoundary U T := parabolicBoundary_subset hT'T.le hzΓ'
      have h1 : u p - ε * p 0 ≤ u z - ε * z 0 := hzmax p hp
      have h2 : u z ≤ u zb := hzbmax z hzΓ
      nlinarith [hp0.1, hp0.2, hT'T, hz0]
    by_contra hlt
    rw [not_le] at hlt
    have hεT : (0 : ℝ) < (u p - u zb) / (2 * T) := by positivity
    have hbound' := hbound _ hεT
    have hT2 : (u p - u zb) / (2 * T) * T = (u p - u zb) / 2 := by
      field_simp
    rw [hT2] at hbound'
    linarith
  have hintcase : ∀ r ∈ closure (parabolicCylinder U T), r 0 < T → u r ≤ u zb := by
    intro r hr hrlt
    have hrIcc := closure_parabolicCylinder_subset U T hr
    set T' : ℝ := (r 0 + T) / 2 with hT'def
    have hr0 : 0 ≤ r 0 := hrIcc.2.1
    have hT'0 : 0 < T' := by rw [hT'def]; linarith
    have hT'T : T' < T := by rw [hT'def]; linarith
    have hrT' : r 0 < T' := by rw [hT'def]; linarith
    refine hstep1 T' hT'0 hT'T r ?_
    rw [mem_closure_iff_nhds]
    intro V hV
    have hW : V ∩ {q : SpaceTime n | q 0 < T'} ∈ 𝓝 r :=
      Filter.inter_mem hV
        ((isOpen_Iio.preimage continuous_timeCoord).mem_nhds hrT')
    obtain ⟨w, hwVW, hwC⟩ := mem_closure_iff_nhds.1 hr _ hW
    exact ⟨w, hwVW.1, hwC.1, hwC.2.1, (hwVW.2 : w 0 < T').le⟩
  intro p hp
  have hpIcc := closure_parabolicCylinder_subset U T hp
  rcases lt_or_eq_of_le hpIcc.2.2 with hplt | hpeq
  · exact hintcase p hp hplt
  · have hkey : ∀ s : ℝ, -(T / 2) < s → s < 0 →
        p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) ∈
          closure (parabolicCylinder U T) := by
      intro s hs1 hs2
      rw [mem_closure_iff_nhds]
      intro V hV
      have hcshift : Continuous fun r : SpaceTime n =>
          r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) := by fun_prop
      have hVpre : (fun r : SpaceTime n =>
          r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) ⁻¹' V ∈ 𝓝 p :=
        hcshift.continuousAt.preimage_mem_nhds hV
      have hW : ((fun r : SpaceTime n =>
          r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) ⁻¹' V) ∩
          {r : SpaceTime n | -s < r 0} ∈ 𝓝 p := by
        refine Filter.inter_mem hVpre
          ((isOpen_Ioi.preimage continuous_timeCoord).mem_nhds ?_)
        show -s < p 0
        rw [hpeq]
        linarith
      obtain ⟨r, ⟨hrV, hrW⟩, hrC⟩ := mem_closure_iff_nhds.1 hp _ hW
      refine ⟨r + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), hrV, ?_, ?_⟩
      · rw [spacePart_add_smul_single_zero]
        exact hrC.1
      · rw [timeCoord_add_smul_single_zero]
        have h1 : -s < r 0 := hrW
        have h2 : r 0 ≤ T := hrC.2.2
        exact ⟨by linarith, by linarith⟩
    have hpathC : Continuous fun s : ℝ =>
        p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) := by fun_prop
    have hIooT : Ioo (-(T / 2)) 0 ∈ 𝓝[<] (0 : ℝ) := by
      refine mem_nhdsWithin.2 ⟨Ioi (-(T / 2)), isOpen_Ioi, by simpa using by linarith, ?_⟩
      rintro s ⟨hs1, hs2⟩
      exact ⟨hs1, hs2⟩
    have hpath : Tendsto (fun s : ℝ =>
        p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) (𝓝[<] (0 : ℝ))
        (𝓝[closure (parabolicCylinder U T)] p) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 : Tendsto (fun s : ℝ =>
            p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) (𝓝 0)
            (𝓝 (p + (0 : ℝ) • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) :=
          hpathC.continuousAt
        simp only [zero_smul, add_zero] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [hIooT] with s hs
        exact hkey s hs.1 hs.2
    have hulim : Tendsto (fun s : ℝ =>
        u (p + s • EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ))) (𝓝[<] (0 : ℝ))
        (𝓝 (u p)) := (hcont p hp).tendsto.comp hpath
    refine le_of_tendsto hulim ?_
    filter_upwards [hIooT] with s hs
    refine hintcase _ (hkey s hs.1 hs.2) ?_
    rw [timeCoord_add_smul_single_zero, hpeq]
    linarith [hs.2]

/--
**Uniqueness with anisotropic regularity.** The bounded-domain heat uniqueness
theorem remains valid when the two solutions are described by the line-based
`C^2_1` hypotheses above.
-/
theorem eqOn_closure_of_eqOn_parabolicBoundary_anisotropic {v f : SpaceTime n → ℝ}
    (hU : IsOpen U) (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) (hT : 0 < T)
    (hcu : ContinuousOn u (closure (parabolicCylinder U T)))
    (hcv : ContinuousOn v (closure (parabolicCylinder U T)))
    (hregu : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      HasAnisotropicHeatRegularityAt u p)
    (hregv : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      HasAnisotropicHeatRegularityAt v p)
    (hheatu : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      heatTimeLineDeriv u p = (∑ j : Fin n, heatSpaceLineDeriv2 u p j) + f p)
    (hheatv : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
      heatTimeLineDeriv v p = (∑ j : Fin n, heatSpaceLineDeriv2 v p j) + f p)
    (hbdry : EqOn u v (parabolicBoundary U T)) :
    EqOn u v (closure (parabolicCylinder U T)) := by
  have key : ∀ u₁ u₂ : SpaceTime n → ℝ,
      ContinuousOn u₁ (closure (parabolicCylinder U T)) →
      ContinuousOn u₂ (closure (parabolicCylinder U T)) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        HasAnisotropicHeatRegularityAt u₁ p) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        HasAnisotropicHeatRegularityAt u₂ p) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        heatTimeLineDeriv u₁ p = (∑ j : Fin n, heatSpaceLineDeriv2 u₁ p j) + f p) →
      (∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        heatTimeLineDeriv u₂ p = (∑ j : Fin n, heatSpaceLineDeriv2 u₂ p j) + f p) →
      (∀ z ∈ parabolicBoundary U T, u₁ z = u₂ z) →
      ∀ p ∈ closure (parabolicCylinder U T), u₁ p - u₂ p ≤ 0 := by
    intro u₁ u₂ hc₁ hc₂ hreg₁ hreg₂ hheat₁ hheat₂ h₁₂
    set w : SpaceTime n → ℝ := fun q => u₁ q - u₂ q with hw
    have hwcont : ContinuousOn w (closure (parabolicCylinder U T)) := hc₁.sub hc₂
    have hwreg : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        HasAnisotropicHeatRegularityAt w p := by
      intro p hpU hpt
      exact (hreg₁ p hpU hpt).sub (hreg₂ p hpU hpt)
    have hwheat : ∀ p : SpaceTime n, spacePart p ∈ U → p 0 ∈ Ioo 0 T →
        SolvesHeatAnisotropicAt w p := by
      intro p hpU hpt
      have hr₁ := hreg₁ p hpU hpt
      have hr₂ := hreg₂ p hpU hpt
      have htime := heatTimeLineDeriv_sub hr₁.1 hr₂.1
      have hspace : ∀ j : Fin n,
          heatSpaceLineDeriv2 w p j =
            heatSpaceLineDeriv2 u₁ p j - heatSpaceLineDeriv2 u₂ p j := by
        intro j
        rw [hw]
        exact heatSpaceLineDeriv2_sub j (hr₁.2 j) (hr₂.2 j)
      unfold SolvesHeatAnisotropicAt
      rw [hw, htime, hheat₁ p hpU hpt, hheat₂ p hpU hpt]
      have halg :
          (∑ j : Fin n, heatSpaceLineDeriv2 u₁ p j) + f p -
              ((∑ j : Fin n, heatSpaceLineDeriv2 u₂ p j) + f p) =
            (∑ j : Fin n, heatSpaceLineDeriv2 u₁ p j) -
              (∑ j : Fin n, heatSpaceLineDeriv2 u₂ p j) := by ring
      rw [halg, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      exact (hspace j).symm
    obtain ⟨z, hzΓ, hzmax⟩ :=
      exists_parabolicBoundary_isMaxOn_anisotropic hU hUbdd hUne hT hwcont hwreg hwheat
    intro p hp
    have h0 : w z = 0 := by
      rw [hw]
      simp only [h₁₂ z hzΓ, sub_self]
    exact (hzmax p hp).trans_eq h0
  intro p hp
  have h1 := key u v hcu hcv hregu hregv hheatu hheatv (fun z hz => hbdry hz) p hp
  have h2 := key v u hcv hcu hregv hregu hheatv hheatu
    (fun z hz => (hbdry hz).symm) p hp
  simp only [sub_nonpos] at h1 h2
  exact le_antisymm h1 h2

end EvansLib

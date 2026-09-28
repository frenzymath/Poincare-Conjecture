import EvansLib.Ch02.WaveEnergyContinuity
import EvansLib.Ch02.HeatMaxPrinciple
import EvansLib.Ch02.PolarIntegration
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Evans, Ch. 2 section 2.4.3 -- the shrinking-ball energy reduction

This file isolates the measure-theoretic conclusion of Evans's finite-propagation
argument.  The local conservation law and the sharp lateral-flux estimate live in
`WaveEnergy.lean`.  Here we define the energy on a spatial ball and prove that
antitonicity of the energy on the shrinking balls forces a wave with zero local
Cauchy data to vanish in the corresponding open cone, in every spatial dimension.

Thus the remaining analytic interface is precise: a Reynolds/divergence theorem
must show that `waveConeEnergy` is antitone for a classical wave.  No positivity,
zero-integral, initial-gradient, or final vertical-line argument remains hidden in
that interface.
-/

open Filter MeasureTheory Metric Set

noncomputable section

namespace EvansLib

/-! ## Fixed-time wave energy -/

/-- Twice the usual wave energy on the spatial ball `B(x0,r)` at time `t`. -/
def waveBallEnergy {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (r t : ℝ) : ℝ :=
  ∫ x in ball x0 r, waveEnergyDensity u (toSpaceTime t x)

/-- The wave energy on Evans's shrinking ball `B(x0,t0-t)`. -/
def waveConeEnergy {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (t0 t : ℝ) : ℝ :=
  waveBallEnergy u x0 (t0 - t) t

/-- The energy density restricted to a fixed time slice is continuous in space. -/
lemma waveEnergyDensity_slice_continuous {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (t : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      waveEnergyDensity u (toSpaceTime t x)) := by
  apply (continuous_waveEnergyDensity_of_contDiff hu).comp
  unfold toSpaceTime
  exact (PiLp.continuous_toLp 2 _).comp
    (continuous_const.finCons
      (continuous_pi fun i => PiLp.continuous_apply 2 _ i))

/-- In positive spatial dimension, the energy on Evans's shrinking ball is
continuous up to (and including) the time at which the ball collapses.  The
proof writes the ball integral in polar coordinates and regards its radius as
the upper endpoint of a parameter-dependent interval integral. -/
lemma continuousOn_waveConeEnergy {n : ℕ} [Nonempty (Fin n)]
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n)) (t0 : ℝ) :
    ContinuousOn (waveConeEnergy u x0 t0) (Iic t0) := by
  have hG : Continuous
      (Function.uncurry (fun p : ℝ × ℝ =>
        fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          waveEnergyDensity u
            (toSpaceTime p.1
              (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n)))))) := by
    apply (continuous_waveEnergyDensity_of_contDiff hu).comp
    unfold toSpaceTime
    apply (PiLp.continuous_toLp 2 _).comp
    apply continuous_pi
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact continuous_fst.fst
    · simp only [Fin.cons_succ]
      exact (PiLp.continuous_apply 2 _ j).comp
        (continuous_const.add ((continuous_fst.snd).smul
          (continuous_subtype_val.comp continuous_snd)))
  have hS : Continuous (fun p : ℝ × ℝ =>
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        waveEnergyDensity u
          (toSpaceTime p.1
            (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) := by
    have h := continuous_parametric_integral_of_continuous
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
      (f := fun p : ℝ × ℝ =>
        fun omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
          waveEnergyDensity u
            (toSpaceTime p.1
              (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n)))))
      hG (isCompact_univ :
        IsCompact (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    simpa only [Measure.restrict_univ] using h
  have hF : Continuous (fun p : ℝ × ℝ =>
      p.2 ^ (n - 1) *
        (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          waveEnergyDensity u
            (toSpaceTime p.1
              (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere))) := by
    exact (continuous_snd.pow _).mul hS
  have hJ : Continuous (fun t : ℝ =>
      ∫ r in (0 : ℝ)..(t0 - t),
        r ^ (n - 1) *
          (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            waveEnergyDensity u
              (toSpaceTime t
                (x0 + r • (omega : EuclideanSpace ℝ (Fin n))))
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere))) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (by
        convert hF using 1
        rfl)
      (continuous_const.sub continuous_id)
  apply hJ.continuousOn.congr
  intro t ht
  have hr : 0 ≤ t0 - t := sub_nonneg.mpr ht
  have hcontslice : ContinuousOn
      (fun x : EuclideanSpace ℝ (Fin n) =>
        waveEnergyDensity u (toSpaceTime t x))
      (closedBall x0 (t0 - t)) :=
    (waveEnergyDensity_slice_continuous hu t).continuousOn
  have hint : IntegrableOn
      (fun x : EuclideanSpace ℝ (Fin n) =>
        waveEnergyDensity u (toSpaceTime t x))
      (ball x0 (t0 - t)) volume :=
    hcontslice.integrableOn_compact (isCompact_closedBall x0 (t0 - t))
      |>.mono_set ball_subset_closedBall
  have hp := setIntegral_ball_eq_polar_radius_add (μ := volume) x0 hint
  have hp' : waveBallEnergy u x0 (t0 - t) t =
      ∫ r in Ioo (0 : ℝ) (t0 - t),
        r ^ (n - 1) *
          (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            waveEnergyDensity u
              (toSpaceTime t
                (x0 + r • (omega : EuclideanSpace ℝ (Fin n))))
            ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)) := by
    simpa [waveBallEnergy, finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
      using hp
  rw [waveConeEnergy, hp']
  change (∫ r in Ioo (0 : ℝ) (t0 - t),
      r ^ (n - 1) *
        (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          waveEnergyDensity u
            (toSpaceTime t
              (x0 + r • (omega : EuclideanSpace ℝ (Fin n))))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere))) =
    ∫ r in (0 : ℝ)..(t0 - t),
      r ^ (n - 1) *
        (∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          waveEnergyDensity u
            (toSpaceTime t
              (x0 + r • (omega : EuclideanSpace ℝ (Fin n))))
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere))
  rw [intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]

/-- A continuous nonnegative wave-energy density has zero integral on a
positive-radius open ball exactly when it vanishes pointwise there. -/
lemma waveBallEnergy_eq_zero_iff {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) {x0 : EuclideanSpace ℝ (Fin n)} {r t : ℝ} :
    waveBallEnergy u x0 r t = 0 ↔
      ∀ x ∈ ball x0 r, waveEnergyDensity u (toSpaceTime t x) = 0 := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => waveEnergyDensity u (toSpaceTime t x)
  have hfcont : Continuous f := waveEnergyDensity_slice_continuous hu t
  have hfint : IntegrableOn f (ball x0 r) volume :=
    (hfcont.continuousOn.integrableOn_compact (isCompact_closedBall x0 r)).mono_set
      ball_subset_closedBall
  constructor
  · intro hzero
    have hnonneg : 0 ≤ᵐ[volume.restrict (ball x0 r)] f :=
      (ae_restrict_iff' measurableSet_ball).2 <|
        ae_of_all _ fun x _ => waveEnergyDensity_nonneg u (toSpaceTime t x)
    have hae : f =ᵐ[volume.restrict (ball x0 r)] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae hnonneg hfint).1 (by
        simpa [waveBallEnergy, f] using hzero)
    exact Measure.eqOn_open_of_ae_eq hae isOpen_ball
      hfcont.continuousOn continuousOn_const
  · intro hpoint
    unfold waveBallEnergy
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hpoint x hx

lemma waveBallEnergy_nonneg {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (r t : ℝ) :
    0 ≤ waveBallEnergy u x0 r t := by
  unfold waveBallEnergy
  exact integral_nonneg_of_ae <| Filter.Eventually.of_forall fun x =>
    waveEnergyDensity_nonneg u (toSpaceTime t x)

/-! ## Zero local Cauchy data -/

/-- A spatial partial derivative at time zero vanishes at every interior point
of a ball on which the initial displacement vanishes. -/
lemma waveSpatialDerivative_initial_zero_of_ball {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    {x0 : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hinit : ∀ x ∈ ball x0 r, u (toSpaceTime 0 x) = 0)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ ball x0 r) (i : Fin n) :
    waveSpatialDerivative u i (toSpaceTime 0 x) = 0 := by
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1 : ℝ)
  have hevMem : ∀ᶠ s : ℝ in nhds 0, x + s • e ∈ ball x0 r := by
    have hcont : ContinuousAt (fun s : ℝ => x + s • e) 0 := by fun_prop
    exact hcont (isOpen_ball.mem_nhds (by simpa using hx))
  have hlinePoint (s : ℝ) :
      toSpaceTime 0 x + s • spaceDir n i = toSpaceTime 0 (x + s • e) := by
    ext k
    refine Fin.cases ?_ (fun j => ?_) k
    · simp [toSpaceTime, spaceDir]
    · simp [toSpaceTime, spaceDir, e, Fin.succ_inj]
  have hevZero :
      (fun s : ℝ => u (toSpaceTime 0 x + s • spaceDir n i)) =ᶠ[nhds 0]
        (fun _ => (0 : ℝ)) := by
    filter_upwards [hevMem] with s hs
    rw [hlinePoint]
    exact hinit _ hs
  have hpath : HasDerivAt
      (fun s : ℝ => toSpaceTime 0 x + s • spaceDir n i) (spaceDir n i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (spaceDir n i)).const_add
      (toSpaceTime 0 x)
  have huLine : HasDerivAt
      (fun s : ℝ => u (toSpaceTime 0 x + s • spaceDir n i))
      (waveSpatialDerivative u i (toSpaceTime 0 x)) 0 := by
    have h := (hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
      |>.comp_hasDerivAt 0 hpath
    convert h using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · simp [waveSpatialDerivative]
  exact huLine.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hevZero)

/-- Zero initial displacement and velocity on a ball make its initial wave
energy vanish.  The spatial-gradient part follows by differentiating the local
zero displacement along each spatial coordinate line. -/
lemma waveBallEnergy_initial_eq_zero {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) {x0 : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hinit : ∀ x ∈ ball x0 r, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 r,
      waveTimeDerivative u (toSpaceTime 0 x) = 0) :
    waveBallEnergy u x0 r 0 = 0 := by
  unfold waveBallEnergy
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  apply (waveEnergyDensity_eq_zero_iff u (toSpaceTime 0 x)).2
  exact ⟨hinit_t x hx, fun i =>
    waveSpatialDerivative_initial_zero_of_ball hu hinit hx i⟩

/-! ## From shrinking energy to finite propagation -/

/-- A continuous shrinking-ball energy whose derivative is nonpositive in the
open time interval is antitone on the closed interval.  This is the calculus
interface for the Reynolds/divergence computation in Evans's proof. -/
lemma waveConeEnergy_antitone_of_deriv_nonpos {n : ℕ}
    {u : SpaceTime n → ℝ} {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ}
    (hcont : ContinuousOn (waveConeEnergy u x0 t0) (Icc 0 t0))
    (E' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) t0,
      HasDerivAt (waveConeEnergy u x0 t0) (E' t) t)
    (hE' : ∀ t ∈ Ioo (0 : ℝ) t0, E' t ≤ 0) :
    AntitoneOn (waveConeEnergy u x0 t0) (Icc 0 t0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (0 : ℝ) t0) hcont
  · intro t ht
    rw [interior_Icc] at ht
    exact (hderiv t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Icc] at ht
    rw [(hderiv t ht).deriv]
    exact hE' t ht

/-- For a `C²` field in positive spatial dimension, continuity of the cone
energy is automatic, so a nonpositive derivative directly gives antitonicity. -/
lemma waveConeEnergy_antitone_of_deriv_nonpos_of_contDiff
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ}
    (E' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) t0,
      HasDerivAt (waveConeEnergy u x0 t0) (E' t) t)
    (hE' : ∀ t ∈ Ioo (0 : ℝ) t0, E' t ≤ 0) :
    AntitoneOn (waveConeEnergy u x0 t0) (Icc 0 t0) := by
  apply waveConeEnergy_antitone_of_deriv_nonpos
    ((continuousOn_waveConeEnergy hu x0 t0).mono ?_) E' hderiv hE'
  intro t ht
  exact ht.2

/-- **Finite propagation from shrinking-ball energy monotonicity.**

If the energy on `B(x0,t0-t)` is antitone for `0 <= t <= t0`, then zero
displacement and velocity on the initial ball force `u` to vanish in the open
backward cone.  This is the general-dimensional conclusion of Evans's energy
argument; the PDE is used upstream to establish the antitonicity hypothesis. -/
theorem wave_finite_propagation_of_coneEnergy_antitone {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (henergy : AntitoneOn (waveConeEnergy u x0 t0) (Icc 0 t0)) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 := by
  have hE0 : waveConeEnergy u x0 t0 0 = 0 := by
    simpa [waveConeEnergy] using
      waveBallEnergy_initial_eq_zero hu hinit hinit_t
  have hEzero : ∀ s ∈ Icc (0 : ℝ) t0, waveConeEnergy u x0 t0 s = 0 := by
    intro s hs
    have hle : waveConeEnergy u x0 t0 s ≤ waveConeEnergy u x0 t0 0 :=
      henergy (by exact ⟨le_rfl, ht0.le⟩) hs hs.1
    have hnonneg : 0 ≤ waveConeEnergy u x0 t0 s :=
      waveBallEnergy_nonneg u x0 (t0 - s) s
    linarith
  intro t ht x hx
  have htimeLine : ∀ s ∈ Icc (0 : ℝ) t,
      HasDerivWithinAt (fun s : ℝ => u (toSpaceTime s x)) 0 (Icc (0 : ℝ) t) s := by
    intro s hs
    have hs0 : 0 ≤ s := hs.1
    have hst : s ≤ t := hs.2
    have hst0 : s ≤ t0 := hst.trans ht.2
    have hxs : x ∈ ball x0 (t0 - s) := by
      rw [mem_ball]
      have hdist : dist x x0 < t0 - t := by
        simpa [dist_comm] using hx
      exact hdist.trans_le (by linarith)
    have hEdensity : waveEnergyDensity u (toSpaceTime s x) = 0 := by
      apply (waveBallEnergy_eq_zero_iff hu).1
        (show waveBallEnergy u x0 (t0 - s) s = 0 from ?_) x hxs
      simpa [waveConeEnergy] using hEzero s ⟨hs0, hst0⟩
    have hut : waveTimeDerivative u (toSpaceTime s x) = 0 :=
      (waveEnergyDensity_eq_zero_iff u (toSpaceTime s x)).1 hEdensity |>.1
    have hpoint (q : ℝ) :
        toSpaceTime q x = toSpaceTime 0 x + q • timeDir n := by
      ext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp [toSpaceTime, timeDir]
      · simp [toSpaceTime, timeDir]
    have hpath : HasDerivAt (fun q : ℝ => toSpaceTime q x) (timeDir n) s := by
      have hpath' : HasDerivAt
          (fun q : ℝ => toSpaceTime 0 x + q • timeDir n) (timeDir n) s := by
        simpa using
          ((hasDerivAt_id s).smul_const (timeDir n)).const_add (toSpaceTime 0 x)
      have heq : (fun q : ℝ => toSpaceTime q x) =
          fun q : ℝ => toSpaceTime 0 x + q • timeDir n := by
        funext q
        exact hpoint q
      rw [heq]
      exact hpath'
    have huLine : HasDerivAt (fun q : ℝ => u (toSpaceTime q x))
        (waveTimeDerivative u (toSpaceTime s x)) s := by
      have h := (hu.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
        |>.comp_hasDerivAt s hpath
      convert h using 1
      · exact AddCommGroup.ext rfl
      · exact Module.ext rfl
      · rfl
      · simp [waveTimeDerivative]
    exact (huLine.congr_deriv hut).hasDerivWithinAt
  have hbound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Icc (0 : ℝ) t) (f := fun s : ℝ => u (toSpaceTime s x))
    (f' := fun _ => (0 : ℝ)) (C := 0) (x := 0) (y := t)
    htimeLine (fun s hs => by simp) (convex_Icc 0 t)
    ⟨le_rfl, ht.1⟩ ⟨ht.1, le_rfl⟩
  have heq : u (toSpaceTime t x) = u (toSpaceTime 0 x) := by
    have hnorm : ‖u (toSpaceTime t x) - u (toSpaceTime 0 x)‖ = 0 :=
      le_antisymm (by simpa using hbound) (norm_nonneg _)
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  rw [heq]
  apply hinit x
  rw [mem_ball]
  have hdist : dist x x0 < t0 - t := by
    simpa [dist_comm] using hx
  exact hdist.trans_le (by linarith [ht.1])

/-- A derivative-form version of
`wave_finite_propagation_of_coneEnergy_antitone`.  Once a moving-domain
calculation supplies a continuous cone energy and a nonpositive derivative,
finite propagation follows immediately. -/
theorem wave_finite_propagation_of_coneEnergy_deriv_nonpos {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (hcont : ContinuousOn (waveConeEnergy u x0 t0) (Icc 0 t0))
    (E' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) t0,
      HasDerivAt (waveConeEnergy u x0 t0) (E' t) t)
    (hE' : ∀ t ∈ Ioo (0 : ℝ) t0, E' t ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 :=
  wave_finite_propagation_of_coneEnergy_antitone hu ht0 hinit hinit_t
    (waveConeEnergy_antitone_of_deriv_nonpos hcont E' hderiv hE')

/-- Positive-dimensional derivative-form finite propagation with cone-energy
continuity discharged from the `C²` regularity of the wave. -/
theorem wave_finite_propagation_of_coneEnergy_deriv_nonpos_of_contDiff
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (E' : ℝ → ℝ)
    (hderiv : ∀ t ∈ Ioo (0 : ℝ) t0,
      HasDerivAt (waveConeEnergy u x0 t0) (E' t) t)
    (hE' : ∀ t ∈ Ioo (0 : ℝ) t0, E' t ≤ 0) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 :=
  wave_finite_propagation_of_coneEnergy_antitone hu ht0 hinit hinit_t
    (waveConeEnergy_antitone_of_deriv_nonpos_of_contDiff hu E' hderiv hE')

end EvansLib

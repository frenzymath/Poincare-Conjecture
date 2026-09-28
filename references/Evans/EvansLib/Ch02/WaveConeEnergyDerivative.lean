import EvansLib.Ch02.WaveFinitePropagation
import EvansLib.Ch02.ParametricIntegral
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Differentiating the shrinking-ball wave energy

This file supplies the moving-domain calculus in Evans's finite-propagation
argument.  Polar coordinates turn the shrinking-ball energy into an interval
integral with a moving upper endpoint.  We first prove a general Leibniz rule
for that situation, then apply it to the wave-energy density.
-/

open Filter MeasureTheory Metric Set
open scoped ContDiff Interval

noncomputable section

namespace EvansLib

/-- The derivative in the first coordinate of a `C^1` scalar function on
`R x R`, evaluated as a directional Frechet derivative. -/
def firstCoordinateDerivative (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ F p (1, 0)

private lemma continuous_firstCoordinateDerivative {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) :
    Continuous (firstCoordinateDerivative F) := by
  unfold firstCoordinateDerivative
  exact (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const

private lemma hasDerivAt_firstCoordinateSlice {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    HasDerivAt (fun t => F (t, p.2)) (firstCoordinateDerivative F p) p.1 := by
  have hline : HasDerivAt (fun t : ℝ => (t, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h := (hF.differentiable (by norm_num) p).hasFDerivAt
    |>.comp_hasDerivAt p.1 hline
  convert h using 1
  · exact AddCommGroup.ext rfl
  · exact Module.ext rfl
  · rfl
  · rfl

/-- Differentiation under a fixed interval integral for a jointly `C^1`
integrand. -/
private lemma hasDerivAt_intervalIntegral_firstCoordinate
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (t a b : ℝ) :
    HasDerivAt (fun q => ∫ s in a..b, F (q, s))
      (∫ s in a..b, firstCoordinateDerivative F (t, s)) t := by
  let dF : ℝ × ℝ → ℝ := firstCoordinateDerivative F
  have hdF : Continuous dF := continuous_firstCoordinateDerivative hF
  let K : Set (ℝ × ℝ) := closedBall t 1 ×ˢ uIcc a b
  have hK : IsCompact K := isCompact_closedBall t 1 |>.prod isCompact_uIcc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hdF.continuousOn
  have hmeas : ∀ q : ℝ,
      AEStronglyMeasurable (fun s => F (q, s))
        (volume.restrict (Ι a b)) := by
    intro q
    exact (hF.continuous.comp (continuous_const.prodMk continuous_id))
      |>.aestronglyMeasurable
  have hint : IntervalIntegrable (fun s => F (t, s)) volume a b :=
    (hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hdmeas : AEStronglyMeasurable (fun s => dF (t, s))
      (volume.restrict (Ι a b)) :=
    (hdF.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hbound : ∀ᵐ s ∂volume, s ∈ Ι a b →
      ∀ q ∈ ball t 1, ‖dF (q, s)‖ ≤ C := by
    filter_upwards [] with s hs q hq
    exact hC (q, s) ⟨ball_subset_closedBall hq, uIoc_subset_uIcc hs⟩
  have hdiff : ∀ᵐ s ∂volume, s ∈ Ι a b →
      ∀ q ∈ ball t 1,
        HasDerivAt (fun q => F (q, s)) (dF (q, s)) q := by
    filter_upwards [] with s _hs q _hq
    simpa [dF] using hasDerivAt_firstCoordinateSlice hF (q, s)
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball t 1) (bound := fun _ => C) (x₀ := t)
    (ball_mem_nhds t one_pos)
    (Filter.Eventually.of_forall hmeas) hint hdmeas hbound
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => C) volume a b)
    hdiff).2

/-- Leibniz's rule for a jointly `C^1` integrand with a `C^1` upper
endpoint. -/
theorem hasDerivAt_parametricIntervalIntegral_moving_right
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    {b : ℝ → ℝ} {b' t : ℝ} (hb : HasDerivAt b b' t) (a : ℝ) :
    HasDerivAt (fun q => ∫ s in a..b q, F (q, s))
      ((∫ s in a..b t, firstCoordinateDerivative F (t, s)) +
        b' * F (t, b t)) t := by
  let J : ℝ → ℝ → ℝ := fun q r => ∫ s in a..r, F (q, s)
  let dT : ℝ → ℝ → ℝ := fun q r =>
    ∫ s in a..r, firstCoordinateDerivative F (q, s)
  let dR : ℝ → ℝ → ℝ := fun q r => F (q, r)
  let fT : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun q r =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (dT q r)
  let fR : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun q r =>
    (1 : ℝ →L[ℝ] ℝ).smulRight (dR q r)
  have hpartialT : ∀ p : ℝ × ℝ,
      HasFDerivAt (J · p.2) (fT p.1 p.2) p.1 := by
    intro p
    have h := (hasDerivAt_intervalIntegral_firstCoordinate
      hF p.1 a p.2).hasFDerivAt
    convert h using 1
    · exact AddCommGroup.ext rfl
    · dsimp [fT, dT]
      rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  have hpartialR : ∀ p : ℝ × ℝ,
      HasFDerivAt (J p.1) (fR p.1 p.2) p.2 := by
    intro p
    have hc : Continuous (fun s => F (p.1, s)) :=
      hF.continuous.comp (continuous_const.prodMk continuous_id)
    have h := (hc.integral_hasStrictDerivAt a p.2).hasDerivAt.hasFDerivAt
    convert h using 1
    · exact AddCommGroup.ext rfl
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · dsimp [fR, dR]
      rw [ContinuousLinearMap.smulRight_one_eq_toSpanSingleton]
  have hdT : Continuous (Function.uncurry dT) := by
    simpa [dT, Function.uncurry_def] using
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun p : ℝ × ℝ => fun s =>
          firstCoordinateDerivative F (p.1, s))
        ((continuous_firstCoordinateDerivative hF).comp
          ((continuous_fst.comp continuous_fst).prodMk continuous_snd))
        continuous_snd
  have hfT : Continuous (Function.uncurry fT) := by
    change Continuous (fun p : ℝ × ℝ =>
      (1 : ℝ →L[ℝ] ℝ).smulRight (Function.uncurry dT p))
    fun_prop
  have hfR : Continuous (Function.uncurry fR) := by
    change Continuous (fun p : ℝ × ℝ =>
      (1 : ℝ →L[ℝ] ℝ).smulRight (F p))
    fun_prop
  have hJ : HasFDerivAt (Function.uncurry J)
      ((fT t (b t)).coprod (fR t (b t))) (t, b t) :=
    (hasStrictFDerivAt_uncurry_coprod (f := J) (f₁ := fT) (f₂ := fR)
      (u := (t, b t))
      (Filter.Eventually.of_forall hpartialT)
      (Filter.Eventually.of_forall hpartialR)
      hfT.continuousAt hfR.continuousAt).hasFDerivAt
  have hpath : HasDerivAt (fun q => (q, b q)) (1, b') t :=
    (hasDerivAt_id t).prodMk hb
  have hcomp := hJ.comp_hasDerivAt t hpath
  convert hcomp using 1
  · exact AddCommGroup.ext rfl
  · exact Module.ext rfl
  · rfl
  · simp [fT, fR, dT, dR, ContinuousLinearMap.coprod_apply]

/-! ## The polar wave-energy integrand -/

/-- A `C^2` scalar field has a `C^1` wave-energy density. -/
lemma waveEnergyDensity_contDiff_one {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) : ContDiff ℝ 1 (waveEnergyDensity u) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  have ht : ContDiff ℝ 1 (waveTimeDerivative u) := by
    unfold waveTimeDerivative
    exact hfd.clm_apply contDiff_const
  have hx (i : Fin n) : ContDiff ℝ 1 (waveSpatialDerivative u i) := by
    unfold waveSpatialDerivative
    exact hfd.clm_apply contDiff_const
  have hsum : ContDiff ℝ 1
      (fun p => ∑ i : Fin n, waveSpatialDerivative u i p ^ 2) := by
    apply ContDiff.sum
    intro i _hi
    exact (hx i).pow 2
  unfold waveEnergyDensity
  exact (ht.pow 2).add hsum

/-- A `C^2` scalar field has `C^1` spatial wave-energy flux components. -/
lemma waveEnergyFlux_contDiff_one {n : ℕ} {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (i : Fin n) :
    ContDiff ℝ 1 (waveEnergyFlux u i) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (m := 1) (by norm_num)
  have ht : ContDiff ℝ 1 (waveTimeDerivative u) := by
    unfold waveTimeDerivative
    exact hfd.clm_apply contDiff_const
  have hx : ContDiff ℝ 1 (waveSpatialDerivative u i) := by
    unfold waveSpatialDerivative
    exact hfd.clm_apply contDiff_const
  unfold waveEnergyFlux
  exact (contDiff_const.mul ht).mul hx

/-- The sphere integral of the wave-energy density at a fixed time and radius. -/
def waveSphereEnergyIntegral {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      waveEnergyDensity u
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- The radial integrand in the polar-coordinate expression for twice the
wave energy on a ball. -/
def wavePolarEnergyIntegrand {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ (n - 1) * waveSphereEnergyIntegral u x0 p

private def wavePolarSphereFiber {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 omega : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  waveEnergyDensity u (toSpaceTime p.1 (x0 + p.2 • omega))

private def wavePolarSphereJoint {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n))
    (q : EuclideanSpace ℝ (Fin n) × (ℝ × ℝ)) : ℝ :=
  wavePolarSphereFiber u x0 q.1 q.2

private lemma contDiff_toSpaceTime_comp {n k : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t : E → ℝ} {x : E → EuclideanSpace ℝ (Fin n)}
    (ht : ContDiff ℝ k t) (hx : ContDiff ℝ k x) :
    ContDiff ℝ k (fun q => toSpaceTime (t q) (x q)) := by
  unfold toSpaceTime
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.2
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ht
  · simp only [Fin.cons_succ]
    exact (PiLp.proj 2 (fun _ : Fin n => ℝ) j).contDiff.comp hx

private lemma wavePolarSphereJoint_contDiff_one {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (wavePolarSphereJoint u x0) := by
  change ContDiff ℝ 1 (fun q : EuclideanSpace ℝ (Fin n) × (ℝ × ℝ) =>
    waveEnergyDensity u
      (toSpaceTime q.2.1 (x0 + q.2.2 • q.1)))
  apply (waveEnergyDensity_contDiff_one hu).comp
  apply contDiff_toSpaceTime_comp
  · fun_prop
  · fun_prop

private lemma wavePolarSphereFiber_contDiff_one {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n))
    (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    ContDiff ℝ 1
      (wavePolarSphereFiber u x0
        (omega : EuclideanSpace ℝ (Fin n))) := by
  change ContDiff ℝ 1 (fun p : ℝ × ℝ =>
    waveEnergyDensity u
      (toSpaceTime p.1
        (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n)))))
  apply (waveEnergyDensity_contDiff_one hu).comp
  apply contDiff_toSpaceTime_comp
  · fun_prop
  · fun_prop

private lemma continuous_wavePolarSphereFiber_iteratedFDeriv_one {n : ℕ}
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n))
    (m : ℕ) (hm : m ≤ 1) :
    Continuous (fun q : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × (ℝ × ℝ) =>
      iteratedFDeriv ℝ m
        (wavePolarSphereFiber u x0
          (q.1 : EuclideanSpace ℝ (Fin n))) q.2) := by
  have hpartial := continuous_iteratedFDeriv_partial_of_order
    (wavePolarSphereJoint_contDiff_one hu x0) m hm
  convert hpartial.comp (continuous_subtype_val.prodMap
    (continuous_id : Continuous (fun p : ℝ × ℝ => p))) using 1
  rfl

private theorem iteratedFDeriv_waveSphereEnergyIntegral_one
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n))
    (p : ℝ × ℝ) :
    iteratedFDeriv ℝ 1 (waveSphereEnergyIntegral u x0) p =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        iteratedFDeriv ℝ 1
          (wavePolarSphereFiber u x0
            (omega : EuclideanSpace ℝ (Fin n))) p
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hseries := hasFTaylorSeriesUpTo_parametricIntegral_of_order 1
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
    (fun omega => wavePolarSphereFiber_contDiff_one hu x0 omega)
    (fun m hm =>
      continuous_wavePolarSphereFiber_iteratedFDeriv_one hu x0 m hm)
  have hEq := hseries.eq_iteratedFDeriv (m := 1) (by norm_num) p
  exact hEq.symm

private theorem waveSphereEnergyIntegral_contDiff_one
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (waveSphereEnergyIntegral u x0) := by
  exact contDiff_parametricIntegral_of_order 1
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)
      (fun omega => wavePolarSphereFiber_contDiff_one hu x0 omega)
      (fun m hm =>
        continuous_wavePolarSphereFiber_iteratedFDeriv_one hu x0 m hm)

/-- The polar wave-energy integrand is jointly `C^1` in time and radius. -/
theorem wavePolarEnergyIntegrand_contDiff_one {n : ℕ} [Nonempty (Fin n)]
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n)) :
    ContDiff ℝ 1 (wavePolarEnergyIntegrand u x0) := by
  unfold wavePolarEnergyIntegrand
  exact (contDiff_snd.pow (n - 1)).mul
    (waveSphereEnergyIntegral_contDiff_one hu x0)

private lemma toSpaceTime_hasDerivAt_time {n : ℕ}
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s => toSpaceTime s x) (timeDir n) t := by
  have heq : (fun s => toSpaceTime s x) =
      fun s => toSpaceTime 0 x + s • timeDir n := by
    funext s
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [toSpaceTime, timeDir]
    · simp [toSpaceTime, timeDir]
  rw [heq]
  simpa using
    ((hasDerivAt_id t).smul_const (timeDir n)).const_add (toSpaceTime 0 x)

private lemma continuous_toSpaceTime_comp {n : ℕ} {α : Type*}
    [TopologicalSpace α] {t : α → ℝ}
    {x : α → EuclideanSpace ℝ (Fin n)}
    (ht : Continuous t) (hx : Continuous x) :
    Continuous (fun q => toSpaceTime (t q) (x q)) := by
  unfold toSpaceTime
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using ht
  · simp only [Fin.cons_succ]
    exact (PiLp.continuous_apply 2 _ j).comp hx

private lemma firstCoordinateDerivative_wavePolarSphereFiber
    {n : ℕ} {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n))
    (omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (p : ℝ × ℝ) :
    firstCoordinateDerivative
        (wavePolarSphereFiber u x0
          (omega : EuclideanSpace ℝ (Fin n))) p =
      fderiv ℝ (waveEnergyDensity u)
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
        (timeDir n) := by
  have hfirst := hasDerivAt_firstCoordinateSlice
    (wavePolarSphereFiber_contDiff_one hu x0 omega) p
  have hcomp :=
    ((waveEnergyDensity_contDiff_one hu).differentiable (by norm_num)
      (toSpaceTime p.1
        (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))).hasFDerivAt
      |>.comp_hasDerivAt p.1
        (toSpaceTime_hasDerivAt_time
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))) p.1)
  exact hfirst.unique hcomp

private theorem firstCoordinateDerivative_waveSphereEnergyIntegral
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n))
    (p : ℝ × ℝ) :
    firstCoordinateDerivative (waveSphereEnergyIntegral u x0) p =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ (waveEnergyDensity u)
          (toSpaceTime p.1
            (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
          (timeDir n)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hEq := iteratedFDeriv_waveSphereEnergyIntegral_one hu x0 p
  have hint : Integrable (fun omega : sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      iteratedFDeriv ℝ 1
        (wavePolarSphereFiber u x0
          (omega : EuclideanSpace ℝ (Fin n))) p)
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) :=
    integrable_iteratedFDeriv_apply
      (continuous_wavePolarSphereFiber_iteratedFDeriv_one hu x0 1 le_rfl) p
  have happ := congrArg
    (fun T => T ![((1 : ℝ), (0 : ℝ))]) hEq
  have happ' :
      (iteratedFDeriv ℝ 1 (waveSphereEnergyIntegral u x0) p)
          ![((1 : ℝ), (0 : ℝ))] =
        ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          (iteratedFDeriv ℝ 1
            (wavePolarSphereFiber u x0
              (omega : EuclideanSpace ℝ (Fin n))) p)
            ![((1 : ℝ), (0 : ℝ))]
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
    simpa only [ContinuousMultilinearMap.integral_apply hint] using happ
  simp only [iteratedFDeriv_one_apply] at happ'
  have happ'' :
      fderiv ℝ (waveSphereEnergyIntegral u x0) p (1, 0) =
        ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          fderiv ℝ
            (wavePolarSphereFiber u x0
              (omega : EuclideanSpace ℝ (Fin n))) p (1, 0)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
    simpa using happ'
  change fderiv ℝ (waveSphereEnergyIntegral u x0) p (1, 0) = _
  rw [happ'']
  apply integral_congr_ae
  filter_upwards [] with omega
  exact firstCoordinateDerivative_wavePolarSphereFiber hu x0 omega p

/-- The time derivative of the polar energy integrand is the polar integral of
the pointwise time derivative of the energy density. -/
theorem firstCoordinateDerivative_wavePolarEnergyIntegrand
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n))
    (p : ℝ × ℝ) :
    firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) p =
      p.2 ^ (n - 1) *
        ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          fderiv ℝ (waveEnergyDensity u)
            (toSpaceTime p.1
              (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
            (timeDir n)
          ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) := by
  have hfirst := hasDerivAt_firstCoordinateSlice
    (wavePolarEnergyIntegrand_contDiff_one hu x0) p
  have hsphere := hasDerivAt_firstCoordinateSlice
    (waveSphereEnergyIntegral_contDiff_one hu x0) p
  have hmul := hsphere.const_mul (p.2 ^ (n - 1))
  have hderiv : firstCoordinateDerivative
      (waveSphereEnergyIntegral u x0) p =
      ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ (waveEnergyDensity u)
          (toSpaceTime p.1
            (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
          (timeDir n)
        ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) :=
    firstCoordinateDerivative_waveSphereEnergyIntegral hu x0 p
  rw [hderiv] at hmul
  exact hfirst.unique (by simpa [wavePolarEnergyIntegrand] using hmul)

/-- The polar integral of the spatial divergence of the wave-energy flux. -/
def wavePolarFluxDivergenceIntegrand {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ (n - 1) *
    ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      (∑ i : Fin n,
        fderiv ℝ (waveEnergyFlux u i)
          (toSpaceTime p.1
            (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
          (spaceDir n i))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- The outward normal flux on a polar sphere, with the same radial Jacobian
as `wavePolarFluxDivergenceIntegrand`. -/
def wavePolarNormalFluxIntegrand {n : ℕ} (u : SpaceTime n → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ (n - 1) *
    ∫ omega : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      waveNormalEnergyFlux u (omega : EuclideanℝN n)
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
      ∂((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere)

/-- Integrating the polar spatial-flux divergence from radius zero to `r`
is exactly integrating the spatial divergence over `B(x0,r)`.  Thus the
remaining boundary-flux identity in the finite-propagation argument is the
ordinary divergence theorem on a ball, with no polar-coordinate conversion
left implicit. -/
theorem intervalIntegral_wavePolarFluxDivergenceIntegrand_eq_ballIntegral
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n))
    {r t : ℝ} (hr : 0 ≤ r) :
    (∫ s in (0 : ℝ)..r, wavePolarFluxDivergenceIntegrand u x0 (t, s)) =
      ∫ x in ball x0 r,
        ∑ i : Fin n,
          fderiv ℝ (waveEnergyFlux u i) (toSpaceTime t x) (spaceDir n i) := by
  have hmap : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      toSpaceTime t x) := by
    apply continuous_toSpaceTime_comp continuous_const
    exact continuous_id
  have hdivcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i : Fin n,
        fderiv ℝ (waveEnergyFlux u i) (toSpaceTime t x) (spaceDir n i)) := by
    apply continuous_finsetSum
    intro i _hi
    have hfderiv : Continuous (fderiv ℝ (waveEnergyFlux u i)) :=
      ((waveEnergyFlux_contDiff_one hu i).fderiv_right
        (m := 0) (by norm_num)).continuous
    exact (hfderiv.comp hmap).clm_apply continuous_const
  have hint : IntegrableOn (fun x : EuclideanSpace ℝ (Fin n) =>
      ∑ i : Fin n,
        fderiv ℝ (waveEnergyFlux u i) (toSpaceTime t x) (spaceDir n i))
      (ball x0 r) volume :=
    (hdivcont.continuousOn.integrableOn_compact (isCompact_closedBall x0 r)).mono_set
      ball_subset_closedBall
  have hp := setIntegral_ball_eq_polar_radius_add (μ := volume) x0 hint
  have hp' :
      (∫ x in ball x0 r,
        ∑ i : Fin n,
          fderiv ℝ (waveEnergyFlux u i) (toSpaceTime t x) (spaceDir n i)) =
        ∫ s in Ioo (0 : ℝ) r,
          wavePolarFluxDivergenceIntegrand u x0 (t, s) := by
    simpa [wavePolarFluxDivergenceIntegrand, finrank_euclideanSpace,
      Fintype.card_fin, smul_eq_mul] using hp
  rw [intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]
  exact hp'.symm

/-! The flux estimate is the elementary boundary part of the energy method. -/

theorem wavePolarNormalFluxIntegrand_le_energy
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n))
    {p : ℝ × ℝ} (hr : 0 ≤ p.2) :
    wavePolarNormalFluxIntegrand u x0 p ≤
      wavePolarEnergyIntegrand u x0 p := by
  let μ : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere
  let hmap : Continuous (fun omega : sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      toSpaceTime p.1
        (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n)))) := by
    apply continuous_toSpaceTime_comp continuous_const
    have hpcont : Continuous
        (fun _ : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => p.2) :=
      continuous_const
    exact continuous_const.add (hpcont.smul continuous_subtype_val)
  have hEcont : Continuous (fun omega : sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      waveEnergyDensity u
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))) := by
    exact (continuous_waveEnergyDensity_of_contDiff hu).comp hmap
  have hNcont : Continuous (fun omega : sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      waveNormalEnergyFlux u (omega : EuclideanℝN n)
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))) := by
    apply continuous_finsetSum
    intro i _hi
    apply Continuous.mul
    · exact (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val
    · exact (continuous_waveEnergyFlux_of_contDiff hu i).comp hmap
  have hEint : Integrable (fun omega : sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      waveEnergyDensity u
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))) μ :=
    hEcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNint : Integrable (fun omega : sphere
      (0 : EuclideanSpace ℝ (Fin n)) 1 =>
      waveNormalEnergyFlux u (omega : EuclideanℝN n)
        (toSpaceTime p.1
          (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))) μ :=
    hNcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let NF : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ := fun omega =>
    waveNormalEnergyFlux u (omega : EuclideanℝN n)
      (toSpaceTime p.1
        (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
  let ED : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ := fun omega =>
    waveEnergyDensity u
      (toSpaceTime p.1
        (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))
  change Integrable NF μ at hNint
  change Integrable ED μ at hEint
  have hinter : (∫ omega, NF omega ∂μ) ≤ ∫ omega, ED omega ∂μ := by
    apply MeasureTheory.integral_mono hNint hEint
    intro omega
    have hω : ‖(omega : EuclideanSpace ℝ (Fin n))‖ = 1 :=
      mem_sphere_zero_iff_norm.1 omega.2
    simpa [NF, ED] using
      wave_moving_boundary_flux_nonpos u (omega : EuclideanℝN n)
      (toSpaceTime p.1
        (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n)))) hω.le
  simpa [wavePolarNormalFluxIntegrand, wavePolarEnergyIntegrand,
    waveSphereEnergyIntegral, NF, ED, μ] using
      mul_le_mul_of_nonneg_left hinter (pow_nonneg hr (n - 1))

/-- For a classical wave, the time derivative of the polar energy integrand
is the polar integral of the spatial flux divergence. -/
theorem firstCoordinateDerivative_wavePolarEnergyIntegrand_eq_fluxDivergence
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 univ (waveSymbol n) u)
    (x0 : EuclideanSpace ℝ (Fin n)) (p : ℝ × ℝ) :
    firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) p =
      wavePolarFluxDivergenceIntegrand u x0 p := by
  rw [firstCoordinateDerivative_wavePolarEnergyIntegrand hu]
  unfold wavePolarFluxDivergenceIntegrand
  congr 1
  apply integral_congr_ae
  filter_upwards [] with omega
  exact wave_energy_conservation_pointwise hu hsol
    (toSpaceTime p.1
      (x0 + p.2 • (omega : EuclideanSpace ℝ (Fin n))))

/-- Polar coordinates express the wave energy on a nonnegative-radius ball as
the interval integral of `wavePolarEnergyIntegrand`. -/
theorem waveBallEnergy_eq_intervalIntegral_wavePolarEnergyIntegrand
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n))
    {r t : ℝ} (hr : 0 ≤ r) :
    waveBallEnergy u x0 r t =
      ∫ s in (0 : ℝ)..r, wavePolarEnergyIntegrand u x0 (t, s) := by
  have hcontslice : ContinuousOn
      (fun x : EuclideanSpace ℝ (Fin n) =>
        waveEnergyDensity u (toSpaceTime t x))
      (closedBall x0 r) :=
    (waveEnergyDensity_slice_continuous hu t).continuousOn
  have hint : IntegrableOn
      (fun x : EuclideanSpace ℝ (Fin n) =>
        waveEnergyDensity u (toSpaceTime t x))
      (ball x0 r) volume :=
    hcontslice.integrableOn_compact (isCompact_closedBall x0 r)
      |>.mono_set ball_subset_closedBall
  have hp := setIntegral_ball_eq_polar_radius_add (μ := volume) x0 hint
  have hp' : waveBallEnergy u x0 r t =
      ∫ s in Ioo (0 : ℝ) r,
        wavePolarEnergyIntegrand u x0 (t, s) := by
    convert hp using 1
    · rfl
    · refine setIntegral_congr_fun measurableSet_Ioo fun s _ => ?_
      simp [wavePolarEnergyIntegrand, waveSphereEnergyIntegral,
        finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul]
  rw [hp']
  rw [intervalIntegral.integral_of_le hr, integral_Ioc_eq_integral_Ioo]

/-- Reynolds's moving-ball derivative before applying the divergence theorem.
The first term differentiates the energy density at fixed polar radius; the
second is the loss through the unit-speed shrinking boundary. -/
theorem waveConeEnergy_hasDerivAt_polar {n : ℕ} [Nonempty (Fin n)]
    {u : SpaceTime n → ℝ} (hu : ContDiff ℝ 2 u)
    (x0 : EuclideanSpace ℝ (Fin n)) {t0 t : ℝ} (ht : t < t0) :
    HasDerivAt (waveConeEnergy u x0 t0)
      ((∫ s in (0 : ℝ)..(t0 - t),
          firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) (t, s)) -
        wavePolarEnergyIntegrand u x0 (t, t0 - t)) t := by
  have hb : HasDerivAt (fun q : ℝ => t0 - q) (-1 : ℝ) t := by
    convert (hasDerivAt_const t t0).sub (hasDerivAt_id t) using 1
    · exact AddCommGroup.ext rfl
    · exact Module.ext rfl
    · rfl
    · norm_num
  have hpolar := hasDerivAt_parametricIntervalIntegral_moving_right
    (wavePolarEnergyIntegrand_contDiff_one hu x0) hb 0
  have heq : waveConeEnergy u x0 t0 =ᶠ[nhds t]
      (fun q => ∫ s in (0 : ℝ)..(t0 - q),
        wavePolarEnergyIntegrand u x0 (q, s)) := by
    filter_upwards [Iio_mem_nhds ht] with q hq
    unfold waveConeEnergy
    exact waveBallEnergy_eq_intervalIntegral_wavePolarEnergyIntegrand
      hu x0 (sub_nonneg.mpr hq.le)
  convert hpolar.congr_of_eventuallyEq heq using 1
  · exact AddCommGroup.ext rfl
  · exact Module.ext rfl
  · ring

/-- If the integrated time derivative of the polar energy is bounded by the
energy on the shrinking boundary, then the cone energy is antitone.  For a
classical wave this inequality is the remaining divergence-theorem step in
Evans's proof. -/
theorem waveConeEnergy_antitone_of_polar_balance
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u) (x0 : EuclideanSpace ℝ (Fin n)) (t0 : ℝ)
    (hbalance : ∀ t ∈ Ioo (0 : ℝ) t0,
      (∫ s in (0 : ℝ)..(t0 - t),
          firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) (t, s)) ≤
        wavePolarEnergyIntegrand u x0 (t, t0 - t)) :
    AntitoneOn (waveConeEnergy u x0 t0) (Icc 0 t0) := by
  let E' : ℝ → ℝ := fun t =>
    (∫ s in (0 : ℝ)..(t0 - t),
        firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) (t, s)) -
      wavePolarEnergyIntegrand u x0 (t, t0 - t)
  apply waveConeEnergy_antitone_of_deriv_nonpos_of_contDiff hu E'
  · intro t ht
    exact waveConeEnergy_hasDerivAt_polar hu x0 ht.2
  · intro t ht
    exact sub_nonpos.mpr (hbalance t ht)

/-- Finite propagation reduced to the integrated polar flux inequality.  All
other parts of Evans's shrinking-energy argument, including the moving-domain
derivative, continuity at the collapsing ball, and recovery of pointwise
vanishing from zero energy, are discharged here. -/
theorem wave_finite_propagation_of_polar_balance
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (hbalance : ∀ t ∈ Ioo (0 : ℝ) t0,
      (∫ s in (0 : ℝ)..(t0 - t),
          firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) (t, s)) ≤
        wavePolarEnergyIntegrand u x0 (t, t0 - t)) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 :=
  wave_finite_propagation_of_coneEnergy_antitone hu ht0 hinit hinit_t
    (waveConeEnergy_antitone_of_polar_balance hu x0 t0 hbalance)

/-- Finite propagation from the polar-coordinate divergence inequality.  The
remaining hypothesis is precisely the ball divergence theorem followed by the
pointwise estimate `wave_moving_boundary_flux_nonpos`. -/
theorem wave_finite_propagation_of_polar_divergence
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 univ (waveSymbol n) u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (hdiv : ∀ t ∈ Ioo (0 : ℝ) t0,
      (∫ s in (0 : ℝ)..(t0 - t),
          wavePolarFluxDivergenceIntegrand u x0 (t, s)) ≤
        wavePolarEnergyIntegrand u x0 (t, t0 - t)) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 := by
  apply wave_finite_propagation_of_polar_balance hu ht0 hinit hinit_t
  intro t ht
  calc
    (∫ s in (0 : ℝ)..(t0 - t),
        firstCoordinateDerivative (wavePolarEnergyIntegrand u x0) (t, s)) =
        ∫ s in (0 : ℝ)..(t0 - t),
          wavePolarFluxDivergenceIntegrand u x0 (t, s) := by
      apply intervalIntegral.integral_congr
      intro s _hs
      exact firstCoordinateDerivative_wavePolarEnergyIntegrand_eq_fluxDivergence
        hu hsol x0 (t, s)
    _ ≤ wavePolarEnergyIntegrand u x0 (t, t0 - t) := hdiv t ht

/-- A divergence-theorem interface for the shrinking ball is enough to finish
Evans's finite-propagation proof.  The interface is stated in polar form so it
can be discharged independently of the energy argument. -/
theorem wave_finite_propagation_of_polar_flux_identity
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 univ (waveSymbol n) u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (hflux : ∀ t ∈ Ioo (0 : ℝ) t0,
      (∫ s in (0 : ℝ)..(t0 - t),
          wavePolarFluxDivergenceIntegrand u x0 (t, s)) =
        wavePolarNormalFluxIntegrand u x0 (t, t0 - t)) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 := by
  apply wave_finite_propagation_of_polar_divergence hu hsol ht0 hinit hinit_t
  intro t ht
  rw [hflux t ht]
  exact wavePolarNormalFluxIntegrand_le_energy hu x0
    (p := (t, t0 - t)) (sub_nonneg.mpr ht.2.le)

/-- The same finite-propagation conclusion with the divergence-theorem input
stated directly as a volume integral over each shrinking ball. -/
theorem wave_finite_propagation_of_ball_flux_identity
    {n : ℕ} [Nonempty (Fin n)] {u : SpaceTime n → ℝ}
    (hu : ContDiff ℝ 2 u)
    (hsol : IsPDESolutionOn 2 univ (waveSymbol n) u)
    {x0 : EuclideanSpace ℝ (Fin n)} {t0 : ℝ} (ht0 : 0 < t0)
    (hinit : ∀ x ∈ ball x0 t0, u (toSpaceTime 0 x) = 0)
    (hinit_t : ∀ x ∈ ball x0 t0,
      waveTimeDerivative u (toSpaceTime 0 x) = 0)
    (hflux : ∀ t ∈ Ioo (0 : ℝ) t0,
      (∫ x in ball x0 (t0 - t),
        ∑ i : Fin n,
          fderiv ℝ (waveEnergyFlux u i) (toSpaceTime t x) (spaceDir n i)) =
        wavePolarNormalFluxIntegrand u x0 (t, t0 - t)) :
    ∀ t ∈ Icc (0 : ℝ) t0, ∀ x ∈ ball x0 (t0 - t),
      u (toSpaceTime t x) = 0 := by
  apply wave_finite_propagation_of_polar_flux_identity hu hsol ht0 hinit hinit_t
  intro t ht
  rw [intervalIntegral_wavePolarFluxDivergenceIntegrand_eq_ballIntegral hu x0
    (t := t) (r := t0 - t) (sub_nonneg.mpr ht.2.le)]
  exact hflux t ht

end EvansLib

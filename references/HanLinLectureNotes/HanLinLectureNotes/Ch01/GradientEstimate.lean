import HanLinLectureNotes.Ch01.HarmonicMeanValue

/-!
# Han--Lin Chapter 1: sharp interior gradient estimate

This module proves the mean-value kernel of the sharp nonnegative harmonic
gradient estimate. The harmonic-to-mean-value bridge is developed separately.
-/

open Filter MeasureTheory Metric Set
open InnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- Scaling and translation invariance of Euclidean ball volume. -/
lemma measureReal_ball_mul [Nonempty (Fin n)]
    (x y : EuclideanSpace Real (Fin n)) (r c : Real) (hc : 0 <= c) :
    volume.real (ball x (c * r)) = c ^ n * volume.real (ball y r) := by
  have hfr : Module.finrank Real (EuclideanSpace Real (Fin n)) = n :=
    finrank_euclideanSpace_fin
  have hmul := Measure.addHaar_ball_mul
    (volume : Measure (EuclideanSpace Real (Fin n))) x hc r
  rw [hfr] at hmul
  have hcenter : volume (ball (0 : EuclideanSpace Real (Fin n)) r) =
      volume (ball y r) :=
    (Measure.addHaar_ball_center volume y r).symm
  rw [hcenter] at hmul
  have hreal : volume.real (ball x (c * r)) =
      (ENNReal.ofReal (c ^ n) * volume (ball y r)).toReal := by
    rw [Measure.real, hmul]
  rw [hreal, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hc n),
    Measure.real]

/-- A nonnegative function with the ball mean-value property satisfies the
sharp nested-ball comparison used in Han--Lin Lemma 1.11. -/
theorem meanValue_pointwise_harnack [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))}
    (hu : HasBallMeanValueProperty u Omega) (hcont : ContinuousOn u Omega)
    (hnonneg : forall z, z ∈ Omega -> 0 <= u z)
    {x y : EuclideanSpace Real (Fin n)} {R : Real} (hR : 0 < R)
    (hxy : dist x y < R) (hball : closedBall x R ⊆ Omega) :
    u y <= (R / (R - dist x y)) ^ n * u x := by
  let rho : Real := R - dist x y
  have hrho : 0 < rho := by simp only [rho]; linarith
  have hsubClosed : closedBall y rho ⊆ closedBall x R :=
    closedBall_subset_closedBall' (by simp only [rho]; rw [dist_comm]; linarith)
  have hsubOpen : ball y rho ⊆ ball x R :=
    ball_subset_ball' (by simp only [rho]; rw [dist_comm]; linarith)
  have hyOmega : closedBall y rho ⊆ Omega := hsubClosed.trans hball
  have hVy : 0 < volume.real (ball y rho) := measureReal_ball_pos hrho
  have hVx : 0 < volume.real (ball x R) := measureReal_ball_pos hR
  have huy : u y = (volume.real (ball y rho))⁻¹ * ∫ z in ball y rho, u z := by
    rw [← smul_eq_mul, ← setAverage_eq]
    exact hu hrho hyOmega
  have hux : u x = (volume.real (ball x R))⁻¹ * ∫ z in ball x R, u z := by
    rw [← smul_eq_mul, ← setAverage_eq]
    exact hu hR hball
  have hint : IntegrableOn u (ball x R) volume :=
    integrableOn_ball_of_continuousOn hcont hball
  have hnn : 0 ≤ᵐ[volume.restrict (ball x R)] u :=
    (ae_restrict_iff' measurableSet_ball).2 <|
      ae_of_all _ fun z hz => hnonneg z (hball (ball_subset_closedBall hz))
  have hmono : ∫ z in ball y rho, u z <= ∫ z in ball x R, u z :=
    setIntegral_mono_set hint hnn hsubOpen.eventuallyLE
  have hc : 0 <= R / rho := div_nonneg hR.le hrho.le
  have hscale : R / rho * rho = R := div_mul_cancel₀ R hrho.ne'
  have hV := measureReal_ball_mul x y rho (R / rho) hc
  rw [hscale] at hV
  have key : (R / rho) ^ n * u x =
      (volume.real (ball y rho))⁻¹ * ∫ z in ball x R, u z := by
    rw [hux, hV]
    field_simp
  rw [show R - dist x y = rho by rfl, key, huy]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- Mean-value form of Han--Lin Lemma 1.11. A differentiable nonnegative
function with the ball mean-value property has the sharp center estimate
`||Du(x)|| <= n / R * u(x)`. -/
theorem fderiv_norm_le_of_nonnegative_meanValue [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))}
    (hu : HasBallMeanValueProperty u Omega) (hcont : ContinuousOn u Omega)
    (hnonneg : forall z, z ∈ Omega -> 0 <= u z)
    {x : EuclideanSpace Real (Fin n)} {R : Real} (hR : 0 < R)
    (hball : closedBall x R ⊆ Omega) (hdiff : DifferentiableAt Real u x) :
    ‖fderiv Real u x‖ <= (n : Real) / R * u x := by
  let L : EuclideanSpace Real (Fin n) →L[Real] Real := fderiv Real u x
  let M : Real := (n : Real) / R * u x
  have hxOmega : x ∈ Omega := hball (mem_closedBall_self hR.le)
  have hux0 : 0 <= u x := hnonneg x hxOmega
  have hM0 : 0 <= M := by
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg n) hR.le) hux0
  have hupper (v : EuclideanSpace Real (Fin n)) : L v <= M * ‖v‖ := by
    let g : Real -> Real := fun t => u (x + t • v)
    let q : Real -> Real := fun t => (R / (R - t * ‖v‖)) ^ n * u x
    have hline : HasDerivAt (fun t : Real => x + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : Real)).smul_const v).const_add x
    have hg : HasDerivAt g (L v) 0 := by
      have hdiff' : HasFDerivAt u L (x + (0 : Real) • v) := by
        simpa [L] using hdiff.hasFDerivAt
      have hcomp := hdiff'.comp_hasDerivAt (0 : Real) hline
      simpa [g, L, Function.comp_def] using hcomp
    have hden : HasDerivAt (fun t : Real => R - t * ‖v‖) (-‖v‖) 0 := by
      simpa using ((hasDerivAt_id (0 : Real)).mul_const ‖v‖).const_sub R
    have hfrac : HasDerivAt (fun t : Real => R / (R - t * ‖v‖)) (‖v‖ / R) 0 := by
      have h := (hasDerivAt_const (0 : Real) R).div hden (by simpa using hR.ne')
      change HasDerivAt (fun t : Real => R / (R - t * ‖v‖))
        ((0 * (R - 0 * ‖v‖) - R * (-‖v‖)) / (R - 0 * ‖v‖) ^ 2) 0 at h
      have heq : (0 * (R - 0 * ‖v‖) - R * (-‖v‖)) /
          (R - 0 * ‖v‖) ^ 2 = ‖v‖ / R := by
        field_simp [hR.ne']; ring
      rwa [heq] at h
    have hpow : HasDerivAt (fun t : Real => (R / (R - t * ‖v‖)) ^ n)
        ((n : Real) * ‖v‖ / R) 0 := by
      have h := hfrac.pow n
      change HasDerivAt (fun t : Real => (R / (R - t * ‖v‖)) ^ n)
        ((n : Real) * (R / (R - 0 * ‖v‖)) ^ (n - 1) * (‖v‖ / R)) 0 at h
      have heq : (n : Real) * (R / (R - 0 * ‖v‖)) ^ (n - 1) * (‖v‖ / R) =
          (n : Real) * ‖v‖ / R := by
        simp [hR.ne']
        ring
      rwa [heq] at h
    have hq : HasDerivAt q (M * ‖v‖) 0 := by
      have h := hpow.mul_const (u x)
      change HasDerivAt q (((n : Real) * ‖v‖ / R) * u x) 0 at h
      have heq : ((n : Real) * ‖v‖ / R) * u x = M * ‖v‖ := by
        dsimp [M]
        ring
      rwa [heq] at h
    have hgt : Tendsto (fun t : Real => t⁻¹ • (g (0 + t) - g 0))
        (nhdsWithin 0 (Ioi 0)) (nhds (L v)) :=
      hg.tendsto_slope_zero.mono_left <|
        nhdsWithin_mono 0 (by
          intro t ht
          simp only [mem_compl_iff, mem_singleton_iff]
          exact ne_of_gt ht)
    have hqt : Tendsto (fun t : Real => t⁻¹ • (q (0 + t) - q 0))
        (nhdsWithin 0 (Ioi 0)) (nhds (M * ‖v‖)) :=
      hq.tendsto_slope_zero.mono_left <|
        nhdsWithin_mono 0 (by
          intro t ht
          simp only [mem_compl_iff, mem_singleton_iff]
          exact ne_of_gt ht)
    let eps : Real := R / (‖v‖ + 1)
    have heps : 0 < eps := div_pos hR (by positivity)
    have hslope : (fun t : Real => t⁻¹ • (g (0 + t) - g 0)) ≤ᶠ[
        nhdsWithin 0 (Ioi 0)]
        (fun t : Real => t⁻¹ • (q (0 + t) - q 0)) := by
      filter_upwards [Ioo_mem_nhdsGT heps] with t ht
      have htnorm : t * ‖v‖ < R := by
        have hlt : t * (‖v‖ + 1) < R := by
          calc
            t * (‖v‖ + 1) < eps * (‖v‖ + 1) :=
              mul_lt_mul_of_pos_right ht.2 (by positivity)
            _ = R := by simp [eps, ne_of_gt (show 0 < ‖v‖ + 1 by positivity)]
        nlinarith [norm_nonneg v]
      have hdist : dist x (x + t • v) = t * ‖v‖ := by
        simp [dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
      have hpoint := meanValue_pointwise_harnack hu hcont hnonneg hR
        (by rw [hdist]; exact htnorm) hball
      have hle : g t <= q t := by simpa [g, q, hdist] using hpoint
      have hg0 : g 0 = u x := by simp [g]
      have hq0 : q 0 = u x := by simp [q, hR.ne']
      have hsub : g t - g 0 <= q t - q 0 := by rw [hg0, hq0]; linarith
      simpa [smul_eq_mul] using
        mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr ht.1.le)
    exact le_of_tendsto_of_tendsto hgt hqt hslope
  refine L.opNorm_le_bound hM0 ?_
  intro v
  have hupp := hupper v
  have hlow : -(M * ‖v‖) <= L v := by
    have h := neg_le_neg (hupper (-v))
    simpa using h
  rw [Real.norm_eq_abs]
  exact abs_le.2 ⟨hlow, hupp⟩

/-- Han--Lin Lemma 1.11. A nonnegative function harmonic in an open ball and
continuous on its closure satisfies the sharp center gradient estimate. -/
theorem IsHarmonicOn.fderiv_norm_le_of_nonnegative_ball [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {x : EuclideanSpace Real (Fin n)} {R : Real} (hR : 0 < R)
    (hu : IsHarmonicOn u (ball x R))
    (hcont : ContinuousOn u (closedBall x R))
    (hnonneg : forall z, z ∈ ball x R -> 0 <= u z) :
    ‖fderiv Real u x‖ <= (n : Real) / R * u x := by
  have hx : x ∈ ball x R := mem_ball_self hR
  have hnhd : HarmonicOnNhd u (ball x R) :=
    (harmonicOnNhd_iff_isHarmonicOn isOpen_ball).2 hu
  have hmean : HasBallMeanValueProperty u (ball x R) :=
    HarmonicOnNhd.hasBallMeanValueProperty hnhd isOpen_ball
  have hdiff : DifferentiableAt Real u x :=
    ((hu.contDiffOn x hx).contDiffAt (isOpen_ball.mem_nhds hx)).differentiableAt
      (by norm_num)
  have hbound : forall s, s ∈ Ioo (0 : Real) R ->
      ‖fderiv Real u x‖ <= (n : Real) / s * u x := by
    intro s hs
    exact fderiv_norm_le_of_nonnegative_meanValue hmean
      (hcont.mono ball_subset_closedBall) hnonneg hs.1
      (closedBall_subset_ball hs.2) hdiff
  have hlimLeft : Tendsto (fun _ : Real => ‖fderiv Real u x‖)
      (nhdsWithin R (Iio R)) (nhds ‖fderiv Real u x‖) :=
    tendsto_const_nhds
  have hlimRight : Tendsto (fun s : Real => (n : Real) / s * u x)
      (nhdsWithin R (Iio R)) (nhds ((n : Real) / R * u x)) := by
    have hcontinuous : ContinuousAt (fun s : Real => (n : Real) / s * u x) R :=
      (continuousAt_const.div continuousAt_id hR.ne').mul continuousAt_const
    exact hcontinuous.tendsto.mono_left inf_le_left
  apply le_of_tendsto_of_tendsto hlimLeft hlimRight
  filter_upwards [Ioo_mem_nhdsLT hR] with s hs
  exact hbound s hs

end HanLinLectureNotes.Ch01

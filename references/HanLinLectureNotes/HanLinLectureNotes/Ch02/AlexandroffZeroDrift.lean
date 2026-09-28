import HanLinLectureNotes.Ch02.Alexandroff
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.Algebra.Module.PerfectSpace

/-!
# Han--Lin Chapter 2: the zero-drift Alexandroff estimate

The constant-weight consequence of the weighted contact inequality.  The
extended-real formulation includes the case where the contact Hessian integral
is infinite.
-/

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- Taking the weight to be one in the Alexandroff contact inequality bounds
the supporting-slope radius by the normalized Hessian integral. -/
theorem alexandroff_zero_weight_slope_bound
    {n : Nat} [NeZero n]
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega) :
    ENNReal.ofReal (alexandroffSlopeRadius Omega u) <=
      ((∫⁻ x in upperContactSet Omega u,
          ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
        mu (Metric.ball (0 : Euclidean n) 1)) ^
          ((n : Real)⁻¹) := by
  let J : ENNReal := ∫⁻ x in upperContactSet Omega u,
    ENNReal.ofReal |(hessianMatrix u x).det| ∂mu
  let omega : ENNReal := mu (Metric.ball (0 : Euclidean n) 1)
  have hn : 0 < (n : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  have homega0 : omega ≠ 0 := by
    simpa only [omega] using
      (ne_of_gt (Metric.measure_ball_pos mu (0 : Euclidean n) one_pos))
  have homegaTop : omega ≠ ⊤ := by
    simpa only [omega] using
      (ne_of_lt (MeasureTheory.measure_ball_lt_top
        (μ := mu) (x := (0 : Euclidean n)) (r := 1)))
  by_cases hr : 0 < alexandroffSlopeRadius Omega u
  · have hcontact :
        mu (Metric.ball (0 : Euclidean n)
          (alexandroffSlopeRadius Omega u)) <= J := by
      have h := alexandroff_weighted_contact_integral
        mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu
        (g := fun _ => (1 : Real)) measurable_const (fun _ => zero_le_one)
        continuous_const.locallyIntegrable
      simpa only [ENNReal.ofReal_one, one_mul, setLIntegral_one, J] using h
    have hball :
        ENNReal.ofReal (alexandroffSlopeRadius Omega u) ^ n * omega <= J := by
      rw [MeasureTheory.Measure.addHaar_ball_of_pos mu
        (0 : Euclidean n) hr] at hcontact
      simpa only [finrank_euclideanSpace, Fintype.card_fin,
        ENNReal.ofReal_pow hr.le, omega] using hcontact
    apply (ENNReal.le_rpow_inv_iff hn).2
    rw [ENNReal.rpow_natCast]
    exact (ENNReal.le_div_iff_mul_le (Or.inl homega0)
      (Or.inl homegaTop)).2 hball
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hr)]
    exact bot_le

/-- Convert a measure bound for the Alexandroff slope ball into a bound for
the positive supremum gap. -/
theorem alexandroff_gap_bound_of_ball_measure_le
    {n : Nat} [NeZero n]
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega) {J : ENNReal}
    (hmeasure :
      mu (Metric.ball (0 : Euclidean n)
        (alexandroffSlopeRadius Omega u)) <= J) :
    ENNReal.ofReal (domainSup Omega u - boundaryPositiveSup Omega u) <=
      ENNReal.ofReal (Metric.diam Omega) *
        (J / mu (Metric.ball (0 : Euclidean n) 1)) ^
          ((n : Real)⁻¹) := by
  have hOmegaNontrivial : Omega.Nontrivial := by
    rcases hOmegaNe with ⟨x, hx⟩
    have hacc : AccPt x (Filter.principal Omega) :=
      hOmegaOpen.preperfect x hx
    rcases (accPt_iff_frequently.mp hacc).exists with ⟨y, hyx, hy⟩
    exact ⟨x, hx, y, hy, hyx.symm⟩
  have hdiam : 0 < Metric.diam Omega :=
    Metric.diam_pos hOmegaNontrivial hOmegaBdd
  have hn : 0 < (n : Real) := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne n))
  let omega : ENNReal := mu (Metric.ball (0 : Euclidean n) 1)
  have homega0 : omega ≠ 0 := by
    simpa only [omega] using
      (ne_of_gt (Metric.measure_ball_pos mu (0 : Euclidean n) one_pos))
  have homegaTop : omega ≠ ⊤ := by
    simpa only [omega] using
      (ne_of_lt (MeasureTheory.measure_ball_lt_top
        (μ := mu) (x := (0 : Euclidean n)) (r := 1)))
  by_cases hgap : 0 < domainSup Omega u - boundaryPositiveSup Omega u
  · have hr : 0 < alexandroffSlopeRadius Omega u := by
      rw [alexandroffSlopeRadius]
      exact div_pos hgap hdiam
    have hball :
        ENNReal.ofReal (alexandroffSlopeRadius Omega u) ^ n * omega <= J := by
      rw [MeasureTheory.Measure.addHaar_ball_of_pos mu
        (0 : Euclidean n) hr] at hmeasure
      simpa only [finrank_euclideanSpace, Fintype.card_fin,
        ENNReal.ofReal_pow hr.le, omega] using hmeasure
    have hslope :
        ENNReal.ofReal (alexandroffSlopeRadius Omega u) <=
          (J / omega) ^ ((n : Real)⁻¹) := by
      apply (ENNReal.le_rpow_inv_iff hn).2
      rw [ENNReal.rpow_natCast]
      exact (ENNReal.le_div_iff_mul_le (Or.inl homega0)
        (Or.inl homegaTop)).2 hball
    calc
      ENNReal.ofReal (domainSup Omega u - boundaryPositiveSup Omega u) =
          ENNReal.ofReal
            (Metric.diam Omega * alexandroffSlopeRadius Omega u) := by
        rw [alexandroffSlopeRadius, mul_div_cancel₀ _ hdiam.ne']
      _ = ENNReal.ofReal (Metric.diam Omega) *
          ENNReal.ofReal (alexandroffSlopeRadius Omega u) :=
        ENNReal.ofReal_mul hdiam.le
      _ <= ENNReal.ofReal (Metric.diam Omega) *
          (J / omega) ^ ((n : Real)⁻¹) :=
        mul_le_mul_right hslope _
  · rw [ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hgap)]
    exact bot_le

/-- The extended-real form of the zero-drift Alexandroff maximum estimate.
It is the first displayed inequality in Han--Lin Remark 2.35, with the
right-hand side normalized by the volume of the unit ball. -/
theorem alexandroff_zero_weight_gap_bound
    {n : Nat} [NeZero n]
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega) :
    ENNReal.ofReal (domainSup Omega u - boundaryPositiveSup Omega u) <=
      ENNReal.ofReal (Metric.diam Omega) *
        (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)) ^
            ((n : Real)⁻¹)) := by
  have hOmegaNontrivial : Omega.Nontrivial := by
    rcases hOmegaNe with ⟨x, hx⟩
    have hacc : AccPt x (Filter.principal Omega) :=
      hOmegaOpen.preperfect x hx
    rcases (accPt_iff_frequently.mp hacc).exists with ⟨y, hyx, hy⟩
    exact ⟨x, hx, y, hy, hyx.symm⟩
  have hdiam : 0 < Metric.diam Omega :=
    Metric.diam_pos hOmegaNontrivial hOmegaBdd
  let q : ENNReal :=
    (((∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
      mu (Metric.ball (0 : Euclidean n) 1)) ^
        ((n : Real)⁻¹))
  have hslope :
      ENNReal.ofReal
          ((domainSup Omega u - boundaryPositiveSup Omega u) /
            Metric.diam Omega) <= q := by
    simpa only [alexandroffSlopeRadius, q] using
      (alexandroff_zero_weight_slope_bound mu hOmegaOpen hOmegaNe
        hOmegaBdd huClosure hu)
  calc
    ENNReal.ofReal (domainSup Omega u - boundaryPositiveSup Omega u) =
        ENNReal.ofReal
          (Metric.diam Omega *
            ((domainSup Omega u - boundaryPositiveSup Omega u) /
              Metric.diam Omega)) := by
        rw [mul_div_cancel₀ _ hdiam.ne']
    _ = ENNReal.ofReal (Metric.diam Omega) *
        ENNReal.ofReal
          ((domainSup Omega u - boundaryPositiveSup Omega u) /
            Metric.diam Omega) := ENNReal.ofReal_mul hdiam.le
    _ <= ENNReal.ofReal (Metric.diam Omega) * q :=
      mul_le_mul_right hslope _

/-- Real-valued form of the zero-drift Alexandroff maximum estimate when the
contact Hessian integral is finite. -/
theorem alexandroff_zero_weight_maximum_estimate
    {n : Nat} [NeZero n]
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    (hfinite :
      (∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) ≠ ⊤) :
    domainSup Omega u <= boundaryPositiveSup Omega u +
      Metric.diam Omega *
        (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)).toReal ^
            ((n : Real)⁻¹)) := by
  let J : ENNReal := ∫⁻ x in upperContactSet Omega u,
    ENNReal.ofReal |(hessianMatrix u x).det| ∂mu
  let omega : ENNReal := mu (Metric.ball (0 : Euclidean n) 1)
  let q : ENNReal := ENNReal.ofReal (Metric.diam Omega) *
    (J / omega) ^ ((n : Real)⁻¹)
  have homega0 : omega ≠ 0 := by
    simpa only [omega] using
      (ne_of_gt (Metric.measure_ball_pos mu (0 : Euclidean n) one_pos))
  have hqTop : q ≠ ⊤ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
    exact ENNReal.div_ne_top (by simpa only [J] using hfinite) homega0
  have hgap := alexandroff_zero_weight_gap_bound
    mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu
  by_cases hgapPos : 0 < domainSup Omega u - boundaryPositiveSup Omega u
  · have hreal := ENNReal.toReal_mono hqTop hgap
    change
      (ENNReal.ofReal
        (domainSup Omega u - boundaryPositiveSup Omega u)).toReal <=
        q.toReal at hreal
    rw [ENNReal.toReal_ofReal hgapPos.le] at hreal
    simp only [q, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal Metric.diam_nonneg, J, omega] at hreal
    rw [← ENNReal.toReal_rpow] at hreal
    linarith
  · have hrootNonneg :
        0 <= (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)).toReal ^
            ((n : Real)⁻¹)) :=
      Real.rpow_nonneg ENNReal.toReal_nonneg _
    have htermNonneg :
        0 <= Metric.diam Omega *
          (((∫⁻ x in upperContactSet Omega u,
              ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
            mu (Metric.ball (0 : Euclidean n) 1)).toReal ^
              ((n : Real)⁻¹)) :=
      mul_nonneg Metric.diam_nonneg hrootNonneg
    linarith [le_of_not_gt hgapPos]

end HanLinLectureNotes.Ch02

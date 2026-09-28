import HanLinLectureNotes.Ch02.AlexandroffOperator
import HanLinLectureNotes.Ch02.AlexandroffZeroDrift

/-!
# Han--Lin Chapter 2: zero-drift Alexandroff consequences

The two constant-weight maximum estimates of Han--Lin Remark 2.35.
-/

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The operator form of the zero-weight Alexandroff estimate. -/
theorem alexandroff_operator_zero_weight_gap_bound
    {n : Nat} (hn : 0 < n)
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    (A : Euclidean n -> Matrix (Fin n) (Fin n) Real)
    (hA : ∀ x ∈ upperContactSet Omega u, (A x).PosDef)
    (Dstar : Euclidean n -> Real)
    (hDstarPos : ∀ x ∈ upperContactSet Omega u, 0 < Dstar x)
    (hDstarPow : ∀ x ∈ upperContactSet Omega u,
      Dstar x ^ n = (A x).det) :
    ENNReal.ofReal (domainSup Omega u - boundaryPositiveSup Omega u) <=
      ENNReal.ofReal (Metric.diam Omega) *
        (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal
              (((-(A x * hessianMatrix u x).trace) /
                ((n : Real) * Dstar x)) ^ n) ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)) ^
            ((n : Real)⁻¹)) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let J : ENNReal :=
    ∫⁻ x in upperContactSet Omega u,
      ENNReal.ofReal
        (((-(A x * hessianMatrix u x).trace) /
          ((n : Real) * Dstar x)) ^ n) ∂mu
  have hmeasure :
      mu (Metric.ball (0 : Euclidean n)
        (alexandroffSlopeRadius Omega u)) <= J := by
    have h := alexandroff_weighted_operator_contact_integral
      hn mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu
        A hA Dstar hDstarPos hDstarPow
        (g := fun _ => (1 : Real)) measurable_const (fun _ => zero_le_one)
        continuous_const.locallyIntegrable
    simpa only [ENNReal.ofReal_one, one_mul, setLIntegral_one, J] using h
  exact alexandroff_gap_bound_of_ball_measure_le
    mu hOmegaOpen hOmegaNe hOmegaBdd hmeasure

/-- Han--Lin Remark 2.35. Taking `g = 1` gives the Hessian-Jacobian maximum
estimate, followed by its determinant--trace operator bound. The inequalities
are stated in `ENNReal`, so the possibly infinite contact integrals are retained. -/
theorem alexandroff_zero_drift_contact_bounds
    {n : Nat} (hn : 0 < n)
    [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    (A : Euclidean n -> Matrix (Fin n) (Fin n) Real)
    (hA : ∀ x ∈ upperContactSet Omega u, (A x).PosDef)
    (Dstar : Euclidean n -> Real)
    (hDstarPos : ∀ x ∈ upperContactSet Omega u, 0 < Dstar x)
    (hDstarPow : ∀ x ∈ upperContactSet Omega u,
      Dstar x ^ n = (A x).det) :
    (ENNReal.ofReal (domainSup Omega u - boundaryPositiveSup Omega u) <=
      ENNReal.ofReal (Metric.diam Omega) *
        (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)) ^
            ((n : Real)⁻¹))) ∧
    (ENNReal.ofReal (Metric.diam Omega) *
        (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)) ^
            ((n : Real)⁻¹)) <=
      ENNReal.ofReal (Metric.diam Omega) *
        (((∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal
              (((-(A x * hessianMatrix u x).trace) /
                ((n : Real) * Dstar x)) ^ n) ∂mu) /
          mu (Metric.ball (0 : Euclidean n) 1)) ^
            ((n : Real)⁻¹))) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  constructor
  · exact alexandroff_zero_weight_gap_bound
      mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu
  · have hIntegral :=
      alexandroff_weighted_hessian_contact_integral_le_operator
        hn mu hOmegaOpen hu A hA Dstar hDstarPos hDstarPow
          (g := fun _ => (1 : Real)) (fun _ => zero_le_one)
    have hIntegral' :
        (∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal |(hessianMatrix u x).det| ∂mu) <=
          ∫⁻ x in upperContactSet Omega u,
            ENNReal.ofReal
              (((-(A x * hessianMatrix u x).trace) /
                ((n : Real) * Dstar x)) ^ n) ∂mu := by
      simpa only [one_mul] using hIntegral
    exact mul_le_mul_right
      (ENNReal.rpow_le_rpow
        (ENNReal.div_le_div_right hIntegral'
          (mu (Metric.ball (0 : Euclidean n) 1))) (by positivity)) _

end HanLinLectureNotes.Ch02

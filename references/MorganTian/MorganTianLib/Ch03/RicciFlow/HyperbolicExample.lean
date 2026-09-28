import MorganTianLib.Ch03.RicciFlow.ExactSolutions
import MorganTianLib.Ch01.ExpBallDiffeo
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh8HyperbolicCurvature

/-!
# Morgan--Tian Ch. 3 -- the hyperbolic Einstein example

The checked do Carmo half-space curvature formula is contracted in an
orthonormal basis to obtain the Einstein constant `-(n-1)`.  The subsequent
Ricci-flow family is supplied by the exact Einstein-scaling calculation.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

open Riemannian.Hyperbolic

variable {n : ℕ} [NeZero n]

/-- **Math.** Hyperbolic half-space with its standard metric is Einstein with
constant `-(n-1)`, by contracting the checked constant-curvature tensor.
Blueprint: `ex:einstein-ricci-flow`. -/
theorem hyperbolicMetric_isEinsteinTensor (e : Fin n) :
    IsEinsteinTensor (hyperbolicMetric e)
      (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) := by
  intro p v w
  rw [← ricciAt_leviCivita_eq_ricciTensorAt
    (hyperbolicMetric e)
    (isLeviCivita_leviCivitaConnection (hyperbolicMetric e)) p v w]
  letI : Bundle.RiemannianBundle
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) :
        (upperHalfSpace e) → Type _) :=
    ⟨(hyperbolicMetric e).toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ
    (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p)
  rw [ricciAt, Riemannian.ricciForm_eq_sum _ v w b]
  have hdiag (i : Fin
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
      (hyperbolicMetric e).metricInner p (b i) (b i) = 1 := by
    exact (orthonormal_iff_ite.mp b.orthonormal i i).trans (by simp)
  have hsum (i : Fin
      (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
      (hyperbolicMetric e).metricInner p (b i) w
        * (hyperbolicMetric e).metricInner p v (b i) =
      inner ℝ (b i) w * inner ℝ v (b i) := by rfl
  simp_rw [curvatureFormAt_eq_affineCurvatureFormAt]
  simp_rw [hyperbolic_curvatureFormAt_eq]
  simp_rw [hdiag]
  have hparseval :
      (∑ i, inner ℝ v (b i) * inner ℝ (b i) w) = inner ℝ v w :=
    OrthonormalBasis.sum_inner_mul_inner b v w
  have hparseval' :
      (∑ i, (hyperbolicMetric e).metricInner p v (b i)
        * (hyperbolicMetric e).metricInner p (b i) w) =
      (hyperbolicMetric e).metricInner p v w := by
    change (∑ i, inner ℝ v (b i) * inner ℝ (b i) w) = inner ℝ v w
    exact hparseval
  have hparseval'' :
      (∑ i, (hyperbolicMetric e).metricInner p (b i) w
        * (hyperbolicMetric e).metricInner p v (b i)) =
      (hyperbolicMetric e).metricInner p v w := by
    calc
      _ = ∑ i, (hyperbolicMetric e).metricInner p v (b i)
          * (hyperbolicMetric e).metricInner p (b i) w := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := hparseval'
  have hfr : Module.finrank ℝ
      (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) p) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := rfl
  simp_rw [neg_sub]
  rw [Finset.sum_sub_distrib, hparseval'']
  simp only [mul_one, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hfr]
  ring

/-- **Math.** The standard hyperbolic metric gives the exact expanding Einstein
Ricci-flow equation on any time set where `1+2(n-1)t` stays positive. -/
theorem hyperbolicMetric_isRicciFlowEquationOn (e : Fin n) (J : Set ℝ)
    (hpos : ∀ t ∈ J, 0 < einsteinScale
      (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) t) :
    IsRicciFlowEquationOn
      (einsteinMetricFamilyOn (hyperbolicMetric e) J
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1)) hpos) J := by
  exact isRicciFlowEquationOn_einsteinMetricFamilyOn _ _ _ hpos
    (hyperbolicMetric_isEinsteinTensor e)

/-- **Math.** The standard hyperbolic metric gives the canonical expanding
Ricci flow on the full nonnegative time half-line. -/
theorem hyperbolicMetric_isRicciFlowEquationOn_nonneg (e : Fin n) :
    IsRicciFlowEquationOn
      (einsteinMetricFamilyOn (hyperbolicMetric e) (Ici 0)
        (-((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1))
        (by
          intro t ht
          unfold einsteinScale
          have hdim : 1 ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
            simpa using (Nat.one_le_iff_ne_zero.mpr (NeZero.ne n))
          have hfactor : 0 ≤
              (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1 := by
            have hdim' : (1 : ℝ) ≤ Module.finrank ℝ
                (EuclideanSpace ℝ (Fin n)) := by exact_mod_cast hdim
            linarith
          have hprod : 0 ≤
              2 * ((Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) - 1) * t :=
            mul_nonneg (mul_nonneg (by norm_num) hfactor) ht
          nlinarith)) (Ici 0) := by
  exact hyperbolicMetric_isRicciFlowEquationOn e (Ici 0) _

end MorganTianLib

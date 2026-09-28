import MorganTianLib.Ch03.RicciFlow.ShiEstimates
import MorganTianLib.Ch03.RicciFlow.ShiAllOrderBridge
import MorganTianLib.Ch03.RicciFlow.ShiNormBounds

/-!
# Morgan--Tian Ch. 3 -- extracting the initial-derivative scale

The Bernstein quantity `shiFm` is the object bounded at the maximum point in
the initial-derivative induction.  This file records the final algebraic
extraction separately from the geometric evolution argument: once a bound for
`shiFm` is available, the exact natural-number exponent
`m + 1 - l = max (m + 1 - l) 0` gives the asserted time scale.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Set

noncomputable section

namespace MorganTianLib

/-- **Math.** A pointwise bound for the Bernstein quantity gives the level
`m + 1` bound with the initial-derivative exponent.  The natural subtraction
in the exponent is the Lean form of `max {m + 1 - l, 0}` in the source.
The hypotheses are only the nonnegativity and normalization used by the
Bernstein extraction; the evolution/max-principle proof of `hbound` is kept
separate.
-/
theorem shiFm_level_le_of_bound
    {X : Type*} {m l : ℕ} {C B : ℝ}
    {w : ℕ → X → ℝ → ℝ}
    (hC : 1 ≤ C)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    {x : X} {t : ℝ} (ht : 0 < t)
    (hbound : shiFm m l C w x t ≤ B) :
    w (m + 1) x t ≤ B / t ^ (m + 1 - l) := by
  have htop : t ^ (m + 1 - l) * w (m + 1) x t ≤
      shiFm m l C w x t :=
    shiFm_top_term_le hC hwnneg ht.le
  have hprod : t ^ (m + 1 - l) * w (m + 1) x t ≤ B :=
    htop.trans hbound
  have hpow : 0 < t ^ (m + 1 - l) := pow_pos ht (m + 1 - l)
  apply (le_div_iff₀ hpow).2
  simpa [mul_comm] using hprod

/-- **Math.** Square-root form of `shiFm_level_le_of_bound`, matching the
pointwise norm estimate used in Shi's theorem. -/
theorem shiFm_sqrt_level_le_of_bound
    {X : Type*} {m l : ℕ} {C B : ℝ}
    {w : ℕ → X → ℝ → ℝ}
    (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    {x : X} {t : ℝ} (ht : 0 < t)
    (hbound : shiFm m l C w x t ≤ B) :
    Real.sqrt (w (m + 1) x t) ≤
      Real.sqrt B / Real.sqrt (t ^ (m + 1 - l)) := by
  have hw := shiFm_level_le_of_bound hC hwnneg ht hbound
  have hsqrt := Real.sqrt_le_sqrt hw
  rw [Real.sqrt_div hB] at hsqrt
  exact hsqrt

/-! ## Source-scale normalizations -/

/-- **Math.** The square root of a nonnegative natural power is the real-power
half-scale used in the analytic statement of Shi's estimates. -/
theorem realSqrt_natPow_eq_rpow_half
    {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    Real.sqrt (t ^ n) = t ^ ((n : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul ht]
  congr 1
  ring

/-- **Math.** A Bernstein bound in square-root form, rewritten with the
source's real-power time scale. -/
theorem shiFm_sqrt_level_le_of_bound_rpow
    {X : Type*} {m l : ℕ} {C B : ℝ}
    {w : ℕ → X → ℝ → ℝ}
    (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    {x : X} {t : ℝ} (ht : 0 < t)
    (hbound : shiFm m l C w x t ≤ B) :
    Real.sqrt (w (m + 1) x t) ≤
      Real.sqrt B / t ^ (((m + 1 - l : ℕ) : ℝ) / 2) := by
  have hbase := shiFm_sqrt_level_le_of_bound
    (m := m) (l := l) (C := C) (B := B) (w := w)
    hC hB hwnneg ht hbound
  have hpow : Real.sqrt (t ^ (m + 1 - l)) =
      t ^ (((m + 1 - l : ℕ) : ℝ) / 2) :=
    realSqrt_natPow_eq_rpow_half ht.le (m + 1 - l)
  rw [hpow] at hbase
  exact hbase

/-- **Math.** The `l = 0` Bernstein extraction has the usual
`t ^ ((m + 1) / 2)` Shi time scale. -/
theorem shiFm_sqrt_level_le_of_bound_rpow_zero
    {X : Type*} {m : ℕ} {C B : ℝ}
    {w : ℕ → X → ℝ → ℝ}
    (hC : 1 ≤ C) (hB : 0 ≤ B)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    {x : X} {t : ℝ} (ht : 0 < t)
    (hbound : shiFm m 0 C w x t ≤ B) :
    Real.sqrt (w (m + 1) x t) ≤
      Real.sqrt B / t ^ (((m + 1 : ℕ) : ℝ) / 2) := by
  simpa using (shiFm_sqrt_level_le_of_bound_rpow
    (m := m) (l := 0) (C := C) (B := B) (w := w)
    hC hB hwnneg ht hbound)

/-- **Math.** The geometric all-order compact-interior bound in the preceding
bridge, expressed directly in the source's real-power time scale. -/
theorem riemannCovDerivNormAt_le_shi_bound_on_compact_interior_rpow
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ}
    (hcert : ∀ k : ℕ,
      RiemannianShiTowerCertificate (I := I) g K lap lapCombination T k) :
    ∀ k : ℕ, ∀ x ∈ K, ∀ t ∈ Icc (hcert k).tau T,
      riemannCovDerivNormAt (g t) k x ≤
        Real.sqrt
            (shiCoefficient (hcert k).c k 0 * (hcert k).m ^ 2 +
              ((hcert k).rho * shiWeightAt (hcert k).c k T +
                shiCoefficient (hcert k).c k 0 *
                  ((hcert k).kappa * (hcert k).m ^ 2)) * T) /
          (hcert k).tau ^ ((k : ℝ) / 2) := by
  intro k x hx t ht
  have hbase := riemannCovDerivNormAt_le_shi_bound_on_compact_interior
    (I := I) hcert k x hx t ht
  have hpow : Real.sqrt ((hcert k).tau ^ k) =
      (hcert k).tau ^ ((k : ℝ) / 2) :=
    realSqrt_natPow_eq_rpow_half (hcert k).htau.le k
  rw [hpow] at hbase
  exact hbase

/-! ## Curvature-operator input for the zeroth tower level -/

/-- **Math.** A uniform curvature-operator bound supplies the zeroth Shi
energy hypothesis at any larger threshold `m`.  This is the adapter needed to
instantiate the `hw0` field of a geometric Shi tower certificate: the
positive-order evolution and cutoff hypotheses remain separate. -/
theorem riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeOnTime_of_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [I.Boundaryless]
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {K m : ℝ}
    (hK : 0 ≤ K)
    (hm : (Module.finrank ℝ E : ℝ) ^ 2 * K ≤ m)
    (hRm : HasCurvatureOperatorNormLeOnTime g J K) :
    ∀ t ∈ J, ∀ p : M,
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(g t).toRiemannianMetric⟩
      riemannCovDerivNormSqAt (g t) 0 p ≤ m ^ 2 := by
  intro t ht p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(g t).toRiemannianMetric⟩
  have hbase :=
    riemannCovDerivNormSqAt_zero_le_of_hasCurvatureOperatorNormLeAt
      (g t) hK p (hRm t ht p)
  have hscale : 0 ≤ (Module.finrank ℝ E : ℝ) ^ 2 * K :=
    mul_nonneg (sq_nonneg _) hK
  have hm_nonneg : 0 ≤ m := hscale.trans hm
  have hsq :
      ((Module.finrank ℝ E : ℝ) ^ 2 * K) ^ 2 ≤ m ^ 2 :=
    (sq_le_sq₀ hscale hm_nonneg).2 hm
  exact hbase.trans hsq

end MorganTianLib

end

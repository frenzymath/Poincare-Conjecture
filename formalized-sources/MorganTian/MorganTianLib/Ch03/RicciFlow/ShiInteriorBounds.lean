import MorganTianLib.Ch03.RicciFlow.ShiMetricBridge

/-!
# Morgan--Tian Ch. 3 - compact interior Shi bounds

The finite tower estimate is singular only at the initial time.  This module
packages the standard compact-interior consequence: after fixing a positive
time margin, the order-​`k` curvature level is uniformly bounded on the whole
compact spatial set.  All geometric inputs remain explicit in the tower and
cutoff interfaces imported from the preceding modules.
-/

open Set

noncomputable section

namespace MorganTianLib

/-- **Math.** A square-root Shi bound with the time denominator frozen at a
positive interior time `tau`.  This is the form used when passing to smooth
pointed limits on compact subsets away from the initial slice.  The adjustable
weight slack is recorded by the hypothesis `T * kappa ≤ 1 + c`. -/
theorem shiTower_sqrt_le_div_on_compact_interior_of_mul_le
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {w lap : ℕ → X → ℝ → ℝ} {lapCombination : X → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hm : 0 < m) (hkT : T * kappa ≤ 1 + c) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T → w 0 x t ≤ m ^ 2)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2)
      (K ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      (∀ y ∈ K, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) → lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ∀ j < k + 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      derivWithin (fun s => w j x s) (Icc 0 T) t ≤
        lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho)
    {tau : ℝ} (htau : 0 < tau) (_htauT : tau ≤ T) :
    ∀ x ∈ K, ∀ t ∈ Icc tau T,
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (tau ^ k) := by
  intro x hx t ht
  have htbase : t ∈ Icc (0 : ℝ) T := by
    exact ⟨le_trans htau.le ht.1, ht.2⟩
  have hbound := shiTower_sqrt_le_div_on_compact_of_mul_le
    (K := K) hK hKne hT hc hrho hm hkT hkappa hwnneg hw0 hderiv
      hcombCont hspatialMax hlap htower x hx t
      (lt_of_lt_of_le htau ht.1) htbase.2
  have hpow : tau ^ k ≤ t ^ k :=
    pow_le_pow_left₀ htau.le ht.1 k
  have hsqrtpow : Real.sqrt (tau ^ k) ≤ Real.sqrt (t ^ k) :=
    Real.sqrt_le_sqrt hpow
  have hsqrtpow_pos : 0 < Real.sqrt (tau ^ k) :=
    Real.sqrt_pos.2 (pow_pos htau k)
  have hdenom :
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (tau ^ k) := by
    apply le_trans hbound
    apply div_le_div₀ (Real.sqrt_nonneg _) le_rfl hsqrtpow_pos hsqrtpow
  exact hdenom

/-- **Math.** Backwards-compatible small-time specialization of
`shiTower_sqrt_le_div_on_compact_interior_of_mul_le`. -/
theorem shiTower_sqrt_le_div_on_compact_interior
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {w lap : ℕ → X → ℝ → ℝ} {lapCombination : X → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hm : 0 < m) (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T → w 0 x t ≤ m ^ 2)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2)
      (K ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      (∀ y ∈ K, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) → lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ∀ j < k + 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      derivWithin (fun s => w j x s) (Icc 0 T) t ≤
        lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho)
    {tau : ℝ} (htau : 0 < tau) (htauT : tau ≤ T) :
    ∀ x ∈ K, ∀ t ∈ Icc tau T,
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (tau ^ k) := by
  apply shiTower_sqrt_le_div_on_compact_interior_of_mul_le hK hKne hT hc hrho hm
    (by linarith) hkappa hwnneg hw0 hderiv hcombCont hspatialMax hlap htower
    htau htauT

/-- **Math.** Uniform compact-interior packaging of the all-order Shi bound.
For each order and each positive time margin, one explicit finite constant
controls the square root of the corresponding tower level.  The generalized
form accepts the adjustable slack `T * kappa ≤ 1 + c`. -/
theorem exists_uniform_shiTower_sqrt_bound_on_compact_interior_of_mul_le
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {w lap : ℕ → X → ℝ → ℝ} {lapCombination : X → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hm : 0 < m) (hkT : T * kappa ≤ 1 + c) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T → w 0 x t ≤ m ^ 2)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2)
      (K ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      (∀ y ∈ K, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) → lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ∀ j < k + 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      derivWithin (fun s => w j x s) (Icc 0 T) t ≤
        lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho)
    {tau : ℝ} (htau : 0 < tau) (_htauT : tau ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ t ∈ Icc tau T,
      Real.sqrt (w k x t) ≤ C := by
  let C : ℝ :=
    Real.sqrt
        (shiCoefficient c k 0 * m ^ 2 +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
      Real.sqrt (tau ^ k)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro x hx t ht
  exact shiTower_sqrt_le_div_on_compact_interior_of_mul_le
    hK hKne hT hc hrho hm hkT hkappa hwnneg hw0 hderiv hcombCont
      hspatialMax hlap htower htau _htauT x hx t ht

/-- **Math.** Backwards-compatible small-time specialization of
`exists_uniform_shiTower_sqrt_bound_on_compact_interior_of_mul_le`. -/
theorem exists_uniform_shiTower_sqrt_bound_on_compact_interior
    {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) (hKne : K.Nonempty)
    {w lap : ℕ → X → ℝ → ℝ} {lapCombination : X → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hm : 0 < m) (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T → w 0 x t ≤ m ^ 2)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2)
      (K ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      (∀ y ∈ K, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) → lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ∀ j < k + 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
      derivWithin (fun s => w j x s) (Icc 0 T) t ≤
        lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho)
    {tau : ℝ} (htau : 0 < tau) (htauT : tau ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ t ∈ Icc tau T,
      Real.sqrt (w k x t) ≤ C := by
  apply exists_uniform_shiTower_sqrt_bound_on_compact_interior_of_mul_le
    hK hKne hT hc hrho hm (by linarith) hkappa hwnneg hw0 hderiv hcombCont
    hspatialMax hlap htower htau htauT

end MorganTianLib

import MorganTianLib.Ch03.RicciFlow.ShiCutoff
import MorganTianLib.Ch03.RicciFlow.ShiMaximumPrinciple
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Morgan--Tian Ch. 3 - the all-order Shi tower

The geometric commutation calculation is deliberately represented by the
explicit `ShiTowerInequalitiesOn` hypothesis.  The results below perform the
finite tower cancellation and the compact parabolic comparison, which are the
analytic producers used after that geometric input and before a local cutoff
argument.
-/

open Set

noncomputable section

namespace MorganTianLib

/-- **Math.** The pointwise evolution inequalities consumed by the finite Shi
tower.  For a geometric instantiation, `w j` is the squared norm of
`∇^j Rm`, and `lap j` is its spatial Laplacian. -/
def ShiTowerInequalitiesOn {X : Type*}
    (w lap : ℕ → X → ℝ → ℝ) (kappa rho : ℝ) (k : ℕ) (J : Set ℝ) : Prop :=
  ∀ j < k + 1, ∀ t ∈ J, ∀ x : X,
    derivWithin (fun s => w j x s) J t ≤
      lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho

/-- **Math.** The weighted Bernstein quantity used in the induction step of
Shi's argument.  The levels of `w` are intended to be squared curvature
derivative norms, but the definition itself is analytic and independent of a
particular tensor implementation. -/
def shiFm {X : Type*} (m l : ℕ) (C : ℝ)
    (w : ℕ → X → ℝ → ℝ) (x : X) (t : ℝ) : ℝ :=
  (C + t ^ (m - l) * w m x t) *
    t ^ (m + 1 - l) * w (m + 1) x t

/-- **Math.** Nonnegativity of the Bernstein quantity under nonnegative level
data and a nonnegative constant. -/
theorem shiFm_nonneg {X : Type*} {m l : ℕ} {C : ℝ}
    {w : ℕ → X → ℝ → ℝ} (hC : 0 ≤ C) (hwnneg : ∀ j x t, 0 ≤ w j x t)
    {x : X} {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ shiFm m l C w x t := by
  have hfactor : 0 ≤ C + t ^ (m - l) * w m x t :=
    add_nonneg hC (mul_nonneg (pow_nonneg ht _) (hwnneg m x t))
  exact mul_nonneg (mul_nonneg hfactor (pow_nonneg ht _))
    (hwnneg (m + 1) x t)

/-- **Math.** If the additive constant in `F_m` is at least one, its value
dominates the top weighted level.  This is the algebraic extraction used after
the maximum estimate. -/
theorem shiFm_top_term_le {X : Type*} {m l : ℕ} {C : ℝ}
    {w : ℕ → X → ℝ → ℝ} (hC : 1 ≤ C)
    (hwnneg : ∀ j x t, 0 ≤ w j x t) {x : X} {t : ℝ} (ht : 0 ≤ t) :
    t ^ (m + 1 - l) * w (m + 1) x t ≤ shiFm m l C w x t := by
  have hbase : 1 ≤ C + t ^ (m - l) * w m x t := by
    have hprod : 0 ≤ t ^ (m - l) * w m x t :=
      mul_nonneg (pow_nonneg ht _) (hwnneg m x t)
    linarith
  have htop : 0 ≤ t ^ (m + 1 - l) * w (m + 1) x t :=
    mul_nonneg (pow_nonneg ht _) (hwnneg (m + 1) x t)
  have hmul := mul_le_mul_of_nonneg_right hbase htop
  simpa [shiFm, mul_assoc] using hmul

/-- **Math.** The weighted combination has the derivative obtained by applying
the product rule to each level of the finite tower. -/
theorem shiTowerCombination_hasDerivWithinAt
    {X : Type*} {w : ℕ → X → ℝ → ℝ} {c : ℝ} {k : ℕ} {T : ℝ}
    {x : X} {s : ℝ} (_ht : s ∈ Icc (0 : ℝ) T)
    (hderiv : ∀ j, HasDerivWithinAt (fun r => w j x r)
      (derivWithin (fun r => w j x r) (Icc 0 T) s) (Icc 0 T) s) :
    HasDerivWithinAt
      (fun r => shiTowerCombination c k w x r)
      (∑ j ∈ Finset.range (k + 1),
        ((j : ℝ) * shiCoefficient c k j * s ^ (j - 1) * w j x s
          + shiCoefficient c k j * s ^ j *
            derivWithin (fun r => w j x r) (Icc 0 T) s))
      (Icc 0 T) s := by
  classical
  have hlev : ∀ j ∈ Finset.range (k + 1),
      HasDerivWithinAt
        (fun r : ℝ => shiCoefficient c k j * r ^ j * w j x r)
        ((j : ℝ) * shiCoefficient c k j * s ^ (j - 1) * w j x s
          + shiCoefficient c k j * s ^ j *
            derivWithin (fun r => w j x r) (Icc 0 T) s)
        (Icc 0 T) s := by
    intro j _hj
    have hpow : HasDerivWithinAt (fun r : ℝ => shiCoefficient c k j * r ^ j)
        (shiCoefficient c k j * ((j : ℝ) * s ^ (j - 1))) (Icc 0 T) s :=
      ((hasDerivAt_pow j s).const_mul (shiCoefficient c k j)).hasDerivWithinAt
    have hprod := hpow.mul (hderiv j)
    have hshape : (fun r => shiCoefficient c k j * r ^ j) *
        (fun r => w j x r) =
        (fun r => shiCoefficient c k j * r ^ j * w j x r) := by
      rfl
    rw [hshape] at hprod
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
  have hsum := HasDerivWithinAt.fun_sum hlev
  simpa [shiTowerCombination] using hsum

/-- **Math.** The tower cancellation reassembles into a parabolic inequality
for the weighted combination.  `hlap` is the explicit linearity bridge for the
chosen spatial Laplacian; supplying it from the Riemannian Laplacian is a
separate geometric interface. -/
theorem shiTowerCombination_deriv_le_of_mul_le
    {X : Type*} {w lap : ℕ → X → ℝ → ℝ}
    {lapCombination : X → ℝ → ℝ}
    {c kappa rho T : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hkT : T * kappa ≤ 1 + c) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ShiTowerInequalitiesOn w lap kappa rho k (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      derivWithin (fun s => shiTowerCombination c k w x s) (Icc 0 T) t ≤
        lapCombination x t +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * w 0 x t)) := by
  classical
  intro t ht x
  have hder := shiTowerCombination_hasDerivWithinAt (w := w) (c := c)
    (k := k) (x := x) ht (fun j => hderiv j x t ht)
  rw [hder.derivWithin (uniqueDiffOn_Icc hT t ht), Finset.sum_add_distrib]
  rw [hlap t ht x]
  have hsub : ∀ j ∈ Finset.range (k + 1),
      ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * w j x t
          + shiCoefficient c k j * t ^ j *
            derivWithin (fun s => w j x s) (Icc 0 T) t)
        ≤ shiCoefficient c k j * t ^ j * lap j x t
          + ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * w j x t
            + shiCoefficient c k j * t ^ j *
              (-2 * w (j + 1) x t + kappa * w j x t + rho)) := by
    intro j hj
    have hjk : j < k + 1 := Finset.mem_range.mp hj
    have htow := htower j hjk t ht x
    have hweight : 0 ≤ shiCoefficient c k j * t ^ j := by
      have hcj := (shiCoefficient_pos hc k j).le
      have htpow : (0 : ℝ) ≤ t ^ j := pow_nonneg ht.1 j
      positivity
    calc
      ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * w j x t
          + shiCoefficient c k j * t ^ j *
            derivWithin (fun s => w j x s) (Icc 0 T) t)
          ≤ ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * w j x t
            + shiCoefficient c k j * t ^ j *
              (lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho)) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left htow hweight) _
      _ = shiCoefficient c k j * t ^ j * lap j x t
          + ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * w j x t
            + shiCoefficient c k j * t ^ j *
              (-2 * w (j + 1) x t + kappa * w j x t + rho)) := by ring
  have hsum := Finset.sum_le_sum hsub
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have htk : t * kappa ≤ 1 + c := by
    exact le_trans (mul_le_mul_of_nonneg_right ht.2 hkappa) hkT
  have hreact := shiReactionSum_le_of_mul_le (c := c) (rho := rho) hc k
    (t := t) (kappa := kappa) (T := T) ht.1 ht.2 htk
    (v := fun j => w j x t) (fun j => hwnneg j x t) hrho
  linarith

/-- **Math.** Small-time specialization of
`shiTowerCombination_deriv_le_of_mul_le`, retaining the original interface
when the tower weight has not been enlarged to absorb `T * kappa`. -/
theorem shiTowerCombination_deriv_le
    {X : Type*} {w lap : ℕ → X → ℝ → ℝ}
    {lapCombination : X → ℝ → ℝ}
    {c kappa rho T : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ShiTowerInequalitiesOn w lap kappa rho k (Icc 0 T)) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      derivWithin (fun s => shiTowerCombination c k w x s) (Icc 0 T) t ≤
        lapCombination x t +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * w 0 x t)) := by
  apply shiTowerCombination_deriv_le_of_mul_le hT hc hrho (by linarith)
    hkappa hwnneg hderiv hlap htower

/-- **Math.** A compact all-order Shi barrier.  If the explicit tower
inequalities hold and the spatial Laplacian of the combination is nonpositive
at a spatial maximum, then every level is bounded by the affine barrier. -/
theorem shiTower_mul_pow_le_affine_of_mul_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w lap : ℕ → X → ℝ → ℝ} {lapCombination : X → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hkT : T * kappa ≤ 1 + c) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T → w 0 x t ≤ m ^ 2)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (∀ y, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) →
      lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ShiTowerInequalitiesOn w lap kappa rho k (Icc 0 T)) :
    ∀ x t, t ∈ Icc (0 : ℝ) T →
      t ^ k * w k x t ≤
        shiCoefficient c k 0 * m ^ 2 +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * m ^ 2)) * t := by
  have hcombDeriv : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt
        (fun s => shiTowerCombination c k w x s)
        (derivWithin (fun s => shiTowerCombination c k w x s)
          (Icc 0 T) t) (Icc 0 T) t := by
    intro x t ht
    have h := shiTowerCombination_hasDerivWithinAt (w := w) (c := c)
      (k := k) (T := T) (x := x) (s := t) ht
      (fun j => hderiv j x t ht)
    exact h.congr_deriv (h.derivWithin (uniqueDiffOn_Icc hT t ht)).symm
  have hcombIneq : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      derivWithin (fun s => shiTowerCombination c k w x s) (Icc 0 T) t ≤
        lapCombination x t +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * w 0 x t)) :=
    shiTowerCombination_deriv_le_of_mul_le hT hc hrho hkT hkappa hwnneg
      hderiv hlap htower
  have hmax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, 0 < t →
      (∀ y, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) →
      derivWithin (fun s => shiTowerCombination c k w x s)
        (Icc 0 T) t ≤
        rho * shiWeightAt c k T + shiCoefficient c k 0 * (kappa * m ^ 2) := by
    intro t ht x htpos hmx
    have hL := hspatialMax t ht x hmx
    have h0 := hw0 x t ht
    have hcoef := (shiCoefficient_pos hc k 0).le
    have hreact := hcombIneq t ht x
    have hκ : shiCoefficient c k 0 * (kappa * w 0 x t) ≤
        shiCoefficient c k 0 * (kappa * m ^ 2) := by
      have := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h0 hkappa) hcoef
      linarith
    linarith
  have hzero : ∀ x, shiTowerCombination c k w x 0 ≤
      shiCoefficient c k 0 * m ^ 2 := by
    intro x
    rw [shiTowerCombination_zero]
    have h0 := hw0 x 0 ⟨le_rfl, hT.le⟩
    exact mul_le_mul_of_nonneg_left h0 (shiCoefficient_pos hc k 0).le
  have hbar := shi_le_affineBarrier_of_parabolic_inequality
    (u := fun x t => shiTowerCombination c k w x t)
    (ut := fun x t => derivWithin (fun s => shiTowerCombination c k w x s)
      (Icc 0 T) t)
    (T := T) (a := shiCoefficient c k 0 * m ^ 2)
    (c := rho * shiWeightAt c k T + shiCoefficient c k 0 * (kappa * m ^ 2))
    hT hcombCont hcombDeriv hmax hzero
  intro x t ht
  exact le_trans (shiTopTerm_le_tower hc k ht.1 (fun j => hwnneg j x t))
    (hbar x t ht)

/-- **Math.** Original small-time form of the affine Shi tower barrier. -/
theorem shiTower_mul_pow_le_affine
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    {w lap : ℕ → X → ℝ → ℝ} {lapCombination : X → ℝ → ℝ}
    {c kappa rho T m : ℝ} {k : ℕ}
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hkT : T * kappa ≤ 1) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j x t, 0 ≤ w j x t)
    (hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T → w 0 x t ≤ m ^ 2)
    (hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => w j x s)
        (derivWithin (fun s => w j x s) (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : X × ℝ => shiTowerCombination c k w z.1 z.2)
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (∀ y, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) →
      lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ShiTowerInequalitiesOn w lap kappa rho k (Icc 0 T)) :
    ∀ x t, t ∈ Icc (0 : ℝ) T →
      t ^ k * w k x t ≤
        shiCoefficient c k 0 * m ^ 2 +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * m ^ 2)) * t := by
  apply shiTower_mul_pow_le_affine_of_mul_le hT hc hrho (by linarith)
    hkappa hwnneg hw0 hderiv hcombCont hspatialMax hlap htower

/-- **Math.** The finite tower gives the usual square-root derivative scale.

The numerator is evaluated at the terminal time, so the statement is uniform
on the whole interval once the tower constants are fixed. -/
theorem shiTower_sqrt_le_div_of_mul_le
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
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
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (∀ y, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) →
      lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ShiTowerInequalitiesOn w lap kappa rho k (Icc 0 T)) :
    ∀ x t, 0 < t → t ≤ T →
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (t ^ k) := by
  intro x t htpos htT
  have hmain := shiTower_mul_pow_le_affine_of_mul_le
    (w := w) (lap := lap) (lapCombination := lapCombination)
    hT hc hrho hkT hkappa hwnneg hw0 hderiv hcombCont hspatialMax hlap htower
    x t ⟨htpos.le, htT⟩
  have hweight : 0 ≤ shiWeightAt c k T :=
    (shiWeightAt_pos hc k hT).le
  have hcoef : 0 ≤ shiCoefficient c k 0 :=
    (shiCoefficient_pos hc k 0).le
  have hbarSlope : 0 ≤ rho * shiWeightAt c k T +
      shiCoefficient c k 0 * (kappa * m ^ 2) := by
    positivity
  have hbarMono :
      shiCoefficient c k 0 * m ^ 2 +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * m ^ 2)) * t ≤
        shiCoefficient c k 0 * m ^ 2 +
          (rho * shiWeightAt c k T +
            shiCoefficient c k 0 * (kappa * m ^ 2)) * T := by
    have hmul := mul_le_mul_of_nonneg_left htT hbarSlope
    linarith
  have hprod : t ^ k * w k x t ≤
      shiCoefficient c k 0 * m ^ 2 +
        (rho * shiWeightAt c k T +
          shiCoefficient c k 0 * (kappa * m ^ 2)) * T :=
    le_trans hmain hbarMono
  have hpowpos : 0 < t ^ k := pow_pos htpos k
  have hwbound : w k x t ≤
      (shiCoefficient c k 0 * m ^ 2 +
        (rho * shiWeightAt c k T +
          shiCoefficient c k 0 * (kappa * m ^ 2)) * T) / (t ^ k) := by
    apply (le_div_iff₀ hpowpos).2
    simpa [mul_comm] using hprod
  have hnumerator : 0 ≤
      shiCoefficient c k 0 * m ^ 2 +
        (rho * shiWeightAt c k T +
          shiCoefficient c k 0 * (kappa * m ^ 2)) * T := by
    have hleft : 0 ≤ t ^ k * w k x t :=
      mul_nonneg hpowpos.le (hwnneg k x t)
    exact le_trans hleft hprod
  have hsqrt := Real.sqrt_le_sqrt hwbound
  rw [Real.sqrt_div hnumerator] at hsqrt
  exact hsqrt

/-- **Math.** Original small-time square-root estimate for the Shi tower. -/
theorem shiTower_sqrt_le_div
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
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
      ((Set.univ : Set X) ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (∀ y, shiTowerCombination c k w y t ≤
        shiTowerCombination c k w x t) →
      lapCombination x t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombination x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lap j x t)
    (htower : ShiTowerInequalitiesOn w lap kappa rho k (Icc 0 T)) :
    ∀ x t, 0 < t → t ≤ T →
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (t ^ k) := by
  apply shiTower_sqrt_le_div_of_mul_le hT hc hrho hm (by linarith)
    hkappa hwnneg hw0 hderiv hcombCont hspatialMax hlap htower

/-! ## Compact-interior packaging -/

/-- **Math.** The all-order tower estimate on a compact interior set.  The ambient space
need not be compact: every continuity, maximum, and evolution hypothesis is
restricted explicitly to `K`, then transported to the subtype carrying its
compact-space instance. -/
theorem shiTower_sqrt_le_div_on_compact_of_mul_le
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
        lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (t ^ k) := by
  let Y := K
  let wY : ℕ → Y → ℝ → ℝ := fun j x t => w j (x : X) t
  let lapY : ℕ → Y → ℝ → ℝ := fun j x t => lap j (x : X) t
  let lapCombinationY : Y → ℝ → ℝ := fun x t => lapCombination (x : X) t
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hK
  letI : Nonempty Y := Set.nonempty_coe_sort.mpr hKne
  have hcombContY : ContinuousOn
      (fun z : Y × ℝ => shiTowerCombination c k wY z.1 z.2)
      ((Set.univ : Set Y) ×ˢ Icc 0 T) := by
    have hmap : ContinuousOn (fun z : Y × ℝ => ((z.1 : X), z.2))
        ((Set.univ : Set Y) ×ˢ Icc 0 T) := by
      have hval : Continuous (fun z : Y × ℝ => (z.1 : X)) :=
        continuous_subtype_val.comp continuous_fst
      exact hval.continuousOn.prodMk continuous_snd.continuousOn
    apply hcombCont.comp' hmap
    intro z hz
    exact ⟨z.1.property, hz.2⟩
  have hwnnegY : ∀ j x t, 0 ≤ wY j x t := by
    intro j x t
    exact hwnneg j (x : X) t
  have hw0Y : ∀ x t, t ∈ Icc (0 : ℝ) T → wY 0 x t ≤ m ^ 2 := by
    intro x t ht
    exact hw0 (x : X) t ht
  have hderivY : ∀ j x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (fun s => wY j x s)
        (derivWithin (fun s => wY j x s) (Icc 0 T) t) (Icc 0 T) t := by
    intro j x t ht
    exact hderiv j (x : X) t ht
  have hspatialMaxY : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      (∀ y, shiTowerCombination c k wY y t ≤
        shiTowerCombination c k wY x t) → lapCombinationY x t ≤ 0 := by
    intro t ht x hmx
    apply hspatialMax t ht (x : X) x.property
    intro y hy
    exact hmx ⟨y, hy⟩
  have hlapY : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
      lapCombinationY x t =
        ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * lapY j x t := by
    intro t ht x
    exact hlap t ht (x : X) x.property
  have htowerY : ShiTowerInequalitiesOn wY lapY kappa rho k (Icc 0 T) := by
    intro j hj t ht x
    exact htower j hj t ht (x : X) x.property
  have hbound := shiTower_sqrt_le_div_of_mul_le
    (X := Y) (w := wY) (lap := lapY) (lapCombination := lapCombinationY)
    hT hc hrho hm hkT hkappa hwnnegY hw0Y hderivY hcombContY
      hspatialMaxY hlapY htowerY
  intro x hx t htpos htT
  exact hbound ⟨x, hx⟩ t htpos htT

/-- **Math.** Original small-time compact-set packaging of the Shi tower. -/
theorem shiTower_sqrt_le_div_on_compact
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
        lap j x t - 2 * w (j + 1) x t + kappa * w j x t + rho) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      Real.sqrt (w k x t) ≤
        Real.sqrt
            (shiCoefficient c k 0 * m ^ 2 +
              (rho * shiWeightAt c k T +
                shiCoefficient c k 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt (t ^ k) := by
  apply shiTower_sqrt_le_div_on_compact_of_mul_le hK hKne hT hc hrho hm
    (by linarith) hkappa hwnneg hw0 hderiv hcombCont hspatialMax hlap htower

end MorganTianLib

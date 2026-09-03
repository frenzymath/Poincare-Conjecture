import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Morgan--Tian Ch. 3 - the Shi tower and cutoff arithmetic

This file isolates the finite arithmetic used in the Bernstein--Bando--Shi
argument.  The coefficients, their telescoping cancellation, and the
weighted maximum-point estimate are proved here without introducing a
geometric evolution theorem as an assumption of a public result.

`ShiParabolicCutoff` records the support, Laplacian, and gradient-ratio bounds
of the cutoff used in the local proof.  Constructing such a cutoff from an
exponential chart and a Ricci-flow curvature bound is a separate geometric
contract and is deliberately not identified with the certificate here.
-/

open Set
open scoped ContDiff

noncomputable section

namespace MorganTianLib

/-! ## Finite tower coefficients -/

/-- The downward recursion used for the level weights in the Shi estimate. -/
def shiCoefficientAux (c : ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 1
  | d + 1 => (1 + c + ((k - d : ℕ) : ℝ)) * shiCoefficientAux c k d / 2

/-- The coefficient multiplying `t^j w_j` in the order-`k` tower. -/
def shiCoefficient (c : ℝ) (k j : ℕ) : ℝ :=
  shiCoefficientAux c k (k - j)

theorem shiCoefficient_top (c : ℝ) (k : ℕ) :
    shiCoefficient c k k = 1 := by
  simp [shiCoefficient, shiCoefficientAux]

theorem shiCoefficient_of_le (c : ℝ) {k j : ℕ} (h : k ≤ j) :
    shiCoefficient c k j = 1 := by
  rw [shiCoefficient, Nat.sub_eq_zero_of_le h]
  rfl

theorem shiCoefficient_succ (c : ℝ) {k j : ℕ} (h : j < k) :
    shiCoefficient c k j =
      (1 + c + ((j + 1 : ℕ) : ℝ)) * shiCoefficient c k (j + 1) / 2 := by
  have hgap : k - j = (k - (j + 1)) + 1 := by omega
  have hsub : k - (k - (j + 1)) = j + 1 := by omega
  rw [shiCoefficient, hgap, shiCoefficientAux, hsub, shiCoefficient]

theorem shiCoefficient_pos {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    ∀ j, 0 < shiCoefficient c k j := by
  intro j
  induction hd : k - j generalizing j with
  | zero =>
      rw [shiCoefficient_of_le c (by omega)]
      exact one_pos
  | succ d ih =>
      have hjk : j < k := by omega
      rw [shiCoefficient_succ c hjk]
      have hnext := ih (j + 1) (by omega)
      positivity

/-- The differentiated weight and the reaction slack are paid for by the
favourable term at the preceding level. -/
theorem shiCoefficient_telescope {c : ℝ} (hc : 0 ≤ c)
    {k j : ℕ} (h : j < k) :
    ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1)
        + (1 + c) * shiCoefficient c k (j + 1)
      ≤ 2 * shiCoefficient c k j := by
  rw [shiCoefficient_succ c h]
  have hpos := shiCoefficient_pos hc k (j + 1)
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by
    push_cast
    rfl
  rw [hcast]
  ring_nf
  nlinarith [hpos]

/-! ## The combination and its initial/top-level bookkeeping -/

/-- The finite weighted tower `sum a_j t^j w_j`. -/
def shiTowerCombination {X : Type*} (c : ℝ) (k : ℕ)
    (w : ℕ → X → ℝ → ℝ) (x : X) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    shiCoefficient c k j * t ^ j * w j x t

theorem shiTowerCombination_zero {X : Type*} (c : ℝ) (k : ℕ)
    (w : ℕ → X → ℝ → ℝ) (x : X) :
    shiTowerCombination c k w x 0 = shiCoefficient c k 0 * w 0 x 0 := by
  rw [shiTowerCombination,
    Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr (by omega))]
  · simp
  · intro j hj hj0
    rw [zero_pow hj0]
    ring

theorem shiTopTerm_le_tower {X : Type*} {c : ℝ} (hc : 0 ≤ c)
    (k : ℕ) {w : ℕ → X → ℝ → ℝ} {x : X} {t : ℝ}
    (ht : 0 ≤ t) (hw : ∀ j, 0 ≤ w j x t) :
    t ^ k * w k x t ≤ shiTowerCombination c k w x t := by
  classical
  rw [shiTowerCombination]
  have hmem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hle := Finset.single_le_sum
    (f := fun j => shiCoefficient c k j * t ^ j * w j x t)
    (fun j _ => by
      have hcj := (shiCoefficient_pos hc k j).le
      have hwt := hw j
      have hpow : 0 ≤ t ^ j := pow_nonneg ht j
      positivity)
    hmem
  rwa [shiCoefficient_top, one_mul] at hle

/-! ## Arithmetic cancellation -/

theorem shiLevelCancel {c : ℝ} (hc : 0 ≤ c) {k j : ℕ} (h : j < k)
    {v d : ℝ} (hv : 0 ≤ v) (hd : d ≤ 1 + c) :
    ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1) * v
        + d * shiCoefficient c k (j + 1) * v
      ≤ 2 * shiCoefficient c k j * v := by
  have hpos := shiCoefficient_pos hc k (j + 1)
  have htel := shiCoefficient_telescope hc h
  have hreact : d * shiCoefficient c k (j + 1) ≤
      (1 + c) * shiCoefficient c k (j + 1) :=
    mul_le_mul_of_nonneg_right hd hpos.le
  nlinarith [hv, htel, hreact]

/-- The total weight used to bound the additive reaction in a finite tower. -/
def shiWeightAt (c : ℝ) (k : ℕ) (T : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), shiCoefficient c k j * T ^ j

theorem shiWeightAt_pos {c : ℝ} (hc : 0 ≤ c) (k : ℕ)
    {T : ℝ} (hT : 0 < T) : 0 < shiWeightAt c k T := by
  rw [shiWeightAt]
  refine Finset.sum_pos (fun j _ => ?_)
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hcj := shiCoefficient_pos hc k j
  positivity

/-- Finite-sum cancellation for the reaction terms of the Shi tower.

The condition `t * kappa ≤ 1 + c` is an adjustable reaction-absorption
slack.  No geometric assertion is hidden in this arithmetic statement; the
legacy small-time specialization below recovers the `t * kappa ≤ 1` form. -/
theorem shiReactionSum_le_of_mul_le {c rho : ℝ} (hc : 0 ≤ c) (k : ℕ)
    {t kappa T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hk1 : t * kappa ≤ 1 + c) {v : ℕ → ℝ}
    (hv : ∀ j, 0 ≤ v j) (hrho : 0 ≤ rho) :
    ∑ j ∈ Finset.range (k + 1),
        (((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j)
          + shiCoefficient c k j * t ^ j
              * (-2 * v (j + 1) + kappa * v j + rho))
      ≤ rho * shiWeightAt c k T
          + shiCoefficient c k 0 * (kappa * v 0) := by
  classical
  have hsplit : ∀ j ∈ Finset.range (k + 1),
      (j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j
        + shiCoefficient c k j * t ^ j
            * (-2 * v (j + 1) + kappa * v j + rho)
      = ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j
          + shiCoefficient c k j * t ^ j * (kappa * v j)
          - 2 * (shiCoefficient c k j * t ^ j * v (j + 1)))
        + shiCoefficient c k j * t ^ j * rho := by
    intro j _
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  have hcancel :
      ∑ j ∈ Finset.range (k + 1),
        ((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j
          + shiCoefficient c k j * t ^ j * (kappa * v j)
          - 2 * (shiCoefficient c k j * t ^ j * v (j + 1)))
      ≤ shiCoefficient c k 0 * (kappa * v 0) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hderiv :
        ∑ j ∈ Finset.range (k + 1),
            (j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j
          = ∑ j ∈ Finset.range k,
              ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1)
                * t ^ j * v (j + 1) := by
      rw [Finset.sum_range_succ' (fun j =>
        (j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j) k]
      simp
    rw [hderiv]
    rw [Finset.sum_range_succ'
      (fun j => shiCoefficient c k j * t ^ j * (kappa * v j)) k]
    rw [Finset.sum_range_succ
      (fun j => 2 * (shiCoefficient c k j * t ^ j * v (j + 1))) k]
    have hterm : ∀ j ∈ Finset.range k,
        ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1)
              * t ^ j * v (j + 1)
          + shiCoefficient c k (j + 1) * t ^ (j + 1)
              * (kappa * v (j + 1))
        ≤ 2 * (shiCoefficient c k j * t ^ j * v (j + 1)) := by
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      have hpow : 0 ≤ t ^ j := pow_nonneg ht j
      have hvj : 0 ≤ v (j + 1) := hv (j + 1)
      have hd : t * kappa ≤ 1 + c := by linarith
      have hcancel := shiLevelCancel hc hjk
        (v := t ^ j * v (j + 1)) (d := t * kappa)
        (by positivity) hd
      have hrw : shiCoefficient c k (j + 1) * t ^ (j + 1)
            * (kappa * v (j + 1))
          = (t * kappa) * shiCoefficient c k (j + 1)
              * (t ^ j * v (j + 1)) := by
        rw [pow_succ]
        ring
      rw [hrw]
      have hrw2 : ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1)
            * t ^ j * v (j + 1)
          = ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1)
              * (t ^ j * v (j + 1)) := by ring
      rw [hrw2]
      calc
        ((j + 1 : ℕ) : ℝ) * shiCoefficient c k (j + 1)
              * (t ^ j * v (j + 1))
            + (t * kappa) * shiCoefficient c k (j + 1)
                * (t ^ j * v (j + 1))
          ≤ 2 * shiCoefficient c k j * (t ^ j * v (j + 1)) := hcancel
        _ = 2 * (shiCoefficient c k j * t ^ j * v (j + 1)) := by ring
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib] at hsum
    have htop : 0 ≤ 2 * (shiCoefficient c k k * t ^ k * v (k + 1)) := by
      have hck := (shiCoefficient_pos hc k k).le
      have hvk := hv (k + 1)
      have htk : (0 : ℝ) ≤ t ^ k := pow_nonneg ht k
      positivity
    simp only [pow_zero, mul_one]
    linarith
  have hrhogroup :
      ∑ j ∈ Finset.range (k + 1),
          shiCoefficient c k j * t ^ j * rho
        ≤ rho * shiWeightAt c k T := by
    rw [shiWeightAt, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have hcj := (shiCoefficient_pos hc k j).le
    have hpow : t ^ j ≤ T ^ j := pow_le_pow_left₀ ht htT j
    have hcoef : shiCoefficient c k j * t ^ j
        ≤ shiCoefficient c k j * T ^ j :=
      mul_le_mul_of_nonneg_left hpow hcj
    calc
      shiCoefficient c k j * t ^ j * rho
          ≤ shiCoefficient c k j * T ^ j * rho :=
            mul_le_mul_of_nonneg_right hcoef hrho
      _ = rho * (shiCoefficient c k j * T ^ j) := by ring
  linarith

/-- **Math.** Backwards-compatible small-time specialization of
`shiReactionSum_le_of_mul_le`.  The stronger hypothesis `t * kappa ≤ 1`
implies the generalized slack condition whenever `c` is nonnegative. -/
theorem shiReactionSum_le {c rho : ℝ} (hc : 0 ≤ c) (k : ℕ)
    {t kappa T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T)
    (hk1 : t * kappa ≤ 1) {v : ℕ → ℝ}
    (hv : ∀ j, 0 ≤ v j) (hrho : 0 ≤ rho) :
    ∑ j ∈ Finset.range (k + 1),
        (((j : ℝ) * shiCoefficient c k j * t ^ (j - 1) * v j)
          + shiCoefficient c k j * t ^ j
              * (-2 * v (j + 1) + kappa * v j + rho))
      ≤ rho * shiWeightAt c k T
          + shiCoefficient c k 0 * (kappa * v 0) := by
  apply shiReactionSum_le_of_mul_le hc k ht htT (by linarith)
    hv hrho

/-! ## Cutoff certificate and the local maximum-point arithmetic -/

/-- A cutoff certificate with exactly the estimates consumed at a weighted
parabolic maximum.  The fields are intentionally pointwise; a geometric
construction supplies them separately on a chosen chart and time interval. -/
structure ShiParabolicCutoff {X : Type*}
    (core outer : Set X) (eta lap grad : X → ℝ) (L G : ℝ) : Prop where
  L_nonneg : 0 ≤ L
  G_nonneg : 0 ≤ G
  nonneg : ∀ x, 0 ≤ eta x
  bounded : ∀ x, eta x ≤ 1
  one_on_core : ∀ x, x ∈ core → eta x = 1
  zero_off_outer : ∀ x, x ∉ outer → eta x = 0
  laplacian_bound : ∀ x, |lap x| ≤ L
  gradient_ratio : ∀ x, 0 < eta x → grad x ^ 2 / eta x ≤ G

/-! ## Explicit radial cutoff data -/

/-- The Euclidean cutoff used in the local Shi argument.  Its inner plateau is
the closed ball of radius `r / 4`, and its support is the open ball of radius
`r / 2`. -/
noncomputable def shiEuclideanCutoff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (hr : 0 < r) : ContDiffBump (0 : E) :=
  ⟨r / 4, r / 2, by linarith, by linarith⟩

theorem shiEuclideanCutoff_contDiff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ ∞ (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) := by
  exact (shiEuclideanCutoff (E := E) r hr).contDiff

theorem shiEuclideanCutoff_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) :
    0 ≤ (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x := by
  exact (shiEuclideanCutoff (E := E) r hr).nonneg

theorem shiEuclideanCutoff_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) (hr : 0 < r) (x : E) :
    (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x ≤ 1 := by
  exact (shiEuclideanCutoff (E := E) r hr).le_one

theorem shiEuclideanCutoff_eq_one_of_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {x : E}
    (hx : x ∈ Metric.closedBall (0 : E) (r / 4)) :
    (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x = 1 := by
  exact (shiEuclideanCutoff (E := E) r hr).one_of_mem_closedBall hx

theorem shiEuclideanCutoff_eq_zero_of_not_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {r : ℝ} (hr : 0 < r) {x : E}
    (hx : x ∉ Metric.ball (0 : E) (r / 2)) :
    (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) x = 0 := by
  have hs : x ∉ Function.support (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) := by
    rw [(shiEuclideanCutoff (E := E) r hr).support_eq]
    exact hx
  simpa [Function.mem_support] using hs

theorem shiEuclideanCutoff_hasCompactSupport
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) := by
  exact (shiEuclideanCutoff (E := E) r hr).hasCompactSupport

/-- Build the pointwise Shi cutoff certificate from the explicit Euclidean
bump.  The support and plateau inclusions are separated from the metric
estimates: `hlap` and `hgrad` are the geometric input on the evolving chart. -/
theorem shiParabolicCutoff_of_euclidean_bump
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {core outer : Set E} {r L G : ℝ} (hr : 0 < r)
    {lap grad : E → ℝ}
    (hcore : ∀ x, x ∈ core → x ∈ Metric.closedBall (0 : E) (r / 4))
    (houter : ∀ x, x ∉ outer → x ∉ Metric.ball (0 : E) (r / 2))
    (hL : 0 ≤ L) (hG : 0 ≤ G)
    (hlap : ∀ x, |lap x| ≤ L)
    (hgrad : ∀ x, 0 < (ContDiffBump.toFun (shiEuclideanCutoff r hr)) x →
      grad x ^ 2 / (ContDiffBump.toFun (shiEuclideanCutoff r hr)) x ≤ G) :
    ShiParabolicCutoff core outer
      (ContDiffBump.toFun (shiEuclideanCutoff (E := E) r hr)) lap grad L G := by
  refine
    { L_nonneg := hL
      G_nonneg := hG
      nonneg := fun x => shiEuclideanCutoff_nonneg r hr x
      bounded := fun x => shiEuclideanCutoff_le_one r hr x
      one_on_core := fun x hx => shiEuclideanCutoff_eq_one_of_mem hr (hcore x hx)
      zero_off_outer := fun x hx =>
        shiEuclideanCutoff_eq_zero_of_not_mem hr (houter x hx)
      laplacian_bound := hlap
      gradient_ratio := hgrad }

/-- The algebraic estimate at a positive interior maximum of `eta * F`.

The equation `hmaxgrad` is the vanishing spatial derivative of the weighted
quantity, and `hpde` is the parabolic differential inequality at that point.
Together with the cutoff fields, they imply the coercive bound used in the
Shi localization argument.  Supplying these maximum-principle hypotheses from
the curvature evolution and a chart cutoff is a separate Chapter 3 task. -/
theorem shiCutoffMaximumBound {X : Type*}
    {core outer : Set X} {eta lap grad dF F : X → ℝ} {L G c C0 C1 : ℝ}
    (hcut : ShiParabolicCutoff core outer eta lap grad L G)
    {x : X} (_hx : x ∈ outer) (heta : 0 < eta x)
    (hF : 2 * C0 ≤ F x) (hc : 0 < c) (hC0 : 0 < C0)
    (hmaxgrad : eta x * dF x + grad x * F x = 0)
    (hpde : 0 ≤ eta x * (-c * (F x - C0) ^ 2 + C1)
      - lap x * F x - 2 * grad x * dF x) :
    c * C0 * eta x * F x
      ≤ 2 * C1 * eta x + 4 * L * F x + 8 * G * F x := by
  have hF0 : 0 ≤ F x := by nlinarith
  have hratio : grad x ^ 2 ≤ G * eta x := by
    exact (div_le_iff₀ heta).mp (hcut.gradient_ratio x heta)
  have habs := abs_le.mp (hcut.laplacian_bound x)
  have hlower : -L ≤ lap x := habs.1
  have hdf : dF x = -grad x * F x / eta x := by
    apply (eq_div_iff (ne_of_gt heta)).2
    nlinarith [hmaxgrad]
  have hcross : -2 * grad x * dF x
      = 2 * grad x ^ 2 * F x / eta x := by
    rw [hdf]
    field_simp [ne_of_gt heta]
  have hgrad : 2 * grad x ^ 2 * F x / eta x ≤ 2 * G * F x := by
    apply (div_le_iff₀ heta).2
    nlinarith [hratio, hF0]
  have hlapterm : -lap x * F x ≤ L * F x := by
    exact mul_le_mul_of_nonneg_right (by linarith) hF0
  have hevol : c * eta x * (F x - C0) ^ 2
      ≤ eta x * C1 + L * F x + 2 * G * F x := by
    nlinarith [hpde, hcross, hgrad, hlapterm]
  have hsquare : F x ^ 2 / 4 ≤ (F x - C0) ^ 2 := by
    nlinarith [hF]
  have hmul := mul_le_mul_of_nonneg_left hsquare
    (mul_nonneg (le_of_lt hc) (le_of_lt heta))
  have hmul2 : c * eta x * F x ^ 2 / 2
      ≤ 2 * (eta x * C1 + L * F x + 2 * G * F x) := by
    nlinarith [hevol, hmul]
  have hC : c * C0 * eta x * F x ≤ c * eta x * F x ^ 2 / 2 := by
    nlinarith [hF, hc, hC0, heta]
  have hL : 0 ≤ L * F x := mul_nonneg hcut.L_nonneg hF0
  have hG : 0 ≤ G * F x := mul_nonneg hcut.G_nonneg hF0
  nlinarith [hmul2, hC, hL, hG]

end MorganTianLib

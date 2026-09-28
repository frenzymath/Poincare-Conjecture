import MorganTianLib.Ch03.RicciFlow.ShiKZeroBridge
import MorganTianLib.Ch03.RicciFlow.ShiTimeDependentGeometry

/-!
# Morgan--Tian Ch. 3 - the first Shi derivative estimate

This module exposes the order-one Shi estimate in the geometric notation used
for curvature.  The compact comparison theorem in `ShiEstimates` is stated
for an arbitrary tower; here the first two geometric evolution inequalities
are assembled into that tower explicitly.  In particular, this is a direct
producer for `|∇Rm|`, rather than a projection of a tower certificate.
The evolution and spatial maximum hypotheses remain explicit inputs: this
file does not assert the nonlinear curvature commutation calculation.
-/

open Set
open scoped ContDiff Manifold Topology Bundle BigOperators
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## The first derivative norm -/

/-- **Math.** The pointwise norm of the first covariant derivative of the
Riemann tensor, defined as the square root of the first Shi energy level. -/
def gradRiemannNormAt (g : RiemannianMetric I M) (p : M) : ℝ :=
  Real.sqrt (gradRiemannNormSqAt g p)

theorem gradRiemannNormAt_nonneg (g : RiemannianMetric I M) (p : M) :
    0 ≤ gradRiemannNormAt g p := by
  exact Real.sqrt_nonneg _

theorem gradRiemannNormAt_sq (g : RiemannianMetric I M) (p : M) :
    gradRiemannNormAt g p ^ 2 = gradRiemannNormSqAt g p := by
  unfold gradRiemannNormAt
  exact Real.sq_sqrt (riemannCovDerivNormSqAt_nonneg g 1 p)

/-! ## The source-scale first-order estimate -/

/-- **Math.** A compact first-order Shi bound for the geometric curvature
level.  The hypotheses `hzero` and `hone` are the actual level-zero and
level-one differential inequalities; the proof assembles them into
`ShiTowerInequalitiesOn` at order `k = 1` and applies the compact parabolic
comparison.  Thus the conclusion is the source-scale estimate
`|∇Rm|(p,t) ≤ C / √t` on `K`.

The remaining inputs (`hderiv`, `hcombCont`, `hspatialMax`, and `hlap`) are
the regularity, maximum-principle, and Laplacian interfaces required by the
analytic comparison.  No geometric evolution statement is hidden in a
certificate or supplied by an axiom.
-/
theorem shiFirstDerivativeBound_of_tower
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {c kappa rho T m : ℝ}
    (hK : IsCompact K) (hKne : K.Nonempty)
    (hT : 0 < T) (hc : 0 ≤ c) (hrho : 0 ≤ rho)
    (hm : 0 < m) (hkT : T * kappa ≤ 1 + c) (hkappa : 0 ≤ kappa)
    (hwnneg : ∀ j p t,
      0 ≤ riemannCovDerivNormSqAt (g t) j p)
    (hw0 : ∀ p t, t ∈ Icc (0 : ℝ) T →
      riemannCovDerivNormSqAt (g t) 0 p ≤ m ^ 2)
    (hderiv : ∀ j p t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt
        (fun s => riemannCovDerivNormSqAt (g s) j p)
        (derivWithin
          (fun s => riemannCovDerivNormSqAt (g s) j p)
          (Icc 0 T) t) (Icc 0 T) t)
    (hcombCont : ContinuousOn
      (fun z : M × ℝ =>
        shiTowerCombination c 1
          (fun j p t => riemannCovDerivNormSqAt (g t) j p)
          z.1 z.2)
      (K ×ˢ Icc 0 T))
    (hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ p ∈ K,
      (∀ q ∈ K,
        shiTowerCombination c 1
          (fun j x s => riemannCovDerivNormSqAt (g s) j x)
          q t ≤
        shiTowerCombination c 1
          (fun j x s => riemannCovDerivNormSqAt (g s) j x)
          p t) →
      lapCombination p t ≤ 0)
    (hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ p ∈ K,
      lapCombination p t =
        ∑ j ∈ Finset.range (1 + 1),
          shiCoefficient c 1 j * t ^ j * lap j p t)
    (hzero : ∀ t ∈ Icc (0 : ℝ) T, ∀ p ∈ K,
      derivWithin (fun s => riemannNormSqAt (g s) p)
          (Icc 0 T) t ≤
        lap 0 p t - 2 * gradRiemannNormSqAt (g t) p
          + kappa * riemannNormSqAt (g t) p + rho)
    (hone : ∀ t ∈ Icc (0 : ℝ) T, ∀ p ∈ K,
      derivWithin (fun s => gradRiemannNormSqAt (g s) p)
          (Icc 0 T) t ≤
        lap 1 p t - 2 * riemannCovDerivNormSqAt (g t) 2 p
          + kappa * gradRiemannNormSqAt (g t) p + rho) :
    ∀ p ∈ K, ∀ t, 0 < t → t ≤ T →
      gradRiemannNormAt (g t) p ≤
        Real.sqrt
            (shiCoefficient c 1 0 * m ^ 2 +
              (rho * shiWeightAt c 1 T +
                shiCoefficient c 1 0 * (kappa * m ^ 2)) * T) /
          Real.sqrt t := by
  have htower : ∀ j < 1 + 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ p ∈ K,
      derivWithin
          (fun s => riemannCovDerivNormSqAt (g s) j p)
          (Icc 0 T) t ≤
        lap j p t -
            2 * riemannCovDerivNormSqAt (g t) (j + 1) p +
          kappa * riemannCovDerivNormSqAt (g t) j p + rho := by
    intro j hj t ht p hp
    have hjcases : j = 0 ∨ j = 1 := by omega
    rcases hjcases with rfl | rfl
    · simpa [riemannNormSqAt, gradRiemannNormSqAt] using
        hzero t ht p hp
    · simpa [gradRiemannNormSqAt] using hone t ht p hp
  intro p hp t htpos htT
  have hbound :=
    shiTower_sqrt_le_div_on_compact_of_mul_le
      (K := K)
      (w := fun j x s => riemannCovDerivNormSqAt (g s) j x)
      (lap := lap) (lapCombination := lapCombination)
      hK hKne hT hc hrho hm hkT hkappa hwnneg hw0 hderiv
      hcombCont hspatialMax hlap htower p hp t htpos htT
  simpa [gradRiemannNormAt, gradRiemannNormSqAt] using hbound

/-! The certificate-facing projection keeps the all-order tower hypotheses
bundled while exposing the first-order source estimate directly. -/

/-- **Math.** An order-one geometric Shi certificate controls the first
covariant derivative of curvature at the source scale `t^(-1/2)`. -/
theorem RiemannianShiTowerCertificate.gradRiemannNormAt_le_time
    {g : ℝ → RiemannianMetric I M} {K : Set M}
    {lap : ℕ → M → ℝ → ℝ} {lapCombination : M → ℝ → ℝ}
    {T : ℝ}
    (C : RiemannianShiTowerCertificate (I := I)
      g K lap lapCombination T 1) :
    ∀ x ∈ K, ∀ t, 0 < t → t ≤ T →
      gradRiemannNormAt (g t) x ≤
        Real.sqrt
            (shiCoefficient C.c 1 0 * C.m ^ 2 +
              (C.rho * shiWeightAt C.c 1 T +
                shiCoefficient C.c 1 0 * (C.kappa * C.m ^ 2)) * T) /
          Real.sqrt t := by
  intro x hx t htpos htT
  have h := C.riemannCovDerivNormAt_le_time x hx t htpos htT
  change covTensorNormAt (g t) (riemannCovDerivTower (g t) 1) x ≤ _
  simpa [riemannCovDerivNormAt, pow_one] using h

end MorganTianLib

end

#print axioms MorganTianLib.gradRiemannNormAt
#print axioms MorganTianLib.gradRiemannNormAt_sq
#print axioms MorganTianLib.shiFirstDerivativeBound_of_tower
#print axioms MorganTianLib.RiemannianShiTowerCertificate.gradRiemannNormAt_le_time

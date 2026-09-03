import MorganTianLib.Ch03.RicciFlow.ShiInteriorBounds
import MorganTianLib.Ch03.RicciFlow.ShiGeometricLevels

/-!
# Morgan--Tian Ch. 3 - geometric all-order Shi bridge

`ShiEstimates` is deliberately phrased for an abstract family of scalar
levels.  This file packages the same finite-tower hypotheses with the levels
chosen to be the squared pointwise norms of the iterated Riemann tensor, and
then exposes the resulting compact-interior estimate as an ordinary geometric
norm bound.  The evolution and Laplacian inputs remain explicit: this is a
conditional bridge, not an assertion that those inputs follow from the
definitions alone.
-/

open scoped ContDiff Manifold Topology Bundle BigOperators
open Set

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Per-order geometric certificates -/

/-- **Math.** The finite Shi-tower data at order `k`, with the scalar levels fixed to
the squared norms of the geometric Riemann tensor derivative tower. -/
structure RiemannianShiTowerCertificate
    (g : ℝ → RiemannianMetric I M) (K : Set M)
    (lap : ℕ → M → ℝ → ℝ) (lapCombination : M → ℝ → ℝ)
    (T : ℝ) (k : ℕ) where
  c : ℝ
  kappa : ℝ
  rho : ℝ
  m : ℝ
  tau : ℝ
  hT : 0 < T
  hc : 0 ≤ c
  hrho : 0 ≤ rho
  hm : 0 < m
  hkT : T * kappa ≤ 1 + c
  hkappa : 0 ≤ kappa
  htau : 0 < tau
  htauT : tau ≤ T
  hK : IsCompact K
  hKne : K.Nonempty
  hwnneg : ∀ j x t, 0 ≤ riemannCovDerivNormSqAt (g t) j x
  hw0 : ∀ x t, t ∈ Icc (0 : ℝ) T →
    riemannCovDerivNormSqAt (g t) 0 x ≤ m ^ 2
  hderiv : ∀ j x t, t ∈ Icc (0 : ℝ) T →
    HasDerivWithinAt
      (fun s => riemannCovDerivNormSqAt (g s) j x)
      (derivWithin (fun s => riemannCovDerivNormSqAt (g s) j x)
        (Icc 0 T) t) (Icc 0 T) t
  hcombCont : ContinuousOn
    (fun z : M × ℝ =>
      shiTowerCombination c k
        (fun j x t => riemannCovDerivNormSqAt (g t) j x) z.1 z.2)
    (K ×ˢ Icc 0 T)
  hspatialMax : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
    (∀ y ∈ K,
      shiTowerCombination c k
        (fun j x t => riemannCovDerivNormSqAt (g t) j x) y t ≤
      shiTowerCombination c k
        (fun j x t => riemannCovDerivNormSqAt (g t) j x) x t) →
      lapCombination x t ≤ 0
  hlap : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
    lapCombination x t =
      ∑ j ∈ Finset.range (k + 1),
        shiCoefficient c k j * t ^ j * lap j x t
  htower : ∀ j < k + 1, ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ K,
    derivWithin (fun s => riemannCovDerivNormSqAt (g s) j x)
        (Icc 0 T) t ≤
      lap j x t - 2 * riemannCovDerivNormSqAt (g t) (j + 1) x +
        kappa * riemannCovDerivNormSqAt (g t) j x + rho

/-! ## All-order geometric norm estimate -/

/-- **Math.** A family of finite Shi-tower certificates yields, at every
order, an explicit compact-interior bound for the corresponding geometric
Riemann tensor derivative norm. -/
theorem riemannCovDerivNormAt_le_shi_bound_on_compact_interior
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
          Real.sqrt ((hcert k).tau ^ k) := by
  intro k x hx t ht
  let C := hcert k
  have hbound := shiTower_sqrt_le_div_on_compact_interior_of_mul_le
    (K := K)
    (w := fun j y s => riemannCovDerivNormSqAt (g s) j y)
    (lap := lap) (lapCombination := lapCombination)
    C.hK C.hKne C.hT C.hc C.hrho C.hm C.hkT C.hkappa C.hwnneg C.hw0
    C.hderiv C.hcombCont C.hspatialMax C.hlap C.htower C.htau C.htauT
    x hx t ht
  change Real.sqrt
      (covTensorNormSqAt (g t) (riemannCovDerivTower (g t) k) x) ≤ _
  simpa [C, riemannCovDerivNormSqAt] using hbound

end MorganTianLib

end

#print axioms MorganTianLib.riemannCovDerivNormAt_le_shi_bound_on_compact_interior

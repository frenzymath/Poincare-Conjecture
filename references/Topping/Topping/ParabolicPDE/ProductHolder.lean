import Topping.ParabolicPDE.ParabolicHolder

/-!
# Product-space Holder bridge

The parabolic package stores spatial and temporal estimates separately.  On a
product chart, when the two exponents agree, those estimates combine into an
ordinary Holder estimate for the max product metric.  This file records that
conversion on an arbitrary spatial chart domain.  It is an unconditional
metric-space statement and does not assume a PDE solution or a bundle
trivialization.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace ParabolicHolderControl

variable {X T V : Type*}
  [PseudoEMetricSpace X] [PseudoEMetricSpace T] [PseudoEMetricSpace V]
  {u : X × T → V} {J : Set T}

/-- Separate spatial and temporal Holder estimates with a common exponent
give a Holder estimate on every product chart domain.  The product metric is
the max metric, so each factor distance is bounded by the product distance. -/
theorem holderOnWith_prod_of_common_exponent
    (S : Set X) {Cs Ct α : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct α) :
    HolderOnWith (Cs + Ct) α u (S ×ˢ J) := by
  rintro ⟨x, s⟩ hs ⟨y, t⟩ ht
  have hsJ : s ∈ J := hs.2
  have htJ : t ∈ J := ht.2
  have hxy : edist x y ≤ edist (x, s) (y, t) := by
    rw [Prod.edist_eq]
    exact le_max_left _ _
  have hst : edist s t ≤ edist (x, s) (y, t) := by
    rw [Prod.edist_eq]
    exact le_max_right _ _
  have hpowxy : edist x y ^ (α : ℝ) ≤
      edist (x, s) (y, t) ^ (α : ℝ) := by
    exact ENNReal.rpow_le_rpow hxy α.coe_nonneg
  have hpowst : edist s t ^ (α : ℝ) ≤
      edist (x, s) (y, t) ^ (α : ℝ) := by
    exact ENNReal.rpow_le_rpow hst α.coe_nonneg
  calc
    edist (u (x, s)) (u (y, t)) ≤
        (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ) +
          (Ct : ℝ≥0∞) * edist s t ^ (α : ℝ) :=
      h.edist_le_split hsJ htJ
    _ ≤ (Cs : ℝ≥0∞) * edist (x, s) (y, t) ^ (α : ℝ) +
          (Ct : ℝ≥0∞) * edist (x, s) (y, t) ^ (α : ℝ) := by
      exact add_le_add
        (by simpa [mul_comm] using
          (mul_le_mul_right hpowxy (Cs : ℝ≥0∞)))
        (by simpa [mul_comm] using
          (mul_le_mul_right hpowst (Ct : ℝ≥0∞)))
    _ = (↑(Cs + Ct) : ℝ≥0∞) * edist (x, s) (y, t) ^ (α : ℝ) := by
      rw [ENNReal.coe_add, add_mul]

/-! A positive common exponent upgrades the product estimate to continuity on
the chart domain. -/

/-- The common-exponent product Holder bridge gives continuity on every
spatial chart domain once its exponent is positive. -/
theorem continuousOn_prod_of_common_exponent
    (S : Set X) {Cs Ct α : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct α)
    (hα : 0 < α) :
    ContinuousOn u (S ×ˢ J) := by
  exact (h.holderOnWith_prod_of_common_exponent S).continuousOn hα

/-- On the full product, a common-exponent parabolic Holder control is an
ordinary global Holder control for the max product metric. -/
theorem holderWith_prod_of_common_exponent
    {Cs Ct α : ℝ≥0}
    (h : ParabolicHolderControl u (Set.univ : Set T) Cs α Ct α) :
    HolderWith (Cs + Ct) α u := by
  have hp := h.holderOnWith_prod_of_common_exponent
    (S := (Set.univ : Set X))
  simpa only [Set.univ_prod_univ, holderOnWith_univ] using hp

/-- A bounded product chart also converts anisotropic Holder control to an
ordinary Holder estimate at any lower exponent.  The diameter factors record
the loss from the spatial and temporal exponents separately. -/
theorem holderOnWith_prod_of_bounded_diameter
    (S : Set X) {Cs Ct α β r D : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β)
    (hrα : r ≤ α) (hrβ : r ≤ β)
    (hD : ∀ z ∈ S ×ˢ J, ∀ z' ∈ S ×ˢ J,
      edist z z' ≤ (D : ℝ≥0∞)) :
    HolderOnWith
      (Cs * D ^ ((α : ℝ) - (r : ℝ)) +
        Ct * D ^ ((β : ℝ) - (r : ℝ))) r u (S ×ˢ J) := by
  rintro ⟨x, s⟩ hs ⟨y, t⟩ ht
  have hsJ : s ∈ J := hs.2
  have htJ : t ∈ J := ht.2
  have hprodxy : edist x y ≤ edist (x, s) (y, t) := by
    rw [Prod.edist_eq]
    exact le_max_left _ _
  have hprodst : edist s t ≤ edist (x, s) (y, t) := by
    rw [Prod.edist_eq]
    exact le_max_right _ _
  have hdiam : edist (x, s) (y, t) ≤ (D : ℝ≥0∞) :=
    hD (x, s) hs (y, t) ht
  have hxyD : edist x y ≤ (D : ℝ≥0∞) := hprodxy.trans hdiam
  have hstD : edist s t ≤ (D : ℝ≥0∞) := hprodst.trans hdiam
  have hr0 : 0 ≤ (r : ℝ) := r.coe_nonneg
  have hαr : 0 ≤ (α : ℝ) - (r : ℝ) :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrα)
  have hβr : 0 ≤ (β : ℝ) - (r : ℝ) :=
    sub_nonneg.mpr (NNReal.coe_le_coe.mpr hrβ)
  have hpowα : edist x y ^ (α : ℝ) ≤
      (D : ℝ≥0∞) ^ ((α : ℝ) - (r : ℝ)) *
        edist (x, s) (y, t) ^ (r : ℝ) := by
    calc
      edist x y ^ (α : ℝ) =
          edist x y ^ ((α : ℝ) - (r : ℝ)) *
            edist x y ^ (r : ℝ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hαr hr0]
        congr 1
        ring
      _ ≤ (D : ℝ≥0∞) ^ ((α : ℝ) - (r : ℝ)) *
          edist (x, s) (y, t) ^ (r : ℝ) := by
        exact mul_le_mul
          (ENNReal.rpow_le_rpow hxyD hαr)
          (ENNReal.rpow_le_rpow hprodxy hr0)
          (by positivity) (by positivity)
  have hpowβ : edist s t ^ (β : ℝ) ≤
      (D : ℝ≥0∞) ^ ((β : ℝ) - (r : ℝ)) *
        edist (x, s) (y, t) ^ (r : ℝ) := by
    calc
      edist s t ^ (β : ℝ) =
          edist s t ^ ((β : ℝ) - (r : ℝ)) *
            edist s t ^ (r : ℝ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ hβr hr0]
        congr 1
        ring
      _ ≤ (D : ℝ≥0∞) ^ ((β : ℝ) - (r : ℝ)) *
          edist (x, s) (y, t) ^ (r : ℝ) := by
        exact mul_le_mul
          (ENNReal.rpow_le_rpow hstD hβr)
          (ENNReal.rpow_le_rpow hprodst hr0)
          (by positivity) (by positivity)
  calc
    edist (u (x, s)) (u (y, t)) ≤
        (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ) +
          (Ct : ℝ≥0∞) * edist s t ^ (β : ℝ) :=
      h.edist_le_split hsJ htJ
    _ ≤ (Cs : ℝ≥0∞) *
          ((D : ℝ≥0∞) ^ ((α : ℝ) - (r : ℝ)) *
            edist (x, s) (y, t) ^ (r : ℝ)) +
          (Ct : ℝ≥0∞) *
          ((D : ℝ≥0∞) ^ ((β : ℝ) - (r : ℝ)) *
            edist (x, s) (y, t) ^ (r : ℝ)) := by
      exact add_le_add
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_right hpowα (Cs : ℝ≥0∞)))
        (by simpa [mul_comm, mul_left_comm, mul_assoc] using
          (mul_le_mul_right hpowβ (Ct : ℝ≥0∞)))
    _ = (↑(Cs * D ^ ((α : ℝ) - (r : ℝ)) +
          Ct * D ^ ((β : ℝ) - (r : ℝ))) : ℝ≥0∞) *
          edist (x, s) (y, t) ^ (r : ℝ) := by
      simp only [ENNReal.coe_add, ENNReal.coe_mul,
        ENNReal.coe_rpow_of_nonneg _ hαr,
        ENNReal.coe_rpow_of_nonneg _ hβr]
      ring

/-- The bounded-diameter lower-exponent bridge gives continuity whenever the
chosen lower exponent is positive. -/
theorem continuousOn_prod_of_bounded_diameter
    (S : Set X) {Cs Ct α β r D : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β)
    (hrα : r ≤ α) (hrβ : r ≤ β)
    (hD : ∀ z ∈ S ×ˢ J, ∀ z' ∈ S ×ˢ J,
      edist z z' ≤ (D : ℝ≥0∞))
    (hr : 0 < r) :
    ContinuousOn u (S ×ˢ J) := by
  exact (h.holderOnWith_prod_of_bounded_diameter S hrα hrβ hD).continuousOn hr

/-- The canonical lower-exponent specialization uses the minimum of the two
parabolic exponents. -/
theorem holderOnWith_prod_of_bounded_diameter_min_exponent
    (S : Set X) {Cs Ct α β D : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β)
    (hD : ∀ z ∈ S ×ˢ J, ∀ z' ∈ S ×ˢ J,
      edist z z' ≤ (D : ℝ≥0∞)) :
    HolderOnWith
      (Cs * D ^ ((α : ℝ) - (↑(min α β) : ℝ)) +
        Ct * D ^ ((β : ℝ) - (↑(min α β) : ℝ))) (min α β) u (S ×ˢ J) := by
  exact h.holderOnWith_prod_of_bounded_diameter S
    (min_le_left _ _) (min_le_right _ _) hD

end ParabolicHolderControl

end
end ParabolicPDE
end Topping

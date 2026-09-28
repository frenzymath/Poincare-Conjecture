import Topping.ParabolicPDE.ParabolicHolder
import Topping.ParabolicPDE.VariableHolder

/-!
# Parabolic Holder control for variable-coefficient section maps

This module combines the separate spatial and temporal Holder package with
the variable-coefficient second-order jet estimate.  It is the section-valued
closure estimate needed before a chartwise Schauder construction: applying a
uniformly bounded parabolic Holder coefficient field to uniformly bounded
parabolic Holder value and jet fields preserves both parabolic exponents.
-/

namespace Topping

open scoped BigOperators NNReal ENNReal Topology

noncomputable section

namespace ParabolicPDE

open Set

namespace ParabolicHolderControl

variable {X T E V : Type*}
  [PseudoMetricSpace X] [PseudoMetricSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V]
  {J : Set T}

/-! ## Products and finite sums -/

/-! Scalar and additive closure are useful when forming linearized
perturbations of a section-space source. -/

/-- Scalar multiplication preserves parabolic Holder control, with both
Holder constants scaled by the scalar norm. -/
theorem smul
    [NormedSpace ℝ V]
    (c : ℝ) {u : X × T → V} {Cs Ct α β : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β) :
    ParabolicHolderControl (fun z => c • u z) J
      (‖c‖₊ * Cs) α (‖c‖₊ * Ct) β := by
  refine ⟨?_, ?_⟩
  · intro t ht x y
    change edist (c • u (x, t)) (c • u (y, t)) ≤
      (↑(‖c‖₊ * Cs) : ℝ≥0∞) * edist x y ^ (α : ℝ)
    rw [edist_smul₀, ENNReal.smul_def, smul_eq_mul]
    simpa [NNReal.coe_mul, mul_assoc] using
      (mul_le_mul_right (h.spatial t ht x y)
        (‖c‖₊ : ℝ≥0∞))
  · intro x s hs t ht
    change edist (c • u (x, s)) (c • u (x, t)) ≤
      (↑(‖c‖₊ * Ct) : ℝ≥0∞) * edist s t ^ (β : ℝ)
    rw [edist_smul₀, ENNReal.smul_def, smul_eq_mul]
    simpa [NNReal.coe_mul, mul_assoc] using
      (mul_le_mul_right (h.temporal x s hs t ht)
        (‖c‖₊ : ℝ≥0∞))

/-- Negation preserves parabolic Holder control. -/
theorem neg
    {u : X × T → V} {Cs Ct α β : ℝ≥0}
    (h : ParabolicHolderControl u J Cs α Ct β) :
    ParabolicHolderControl (fun z => -u z) J Cs α Ct β := by
  refine ⟨?_, ?_⟩
  · intro t ht x y
    change edist (-u (x, t)) (-u (y, t)) ≤
      (Cs : ℝ≥0∞) * edist x y ^ (α : ℝ)
    simpa only [edist_neg_neg] using h.spatial t ht x y
  · intro x s hs t ht
    change edist (-u (x, s)) (-u (x, t)) ≤
      (Ct : ℝ≥0∞) * edist s t ^ (β : ℝ)
    simpa only [edist_neg_neg] using h.temporal x s hs t ht

/-- Applying a variable continuous-linear operator to a parabolically Holder
field preserves the two estimates, with the usual product constants. -/
theorem clm_apply
    [NormedSpace ℝ V]
    {F : X × T → (E →L[ℝ] V)} {u : X × T → E}
    {CFs CFt Cus Cut BF Bu α β : ℝ≥0}
    (hF : ParabolicHolderControl F J CFs α CFt β)
    (hu : ParabolicHolderControl u J Cus α Cut β)
    (hFbound : ∀ z, ‖F z‖ ≤ BF)
    (hubound : ∀ z, ‖u z‖ ≤ Bu) :
    ParabolicHolderControl (fun z => F z (u z)) J
      (BF * Cus + CFs * Bu) α
      (BF * Cut + CFt * Bu) β := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact holderWith_clm_apply
      (hF.spatial t ht) (hu.spatial t ht)
      (fun x => hFbound (x, t)) (fun x => hubound (x, t))
  · intro x s hs t ht
    have hF' : HolderWith CFt β (J.restrict (fun t : T => F (x, t))) :=
      (hF.temporal x).holderWith
    have hu' : HolderWith Cut β (J.restrict (fun t : T => u (x, t))) :=
      (hu.temporal x).holderWith
    have hFbound' : ∀ q : J, ‖F (x, q.1)‖ ≤ BF := by
      intro q
      exact hFbound (x, q.1)
    have hubound' : ∀ q : J, ‖u (x, q.1)‖ ≤ Bu := by
      intro q
      exact hubound (x, q.1)
    have h := holderWith_clm_apply hF' hu' hFbound' hubound'
    simpa using h ⟨s, hs⟩ ⟨t, ht⟩

/-- The sum of two parabolic Holder fields is parabolically Holder. -/
theorem add
    {u v : X × T → V} {Cu Cv Du Dv α β : ℝ≥0}
    (hu : ParabolicHolderControl u J Cu α Cv β)
    (hv : ParabolicHolderControl v J Du α Dv β) :
    ParabolicHolderControl (fun z => u z + v z) J
      (Cu + Du) α (Cv + Dv) β := by
  refine ⟨?_, ?_⟩
  · intro t ht x y
    change edist (u (x, t) + v (x, t)) (u (y, t) + v (y, t)) ≤
      (↑(Cu + Du) : ℝ≥0∞) * edist x y ^ (α : ℝ)
    calc
      edist (u (x, t) + v (x, t)) (u (y, t) + v (y, t)) ≤
          edist (u (x, t)) (u (y, t)) +
            edist (v (x, t)) (v (y, t)) := edist_add_add_le _ _ _ _
      _ ≤ (Cu : ℝ≥0∞) * edist x y ^ (α : ℝ) +
          (Du : ℝ≥0∞) * edist x y ^ (α : ℝ) :=
        add_le_add (hu.spatial t ht x y) (hv.spatial t ht x y)
      _ = (↑(Cu + Du) : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_add, add_mul]
  · intro x s hs t ht
    change edist (u (x, s) + v (x, s)) (u (x, t) + v (x, t)) ≤
      (↑(Cv + Dv) : ℝ≥0∞) * edist s t ^ (β : ℝ)
    calc
      edist (u (x, s) + v (x, s)) (u (x, t) + v (x, t)) ≤
          edist (u (x, s)) (u (x, t)) +
            edist (v (x, s)) (v (x, t)) := edist_add_add_le _ _ _ _
      _ ≤ (Cv : ℝ≥0∞) * edist s t ^ (β : ℝ) +
          (Dv : ℝ≥0∞) * edist s t ^ (β : ℝ) :=
        add_le_add (hu.temporal x s hs t ht) (hv.temporal x s hs t ht)
      _ = (↑(Cv + Dv) : ℝ≥0∞) * edist s t ^ (β : ℝ) := by
        rw [ENNReal.coe_add, add_mul]

/-- Finite sums preserve parabolic Holder control, with constants summed over
the same finite index set. -/
theorem finset_sum
    {ι : Type*} (s : Finset ι) {f : ι → X × T → V}
    {Cs Ct : ι → ℝ≥0} {α β : ℝ≥0}
    (hf : ∀ i ∈ s,
      ParabolicHolderControl (f i) J (Cs i) α (Ct i) β) :
    ParabolicHolderControl (fun z => ∑ i ∈ s, f i z) J
      (∑ i ∈ s, Cs i) α (∑ i ∈ s, Ct i) β := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_⟩
      · intro t ht
        simp [SpatialHolderWith]
      · intro x s hs t ht
        simp
  | @insert i s hi ih =>
      have hi' := hf i (by simp)
      have hs' : ∀ j ∈ s,
          ParabolicHolderControl (f j) J (Cs j) α (Ct j) β := by
        intro j hj
        exact hf j (by simp [hj])
      have hsum := add hi' (ih hs')
      simpa [Finset.sum_insert hi, Pi.add_apply] using hsum

/-- Subtraction preserves parabolic Holder control, with additive constants. -/
theorem sub
    {u v : X × T → V} {Cu Cv Du Dv α β : ℝ≥0}
    (hu : ParabolicHolderControl u J Cu α Cv β)
    (hv : ParabolicHolderControl v J Du α Dv β) :
    ParabolicHolderControl (fun z => u z - v z) J
      (Cu + Du) α (Cv + Dv) β := by
  simpa [sub_eq_add_neg] using hu.add hv.neg

end ParabolicHolderControl

namespace VectorSecondOrderCoefficients

variable {X T : Type*} [PseudoMetricSpace X] [PseudoMetricSpace T]
  {ι : Type*} [Fintype ι] {V : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {J : Set T}

/-! ## The variable second-order evaluator -/

/-- A variable second-order coefficient field applied to parabolically Holder
value and jet fields remains parabolically Holder.  The theorem is entirely
local-coordinate algebra and supplies the section-space estimate needed by a
later Schauder construction. -/
theorem parabolicHolderControl_applyJetArgs
    (A : VectorSecondOrderCoefficients (X × T) ι V)
    (value : X × T → V) (first : ι → X × T → V)
    (second : ι → ι → X × T → V)
    {α β : ℝ≥0}
    (valueCs valueCt valueB : ℝ≥0)
    (firstCs firstCt : ι → ℝ≥0) (firstB : ι → ℝ≥0)
    (secondCs secondCt : ι → ι → ℝ≥0)
    (secondB : ι → ι → ℝ≥0)
    (aCs aCt : ι → ι → ℝ≥0) (aB : ι → ι → ℝ≥0)
    (bCs bCt : ι → ℝ≥0) (bB : ι → ℝ≥0)
    (cCs cCt cB : ℝ≥0)
    (hv : ParabolicHolderControl value J valueCs α valueCt β)
    (hfirst : ∀ i,
      ParabolicHolderControl (first i) J (firstCs i) α (firstCt i) β)
    (hsecond : ∀ i k,
      ParabolicHolderControl (second i k) J (secondCs i k) α
        (secondCt i k) β)
    (ha : ∀ i k,
      ParabolicHolderControl (fun z => A.a z i k) J (aCs i k) α
        (aCt i k) β)
    (hb : ∀ i,
      ParabolicHolderControl (fun z => A.b z i) J (bCs i) α (bCt i) β)
    (hc : ParabolicHolderControl (fun z => A.c z) J cCs α cCt β)
    (ha_bound : ∀ i k z, ‖A.a z i k‖ ≤ aB i k)
    (hb_bound : ∀ i z, ‖A.b z i‖ ≤ bB i)
    (hc_bound : ∀ z, ‖A.c z‖ ≤ cB)
    (value_bound : ∀ z, ‖value z‖ ≤ valueB)
    (first_bound : ∀ i z, ‖first i z‖ ≤ firstB i)
    (second_bound : ∀ i k z, ‖second i k z‖ ≤ secondB i k) :
    ParabolicHolderControl
      (fun z => A.applyJetArgs z (value z)
        (fun i => first i z) (fun i k => second i k z)) J
      ((∑ i, ∑ k, (aB i k * secondCs i k + aCs i k * secondB i k)) +
        (∑ i, (bB i * firstCs i + bCs i * firstB i)) +
          (cB * valueCs + cCs * valueB)) α
      ((∑ i, ∑ k, (aB i k * secondCt i k + aCt i k * secondB i k)) +
        (∑ i, (bB i * firstCt i + bCt i * firstB i)) +
          (cB * valueCt + cCt * valueB)) β := by
  have ha' : ∀ i k,
      ParabolicHolderControl
        (fun z => A.a z i k (second i k z)) J
        (aB i k * secondCs i k + aCs i k * secondB i k) α
        (aB i k * secondCt i k + aCt i k * secondB i k) β := by
    intro i k
    exact ParabolicHolderControl.clm_apply (ha i k) (hsecond i k)
      (ha_bound i k) (second_bound i k)
  have hb' : ∀ i,
      ParabolicHolderControl
        (fun z => A.b z i (first i z)) J
        (bB i * firstCs i + bCs i * firstB i) α
        (bB i * firstCt i + bCt i * firstB i) β := by
    intro i
    exact ParabolicHolderControl.clm_apply (hb i) (hfirst i)
      (hb_bound i) (first_bound i)
  have hc' : ParabolicHolderControl
      (fun z => A.c z (value z)) J
      (cB * valueCs + cCs * valueB) α
      (cB * valueCt + cCt * valueB) β :=
    ParabolicHolderControl.clm_apply hc hv hc_bound value_bound
  have hsumA := ParabolicHolderControl.finset_sum (s := Finset.univ)
    (fun i hi => ParabolicHolderControl.finset_sum (s := Finset.univ)
      (fun k hk => ha' i k))
  have hsumB := ParabolicHolderControl.finset_sum (s := Finset.univ)
    (fun i hi => hb' i)
  have htotal := ParabolicHolderControl.add hsumA hsumB
  have htotal' := ParabolicHolderControl.add htotal hc'
  convert htotal' using 1
  rfl

end VectorSecondOrderCoefficients

end ParabolicPDE

end
end Topping

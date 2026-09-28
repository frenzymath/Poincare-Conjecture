import MorganTianLib.Ch04.PositiveRicciPinching

/-!
# Algebraic positive-Ricci ratio cone

This file supplies the finite-dimensional reaction estimate behind the
positive-Ricci pinching argument.  It is deliberately independent of the
geometric maximum principle: the latter is still responsible for transporting
the ratio bound through space and time.
-/

noncomputable section

namespace MorganTianLib

/-- **Math.** The ordinary Ricci eigenvalue reaction preserves the lower
ratio bound in every coordinate of the nonnegative Ricci cone. -/
theorem ricciEigenReaction_ratio_lower_bound
    {a b c delta : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hδ : 3 * delta ≤ 1)
    (hapinch : delta * ricciEigenScalar a b c ≤ a)
    (hbpinch : delta * ricciEigenScalar a b c ≤ b)
    (hpinch : delta * ricciEigenScalar a b c ≤ c) :
    delta * (ricciEigenReaction a b c +
      ricciEigenReaction b a c + ricciEigenReaction c a b) ≤
      ricciEigenReaction c a b := by
  have hR : 0 ≤ ricciEigenScalar a b c := by
    unfold ricciEigenScalar
    linarith
  have hδlt : 0 ≤ 1 - 3 * delta := by linarith
  have hs : 0 ≤ a + b - 2 * delta * ricciEigenScalar a b c := by
    linarith
  have hz : 0 ≤ c - delta * ricciEigenScalar a b c := sub_nonneg.mpr hpinch
  have hd : 0 ≤ (a - b) ^ 2 := sq_nonneg _
  have h1 : 0 ≤ 1 - delta := by linarith
  have h2 : 0 ≤ 1 + 3 * delta := by linarith
  have hfactor :
      ricciEigenReaction c a b -
          delta * (ricciEigenReaction a b c +
            ricciEigenReaction b a c + ricciEigenReaction c a b) =
        (1 - delta) * (a - b) ^ 2 +
          delta ^ 2 * (1 - 3 * delta) * ricciEigenScalar a b c ^ 2 +
          (1 + 3 * delta) * (c - delta * ricciEigenScalar a b c) *
            (a + b - 2 * delta * ricciEigenScalar a b c) +
          3 * delta ^ 2 * ricciEigenScalar a b c *
            (c - delta * ricciEigenScalar a b c) := by
    unfold ricciEigenReaction ricciEigenScalar
    ring
  have hnonneg : 0 ≤
      (1 - delta) * (a - b) ^ 2 +
        delta ^ 2 * (1 - 3 * delta) * ricciEigenScalar a b c ^ 2 +
        (1 + 3 * delta) * (c - delta * ricciEigenScalar a b c) *
          (a + b - 2 * delta * ricciEigenScalar a b c) +
        3 * delta ^ 2 * ricciEigenScalar a b c *
          (c - delta * ricciEigenScalar a b c) := by
    positivity
  have hineq : 0 ≤ ricciEigenReaction c a b -
      delta * (ricciEigenReaction a b c +
        ricciEigenReaction b a c + ricciEigenReaction c a b) := by
    rw [hfactor]
    exact hnonneg
  exact sub_nonneg.mp hineq

/-- **Math.** The ordered coordinate form supplies the same pinching bound
used by `positiveRicciPinching_weighted_reaction_nonpos`. -/
theorem ricciEigenReaction_pinching_nonneg
    {a b c delta : ℝ} (hab : b ≤ a) (hbc : c ≤ b)
    (hc : 0 ≤ c) (hdelta : 0 ≤ delta)
    (hδ : 3 * delta ≤ 1)
    (hpinch : delta * ricciEigenScalar a b c ≤ c) :
    delta * (ricciEigenReaction a b c +
      ricciEigenReaction b a c + ricciEigenReaction c a b) ≤
      ricciEigenReaction c a b :=
  ricciEigenReaction_ratio_lower_bound (hc.trans (hbc.trans hab)) (hc.trans hbc)
    hc hdelta hδ (hpinch.trans (hbc.trans hab)) (hpinch.trans hbc) hpinch

/-- **Math.** Nonnegative Ricci eigenvalues with a uniform scalar ratio bound. -/
def positiveRicciRatioCone (delta : ℝ) : Set (Fin 3 → ℝ) :=
  {v | ∀ i, 0 ≤ v i ∧ delta * ricciEigenScalar (v 0) (v 1) (v 2) ≤ v i}

/-- **Math.** The ordinary Ricci eigenvalue reaction in vector form. -/
def ricciEigenReactionVector (v : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![ricciEigenReaction (v 0) (v 1) (v 2),
    ricciEigenReaction (v 1) (v 0) (v 2),
    ricciEigenReaction (v 2) (v 0) (v 1)]

/-- **Math.** The ratio cone is closed. -/
theorem isClosed_positiveRicciRatioCone (delta : ℝ) :
    IsClosed (positiveRicciRatioCone delta) := by
  change IsClosed {v : Fin 3 → ℝ | ∀ i,
    0 ≤ v i ∧ delta * ricciEigenScalar (v 0) (v 1) (v 2) ≤ v i}
  rw [show {v : Fin 3 → ℝ | ∀ i,
      0 ≤ v i ∧ delta * ricciEigenScalar (v 0) (v 1) (v 2) ≤ v i} =
      ⋂ i : Fin 3, {v : Fin 3 → ℝ |
        0 ≤ v i ∧ delta * ricciEigenScalar (v 0) (v 1) (v 2) ≤ v i} by
    ext v; simp]
  apply isClosed_iInter
  intro i
  apply IsClosed.inter
  · exact isClosed_le continuous_const (continuous_apply i)
  · apply isClosed_le _ (continuous_apply i)
    unfold ricciEigenScalar
    fun_prop

/-- **Math.** The ratio cone is convex. -/
theorem convex_positiveRicciRatioCone (delta : ℝ) :
    Convex ℝ (positiveRicciRatioCone delta) := by
  intro u hu v hv a b ha hb hab i
  obtain ⟨hu0, hur⟩ := hu i
  obtain ⟨hv0, hvr⟩ := hv i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · exact add_nonneg (mul_nonneg ha hu0) (mul_nonneg hb hv0)
  · unfold ricciEigenScalar at hur hvr ⊢
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hur),
      mul_nonneg hb (sub_nonneg.mpr hvr)]

@[simp] theorem zero_mem_positiveRicciRatioCone (delta : ℝ) :
    (0 : Fin 3 → ℝ) ∈ positiveRicciRatioCone delta := by
  intro i
  simp [ricciEigenScalar]

/-- **Math.** The quantitative Ricci cone is stable under addition. -/
theorem add_mem_positiveRicciRatioCone {delta : ℝ} {u v : Fin 3 → ℝ}
    (hu : u ∈ positiveRicciRatioCone delta) (hv : v ∈ positiveRicciRatioCone delta) :
    u + v ∈ positiveRicciRatioCone delta := by
  intro i
  obtain ⟨hu0, hur⟩ := hu i
  obtain ⟨hv0, hvr⟩ := hv i
  constructor
  · exact add_nonneg hu0 hv0
  · change delta * ricciEigenScalar (u 0 + v 0) (u 1 + v 1) (u 2 + v 2) ≤ _
    unfold ricciEigenScalar at hur hvr ⊢
    change delta * (u 0 + v 0 + (u 1 + v 1) + (u 2 + v 2)) ≤ u i + v i
    nlinarith

/-- **Math.** For `0 <= delta <= 1/3`, the ordinary Ricci reaction maps the
whole quantitative Ricci cone into itself. -/
theorem ricciEigenReactionVector_mem_positiveRicciRatioCone
    {delta : ℝ} (hdelta : 0 ≤ delta) (hδ : 3 * delta ≤ 1)
    {v : Fin 3 → ℝ} (hv : v ∈ positiveRicciRatioCone delta) :
    ricciEigenReactionVector v ∈ positiveRicciRatioCone delta := by
  have h0 := hv 0
  have h1 := hv 1
  have h2 := hv 2
  have h (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
      (hpa : delta * ricciEigenScalar a b c ≤ a)
      (hpb : delta * ricciEigenScalar a b c ≤ b)
      (hpc : delta * ricciEigenScalar a b c ≤ c) :
      0 ≤ ricciEigenReaction c a b ∧
      delta * ricciEigenScalar (ricciEigenReaction a b c)
        (ricciEigenReaction b a c) (ricciEigenReaction c a b) ≤
        ricciEigenReaction c a b := by
    constructor
    · unfold ricciEigenReaction
      positivity
    · exact ricciEigenReaction_ratio_lower_bound ha hb hc hdelta hδ hpa hpb hpc
  have hr (a b c : ℝ) : ricciEigenReaction a b c = ricciEigenReaction a c b := by
    unfold ricciEigenReaction
    ring
  intro i
  fin_cases i
  · change 0 ≤ ricciEigenReaction (v 0) (v 1) (v 2) ∧
      delta * ricciEigenScalar (ricciEigenReaction (v 0) (v 1) (v 2))
        (ricciEigenReaction (v 1) (v 0) (v 2))
        (ricciEigenReaction (v 2) (v 0) (v 1)) ≤
        ricciEigenReaction (v 0) (v 1) (v 2)
    have hh := h (v 1) (v 2) (v 0) h1.1 h2.1 h0.1
        (by simpa [ricciEigenScalar, add_comm, add_left_comm, add_assoc] using h1.2)
        (by simpa [ricciEigenScalar, add_comm, add_left_comm, add_assoc] using h2.2)
        (by simpa [ricciEigenScalar, add_comm, add_left_comm, add_assoc] using h0.2)
    rw [hr (v 1) (v 2) (v 0), hr (v 2) (v 1) (v 0)] at hh
    constructor
    · exact hh.1
    · convert hh.2 using 1
      unfold ricciEigenScalar
      ring
  · change 0 ≤ ricciEigenReaction (v 1) (v 0) (v 2) ∧
      delta * ricciEigenScalar (ricciEigenReaction (v 0) (v 1) (v 2))
        (ricciEigenReaction (v 1) (v 0) (v 2))
        (ricciEigenReaction (v 2) (v 0) (v 1)) ≤
        ricciEigenReaction (v 1) (v 0) (v 2)
    simpa [ricciEigenScalar, hr, add_comm, add_left_comm,
      add_assoc] using h (v 0) (v 2) (v 1) h0.1 h2.1 h1.1
        (by simpa [ricciEigenScalar, add_comm, add_left_comm, add_assoc] using h0.2)
        (by simpa [ricciEigenScalar, add_comm, add_left_comm, add_assoc] using h2.2)
        (by simpa [ricciEigenScalar, add_comm, add_left_comm, add_assoc] using h1.2)
  · change 0 ≤ ricciEigenReaction (v 2) (v 0) (v 1) ∧
      delta * ricciEigenScalar (ricciEigenReaction (v 0) (v 1) (v 2))
        (ricciEigenReaction (v 1) (v 0) (v 2))
        (ricciEigenReaction (v 2) (v 0) (v 1)) ≤
        ricciEigenReaction (v 2) (v 0) (v 1)
    exact h (v 0) (v 1) (v 2) h0.1 h1.1 h2.1 h0.2 h1.2 h2.2

/-- **Math.** The ratio cone satisfies the tangent condition used by
Hamilton's maximum principle. -/
theorem ricciEigenReactionVector_preserves_positiveRicciRatioCone
    {delta : ℝ} (hdelta : 0 ≤ delta) (hδ : 3 * delta ≤ 1) :
    vectorFieldPreservesConvexSet (positiveRicciRatioCone delta)
      ricciEigenReactionVector := by
  apply vectorFieldPreservesConvexSet_of_segment (convex_positiveRicciRatioCone delta)
  intro v hv
  exact ⟨v + ricciEigenReactionVector v, add_mem_positiveRicciRatioCone hv
    (ricciEigenReactionVector_mem_positiveRicciRatioCone hdelta hδ hv), by simp⟩

/-- **Math.** The coordinate sum of the ordinary reaction is twice the
squared Ricci norm, as in the scalar-curvature reaction equation. -/
theorem ricciEigenScalar_reactionVector (v : Fin 3 → ℝ) :
    ricciEigenScalar (ricciEigenReactionVector v 0) (ricciEigenReactionVector v 1)
      (ricciEigenReactionVector v 2) = 2 * ricciEigenNormSq (v 0) (v 1) (v 2) := by
  change ricciEigenReaction (v 0) (v 1) (v 2) +
      ricciEigenReaction (v 1) (v 0) (v 2) +
      ricciEigenReaction (v 2) (v 0) (v 1) = _
  unfold ricciEigenNormSq ricciEigenReaction
  ring

/-- **Math.** A positive scalar curvature and positive ratio constant make
every Ricci coordinate strictly positive. -/
theorem positiveRicciRatioCone_coord_pos
    {delta : ℝ} (hdelta : 0 < delta) {v : Fin 3 → ℝ}
    (hv : v ∈ positiveRicciRatioCone delta)
    (hR : 0 < ricciEigenScalar (v 0) (v 1) (v 2)) (i : Fin 3) :
    0 < v i :=
  (mul_pos hdelta hR).trans_le (hv i).2

/-- **Math.** The quantitative cone supplies the Ricci pinching hypothesis
in Hamilton's weighted trace-free reaction estimate. -/
theorem positiveRicciPinching_weighted_reaction_nonpos_of_ratioCone
    {v : Fin 3 → ℝ} {delta epsilon : ℝ}
    (hv : v ∈ positiveRicciRatioCone delta) (hdelta : 0 ≤ delta)
    (h01 : v 1 ≤ v 0) (h12 : v 2 ≤ v 1)
    (hepsilon : epsilon ≤ 2 * delta ^ 2)
    (hR : 0 < ricciEigenScalar (v 0) (v 1) (v 2)) :
    2 * (epsilon * ricciEigenNormSq (v 0) (v 1) (v 2) *
      traceFreeRicciEigenNormSq (v 0) (v 1) (v 2) -
        hamiltonRicciQuartic (v 0) (v 1) (v 2)) /
      ricciEigenScalar (v 0) (v 1) (v 2) ^ (3 - epsilon) ≤ 0 :=
  positiveRicciPinching_weighted_reaction_nonpos h01 h12 (hv 2).1 hdelta
    (hv 2).2 hepsilon hR

end MorganTianLib

#print axioms MorganTianLib.ricciEigenReaction_pinching_nonneg
#print axioms MorganTianLib.ricciEigenReactionVector_preserves_positiveRicciRatioCone
#print axioms MorganTianLib.positiveRicciPinching_weighted_reaction_nonpos_of_ratioCone

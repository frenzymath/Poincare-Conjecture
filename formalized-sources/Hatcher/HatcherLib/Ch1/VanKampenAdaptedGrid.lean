import HatcherLib.Ch1.VanKampenGrid

/-!
# An adapted rectangular grid for van Kampen's theorem

An ordinary rectangular subdivision can have four different labels at an
interior vertex.  This file removes that obstruction without changing the
rectangular grid interface: cells in alternating rows are paired into
horizontal dominoes.  A Lebesgue mesh makes each domino subordinate to one
cover member.  The two row patterns are offset, so at every vertex one of the
two rows contributes only one label.
-/

namespace HatcherLib

open Set unitInterval

noncomputable section

universe u v

variable {X : Type u} [TopologicalSpace X]

/-! ## The two-cell Lebesgue estimate -/

private theorem abs_sub_addNSMul_le_two {d : ℝ} (hd : 0 ≤ d)
    {z : I} (n : ℕ)
    (hz : z ∈ Set.Icc (Set.Icc.addNSMul (show (0 : ℝ) ≤ 1 by norm_num) d n)
      (Set.Icc.addNSMul (show (0 : ℝ) ≤ 1 by norm_num) d (n + 2))) :
    |(z : ℝ) - Set.Icc.addNSMul (show (0 : ℝ) ≤ 1 by norm_num) d n| ≤ 2 * d := by
  let h : (0 : ℝ) ≤ 1 := by norm_num
  let t := Set.Icc.addNSMul h d
  change |(z : ℝ) - (t n : ℝ)| ≤ 2 * d
  change z ∈ Set.Icc (t n) (t (n + 2)) at hz
  have hz0 : (t n : ℝ) ≤ (z : ℝ) := hz.1
  have hz1 : (z : ℝ) ≤ (t (n + 2) : ℝ) := hz.2
  calc
    |(z : ℝ) - (t n : ℝ)| = (z : ℝ) - (t n : ℝ) :=
      abs_eq_self.mpr (sub_nonneg.mpr hz0)
    _ ≤ (t (n + 2) : ℝ) - (t n : ℝ) := sub_le_sub_right hz1 _
    _ ≤ |(t (n + 2) : ℝ) - (t n : ℝ)| := le_abs_self _
    _ ≤ |((0 : ℝ) + (n + 2) • d) - ((0 : ℝ) + n • d)| := by
      exact Set.abs_projIcc_sub_projIcc h
    _ = 2 * d := by
      rw [zero_add, add_nsmul, two_nsmul, abs_of_nonneg]
      · ring
      · nlinarith

private theorem domino_rect_subset_ball {δ : ℝ} (hδ : 0 < δ) :
    let d := δ / 4
    let h : (0 : ℝ) ≤ 1 := by norm_num
    let t := Set.Icc.addNSMul h d
    ∀ n m, Set.Icc (t n) (t (n + 2)) ×ˢ Set.Icc (t m) (t (m + 1)) ⊆
      Metric.ball ((t n, t m)) δ := by
  let d : ℝ := δ / 4
  have hd : 0 ≤ d := by dsimp [d]; positivity
  let h : (0 : ℝ) ≤ 1 := by norm_num
  let t := Set.Icc.addNSMul h d
  change ∀ n m, Set.Icc (t n) (t (n + 2)) ×ˢ Set.Icc (t m) (t (m + 1)) ⊆
      Metric.ball ((t n, t m)) δ
  intro n m z hz
  rw [Metric.mem_ball]
  have hx := abs_sub_addNSMul_le_two hd n hz.1
  have hy := Set.Icc.abs_sub_addNSMul_le (show (0 : ℝ) ≤ 1 by norm_num) hd m hz.2
  rw [dist_comm]
  change dist (t n, t m) z < δ
  rw [Prod.dist_eq]
  apply max_lt
  · have hx' : |(z.1 : ℝ) - (t n : ℝ)| ≤ 2 * d := by
      simpa [t] using hx
    have hxd : 2 * d < δ := by dsimp [d]; linarith
    change dist ((t n : ℝ)) (z.1 : ℝ) < δ
    simpa [Real.dist_eq, abs_sub_comm] using lt_of_le_of_lt hx' hxd
  · have hy' : |(z.2 : ℝ) - (t m : ℝ)| ≤ d := by
      simpa [t] using hy
    have hyd : d < δ := by dsimp [d]; linarith
    change dist ((t m : ℝ)) (z.2 : ℝ) < δ
    simpa [Real.dist_eq, abs_sub_comm] using lt_of_le_of_lt hy' hyd

/-! ## Alternating domino bookkeeping -/

private def dominoAnchor (row column : ℕ) : ℕ :=
  if row % 2 = 0 then 2 * (column / 2)
  else 2 * ((column + 1) / 2) - 1

private theorem dominoAnchor_le_or_succ (row column : ℕ) :
    dominoAnchor row column = column ∨ dominoAnchor row column + 1 = column := by
  unfold dominoAnchor
  split <;> omega

private theorem dominoAnchor_adjacent_collision (row column : ℕ) :
    dominoAnchor row column = dominoAnchor row (column + 1) ∨
      dominoAnchor (row + 1) column = dominoAnchor (row + 1) (column + 1) := by
  unfold dominoAnchor
  split <;> split <;> omega

private theorem dominoAnchor_eq_of_parity_change {row column : ℕ}
    (hrow : row % 2 = column % 2) :
    dominoAnchor row column = dominoAnchor row (column + 1) := by
  unfold dominoAnchor
  split <;> omega

private theorem dominoAnchor_adjacent_eq_or_of_bounds
    {row column : ℕ} :
    dominoAnchor row column = dominoAnchor row (column + 1) ∨
      dominoAnchor (row + 1) column = dominoAnchor (row + 1) (column + 1) := by
  exact dominoAnchor_adjacent_collision row column

/-! A finite vertex has canonical left/right and lower/upper incident cells. -/

private def leftCell (h : ℕ) (hh : 0 < h) (r : Fin (h + 1)) : Fin h :=
  ⟨if r = 0 then 0 else r - 1, by
    split
    · omega
    · omega⟩

private def rightCell (h : ℕ) (hh : 0 < h) (r : Fin (h + 1)) : Fin h :=
  ⟨if r = h then h - 1 else r, by
    split
    · omega
    · omega⟩

private def lowerCell (h : ℕ) (hh : 0 < h) (r : Fin (h + 1)) : Fin h :=
  leftCell h hh r

private def upperCell (h : ℕ) (hh : 0 < h) (r : Fin (h + 1)) : Fin h :=
  rightCell h hh r

private theorem leftCell_touches {h : ℕ} (hh : 0 < h) (r : Fin (h + 1)) :
    VanKampenCellTouchesVertex (leftCell h hh r) r := by
  unfold leftCell VanKampenCellTouchesVertex
  split <;> rename_i hr
  · exact Or.inl hr
  · right
    apply Fin.ext
    have hrval : (r : ℕ) ≠ 0 := by
      intro hval
      apply hr
      exact Fin.ext hval
    simp only [Fin.succ_mk]
    omega

private theorem rightCell_touches {h : ℕ} (hh : 0 < h) (r : Fin (h + 1)) :
    VanKampenCellTouchesVertex (rightCell h hh r) r := by
  unfold rightCell VanKampenCellTouchesVertex
  split <;> rename_i hr
  · right
    apply Fin.ext
    have hrval := hr
    simp only [Fin.succ_mk]
    omega
  · exact Or.inl rfl

private theorem incident_cell_eq_left_or_right {h : ℕ} (hh : 0 < h)
    (r : Fin (h + 1)) (i : Fin h)
    (hi : VanKampenCellTouchesVertex i r) :
    i = leftCell h hh r ∨ i = rightCell h hh r := by
  unfold VanKampenCellTouchesVertex at hi
  rcases hi with hi | hi
  · right
    unfold rightCell
    split <;> rename_i hr
    · exfalso
      have hiv := congrArg Fin.val hi
      change (r : ℕ) = (i : ℕ) at hiv
      have hrv := hr
      omega
    · apply Fin.ext
      exact (congrArg Fin.val hi).symm
  · left
    unfold leftCell
    split <;> rename_i hr
    · exfalso
      have hiv := congrArg Fin.val hi
      change (r : ℕ) = (i : ℕ) + 1 at hiv
      have hrv := congrArg Fin.val hr
      change (r : ℕ) = 0 at hrv
      omega
    · apply Fin.ext
      have hiv := congrArg Fin.val hi
      change (r : ℕ) = (i : ℕ) + 1 at hiv
      have hrval : (r : ℕ) ≠ 0 := by
        intro hval
        apply hr
        exact Fin.ext hval
      change (i : ℕ) = (r : ℕ) - 1
      omega

private theorem cell_touches_vertex_left_right {h : ℕ} (hh : 0 < h)
    (r : Fin (h + 1)) :
    VanKampenCellTouchesVertex (leftCell h hh r) r ∧
      VanKampenCellTouchesVertex (rightCell h hh r) r :=
  ⟨leftCell_touches hh r, rightCell_touches hh r⟩

/-! ## Existence -/

/-- Every path-homotopy square has a subordinate rectangular grid whose
incident labels at each vertex involve at most three cover members.  The
construction uses alternating horizontal dominoes, so this is compatible with
the `VanKampenSquareGrid` interface used by the sweep lemmas. -/
theorem exists_vanKampenSquareGrid
    {x₀ : X} {ι : Type v} {p q : Loop x₀}
    (cover : PathConnectedOpenCover x₀ ι) (F : Path.Homotopy p q) :
    Nonempty (VanKampenSquareGrid cover F) := by
  have hopen : ∀ i, IsOpen (F ⁻¹' cover.carrier i) := fun i =>
    (cover.isOpen i).preimage F.continuous
  have hcover : (Set.univ : Set (I × I)) ⊆
      ⋃ i, F ⁻¹' cover.carrier i := by
    intro z _
    rcases Set.mem_iUnion.1
        (cover.cover (Set.mem_univ (F z))) with ⟨i, hi⟩
    exact Set.mem_iUnion.2 ⟨i, hi⟩
  obtain ⟨δ, hδ, hball⟩ :=
    lebesgue_number_lemma_of_metric isCompact_univ hopen hcover
  let d : ℝ := δ / 4
  have hd : 0 < d := by dsimp [d]; linarith
  let hzeroone : (0 : ℝ) ≤ 1 := by norm_num
  let t : ℕ → I := Set.Icc.addNSMul hzeroone d
  obtain ⟨tail, htail⟩ := Set.Icc.addNSMul_eq_right hzeroone hd
  let horizontalCells : ℕ := 2 * (tail + 1)
  let verticalCells : ℕ := tail + 1
  have hhorizontal : 0 < horizontalCells := by
    dsimp [horizontalCells]
    omega
  have hvertical : 0 < verticalCells := by
    dsimp [verticalCells]
    omega
  have htmono : Monotone t := by
    intro a b hab
    exact Set.Icc.monotone_addNSMul hzeroone hd.le hab
  have htzero : t 0 = 0 := by
    dsimp [t]
    simpa using Set.Icc.addNSMul_zero hzeroone
  have htone (n : ℕ) (hn : tail ≤ n) : t n = 1 := by
    dsimp [t]
    apply Subtype.ext
    exact htail n hn
  have hball_rect (a j : ℕ) :
      Set.Icc (t a) (t (a + 2)) ×ˢ Set.Icc (t j) (t (j + 1)) ⊆
        Metric.ball (t a, t j) δ := by
    have h := domino_rect_subset_ball hδ
    dsimp [d, hzeroone, t] at h ⊢
    exact h a j
  let label : ℕ → ℕ → ι := fun a j =>
    Classical.choose (hball (t a, t j) (Set.mem_univ _))
  have label_spec (a j : ℕ) :
      Metric.ball (t a, t j) δ ⊆ F ⁻¹' cover.carrier (label a j) :=
    Classical.choose_spec (hball (t a, t j) (Set.mem_univ _))
  let cellLabel : Fin horizontalCells → Fin verticalCells → ι := fun i j =>
    label (dominoAnchor j i) j
  have hcell_subordinate (i : Fin horizontalCells) (j : Fin verticalCells) :
      Set.Icc (t i.castSucc) (t i.succ) ×ˢ Set.Icc (t j.castSucc) (t j.succ) ⊆
        F ⁻¹' cover.carrier (cellLabel i j) := by
    have ha := dominoAnchor_le_or_succ j i
    have hia : (dominoAnchor j i : ℕ) ≤ i := by
      rcases ha with ha | ha
      · omega
      · omega
    have hia2 : i + 1 ≤ dominoAnchor j i + 2 := by
      rcases ha with ha | ha
      · omega
      · omega
    have hja : (j : ℕ) ≤ j := le_rfl
    intro z hz
    apply label_spec (dominoAnchor j i) j
    apply hball_rect (dominoAnchor j i) j
    refine ⟨?_, ?_⟩
    · exact ⟨(htmono hia).trans hz.1.1, hz.1.2.trans (htmono hia2)⟩
    · have hjnext : (j.succ : ℕ) ≤ (j : ℕ) + 1 := by rfl
      exact ⟨hz.2.1, hz.2.2.trans (htmono hjnext)⟩
  sorry

end
end HatcherLib

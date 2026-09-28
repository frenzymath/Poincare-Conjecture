import HatcherLib.Ch0.CellComplexes
import HatcherLib.Ch0.CWSubcomplexRelative
import HatcherLib.Ch0.CWCharacteristicQuotient

/-!
# Chapter 0 - CW structures on quotients by subcomplexes

This file constructs the classical CW structure on the quotient obtained by
collapsing a subcomplex to a point.
-/

namespace HatcherLib

open Metric Set Function
open Topology

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]

namespace CWQuotientStructure

variable {C : Set X} [CWComplex C] (E : CWComplex.Subcomplex C)

omit [T2Space X] in
private theorem collapseMk_injectiveOn_compl :
    Set.InjOn (collapseMk (E : Set X)) (E : Set X)ᶜ := by
  intro x hx y hy hxy
  have hrel : (collapseSetoid (E : Set X)).r x y := Quotient.exact hxy
  rcases hrel with h | h
  · exact h
  · exact False.elim (hx h.1)

omit [T2Space X] in
private theorem collapseMk_preimage_image_compl {U : Set X}
    (hU : U ⊆ (E : Set X)ᶜ) :
    collapseMk (E : Set X) ⁻¹' (collapseMk (E : Set X) '' U) = U := by
  apply Set.Subset.antisymm
  · rintro x ⟨y, hyU, hxy⟩
    have hrel : (collapseSetoid (E : Set X)).r x y := Quotient.exact hxy.symm
    rcases hrel with h | h
    · simpa [h] using hyU
    · exact False.elim (hU hyU h.2)
  · exact Set.subset_preimage_image _ _

omit [T2Space X] in
private theorem isOpenEmbedding_collapseMk_compl :
    IsOpenEmbedding (fun x : ↥((E : Set X)ᶜ) => collapseMk (E : Set X) x.1) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact (collapseMk (E : Set X)).continuous.comp continuous_subtype_val
  · intro x y hxy
    exact Subtype.ext (collapseMk_injectiveOn_compl E x.2 y.2 hxy)
  · intro U hU
    have hEval : IsOpen (((↑) : ↥((E : Set X)ᶜ) → X) '' U) :=
      E.closed.isOpen_compl.isOpenEmbedding_subtypeVal.isOpenMap U hU
    have hopen : IsOpen (collapseMk (E : Set X) ''
        (((↑) : ↥((E : Set X)ᶜ) → X) '' U)) := by
      apply (isQuotientMap_quotient_mk' (s := collapseSetoid (E : Set X))).isCoinducing
        |>.isOpen_preimage.mp
      have hpre : collapseMk (E : Set X) ⁻¹' (collapseMk (E : Set X) ''
          (((↑) : ↥((E : Set X)ᶜ) → X) '' U)) =
          ((↑) : ↥((E : Set X)ᶜ) → X) '' U := by
        apply collapseMk_preimage_image_compl E
        rintro _ ⟨x, hx, rfl⟩
        exact x.2
      simpa only [collapseMk] using hpre.symm ▸ hEval
    simpa only [Set.image_image, Function.comp_def] using hopen

private noncomputable def collapseAwayHomeomorph :
    ↥((E : Set X)ᶜ) ≃ₜ Set.range (fun x : ↥((E : Set X)ᶜ) =>
      collapseMk (E : Set X) x.1) :=
  (isOpenEmbedding_collapseMk_compl E).isEmbedding.toHomeomorph

omit [T2Space X] in
private theorem collapseAwayHomeomorph_apply (x : ↥((E : Set X)ᶜ)) :
    collapseAwayHomeomorph E x = ⟨collapseMk (E : Set X) x.1, ⟨x, rfl⟩⟩ := by
  rfl

omit [T2Space X] in
private theorem inherited_map_injective {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    Set.InjOn (fun z : Fin n → ℝ =>
      collapseMk (E : Set X) (Topology.CWComplex.map (C := C) n i.1 z))
      (Metric.ball 0 1) := by
  intro x hx y hy hxy
  apply (Topology.CWComplex.map (C := C) n i.1).injOn
  · exact (Topology.CWComplex.source_eq (C := C) n i.1).symm ▸ hx
  · exact (Topology.CWComplex.source_eq (C := C) n i.1).symm ▸ hy
  apply collapseMk_injectiveOn_compl E
  · intro hm
    exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
      ⟨x, hx, rfl⟩ hm
  · intro hm
    exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
      ⟨y, hy, rfl⟩ hm
  exact hxy

private noncomputable def inheritedMap {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    PartialEquiv (Fin n → ℝ) (collapseQuotient (E : Set X)) :=
  (inherited_map_injective E i).toPartialEquiv
    (fun z => collapseMk (E : Set X) (Topology.CWComplex.map (C := C) n i.1 z))
    (Metric.ball 0 1)

omit [T2Space X] in
private theorem inheritedMap_source {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    (inheritedMap E i).source = Metric.ball 0 1 :=
  rfl

omit [T2Space X] in
private theorem inheritedMap_apply {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n})
    (z : Fin n → ℝ) :
    inheritedMap E i z = collapseMk (E : Set X)
      (Topology.CWComplex.map (C := C) n i.1 z) :=
  rfl

omit [T2Space X] in
private theorem inheritedMap_continuousOn {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    ContinuousOn (inheritedMap E i) (Metric.closedBall 0 1) := by
  change ContinuousOn (fun z => collapseMk (E : Set X)
    (Topology.CWComplex.map (C := C) n i.1 z)) (Metric.closedBall 0 1)
  exact (collapseMk (E : Set X)).continuous.comp_continuousOn
    (Topology.CWComplex.continuousOn (C := C) n i.1)

omit [T2Space X] in
private theorem inheritedMap_target_subset_range {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    (inheritedMap E i).target ⊆
      Set.range (fun x : ↥((E : Set X)ᶜ) => collapseMk (E : Set X) x.1) := by
  rintro z ⟨x, hx, rfl⟩
  let y : ↥((E : Set X)ᶜ) :=
    ⟨Topology.CWComplex.map (C := C) n i.1 x, by
      intro hm
      exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
        ⟨x, hx, rfl⟩ hm⟩
  exact ⟨y, rfl⟩

omit [T2Space X] in
private theorem collapseAwayHomeomorph_symm_inherited {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n})
    (x : Fin n → ℝ) (hx : x ∈ Metric.ball (0 : Fin n → ℝ) 1) :
    (collapseAwayHomeomorph E).symm
        ⟨collapseMk (E : Set X) (Topology.CWComplex.map (C := C) n i.1 x),
          inheritedMap_target_subset_range E i ⟨x, hx, rfl⟩⟩ =
      ⟨Topology.CWComplex.map (C := C) n i.1 x, by
        intro hm
        exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
          ⟨x, hx, rfl⟩ hm⟩ := by
  apply (collapseAwayHomeomorph E).injective
  simp only [Homeomorph.apply_symm_apply, collapseAwayHomeomorph_apply]

omit [T2Space X] in
private theorem inheritedMap_continuousOn_symm {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    ContinuousOn (inheritedMap E i).symm (inheritedMap E i).target := by
  rw [continuousOn_iff_continuous_restrict]
  let lift : ↥((inheritedMap E i).target) →
      Set.range (fun x : ↥((E : Set X)ᶜ) => collapseMk (E : Set X) x.1) :=
    fun z => ⟨z.1, inheritedMap_target_subset_range E i z.2⟩
  let inverse : ↥((inheritedMap E i).target) → (Fin n → ℝ) := fun z =>
    (Topology.CWComplex.map (C := C) n i.1).symm
      ((collapseAwayHomeomorph E).symm (lift z) : X)
  have hlift : Continuous lift :=
    continuous_subtype_val.subtype_mk (fun z => inheritedMap_target_subset_range E i z.2)
  have hinto : ∀ z : ↥((inheritedMap E i).target),
      ((collapseAwayHomeomorph E).symm (lift z) : X) ∈
        (Topology.CWComplex.map (C := C) n i.1).target := by
    intro z
    rcases z.2 with ⟨x, hx, hxz⟩
    have hz : z = ⟨inheritedMap E i x, ⟨x, hx, rfl⟩⟩ :=
      Subtype.ext (by simpa only [inheritedMap_apply] using hxz.symm)
    subst z
    simp only [lift, inheritedMap_apply]
    rw [collapseAwayHomeomorph_symm_inherited E i x hx]
    exact (Topology.CWComplex.map (C := C) n i.1).map_source
      ((Topology.CWComplex.source_eq (C := C) n i.1).symm ▸ hx)
  have hinverse : Continuous inverse := by
    exact (Topology.CWComplex.continuousOn_symm (C := C) n i.1).comp_continuous
      (continuous_subtype_val.comp ((collapseAwayHomeomorph E).symm.continuous.comp hlift)) hinto
  apply hinverse.congr
  intro z
  rcases z.2 with ⟨x, hx, hxz⟩
  have hz : z = ⟨inheritedMap E i x, ⟨x, hx, rfl⟩⟩ :=
    Subtype.ext (by simpa only [inheritedMap_apply] using hxz.symm)
  subst z
  change inverse ⟨inheritedMap E i x, _⟩ =
    (inheritedMap E i).symm (inheritedMap E i x)
  rw [(inheritedMap E i).left_inv (inheritedMap_source E i ▸ hx)]
  simp only [inverse, lift, inheritedMap_apply]
  rw [collapseAwayHomeomorph_symm_inherited E i x hx]
  exact (Topology.CWComplex.map (C := C) n i.1).left_inv
    ((Topology.CWComplex.source_eq (C := C) n i.1).symm ▸ hx)

private noncomputable def pointMap {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) :
    PartialEquiv (Fin n → ℝ) (collapseQuotient (E : Set X)) :=
  PartialEquiv.single 0
    (collapseMk (E : Set X) (Classical.choose h.down.2))

omit [T2Space X] in
private theorem pointMap_source {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) :
    (pointMap E h).source = Metric.ball 0 1 := by
  rcases h with ⟨rfl, hE⟩
  ext z
  simp only [pointMap, PartialEquiv.single_source, Set.mem_singleton_iff,
    Metric.mem_ball, dist_zero_right]
  constructor
  · rintro rfl
    norm_num
  · intro _
    exact Subsingleton.elim _ _

omit [T2Space X] in
private theorem pointMap_apply {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) (z : Fin n → ℝ) :
    pointMap E h z = collapseMk (E : Set X) (Classical.choose h.down.2) :=
  rfl

omit [T2Space X] in
private theorem pointMap_continuousOn {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) :
    ContinuousOn (pointMap E h) (Metric.closedBall 0 1) := by
  change ContinuousOn (fun _ : Fin n → ℝ =>
    collapseMk (E : Set X) (Classical.choose h.down.2)) (Metric.closedBall 0 1)
  exact continuous_const.continuousOn

omit [T2Space X] in
private theorem pointMap_continuousOn_symm {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) :
    ContinuousOn (pointMap E h).symm (pointMap E h).target := by
  change ContinuousOn (fun _ : collapseQuotient (E : Set X) =>
    (0 : Fin n → ℝ)) (pointMap E h).target
  exact continuous_const.continuousOn

private noncomputable def quotientMap (n : ℕ) :
    QuotientCWCellIndex C E n →
      PartialEquiv (Fin n → ℝ) (collapseQuotient (E : Set X))
  | .inl i => inheritedMap E i
  | .inr h => pointMap E h

omit [T2Space X] in
private theorem quotientMap_source (n : ℕ) (i : QuotientCWCellIndex C E n) :
    (quotientMap E n i).source = Metric.ball 0 1 := by
  rcases i with i | h
  · exact inheritedMap_source E i
  · exact pointMap_source E h

omit [T2Space X] in
private theorem quotientMap_continuousOn (n : ℕ) (i : QuotientCWCellIndex C E n) :
    ContinuousOn (quotientMap E n i) (Metric.closedBall 0 1) := by
  rcases i with i | h
  · exact inheritedMap_continuousOn E i
  · exact pointMap_continuousOn E h

omit [T2Space X] in
private theorem quotientMap_continuousOn_symm (n : ℕ)
    (i : QuotientCWCellIndex C E n) :
    ContinuousOn (quotientMap E n i).symm (quotientMap E n i).target := by
  rcases i with i | h
  · exact inheritedMap_continuousOn_symm E i
  · exact pointMap_continuousOn_symm E h

omit [T2Space X] in
private theorem quotientMap_image_ball_inherited {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    quotientMap E n (.inl i) '' Metric.ball 0 1 =
      collapseMk (E : Set X) ''
        Topology.CWComplex.openCell (C := C) n i.1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Topology.CWComplex.map (C := C) n i.1 x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

omit [T2Space X] in
private theorem quotientMap_image_closedBall_inherited {n : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n}) :
    quotientMap E n (.inl i) '' Metric.closedBall 0 1 =
      collapseMk (E : Set X) ''
        Topology.CWComplex.closedCell (C := C) n i.1 := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Topology.CWComplex.map (C := C) n i.1 x, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩

omit [T2Space X] in
private theorem quotientMap_image_ball_point {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) :
    quotientMap E n (.inr h) '' Metric.ball 0 1 =
      collapseMk (E : Set X) '' (E : Set X) := by
  rcases h with ⟨rfl, hE⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let a := Classical.choose hE
    have ha : a ∈ (E : Set X) := Classical.choose_spec hE
    exact ⟨a, ha, collapseMk_eq_of_mem ha ha⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨0, ?_, ?_⟩
    · exact Metric.mem_ball_self one_pos
    · exact collapseMk_eq_of_mem (Classical.choose_spec hE) ha

omit [T2Space X] in
private theorem quotientMap_image_closedBall_point {n : ℕ}
    (h : PLift (n = 0 ∧ (E : Set X).Nonempty)) :
    quotientMap E n (.inr h) '' Metric.closedBall 0 1 =
      collapseMk (E : Set X) '' (E : Set X) := by
  rcases h with ⟨rfl, hE⟩
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let a := Classical.choose hE
    have ha : a ∈ (E : Set X) := Classical.choose_spec hE
    exact ⟨a, ha, collapseMk_eq_of_mem ha ha⟩
  · rintro ⟨a, ha, rfl⟩
    refine ⟨0, Metric.mem_closedBall_self (by norm_num), ?_⟩
    exact collapseMk_eq_of_mem (Classical.choose_spec hE) ha

omit [T2Space X] in
open Classical in
private theorem collapseMk_preimage_image_eq {F : Set X} :
    collapseMk (E : Set X) ⁻¹' (collapseMk (E : Set X) '' F) =
      if (F ∩ (E : Set X)).Nonempty then F ∪ (E : Set X) else F := by
  classical
  by_cases hFE : (F ∩ (E : Set X)).Nonempty
  · rw [if_pos hFE]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hrel : (collapseSetoid (E : Set X)).r x y := Quotient.exact hxy.symm
      rcases hrel with h | h
      · exact Or.inl (h ▸ hy)
      · exact Or.inr h.1
    · intro hx
      rcases hx with hx | hx
      · exact ⟨x, hx, rfl⟩
      · obtain ⟨y, hyF, hyE⟩ := hFE
        exact ⟨y, hyF, collapseMk_eq_of_mem hyE hx⟩
  · rw [if_neg hFE]
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hrel : (collapseSetoid (E : Set X)).r x y := Quotient.exact hxy.symm
      rcases hrel with h | h
      · exact h ▸ hy
      · exact False.elim (hFE ⟨y, hy, h.2⟩)
    · intro hx
      exact ⟨x, hx, rfl⟩

omit [T2Space X] in
private theorem collapseMk_isClosed_image {F : Set X} (hF : IsClosed F) :
    IsClosed (collapseMk (E : Set X) '' F) := by
  have hpre := collapseMk_preimage_image_eq E (F := F)
  have hq : IsQuotientMap (collapseMk (E : Set X)) := by
    change IsQuotientMap (@Quotient.mk' X (collapseSetoid (E : Set X)))
    exact isQuotientMap_quotient_mk' (s := collapseSetoid (E : Set X))
  apply (Topology.isQuotientMap_iff_isClosed.mp hq).2 _ |>.mpr
  rw [hpre]
  split_ifs with hFE
  · exact hF.union E.closed
  · exact hF

omit [T2Space X] in
private theorem quotientMap_inherited_disjoint_point {n m : ℕ}
    (i : {i : Topology.CWComplex.cell C n // i ∉ E.I n})
    (h : PLift (m = 0 ∧ (E : Set X).Nonempty)) :
    Disjoint (quotientMap E n (.inl i) '' Metric.ball 0 1)
      (quotientMap E m (.inr h) '' Metric.ball 0 1) := by
  rw [quotientMap_image_ball_inherited E i, quotientMap_image_ball_point E h]
  refine Set.disjoint_left.2 ?_
  rintro z ⟨y, hyopen, hzy⟩ ⟨a, ha, hza⟩
  rcases hyopen with ⟨x, hx, rfl⟩
  have hrel : (collapseSetoid (E : Set X)).r
      (Topology.CWComplex.map (C := C) n i.1 x) a := Quotient.exact (hzy.trans hza.symm)
  rcases hrel with hrel | hrel
  · exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
      ⟨x, hx, rfl⟩ (hrel ▸ ha)
  · exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
      ⟨x, hx, rfl⟩ hrel.1

omit [T2Space X] in
private theorem quotientMap_pairwiseDisjoint :
    (Set.univ : Set (Σ n, QuotientCWCellIndex C E n)).PairwiseDisjoint
      (fun ni => quotientMap E ni.1 ni.2 '' Metric.ball 0 1) := by
  intro ⟨n, i⟩ _ ⟨m, j⟩ _ hne
  rcases i with i | i <;> rcases j with j | j
  · refine Set.disjoint_left.2 ?_
    rintro z ⟨x, hx, hzx⟩ ⟨y, hy, hzy⟩
    have hnotx : Topology.CWComplex.map (C := C) n i.1 x ∉ (E : Set X) := by
      exact (E.disjoint_openCell_subcomplex_of_not_mem i.2).notMem_of_mem_left
        ⟨x, hx, rfl⟩
    have hnoty : Topology.CWComplex.map (C := C) m j.1 y ∉ (E : Set X) := by
      exact (E.disjoint_openCell_subcomplex_of_not_mem j.2).notMem_of_mem_left
        ⟨y, hy, rfl⟩
    have hmap : Topology.CWComplex.map (C := C) n i.1 x =
        Topology.CWComplex.map (C := C) m j.1 y := by
      apply collapseMk_injectiveOn_compl E hnotx hnoty
      exact hzx.trans hzy.symm
    have hSigma : (⟨n, i.1⟩ : Sigma (Topology.CWComplex.cell C)) ≠
        ⟨m, j.1⟩ := by
      intro hSigma
      rcases Sigma.ext_iff.mp hSigma with ⟨hnm, hij⟩
      have hnm' : n = m := hnm
      subst m
      apply hne
      have hij' : i = j := Subtype.ext (eq_of_heq hij)
      cases hij'
      rfl
    have hd : Disjoint
        (Topology.CWComplex.openCell (C := C) n i.1)
        (Topology.CWComplex.openCell (C := C) m j.1) :=
      Topology.RelCWComplex.disjoint_openCell_of_ne (C := C)
        (i := i.1) (j := j.1) hSigma
    exact (Set.disjoint_left.1 hd)
      ⟨x, hx, rfl⟩ ⟨y, hy, hmap.symm⟩
  · exact quotientMap_inherited_disjoint_point E i j
  · exact (quotientMap_inherited_disjoint_point E j i).symm
  · exfalso
    rcases i with ⟨hi⟩
    rcases j with ⟨hj⟩
    have hnm : n = m := hi.1.trans hj.1.symm
    apply hne
    cases hnm
    apply Sigma.ext rfl
    exact heq_of_eq (congrArg Sum.inr (Subsingleton.elim _ _))

private noncomputable def quotientFiniteIndex
    (I : ∀ m, Finset {i : Topology.CWComplex.cell C m // i ∉ E.I m})
    (m : ℕ) : Finset (QuotientCWCellIndex C E m) := by
  classical
  exact (I m).image Sum.inl ∪
    if h : m = 0 ∧ (E : Set X).Nonempty then
      ({Sum.inr (PLift.up h)} : Finset (QuotientCWCellIndex C E m))
    else ∅

omit [T2Space X] in
private theorem quotientFiniteIndex_mem_inherited
    (I : ∀ m, Finset {i : Topology.CWComplex.cell C m // i ∉ E.I m})
    {m : ℕ} {i : {i : Topology.CWComplex.cell C m // i ∉ E.I m}}
    (hi : i ∈ I m) : Sum.inl i ∈ quotientFiniteIndex E I m := by
  classical
  simp [quotientFiniteIndex, hi]

omit [T2Space X] in
private theorem quotientFiniteIndex_mem_point
    (I : ∀ m, Finset {i : Topology.CWComplex.cell C m // i ∉ E.I m})
    {m : ℕ} (hm : m = 0 ∧ (E : Set X).Nonempty) :
    Sum.inr (PLift.up hm) ∈ quotientFiniteIndex E I m := by
  classical
  simp [quotientFiniteIndex, hm]

private theorem quotientMap_mapsTo {n : ℕ}
    (i : QuotientCWCellIndex C E n) :
    ∃ I : ∀ m, Finset (QuotientCWCellIndex C E m),
      MapsTo (quotientMap E n i) (Metric.sphere 0 1)
        (⋃ (m < n) (j ∈ I m), quotientMap E m j '' Metric.closedBall 0 1) := by
  classical
  rcases i with i | hpoint
  · letI : Topology.RelCWComplex C (E : Set X) :=
      CWSubcomplex.relativeCWComplex C E
    obtain ⟨I, hI⟩ :=
      @Topology.RelCWComplex.mapsTo X _ C (E : Set X) inferInstance n i
    refine ⟨quotientFiniteIndex E I, ?_⟩
    intro z hz
    have hz' : z ∈ Metric.sphere (0 : Fin n → ℝ) 1 := hz
    have hmap := hI hz'
    rcases hmap with hbase | hcells
    · have hEne : (E : Set X).Nonempty := ⟨_, hbase⟩
      have hn : n ≠ 0 := by
        intro hn
        subst n
        have hz0 : z = 0 := Subsingleton.elim _ _
        subst z
        norm_num at hz
      have hzero : (0 : ℕ) < n := Nat.pos_of_ne_zero hn
      let hp : PLift ((0 : ℕ) = 0 ∧ (E : Set X).Nonempty) :=
        PLift.up ⟨rfl, hEne⟩
      have hpfin : Sum.inr hp ∈ quotientFiniteIndex E I 0 :=
        quotientFiniteIndex_mem_point E I ⟨rfl, hEne⟩
      have hpointmem : collapseMk (E : Set X)
          (Topology.CWComplex.map (C := C) n i.1 z) ∈
          quotientMap E 0 (Sum.inr hp) '' Metric.closedBall 0 1 := by
        rw [quotientMap_image_closedBall_point E hp]
        exact ⟨_, hbase, rfl⟩
      refine mem_iUnion.2 ⟨0, ?_⟩
      refine mem_iUnion.2 ⟨hzero, ?_⟩
      refine mem_iUnion.2 ⟨Sum.inr hp, ?_⟩
      exact mem_iUnion.2 ⟨hpfin, hpointmem⟩
    · simp only [mem_iUnion, exists_prop] at hcells
      rcases hcells with ⟨m, hmn, j, hj, y, hy, hzy⟩
      have hjfin : Sum.inl j ∈ quotientFiniteIndex E I m :=
        quotientFiniteIndex_mem_inherited E I hj
      refine mem_iUnion.2 ⟨m, ?_⟩
      refine mem_iUnion.2 ⟨hmn, ?_⟩
      refine mem_iUnion.2 ⟨Sum.inl j, ?_⟩
      refine mem_iUnion.2 ⟨hjfin, ?_⟩
      refine ⟨y, hy, ?_⟩
      change collapseMk (E : Set X) (Topology.CWComplex.map (C := C) m j.1 y) =
        collapseMk (E : Set X) (Topology.CWComplex.map (C := C) n i.1 z)
      exact congrArg (collapseMk (E : Set X)) hzy
  · rcases hpoint with ⟨hn, hE⟩
    subst n
    refine ⟨fun _ => ∅, ?_⟩
    intro z hz
    have hz0 : z = 0 := Subsingleton.elim _ _
    subst z
    norm_num at hz

private theorem quotientMap_union_closedBall :
    (⋃ (n : ℕ) (i : QuotientCWCellIndex C E n),
      quotientMap E n i '' Metric.closedBall 0 1) =
      quotientCWCarrier C E := by
  ext z
  constructor
  · intro hz
    simp only [mem_iUnion] at hz
    rcases hz with ⟨n, i, hz⟩
    rcases i with i | hpoint
    · rw [quotientMap_image_closedBall_inherited E i] at hz
      rcases hz with ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨Topology.CWComplex.map (C := C) n i.1 x,
        Topology.CWComplex.closedCell_subset_complex (C := C) n i.1 ⟨x, hx, rfl⟩, rfl⟩
    · rw [quotientMap_image_closedBall_point E hpoint] at hz
      rcases hz with ⟨x, hx, rfl⟩
      exact ⟨x, E.subset_complex hx, rfl⟩
  · rintro ⟨x, hxC, rfl⟩
    letI : Topology.RelCWComplex C (E : Set X) :=
      CWSubcomplex.relativeCWComplex C E
    have hxU : x ∈ (E : Set X) ∪
        ⋃ (n : ℕ) (i : Topology.RelCWComplex.cell C n),
          Topology.RelCWComplex.closedCell n i := by
      rw [@Topology.RelCWComplex.union X _ C (E : Set X) inferInstance]
      exact hxC
    rcases hxU with hxE | hxcell
    · have hEne : (E : Set X).Nonempty := ⟨x, hxE⟩
      let hp : PLift ((0 : ℕ) = 0 ∧ (E : Set X).Nonempty) :=
        PLift.up ⟨rfl, hEne⟩
      refine mem_iUnion.2 ⟨0, ?_⟩
      refine mem_iUnion.2 ⟨Sum.inr hp, ?_⟩
      rw [quotientMap_image_closedBall_point E hp]
      exact ⟨x, hxE, rfl⟩
    · simp only [mem_iUnion] at hxcell
      rcases hxcell with ⟨n, i, hxcell⟩
      rcases hxcell with ⟨y, hy, rfl⟩
      refine mem_iUnion.2 ⟨n, ?_⟩
      refine mem_iUnion.2 ⟨Sum.inl i, ?_⟩
      rw [quotientMap_image_closedBall_inherited E i]
      exact ⟨Topology.CWComplex.map (C := C) n i.1 y, ⟨y, hy, rfl⟩, rfl⟩

private theorem quotient_closed_of_cell_intersections
    (A : Set (collapseQuotient (E : Set X)))
    (hAK : A ⊆ quotientCWCarrier C E)
    (hcell : ∀ n (i : QuotientCWCellIndex C E n),
      IsClosed (A ∩ quotientMap E n i '' Metric.closedBall 0 1)) :
    IsClosed A := by
  let B : Set X := collapseMk (E : Set X) ⁻¹' A
  have hBC : B ⊆ C := by
    intro x hx
    rcases hAK hx with ⟨y, hy, hxy⟩
    have hrel : (collapseSetoid (E : Set X)).r x y := Quotient.exact hxy.symm
    rcases hrel with h | h
    · exact h ▸ hy
    · exact E.subset_complex h.1
  have hBcell : ∀ n (j : Topology.CWComplex.cell C n),
      IsClosed (B ∩ Topology.CWComplex.closedCell (C := C) n j) := by
    intro n j
    by_cases hj : j ∈ E.I n
    · have hEcell : Topology.CWComplex.closedCell (C := C) n j ⊆ (E : Set X) :=
        E.closedCell_subset_of_mem hj
      have hEne : (E : Set X).Nonempty := by
        refine ⟨Topology.CWComplex.map (C := C) n j 0, hEcell ?_⟩
        exact Topology.CWComplex.map_zero_mem_closedCell (C := C) n j
      let a : X := Classical.choose hEne
      have haE : a ∈ (E : Set X) := Classical.choose_spec hEne
      by_cases haA : collapseMk (E : Set X) a ∈ A
      · have heq : B ∩ Topology.CWComplex.closedCell (C := C) n j =
            Topology.CWComplex.closedCell (C := C) n j := by
          ext x
          constructor
          · exact fun hx => hx.2
          · intro hx
            refine ⟨?_, hx⟩
            change collapseMk (E : Set X) x ∈ A
            rw [collapseMk_eq_of_mem (hEcell hx) haE]
            exact haA
        rw [heq]
        exact Topology.RelCWComplex.isClosed_closedCell (C := C) (n := n) (i := j)
      · have heq : B ∩ Topology.CWComplex.closedCell (C := C) n j = ∅ := by
          ext x
          constructor
          · intro hx
            exfalso
            apply haA
            rw [← collapseMk_eq_of_mem (hEcell hx.2) haE]
            exact hx.1
          · simp
        rw [heq]
        exact isClosed_empty
    · have hqcell := hcell n (.inl ⟨j, hj⟩)
      have hqpre : IsClosed
          (collapseMk (E : Set X) ⁻¹'
            (A ∩ quotientMap E n (.inl ⟨j, hj⟩) '' Metric.closedBall 0 1)) :=
        hqcell.preimage (collapseMk (E : Set X)).continuous
      have hclosed : IsClosed
          (Topology.CWComplex.closedCell (C := C) n j) :=
        Topology.RelCWComplex.isClosed_closedCell (C := C) (n := n) (i := j)
      have heq : B ∩ Topology.CWComplex.closedCell (C := C) n j =
          (collapseMk (E : Set X) ⁻¹'
            (A ∩ quotientMap E n (.inl ⟨j, hj⟩) '' Metric.closedBall 0 1)) ∩
            Topology.CWComplex.closedCell (C := C) n j := by
        ext x
        constructor
        · rintro ⟨hxB, hxcell⟩
          refine ⟨⟨hxB, ?_⟩, hxcell⟩
          rw [quotientMap_image_closedBall_inherited E ⟨j, hj⟩]
          exact ⟨x, hxcell, rfl⟩
        · rintro ⟨⟨hxB, -⟩, hxcell⟩
          exact ⟨hxB, hxcell⟩
      rw [heq]
      exact hqpre.inter hclosed
  have hBclosed : IsClosed B := by
    exact Topology.CWComplex.closed' (C := C) B hBC hBcell
  have hq : IsQuotientMap (collapseMk (E : Set X)) := by
    change IsQuotientMap (@Quotient.mk' X (collapseSetoid (E : Set X)))
    exact isQuotientMap_quotient_mk' (s := collapseSetoid (E : Set X))
  exact (Topology.isQuotientMap_iff_isClosed.mp hq).2 _ |>.mpr hBclosed

/-- The CW structure on the collapse quotient, with one extra zero-cell for
the collapsed subcomplex. -/
@[reducible]
noncomputable def quotientCWComplex :
    Topology.CWComplex (quotientCWCarrier C E) where
  cell := QuotientCWCellIndex C E
  map := quotientMap E
  source_eq := quotientMap_source E
  continuousOn := quotientMap_continuousOn E
  continuousOn_symm := quotientMap_continuousOn_symm E
  pairwiseDisjoint' := quotientMap_pairwiseDisjoint E
  mapsTo' := by
    intro n i
    exact quotientMap_mapsTo E i
  closed' := by
    intro A hAK hcell
    exact quotient_closed_of_cell_intersections E A hAK hcell
  union' := quotientMap_union_closedBall E

theorem quotientCWComplex_isQuotientCWStructure :
    letI : Topology.CWComplex (quotientCWCarrier C E) := quotientCWComplex E
    IsQuotientCWStructure C E := by
  letI : Topology.CWComplex (quotientCWCarrier C E) := quotientCWComplex E
  refine ⟨fun _ => Equiv.refl _, ?_, ?_⟩
  · intro n i
    rcases i with i | hpoint
    · exact quotientMap_image_ball_inherited E i
    · exact quotientMap_image_ball_point E hpoint
  · intro n i hi x hx
    exact rfl

end CWQuotientStructure

end HatcherLib

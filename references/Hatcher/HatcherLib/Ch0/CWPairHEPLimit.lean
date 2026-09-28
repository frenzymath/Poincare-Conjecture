import HatcherLib.Ch0.CWSkeletonHEPTower
import HatcherLib.Ch0.GlobalCharacteristicQuotient
import HatcherLib.Ch0.CellComplexes

/-!
# Chapter 0 — the weak-topology limit of the skeletal HEP construction

This file performs the limit step in the CW-pair argument.  Compatible
extensions on the finite relative skeleta are evaluated at a finite skeleton
chosen for each point.  The characteristic-cover quotient map then supplies
continuity of the resulting global homotopy.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap
open Set
open Topology

universe u

namespace CWSkeletonHEPLimit

variable {X Y : Type u} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C D : Set X} [RelCWComplex C D]

/-! ## A finite skeleton can be chosen for every point -/

noncomputable def stageWitness (x : ↥C) : ∃ n : Nat,
    x.1 ∈ (RelCWComplex.skeletonLT C n : Set X) := by
  have hx : x.1 ∈ ⋃ n : Nat, (RelCWComplex.skeletonLT C n : Set X) := by
    rw [RelCWComplex.iUnion_skeletonLT_eq_complex (C := C) (D := D)]
    exact x.2
  exact Set.mem_iUnion.mp hx

noncomputable def stageIndex (C : Set X) {D : Set X} [RelCWComplex C D]
    (x : ↥C) : Nat := by
  classical
  exact Nat.find (stageWitness (C := C) (D := D) x)

theorem stageIndex_mem (x : ↥C) :
    x.1 ∈ (RelCWComplex.skeletonLT C (stageIndex (C := C) (D := D) x) : Set X) :=
  by
    classical
    simpa [stageIndex] using Nat.find_spec (stageWitness (C := C) (D := D) x)

noncomputable def stagePoint (x : ↥C) :
    ↥(RelCWComplex.skeletonLT C (stageIndex (C := C) (D := D) x)) :=
  ⟨x.1, stageIndex_mem (C := C) (D := D) x⟩

@[simp]
theorem stagePoint_val (x : ↥C) :
    (stagePoint (C := C) (D := D) x : X) = x :=
  rfl

/-! ## A tower evaluated at the chosen finite stage -/

noncomputable def globalEval
    (φ : C(↥C, Y))
    (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0)
    (x : ↥C) (t : I) : Y :=
  (CWSkeletonHEPTower.tower C φ hstep initial
      (stageIndex (C := C) (D := D) x)).1
    (stagePoint (C := C) (D := D) x, t)

/-! A common later stage lets us compare two evaluations of the tower. -/

theorem globalEval_eq_stage
    (φ : C(↥C, Y))
    (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0)
    {n : Nat} (x : ↥(RelCWComplex.skeletonLT C n)) (t : I) :
    globalEval (C := C) (D := D) φ hstep initial
        ⟨x.1, (RelCWComplex.skeletonLT C n).subset_complex x.2⟩ t =
      (CWSkeletonHEPTower.tower C φ hstep initial n).1 (x, t) := by
  let xc : ↥C := ⟨x.1, (RelCWComplex.skeletonLT C n).subset_complex x.2⟩
  let k : Nat := stageIndex (C := C) (D := D) xc
  let N : Nat := max k n
  have hkN : k ≤ N := Nat.le_max_left _ _
  have hnN : n ≤ N := Nat.le_max_right _ _
  let xk : ↥(RelCWComplex.skeletonLT C k) := stagePoint (C := C) (D := D) xc
  have hxN : x.1 ∈ (RelCWComplex.skeletonLT C N : Set X) :=
    (RelCWComplex.skeletonLT_mono (show (n : ℕ∞) ≤ N by exact_mod_cast hnN)) x.2
  let xN : ↥(RelCWComplex.skeletonLT C N) := ⟨x.1, hxN⟩
  have hxkN :
      CWSkeletonHEPTower.stageInclOfLE C hkN xk = xN := by
    apply Subtype.ext
    rfl
  have hxnN :
      CWSkeletonHEPTower.stageInclOfLE C hnN x = xN := by
    apply Subtype.ext
    rfl
  have hleft := CWSkeletonHEPTower.tower_restrict_of_le C φ hstep initial hkN xk t
  have hright := CWSkeletonHEPTower.tower_restrict_of_le C φ hstep initial hnN x t
  change (CWSkeletonHEPTower.tower C φ hstep initial k).1 (xk, t) =
    (CWSkeletonHEPTower.tower C φ hstep initial n).1 (x, t)
  rw [← hleft, ← hright, hxkN, hxnN]

/-! The chosen stage is zero on the relative base. -/

theorem stageIndex_base (d : ↥D) :
    stageIndex (C := C) (D := D)
      ⟨d.1, RelCWComplex.base_subset_complex d.2⟩ = 0 := by
  classical
  apply Nat.eq_zero_of_le_zero
  have h0 : d.1 ∈ (RelCWComplex.skeletonLT C 0 : Set X) := by
    rw [RelCWComplex.skeletonLT_zero_eq_base]
    exact d.2
  simpa [stageIndex] using Nat.find_min' (stageWitness (C := C) (D := D)
    ⟨d.1, RelCWComplex.base_subset_complex d.2⟩) h0

/-! ## The initial stage and the characteristic-cover homotopy -/

/-- The canonical inclusion of the relative base in the complex. -/
def relativeBaseIncl (C D : Set X) [RelCWComplex C D] : C(↥D, ↥C) where
  toFun d := ⟨d.1, RelCWComplex.base_subset_complex d.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

omit [T2Space X] in
@[simp]
theorem relativeBaseIncl_apply (C D : Set X) [RelCWComplex C D] (d : ↥D) :
    relativeBaseIncl C D d = ⟨d.1, RelCWComplex.base_subset_complex d.2⟩ :=
  rfl

private def baseStageMap (C D : Set X) [RelCWComplex C D] :
    C(↥D, ↥(RelCWComplex.skeletonLT C 0)) where
  toFun d := ⟨d.1, by
    have hd : d.1 ∈ (RelCWComplex.skeletonLT C 0 : Set X) := by
      rw [RelCWComplex.skeletonLT_zero_eq_base]
      exact d.2
    exact hd⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun d => by
    have hd : d.1 ∈ (RelCWComplex.skeletonLT C 0 : Set X) := by
      rw [RelCWComplex.skeletonLT_zero_eq_base]
      exact d.2
    exact hd)

private def stageBaseMap (C D : Set X) [RelCWComplex C D] :
    C(↥(RelCWComplex.skeletonLT C 0), ↥D) where
  toFun x := ⟨x.1, by
    exact (congrArg (fun S : Set X => x.1 ∈ S)
      (RelCWComplex.skeletonLT_zero_eq_base (C := C) (D := D))).mp x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk (fun x => by
    exact (congrArg (fun S : Set X => x.1 ∈ S)
      (RelCWComplex.skeletonLT_zero_eq_base (C := C) (D := D))).mp x.2)

private theorem stageZero_mem_base (C D : Set X) [RelCWComplex C D]
    (x : ↥(RelCWComplex.skeletonLT C 0)) : x.1 ∈ D :=
  (congrArg (fun S : Set X => x.1 ∈ S)
    (RelCWComplex.skeletonLT_zero_eq_base (C := C) (D := D))).mp x.2

private def initialExtension
    (φ : C(↥C, Y)) (h : C(↥D × I, Y))
    (hcompat : ∀ d : ↥D, h (d, 0) = φ (relativeBaseIncl C D d)) :
    CWSkeletonHEPTower.StageExtension C φ 0 := by
  let H : C(↥(RelCWComplex.skeletonLT C 0) × I, Y) :=
    h.comp ((stageBaseMap C D).prodMap (ContinuousMap.id I))
  refine ⟨H, ?_⟩
  intro x
  have hx : stageBaseMap C D x =
      (⟨x.1, (show x.1 ∈ D by
        exact stageZero_mem_base C D x)⟩ : ↥D) := by
    apply Subtype.ext
    rfl
  change h (stageBaseMap C D x, 0) = φ (CWSkeletonHEPTower.stageInclComplex C 0 x)
  rw [hx]
  apply (hcompat (⟨x.1, (show x.1 ∈ D by
    exact stageZero_mem_base C D x)⟩ : ↥D)).trans
  congr 1

private def cellStageMap (C : Set X) [RelCWComplex C D] (n : Nat)
    (i : RelCWComplex.cell C n) :
    C(CellCoverBall n, ↥(RelCWComplex.skeletonLT C (n + 1))) where
  toFun z := ⟨RelCWComplex.map n i z,
    RelCWComplex.closedCell_subset_skeletonLT n i ⟨z, z.2, rfl⟩⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_restrict.mp
      (RelCWComplex.continuousOn n i)

@[simp]
private theorem cellStageMap_apply (C : Set X) [RelCWComplex C D] (n : Nat)
    (i : RelCWComplex.cell C n) (z : CellCoverBall n) :
    (cellStageMap C n i z : X) = RelCWComplex.map n i z :=
  rfl

private noncomputable def coverHomotopy
    (φ : C(↥C, Y)) (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0) :
    C((CellCover C D) × I, Y) := by
  let base : C(↥D × I, Y) :=
    (initial.1.comp ((baseStageMap C D).prodMap (ContinuousMap.id I)))
  let cellPart : C((Σ q : CellCoverIndex C D,
      CellCoverBall q.1) × I, Y) := by
    let G : C(Σ q : CellCoverIndex C D,
        CellCoverBall q.1 × I, Y) :=
      ⟨fun q =>
        (CWSkeletonHEPTower.tower C φ hstep initial (q.1.1 + 1)).1
          ((cellStageMap C q.1.1 q.1.2 q.2.1), q.2.2), by
        exact continuous_sigma (fun q : CellCoverIndex C D =>
          (map_continuous
            (CWSkeletonHEPTower.tower C φ hstep initial (q.1 + 1)).1).comp
            ((cellStageMap C q.1 q.2).prodMap (ContinuousMap.id _)).continuous)⟩
    let e : C((Σ q : CellCoverIndex C D, CellCoverBall q.1) × I,
        Σ q : CellCoverIndex C D, CellCoverBall q.1 × I) :=
      ⟨Homeomorph.sigmaProdDistrib, Homeomorph.sigmaProdDistrib.continuous⟩
    exact G.comp e
  let out : C((↥D ⊕ Σ q : CellCoverIndex C D,
      CellCoverBall q.1) × I, Y) :=
    ⟨fun p => p.1.elim (fun d => base (d, p.2))
      (fun q => cellPart (q, p.2)), by
      apply continuous_sumProd
      · exact map_continuous base
      · exact map_continuous cellPart⟩
  exact out

private theorem coverHomotopy_characteristicCover
    (φ : C(↥C, Y)) (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0)
    (q : CellCover C D) (t : I) :
    coverHomotopy (C := C) (D := D) φ hstep initial (q, t) =
      globalEval (C := C) (D := D) φ hstep initial
        (characteristicCover (C := C) (D := D) q) t := by
  cases q with
  | inl d =>
      let x : ↥(RelCWComplex.skeletonLT C 0) := baseStageMap C D d
      have h := globalEval_eq_stage (C := C) (D := D) φ hstep initial x t
      change initial.1 (((baseStageMap C D).prodMap (ContinuousMap.id I)) (d, t)) = _
      rw [ContinuousMap.prodMap_apply]
      exact h.symm
  | inr q =>
      let x : ↥(RelCWComplex.skeletonLT C (q.1.1 + 1)) :=
        cellStageMap C q.1.1 q.1.2 q.2
      have h := globalEval_eq_stage (C := C) (D := D) φ hstep initial x t
      simpa [coverHomotopy, x, cellStageMap, characteristicCover] using h.symm

private theorem continuous_globalEval
    (φ : C(↥C, Y)) (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0) :
    Continuous (fun p : ↥C × I =>
      globalEval (C := C) (D := D) φ hstep initial p.1 p.2) := by
  apply (isQuotientMap_characteristicCover (C := C) (D := D)).continuous_lift_prod_left
  let K := coverHomotopy (C := C) (D := D) φ hstep initial
  have hK : Continuous (fun p : CellCover C D × I =>
      globalEval (C := C) (D := D) φ hstep initial
        (characteristicCover (C := C) (D := D) p.1) p.2) := by
    exact (map_continuous K).congr (fun p => by
      simpa [K] using
        (coverHomotopy_characteristicCover (C := C) (D := D) φ hstep initial p.1 p.2))
  exact hK

private noncomputable def globalExtension
    (φ : C(↥C, Y)) (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0) : C(↥C × I, Y) :=
  ⟨fun p => globalEval (C := C) (D := D) φ hstep initial p.1 p.2,
    continuous_globalEval (C := C) (D := D) φ hstep initial⟩

private theorem globalExtension_zero
    (φ : C(↥C, Y)) (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0)
    (x : ↥C) :
    globalExtension (C := C) (D := D) φ hstep initial (x, 0) = φ x := by
  change globalEval (C := C) (D := D) φ hstep initial x 0 = φ x
  unfold globalEval
  rw [(CWSkeletonHEPTower.tower C φ hstep initial
      (stageIndex (C := C) (D := D) x)).2 (stagePoint (C := C) (D := D) x)]
  rfl

private theorem globalExtension_base
    (φ : C(↥C, Y)) (h : C(↥D × I, Y))
    (hcompat : ∀ d : ↥D, h (d, 0) = φ (relativeBaseIncl C D d))
    (hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n))
    (initial : CWSkeletonHEPTower.StageExtension C φ 0)
    (hinitial : initial = initialExtension (C := C) (D := D) φ h hcompat)
    (d : ↥D) (t : I) :
    globalExtension (C := C) (D := D) φ hstep initial
        (relativeBaseIncl C D d, t) = h (d, t) := by
  let initial0 : CWSkeletonHEPTower.StageExtension C φ 0 :=
    initialExtension (C := C) (D := D) φ h hcompat
  let x : ↥(RelCWComplex.skeletonLT C 0) := baseStageMap C D d
  have hx := globalEval_eq_stage (C := C) (D := D) φ hstep initial0 x t
  have hi : initial0.1 (x, t) = h (d, t) := by
    change h (stageBaseMap C D x, t) = h (d, t)
    congr 1
  have hgoal : globalExtension (C := C) (D := D) φ hstep initial0
      (relativeBaseIncl C D d, t) = h (d, t) := by
    change globalEval (C := C) (D := D) φ hstep initial0
        (relativeBaseIncl C D d) t = h (d, t)
    have heq : relativeBaseIncl C D d =
        ⟨x.1, (RelCWComplex.skeletonLT C 0).subset_complex x.2⟩ := by
      apply Subtype.ext
      rfl
    rw [heq, hx]
    exact hi
  simpa [hinitial] using hgoal

/-! ## The relative CW-pair HEP -/

theorem hasHEPMap_relativeBaseIncl (C D : Set X) [RelCWComplex C D] :
    HasHEPMap (relativeBaseIncl C D) := by
  intro Z _ φ h hcompat
  let hstep : ∀ n, HasHEPMap (CWSkeletonHEPTower.stageInclSucc C n) :=
    CWSkeletonHEPTower.hasHEPMap_stageInclSucc C
  let initial : CWSkeletonHEPTower.StageExtension C φ 0 :=
    initialExtension (C := C) (D := D) φ h hcompat
  let F : C(↥C × I, Z) := globalExtension (C := C) (D := D) φ hstep initial
  refine ⟨F, ?_, ?_⟩
  · exact globalExtension_zero (C := C) (D := D) φ hstep initial
  · intro d t
    exact globalExtension_base (C := C) (D := D) φ h hcompat hstep initial rfl d t

/-- A CW subcomplex of a CW complex has the homotopy extension property in
the ambient space.  This is Hatcher's CW-pair HEP theorem. -/
theorem IsCWPair.hasHEP {A : Set X} [CWComplex (Set.univ : Set X)]
    (hA : IsCWPair A) : HasHEP.{u, u} A := by
  obtain ⟨E, hEA⟩ := hA
  subst A
  letI : RelCWComplex (Set.univ : Set X) (E : Set X) :=
    CWSubcomplex.relativeCWComplex (Set.univ : Set X) E
  have hrel : HasHEPMap
      (relativeBaseIncl (Set.univ : Set X) (E : Set X)) :=
    hasHEPMap_relativeBaseIncl (Set.univ : Set X) (E : Set X)
  have hsub : HasHEPMap (subtypeIncl (E : Set X)) := by
    let eSource : ↥(E : Set X) ≃ₜ ↥(E : Set X) := Homeomorph.refl _
    let eTarget : ↥(Set.univ : Set X) ≃ₜ X := Homeomorph.Set.univ X
    have hcomm : ∀ a : ↥(E : Set X),
        eTarget (relativeBaseIncl (Set.univ : Set X) (E : Set X) a) =
          subtypeIncl (E : Set X) (eSource a) := by
      intro a
      rfl
    exact @HasHEPMap.congr_homeomorph
      (↥(E : Set X)) (↥(E : Set X)) (↥(Set.univ : Set X)) X
      _ _ _ _ eSource eTarget
      (relativeBaseIncl (Set.univ : Set X) (E : Set X))
      (subtypeIncl (E : Set X)) hcomm hrel
  apply (hasHEP_iff_hasHEPMap (X := X) (E : Set X)).2
  exact hsub

end CWSkeletonHEPLimit

end HatcherLib

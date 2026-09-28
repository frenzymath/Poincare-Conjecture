import HatcherLib.Ch0.CWSkeletonPushout

/-!
# Compatible homotopies along a relative CW skeleton tower

This file isolates the dependent-choice bookkeeping in the proof that a
relative CW complex has the homotopy extension property.  If every successor
skeleton inclusion has the map-form HEP, a homotopy on the zero skeleton can be
extended recursively to compatible homotopies on all finite skeleta.

The remaining limit-stage theorem uses the weak topology of the relative CW
complex to glue this tower over the whole complex.
-/

namespace HatcherLib

open scoped unitInterval
open ContinuousMap

universe u

namespace CWSkeletonHEPTower

open Topology

variable {X Y : Type u} [TopologicalSpace X] [T2Space X]
  [TopologicalSpace Y] {C D : Set X} [RelCWComplex C D]

/-- The inclusion of a finite relative skeleton into the ambient complex. -/
def stageInclComplex (C : Set X) [RelCWComplex C D] (n : Nat) :
    C(↥(Topology.RelCWComplex.skeletonLT C n), ↥C) where
  toFun x := ⟨x.1, (Topology.RelCWComplex.skeletonLT C n).subset_complex x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem stageInclComplex_apply (C : Set X) [RelCWComplex C D] (n : Nat)
    (x : ↥(Topology.RelCWComplex.skeletonLT C n)) :
    (stageInclComplex C n x : X) = x :=
  rfl

/-- The normalized inclusion from the `n`th stage to the `(n+1)`st stage. -/
def stageInclSucc (C : Set X) [RelCWComplex C D] (n : Nat) :
    C(↥(Topology.RelCWComplex.skeletonLT C n),
      ↥(Topology.RelCWComplex.skeletonLT C ((n + 1 : Nat) : ℕ∞))) where
  toFun x := ⟨x.1, Topology.RelCWComplex.skeletonLT_mono (by norm_num) x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem stageInclSucc_apply (C : Set X) [RelCWComplex C D] (n : Nat)
    (x : ↥(Topology.RelCWComplex.skeletonLT C n)) :
    (stageInclSucc C n x : X) = x :=
  rfl

/-- The canonical inclusion between any two ordered finite skeleta. -/
def stageInclOfLE (C : Set X) [RelCWComplex C D] {m n : Nat} (hmn : m ≤ n) :
    C(↥(Topology.RelCWComplex.skeletonLT C m),
      ↥(Topology.RelCWComplex.skeletonLT C n)) where
  toFun x := ⟨x.1, Topology.RelCWComplex.skeletonLT_mono (by exact_mod_cast hmn) x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem stageInclOfLE_apply (C : Set X) [RelCWComplex C D] {m n : Nat}
    (hmn : m ≤ n) (x : ↥(Topology.RelCWComplex.skeletonLT C m)) :
    (stageInclOfLE C hmn x : X) = x :=
  rfl

/-- A homotopy on one skeleton whose time-zero map is the restriction of
`phi : C -> Y`. -/
def StageExtension (C : Set X) [RelCWComplex C D] (phi : C(↥C, Y)) (n : Nat) :=
  { H : C(↥(Topology.RelCWComplex.skeletonLT C n) × I, Y) //
    ∀ x, H (x, 0) = phi (stageInclComplex C n x) }

/-- The restriction of the ambient time-zero map to one skeleton. -/
def stageMap (C : Set X) [RelCWComplex C D] (phi : C(↥C, Y)) (n : Nat) :
    C(↥(Topology.RelCWComplex.skeletonLT C n), Y) :=
  phi.comp (stageInclComplex C n)

/-- The HEP extension problem determined by one member of the tower. -/
noncomputable def nextStageWitness (C : Set X) [RelCWComplex C D]
    (phi : C(↥C, Y)) (n : Nat)
    (hstep : HasHEPMap (stageInclSucc C n))
    (previous : StageExtension C phi n) :
    ∃ F : C(↥(Topology.RelCWComplex.skeletonLT C ((n + 1 : Nat) : ℕ∞)) × I, Y),
      (∀ x, F (x, 0) = stageMap C phi (n + 1) x) ∧
        ∀ x t, F (stageInclSucc C n x, t) = previous.1 (x, t) := by
  apply hstep (stageMap C phi (n + 1)) previous.1
  intro x
  rw [previous.2 x]
  rfl

/-- Extend one stage of a compatible homotopy tower using the HEP of the next
skeleton inclusion. -/
noncomputable def nextStage (C : Set X) [RelCWComplex C D]
    (phi : C(↥C, Y)) (n : Nat)
    (hstep : HasHEPMap (stageInclSucc C n))
    (previous : StageExtension C phi n) : StageExtension C phi (n + 1) :=
  ⟨Classical.choose (nextStageWitness C phi n hstep previous),
    (Classical.choose_spec (nextStageWitness C phi n hstep previous)).1⟩

theorem nextStage_restrict (C : Set X) [RelCWComplex C D]
    (phi : C(↥C, Y)) (n : Nat)
    (hstep : HasHEPMap (stageInclSucc C n))
    (previous : StageExtension C phi n)
    (x : ↥(Topology.RelCWComplex.skeletonLT C n)) (t : I) :
    (nextStage C phi n hstep previous).1
        (stageInclSucc C n x, t) = previous.1 (x, t) :=
  (Classical.choose_spec (nextStageWitness C phi n hstep previous)).2 x t

/-- Starting from a homotopy on the zero skeleton, recursively choose compatible
extensions over every finite skeleton. -/
noncomputable def tower (C : Set X) [RelCWComplex C D]
    (phi : C(↥C, Y))
    (hstep : ∀ n, HasHEPMap (stageInclSucc C n))
    (initial : StageExtension C phi 0) : ∀ n, StageExtension C phi n
  | 0 => initial
  | n + 1 => nextStage C phi n (hstep n) (tower C phi hstep initial n)

/-- Consecutive members of the recursively chosen tower agree on the previous
skeleton, exactly as supplied by the HEP extension. -/
theorem tower_succ_restrict (C : Set X) [RelCWComplex C D]
    (phi : C(↥C, Y))
    (hstep : ∀ n, HasHEPMap (stageInclSucc C n))
    (initial : StageExtension C phi 0) (n : Nat)
    (x : ↥(Topology.RelCWComplex.skeletonLT C n)) (t : I) :
    (tower C phi hstep initial (n + 1)).1
        (stageInclSucc C n x, t) =
      (tower C phi hstep initial n).1 (x, t) := by
  change (nextStage C phi n (hstep n) (tower C phi hstep initial n)).1
      (stageInclSucc C n x, t) =
    (tower C phi hstep initial n).1 (x, t)
  exact nextStage_restrict C phi n (hstep n) (tower C phi hstep initial n) x t

/-- Every later member of the tower restricts to every earlier member. -/
theorem tower_restrict_of_le (C : Set X) [RelCWComplex C D]
    (phi : C(↥C, Y))
    (hstep : ∀ n, HasHEPMap (stageInclSucc C n))
    (initial : StageExtension C phi 0) {m n : Nat} (hmn : m ≤ n)
    (x : ↥(Topology.RelCWComplex.skeletonLT C m)) (t : I) :
    (tower C phi hstep initial n).1 (stageInclOfLE C hmn x, t) =
      (tower C phi hstep initial m).1 (x, t) := by
  induction n, hmn using Nat.le_induction with
  | base =>
      rfl
  | succ n hmn ih =>
      calc
        (tower C phi hstep initial (n + 1)).1
            (stageInclOfLE C (Nat.le.step hmn) x, t) =
          (tower C phi hstep initial (n + 1)).1
            (stageInclSucc C n (stageInclOfLE C hmn x), t) := by
              congr 2
        _ = (tower C phi hstep initial n).1 (stageInclOfLE C hmn x, t) :=
          tower_succ_restrict C phi hstep initial n (stageInclOfLE C hmn x) t
        _ = (tower C phi hstep initial m).1 (x, t) := ih

/-! ## The actual relative CW skeleton steps -/

/-- Every normalized successor-skeleton inclusion has the HEP.  The component
boundaries have the HEP by the explicit ball-boundary retraction; disjoint
unions and attachment preserve HEP, and the successor-skeleton homeomorphism
transports it to the classical relative CW skeleton. -/
theorem hasHEPMap_stageInclSucc (C : Set X) [RelCWComplex C D] (n : Nat) :
    HasHEPMap (stageInclSucc C n) := by
  have hold : HasHEPMap (CWSkeletonPushout.skeletonIncl C n) :=
    CWSkeletonPushout.hasHEPMap_skeletonIncl C n
  let eTarget :
      ↥(RelCWComplex.skeletonLT C ((n : ℕ∞) + 1)) ≃ₜ
        ↥(RelCWComplex.skeletonLT C ((n + 1 : Nat) : ℕ∞)) :=
    Homeomorph.setCongr (by norm_num)
  let eSource : ↥(RelCWComplex.skeletonLT C n) ≃ₜ
      ↥(RelCWComplex.skeletonLT C n) := Homeomorph.refl _
  have hcomm : ∀ x, eTarget (CWSkeletonPushout.skeletonIncl C n x) =
      stageInclSucc C n (eSource x) := by
    intro x
    apply Subtype.ext
    rfl
  exact @HasHEPMap.congr_homeomorph
    (↥(RelCWComplex.skeletonLT C n))
    (↥(RelCWComplex.skeletonLT C n))
    (↥(RelCWComplex.skeletonLT C ((n : ℕ∞) + 1)))
    (↥(RelCWComplex.skeletonLT C ((n + 1 : Nat) : ℕ∞)))
    _ _ _ _ eSource eTarget
    (CWSkeletonPushout.skeletonIncl C n) (stageInclSucc C n) hcomm hold

end CWSkeletonHEPTower

end HatcherLib

import Topping.ParabolicPDE.ParabolicHolder
import Topping.ParabolicPDE.VariableParabolicHolder
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Holder section spaces

This file turns the pointwise Holder estimates from `ParabolicHolder` into
complete metric spaces of bounded continuous sections.  The spaces are
subtypes of bounded continuous functions, so the closedness proofs are
genuine (they do not postulate a Schauder space).  A centered closed ball is
also packaged for use by later contraction arguments.
-/

namespace Topping
namespace ParabolicPDE

open Set
open scoped BoundedContinuousFunction NNReal ENNReal Topology

noncomputable section

/-! ## A spatial Holder section space -/

/-- Bounded continuous sections over a domain satisfying one Holder estimate. -/
def HolderSectionSet {X V : Type*} [TopologicalSpace X] [PseudoMetricSpace X]
    [PseudoMetricSpace V] (S : Set X) (C alpha : NNReal) : Set (S →ᵇ V) :=
  {u | HolderWith C alpha (fun x : S => u x)}

/-- The subtype of bounded continuous Holder sections on `S`. -/
abbrev HolderSectionSpace {X V : Type*} [TopologicalSpace X] [PseudoMetricSpace X]
    [PseudoMetricSpace V] (S : Set X) (C alpha : NNReal) :=
  {u : S →ᵇ V // u ∈ HolderSectionSet (X := X) (V := V) S C alpha}

/-- A fixed Holder constraint is closed in the uniform metric. -/
theorem isClosed_holderSectionSet {X V : Type*} [TopologicalSpace X]
    [PseudoMetricSpace X] [PseudoMetricSpace V]
    (S : Set X) (C alpha : NNReal) :
    IsClosed (HolderSectionSet (X := X) (V := V) S C alpha) := by
  rw [HolderSectionSet]
  simp only [HolderWith, Set.setOf_forall]
  refine isClosed_iInter (fun x : S => ?_)
  refine isClosed_iInter (fun y : S => ?_)
  exact isClosed_le
    ((continuous_eval_const x).edist (continuous_eval_const y))
    continuous_const

/- The closed subtype inherits completeness from the bounded-function space. -/
instance completeSpace_holderSectionSpace {X V : Type*} [TopologicalSpace X]
    [PseudoMetricSpace X] [MetricSpace V] [CompleteSpace V]
    (S : Set X) (C alpha : NNReal) :
    CompleteSpace (HolderSectionSpace (X := X) (V := V) S C alpha) := by
  letI : IsClosed (HolderSectionSet (X := X) (V := V) S C alpha) :=
    isClosed_holderSectionSet S C alpha
  exact IsClosed.completeSpace_coe

/-- Recover the Holder estimate carried by a spatial section. -/
theorem holderSectionSpace_mem {X V : Type*} [TopologicalSpace X]
    [PseudoMetricSpace X] [PseudoMetricSpace V]
    (S : Set X) (C alpha : NNReal)
    (u : HolderSectionSpace (X := X) (V := V) S C alpha) :
    HolderWith C alpha (fun x : S => u.1 x) := by
  change u.1 ∈ HolderSectionSet (X := X) (V := V) S C alpha
  exact u.2

/-! ## A parabolic Holder section space -/

/-- Separate spatial and temporal Holder constraints on a bounded section over
`S x J`.  The time set is represented by the subtype `J`, so the constraint
is the global (`univ`) version of `ParabolicHolderControl`. -/
def ParabolicHolderSectionSet {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal) :
    Set ((S × J) →ᵇ V) :=
  {u | ParabolicHolderControl (fun z : S × J => u z)
    (Set.univ : Set J) Cs alpha Ct beta}

/-- The complete-space candidate for a parabolic Holder scale. -/
abbrev ParabolicHolderSectionSpace {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal) :=
  {u : (S × J) →ᵇ V //
    u ∈ ParabolicHolderSectionSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta}

/-- The two pieces of a parabolic Holder constraint are closed separately,
because every inequality is a closed evaluation inequality. -/
theorem isClosed_parabolicHolderSectionSet {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal) :
    IsClosed (ParabolicHolderSectionSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta) := by
  have hset :
      ParabolicHolderSectionSet (X := X) (T := T) (V := V)
          S J Cs alpha Ct beta =
        {u : (S × J) →ᵇ V |
          forall t : J, HolderWith Cs alpha (fun x : S => u (x, t))} ∩
        {u : (S × J) →ᵇ V |
          forall x : S,
            HolderOnWith Ct beta (fun t : J => u (x, t))
              (Set.univ : Set J)} := by
    ext u
    change
      ParabolicHolderControl (fun z : S × J => u z)
          (Set.univ : Set J) Cs alpha Ct beta <-> _
    constructor
    · intro hu
      refine ⟨?_, ?_⟩
      · intro t
        simpa only [SpatialHolderWith] using hu.spatial t (by trivial)
      · intro x
        exact hu.temporal x
    · intro hu
      refine ⟨?_, ?_⟩
      · intro t ht
        simpa only [SpatialHolderWith] using hu.1 t
      · intro x
        exact hu.2 x
  rw [hset]
  apply IsClosed.inter
  · simp only [HolderWith, Set.setOf_forall]
    refine isClosed_iInter (fun t : J => ?_)
    refine isClosed_iInter (fun x : S => ?_)
    refine isClosed_iInter (fun y : S => ?_)
    exact isClosed_le
      ((continuous_eval_const (x, t)).edist
        (continuous_eval_const (y, t)))
      continuous_const
  · simp only [HolderOnWith, Set.setOf_forall, mem_univ, true_implies]
    refine isClosed_iInter (fun x : S => ?_)
    refine isClosed_iInter (fun s : J => ?_)
    refine isClosed_iInter (fun t : J => ?_)
    exact isClosed_le
      ((continuous_eval_const (x, s)).edist
        (continuous_eval_const (x, t)))
      continuous_const

/- The closed parabolic subtype is complete whenever the target is complete. -/
instance completeSpace_parabolicHolderSectionSpace {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [MetricSpace V] [CompleteSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal) :
    CompleteSpace (ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta) := by
  letI : IsClosed (ParabolicHolderSectionSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta) :=
    isClosed_parabolicHolderSectionSet S J Cs alpha Ct beta
  exact IsClosed.completeSpace_coe

/-- Recover the full parabolic Holder control carried by a section. -/
theorem parabolicHolderSectionSpace_mem {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta) :
    ParabolicHolderControl (fun z : S × J => u.1 z)
      (Set.univ : Set J) Cs alpha Ct beta := by
  change u.1 ∈ ParabolicHolderSectionSet (X := X) (T := T) (V := V)
    S J Cs alpha Ct beta
  exact u.2

/-- The spatial slice estimate exposed directly from a parabolic section. -/
theorem parabolicHolderSectionSpace_spatial_edist_le {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta)
    (t : J) (x y : S) :
    edist (u.1 (x, t)) (u.1 (y, t)) <=
      (Cs : ENNReal) * edist x y ^ (alpha : Real) := by
  simpa only [SpatialHolderWith] using
    (parabolicHolderSectionSpace_mem S J Cs alpha Ct beta u).spatial
      t (by trivial) x y

/-- The temporal trace estimate exposed directly from a parabolic section. -/
theorem parabolicHolderSectionSpace_temporal_edist_le {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta)
    (x : S) (s t : J) :
    edist (u.1 (x, s)) (u.1 (x, t)) <=
      (Ct : ENNReal) * edist s t ^ (beta : Real) :=
  (parabolicHolderSectionSpace_mem S J Cs alpha Ct beta u).temporal
    x s (by trivial) t (by trivial)

/-! ## Algebraic closure of the section subtype -/

/-- Scalar multiplication preserves the parabolic Holder section space, with
Holder constants scaled by the norm of the scalar. -/
def parabolicHolderSectionSpace_smul {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (c : ℝ)
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta) :
    ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J (‖c‖₊ * Cs) alpha (‖c‖₊ * Ct) beta := by
  refine ⟨c • u.1, ?_⟩
  change ParabolicHolderControl (fun z : S × J => c • u.1 z)
    (Set.univ : Set J) (‖c‖₊ * Cs) alpha (‖c‖₊ * Ct) beta
  simpa only [BoundedContinuousFunction.smul_apply] using
    (ParabolicHolderControl.smul c
      (parabolicHolderSectionSpace_mem S J Cs alpha Ct beta u))

/-- Addition preserves the parabolic Holder section space, with the spatial
and temporal constants added componentwise. -/
def parabolicHolderSectionSpace_add {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [NormedAddCommGroup V]
    (S : Set X) (J : Set T)
    (Cu alpha Cv beta Du Dv : NNReal)
    (u : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Cu alpha Cv beta)
    (v : ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J Du alpha Dv beta) :
    ParabolicHolderSectionSpace (X := X) (T := T) (V := V)
      S J (Cu + Du) alpha (Cv + Dv) beta := by
  refine ⟨u.1 + v.1, ?_⟩
  change ParabolicHolderControl (fun z : S × J => u.1 z + v.1 z)
    (Set.univ : Set J) (Cu + Du) alpha (Cv + Dv) beta
  simpa only [BoundedContinuousFunction.add_apply] using
    (ParabolicHolderControl.add
      (parabolicHolderSectionSpace_mem S J Cu alpha Cv beta u)
      (parabolicHolderSectionSpace_mem S J Du alpha Dv beta v))

/-! ## Complete Holder balls -/

/-- A Holder section space intersected with a closed uniform ball. -/
def ParabolicHolderSectionBallSet {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real) : Set ((S × J) →ᵇ V) :=
  ParabolicHolderSectionSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta ∩ Metric.closedBall center radius

/-- The subtype used as a closed Holder ball for a parabolic iteration. -/
abbrev ParabolicHolderSectionBall {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real) :=
  {u : (S × J) →ᵇ V //
    u ∈ ParabolicHolderSectionBallSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius}

/-- The parabolic Holder ball is closed in the bounded-section metric. -/
theorem isClosed_parabolicHolderSectionBallSet {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real) :
    IsClosed (ParabolicHolderSectionBallSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius) :=
  (isClosed_parabolicHolderSectionSet S J Cs alpha Ct beta).inter
    Metric.isClosed_closedBall

/- The ball inherits completeness from the target metric space. -/
instance completeSpace_parabolicHolderSectionBall {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [MetricSpace V] [CompleteSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real) :
    CompleteSpace (ParabolicHolderSectionBall (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius) := by
  letI : IsClosed (ParabolicHolderSectionBallSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius) :=
    isClosed_parabolicHolderSectionBallSet S J Cs alpha Ct beta center radius
  exact IsClosed.completeSpace_coe

/-- A section in the parabolic Holder ball retains its Holder control. -/
theorem parabolicHolderSectionBall_mem {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real)
    (u : ParabolicHolderSectionBall (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius) :
    ParabolicHolderControl (fun z : S × J => u.1 z)
      (Set.univ : Set J) Cs alpha Ct beta :=
  u.2.1

/-- The uniform distance from a ball element to its center is bounded by the
ball radius. -/
theorem parabolicHolderSectionBall_dist_center_le {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real)
    (u : ParabolicHolderSectionBall (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius) :
    dist u.1 center <= radius :=
  Metric.mem_closedBall.mp u.2.2

/-- Pointwise evaluation inherits the uniform ball bound. -/
theorem parabolicHolderSectionBall_eval_dist_center_le {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real)
    (u : ParabolicHolderSectionBall (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius) (z : S × J) :
    dist (u.1 z) (center z) <= radius :=
  (BoundedContinuousFunction.dist_coe_le_dist z).trans
    (parabolicHolderSectionBall_dist_center_le S J Cs alpha Ct beta center radius u)

/-- The center belongs to its Holder ball when it satisfies the Holder
constraint and the radius is nonnegative. -/
theorem parabolicHolderSectionBall_center_mem {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [PseudoMetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V) (radius : Real)
    (hcenter : center ∈ ParabolicHolderSectionSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta) (hradius : 0 <= radius) :
    center ∈ ParabolicHolderSectionBallSet (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center radius := by
  exact ⟨hcenter, by rw [Metric.mem_closedBall, dist_self]; exact hradius⟩

/-- A zero-radius Holder ball contains only its center (under a genuine
metric on the target). -/
theorem parabolicHolderSectionBall_eq_center_of_radius_eq_zero {X T V : Type*}
    [TopologicalSpace X] [PseudoMetricSpace X]
    [TopologicalSpace T] [PseudoMetricSpace T]
    [MetricSpace V]
    (S : Set X) (J : Set T) (Cs alpha Ct beta : NNReal)
    (center : (S × J) →ᵇ V)
    (u : ParabolicHolderSectionBall (X := X) (T := T) (V := V)
      S J Cs alpha Ct beta center 0) :
    u.1 = center := by
  apply dist_eq_zero.mp
  exact le_antisymm
    (parabolicHolderSectionBall_dist_center_le S J Cs alpha Ct beta center 0 u)
    dist_nonneg

#print axioms isClosed_holderSectionSet
#print axioms isClosed_parabolicHolderSectionSet
#print axioms completeSpace_parabolicHolderSectionSpace
#print axioms parabolicHolderSectionBall_eq_center_of_radius_eq_zero

end
end ParabolicPDE
end Topping

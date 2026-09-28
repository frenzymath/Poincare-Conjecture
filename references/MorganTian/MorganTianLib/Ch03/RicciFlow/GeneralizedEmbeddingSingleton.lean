import MorganTianLib.Ch03.RicciFlow.GeneralizedEmbedding

/-!
# Morgan--Tian Ch. 3 - singleton flow-line restrictions and domains

The source defines a flow line as the singleton case of a compatible
time-slice embedding.  This file records the restriction from a compatible
embedding to each of its singleton spatial fibres, and the resulting union of
open, preconnected singleton intervals.  The latter is an honest admissible
interval domain; the global gluing and maximality argument is deliberately left
as a later input.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

/-- Restrict a compatible time-slice embedding to one spatial fibre. -/
def GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.restrictSingleton
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t J) {x : N} (hx : x ∈ C) :
    S.FlowLine n x t J := by
  have hsub : ({x} : Set N) ×ˢ J ⊆ C ×ˢ J := by
    rintro ⟨y, s⟩ ⟨hy, hs⟩
    have hyx : y = x := by simpa using hy
    subst y
    exact ⟨hx, hs⟩
  let incl : ({x} : Set N) ×ˢ J → C ×ˢ J := Set.inclusion hsub
  let hincl : Topology.IsEmbedding incl := Topology.IsEmbedding.inclusion hsub
  have hemb :
      Topology.IsEmbedding (Set.restrict (({x} : Set N) ×ˢ J) e.toFun) := by
    have hcomp := e.toCompatibleEmbedding.isEmbedding.comp hincl
    convert hcomp using 1
    funext z
    rfl
  refine
    { toCompatibleEmbedding :=
        { toFun := e.toFun
          isEmbedding := hemb
          time_eq := ?_
          isIntegralCurveOn := ?_ }
      center_mem := e.center_mem
      source_subset := ?_
      center_eq := ?_ }
  · intro z hz
    exact e.toCompatibleEmbedding.time_eq z (hsub hz)
  · intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact e.toCompatibleEmbedding.isIntegralCurveOn x hx
  · intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact e.source_subset hx
  · intro y hy
    have hyx : y = x := by simpa using hy
    subst y
    exact e.center_eq x hx

/-! A witness used to index the admissible domain. -/
def GeneralizedSpaceTime.FlowLineDomainWitness
    (S : GeneralizedSpaceTime n (N := N)) (x : N) (t : ℝ) : Type :=
  {J : Set ℝ // IsOpen J ∧ IsPreconnected J ∧ t ∈ J ∧
    Nonempty (S.FlowLine n x t J)}

/- The union of all open, preconnected intervals carrying a singleton flow
line. -/
def GeneralizedSpaceTime.flowLineDomain
    (S : GeneralizedSpaceTime n (N := N)) (x : N) (t : ℝ) : Set ℝ :=
  ⋃ w : S.FlowLineDomainWitness n x t, (w.1 : Set ℝ)

/-- Any open singleton flow-line interval is contained in the admissible
domain. -/
theorem GeneralizedSpaceTime.flowLineDomain_subset_of_witness
    {S : GeneralizedSpaceTime n (N := N)} {x : N} {t : ℝ} {J : Set ℝ}
    (e : S.FlowLine n x t J) (hJ : IsOpen J) (hJpre : IsPreconnected J)
    (ht : t ∈ J) :
    J ⊆ S.flowLineDomain n x t := by
  let w : S.FlowLineDomainWitness n x t := ⟨J, hJ, hJpre, ht, ⟨e⟩⟩
  intro s hs
  exact mem_iUnion.2 ⟨w, hs⟩

/-- The admissible singleton flow-line domain is open. -/
theorem GeneralizedSpaceTime.isOpen_flowLineDomain
    {S : GeneralizedSpaceTime n (N := N)} (x : N) (t : ℝ) :
    IsOpen (S.flowLineDomain n x t) := by
  exact isOpen_iUnion fun w => w.2.1

/-- The admissible singleton flow-line domain is preconnected, since all
witness intervals contain the same central time. -/
theorem GeneralizedSpaceTime.isPreconnected_flowLineDomain
    {S : GeneralizedSpaceTime n (N := N)} (x : N) (t : ℝ) :
    IsPreconnected (S.flowLineDomain n x t) := by
  apply IsPreconnected.iUnion_of_reflTransGen
  · intro w
    exact w.2.2.1
  · intro w v
    apply Relation.ReflTransGen.single
    exact ⟨t, w.2.2.2.1, v.2.2.2.1⟩

/-- Every witness interval contains the central time in the admissible domain. -/
theorem GeneralizedSpaceTime.mem_flowLineDomain_center
    {S : GeneralizedSpaceTime n (N := N)} {x : N} {t : ℝ} {J : Set ℝ}
    (e : S.FlowLine n x t J) (hJ : IsOpen J) (hJpre : IsPreconnected J)
    (ht : t ∈ J) :
    t ∈ S.flowLineDomain n x t :=
  S.flowLineDomain_subset_of_witness n e hJ hJpre ht ht

/-- Every time in the admissible singleton domain is an occurring
space-time time. -/
theorem GeneralizedSpaceTime.flowLineDomain_subset_timeRange
    {S : GeneralizedSpaceTime n (N := N)} {x : N} {t s : ℝ}
    (hs : s ∈ S.flowLineDomain n x t) : s ∈ Set.range S.time := by
  rcases mem_iUnion.1 hs with ⟨w, hsJ⟩
  rcases w.2.2.2.2 with ⟨e⟩
  refine ⟨e.toFun (x, s), ?_⟩
  exact e.toCompatibleEmbedding.time_toFun n (by simp) hsJ

/- The forward half of the source's pointwise-domain criterion. -/
theorem GeneralizedSpaceTime.CompatibleTimeSliceEmbedding.flowLineDomain_subset
    {S : GeneralizedSpaceTime n (N := N)} {C : Set N} {t : ℝ} {J : Set ℝ}
    (e : S.CompatibleTimeSliceEmbedding n C t J)
    (hJ : IsOpen J) (hJpre : IsPreconnected J) :
    ∀ x ∈ C, J ⊆ S.flowLineDomain n x t := by
  intro x hx
  exact S.flowLineDomain_subset_of_witness n
    (e.restrictSingleton n hx) hJ hJpre e.center_mem

end MorganTianLib

end

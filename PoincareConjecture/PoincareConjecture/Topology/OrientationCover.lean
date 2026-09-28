import Mathlib.Topology.VectorBundle.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Order
import Mathlib.Tactic

/-!
# Orienting a real vector bundle over a simply connected base

We construct the actual orientation double cover from the signs of the
determinants of the bundle's coordinate changes. Its covering property is a
consequence of the constructed local trivializations, not an assumption.
Lifting the identity of a simply connected base gives a continuous section.
In local coordinates this is a compatible choice of orientation signs.

The resulting signs turn every transition determinant positive. This is the
usual orientation criterion for a real vector bundle; the tangent-bundle
specialization gives the manifold orientability step in the Poincare proof.
-/

open Set Function Filter Topology
open scoped Topology

noncomputable section

namespace PoincareConjecture

/-- A negative determinant reverses the two choices of orientation. -/
def orientationChange (d : ℝ) (s : Bool) : Bool := if 0 < d then s else !s

theorem orientationChange_mul {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (s : Bool) :
    orientationChange (b * a) s = orientationChange b (orientationChange a s) := by
  rcases lt_or_gt_of_ne ha with ha | ha <;> rcases lt_or_gt_of_ne hb with hb | hb
  · simp [orientationChange, ha.not_gt, hb.not_gt, mul_pos_of_neg_of_neg hb ha]
  · simp [orientationChange, ha.not_gt, hb, (mul_neg_of_pos_of_neg hb ha).not_gt]
  · simp [orientationChange, ha, hb.not_gt, (mul_neg_of_neg_of_pos hb ha).not_gt]
  · simp [orientationChange, ha, hb, mul_pos hb ha]

/-- The scalar multiplying a frame when that local frame is reversed. -/
def orientationSign (s : Bool) : ℝ := if s then -1 else 1

theorem orientationChange_positive {d : ℝ} (hd : d ≠ 0) (s : Bool) :
    0 < orientationSign (orientationChange d s) * d * orientationSign s := by
  by_cases hpos : 0 < d
  · cases s <;> simp [orientationChange, orientationSign, hpos]
  · have hneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hd
    cases s <;> simp [orientationChange, orientationSign, hpos, hneg]

variable {B F ι : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (Z : VectorBundleCore ℝ B F ι)

theorem orientationDet_self (i : ι) {x : B} (hx : x ∈ Z.baseSet i) :
    (Z.coordChange i i x).det = 1 := by
  have he : Z.coordChange i i x = ContinuousLinearMap.id ℝ F := by
    ext v
    exact Z.coordChange_self i x hx v
  rw [he]
  exact LinearMap.det_id

theorem orientationDet_comp (i j k : ι) {x : B}
    (hx : x ∈ Z.baseSet i ∩ Z.baseSet j ∩ Z.baseSet k) :
    (Z.coordChange j k x).det * (Z.coordChange i j x).det = (Z.coordChange i k x).det := by
  rw [← LinearMap.det_comp]
  exact congrArg (fun f : F →L[ℝ] F => f.det) (Z.coordChange_linear_comp i j k x hx)

theorem orientationDet_ne_zero (i j : ι) {x : B} (hx : x ∈ Z.baseSet i ∩ Z.baseSet j) :
    (Z.coordChange i j x).det ≠ 0 := by
  have h := orientationDet_comp Z i j i ⟨hx, hx.1⟩
  rw [orientationDet_self Z i hx.1] at h
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

/-- The sign of a nonzero continuous determinant acts continuously on a
discrete two-point fibre over the overlap of two bundle charts. -/
theorem orientationChange_continuousOn (i j : ι) :
    ContinuousOn (fun p : B × Bool => orientationChange (Z.coordChange i j p.1).det p.2)
      ((Z.baseSet i ∩ Z.baseSet j) ×ˢ univ) := by
  have hd : ContinuousOn (fun x => (Z.coordChange i j x).det) (Z.baseSet i ∩ Z.baseSet j) :=
    ContinuousLinearMap.continuous_det.comp_continuousOn (Z.continuousOn_coordChange i j)
  intro p hp
  have hc : ContinuousAt (fun q : B × Bool => (Z.coordChange i j q.1).det) p :=
    (hd.continuousAt (((Z.isOpen_baseSet i).inter (Z.isOpen_baseSet j)).mem_nhds hp.1)).comp
      continuous_fst.continuousAt
  by_cases hpos : 0 < (Z.coordChange i j p.1).det
  · apply ContinuousAt.continuousWithinAt
    apply continuous_snd.continuousAt.congr_of_eventuallyEq
    filter_upwards [hc (Ioi_mem_nhds hpos)] with q hq
    change 0 < (Z.coordChange i j q.1).det at hq
    simp [orientationChange, hq]
  · have hneg : (Z.coordChange i j p.1).det < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) (orientationDet_ne_zero Z i j hp.1)
    apply ContinuousAt.continuousWithinAt
    apply ((continuous_of_discreteTopology : Continuous (fun s : Bool => !s)).comp
      continuous_snd).continuousAt.congr_of_eventuallyEq
    filter_upwards [hc (Iio_mem_nhds hneg)] with q hq
    change (Z.coordChange i j q.1).det < 0 at hq
    simp [orientationChange, hq.not_gt]

/-- The genuine orientation double cover: the fibre has two points, glued
by the signs of the original linear coordinate changes. -/
def orientationCoverCore : FiberBundleCore ι B Bool where
  baseSet := Z.baseSet
  isOpen_baseSet := Z.isOpen_baseSet
  indexAt := Z.indexAt
  mem_baseSet_at := Z.mem_baseSet_at
  coordChange i j x := orientationChange (Z.coordChange i j x).det
  coordChange_self i x hx s := by
    simp [orientationChange, orientationDet_self Z i hx]
  continuousOn_coordChange := orientationChange_continuousOn Z
  coordChange_comp i j k x hx s := by
    rw [← orientationChange_mul (orientationDet_ne_zero Z i j hx.1)
      (orientationDet_ne_zero Z j k ⟨hx.1.2, hx.2⟩), orientationDet_comp Z i j k hx]

/-- Local trivializations, with discrete fibres, prove the covering property. -/
theorem orientationCover_isCoveringMap : IsCoveringMap (orientationCoverCore Z).proj :=
  IsCoveringMap.mk (f := (orientationCoverCore Z).proj)
    (fun _ => Bool) (fun b => (orientationCoverCore Z).localTrivAt b)
    ((orientationCoverCore Z).mem_localTrivAt_baseSet)

/-- The section is constructed by path lifting; its existence is not a
replacement hypothesis for orientability. -/
theorem orientationCover_exists_section [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] :
    ∃ s : C(B, (orientationCoverCore Z).TotalSpace),
      (orientationCoverCore Z).proj ∘ s = id := by
  obtain ⟨b⟩ := (inferInstance : Nonempty B)
  let e : (orientationCoverCore Z).TotalSpace := ⟨b, false⟩
  obtain ⟨s, hs, _⟩ := (orientationCover_isCoveringMap Z).existsUnique_continuousMap_lifts
    (ContinuousMap.id B) b e rfl
  exact ⟨s, hs.2⟩

/-- A compatible local orientation for the original vector-bundle atlas. -/
theorem exists_compatible_orientationSigns [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] :
    ∃ σ : ι → B → Bool,
      (∀ i, ContinuousOn (σ i) (Z.baseSet i)) ∧
      ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
        σ j x = orientationChange (Z.coordChange i j x).det (σ i x) := by
  let C := orientationCoverCore Z
  obtain ⟨s, hs⟩ := orientationCover_exists_section Z
  have hproj (x : B) : (s x).proj = x := congrFun hs x
  let σ : ι → B → Bool := fun i x => ((C.localTriv i) (s x)).2
  refine ⟨σ, ?_, ?_⟩
  · intro i x hx
    have hsource : s x ∈ (C.localTriv i).source := by
      change (s x).proj ∈ Z.baseSet i
      rw [hproj]
      exact hx
    exact (continuous_snd.continuousAt.comp
      (((C.localTriv i).continuousAt hsource).comp s.continuous.continuousAt)).continuousWithinAt
  · intro i j x hx
    have hc := C.coordChange_comp (C.indexAt x) i j x
      ⟨⟨C.mem_baseSet_at x, hx.1⟩, hx.2⟩ (s x).2
    dsimp [σ]
    simp only [hproj]
    exact hc.symm

/-- Orientability expressed by continuous local frame signs making every
actual coordinate-change determinant positive. -/
def HasPositiveOrientationAtlas : Prop :=
  ∃ σ : ι → B → Bool,
    (∀ i, ContinuousOn (σ i) (Z.baseSet i)) ∧
    ∀ i j x, x ∈ Z.baseSet i ∩ Z.baseSet j →
      0 < orientationSign (σ j x) * (Z.coordChange i j x).det * orientationSign (σ i x)

/-- Every real finite-dimensional vector bundle on a simply connected,
locally path-connected base has an orientation. -/
theorem hasPositiveOrientationAtlas_of_simplyConnected
    [FiniteDimensional ℝ F] [SimplyConnectedSpace B] [LocallyPathConnectedSpace B] :
    HasPositiveOrientationAtlas Z := by
  obtain ⟨σ, hcont, hcompat⟩ := exists_compatible_orientationSigns Z
  refine ⟨σ, hcont, ?_⟩
  intro i j x hx
  rw [hcompat i j x hx]
  exact orientationChange_positive (orientationDet_ne_zero Z i j hx) (σ i x)

end PoincareConjecture

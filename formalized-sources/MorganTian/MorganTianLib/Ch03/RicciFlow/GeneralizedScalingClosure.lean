import MorganTianLib.Ch03.RicciFlow.GeneralizedAffineChart
import MorganTianLib.Ch03.RicciFlow.GeneralizedScaling

/-!
# Morgan--Tian Ch. 3 - packaging affine scaling of generalized space-time

The preceding scaling files establish the coordinate and differential laws for
an affine change of time.  This file packages those laws into an actual
`GeneralizedSpaceTime`; no Ricci-flow equation or smooth metric transport is
claimed here.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

private theorem affineTimeChange_range_aux
    {S : GeneralizedSpaceTime n (N := N)} (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Set.range (fun x => Q * S.time x + a) =
      parabolicTimeOrderIso Q hQ a '' Set.range S.time := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨S.time x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

private theorem affineTimeChange_range_ordConnected_aux
    {S : GeneralizedSpaceTime n (N := N)} (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (parabolicTimeOrderIso Q hQ a '' Set.range S.time).OrdConnected := by
  refine ⟨?_⟩
  intro s hs t ht u hu
  rcases hs with ⟨s', hs', rfl⟩
  rcases ht with ⟨t', ht', rfl⟩
  let e := parabolicTimeOrderIso Q hQ a
  have hu' : e.symm u ∈ Set.Icc s' t' := by
    constructor
    · have heq : e (e.symm u) = u := e.apply_symm_apply u
      have hpoint : e s' ≤ e (e.symm u) := by
        rw [heq]
        exact hu.1
      have h := (e.map_rel_iff).1 hpoint
      simpa using h
    · have heq : e (e.symm u) = u := e.apply_symm_apply u
      have hpoint : e (e.symm u) ≤ e t' := by
        rw [heq]
        exact hu.2
      have h := (e.map_rel_iff).1 hpoint
      simpa using h
  exact ⟨e.symm u, S.timeRange_ordConnected.out hs' ht' hu', e.apply_symm_apply u⟩

private theorem affineTimeChange_frontier_range_aux
    {S : GeneralizedSpaceTime n (N := N)} (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    frontier (Set.range (fun x => Q * S.time x + a)) =
      parabolicTimeOrderIso Q hQ a '' frontier (Set.range S.time) := by
  rw [affineTimeChange_range_aux (S := S) n Q hQ a]
  change frontier ((parabolicTimeOrderIso Q hQ a).toHomeomorph ''
      Set.range S.time) =
    (parabolicTimeOrderIso Q hQ a).toHomeomorph '' frontier (Set.range S.time)
  exact (parabolicTimeOrderIso Q hQ a).toHomeomorph.image_frontier
    (Set.range S.time) |>.symm

private theorem affineTimeChange_preimage_frontier_range_aux
    {S : GeneralizedSpaceTime n (N := N)} (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (fun x => Q * S.time x + a) ⁻¹'
        frontier (Set.range (fun x => Q * S.time x + a)) =
      S.time ⁻¹' frontier (Set.range S.time) := by
  rw [affineTimeChange_frontier_range_aux (S := S) n Q hQ a]
  ext x
  constructor
  · rintro ⟨u, hu, hux⟩
    have hval : u = S.time x := by
      apply (parabolicTimeOrderIso Q hQ a).injective
      calc
        parabolicTimeOrderIso Q hQ a u = Q * S.time x + a := hux
        _ = parabolicTimeOrderIso Q hQ a (S.time x) := rfl
    simpa [hval] using hu
  · intro hx
    exact ⟨S.time x, hx, rfl⟩

/-- **Math.** A positive affine change of time packages into a generalized
space-time.  The local products are pulled back along the affine product
diffeomorphism, so the boundary and time-vector contracts are preserved. -/
def GeneralizedSpaceTime.affineTimeChange
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    GeneralizedSpaceTime n (N := N) := by
  let time' : N → ℝ := fun x => Q * S.time x + a
  let vector' := S.scaledTimeVector n Q
  refine
    { paracompactSpace := S.paracompactSpace
      t2Space := S.t2Space
      time := time'
      timeVector := vector'
      time_contMDiff := ?_
      timeRange_ordConnected := ?_
      boundary_eq := ?_
      localProduct := ?_ }
  · have hscaled : ContMDiff (modelWithCornersEuclideanHalfSpace n.succ)
        (modelWithCornersSelf ℝ ℝ) ∞ (fun x => Q * S.time x) := by
      convert S.scaledTime_contMDiff n Q using 1
      funext x
      simp [GeneralizedSpaceTime.scaledTime, smul_eq_mul]
    have hconst : ContMDiff (modelWithCornersEuclideanHalfSpace n.succ)
        (modelWithCornersSelf ℝ ℝ) ∞ (fun _ : N => a) := contMDiff_const
    have hadd := hscaled.add hconst
    convert hadd using 1
    funext x
    rfl
  · change (Set.range (fun x => Q * S.time x + a)).OrdConnected
    rw [affineTimeChange_range_aux (S := S) n Q hQ a]
    exact affineTimeChange_range_ordConnected_aux (S := S) n Q hQ a
  · have hpre := affineTimeChange_preimage_frontier_range_aux (S := S) n Q hQ a
    simpa [time'] using S.boundary_eq.trans hpre.symm
  · intro x
    let c := S.localProduct x
    let c' := affineTimeChangeChart n c Q hQ a
    refine
      { spatialSource := c.spatialSource
        timeSource := parabolicTimeOrderIso Q hQ a '' c.timeSource
        spatialSource_isOpen := c.spatialSource_isOpen
        timeSource_ordConnected := ?_
        equiv := c'
        source_eq := ?_
        target_isOpen := ?_
        center_mem := ?_
        source_uniqueMDiffOn := ?_
        to_contMDiffOn := ?_
        inv_contMDiffOn := ?_
        time_eq := ?_
        timeVector_eq := ?_ }
    · refine ⟨?_⟩
      intro s hs t ht u hu
      rcases hs with ⟨s', hs', rfl⟩
      rcases ht with ⟨t', ht', rfl⟩
      let e := parabolicTimeOrderIso Q hQ a
      have hu' : e.symm u ∈ Set.Icc s' t' := by
        constructor
        · have heq : e (e.symm u) = u := e.apply_symm_apply u
          have hpoint : e s' ≤ e (e.symm u) := by
            rw [heq]
            exact hu.1
          have h := (e.map_rel_iff).1 hpoint
          simpa using h
        · have heq : e (e.symm u) = u := e.apply_symm_apply u
          have hpoint : e (e.symm u) ≤ e t' := by
            rw [heq]
            exact hu.2
          have h := (e.map_rel_iff).1 hpoint
          simpa using h
      exact ⟨e.symm u, c.timeSource_ordConnected.out hs' ht' hu',
        e.apply_symm_apply u⟩
    · exact affineTimeChangeChart_source n c Q hQ a
    · rw [affineTimeChangeChart_target n c Q hQ a]
      exact c.target_isOpen
    · exact affineTimeChangeChart_center_mem n c Q hQ a
    · exact affineTimeChangeChart_source_uniqueMDiffOn n c Q hQ a
    · exact affineTimeChangeChart_contMDiffOn n c Q hQ a
    · exact affineTimeChangeChart_inv_contMDiffOn n c Q hQ a
    · intro z hz
      exact affineTimeChangeChart_time_coordinate n c Q hQ a hz
    · intro z hz
      simpa [time', vector', c'] using
        (affineTimeChangeChart_timeVector_eq n c Q hQ a hz)

@[simp]
theorem GeneralizedSpaceTime.affineTimeChange_time
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x : N) :
    (S.affineTimeChange n Q hQ a).time x = Q * S.time x + a :=
  by
    simp [GeneralizedSpaceTime.affineTimeChange]

@[simp]
theorem GeneralizedSpaceTime.affineTimeChange_timeVector
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)
    (x : N) :
    (S.affineTimeChange n Q hQ a).timeVector x = Q⁻¹ • S.timeVector x :=
  by
    simp [GeneralizedSpaceTime.affineTimeChange]

theorem GeneralizedSpaceTime.affineTimeChange_range
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    Set.range (S.affineTimeChange n Q hQ a).time =
      parabolicTimeOrderIso Q hQ a '' Set.range S.time := by
  exact affineTimeChange_range_aux (S := S) n Q hQ a

theorem GeneralizedSpaceTime.affineTimeChange_frontier_range
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    frontier (Set.range (S.affineTimeChange n Q hQ a).time) =
      parabolicTimeOrderIso Q hQ a '' frontier (Set.range S.time) := by
  exact affineTimeChange_frontier_range_aux (S := S) n Q hQ a

theorem GeneralizedSpaceTime.affineTimeChange_preimage_frontier_range
    (S : GeneralizedSpaceTime n (N := N)) (Q : ℝ) (hQ : 0 < Q) (a : ℝ) :
    (S.affineTimeChange n Q hQ a).time ⁻¹'
        frontier (Set.range (S.affineTimeChange n Q hQ a).time) =
      S.time ⁻¹' frontier (Set.range S.time) := by
  exact affineTimeChange_preimage_frontier_range_aux (S := S) n Q hQ a

end MorganTianLib

end

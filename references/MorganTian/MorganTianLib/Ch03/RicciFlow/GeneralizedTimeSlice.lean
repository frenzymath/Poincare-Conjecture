import MorganTianLib.Ch03.RicciFlow.TimeSlice

/-!
# Morgan--Tian Ch. 3 - charts on generalized time-slices

The adapted product charts of a generalized space-time restrict at fixed time
to ordinary `n`-dimensional charts on the level set `M_t`.  This module builds
those restricted charts; they are the intrinsic domains on which the horizontal
metric and its Ricci tensor are read.
-/

open scoped ContDiff Manifold Topology
open Set

noncomputable section

namespace MorganTianLib

variable (n : ℕ)
  {N : Type*} [TopologicalSpace N]
  [ChartedSpace (EuclideanHalfSpace n.succ) N]
  [IsManifold (modelWithCornersEuclideanHalfSpace n.succ) ∞ N]

private theorem GeneralizedSpaceTimeLocalChart.time_mem_source
    {S : GeneralizedSpaceTime n (N := N)} {t : ℝ}
    (x : S.timeSlice n t)
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x) :
    t ∈ c.timeSource := by
  let z := c.equiv.symm (x : N)
  have hz : z ∈ c.equiv.source := c.equiv.map_target c.center_mem
  have hzprod : z ∈ c.spatialSource ×ˢ c.timeSource := c.source_eq ▸ hz
  have htime := c.time_eq z hz
  have hzx : c.equiv z = (x : N) := c.equiv.right_inv c.center_mem
  have hxt : S.time (x : N) = t :=
    (S.mem_timeSlice_iff (n := n)).1 x.property
  rw [hzx, hxt] at htime
  exact (congrArg (fun s : ℝ => s ∈ c.timeSource) htime).mpr hzprod.2

private theorem GeneralizedSpaceTimeLocalChart.symm_time_eq
    {S : GeneralizedSpaceTime n (N := N)} {t : ℝ} {x : N}
    (c : GeneralizedSpaceTimeLocalChart n S.time S.timeVector x)
    (y : S.timeSlice n t) (hy : (y : N) ∈ c.equiv.target) :
    (c.equiv.symm (y : N)).2 = t := by
  let z := c.equiv.symm (y : N)
  have hz : z ∈ c.equiv.source := c.equiv.map_target hy
  have htime := c.time_eq z hz
  have hzy : c.equiv z = (y : N) := c.equiv.right_inv hy
  have hyt : S.time (y : N) = t :=
    (S.mem_timeSlice_iff (n := n)).1 y.property
  rw [hzy, hyt] at htime
  change z.2 = t
  exact htime.symm

/-- **Math.** The product chart at `x in M_t`, restricted to the spatial
plaque at time `t`.  Its source in `M_t` is the part lying in the ambient
chart target, and its image is the open spatial domain `V`. -/
def GeneralizedSpaceTime.timeSliceChart
    (S : GeneralizedSpaceTime n (N := N)) (t : ℝ)
    (x : S.timeSlice n t) :
    OpenPartialHomeomorph (S.timeSlice n t)
      (EuclideanSpace ℝ (Fin n)) := by
  classical
  let c := S.localProduct (x : N)
  have ht : t ∈ c.timeSource := c.time_mem_source n x
  let source : Set (S.timeSlice n t) :=
    Subtype.val ⁻¹' c.equiv.target
  let target : Set (EuclideanSpace ℝ (Fin n)) := c.spatialSource
  let invPoint : ∀ u : target, S.timeSlice n t := fun u =>
    ⟨c.equiv ((u : EuclideanSpace ℝ (Fin n)), t), by
      apply (S.mem_timeSlice_iff (n := n)).2
      have hu : ((u : EuclideanSpace ℝ (Fin n)), t) ∈ c.equiv.source :=
        c.source_eq ▸ ⟨u.property, ht⟩
      exact c.time_eq _ hu⟩
  exact
    { toFun := fun y => (c.equiv.symm (y : N)).1
      invFun := fun u => if hu : u ∈ target then invPoint ⟨u, hu⟩ else x
      source := source
      target := target
      map_source' := by
        intro y hy
        have hz : c.equiv.symm (y : N) ∈ c.equiv.source :=
          c.equiv.map_target hy
        have hzprod : c.equiv.symm (y : N) ∈
            c.spatialSource ×ˢ c.timeSource := c.source_eq ▸ hz
        exact hzprod.1
      map_target' := by
        intro u hu
        rw [dif_pos hu]
        exact c.equiv.map_source (c.source_eq ▸ ⟨hu, ht⟩)
      left_inv' := by
        intro y hy
        have hyV : (c.equiv.symm (y : N)).1 ∈ target := by
          have hz : c.equiv.symm (y : N) ∈ c.equiv.source :=
            c.equiv.map_target hy
          exact (c.source_eq ▸ hz).1
        rw [dif_pos hyV]
        apply Subtype.ext
        change c.equiv ((c.equiv.symm (y : N)).1, t) = (y : N)
        have htime : (c.equiv.symm (y : N)).2 = t :=
          c.symm_time_eq n y hy
        calc
          c.equiv ((c.equiv.symm (y : N)).1, t) =
              c.equiv (c.equiv.symm (y : N)) := by
                apply congrArg c.equiv
                exact Prod.ext rfl htime.symm
          _ = (y : N) := c.equiv.right_inv hy
      right_inv' := by
        intro u hu
        rw [dif_pos hu]
        change (c.equiv.symm (c.equiv (u, t))).1 = u
        rw [c.equiv.left_inv (c.source_eq ▸ ⟨hu, ht⟩)]
      open_source := c.target_isOpen.preimage continuous_subtype_val
      open_target := c.spatialSource_isOpen
      continuousOn_toFun := by
        exact continuous_fst.comp_continuousOn
          (c.inv_contMDiffOn.continuousOn.comp
            continuous_subtype_val.continuousOn (fun y hy => hy))
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        have hmap : ContinuousOn
            (fun u : EuclideanSpace ℝ (Fin n) => c.equiv (u, t)) target :=
          c.to_contMDiffOn.continuousOn.comp
            (continuous_id.prodMk continuous_const).continuousOn
            (fun u hu => c.source_eq ▸ ⟨hu, ht⟩)
        have hrestricted : Continuous (fun u : target => invPoint u) :=
          (continuousOn_iff_continuous_restrict.1 hmap).subtype_mk _
        convert hrestricted using 1
        funext u
        simp only [restrict_apply, dif_pos u.property] }

end MorganTianLib

end

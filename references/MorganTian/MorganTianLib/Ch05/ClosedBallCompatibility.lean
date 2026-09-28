import MorganTianLib.Ch05.PointedGH
import MorganTianLib.Ch05.LengthCone

/-!
# Morgan--Tian Chapter 5: compact closed-ball compatibility

Closed balls are the compact finite-radius carriers used by the packing
diagonalization.  This module supplies their based inclusions and the sharp
length-space annular estimate needed before compatible stages can be glued.
-/

open Set Filter Topology
open scoped Topology unitInterval

namespace MorganTianLib

universe u

/-- **Math.** A point in a larger closed ball can be moved into a smaller closed ball
along a distance-realizing path, with displacement at most the annular width. -/
theorem exists_mem_closedBall_dist_le_sub_of_lengthSpace
    {X : Type*} [MetricSpace X] [LengthSpace X]
    (x y : X) {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (hy : y ∈ Metric.closedBall x s) :
    ∃ z ∈ Metric.closedBall x r, dist y z ≤ s - r := by
  by_cases hyr : y ∈ Metric.closedBall x r
  · exact ⟨y, hyr, by simp [sub_nonneg.mpr hrs]⟩
  by_cases hrzero : r = 0
  · refine ⟨x, Metric.mem_closedBall_self hr, ?_⟩
    have hy' := Metric.mem_closedBall.mp hy
    simpa [hrzero, sub_zero] using hy'
  have hrpos : 0 < r := lt_of_le_of_ne hr (by
    intro h
    exact hrzero h.symm)
  have hxy : r < dist x y := by
    have hxy' : r < dist y x := lt_of_not_ge (by
      intro h
      exact hyr (Metric.mem_closedBall.mpr h))
    simpa [dist_comm] using hxy'
  have hys : dist x y ≤ s := by
    simpa [dist_comm] using (Metric.mem_closedBall.mp hy)
  obtain ⟨γ, hγbv, hγvar⟩ := LengthSpace.exists_path_realizing_dist X x y
  have hcont : Continuous (fun t : I => dist x (γ t)) :=
    continuous_const.dist γ.continuous
  obtain ⟨t, ht, hdist⟩ :=
    intermediate_value_Icc (show (0 : I) ≤ 1 from zero_le_one)
      hcont.continuousOn
      (show r ∈ Icc (dist x (γ 0)) (dist x (γ 1)) by
        simp [hr, hxy.le])
  have ht0 : (0 : I) ≤ t := ht.1
  have ht1 : t ≤ (1 : I) := ht.2
  let z : X := γ t
  have hzdist : dist x z = r := by
    simpa [z] using hdist
  have hzball : z ∈ Metric.closedBall x r := by
    apply Metric.mem_closedBall.mpr
    simp [dist_comm, hzdist]
  have hleft : BoundedVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t) :=
    hγbv.mono inter_subset_left
  have hright : BoundedVariationOn (γ : I → X) (Set.univ ∩ Icc t (1 : I)) :=
    hγbv.mono inter_subset_left
  have hadd := eVariationOn.Icc_add_Icc (γ : I → X) ht0 ht1
    (show t ∈ (Set.univ : Set I) from mem_univ _)
  have htoleft :
      (eVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t)).toReal ≥ r := by
    have hdistxz : edist x z ≤
        eVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t) := by
      simpa [z] using (eVariationOn.edist_le (γ : I → X)
        (s := Set.univ ∩ Icc (0 : I) t) (x := (0 : I)) (y := t)
        ⟨mem_univ _, ⟨le_rfl, ht0⟩⟩ ⟨mem_univ _, ⟨ht.1, le_rfl⟩⟩)
    calc
      r = dist x z := hzdist.symm
      _ = (edist x z).toReal := dist_edist _ _
      _ ≤ (eVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t)).toReal :=
        ENNReal.toReal_mono hleft hdistxz
  have hright_le :
      (eVariationOn (γ : I → X) (Icc t (1 : I))).toReal ≤
        dist x y - r := by
    have htoadd := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add hleft hright] at htoadd
    simp only [univ_inter] at htoadd
    have hIcc : Icc (0 : I) (1 : I) = (Set.univ : Set I) := by
      apply Set.eq_univ_of_forall
      intro u
      exact ⟨u.2.1, u.2.2⟩
    have htotal : (eVariationOn (γ : I → X) (Icc (0 : I) (1 : I))).toReal =
        dist x y := by
      rw [hIcc]
      exact hγvar
    rw [htotal] at htoadd
    have htoleft' :
        (eVariationOn (γ : I → X) (Icc (0 : I) t)).toReal ≥ r := by
      simpa only [univ_inter] using htoleft
    have htail' :
        (eVariationOn (γ : I → X) (Icc t (1 : I))).toReal =
          (eVariationOn (γ : I → X) (Set.univ ∩ Icc t (1 : I))).toReal := by
      simp only [univ_inter]
    linarith [htoadd, htoleft']
  refine ⟨z, hzball, ?_⟩
  calc
    dist y z = (edist y z).toReal := dist_edist _ _
    _ ≤ (eVariationOn (γ : I → X) (Set.univ ∩ Icc t (1 : I))).toReal := by
      apply ENNReal.toReal_mono hright
      have hdistzy := eVariationOn.edist_le (γ : I → X)
        (s := Set.univ ∩ Icc t (1 : I))
        (x := t) (y := (1 : I))
        ⟨mem_univ _, ⟨le_rfl, ht1⟩⟩ ⟨mem_univ _, ⟨ht1, le_rfl⟩⟩
      rw [edist_comm] at hdistzy
      simpa [z] using hdistzy
    _ ≤ s - r := by
      have hright_le' :
          (eVariationOn (γ : I → X) (Set.univ ∩ Icc t (1 : I))).toReal ≤
            dist x y - r := by simpa only [univ_inter] using hright_le
      linarith [hright_le', hys]

/-- **Math.** The finite-diameter pointed model of a closed metric ball. -/
def closedBallModel (X : BasedMetricSpaceBundle.{u}) (r : ℝ) (hr : 0 ≤ r) :
    FiniteDiameterBasedMetricSpace.{u} :=
  { carrier := Metric.closedBall X.base r
    metric := inferInstance
    base := ⟨X.base, Metric.mem_closedBall_self hr⟩
    finite_diameter := by
      refine ⟨2 * r, ?_⟩
      intro p q
      change dist p.1 q.1 ≤ 2 * r
      have hp := Metric.mem_closedBall.mp p.2
      have hq := Metric.mem_closedBall.mp q.2
      calc
        dist p.1 q.1 ≤ dist p.1 X.base + dist X.base q.1 :=
          dist_triangle _ _ _
        _ ≤ r + r := add_le_add hp (by simpa [dist_comm] using hq)
        _ = 2 * r := by ring }

/-- **Math.** The closed and open radius-`r` models have a common pointed
realization in the original length space.  The two maps are the subtype
inclusions, so the only nontrivial estimate is the density of the open ball
inside the closed ball. -/
def closedBallModelBallModelRealization
    (X : BasedMetricSpaceBundle.{u}) (r : ℝ) (hr : 0 < r) :
    PointedGHRealization (closedBallModel X r hr.le) (ballModel X r hr) :=
  { ambient := X
    left := fun p => p.1
    right := fun p => p.1
    left_isometry := by
      intro p q
      rfl
    right_isometry := by
      intro p q
      rfl
    left_base := rfl
    right_base := rfl }

/-- **Math.** In a length space, the compact closed-ball model and the open-ball
model at the same positive radius have pointed GH distance zero.  This is the
target-identification bridge needed when compact diagonal limits are compared
with the source's open-ball definition. -/
theorem pointedGHDistance_closedBallModel_ballModel_eq_zero
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    {r : ℝ} (hr : 0 < r) :
    pointedGHDistance (closedBallModel X r hr.le) (ballModel X r hr) = 0 := by
  apply (pointedGHDistance_eq_zero_iff_forall_pos_exists_realization_lt
    (closedBallModel X r hr.le) (ballModel X r hr)).2
  intro ε hε
  refine ⟨closedBallModelBallModelRealization X r hr, ?_⟩
  unfold pointedHausdorffDist
  calc
    Metric.hausdorffDist
        (Set.range (closedBallModelBallModelRealization X r hr).left)
        (Set.range (closedBallModelBallModelRealization X r hr).right) ≤ ε / 2 := by
      apply Metric.hausdorffDist_le_of_mem_dist (by positivity)
      · rintro z ⟨p, rfl⟩
        have hpball : p.1 ∈ Metric.ball X.base (r + ε / 2) := by
          apply Metric.mem_ball.mpr
          have hpclosed := Metric.mem_closedBall.mp p.2
          simpa [dist_comm] using
            lt_of_le_of_lt hpclosed (lt_add_of_pos_right r (half_pos hε))
        obtain ⟨q, hq, hpq⟩ :=
          exists_mem_ball_dist_le_sub_of_lengthSpace X.base p.1 hr
            (by linarith [hε.le]) hpball
        refine ⟨q, ⟨⟨q, hq⟩, rfl⟩, ?_⟩
        calc
          dist p.1 q ≤ r + ε / 2 - r := hpq
          _ = ε / 2 := by ring
      · rintro z ⟨p, rfl⟩
        let q : (closedBallModel X r hr.le).carrier :=
          ⟨p.1, (Metric.mem_ball.mp p.2).le⟩
        refine ⟨q.1, ⟨q, rfl⟩, ?_⟩
        change dist p.1 p.1 ≤ ε / 2
        exact (dist_self _).le.trans (by positivity)
    _ < ε := by linarith

/-- **Math.** Pointed-GH convergence of positive-radius closed-ball models
transfers to the corresponding open-ball models.  The diameter witness is
transported through the subtype inclusion, while the distance limit uses the
zero-distance bridge above and the pointed triangle inequality. -/
theorem pointedGHConverges_of_closedBallModel_to_ballModel
    (X : ℕ → BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r : ℕ → ℝ) (hr : ∀ k, 0 < r k)
    (L : FiniteDiameterBasedMetricSpace.{u})
    (hconv :
      PointedGHConverges
        (fun k => closedBallModel (X k) (r k) (hr k).le) L) :
    PointedGHConverges
      (fun k => ballModel (X k) (r k) (hr k)) L := by
  constructor
  · obtain ⟨C, hC⟩ := hconv.1
    refine ⟨C, ?_⟩
    intro k p q
    have hpclosed : p.1 ∈ Metric.closedBall (X k).base (r k) :=
      Metric.mem_closedBall.mpr (Metric.mem_ball.mp p.2).le
    have hqclosed : q.1 ∈ Metric.closedBall (X k).base (r k) :=
      Metric.mem_closedBall.mpr (Metric.mem_ball.mp q.2).le
    let p' : (closedBallModel (X k) (r k) (hr k).le).carrier :=
      ⟨p.1, hpclosed⟩
    let q' : (closedBallModel (X k) (r k) (hr k).le).carrier :=
      ⟨q.1, hqclosed⟩
    change dist p.1 q.1 ≤ C
    exact (hC k p' q').trans_eq (by rfl)
  · have hzero : ∀ k : ℕ,
        pointedGHDistance
          (ballModel (X k) (r k) (hr k))
          (closedBallModel (X k) (r k) (hr k).le) = 0 := by
      intro k
      rw [pointedGHDistance_symm]
      exact pointedGHDistance_closedBallModel_ballModel_eq_zero (X k) (hr k)
    have hupper : ∀ k : ℕ,
        pointedGHDistance (ballModel (X k) (r k) (hr k)) L ≤
          pointedGHDistance
              (ballModel (X k) (r k) (hr k))
              (closedBallModel (X k) (r k) (hr k).le) +
            pointedGHDistance (closedBallModel (X k) (r k) (hr k).le) L := by
      intro k
      exact pointedGHDistance_triangle _ _ _
    apply squeeze_zero
    · intro k
      exact pointedGHDistance_nonneg _ _
    · exact hupper
    · have hsum :=
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).add hconv.2
      simpa [hzero] using hsum

/-- **Math.** The canonical inclusion of nested pointed closed balls. -/
def closedBallModelInclusion
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    (closedBallModel X r hr).carrier → (closedBallModel X s hs).carrier :=
  fun p => ⟨p.1, le_trans p.2 hrs⟩

theorem closedBallModelInclusion_isometry
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    Isometry (closedBallModelInclusion X r s hr hs hrs) := by
  intro p q
  rfl

theorem closedBallModelInclusion_base
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    closedBallModelInclusion X r s hr hs hrs (closedBallModel X r hr).base =
      (closedBallModel X s hs).base := by
  apply Subtype.ext
  rfl

/-- **Math.** A nested pair of closed balls has an explicit pointed ambient realization. -/
noncomputable def closedBallModelNestedRealization
    (X : BasedMetricSpaceBundle.{u}) (r s : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    PointedGHRealization (closedBallModel X r hr) (closedBallModel X s hs) :=
  { ambient :=
      { carrier := (closedBallModel X s hs).carrier
        metric := inferInstance
        base := (closedBallModel X s hs).base }
    left := closedBallModelInclusion X r s hr hs hrs
    right := id
    left_isometry := closedBallModelInclusion_isometry X r s hr hs hrs
    right_isometry := isometry_id
    left_base := closedBallModelInclusion_base X r s hr hs hrs
    right_base := rfl }

/-- **Math.** The sharp annular Hausdorff bound for nested closed balls in a length space. -/
theorem pointedHausdorffDist_closedBallModelNestedRealization_le_sub
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    pointedHausdorffDist (closedBallModelNestedRealization X r s hr hs hrs) ≤ s - r := by
  unfold pointedHausdorffDist
  apply Metric.hausdorffDist_le_of_mem_dist (sub_nonneg.mpr hrs)
  · rintro z ⟨p, rfl⟩
    let ip := closedBallModelInclusion X r s hr hs hrs p
    refine ⟨ip, ⟨ip, rfl⟩, ?_⟩
    change dist ip ip ≤ s - r
    exact (dist_self _).le.trans (sub_nonneg.mpr hrs)
  · rintro z ⟨p, rfl⟩
    obtain ⟨q, hq, hpq⟩ :=
      exists_mem_closedBall_dist_le_sub_of_lengthSpace X.base p.1 hr hrs p.2
    refine ⟨closedBallModelInclusion X r s hr hs hrs ⟨q, hq⟩,
      ⟨⟨q, hq⟩, rfl⟩, ?_⟩
    exact hpq

/-- **Math.** The pointed GH distance between nested closed balls is bounded by the
width of their radial annulus. -/
theorem pointedGHDistance_closedBallModel_le_sub
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r ≤ s) :
    pointedGHDistance (closedBallModel X r hr) (closedBallModel X s hs) ≤ s - r :=
  (pointedGHDistance_le_realization
      (closedBallModelNestedRealization X r s hr hs hrs)).trans
    (pointedHausdorffDist_closedBallModelNestedRealization_le_sub
      X r s hr hs hrs)

/-- **Math.** Closed-ball models at arbitrary nonnegative radii are controlled by the
absolute radial difference. -/
theorem pointedGHDistance_closedBallModel_le_abs_sub
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    pointedGHDistance (closedBallModel X r hr) (closedBallModel X s hs) ≤ |s - r| := by
  by_cases hrs : r ≤ s
  · simpa [abs_of_nonneg (sub_nonneg.mpr hrs)] using
      (pointedGHDistance_closedBallModel_le_sub X r s hr hs hrs)
  · have hsr : s ≤ r := le_of_not_ge hrs
    rw [pointedGHDistance_symm]
    calc
      pointedGHDistance (closedBallModel X s hs) (closedBallModel X r hr) ≤ r - s :=
        pointedGHDistance_closedBallModel_le_sub X s r hs hr hsr
      _ = |s - r| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hsr)]
        ring

end MorganTianLib

#print axioms MorganTianLib.exists_mem_closedBall_dist_le_sub_of_lengthSpace
#print axioms MorganTianLib.pointedGHDistance_closedBallModel_le_abs_sub

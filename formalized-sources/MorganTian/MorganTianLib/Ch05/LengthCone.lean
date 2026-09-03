import MorganTianLib.Ch05.PointedGH

/-!
# Morgan--Tian Chapter 5: length-space radial control

The length-space hypothesis gives the radial point needed to compare nested
pointed balls at the sharp annular scale.
-/

open Set Filter Topology
open scoped Topology unitInterval

namespace MorganTianLib

universe u

theorem exists_mem_ball_dist_le_sub_of_lengthSpace
    {X : Type*} [MetricSpace X] [LengthSpace X]
    (x y : X) {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (hy : y ∈ Metric.ball x s) :
    ∃ z ∈ Metric.ball x r, dist y z ≤ s - r := by
  by_cases hyr : y ∈ Metric.ball x r
  · exact ⟨y, hyr, by simp [sub_nonneg.mpr hrs]⟩
  have hxy : r ≤ dist x y := by
    apply le_of_not_gt
    intro hlt
    apply hyr
    simpa [Metric.mem_ball, dist_comm] using hlt
  obtain ⟨γ, hγbv, hγvar⟩ := LengthSpace.exists_path_realizing_dist X x y
  have hty : dist x y < s := by simpa [Metric.mem_ball, dist_comm] using hy
  let ε : ℝ := min (r / 2) ((s - dist x y) / 2)
  let q : ℝ := r - ε
  have hε_nonneg : 0 ≤ ε := by
    dsimp [ε]
    positivity
  have hε_le : ε ≤ (s - dist x y) / 2 := min_le_right _ _
  have hq_pos : 0 < q := by
    dsimp [q]
    have hεr : ε ≤ r / 2 := min_le_left _ _
    linarith
  have hq_lt : q < r := by
    dsimp [q]
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact lt_min (by linarith) (by linarith)
    linarith
  have hq_le : q ≤ dist x y := by
    dsimp [q]
    linarith [hxy, hε_nonneg]
  have hcont : Continuous (fun t : I => dist x (γ t)) :=
    continuous_const.dist γ.continuous
  obtain ⟨t, ht, hdist⟩ :=
    intermediate_value_Icc (show (0 : I) ≤ 1 from zero_le_one)
      hcont.continuousOn (show q ∈ Icc (dist x (γ 0)) (dist x (γ 1)) by
        simp [q, hq_pos.le, hq_le])
  have ht0 : (0 : I) ≤ t := ht.1
  have ht1 : t ≤ (1 : I) := ht.2
  let z : X := γ t
  have hzdist : dist x z = q := by
    simpa [z] using hdist
  have hzball : z ∈ Metric.ball x r := by
    simpa [Metric.mem_ball, dist_comm, hzdist] using hq_lt
  have hleft : BoundedVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t) :=
    hγbv.mono inter_subset_left
  have hright : BoundedVariationOn (γ : I → X) (Set.univ ∩ Icc t (1 : I)) :=
    hγbv.mono inter_subset_left
  have hadd := eVariationOn.Icc_add_Icc (γ : I → X) ht0 ht1
    (show t ∈ (Set.univ : Set I) from mem_univ _)
  have htoleft :
      (eVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t)).toReal ≥ q := by
    have hdistxz : edist x z ≤
        eVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t) := by
      simpa [z] using (eVariationOn.edist_le (γ : I → X)
        (s := Set.univ ∩ Icc (0 : I) t) (x := (0 : I)) (y := t)
        ⟨mem_univ _, ⟨le_rfl, ht0⟩⟩ ⟨mem_univ _, ⟨ht.1, le_rfl⟩⟩)
    calc
      q = dist x z := hzdist.symm
      _ = (edist x z).toReal := dist_edist _ _
      _ ≤ (eVariationOn (γ : I → X) (Set.univ ∩ Icc (0 : I) t)).toReal :=
        ENNReal.toReal_mono hleft hdistxz
  have hright_le :
      (eVariationOn (γ : I → X) (Icc t (1 : I))).toReal ≤
        dist x y - q := by
    have htoadd := congrArg ENNReal.toReal hadd
    rw [ENNReal.toReal_add hleft hright] at htoadd
    simp only [univ_inter] at htoadd
    have hIcc : Icc (0 : I) (1 : I) = (Set.univ : Set I) := by
      apply Set.eq_univ_of_forall
      intro u
      exact ⟨u.2.1, u.2.2⟩
    have htotal : (eVariationOn (γ : I → X) (Icc (0 : I) (1 : I))).toReal = dist x y := by
      rw [hIcc]
      exact hγvar
    rw [htotal] at htoadd
    have htoleft' :
        (eVariationOn (γ : I → X) (Icc (0 : I) t)).toReal ≥ q := by
      simpa only [univ_inter] using htoleft
    have htail' :
        (eVariationOn (γ : I → X) (Icc t (1 : I))).toReal =
          (eVariationOn (γ : I → X) (Set.univ ∩ Icc t (1 : I))).toReal := by
      simp only [univ_inter]
    dsimp [q] at *
    linarith [hε_le, htoleft']
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
            dist x y - q := by simpa only [univ_inter] using hright_le
      dsimp [q] at hright_le'
      linarith [hright_le', hty]

theorem pointedHausdorffDist_ballModelNestedRealization_le_sub
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    pointedHausdorffDist (ballModelNestedRealization X r s hr hs hrs) ≤ s - r := by
  unfold pointedHausdorffDist
  apply Metric.hausdorffDist_le_of_mem_dist (sub_nonneg.mpr hrs)
  · rintro z ⟨p, rfl⟩
    let ip := ballModelInclusion X r s hr hs hrs p
    refine ⟨ip, ⟨ip, rfl⟩, ?_⟩
    change dist ip ip ≤ s - r
    exact (dist_self _).le.trans (sub_nonneg.mpr hrs)
  · rintro z ⟨p, rfl⟩
    obtain ⟨q, hq, hpq⟩ :=
      exists_mem_ball_dist_le_sub_of_lengthSpace X.base p.1 hr hrs p.2
    refine ⟨ballModelInclusion X r s hr hs hrs ⟨q, hq⟩, ⟨⟨q, hq⟩, rfl⟩, ?_⟩
    exact hpq

/-! The nested realization now gives the corresponding pointed
Gromov--Hausdorff estimate.  The next two producers are the radius
compatibility interface used by the unbounded convergence definition. -/

/-- **Math.** The pointed GH distance between nested metric balls is bounded
by the width of their radial annulus. -/
theorem pointedGHDistance_ballModel_le_sub
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    pointedGHDistance (ballModel X r hr) (ballModel X s hs) ≤ s - r := by
  exact (pointedGHDistance_le_realization
    (ballModelNestedRealization X r s hr hs hrs)).trans
    (pointedHausdorffDist_ballModelNestedRealization_le_sub
      X r s hr hs hrs)

/-- **Math.** Positive-radius ball models at two arbitrary radii are at
pointed GH distance at most the absolute radial difference. -/
theorem pointedGHDistance_ballModel_le_abs_sub
    (X : BasedMetricSpaceBundle.{u}) [LengthSpace X.carrier]
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    pointedGHDistance (ballModel X r hr) (ballModel X s hs) ≤ |s - r| := by
  by_cases hrs : r ≤ s
  · simpa [abs_of_nonneg (sub_nonneg.mpr hrs)] using
      (pointedGHDistance_ballModel_le_sub X r s hr hs hrs)
  · have hsr : s ≤ r := le_of_not_ge hrs
    rw [pointedGHDistance_symm]
    calc
      pointedGHDistance (ballModel X s hs) (ballModel X r hr) ≤ r - s :=
        pointedGHDistance_ballModel_le_sub X s r hs hr hsr
      _ = |s - r| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hsr)]
        ring

/-- **Math.** If two positive radius sequences in length spaces converge to
the same finite radius, their ball models converge to one another in pointed
GH distance. -/
theorem pointedGHDistance_ballModel_tendsto_zero_of_same_radius_limit
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ k, LengthSpace (X k).carrier]
    (r s : ℕ → ℝ) {R : ℝ}
    (hr : ∀ k, 0 < r k) (hs : ∀ k, 0 < s k)
    (hrlim : Tendsto r atTop (𝓝 R))
    (hslim : Tendsto s atTop (𝓝 R)) :
    Tendsto
      (fun k => pointedGHDistance
        (ballModel (X k) (r k) (hr k))
        (ballModel (X k) (s k) (hs k))) atTop (𝓝 0) := by
  have hdiff : Tendsto (fun k => s k - r k) atTop (𝓝 0) := by
    simpa using hslim.sub hrlim
  have habs : Tendsto (fun k => |s k - r k|) atTop (𝓝 0) := by
    simpa using hdiff.abs
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · intro k
    exact pointedGHDistance_ballModel_le_abs_sub
      (X k) (r k) (s k) (hr k) (hs k)
  · exact habs

/-- **Math.** A pointed GH limit for one positive-radius choice is unchanged
at the distance level when the radii are replaced by another sequence with the
same limit. -/
theorem pointedGHDistance_tendsto_zero_of_ballModel_radius_change
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ k, LengthSpace (X k).carrier]
    (a b : ℕ → ℝ) {R : ℝ}
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (halim : Tendsto a atTop (𝓝 R))
    (hblim : Tendsto b atTop (𝓝 R))
    (Z : FiniteDiameterBasedMetricSpace.{u})
    (hconv : Tendsto
      (fun k => pointedGHDistance (ballModel (X k) (a k) (ha k)) Z)
      atTop (𝓝 0)) :
    Tendsto
      (fun k => pointedGHDistance (ballModel (X k) (b k) (hb k)) Z)
      atTop (𝓝 0) := by
  have hrad := pointedGHDistance_ballModel_tendsto_zero_of_same_radius_limit
    X b a hb ha hblim halim
  have hupper : ∀ k,
      pointedGHDistance (ballModel (X k) (b k) (hb k)) Z ≤
        pointedGHDistance (ballModel (X k) (b k) (hb k))
            (ballModel (X k) (a k) (ha k)) +
          pointedGHDistance (ballModel (X k) (a k) (ha k)) Z := by
    intro k
    exact pointedGHDistance_triangle
      (ballModel (X k) (b k) (hb k))
      (ballModel (X k) (a k) (ha k)) Z
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · exact hupper
  · simpa using hrad.add hconv

/-- **Math.** A pointwise-positive family of metric balls with uniformly
bounded radii has uniformly bounded diameter. -/
theorem uniformlyBoundedDiameter_ballModel_of_radiusBound
    (X : ℕ → BasedMetricSpaceBundle.{u}) (rad : ℕ → ℝ)
    (hpos : ∀ k, 0 < rad k)
    (hrad : ∃ C : ℝ, ∀ k, rad k ≤ C) :
    UniformlyBoundedDiameter
      (fun k => ballModel (X k) (rad k) (hpos k)) := by
  obtain ⟨C, hC⟩ := hrad
  refine ⟨2 * C, ?_⟩
  intro k p q
  change dist p.1 q.1 ≤ 2 * C
  have hp := Metric.mem_ball.mp p.2
  have hq := Metric.mem_ball.mp q.2
  exact le_of_lt <| calc
    dist p.1 q.1 ≤ dist p.1 (X k).base + dist (X k).base q.1 :=
      dist_triangle _ _ _
    _ < rad k + rad k := add_lt_add hp (by simpa [dist_comm] using hq)
    _ ≤ C + C := add_le_add (hC k) (hC k)
    _ = 2 * C := by ring

/-- **Math.** Bounded pointed GH convergence of length-space balls is
independent of the chosen positive radius sequence, provided both radius
sequences have the same limit. -/
theorem pointedGHConverges_ballModel_radius_change
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ k, LengthSpace (X k).carrier]
    (a b : ℕ → ℝ) {R : ℝ}
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (halim : Tendsto a atTop (𝓝 R))
    (hblim : Tendsto b atTop (𝓝 R))
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (hconv : PointedGHConverges
      (fun k => ballModel (X k) (a k) (ha k)) Y) :
    PointedGHConverges
      (fun k => ballModel (X k) (b k) (hb k)) Y := by
  constructor
  · obtain ⟨C, hC⟩ := hblim.bddAbove_range
    apply uniformlyBoundedDiameter_ballModel_of_radiusBound X b hb
    refine ⟨C, ?_⟩
    intro k
    exact hC ⟨k, rfl⟩
  · exact pointedGHDistance_tendsto_zero_of_ballModel_radius_change
      X a b ha hb halim hblim Y hconv.2

/-- **Math.** For a fixed target ball, the bounded convergence clause in the
unbounded pointed GH definition is independent of the positive perturbation
sequence used to approach its radius. -/
theorem pointedGHConvergesUnbounded_radius_change
    (X : ℕ → BasedMetricSpaceBundle.{u}) (Y : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r : ℝ) (hr : 0 < r) (delta epsilon : ℕ → ℝ)
    (hdelta_lim : Tendsto delta atTop (𝓝 0))
    (hepsilon_lim : Tendsto epsilon atTop (𝓝 0))
    (hdelta_pos : ∀ k, 0 < r + delta k)
    (hepsilon_pos : ∀ k, 0 < r + epsilon k)
    (hconv : PointedGHConverges
      (fun k => ballModel (X k) (r + delta k) (hdelta_pos k))
      (ballModel Y r hr)) :
    PointedGHConverges
      (fun k => ballModel (X k) (r + epsilon k) (hepsilon_pos k))
      (ballModel Y r hr) := by
  have hdelta_rad : Tendsto (fun k => r + delta k) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).add hdelta_lim
  have hepsilon_rad : Tendsto (fun k => r + epsilon k) atTop (𝓝 r) := by
    simpa using (tendsto_const_nhds (x := r)).add hepsilon_lim
  exact pointedGHConverges_ballModel_radius_change
    X (fun k => r + delta k) (fun k => r + epsilon k)
    hdelta_pos hepsilon_pos hdelta_rad hepsilon_rad
    (ballModel Y r hr) hconv

end MorganTianLib

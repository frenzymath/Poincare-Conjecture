import MorganTianLib.Ch05.ClosedBallCompatibility

/-!
# Morgan--Tian Chapter 5: distance control for independent radius limits

The compact limits extracted at two radii need not initially be identified by
an isometry.  Nevertheless, if they come from the same length-space sequence,
the nested-ball realization and the pointed-GH triangle inequality give a
sharp annular bound on their distance.  This file records that metric producer
before any choice of cross-radius maps or common ambient is made.
-/

open Set Filter Topology Metric

noncomputable section

namespace MorganTianLib

universe u

/-- **Math.** Independently chosen pointed-GH limits of the same sequence of
length-space closed balls are no farther apart than the width of the radial
annulus.  The two convergence hypotheses retain the original source sequence,
so the result is usable before the targets are put in a common ambient. -/
theorem pointedGHDistance_closedBall_limits_le_sub
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r s : Real) (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s)
    (Lr Ls : FiniteDiameterBasedMetricSpace.{u})
    (hconv_r : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) Lr)
    (hconv_s : PointedGHConverges
      (fun k => closedBallModel (X k) s hs) Ls) :
    pointedGHDistance Lr Ls <= s - r := by
  have hfirst : Tendsto
      (fun k => pointedGHDistance Lr (closedBallModel (X k) r hr))
      atTop (𝓝 0) := by
    simpa only [pointedGHDistance_symm] using hconv_r.2
  have hlast : Tendsto
      (fun k => pointedGHDistance (closedBallModel (X k) s hs) Ls)
      atTop (𝓝 0) := hconv_s.2
  have hright : Tendsto
      (fun k => pointedGHDistance Lr (closedBallModel (X k) r hr) +
        (s - r) + pointedGHDistance (closedBallModel (X k) s hs) Ls)
      atTop (𝓝 (s - r)) := by
    have hconst : Tendsto (fun _ : ℕ => (s - r : Real)) atTop (𝓝 (s - r)) :=
      tendsto_const_nhds
    have hsum := (hfirst.add hconst).add hlast
    simpa [add_assoc] using hsum
  have hupper : ∀ k : ℕ, pointedGHDistance Lr Ls <=
      pointedGHDistance Lr (closedBallModel (X k) r hr) +
        (s - r) + pointedGHDistance (closedBallModel (X k) s hs) Ls := by
    intro k
    have htri₁ := pointedGHDistance_triangle Lr
      (closedBallModel (X k) r hr) (closedBallModel (X k) s hs)
    have htri₂ := pointedGHDistance_triangle Lr
      (closedBallModel (X k) s hs) Ls
    have hmid := pointedGHDistance_closedBallModel_le_sub
      (X k) r s hr hs hrs
    calc
      pointedGHDistance Lr Ls <=
          pointedGHDistance Lr (closedBallModel (X k) s hs) +
            pointedGHDistance (closedBallModel (X k) s hs) Ls := htri₂
      _ <= (pointedGHDistance Lr (closedBallModel (X k) r hr) +
            pointedGHDistance (closedBallModel (X k) r hr)
              (closedBallModel (X k) s hs)) +
            pointedGHDistance (closedBallModel (X k) s hs) Ls := by
        gcongr
      _ <= pointedGHDistance Lr (closedBallModel (X k) r hr) +
            (s - r) + pointedGHDistance (closedBallModel (X k) s hs) Ls := by
        gcongr
  have hle := le_of_tendsto_of_tendsto
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => pointedGHDistance Lr Ls)
      atTop (𝓝 (pointedGHDistance Lr Ls)))
    hright (Filter.Eventually.of_forall hupper)
  simpa using hle

/-- **Math.** A radius-indexed family of compact pointed limits inherits the
absolute radial-difference bound.  This is the symmetric form of
`pointedGHDistance_closedBall_limits_le_sub` and is independent of the choices
of target representatives. -/
theorem pointedGHDistance_closedBall_limits_le_abs_sub
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (radius : ℕ -> Real) (hr : ∀ i, 0 <= radius i)
    (L : ℕ -> FiniteDiameterBasedMetricSpace.{u})
    (hconv : ∀ i, PointedGHConverges
      (fun k => closedBallModel (X k) (radius i) (hr i)) (L i))
    (i j : ℕ) :
    pointedGHDistance (L i) (L j) <= |radius j - radius i| := by
  by_cases hij : radius i <= radius j
  · simpa [abs_of_nonneg (sub_nonneg.mpr hij)] using
      (pointedGHDistance_closedBall_limits_le_sub X (radius i) (radius j)
        (hr i) (hr j) hij (L i) (L j) (hconv i) (hconv j))
  · have hji : radius j <= radius i := le_of_not_ge hij
    rw [pointedGHDistance_symm]
    calc
      pointedGHDistance (L j) (L i) <= radius i - radius j :=
        pointedGHDistance_closedBall_limits_le_sub X (radius j) (radius i)
          (hr j) (hr i) hji (L j) (L i) (hconv j) (hconv i)
      _ = |radius j - radius i| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hji)]
        ring

/-- **Math.** Two compact pointed limits obtained from the same sequence of
equal-radius closed balls have zero pointed Gromov--Hausdorff distance.  This
is the metric identification statement available before choosing an attained
realization or a concrete based isometry. -/
theorem pointedGHDistance_closedBall_limits_eq_zero_of_same_radius
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r : Real) (hr : 0 <= r)
    (L₁ L₂ : FiniteDiameterBasedMetricSpace.{u})
    (hconv₁ : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) L₁)
    (hconv₂ : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) L₂) :
    pointedGHDistance L₁ L₂ = 0 := by
  apply le_antisymm
  · simpa using
      (pointedGHDistance_closedBall_limits_le_sub X r r hr hr le_rfl
        L₁ L₂ hconv₁ hconv₂)
  · exact pointedGHDistance_nonneg L₁ L₂

/-- **Math.** If two selections of a radius-indexed compact-limit family have
asymptotically equal radii, then their pointed Gromov--Hausdorff distance tends
to zero.  The estimate is uniform in the choices of compact target
representatives and therefore supports diagonal compatibility arguments. -/
theorem pointedGHDistance_closedBall_limits_tendsto_zero_of_radius_gap
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (radius : ℕ -> Real) (hr : ∀ i, 0 <= radius i)
    (L : ℕ -> FiniteDiameterBasedMetricSpace.{u})
    (hconv : ∀ i, PointedGHConverges
      (fun k => closedBallModel (X k) (radius i) (hr i)) (L i))
    (a b : ℕ -> ℕ)
    (hgap : Tendsto (fun k => |radius (a k) - radius (b k)|)
      atTop (𝓝 0)) :
    Tendsto (fun k => pointedGHDistance (L (a k)) (L (b k)))
      atTop (𝓝 0) := by
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · intro k
    exact pointedGHDistance_closedBall_limits_le_abs_sub X radius hr L hconv
      (a k) (b k)
  · simpa [abs_sub_comm] using hgap

/-- **Math.** Whenever an error is larger than the radial annulus, the two
compact limit spaces admit an explicit pointed ambient realization below that
error.  This is the approximate cross-radius coupling needed before any
compactness argument can extract a genuine transition isometry. -/
theorem exists_crossRadiusLimit_realization_lt
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r s : Real) (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s)
    (Lr Ls : FiniteDiameterBasedMetricSpace.{u})
    (hconv_r : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) Lr)
    (hconv_s : PointedGHConverges
      (fun k => closedBallModel (X k) s hs) Ls)
    {epsilon : Real} (hepsilon : s - r < epsilon) :
    ∃ R : PointedGHRealization Lr Ls,
      pointedHausdorffDist R < epsilon := by
  have hbound : pointedGHDistance Lr Ls <= s - r :=
    pointedGHDistance_closedBall_limits_le_sub X r s hr hs hrs Lr Ls
      hconv_r hconv_s
  have hgap : 0 < epsilon - pointedGHDistance Lr Ls := by
    linarith
  obtain ⟨R, hR⟩ := exists_pointedGHRealization_lt_add Lr Ls hgap
  refine ⟨R, ?_⟩
  linarith

/-- **Math.** The annular estimate supplies a sequence of pointed realizations
whose Hausdorff errors are uniformly within `1 / (n+1)` of the radial width.
This sequence is an honest approximate coupling; it does not assert that the
infimum is attained. -/
theorem exists_crossRadiusLimit_realization_sequence
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r s : Real) (hr : 0 <= r) (hs : 0 <= s) (hrs : r <= s)
    (Lr Ls : FiniteDiameterBasedMetricSpace.{u})
    (hconv_r : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) Lr)
    (hconv_s : PointedGHConverges
      (fun k => closedBallModel (X k) s hs) Ls) :
    ∃ R : ℕ -> PointedGHRealization Lr Ls,
      ∀ n, pointedHausdorffDist (R n) < (s - r) + 1 / ((n : Real) + 1) := by
  have hexists : ∀ n : ℕ, ∃ R : PointedGHRealization Lr Ls,
      pointedHausdorffDist R < (s - r) + 1 / ((n : Real) + 1) := by
    intro n
    apply exists_crossRadiusLimit_realization_lt X r s hr hs hrs Lr Ls hconv_r hconv_s
    have hn : 0 < (1 / ((n : Real) + 1) : Real) := by
      have hden : 0 < (n : Real) + 1 := by positivity
      exact one_div_pos.mpr hden
    linarith
  choose R hR using hexists
  exact ⟨R, hR⟩

/-- **Math.** At equal radii, the approximate cross-radius realizations can be
chosen with Hausdorff error tending to zero.  This is the realization-level
form of equal-radius limit identification and is suitable input to a later
compact coupling/diagonal extraction. -/
theorem exists_sameRadius_realization_sequence_tendsto_zero
    (X : ℕ -> BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (r : Real) (hr : 0 <= r)
    (L₁ L₂ : FiniteDiameterBasedMetricSpace.{u})
    (hconv₁ : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) L₁)
    (hconv₂ : PointedGHConverges
      (fun k => closedBallModel (X k) r hr) L₂) :
    ∃ R : ℕ -> PointedGHRealization L₁ L₂,
      Tendsto (fun n => pointedHausdorffDist (R n)) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := exists_crossRadiusLimit_realization_sequence
    X r r hr hr le_rfl L₁ L₂ hconv₁ hconv₂
  refine ⟨R, ?_⟩
  apply squeeze_zero
  · intro n
    exact pointedHausdorffDist_nonneg (R n)
  · intro n
    exact (hR n).le
  · simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real))

end MorganTianLib

#print axioms MorganTianLib.pointedGHDistance_closedBall_limits_le_sub
#print axioms MorganTianLib.pointedGHDistance_closedBall_limits_le_abs_sub
#print axioms MorganTianLib.pointedGHDistance_closedBall_limits_eq_zero_of_same_radius
#print axioms MorganTianLib.pointedGHDistance_closedBall_limits_tendsto_zero_of_radius_gap
#print axioms MorganTianLib.exists_crossRadiusLimit_realization_lt
#print axioms MorganTianLib.exists_crossRadiusLimit_realization_sequence
#print axioms MorganTianLib.exists_sameRadius_realization_sequence_tendsto_zero

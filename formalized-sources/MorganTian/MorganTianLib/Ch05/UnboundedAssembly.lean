import MorganTianLib.Ch05.ClosedBallCompatibility

/-!
# Morgan--Tian Chapter 5: unbounded pointed GH assembly

This file connects the finite-radius pointed convergence package to the
unbounded definition.  It records the subsequence and exact-radius transport
needed after the countable diagonal extraction in `Precompactness`.
-/

open Set Filter Topology
open scoped Topology

namespace MorganTianLib

universe u

/-- **Math.** Bounded pointed Gromov--Hausdorff convergence is preserved by a
strictly increasing reindexing. -/
theorem PointedGHConverges.subseq
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (h : PointedGHConverges X Y) (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    PointedGHConverges (fun n => X (φ n)) Y := by
  constructor
  · obtain ⟨C, hC⟩ := h.1
    exact ⟨C, fun n p q => hC (φ n) p q⟩
  · exact h.2.comp hφ.tendsto_atTop

/-! A zero-distance target change is the elementary finite-radius step used
    when independently extracted compact limits are identified with the
    canonical target ball. -/

/-- **Math.** A bounded pointed GH limit may be replaced by a target at zero
pointed GH distance.  The diameter part of the convergence predicate is
unchanged, while the triangle inequality transfers the distance-to-zero
limit. -/
theorem PointedGHConverges.of_zero_distance_target
    {X : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y Z : FiniteDiameterBasedMetricSpace.{u}}
    (h : PointedGHConverges X Y)
    (hzero : pointedGHDistance Y Z = 0) :
    PointedGHConverges X Z := by
  refine ⟨h.1, ?_⟩
  have hupper : ∀ k : ℕ,
      pointedGHDistance (X k) Z ≤
        pointedGHDistance (X k) Y + pointedGHDistance Y Z := by
    intro k
    exact pointedGHDistance_triangle (X k) Y Z
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · exact hupper
  · simpa [hzero] using h.2

/-! A zero-distance change on the varying source side is the companion to the
    target-side transport above.  This is useful when a compact diagonal
    argument produces closed balls while the canonical convergence package is
    stated for their open-ball models. -/

/-- **Math.** A bounded pointed GH convergence remains valid after replacing
the source sequence by pointwise zero-distance models, provided the replacement
sequence has its own uniform diameter bound. -/
theorem PointedGHConverges.of_zero_distance_source
    {X X' : ℕ → FiniteDiameterBasedMetricSpace.{u}}
    {Y : FiniteDiameterBasedMetricSpace.{u}}
    (h : PointedGHConverges X Y)
    (hzero : ∀ k, pointedGHDistance (X' k) (X k) = 0)
    (hbound : UniformlyBoundedDiameter X') :
    PointedGHConverges X' Y := by
  refine ⟨hbound, ?_⟩
  have hupper : ∀ k,
      pointedGHDistance (X' k) Y ≤
        pointedGHDistance (X' k) (X k) +
          pointedGHDistance (X k) Y := by
    intro k
    exact pointedGHDistance_triangle (X' k) (X k) Y
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · exact hupper
  · simpa [hzero] using h.2

/-- **Math.** Radius-wise compact pointed limits assemble into unbounded
pointed GH convergence once each compact limit is identified with the
corresponding target ball at zero pointed distance.  The source-side
perturbation sequences and their positivity remain explicit, so this theorem
does not hide the finite-radius extraction or the target-identification
obligation. -/
theorem pointedGHConvergesUnbounded_of_radius_limits
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (L : ℝ → FiniteDiameterBasedMetricSpace.{u})
    (hsource : ∀ r : ℝ, ∀ _hr : 0 < r,
      ∃ δ : ℕ → ℝ,
        Tendsto δ atTop (𝓝 0) ∧
        ∃ hpos : ∀ k, 0 < r + δ k,
          PointedGHConverges
            (fun k => ballModel (X k) (r + δ k) (hpos k))
            (L r))
    (htarget : ∀ r : ℝ, ∀ hr : 0 < r,
      pointedGHDistance (L r) (ballModel Y r hr) = 0) :
    PointedGHConvergesUnbounded X Y := by
  intro r hr
  obtain ⟨δ, hδ, hconv⟩ := hsource r hr
  obtain ⟨hpos, hlimit⟩ := hconv
  refine ⟨δ, hδ, hpos, ?_⟩
  exact hlimit.of_zero_distance_target (htarget r hr)

/-- **Math.** Radius-wise convergence of positive-radius closed-ball models
transfers to unbounded pointed GH convergence when each compact target is at
zero pointed distance from the corresponding canonical closed ball. -/
theorem pointedGHConvergesUnbounded_of_closedBallModel_limits
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    [LengthSpace Y.carrier]
    (L : ℝ → FiniteDiameterBasedMetricSpace.{u})
    (hsource : ∀ r : ℝ, ∀ _hr : 0 < r,
      ∃ δ : ℕ → ℝ,
        Tendsto δ atTop (𝓝 0) ∧
        ∃ hpos : ∀ k, 0 < r + δ k,
          PointedGHConverges
            (fun k => closedBallModel (X k) (r + δ k) (hpos k).le)
            (L r))
    (htarget : ∀ r : ℝ, ∀ hr : 0 < r,
      pointedGHDistance (L r) (closedBallModel Y r hr.le) = 0) :
    PointedGHConvergesUnbounded X Y := by
  apply pointedGHConvergesUnbounded_of_radius_limits X Y L
  · intro r hr
    obtain ⟨δ, hδ, hpos, hconv⟩ := hsource r hr
    refine ⟨δ, hδ, hpos, ?_⟩
    exact pointedGHConverges_of_closedBallModel_to_ballModel
      X (fun k => r + δ k) hpos (L r) hconv
  · intro r hr
    have hbridge :
        pointedGHDistance (closedBallModel Y r hr.le) (ballModel Y r hr) = 0 :=
      pointedGHDistance_closedBallModel_ballModel_eq_zero Y hr
    have hupper :
        pointedGHDistance (L r) (ballModel Y r hr) ≤
          pointedGHDistance (L r) (closedBallModel Y r hr.le) +
            pointedGHDistance (closedBallModel Y r hr.le) (ballModel Y r hr) :=
      pointedGHDistance_triangle (L r) (closedBallModel Y r hr.le)
        (ballModel Y r hr)
    apply le_antisymm
    · exact hupper.trans_eq (by rw [htarget r hr, hbridge, add_zero])
    · exact pointedGHDistance_nonneg _ _

/-! The next two producers are the closed-ball counterparts of the radius
    change laws in `LengthCone`. -/

/-- **Math.** Positive-radius closed-ball models with uniformly bounded radii
have uniformly bounded diameter. -/
theorem uniformlyBoundedDiameter_closedBallModel_of_radiusBound
    (X : ℕ → BasedMetricSpaceBundle.{u}) (rad : ℕ → ℝ)
    (hpos : ∀ k, 0 < rad k)
    (hrad : ∃ C : ℝ, ∀ k, rad k ≤ C) :
    UniformlyBoundedDiameter
      (fun k => closedBallModel (X k) (rad k) (hpos k).le) := by
  obtain ⟨C, hC⟩ := hrad
  refine ⟨2 * C, ?_⟩
  intro k p q
  change dist p.1 q.1 ≤ 2 * C
  have hp := Metric.mem_closedBall.mp p.2
  have hq := Metric.mem_closedBall.mp q.2
  exact (dist_triangle _ _ _).trans
      (add_le_add hp (by simpa [dist_comm] using hq)) |>.trans
    (by nlinarith [hC k])

/-- **Math.** Bounded pointed GH convergence of positive-radius closed balls is
independent of the chosen radius sequence when the two sequences have the same
finite limit.  The proof transfers through the open-ball radius law and the
zero-distance closed/open bridge. -/
theorem pointedGHConverges_closedBallModel_radius_change
    (X : ℕ → BasedMetricSpaceBundle.{u}) [∀ k, LengthSpace (X k).carrier]
    (a b : ℕ → ℝ) {R : ℝ}
    (ha : ∀ k, 0 < a k) (hb : ∀ k, 0 < b k)
    (halim : Tendsto a atTop (𝓝 R))
    (hblim : Tendsto b atTop (𝓝 R))
    (Y : FiniteDiameterBasedMetricSpace.{u})
    (hconv : PointedGHConverges
      (fun k => closedBallModel (X k) (a k) (ha k).le) Y) :
    PointedGHConverges
      (fun k => closedBallModel (X k) (b k) (hb k).le) Y := by
  have hopenA :
      PointedGHConverges
        (fun k => ballModel (X k) (a k) (ha k)) Y :=
    pointedGHConverges_of_closedBallModel_to_ballModel X a ha Y hconv
  have hopenB :
      PointedGHConverges
        (fun k => ballModel (X k) (b k) (hb k)) Y :=
    pointedGHConverges_ballModel_radius_change
      X a b ha hb halim hblim Y hopenA
  have hzero : ∀ k,
      pointedGHDistance
        (closedBallModel (X k) (b k) (hb k).le)
        (ballModel (X k) (b k) (hb k)) = 0 := by
    intro k
    exact pointedGHDistance_closedBallModel_ballModel_eq_zero
      (X k) (hb k)
  have hbound : UniformlyBoundedDiameter
      (fun k => closedBallModel (X k) (b k) (hb k).le) := by
    obtain ⟨C, hC⟩ := hblim.bddAbove_range
    exact uniformlyBoundedDiameter_closedBallModel_of_radiusBound
      X b hb ⟨C, fun k => hC ⟨k, rfl⟩⟩
  exact PointedGHConverges.of_zero_distance_source hopenB hzero hbound

/-- **Math.** For length-space source and target bundles, unbounded pointed GH
convergence is equivalent to fixed-radius convergence of the compact
closed-ball models.  The source definition is converted through the
closed/open zero-distance bridge in both directions. -/
theorem pointedGHConvergesUnbounded_iff_fixedRadius_closedBall
    (X : ℕ → BasedMetricSpaceBundle.{u}) (Y : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier] [LengthSpace Y.carrier] :
    PointedGHConvergesUnbounded X Y ↔
      ∀ r : ℝ, ∀ hr : 0 < r,
        PointedGHConverges
          (fun k => closedBallModel (X k) r hr.le)
          (closedBallModel Y r hr.le) := by
  constructor
  · intro h r hr
    obtain ⟨delta, hdelta, hpos, hconv⟩ := h r hr
    have hdeltaRad : Tendsto (fun k => r + delta k) atTop (𝓝 r) := by
      simpa using (tendsto_const_nhds (x := r)).add hdelta
    have hopen :
        PointedGHConverges
          (fun k => ballModel (X k) r hr)
          (ballModel Y r hr) :=
      pointedGHConverges_ballModel_radius_change
        X (fun k => r + delta k) (fun _ => r) hpos (fun _ => hr)
        hdeltaRad tendsto_const_nhds (ballModel Y r hr) hconv
    have hzeroSource : ∀ k,
        pointedGHDistance (closedBallModel (X k) r hr.le)
          (ballModel (X k) r hr) = 0 := by
      intro k
      exact pointedGHDistance_closedBallModel_ballModel_eq_zero (X k) hr
    have hbound :
        UniformlyBoundedDiameter
          (fun k => closedBallModel (X k) r hr.le) :=
      uniformlyBoundedDiameter_closedBallModel_of_radiusBound
        X (fun _ => r) (fun _ => hr) ⟨r, fun _ => le_rfl⟩
    have hclosedOpen :
        PointedGHConverges
          (fun k => closedBallModel (X k) r hr.le)
          (ballModel Y r hr) :=
      PointedGHConverges.of_zero_distance_source
        hopen hzeroSource hbound
    have hzeroTarget :
        pointedGHDistance (ballModel Y r hr)
          (closedBallModel Y r hr.le) = 0 := by
      rw [pointedGHDistance_symm]
      exact pointedGHDistance_closedBallModel_ballModel_eq_zero Y hr
    exact hclosedOpen.of_zero_distance_target hzeroTarget
  · intro h r hr
    refine ⟨fun _ : ℕ => (0 : ℝ), tendsto_const_nhds, ?_, ?_⟩
    · exact fun _ => by simpa using hr
    · have hclosed := h r hr
      have hopenClosed :
          PointedGHConverges
            (fun k => ballModel (X k) r hr)
            (closedBallModel Y r hr.le) :=
        pointedGHConverges_of_closedBallModel_to_ballModel
          X (fun _ => r) (fun _ => hr) (closedBallModel Y r hr.le) hclosed
      have hzeroTarget :
          pointedGHDistance (closedBallModel Y r hr.le)
            (ballModel Y r hr) = 0 :=
        pointedGHDistance_closedBallModel_ballModel_eq_zero Y hr
      simpa using hopenClosed.of_zero_distance_target hzeroTarget

/-- **Math.** Unbounded pointed Gromov--Hausdorff convergence is preserved by
the common strictly increasing subsequence produced by a diagonal argument. -/
theorem PointedGHConvergesUnbounded.subseq
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    (h : PointedGHConvergesUnbounded X Y) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) :
    PointedGHConvergesUnbounded (fun n => X (φ n)) Y := by
  intro r hr
  obtain ⟨delta, hdelta, hpos, hconv⟩ := h r hr
  refine ⟨delta ∘ φ, hdelta.comp hφ.tendsto_atTop, fun n => hpos (φ n), ?_⟩
  exact hconv.subseq φ hφ

/-! A ballwise zero-distance change of target preserves the unbounded limit.
This is the global counterpart of `PointedGHConverges.of_zero_distance_target`;
it isolates the target-identification premise needed by the later uniqueness
and compatible-assembly arguments. -/

/-- **Math.** If every positive-radius target ball of `Y` is at pointed GH
distance zero from the corresponding ball of `Z`, then an unbounded pointed
GH limit to `Y` is also an unbounded pointed GH limit to `Z`. -/
theorem PointedGHConvergesUnbounded.of_zero_distance_target
    {X : ℕ → BasedMetricSpaceBundle.{u}}
    {Y Z : BasedMetricSpaceBundle.{u}}
    [∀ k, LengthSpace (X k).carrier]
    (h : PointedGHConvergesUnbounded X Y)
    (hzero : ∀ r : ℝ, ∀ hr : 0 < r,
      pointedGHDistance (ballModel Y r hr) (ballModel Z r hr) = 0) :
    PointedGHConvergesUnbounded X Z := by
  intro r hr
  obtain ⟨delta, hdelta, hpos, hconv⟩ := h r hr
  refine ⟨delta, hdelta, hpos, ?_⟩
  exact hconv.of_zero_distance_target (hzero r hr)

/-- **Math.** For sequences of length spaces, the perturbation sequence in
the source definition of unbounded pointed GH convergence is inessential:
one may use the exact radius at every index. -/
theorem pointedGHConvergesUnbounded_iff_fixedRadius
    (X : ℕ → BasedMetricSpaceBundle.{u}) (Y : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier] :
    PointedGHConvergesUnbounded X Y ↔
      ∀ r : ℝ, ∀ hr : 0 < r,
        PointedGHConverges
          (fun k => ballModel (X k) r hr)
          (ballModel Y r hr) := by
  constructor
  · intro h r hr
    obtain ⟨delta, hdelta, hpos, hconv⟩ := h r hr
    have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds
    have hfixed : ∀ _k : ℕ, 0 < r + (0 : ℝ) := fun _ => by simpa using hr
    simpa using
      (pointedGHConvergesUnbounded_radius_change X Y r hr
        delta (fun _ : ℕ => (0 : ℝ)) hdelta hzero hpos hfixed hconv)
  · intro h r hr
    refine ⟨fun _ : ℕ => (0 : ℝ), tendsto_const_nhds, ?_, ?_⟩
    · exact fun _ => by simpa using hr
    · simpa using h r hr

/-- **Math.** Unbounded pointed GH convergence controls every positive source
radius sequence converging to a fixed target radius.  This is the varying-radius
form used when finite-radius diagonal data is indexed by approximating radii. -/
theorem PointedGHConvergesUnbounded.converges_ballModel_tendsto_radius
    {X : ℕ → BasedMetricSpaceBundle.{u}} {Y : BasedMetricSpaceBundle.{u}}
    [∀ k, LengthSpace (X k).carrier]
    (h : PointedGHConvergesUnbounded X Y)
    (r : ℕ → ℝ) {R : ℝ}
    (hr : ∀ k, 0 < r k) (hR : 0 < R)
    (hrlim : Tendsto r atTop (𝓝 R)) :
    PointedGHConverges
      (fun k => ballModel (X k) (r k) (hr k))
      (ballModel Y R hR) := by
  have hfixed :=
    (pointedGHConvergesUnbounded_iff_fixedRadius X Y).mp h R hR
  exact pointedGHConverges_ballModel_radius_change
    X (fun _ : ℕ => R) r
    (fun _ => hR) hr
    tendsto_const_nhds hrlim
    (ballModel Y R hR) hfixed

/-- **Math.** Two unbounded pointed GH limits have zero pointed distance on
every common finite-radius ball.  This is the ballwise uniqueness consequence
available before the compatible global assembly is constructed. -/
theorem pointedGHDistance_ballModel_eq_zero_of_common_unbounded_limit
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y Z : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    (hY : PointedGHConvergesUnbounded X Y)
    (hZ : PointedGHConvergesUnbounded X Z)
    {r : ℝ} (hr : 0 < r) :
    pointedGHDistance (ballModel Y r hr) (ballModel Z r hr) = 0 := by
  have hYfixed := (pointedGHConvergesUnbounded_iff_fixedRadius X Y).mp hY r hr
  have hZfixed := (pointedGHConvergesUnbounded_iff_fixedRadius X Z).mp hZ r hr
  exact pointedGHDistance_eq_zero_of_common_pointedGH_limit
    (fun k => ballModel (X k) r hr)
    (ballModel Y r hr) (ballModel Z r hr) hYfixed hZfixed

/-- **Math.** Common unbounded pointed GH limits remain indistinguishable when
the radius is allowed to vary: if positive radii `r k` converge to `R`, then
the pointed GH distance between the corresponding target balls tends to zero.
The proof combines the fixed-radius uniqueness statement with the sharp
length-space annular estimates on both target spaces. -/
theorem pointedGHDistance_ballModel_tendsto_zero_of_common_unbounded_limit_varying_radius
    (X : ℕ → BasedMetricSpaceBundle.{u})
    (Y Z : BasedMetricSpaceBundle.{u})
    [∀ k, LengthSpace (X k).carrier]
    [LengthSpace Y.carrier] [LengthSpace Z.carrier]
    (hY : PointedGHConvergesUnbounded X Y)
    (hZ : PointedGHConvergesUnbounded X Z)
    (r : ℕ → ℝ) {R : ℝ}
    (hr : ∀ k, 0 < r k) (hR : 0 < R)
    (hrlim : Tendsto r atTop (𝓝 R)) :
    Tendsto
      (fun k => pointedGHDistance
        (ballModel Y (r k) (hr k))
        (ballModel Z (r k) (hr k))) atTop (𝓝 0) := by
  have hYR :
      Tendsto
        (fun k => pointedGHDistance
          (ballModel Y (r k) (hr k))
          (ballModel Y R hR)) atTop (𝓝 0) := by
    have hdiff : Tendsto (fun k => |R - r k|) atTop (𝓝 0) := by
      have hsub : Tendsto (fun k => R - r k) atTop (𝓝 (R - R)) :=
        tendsto_const_nhds.sub hrlim
      simpa using hsub.abs
    apply squeeze_zero
    · intro k
      exact pointedGHDistance_nonneg _ _
    · intro k
      exact pointedGHDistance_ballModel_le_abs_sub
        Y (r k) R (hr k) hR
    · exact hdiff
  have hZR :
      Tendsto
        (fun k => pointedGHDistance
          (ballModel Z R hR)
          (ballModel Z (r k) (hr k))) atTop (𝓝 0) := by
    have hdiff : Tendsto (fun k => |r k - R|) atTop (𝓝 0) := by
      have hsub : Tendsto (fun k => r k - R) atTop (𝓝 (R - R)) :=
        hrlim.sub tendsto_const_nhds
      simpa using hsub.abs
    apply squeeze_zero
    · intro k
      exact pointedGHDistance_nonneg _ _
    · intro k
      exact pointedGHDistance_ballModel_le_abs_sub
        Z R (r k) hR (hr k)
    · exact hdiff
  have hYZ :
      pointedGHDistance (ballModel Y R hR) (ballModel Z R hR) = 0 :=
    pointedGHDistance_ballModel_eq_zero_of_common_unbounded_limit
      X Y Z hY hZ hR
  have hupper : ∀ k,
      pointedGHDistance
          (ballModel Y (r k) (hr k))
          (ballModel Z (r k) (hr k)) ≤
        pointedGHDistance
            (ballModel Y (r k) (hr k))
            (ballModel Y R hR) +
          pointedGHDistance
            (ballModel Z R hR)
            (ballModel Z (r k) (hr k)) := by
    intro k
    calc
      pointedGHDistance
          (ballModel Y (r k) (hr k))
          (ballModel Z (r k) (hr k)) ≤
        pointedGHDistance
            (ballModel Y (r k) (hr k))
            (ballModel Y R hR) +
          pointedGHDistance
            (ballModel Y R hR)
            (ballModel Z (r k) (hr k)) :=
        pointedGHDistance_triangle _ _ _
      _ ≤
        pointedGHDistance
            (ballModel Y (r k) (hr k))
            (ballModel Y R hR) +
          (pointedGHDistance (ballModel Y R hR) (ballModel Z R hR) +
            pointedGHDistance
              (ballModel Z R hR)
              (ballModel Z (r k) (hr k))) := by
        gcongr
        exact pointedGHDistance_triangle _ _ _
      _ = _ := by rw [hYZ]; ring
  have hsum :
      Tendsto
        (fun k =>
          pointedGHDistance
              (ballModel Y (r k) (hr k))
              (ballModel Y R hR) +
            pointedGHDistance
              (ballModel Z R hR)
              (ballModel Z (r k) (hr k))) atTop (𝓝 0) := by
    simpa using hYR.add hZR
  apply squeeze_zero
  · intro k
    exact pointedGHDistance_nonneg _ _
  · exact hupper
  · exact hsum

/-- **Math.** A constant sequence of length-space bundles converges to its
own unbounded pointed GH limit. -/
theorem pointedGHConvergesUnbounded_const
    (Y : BasedMetricSpaceBundle.{u}) [LengthSpace Y.carrier] :
    PointedGHConvergesUnbounded (fun _ : ℕ => Y) Y := by
  intro r hr
  refine ⟨fun _ : ℕ => (0 : ℝ), tendsto_const_nhds, ?_, ?_⟩
  · exact fun _ => by simpa using hr
  · constructor
    · have hbound : UniformlyBoundedDiameter
          (fun _ : ℕ => ballModel Y r hr) :=
        uniformlyBoundedDiameter_ballModel_of_radiusBound
          (fun _ : ℕ => Y) (fun _ : ℕ => r) (fun _ => hr)
          ⟨r, fun _ => le_rfl⟩
      simpa using hbound
    · have hself : pointedGHDistance (ballModel Y r hr) (ballModel Y r hr) = 0 :=
        pointedGHDistance_self (ballModel Y r hr)
      simpa using hself

end MorganTianLib

#print axioms MorganTianLib.pointedGHDistance_ballModel_eq_zero_of_common_unbounded_limit
#print axioms MorganTianLib.pointedGHDistance_ballModel_tendsto_zero_of_common_unbounded_limit_varying_radius
#print axioms MorganTianLib.pointedGHConvergesUnbounded_const
#print axioms MorganTianLib.PointedGHConverges.of_zero_distance_source
#print axioms MorganTianLib.uniformlyBoundedDiameter_closedBallModel_of_radiusBound
#print axioms MorganTianLib.pointedGHConverges_closedBallModel_radius_change
#print axioms MorganTianLib.pointedGHConvergesUnbounded_iff_fixedRadius_closedBall

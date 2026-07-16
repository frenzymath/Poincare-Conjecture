import EvansLib.Ch02.Harmonic
import Mathlib.MeasureTheory.Integral.Average

/-!
# Evans, Ch. 2 §2.2.2–§2.2.3 — Consequences of the mean-value property

Evans, *Partial Differential Equations* (2nd ed.), §2.2 derives a whole sequence of
properties of harmonic functions *from the mean-value formulas* (§2.2.2). This file
formalizes that downstream chain in the form Evans actually uses it: taking the
**(solid-ball) mean-value property** as the working hypothesis.

The mean-value property itself — that a harmonic function equals its ball average
(Evans Thm 2, `thm:mean-value-formulas-laplace`) — is the one step that requires the
divergence theorem on a ball (Green's identity), which current mathlib provides only
for boxes. We therefore package the property as a predicate `HasBallMeanValueProperty`
and prove the maximum-principle / uniqueness / Harnack consequences from it; the bridge
`harmonic ⟹ HasBallMeanValueProperty` is `thm:mean-value-formulas-laplace`, still open.

Everything here is stated over `EuclideanSpace ℝ (Fin n)` with the Lebesgue `volume`,
using mathlib's ball average `⨍ y in Metric.ball x r, u y`, so no surface measure is
needed. Results proved:

* `EvansLib.eqOn_ball_of_isMaxOn` — the analytic core: if `u` has the ball MVP and
  attains its maximum over a ball at the centre, then `u` is constant on that ball.
* `EvansLib.eqOn_of_isPreconnected_of_isMaxOn` — **strong maximum principle (ii)**
  (`thm:strong-maximum-principle-laplace`): an interior maximum on a connected open set
  forces `u` to be constant.
* `EvansLib.exists_frontier_isMaxOn` — **maximum principle (i)**: on a bounded open set
  the maximum over the closure is attained on the boundary.
* `EvansLib.eqOn_closure_of_eqOn_frontier` — **uniqueness for the Dirichlet problem**
  (`thm:uniqueness-poisson-dirichlet`).

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.2–§2.2.3.
-/

open scoped Real ContDiff
open MeasureTheory Metric Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- **The (solid-ball) mean-value property** of Evans §2.2.2. A function `u` has the
mean-value property on `U` when it equals its average over every ball whose closure
lies in `U`:
`u x = ⨍_{B(x,r)} u dy` for all `B̄(x,r) ⊆ U`, `r > 0`.
Evans's mean-value formula (`thm:mean-value-formulas-laplace`) asserts every harmonic
function has this property; that implication needs Green's identity and is left open. -/
def HasBallMeanValueProperty (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (U : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ ⦃x : EuclideanSpace ℝ (Fin n)⦄ ⦃r : ℝ⦄, 0 < r → closedBall x r ⊆ U →
    u x = ⨍ y in ball x r, u y

/-! ## Basic measure facts on Euclidean balls -/

/-- The Lebesgue measure of a positive-radius ball in `ℝⁿ` is a strictly positive real. -/
lemma measureReal_ball_pos {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) :
    0 < volume.real (ball x r) := by
  rw [Measure.real]
  exact ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

instance (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

/-- A function continuous on a set is integrable on any ball whose closed ball lies in
the set. -/
lemma integrableOn_ball_of_continuousOn {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hcont : ContinuousOn u U)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hball : closedBall x r ⊆ U) :
    IntegrableOn u (ball x r) volume :=
  ((hcont.mono hball).integrableOn_compact (isCompact_closedBall x r)).mono_set
    ball_subset_closedBall

/-! ## The analytic core: a maximum at the centre forces constancy on the ball -/

/-- **Core lemma.** If `u` has the ball mean-value property and is continuous on `U`,
and `u` attains its maximum over a ball `B(x,r) ⊆ U` at the centre `x`, then `u ≡ u x`
throughout `B(x,r)`.

This is the engine behind the strong maximum principle: the average over the ball
equals the centre value, and a nonnegative continuous function (`u x - u`) with zero
integral over the (open, positive-measure) ball must vanish there. -/
lemma eqOn_ball_of_isMaxOn {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    (hcont : ContinuousOn u U) {x : EuclideanSpace ℝ (Fin n)} {r : ℝ}
    (hr : 0 < r) (hball : closedBall x r ⊆ U)
    (hmax : ∀ y ∈ ball x r, u y ≤ u x) :
    ∀ y ∈ ball x r, u y = u x := by
  have hRpos : 0 < volume.real (ball x r) := measureReal_ball_pos hr
  have hint : IntegrableOn u (ball x r) volume :=
    integrableOn_ball_of_continuousOn hcont hball
  -- average = centre value, unfolded to an integral identity
  have havg : u x = (volume.real (ball x r))⁻¹ • ∫ y in ball x r, u y := by
    rw [← setAverage_eq]; exact hu hr hball
  have hI : ∫ y in ball x r, u y = volume.real (ball x r) * u x := by
    have h : (volume.real (ball x r))⁻¹ * ∫ y in ball x r, u y = u x := by
      rw [← smul_eq_mul, ← havg]
    rwa [inv_mul_eq_iff_eq_mul₀ hRpos.ne'] at h
  -- the nonnegative gap `u x - u` integrates to zero over the ball
  have hgint : Integrable (fun y => u x - u y) (volume.restrict (ball x r)) :=
    (integrable_const (u x)).sub hint
  have hzero : ∫ y in ball x r, (u x - u y) = 0 := by
    rw [integral_sub (integrable_const (u x)) hint, setIntegral_const, hI, smul_eq_mul]
    ring
  have hnonneg : 0 ≤ᵐ[volume.restrict (ball x r)] fun y => u x - u y :=
    (ae_restrict_iff' measurableSet_ball).2 <|
      ae_of_all _ fun y hy => sub_nonneg.2 (hmax y hy)
  have hae0 : (fun y => u x - u y) =ᵐ[volume.restrict (ball x r)] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hgint).1 hzero
  have hae : u =ᵐ[volume.restrict (ball x r)] fun _ => u x := by
    filter_upwards [hae0] with y hy
    have hy' : u x - u y = 0 := hy
    linarith
  have hcontBall : ContinuousOn u (ball x r) :=
    hcont.mono (ball_subset_closedBall.trans hball)
  exact Measure.eqOn_open_of_ae_eq hae isOpen_ball hcontBall continuousOn_const

/-! ## Strong maximum principle (interior maximum ⟹ constant) -/

/-- **Strong maximum principle, Evans §2.2.3 Thm 4(ii)**
(`thm:strong-maximum-principle-laplace`). If `u` has the ball mean-value property and is
continuous on a *connected* open set `U`, and attains its maximum over `U` at some
interior point `x₀`, then `u` is constant on `U`. -/
theorem eqOn_of_isPreconnected_of_isMaxOn {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    (hcont : ContinuousOn u U) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    {x₀ : EuclideanSpace ℝ (Fin n)} (hx₀ : x₀ ∈ U) (hmax : ∀ y ∈ U, u y ≤ u x₀) :
    ∀ y ∈ U, u y = u x₀ := by
  haveI : PreconnectedSpace U := Subtype.preconnectedSpace hUconn
  -- the argmax set inside `U`, as a subset of the subspace; it is clopen and nonempty
  set S : Set U := {p | u (p : EuclideanSpace ℝ (Fin n)) = u x₀} with hS
  have hScl : IsClosed S :=
    isClosed_eq (hcont.restrict) continuous_const
  have hSop : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro p (hp : u (p : EuclideanSpace ℝ (Fin n)) = u x₀)
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hUopen _ p.2
    obtain ⟨ρ, hρpos, hρsub⟩ :
        ∃ ρ, 0 < ρ ∧ closedBall (p : EuclideanSpace ℝ (Fin n)) ρ ⊆ U :=
      ⟨r / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hrsub⟩
    have hmaxBall : ∀ y ∈ ball (p : EuclideanSpace ℝ (Fin n)) ρ, u y ≤ u p := by
      intro y hy
      rw [hp]; exact hmax y (hρsub (ball_subset_closedBall hy))
    have hconstBall := eqOn_ball_of_isMaxOn hu hcont hρpos hρsub hmaxBall
    refine mem_nhds_iff.2 ⟨(fun q : U => (q : EuclideanSpace ℝ (Fin n))) ⁻¹'
      ball (p : EuclideanSpace ℝ (Fin n)) ρ, ?_, isOpen_ball.preimage continuous_subtype_val,
      mem_preimage.2 (mem_ball_self hρpos)⟩
    rintro q hq
    show u (q : EuclideanSpace ℝ (Fin n)) = u x₀
    rw [hconstBall _ hq, hp]
  have hne : S.Nonempty := ⟨⟨x₀, hx₀⟩, rfl⟩
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hScl, hSop⟩ hne
  intro y hy
  have : (⟨y, hy⟩ : U) ∈ S := by rw [hSuniv]; exact mem_univ _
  exact this

/-! ## Maximum principle (i): maximum over the closure is attained on the boundary -/

/-- **Maximum principle, Evans §2.2.3 Thm 4(i)** (`thm:strong-maximum-principle-laplace`).
If `u` has the ball mean-value property on a bounded, nonempty open set `U` and is
continuous on `closure U`, then the maximum of `u` over `closure U` is attained at a
boundary point. The hypothesis `Nonempty (Fin n)` (nonzero dimension) holds throughout
Evans's Laplace chapter and makes the ambient space noncompact. -/
theorem exists_frontier_isMaxOn [Nonempty (Fin n)] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    (hcont : ContinuousOn u (closure U)) (hUopen : IsOpen U)
    (hUbdd : Bornology.IsBounded U) (hUne : U.Nonempty) :
    ∃ z ∈ frontier U, ∀ y ∈ closure U, u y ≤ u z := by
  have hKcomp : IsCompact (closure U) := hUbdd.isCompact_closure
  obtain ⟨z, hzK, hzmax⟩ := hKcomp.exists_isMaxOn hUne.closure hcont
  rw [isMaxOn_iff] at hzmax
  set M : ℝ := u z with hM
  set A : Set (EuclideanSpace ℝ (Fin n)) := closure U ∩ {y | u y = M} with hA
  have hAsub : A ⊆ closure U := inter_subset_left
  have hcontU : ContinuousOn u U := hcont.mono subset_closure
  have hAcl : IsClosed A :=
    hcont.preimage_isClosed_of_isClosed isClosed_closure isClosed_singleton
  have hAne : A.Nonempty := ⟨z, hzK, rfl⟩
  have hAbdd : Bornology.IsBounded A := hUbdd.closure.subset hAsub
  -- at any point of `A` lying in `U`, the ball lemma forces `u ≡ M` on a whole ball
  have keyOpen : ∀ y ∈ A, y ∈ U → ∃ ρ, 0 < ρ ∧ ball y ρ ⊆ A := by
    rintro y ⟨hyK, (hyM : u y = M)⟩ hyU
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hUopen _ hyU
    have hρsub : closedBall y (r / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hrsub
    have hmaxBall : ∀ w ∈ ball y (r / 2), u w ≤ u y := by
      intro w hw
      rw [hyM]; exact hzmax _ (subset_closure (hρsub (ball_subset_closedBall hw)))
    have hconst := eqOn_ball_of_isMaxOn hu hcontU (by positivity) hρsub hmaxBall
    exact ⟨r / 2, by positivity, fun w hw =>
      ⟨subset_closure (hρsub (ball_subset_closedBall hw)),
        show u w = M by rw [hconst w hw, hyM]⟩⟩
  -- the maximum set meets the boundary
  have hmeet : (A ∩ frontier U).Nonempty := by
    by_contra hempty
    rw [not_nonempty_iff_eq_empty] at hempty
    have hAU : A ⊆ U := by
      intro y hy
      by_contra hyU
      have hyf : y ∈ frontier U := ⟨hAsub hy, by rw [hUopen.interior_eq]; exact hyU⟩
      have hcontra : y ∈ (∅ : Set (EuclideanSpace ℝ (Fin n))) := hempty ▸ ⟨hy, hyf⟩
      simp at hcontra
    have hAop : IsOpen A := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨ρ, hρ, hsub⟩ := keyOpen y hy (hAU hy)
      exact Filter.mem_of_superset (ball_mem_nhds y hρ) hsub
    have hAuniv : A = univ := IsClopen.eq_univ ⟨hAcl, hAop⟩ hAne
    rw [hAuniv] at hAbdd
    exact absurd (compactSpace_iff_isBounded_univ.2 hAbdd) (by
      rw [not_compactSpace_iff]; infer_instance)
  obtain ⟨w, hwA, hwf⟩ := hmeet
  exact ⟨w, hwf, fun y hy => by rw [hwA.2]; exact hzmax y hy⟩

/-! ## Linearity of the mean-value property, and Dirichlet uniqueness -/

/-- The ball mean-value property is closed under subtraction (for continuous functions,
so that ball averages split). -/
lemma HasBallMeanValueProperty.sub {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    (hv : HasBallMeanValueProperty v U) (hcu : ContinuousOn u U) (hcv : ContinuousOn v U) :
    HasBallMeanValueProperty (fun y => u y - v y) U := by
  intro x r hr hball
  have hiu := integrableOn_ball_of_continuousOn hcu hball
  have hiv := integrableOn_ball_of_continuousOn hcv hball
  have hgu := hu hr hball
  have hgv := hv hr hball
  show u x - v x = ⨍ y in ball x r, (u y - v y)
  rw [setAverage_eq, integral_sub hiu hiv, smul_sub, ← setAverage_eq, ← setAverage_eq,
    ← hgu, ← hgv]

/-- **Uniqueness for the Dirichlet problem, Evans §2.2.3 Thm 5**
(`thm:uniqueness-poisson-dirichlet`). Two functions with the ball mean-value property on
a bounded open set `U`, continuous up to the closure and agreeing on the boundary
`frontier U`, agree on all of `closure U`. Applied to two solutions of `-Δu = f`, `u = g`
on `∂U` (both harmonic ⟹ both have the MVP, and their boundary data coincide), this is
the uniqueness statement. -/
theorem eqOn_closure_of_eqOn_frontier [Nonempty (Fin n)]
    {u v : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hu : HasBallMeanValueProperty u U) (hv : HasBallMeanValueProperty v U)
    (hcu : ContinuousOn u (closure U)) (hcv : ContinuousOn v (closure U))
    (hUopen : IsOpen U) (hUbdd : Bornology.IsBounded U)
    (hbdry : ∀ z ∈ frontier U, u z = v z) :
    ∀ y ∈ closure U, u y = v y := by
  rcases U.eq_empty_or_nonempty with hUe | hUne
  · subst hUe; simp
  -- `u - v` has the MVP, is continuous up to the closure, and vanishes on the boundary
  obtain ⟨z1, hz1f, hz1max⟩ := exists_frontier_isMaxOn
    (HasBallMeanValueProperty.sub hu hv (hcu.mono subset_closure) (hcv.mono subset_closure))
    (hcu.sub hcv) hUopen hUbdd hUne
  obtain ⟨z2, hz2f, hz2max⟩ := exists_frontier_isMaxOn
    (HasBallMeanValueProperty.sub hv hu (hcv.mono subset_closure) (hcu.mono subset_closure))
    (hcv.sub hcu) hUopen hUbdd hUne
  intro y hy
  have h1 : u y - v y ≤ 0 := by
    have hm := hz1max y hy
    have hz : u z1 - v z1 = 0 := by rw [hbdry z1 hz1f]; ring
    simpa using hm.trans hz.le
  have h2 : v y - u y ≤ 0 := by
    have hm := hz2max y hy
    have hz : v z2 - u z2 = 0 := by rw [← hbdry z2 hz2f]; ring
    simpa using hm.trans hz.le
  linarith

/-! ## Harnack's inequality (local pointwise form) -/

/-- Ratio of Euclidean ball volumes: the ball of radius `2r` has `2ⁿ` times the volume
of a ball of radius `r`. -/
lemma measureReal_ball_two_mul [Nonempty (Fin n)] (x y : EuclideanSpace ℝ (Fin n))
    (r : ℝ) :
    volume.real (ball x (2 * r)) = 2 ^ n * volume.real (ball y r) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hmul := Measure.addHaar_ball_mul (volume (α := EuclideanSpace ℝ (Fin n)))
    x (show (0 : ℝ) ≤ 2 by norm_num) r
  rw [hfr] at hmul
  have hcenter : volume (ball (0 : EuclideanSpace ℝ (Fin n)) r) = volume (ball y r) :=
    (Measure.addHaar_ball_center volume y r).symm
  rw [hcenter] at hmul
  have : volume.real (ball x (2 * r)) = (ENNReal.ofReal (2 ^ n) * volume (ball y r)).toReal := by
    rw [Measure.real, hmul]
  rw [this, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), Measure.real]

/-- **Harnack's inequality, local form** (`thm:harnacks-inequality`, Evans §2.2.3 Thm 11
core estimate). For a nonnegative function with the ball mean-value property, values at
nearby points are comparable: if `dist x y ≤ r` and the ball `B̄(x,2r) ⊆ U`, then
`u y ≤ 2ⁿ u x`. Iterating this along a chain of balls gives the global comparability
`sup_V u ≤ C inf_V u` of Harnack's inequality. -/
theorem harnack_local [Nonempty (Fin n)] {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {U : Set (EuclideanSpace ℝ (Fin n))} (hu : HasBallMeanValueProperty u U)
    (hcont : ContinuousOn u U) (hunonneg : ∀ z ∈ U, 0 ≤ u z)
    {x y : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hxy : dist x y ≤ r)
    (hxU : closedBall x (2 * r) ⊆ U) :
    u y ≤ 2 ^ n * u x := by
  -- the small ball around `y` sits inside the big ball around `x`, hence inside `U`
  have hsub_closed : closedBall y r ⊆ closedBall x (2 * r) :=
    closedBall_subset_closedBall' (by rw [dist_comm] at hxy; linarith)
  have hyU : closedBall y r ⊆ U := hsub_closed.trans hxU
  have hsub_open : ball y r ⊆ ball x (2 * r) :=
    ball_subset_ball' (by rw [dist_comm] at hxy; linarith)
  -- positivity of the two ball volumes
  have hVy : 0 < volume.real (ball y r) := measureReal_ball_pos hr
  have hVx : 0 < volume.real (ball x (2 * r)) := measureReal_ball_pos (by linarith)
  -- the average identities
  have huy : u y = (volume.real (ball y r))⁻¹ * ∫ w in ball y r, u w := by
    rw [← smul_eq_mul, ← setAverage_eq]; exact hu hr hyU
  have hux : u x = (volume.real (ball x (2 * r)))⁻¹ * ∫ w in ball x (2 * r), u w := by
    rw [← smul_eq_mul, ← setAverage_eq]; exact hu (by linarith) hxU
  -- integral over the bigger ball dominates that over the smaller
  have hint : IntegrableOn u (ball x (2 * r)) volume :=
    integrableOn_ball_of_continuousOn hcont hxU
  have hnn : 0 ≤ᵐ[volume.restrict (ball x (2 * r))] u :=
    (ae_restrict_iff' measurableSet_ball).2 <|
      ae_of_all _ fun w hw => hunonneg w (hxU (ball_subset_closedBall hw))
  have hmono : ∫ w in ball y r, u w ≤ ∫ w in ball x (2 * r), u w :=
    setIntegral_mono_set hint hnn hsub_open.eventuallyLE
  -- assemble: `2ⁿ u x = Vy⁻¹ * (∫ over big ball) ≥ Vy⁻¹ * (∫ over small ball) = u y`
  have hV := measureReal_ball_two_mul x y r
  have key : 2 ^ n * u x = (volume.real (ball y r))⁻¹ * ∫ w in ball x (2 * r), u w := by
    rw [hux, hV]
    field_simp
  rw [key, huy]
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

end EvansLib

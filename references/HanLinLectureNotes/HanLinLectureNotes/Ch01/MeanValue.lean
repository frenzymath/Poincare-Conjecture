import HanLinLectureNotes.Basic

/-!
# Han--Lin Chapter 1: mean value properties

This module develops the maximum principle directly from the solid-ball mean
value property.  The spherical predicate uses the surface measure induced by
Lebesgue measure on the unit sphere; the ball predicate uses Lebesgue averages.
-/

open MeasureTheory Metric Set

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- The spherical mean value property on every closed ball contained in `Omega`. -/
def HasSphericalMeanValueProperty [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (Omega : Set (EuclideanSpace Real (Fin n))) : Prop :=
  forall {x : EuclideanSpace Real (Fin n)} {r : Real}, 0 < r ->
    closedBall x r ⊆ Omega ->
      u x = average
        (volume.toSphere : Measure (sphere (0 : EuclideanSpace Real (Fin n)) 1))
        (fun omega : sphere (0 : EuclideanSpace Real (Fin n)) 1 =>
          u (x + r • (omega : EuclideanSpace Real (Fin n))))

/-- The solid-ball mean value property on every closed ball contained in `Omega`. -/
def HasBallMeanValueProperty
    (u : EuclideanSpace Real (Fin n) -> Real)
    (Omega : Set (EuclideanSpace Real (Fin n))) : Prop :=
  forall {x : EuclideanSpace Real (Fin n)} {r : Real}, 0 < r ->
    closedBall x r ⊆ Omega -> u x = average (volume.restrict (ball x r)) u

/-- A continuous function has the mean value properties when it has both the
spherical and solid-ball identities. -/
def HasMeanValueProperties [Nonempty (Fin n)]
    (u : EuclideanSpace Real (Fin n) -> Real)
    (Omega : Set (EuclideanSpace Real (Fin n))) : Prop :=
  ContinuousOn u Omega ∧ HasSphericalMeanValueProperty u Omega ∧
    HasBallMeanValueProperty u Omega

lemma measureReal_ball_pos {x : EuclideanSpace Real (Fin n)} {r : Real}
    (hr : 0 < r) : 0 < volume.real (ball x r) := by
  rw [Measure.real]
  exact ENNReal.toReal_pos (measure_ball_pos volume x hr).ne' measure_ball_lt_top.ne

instance (x : EuclideanSpace Real (Fin n)) (r : Real) :
    IsFiniteMeasure (volume.restrict (ball x r)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩

lemma integrableOn_ball_of_continuousOn
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))} (hu : ContinuousOn u Omega)
    {x : EuclideanSpace Real (Fin n)} {r : Real} (hball : closedBall x r ⊆ Omega) :
    IntegrableOn u (ball x r) volume :=
  ((hu.mono hball).integrableOn_compact (isCompact_closedBall x r)).mono_set
    ball_subset_closedBall

/-- A maximum at the center of an admissible ball forces equality throughout
that ball. -/
lemma eqOn_ball_of_isMaxOn
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))}
    (hu : HasBallMeanValueProperty u Omega) (hcont : ContinuousOn u Omega)
    {x : EuclideanSpace Real (Fin n)} {r : Real} (hr : 0 < r)
    (hball : closedBall x r ⊆ Omega)
    (hmax : forall y, y ∈ ball x r -> u y ≤ u x) :
    forall y, y ∈ ball x r -> u y = u x := by
  have hRpos : 0 < volume.real (ball x r) := measureReal_ball_pos hr
  have hint : IntegrableOn u (ball x r) volume :=
    integrableOn_ball_of_continuousOn hcont hball
  have havg : u x = (volume.real (ball x r))⁻¹ • ∫ y in ball x r, u y := by
    rw [← setAverage_eq]
    exact hu hr hball
  have hI : ∫ y in ball x r, u y = volume.real (ball x r) * u x := by
    have h : (volume.real (ball x r))⁻¹ * ∫ y in ball x r, u y = u x := by
      rw [← smul_eq_mul, ← havg]
    rwa [inv_mul_eq_iff_eq_mul₀ hRpos.ne'] at h
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

/-- On a connected domain, an interior maximum of a continuous function with
the ball mean value property forces constancy. -/
theorem eqOn_of_isPreconnected_of_isMaxOn
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))}
    (hu : HasBallMeanValueProperty u Omega) (hcont : ContinuousOn u Omega)
    (hopen : IsOpen Omega) (hconn : IsPreconnected Omega)
    {x0 : EuclideanSpace Real (Fin n)} (hx0 : x0 ∈ Omega)
    (hmax : forall y, y ∈ Omega -> u y ≤ u x0) :
    EqOn u (fun _ => u x0) Omega := by
  let S : Set Omega := {p | u (p : EuclideanSpace Real (Fin n)) = u x0}
  have hSclosed : IsClosed S := isClosed_eq hcont.restrict continuous_const
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro p (hp : u (p : EuclideanSpace Real (Fin n)) = u x0)
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.1 hopen _ p.2
    have hhalf : 0 < r / 2 := by linarith
    have hsub : closedBall (p : EuclideanSpace Real (Fin n)) (r / 2) ⊆ Omega :=
      (closedBall_subset_ball (by linarith)).trans hrsub
    have hmaxBall : forall y,
        y ∈ ball (p : EuclideanSpace Real (Fin n)) (r / 2) -> u y ≤ u p := by
      intro y hy
      rw [hp]
      exact hmax y (hsub (ball_subset_closedBall hy))
    have hconst := eqOn_ball_of_isMaxOn hu hcont hhalf hsub hmaxBall
    refine mem_nhds_iff.2 ⟨(fun q : Omega =>
      (q : EuclideanSpace Real (Fin n))) ⁻¹' ball p (r / 2), ?_,
      isOpen_ball.preimage continuous_subtype_val, mem_preimage.2 (mem_ball_self hhalf)⟩
    rintro q hq
    show u (q : EuclideanSpace Real (Fin n)) = u x0
    rw [hconst _ hq, hp]
  have hSne : S.Nonempty := ⟨⟨x0, hx0⟩, rfl⟩
  have hSuniv : S = univ := by
    letI : PreconnectedSpace Omega := Subtype.preconnectedSpace hconn
    exact IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSne
  intro y hy
  have : (⟨y, hy⟩ : Omega) ∈ S := by rw [hSuniv]; exact mem_univ _
  exact this

lemma HasBallMeanValueProperty.neg
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))}
    (hu : HasBallMeanValueProperty u Omega) :
    HasBallMeanValueProperty (fun x => -u x) Omega := by
  intro x r hr hball
  simpa [average_neg] using congrArg Neg.neg (hu hr hball)

/-- Han--Lin Theorem 1.4.  Unless the function is constant, every attained
maximum and minimum on the closure lies on the boundary. -/
theorem meanValue_extrema_mem_frontier_of_not_constant [Nonempty (Fin n)]
    {u : EuclideanSpace Real (Fin n) -> Real}
    {Omega : Set (EuclideanSpace Real (Fin n))}
    (hu : HasMeanValueProperties u Omega)
    (hcont : ContinuousOn u (closure Omega))
    (hopen : IsOpen Omega) (hconn : IsPreconnected Omega)
    (hnonconst : ¬ ∃ c : Real, EqOn u (fun _ => c) Omega) :
    (forall x, x ∈ closure Omega -> (forall y, y ∈ closure Omega -> u y ≤ u x) ->
      x ∈ frontier Omega) ∧
    (forall x, x ∈ closure Omega -> (forall y, y ∈ closure Omega -> u x ≤ u y) ->
      x ∈ frontier Omega) := by
  constructor
  · intro x hx hmax
    have hxnot : x ∉ Omega := by
      intro hxOmega
      have hconst := eqOn_of_isPreconnected_of_isMaxOn hu.2.2
        (hcont.mono subset_closure) hopen hconn hxOmega
        (fun y hy => hmax y (subset_closure hy))
      exact hnonconst ⟨u x, hconst⟩
    exact ⟨hx, by rw [hopen.interior_eq]; exact hxnot⟩
  · intro x hx hmin
    have hxnot : x ∉ Omega := by
      intro hxOmega
      have hconstNeg := eqOn_of_isPreconnected_of_isMaxOn
        (HasBallMeanValueProperty.neg hu.2.2)
        (hcont.neg.mono subset_closure) hopen hconn hxOmega
        (fun y hy => neg_le_neg (hmin y (subset_closure hy)))
      have hconst : EqOn u (fun _ => u x) Omega := by
        intro y hy
        have h := hconstNeg hy
        simpa using congrArg Neg.neg h
      exact hnonconst ⟨u x, hconst⟩
    exact ⟨hx, by rw [hopen.interior_eq]; exact hxnot⟩

end HanLinLectureNotes.Ch01

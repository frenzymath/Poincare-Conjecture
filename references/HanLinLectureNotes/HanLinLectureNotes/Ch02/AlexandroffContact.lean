import HanLinLectureNotes.Ch02.MaximumPrinciple
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Han--Lin Chapter 2: upper contact points

The geometric contact-set core of the Alexandroff maximum principle.
-/

open Set Topology
open scoped RealInnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The vector `p` is the slope of an affine function supporting `u` from above
at `y`, relative to the domain `Omega`. -/
def IsUpperSupportingSlope {n : Nat} (Omega : Set (Euclidean n))
    (u : Euclidean n -> Real) (y p : Euclidean n) : Prop :=
  ∀ x ∈ Omega, u x <= u y + inner Real p (x - y)

/-- Points of `Omega` admitting an affine upper support for `u`. -/
def upperContactSet {n : Nat} (Omega : Set (Euclidean n))
    (u : Euclidean n -> Real) : Set (Euclidean n) :=
  {y | y ∈ Omega ∧ ∃ p, IsUpperSupportingSlope Omega u y p}

/-- Slopes realized by affine upper supports to `u` on `Omega`. -/
def upperSupportingSlopes {n : Nat} (Omega : Set (Euclidean n))
    (u : Euclidean n -> Real) : Set (Euclidean n) :=
  {p | ∃ y ∈ Omega, IsUpperSupportingSlope Omega u y p}

/-- The supremum of `u` over `Omega`. -/
def domainSup {n : Nat} (Omega : Set (Euclidean n))
    (u : Euclidean n -> Real) : Real :=
  sSup (u '' Omega)

/-- The supremum on the boundary of the positive part of `u`. -/
def boundaryPositiveSup {n : Nat} (Omega : Set (Euclidean n))
    (u : Euclidean n -> Real) : Real :=
  sSup ((fun x => u x ⊔ 0) '' frontier Omega)

/-- The radius occurring in the contact-set argument for Alexandroff's estimate. -/
def alexandroffSlopeRadius {n : Nat} (Omega : Set (Euclidean n))
    (u : Euclidean n -> Real) : Real :=
  (domainSup Omega u - boundaryPositiveSup Omega u) / Metric.diam Omega

/-- Every slope in the Alexandroff ball has an upper support at an interior
upper-contact point where `u` lies strictly above its positive boundary
supremum. -/
theorem exists_interior_upperContact_strictSuperlevel_of_mem_alexandroffSlopeBall
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (hu : ContinuousOn u (closure Omega)) {p : Euclidean n}
    (hp : p ∈ Metric.ball 0 (alexandroffSlopeRadius Omega u)) :
    ∃ y, y ∈ interior Omega ∧ y ∈ upperContactSet Omega u ∧
      boundaryPositiveSup Omega u < u y ∧
        IsUpperSupportingSlope Omega u y p := by
  have hcompact : IsCompact (closure Omega) := hOmegaBdd.isCompact_closure
  have hvaluesBdd : BddAbove (u '' Omega) := by
    rcases hcompact.bddAbove_image hu with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (image_mono subset_closure hz)
  have hpositiveContinuous :
      ContinuousOn (fun x => u x ⊔ 0) (closure Omega) :=
    hu.sup continuousOn_const
  have hboundaryBdd :
      BddAbove ((fun x => u x ⊔ 0) '' frontier Omega) := by
    rcases hcompact.bddAbove_image hpositiveContinuous with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro z hz
    exact hC (image_mono frontier_subset_closure hz)
  have hp' :
      norm p <
        (domainSup Omega u - boundaryPositiveSup Omega u) / Metric.diam Omega := by
    simpa only [alexandroffSlopeRadius, Metric.mem_ball, dist_zero_right] using hp
  have hratioPos :
      0 < (domainSup Omega u - boundaryPositiveSup Omega u) / Metric.diam Omega :=
    (norm_nonneg p).trans_lt hp'
  have hdiamPos : 0 < Metric.diam Omega := by
    by_contra h
    have hdiamZero : Metric.diam Omega = 0 :=
      le_antisymm (le_of_not_gt h) Metric.diam_nonneg
    simp only [hdiamZero, div_zero] at hratioPos
    exact lt_irrefl 0 hratioPos
  have hgap :
      norm p * Metric.diam Omega <
        domainSup Omega u - boundaryPositiveSup Omega u :=
    (lt_div_iff₀ hdiamPos).mp hp'
  have hthreshold :
      boundaryPositiveSup Omega u + norm p * Metric.diam Omega <
        domainSup Omega u := by
    linarith
  have hvaluesNe : (u '' Omega).Nonempty := hOmegaNe.image u
  have hthreshold' :
      boundaryPositiveSup Omega u + norm p * Metric.diam Omega <
        sSup (u '' Omega) := by
    simpa only [domainSup] using hthreshold
  rcases (lt_csSup_iff hvaluesBdd hvaluesNe).mp hthreshold' with
    ⟨z, ⟨x0, hx0Omega, rfl⟩, hx0⟩
  let tilted : Euclidean n -> Real := fun x => u x - inner Real p x
  have hlinear : Continuous (fun x : Euclidean n => inner Real p x) := by
    simpa using (continuous_const.inner continuous_id)
  have htiltedContinuous : ContinuousOn tilted (closure Omega) := by
    intro x hx
    exact (hu x hx).sub hlinear.continuousAt.continuousWithinAt
  rcases hcompact.exists_isMaxOn (hOmegaNe.mono subset_closure)
      htiltedContinuous with ⟨y, hyClosure, hyMax⟩
  have hclosureBdd : Bornology.IsBounded (closure Omega) :=
    Metric.isBounded_closure_of_isBounded hOmegaBdd
  have hdist : norm (y - x0) <= Metric.diam Omega := by
    have h := Metric.dist_le_diam_of_mem hclosureBdd hyClosure
      (subset_closure hx0Omega)
    rw [Metric.diam_closure] at h
    simpa only [dist_eq_norm] using h
  have hinnerNorm :
      -(norm p * norm (y - x0)) <= inner Real p (y - x0) := by
    calc
      -(norm p * norm (y - x0)) <= -abs (inner Real p (y - x0)) :=
        neg_le_neg (abs_real_inner_le_norm p (y - x0))
      _ <= inner Real p (y - x0) := neg_abs_le _
  have hinnerDiam :
      -(norm p * Metric.diam Omega) <= inner Real p (y - x0) := by
    exact (neg_le_neg (mul_le_mul_of_nonneg_left hdist (norm_nonneg p))).trans
      hinnerNorm
  have hx0Max : tilted x0 <= tilted y :=
    hyMax (subset_closure hx0Omega)
  have hyAboveBoundary : boundaryPositiveSup Omega u < u y := by
    by_contra hyNotAbove
    have hyBoundary : u y <= boundaryPositiveSup Omega u :=
      le_of_not_gt hyNotAbove
    have hyTiltedLt : tilted y < tilted x0 := by
      dsimp only [tilted]
      rw [inner_sub_right] at hinnerDiam
      linarith
    exact (not_lt_of_ge hx0Max) hyTiltedLt
  have hyNotFrontier : y ∉ frontier Omega := by
    intro hyFrontier
    have hyBoundary :
        u y <= boundaryPositiveSup Omega u := by
      calc
        u y <= u y ⊔ 0 := le_sup_left
        _ <= boundaryPositiveSup Omega u :=
          le_csSup hboundaryBdd ⟨y, hyFrontier, rfl⟩
    exact (not_lt_of_ge hyBoundary) hyAboveBoundary
  have hyOmega : y ∈ Omega := by
    rw [closure_eq_self_union_frontier] at hyClosure
    exact hyClosure.resolve_right hyNotFrontier
  have hyInterior : y ∈ interior Omega := by
    simpa only [hOmegaOpen.interior_eq] using hyOmega
  have hsupport : IsUpperSupportingSlope Omega u y p := by
    intro x hxOmega
    have hxy : tilted x <= tilted y := hyMax (subset_closure hxOmega)
    dsimp only [tilted] at hxy
    rw [inner_sub_right]
    linarith
  refine ⟨y, hyInterior, ?_, hyAboveBoundary, hsupport⟩
  exact ⟨hyOmega, p, hsupport⟩

/-- Every slope in the Alexandroff ball has an upper support at an interior
upper-contact point. This is the geometric inclusion used before applying the
area formula in Han--Lin Lemma 2.33. -/
theorem exists_interior_upperContact_of_mem_alexandroffSlopeBall
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (hu : ContinuousOn u (closure Omega)) {p : Euclidean n}
    (hp : p ∈ Metric.ball 0 (alexandroffSlopeRadius Omega u)) :
    ∃ y, y ∈ interior Omega ∧ y ∈ upperContactSet Omega u ∧
      IsUpperSupportingSlope Omega u y p := by
  rcases
      exists_interior_upperContact_strictSuperlevel_of_mem_alexandroffSlopeBall
        hOmegaOpen hOmegaNe hOmegaBdd hu hp with
    ⟨y, hyInterior, hyContact, _hyAboveBoundary, hsupport⟩
  exact ⟨y, hyInterior, hyContact, hsupport⟩

/-- Set form of the supporting-slope inclusion underlying Lemma 2.33. -/
theorem alexandroffSlopeBall_subset_upperSupportingSlopes
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (hu : ContinuousOn u (closure Omega)) :
    Metric.ball 0 (alexandroffSlopeRadius Omega u) ⊆
      upperSupportingSlopes Omega u := by
  intro p hp
  rcases exists_interior_upperContact_of_mem_alexandroffSlopeBall
      hOmegaOpen hOmegaNe hOmegaBdd hu hp with
    ⟨y, hyInterior, _hyContact, hsupport⟩
  exact ⟨y, hOmegaOpen.interior_eq ▸ hyInterior, hsupport⟩

/-- An upper supporting slope at an interior differentiability point is the
    Euclidean gradient. This is the differential bridge for the contact-set
    image in the Alexandroff argument. -/
theorem upperSupportingSlope_eq_gradient
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    {y p : Euclidean n}
    (hy : y ∈ interior Omega)
    (hu : DifferentiableAt Real u y)
    (hsupport : IsUpperSupportingSlope Omega u y p) :
    p = gradient u y := by
  have hqmaxOn : IsMaxOn (fun x : Euclidean n => u x - inner Real p x) Omega y := by
    intro x hx
    have h := hsupport x hx
    rw [inner_sub_right] at h
    calc
      u x - inner Real p x ≤
          u y + (inner Real p x - inner Real p y) - inner Real p x :=
        sub_le_sub_right h _
      _ = u y - inner Real p y := by ring
  have hOmegaNhds : Omega ∈ 𝓝 y :=
    Filter.mem_of_superset (IsOpen.mem_nhds isOpen_interior hy) interior_subset
  have hqmax : IsLocalMax (fun x : Euclidean n => u x - inner Real p x) y :=
    hqmaxOn.isLocalMax hOmegaNhds
  have hlin : HasFDerivAt (fun x : Euclidean n => inner Real p x)
      (innerSL Real (E := Euclidean n) p) y := by
    convert ContinuousLinearMap.hasFDerivAt (innerSL Real (E := Euclidean n) p) (x := y) using 1
    funext x
    exact (innerSL_apply_apply Real p x).symm
  have hqderiv :
      HasFDerivAt (fun x : Euclidean n => u x - inner Real p x)
        (fderiv Real u y - innerSL Real (E := Euclidean n) p) y := by
    exact hu.hasFDerivAt.sub hlin
  have hzero : fderiv Real (fun x : Euclidean n => u x - inner Real p x) y = 0 :=
    hqmax.fderiv_eq_zero
  have hsub : fderiv Real u y - innerSL Real (E := Euclidean n) p = 0 := by
    rw [hqderiv.fderiv] at hzero
    exact hzero
  have hderiv : fderiv Real u y = innerSL Real (E := Euclidean n) p := sub_eq_zero.mp hsub
  apply (innerSL_inj (𝕜 := Real) (E := Euclidean n)).mp
  ext v
  simpa only [innerSL_apply_apply, inner_gradient_left] using
    congrArg (fun L => L v) hderiv.symm

/-- On an open domain, supporting slopes are contained in the image of the
    gradient whenever the function is differentiable throughout the domain. -/
theorem upperSupportingSlopes_subset_gradient_image
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega)
    (hu : ∀ y ∈ Omega, DifferentiableAt Real u y) :
    upperSupportingSlopes Omega u ⊆ gradient u '' Omega := by
  intro p hp
  rcases hp with ⟨y, hyOmega, hsupport⟩
  have hyInterior : y ∈ interior Omega := by
    simpa only [hOmegaOpen.interior_eq] using hyOmega
  have hpGradient : p = gradient u y :=
    upperSupportingSlope_eq_gradient hyInterior (hu y hyOmega) hsupport
  exact ⟨y, hyOmega, hpGradient.symm⟩

/-- The Alexandroff slope ball lies in the gradient image of the upper contact
set, not merely in the gradient image of the ambient domain. -/
theorem alexandroffSlopeBall_subset_gradient_image_upperContactSet
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (hu : ContinuousOn u (closure Omega))
    (hdu : ∀ y, y ∈ Omega -> DifferentiableAt Real u y) :
    Metric.ball 0 (alexandroffSlopeRadius Omega u) ⊆
      gradient u '' upperContactSet Omega u := by
  intro p hp
  rcases exists_interior_upperContact_of_mem_alexandroffSlopeBall
      hOmegaOpen hOmegaNe hOmegaBdd hu hp with
    ⟨y, hyInterior, hyContact, hsupport⟩
  have hyOmega : y ∈ Omega := hOmegaOpen.interior_eq ▸ hyInterior
  have hpGradient : p = gradient u y :=
    upperSupportingSlope_eq_gradient hyInterior (hdu y hyOmega) hsupport
  exact ⟨y, hyContact, hpGradient.symm⟩

/-- The Alexandroff slope ball lies in the gradient image of the part of the
upper contact set where `u` is strictly above its positive boundary supremum. -/
theorem alexandroffSlopeBall_subset_gradient_image_upperContactSet_strictSuperlevel
    {n : Nat} {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (hu : ContinuousOn u (closure Omega))
    (hdu : ∀ y, y ∈ Omega -> DifferentiableAt Real u y) :
    Metric.ball 0 (alexandroffSlopeRadius Omega u) ⊆
      gradient u '' (upperContactSet Omega u ∩
        {y | boundaryPositiveSup Omega u < u y}) := by
  intro p hp
  rcases
      exists_interior_upperContact_strictSuperlevel_of_mem_alexandroffSlopeBall
        hOmegaOpen hOmegaNe hOmegaBdd hu hp with
    ⟨y, hyInterior, hyContact, hyAboveBoundary, hsupport⟩
  have hyOmega : y ∈ Omega := hOmegaOpen.interior_eq ▸ hyInterior
  have hpGradient : p = gradient u y :=
    upperSupportingSlope_eq_gradient hyInterior (hdu y hyOmega) hsupport
  exact ⟨y, ⟨hyContact, hyAboveBoundary⟩, hpGradient.symm⟩

end HanLinLectureNotes.Ch02

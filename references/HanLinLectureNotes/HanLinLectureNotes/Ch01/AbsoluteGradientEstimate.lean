import HanLinLectureNotes.Ch01.AbsoluteGradientBound
import HanLinLectureNotes.Ch01.MaximumPrinciple

/-!
# Han--Lin Chapter 1: absolute interior gradient estimate

This module derives dimension-only interior gradient and Holder estimates.
-/

open Metric Set
open InnerProductSpace

noncomputable section

namespace HanLinLectureNotes.Ch01

variable {n : Nat}

/-- Han--Lin Theorem 1.32.  Harmonic functions on the unit ball have a
dimension-only interior gradient bound and a uniform Holder bound on the
half-ball. -/
theorem exists_interior_gradient_holder_const [Nonempty (Fin n)] :
    ∃ c : Real, 0 < c ∧ ∀ (u : EuclideanSpace Real (Fin n) → Real),
      IsHarmonicOn u (ball 0 1) →
      ContinuousOn u (closedBall 0 1) →
      (∀ x, x ∈ ball 0 (1 / 2 : Real) →
          ‖fderiv Real u x‖ ≤ c * sSup ((fun z => ‖u z‖) '' sphere 0 1)) ∧
      ∀ α, α ∈ Icc (0 : Real) 1 →
        ∀ x, x ∈ ball 0 (1 / 2 : Real) →
          ∀ y, y ∈ ball 0 (1 / 2 : Real) →
            ‖u x - u y‖ ≤
              c * dist x y ^ α * sSup ((fun z => ‖u z‖) '' sphere 0 1) := by
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  have hnReal : 0 < (n : Real) := by exact_mod_cast hn
  refine ⟨2 * (n : Real), by positivity, ?_⟩
  intro u hu hcont
  let M : Real := sSup ((fun z => ‖u z‖) '' sphere 0 1)
  have hsphere : (sphere (0 : EuclideanSpace Real (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  have hMcompact : IsCompact ((fun z => ‖u z‖) '' sphere 0 1) := by
    exact (isCompact_sphere (0 : EuclideanSpace Real (Fin n)) 1).image_of_continuousOn
      (hcont.mono sphere_subset_closedBall).norm
  have hMne : ((fun z => ‖u z‖) '' sphere 0 1).Nonempty :=
    hsphere.image (fun z => ‖u z‖)
  have hMgreatest : IsGreatest ((fun z => ‖u z‖) '' sphere 0 1) M := by
    simpa [M] using hMcompact.isGreatest_sSup hMne
  have hMnonneg : 0 ≤ M := by
    obtain ⟨z, hz⟩ := hsphere
    exact (norm_nonneg (u z)).trans (hMgreatest.2 ⟨z, hz, rfl⟩)
  have hplus : ∃ z, z ∈ sphere 0 1 ∧
      ∀ x, x ∈ ball 0 1 → u x ≤ u z := by
    apply subharmonic_maximum_principle hu.contDiffOn hcont
    intro x hx
    simp [hu.2 x hx]
  have huNeg : IsHarmonicOn (-u) (ball 0 1) :=
    (harmonicOnNhd_iff_isHarmonicOn isOpen_ball).1
      ((harmonicOnNhd_iff_isHarmonicOn isOpen_ball).2 hu).neg
  have hminus : ∃ z, z ∈ sphere 0 1 ∧
      ∀ x, x ∈ ball 0 1 → (-u) x ≤ (-u) z := by
    apply subharmonic_maximum_principle huNeg.contDiffOn hcont.neg
    intro x hx
    exact (huNeg.2 x hx).ge
  obtain ⟨zplus, hzplus, hplus⟩ := hplus
  obtain ⟨zminus, hzminus, hminus⟩ := hminus
  have hnorm : ∀ z, z ∈ ball 0 1 → ‖u z‖ ≤ M := by
    intro z hz
    rw [Real.norm_eq_abs]
    apply abs_le.2
    constructor
    · have hleft : (-u) z ≤ (-u) zminus := hminus z hz
      simp only [Pi.neg_apply] at hleft
      have hbound : ‖u zminus‖ ≤ M := hMgreatest.2 ⟨zminus, hzminus, rfl⟩
      have habs : -u zminus ≤ ‖u zminus‖ := by
        rw [Real.norm_eq_abs]
        exact neg_le_abs _
      linarith
    · have hright : u z ≤ u zplus := hplus z hz
      have hbound : ‖u zplus‖ ≤ M := hMgreatest.2 ⟨zplus, hzplus, rfl⟩
      have habs : u zplus ≤ ‖u zplus‖ := by
        rw [Real.norm_eq_abs]
        exact le_abs_self _
      exact hright.trans (habs.trans hbound)
  have hhalfUnit : ball (0 : EuclideanSpace Real (Fin n)) (1 / 2 : Real) ⊆ ball 0 1 := by
    exact ball_subset_ball (by norm_num)
  have hdiffHalf : ∀ z, z ∈ ball 0 (1 / 2 : Real) → DifferentiableAt Real u z := by
    intro z hz
    have hz' : z ∈ ball 0 1 := hhalfUnit hz
    exact ((hu.contDiffOn z hz').contDiffAt (isOpen_ball.mem_nhds hz')).differentiableAt
      (by norm_num)
  have hgrad : ∀ x, x ∈ ball 0 (1 / 2 : Real) →
      ‖fderiv Real u x‖ ≤ (2 * (n : Real)) * M := by
    intro x hx
    change dist x 0 < (1 / 2 : Real) at hx
    have hopen : ball x (1 / 2 : Real) ⊆ ball 0 1 := by
      apply ball_subset_ball'
      linarith
    have hclosed : closedBall x (1 / 2 : Real) ⊆ ball 0 1 := by
      apply closedBall_subset_ball'
      linarith
    have hlocal : IsHarmonicOn u (ball x (1 / 2 : Real)) := by
      refine ⟨hu.contDiffOn.mono hopen, ?_⟩
      intro z hz
      exact hu.2 z (hopen hz)
    have hlocalCont : ContinuousOn u (closedBall x (1 / 2 : Real)) :=
      hcont.mono (hclosed.trans ball_subset_closedBall)
    have hcenter := hlocal.fderiv_norm_le_of_norm_le_on_closedBall (by norm_num)
      hlocalCont (fun z hz => hnorm z (hclosed hz))
    convert hcenter using 1
    ring
  constructor
  · intro x hx
    exact hgrad x hx
  · intro α hα x hx y hy
    have hdist : dist x y < 1 := by
      change dist x 0 < (1 / 2 : Real) at hx
      change dist y 0 < (1 / 2 : Real) at hy
      calc
        dist x y ≤ dist x 0 + dist 0 y := by
          simpa [dist_comm] using dist_triangle x 0 y
        _ < 1 := by rw [dist_comm 0 y]; linarith
    have hLip : ‖u x - u y‖ ≤ (2 * (n : Real)) * M * dist x y := by
      have h := (convex_ball (0 : EuclideanSpace Real (Fin n)) (1 / 2 : Real)).norm_image_sub_le_of_norm_fderiv_le
        hdiffHalf hgrad hy hx
      simpa [dist_eq_norm] using h
    have hpow : dist x y ≤ dist x y ^ α :=
      Real.self_le_rpow_of_le_one (dist_nonneg) (le_of_lt hdist) hα.2
    calc
      ‖u x - u y‖ ≤ (2 * (n : Real)) * M * dist x y := hLip
      _ ≤ (2 * (n : Real)) * M * dist x y ^ α :=
        mul_le_mul_of_nonneg_left hpow (mul_nonneg (by positivity) hMnonneg)
      _ = (2 * (n : Real)) * dist x y ^ α * M := by ring

end HanLinLectureNotes.Ch01

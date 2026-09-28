import EvansLib.Ch02.LaplaceMeanValueAux
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Evans, Ch. 2 - constancy from the weak shell equation

This file supplies the one-dimensional distributional step used in the radial
proof of the Laplace mean-value formula.  A locally integrable function on an
interval whose pairing with every derivative of a test function vanishes is
constant almost everywhere.
-/

open MeasureTheory Metric Set
open scoped ContDiff Real

noncomputable section

namespace EvansLib

/-- A locally integrable function can be multiplied by a continuous compactly
supported function whose topological support stays in the domain. -/
lemma integrable_mul_of_locallyIntegrableOn_of_tsupport_subset
    {U : Set ℝ} {A g : ℝ → ℝ}
    (hA : LocallyIntegrableOn A U (volume : Measure ℝ))
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    Integrable (fun x => A x * g x) := by
  let K := tsupport g
  have hAK : IntegrableOn A K (volume : Measure ℝ) :=
    hA.integrableOn_compact_subset hgU hgc
  have hprodK : IntegrableOn (fun x => A x * g x) K (volume : Measure ℝ) :=
    hAK.mul_continuousOn hg.continuousOn hgc
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).1 hprodK
  intro x hx
  apply subset_tsupport g
  rw [Function.mem_support]
  intro hgx
  exact hx (by simp [hgx])

/-- A smooth compactly supported real function of integral zero has a smooth
compactly supported primitive.  If the original support lies in `(0, R)`, the
primitive can be chosen with support in the same interval. -/
lemma exists_contDiff_primitive_of_integral_eq_zero
    {q : ℝ → ℝ} {R : ℝ}
    (hq : ContDiff ℝ ∞ q) (hqc : HasCompactSupport q)
    (hqint : ∫ t, q t ∂(volume : Measure ℝ) = 0)
    (hqU : tsupport q ⊆ Ioo (0 : ℝ) R) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ Ioo (0 : ℝ) R ∧ deriv Φ = q := by
  let K := tsupport q
  have hK : IsCompact K := hqc
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · have hqzero : q = 0 := tsupport_eq_empty_iff.mp hKempty
    refine ⟨fun _ => 0, contDiff_const, ?_, by simp, ?_⟩
    · change HasCompactSupport (0 : ℝ → ℝ)
      change IsCompact (tsupport (0 : ℝ → ℝ))
      rw [tsupport_zero]
      exact isCompact_empty
    · funext x
      simp [hqzero]
  · let a := sInf K
    let b := sSup K
    have haK : a ∈ K := hK.sInf_mem hKne
    have hbK : b ∈ K := hK.sSup_mem hKne
    have hamin : ∀ x : ℝ, x ∈ K → a ≤ x :=
      (hK.isLeast_sInf hKne).2
    have hbmax : ∀ x : ℝ, x ∈ K → x ≤ b :=
      (hK.isGreatest_sSup hKne).2
    have ha0 : 0 < a := (hqU haK).1
    have hbR : b < R := (hqU hbK).2
    let left : ℝ := a / 2
    let right : ℝ := (b + R) / 2
    have hleft0 : 0 < left := by dsimp [left]; linarith
    have hlefta : left < a := by dsimp [left]; linarith
    have hbright : b < right := by dsimp [right]; linarith
    have hrightR : right < R := by dsimp [right]; linarith
    have hsuppq : Function.support q ⊆ Ioc left right := by
      intro x hx
      have hxK : x ∈ K := subset_tsupport q hx
      exact ⟨hlefta.trans_le (hamin x hxK), (hbmax x hxK).trans hbright.le⟩
    let Φ : ℝ → ℝ := fun x => ∫ t in left..x, q t
    have hΦderivAt (x : ℝ) : HasDerivAt Φ (q x) x := by
      dsimp [Φ]
      exact intervalIntegral.integral_hasDerivAt_right
        (hq.continuous.intervalIntegrable left x)
        hq.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hq.continuous.continuousAt
    have hΦderiv : deriv Φ = q :=
      funext fun x => (hΦderivAt x).deriv
    have hΦsmooth : ContDiff ℝ ∞ Φ := by
      apply contDiff_infty_iff_deriv.mpr
      refine ⟨fun x => (hΦderivAt x).differentiableAt, ?_⟩
      rw [hΦderiv]
      exact hq
    have hΦzero (x : ℝ) (hx : x ∉ Icc left right) : Φ x = 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · dsimp [Φ]
        calc
          (∫ t in left..x, q t) = ∫ _t in left..x, (0 : ℝ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htleft : t ≤ left := by
              rw [uIcc_of_ge hx.le] at ht
              exact ht.2
            by_contra hqt
            have htSupp : t ∈ Function.support q := Function.mem_support.mpr hqt
            exact (not_lt_of_ge htleft) (hsuppq htSupp).1
          _ = 0 := by simp
      · dsimp [Φ]
        rw [intervalIntegral.integral_eq_integral_of_support_subset]
        · exact hqint
        · intro t ht
          exact ⟨(ht |> hsuppq).1, (ht |> hsuppq).2.trans hx.le⟩
    have hΦsupport : Function.support Φ ⊆ Icc left right := by
      intro x hx
      by_contra hxI
      exact hx (hΦzero x hxI)
    have hΦtsupport : tsupport Φ ⊆ Icc left right :=
      closure_minimal hΦsupport isClosed_Icc
    have hΦcompact : HasCompactSupport Φ :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport Φ) hΦtsupport
    have hΦU : tsupport Φ ⊆ Ioo (0 : ℝ) R := by
      intro x hx
      have hxI := hΦtsupport hx
      exact ⟨hleft0.trans_le hxI.1, hxI.2.trans_lt hrightR⟩
    exact ⟨Φ, hΦsmooth, hΦcompact, hΦU, hΦderiv⟩

/-- If a locally integrable function on `(0, R)` annihilates the derivative of
every smooth compactly supported test function there, then it is constant
almost everywhere on `(0, R)`. -/
theorem exists_ae_eq_const_of_integral_mul_deriv_eq_zero
    {A : ℝ → ℝ} {R : ℝ}
    (hA : LocallyIntegrableOn A (Ioo (0 : ℝ) R) (volume : Measure ℝ))
    (hderiv : ∀ (φ : ℝ → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo (0 : ℝ) R →
      ∫ t, A t * deriv φ t ∂(volume : Measure ℝ) = 0) :
    ∃ c : ℝ, ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) R → A t = c := by
  by_cases hR : 0 < R
  · let bump : ContDiffBump (R / 2) :=
      { rIn := R / 8
        rOut := R / 4
        rIn_pos := by linarith
        rIn_lt_rOut := by linarith }
    let η : ℝ → ℝ := bump.normed (volume : Measure ℝ)
    have hηsmooth : ContDiff ℝ ∞ η := by
      dsimp [η]
      exact bump.contDiff_normed
    have hηcompact : HasCompactSupport η := by
      dsimp [η]
      exact bump.hasCompactSupport_normed
    have hηint : ∫ t, η t ∂(volume : Measure ℝ) = 1 := by
      dsimp [η]
      exact bump.integral_normed
    have hηU : tsupport η ⊆ Ioo (0 : ℝ) R := by
      change tsupport (bump.normed (volume : Measure ℝ)) ⊆ Ioo (0 : ℝ) R
      rw [bump.tsupport_normed_eq]
      change closedBall (R / 2) (R / 4) ⊆ Ioo (0 : ℝ) R
      intro x hx
      rw [mem_closedBall, Real.dist_eq] at hx
      have habs := abs_le.mp hx
      constructor <;> linarith
    let c : ℝ := ∫ t, A t * η t ∂(volume : Measure ℝ)
    refine ⟨c, ae_eq_const_of_integral_contDiff_smul_eq_zero hA ?_⟩
    intro ψ hψsmooth hψcompact hψU
    have hψint : Integrable ψ :=
      hψsmooth.continuous.integrable_of_hasCompactSupport hψcompact
    have hηintg : Integrable η :=
      hηsmooth.continuous.integrable_of_hasCompactSupport hηcompact
    let Iψ : ℝ := ∫ t, ψ t ∂(volume : Measure ℝ)
    let q : ℝ → ℝ := fun t => ψ t - Iψ * η t
    have hqSmooth : ContDiff ℝ ∞ q := by
      exact hψsmooth.sub (contDiff_const.mul hηsmooth)
    have hscaledCompact : HasCompactSupport (fun t => Iψ * η t) := by
      exact hηcompact.mul_left
    have hqCompact : HasCompactSupport q := by
      exact hψcompact.sub hscaledCompact
    have hqU : tsupport q ⊆ Ioo (0 : ℝ) R := by
      refine (tsupport_sub ψ (fun t => Iψ * η t)).trans ?_
      exact union_subset hψU ((tsupport_mul_subset_right).trans hηU)
    have hqInt : ∫ t, q t ∂(volume : Measure ℝ) = 0 := by
      rw [show q = fun t => ψ t - Iψ * η t from rfl,
        integral_sub hψint (hηintg.const_mul Iψ), integral_const_mul, hηint]
      simp [Iψ]
    obtain ⟨Φ, hΦsmooth, hΦcompact, hΦU, hΦderiv⟩ :=
      exists_contDiff_primitive_of_integral_eq_zero hqSmooth hqCompact hqInt hqU
    have hqPair : ∫ t, A t * q t ∂(volume : Measure ℝ) = 0 := by
      rw [← hΦderiv]
      exact hderiv Φ hΦsmooth hΦcompact hΦU
    have hAψ : Integrable (fun t => A t * ψ t) :=
      integrable_mul_of_locallyIntegrableOn_of_tsupport_subset hA
        hψsmooth.continuous hψcompact hψU
    have hAη : Integrable (fun t => A t * η t) :=
      integrable_mul_of_locallyIntegrableOn_of_tsupport_subset hA
        hηsmooth.continuous hηcompact hηU
    have hrelation :
        (∫ t, A t * ψ t ∂(volume : Measure ℝ)) - Iψ * c = 0 := by
      have hfun : (fun t => A t * q t) =
          fun t => A t * ψ t - Iψ * (A t * η t) := by
        funext t
        dsimp [q]
        ring
      rw [hfun, integral_sub hAψ (hAη.const_mul Iψ), integral_const_mul] at hqPair
      exact hqPair
    have hfun : (fun t => ψ t * (A t - c)) =
        fun t => A t * ψ t - c * ψ t := by
      funext t
      ring
    rw [hfun, integral_sub hAψ (hψint.const_mul c), integral_const_mul]
    simpa [Iψ, mul_comm] using hrelation
  · refine ⟨0, ?_⟩
    have hRle : R ≤ 0 := le_of_not_gt hR
    filter_upwards [] with t
    intro ht
    exfalso
    linarith [ht.1, ht.2]

end EvansLib

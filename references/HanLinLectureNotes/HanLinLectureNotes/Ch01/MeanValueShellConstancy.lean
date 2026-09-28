import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Constancy from the weak shell equation

This module supplies the one-dimensional distributional step in the radial
proof of the harmonic mean-value formula.
-/

open MeasureTheory Metric Set
open scoped ContDiff Real

noncomputable section

namespace HanLinLectureNotes.Ch01

/-- A locally integrable function can be multiplied by a continuous compactly
supported function whose topological support stays in the domain. -/
lemma integrable_mul_of_locallyIntegrableOn_of_tsupport_subset
    {U : Set Real} {A g : Real -> Real}
    (hA : LocallyIntegrableOn A U (volume : Measure Real))
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ U) :
    Integrable (fun x => A x * g x) := by
  let K := tsupport g
  have hAK : IntegrableOn A K (volume : Measure Real) :=
    hA.integrableOn_compact_subset hgU hgc
  have hprodK : IntegrableOn (fun x => A x * g x) K (volume : Measure Real) :=
    hAK.mul_continuousOn hg.continuousOn hgc
  apply (integrableOn_iff_integrable_of_support_subset (s := K) ?_).1 hprodK
  intro x hx
  apply subset_tsupport g
  rw [Function.mem_support]
  intro hgx
  exact hx (by simp [hgx])

/-- A smooth compactly supported real function of integral zero has a smooth
compactly supported primitive. If the original support lies in `(0, R)`, the
primitive can be chosen with support in the same interval. -/
lemma exists_contDiff_primitive_of_integral_eq_zero
    {q : Real -> Real} {R : Real}
    (hq : ContDiff Real ∞ q) (hqc : HasCompactSupport q)
    (hqint : ∫ t, q t ∂(volume : Measure Real) = 0)
    (hqU : tsupport q ⊆ Ioo (0 : Real) R) :
    ∃ Phi : Real -> Real, ContDiff Real ∞ Phi ∧ HasCompactSupport Phi ∧
      tsupport Phi ⊆ Ioo (0 : Real) R ∧ deriv Phi = q := by
  let K := tsupport q
  have hK : IsCompact K := hqc
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · have hqzero : q = 0 := tsupport_eq_empty_iff.mp hKempty
    refine ⟨fun _ => 0, contDiff_const, ?_, by simp, ?_⟩
    · change HasCompactSupport (0 : Real -> Real)
      change IsCompact (tsupport (0 : Real -> Real))
      rw [tsupport_zero]
      exact isCompact_empty
    · funext x
      simp [hqzero]
  · let a := sInf K
    let b := sSup K
    have haK : a ∈ K := hK.sInf_mem hKne
    have hbK : b ∈ K := hK.sSup_mem hKne
    have hamin : ∀ x : Real, x ∈ K -> a <= x :=
      (hK.isLeast_sInf hKne).2
    have hbmax : ∀ x : Real, x ∈ K -> x <= b :=
      (hK.isGreatest_sSup hKne).2
    have ha0 : 0 < a := (hqU haK).1
    have hbR : b < R := (hqU hbK).2
    let left : Real := a / 2
    let right : Real := (b + R) / 2
    have hleft0 : 0 < left := by dsimp [left]; linarith
    have hlefta : left < a := by dsimp [left]; linarith
    have hbright : b < right := by dsimp [right]; linarith
    have hrightR : right < R := by dsimp [right]; linarith
    have hsuppq : Function.support q ⊆ Ioc left right := by
      intro x hx
      have hxK : x ∈ K := subset_tsupport q hx
      exact ⟨hlefta.trans_le (hamin x hxK), (hbmax x hxK).trans hbright.le⟩
    let Phi : Real -> Real := fun x => ∫ t in left..x, q t
    have hPhiderivAt (x : Real) : HasDerivAt Phi (q x) x := by
      dsimp [Phi]
      exact intervalIntegral.integral_hasDerivAt_right
        (hq.continuous.intervalIntegrable left x)
        hq.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
        hq.continuous.continuousAt
    have hPhideriv : deriv Phi = q :=
      funext fun x => (hPhiderivAt x).deriv
    have hPhismooth : ContDiff Real ∞ Phi := by
      apply contDiff_infty_iff_deriv.mpr
      refine ⟨fun x => (hPhiderivAt x).differentiableAt, ?_⟩
      rw [hPhideriv]
      exact hq
    have hPhizero (x : Real) (hx : x ∉ Icc left right) : Phi x = 0 := by
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with hx | hx
      · dsimp [Phi]
        calc
          (∫ t in left..x, q t) = ∫ _t in left..x, (0 : Real) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htleft : t <= left := by
              rw [uIcc_of_ge hx.le] at ht
              exact ht.2
            by_contra hqt
            have htSupp : t ∈ Function.support q := Function.mem_support.mpr hqt
            exact (not_lt_of_ge htleft) (hsuppq htSupp).1
          _ = 0 := by simp
      · dsimp [Phi]
        rw [intervalIntegral.integral_eq_integral_of_support_subset]
        · exact hqint
        · intro t ht
          exact ⟨(ht |> hsuppq).1, (ht |> hsuppq).2.trans hx.le⟩
    have hPhisupport : Function.support Phi ⊆ Icc left right := by
      intro x hx
      by_contra hxI
      exact hx (hPhizero x hxI)
    have hPhitsupport : tsupport Phi ⊆ Icc left right :=
      closure_minimal hPhisupport isClosed_Icc
    have hPhicompact : HasCompactSupport Phi :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport Phi) hPhitsupport
    have hPhiU : tsupport Phi ⊆ Ioo (0 : Real) R := by
      intro x hx
      have hxI := hPhitsupport hx
      exact ⟨hleft0.trans_le hxI.1, hxI.2.trans_lt hrightR⟩
    exact ⟨Phi, hPhismooth, hPhicompact, hPhiU, hPhideriv⟩

/-- Vanishing pairings with all smooth compactly supported tests determine a
locally integrable function up to a prescribed constant. -/
lemma ae_eq_const_of_integral_contDiff_mul_eq_zero
    {A : Real -> Real} {R c : Real}
    (hA : LocallyIntegrableOn A (Ioo (0 : Real) R) (volume : Measure Real))
    (hzero : ∀ (phi : Real -> Real), ContDiff Real ∞ phi ->
      HasCompactSupport phi -> tsupport phi ⊆ Ioo (0 : Real) R ->
      ∫ t, phi t * (A t - c) ∂(volume : Measure Real) = 0) :
    ∀ᵐ t ∂(volume : Measure Real), t ∈ Ioo (0 : Real) R -> A t = c := by
  have hdist : ∀ᵐ t ∂(volume : Measure Real),
      t ∈ Ioo (0 : Real) R -> A t - c = 0 := by
    let B : Real -> Real := fun t => A t - c
    have hB : LocallyIntegrableOn B (Ioo (0 : Real) R) (volume : Measure Real) :=
      hA.sub (locallyIntegrableOn_const _)
    apply IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero isOpen_Ioo hB
    intro phi hphi hphic hphiU
    simpa [B, smul_eq_mul] using hzero phi hphi hphic hphiU
  filter_upwards [hdist] with t ht
  intro htI
  linarith [ht htI]

/-- If a locally integrable function on `(0, R)` annihilates the derivative of
every smooth compactly supported test function there, then it is constant
almost everywhere on `(0, R)`. -/
theorem exists_ae_eq_const_of_integral_mul_deriv_eq_zero
    {A : Real -> Real} {R : Real}
    (hA : LocallyIntegrableOn A (Ioo (0 : Real) R) (volume : Measure Real))
    (hderiv : ∀ (phi : Real -> Real), ContDiff Real ∞ phi ->
      HasCompactSupport phi -> tsupport phi ⊆ Ioo (0 : Real) R ->
      ∫ t, A t * deriv phi t ∂(volume : Measure Real) = 0) :
    ∃ c : Real, ∀ᵐ t ∂(volume : Measure Real), t ∈ Ioo (0 : Real) R -> A t = c := by
  by_cases hR : 0 < R
  · let bump : ContDiffBump (R / 2) :=
      { rIn := R / 8
        rOut := R / 4
        rIn_pos := by linarith
        rIn_lt_rOut := by linarith }
    let eta : Real -> Real := bump.normed (volume : Measure Real)
    have hetasmooth : ContDiff Real ∞ eta := by
      dsimp [eta]
      exact bump.contDiff_normed
    have hetacompact : HasCompactSupport eta := by
      dsimp [eta]
      exact bump.hasCompactSupport_normed
    have hetaint : ∫ t, eta t ∂(volume : Measure Real) = 1 := by
      dsimp [eta]
      exact bump.integral_normed
    have hetaU : tsupport eta ⊆ Ioo (0 : Real) R := by
      change tsupport (bump.normed (volume : Measure Real)) ⊆ Ioo (0 : Real) R
      rw [bump.tsupport_normed_eq]
      change closedBall (R / 2) (R / 4) ⊆ Ioo (0 : Real) R
      intro x hx
      rw [mem_closedBall, Real.dist_eq] at hx
      have habs := abs_le.mp hx
      constructor <;> linarith
    let c : Real := ∫ t, A t * eta t ∂(volume : Measure Real)
    refine ⟨c, ae_eq_const_of_integral_contDiff_mul_eq_zero hA ?_⟩
    intro psi hpsismooth hpsicompact hpsiU
    have hpsiint : Integrable psi :=
      hpsismooth.continuous.integrable_of_hasCompactSupport hpsicompact
    have hetaintg : Integrable eta :=
      hetasmooth.continuous.integrable_of_hasCompactSupport hetacompact
    let Ipsi : Real := ∫ t, psi t ∂(volume : Measure Real)
    let q : Real -> Real := fun t => psi t - Ipsi * eta t
    have hqSmooth : ContDiff Real ∞ q := by
      exact hpsismooth.sub (contDiff_const.mul hetasmooth)
    have hscaledCompact : HasCompactSupport (fun t => Ipsi * eta t) := by
      exact hetacompact.mul_left
    have hqCompact : HasCompactSupport q := by
      exact hpsicompact.sub hscaledCompact
    have hqU : tsupport q ⊆ Ioo (0 : Real) R := by
      refine (tsupport_sub psi (fun t => Ipsi * eta t)).trans ?_
      exact union_subset hpsiU ((tsupport_mul_subset_right).trans hetaU)
    have hqInt : ∫ t, q t ∂(volume : Measure Real) = 0 := by
      rw [show q = fun t => psi t - Ipsi * eta t from rfl,
        integral_sub hpsiint (hetaintg.const_mul Ipsi), integral_const_mul, hetaint]
      simp [Ipsi]
    obtain ⟨Phi, hPhismooth, hPhicompact, hPhiU, hPhideriv⟩ :=
      exists_contDiff_primitive_of_integral_eq_zero hqSmooth hqCompact hqInt hqU
    have hqPair : ∫ t, A t * q t ∂(volume : Measure Real) = 0 := by
      rw [← hPhideriv]
      exact hderiv Phi hPhismooth hPhicompact hPhiU
    have hApsi : Integrable (fun t => A t * psi t) :=
      integrable_mul_of_locallyIntegrableOn_of_tsupport_subset hA
        hpsismooth.continuous hpsicompact hpsiU
    have hAeta : Integrable (fun t => A t * eta t) :=
      integrable_mul_of_locallyIntegrableOn_of_tsupport_subset hA
        hetasmooth.continuous hetacompact hetaU
    have hrelation :
        (∫ t, A t * psi t ∂(volume : Measure Real)) - Ipsi * c = 0 := by
      have hfun : (fun t => A t * q t) =
          fun t => A t * psi t - Ipsi * (A t * eta t) := by
        funext t
        dsimp [q]
        ring
      rw [hfun, integral_sub hApsi (hAeta.const_mul Ipsi), integral_const_mul] at hqPair
      exact hqPair
    have hfun : (fun t => psi t * (A t - c)) =
        fun t => A t * psi t - c * psi t := by
      funext t
      ring
    rw [hfun, integral_sub hApsi (hpsiint.const_mul c), integral_const_mul]
    simpa [Ipsi, mul_comm] using hrelation
  · refine ⟨0, ?_⟩
    have hRle : R <= 0 := le_of_not_gt hR
    filter_upwards [] with t
    intro ht
    exfalso
    linarith [ht.1, ht.2]

end HanLinLectureNotes.Ch01

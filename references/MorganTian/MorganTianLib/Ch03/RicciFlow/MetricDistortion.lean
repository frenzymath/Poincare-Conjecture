import MorganTianLib.Ch01.CurvatureNormManifold
import MorganTianLib.Ch03.RicciFlow.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Metric distortion along Ricci flow

This module proves the metric part of Morgan--Tian's bounded-curvature
distortion lemma.  The geometric input is made explicit first: a bound on the
curvature operator bounds the diagonal Ricci tensor by the dimension times the
metric.  The Ricci-flow equation can then be integrated by applying the mean
value theorem to exponentially weighted metric pairings.

Blueprint: `lem:metric-volume-distortion` (metric item).
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian
open exteriorPower

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [I.Boundaryless] in
/-- **Math.** The canonical Levi-Civita connection is Levi-Civita for its
metric.  This named proof lets curvature bounds use a stable proof argument. -/
theorem canonicalLeviCivita_isLeviCivita (g : RiemannianMetric I M) :
    g.leviCivitaConnection.IsLeviCivita g :=
  g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)

/-- **Math.** A uniform curvature-operator bound for an evolving metric on a
time set.  This is Morgan--Tian's hypothesis `|Rm(x,t)| ≤ K`. -/
def HasCurvatureOperatorNormLeOnTime (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) (K : ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    HasCurvatureOperatorNormLeAt (g t) (g t).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g t)) p K

/-- **Math.** A uniform diagonal Ricci bound relative to an evolving metric. -/
def HasAbsoluteRicciBoundOn (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) (C : ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (v : TangentSpace I p),
    |ricciTensorAt (g t) p v v| ≤ C * (g t).metricInner p v v

omit [NeZero (Module.finrank ℝ E)] in
private theorem metricDistortion_curvatureFormAt_eq_affineCurvatureFormAt
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (v w z u : TangentSpace I p) :
    curvatureFormAt g nabla p v w z u = nabla.curvatureFormAt g p v w z u := by
  rw [curvatureFormAt_def]
  symm
  exact nabla.curvatureFormAt_eq g p
    (extendVector_apply p v) (extendVector_apply p w)
    (extendVector_apply p z) (extendVector_apply p u)

private theorem metricDistortion_ricciAt_leviCivita_eq_ricciTensorAt
    (g : RiemannianMetric I M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g) (p : M)
    (v w : TangentSpace I p) :
    ricciAt g g.leviCivitaConnection hLC p v w = ricciTensorAt g p v w := by
  classical
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  simp only [ricciAt, ricciTensorAt, Riemannian.ricciBilin_apply]
  rw [Riemannian.ricciForm_eq_sum _ v w e,
    Riemannian.ricciForm_eq_sum _ v w e]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact metricDistortion_curvatureFormAt_eq_affineCurvatureFormAt
    g g.leviCivitaConnection p v (e i) w (e i)

/-- **Math.** At one point, `|Rm| ≤ K` gives
`|Ric(v,v)| ≤ n K g(v,v)`, where `n` is the dimension.  Taking an
orthonormal trace gives `n` summands, and each curvature-operator summand is
bounded by `K g(v,v)`. -/
theorem abs_ricciTensorAt_le_finrank_mul_of_hasCurvatureOperatorNormLeAt
    (g : RiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K) (p : M)
    (hRm : HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p K)
    (v : TangentSpace I p) :
    |ricciTensorAt g p v v| ≤
      (Module.finrank ℝ E : ℝ) * K * g.metricInner p v v := by
  classical
  let hLC := canonicalLeviCivita_isLeviCivita g
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  rw [← metricDistortion_ricciAt_leviCivita_eq_ricciTensorAt g hLC p v v]
  unfold ricciAt
  rw [Riemannian.ricciForm_eq_sum _ v v e]
  calc
    |∑ i, curvatureFormAt g g.leviCivitaConnection p v (e i) v (e i)| ≤
        ∑ i, |curvatureFormAt g g.leviCivitaConnection p v (e i) v (e i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I p)),
        K * g.metricInner p v v := by
      refine Finset.sum_le_sum fun i _hi => ?_
      have hOp := hRm (exteriorPower.ιMulti ℝ 2 ![v, e i])
      rw [curvatureOperator_wedge_self, wedgeInner_wedge_self] at hOp
      have hei : (inner ℝ (e i) (e i) : ℝ) = 1 := by
        rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i]
        norm_num
      have hwedge : Riemannian.wedgeSq v (e i) ≤ (inner ℝ v v : ℝ) := by
        rw [Riemannian.wedgeSq, hei]
        nlinarith [sq_nonneg (inner ℝ v (e i) : ℝ)]
      calc
        |curvatureFormAt g g.leviCivitaConnection p v (e i) v (e i)| ≤
            K * Riemannian.wedgeSq v (e i) := hOp
        _ ≤ K * (inner ℝ v v : ℝ) :=
          mul_le_mul_of_nonneg_left hwedge hK
        _ = K * g.metricInner p v v := rfl
    _ = (Module.finrank ℝ E : ℝ) * K * g.metricInner p v v := by
      have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
          Module.finrank ℝ (TangentSpace I p) := Fintype.card_fin _
      have hdim : (Module.finrank ℝ (TangentSpace I p) : ℝ) =
          (Module.finrank ℝ E : ℝ) := by
        have hdimNat : Module.finrank ℝ (TangentSpace I p) =
            Module.finrank ℝ E := by
          simpa only [Fintype.card_fin] using hcard.symm
        exact_mod_cast hdimNat
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [hdim]
      ring

/-- **Math.** A uniform curvature-operator bound produces the uniform
dimension-dependent Ricci bound used in the distortion argument. -/
theorem hasAbsoluteRicciBoundOn_of_hasCurvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hRm : HasCurvatureOperatorNormLeOnTime g J K) :
    HasAbsoluteRicciBoundOn g J ((Module.finrank ℝ E : ℝ) * K) := by
  intro t ht p v
  exact abs_ricciTensorAt_le_finrank_mul_of_hasCurvatureOperatorNormLeAt
    (g t) hK p (hRm t ht p) v

/-- **Math.** If `|Ric(v,v)| ≤ C g(v,v)` along a Ricci flow, then the
metric pairing of every fixed tangent vector changes by at most the factors
`exp(±2Ct)`. -/
theorem metricInner_exp_comparison_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T C t : ℝ}
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRic : HasAbsoluteRicciBoundOn g (Icc 0 T) C)
    (ht : t ∈ Icc (0 : ℝ) T) (p : M) (v : TangentSpace I p) :
    Real.exp (-(2 * C) * t) * (g 0).metricInner p v v ≤
        (g t).metricInner p v v ∧
      (g t).metricInner p v v ≤
        Real.exp ((2 * C) * t) * (g 0).metricInner p v v := by
  let f : ℝ → ℝ := fun s => (g s).metricInner p v v
  let upper : ℝ → ℝ := (fun s => Real.exp (-(2 * C) * s)) * f
  let lower : ℝ → ℝ := (fun s => Real.exp ((2 * C) * s)) * f
  have hfDeriv (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) :
      HasDerivWithinAt f (-2 * ricciTensorAt (g s) p v v) (Icc 0 T) s :=
    hflow.equation s hs p v v
  have hfCont : ContinuousOn f (Icc (0 : ℝ) T) :=
    fun s hs => (hfDeriv s hs).continuousWithinAt
  have hUpperCont : ContinuousOn upper (Icc (0 : ℝ) T) := by
    have hExp : Continuous (fun s : ℝ => Real.exp (-(2 * C) * s)) := by
      fun_prop
    exact hExp.continuousOn.mul hfCont
  have hLowerCont : ContinuousOn lower (Icc (0 : ℝ) T) := by
    have hExp : Continuous (fun s : ℝ => Real.exp ((2 * C) * s)) := by
      fun_prop
    exact hExp.continuousOn.mul hfCont
  have hUpperDeriv (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      HasDerivWithinAt upper
        (Real.exp (-(2 * C) * s) *
          (-(2 * C) * f s - 2 * ricciTensorAt (g s) p v v))
        (interior (Icc 0 T)) s := by
    have hsIcc : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have hmetric : HasDerivAt f (-2 * ricciTensorAt (g s) p v v) s :=
      (hfDeriv s hsIcc).hasDerivAt (mem_interior_iff_mem_nhds.mp hs)
    have hExp : HasDerivAt (fun r : ℝ => Real.exp (-(2 * C) * r))
        (-(2 * C) * Real.exp (-(2 * C) * s)) s := by
      convert (((hasDerivAt_id s).const_mul (-(2 * C))).exp) using 1
      · simp only [id]
      · simp only [id, mul_one]
        ring
    have hderiv :
        (-(2 * C) * Real.exp (-(2 * C) * s)) * f s +
            Real.exp (-(2 * C) * s) *
              (-2 * ricciTensorAt (g s) p v v) =
          Real.exp (-(2 * C) * s) *
            (-(2 * C) * f s - 2 * ricciTensorAt (g s) p v v) := by
      ring
    exact ((hExp.mul hmetric).congr_deriv hderiv).hasDerivWithinAt
  have hLowerDeriv (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      HasDerivWithinAt lower
        (Real.exp ((2 * C) * s) *
          ((2 * C) * f s - 2 * ricciTensorAt (g s) p v v))
        (interior (Icc 0 T)) s := by
    have hsIcc : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have hmetric : HasDerivAt f (-2 * ricciTensorAt (g s) p v v) s :=
      (hfDeriv s hsIcc).hasDerivAt (mem_interior_iff_mem_nhds.mp hs)
    have hExp : HasDerivAt (fun r : ℝ => Real.exp ((2 * C) * r))
        ((2 * C) * Real.exp ((2 * C) * s)) s := by
      convert (((hasDerivAt_id s).const_mul (2 * C)).exp) using 1
      · simp only [id]
      · simp only [id, mul_one]
        ring
    have hderiv :
        ((2 * C) * Real.exp ((2 * C) * s)) * f s +
            Real.exp ((2 * C) * s) *
              (-2 * ricciTensorAt (g s) p v v) =
          Real.exp ((2 * C) * s) *
            ((2 * C) * f s - 2 * ricciTensorAt (g s) p v v) := by
      ring
    exact ((hExp.mul hmetric).congr_deriv hderiv).hasDerivWithinAt
  have hUpperNonpos (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      Real.exp (-(2 * C) * s) *
          (-(2 * C) * f s - 2 * ricciTensorAt (g s) p v v) ≤ 0 := by
    have hsIcc : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have hbounds := abs_le.mp (hRic s hsIcc p v)
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    dsimp only [f]
    linarith
  have hLowerNonneg (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      0 ≤ Real.exp ((2 * C) * s) *
          ((2 * C) * f s - 2 * ricciTensorAt (g s) p v v) := by
    have hsIcc : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have hbounds := abs_le.mp (hRic s hsIcc p v)
    apply mul_nonneg (Real.exp_pos _).le
    dsimp only [f]
    linarith
  have hUpperAnti : AntitoneOn upper (Icc (0 : ℝ) T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hUpperCont
      hUpperDeriv hUpperNonpos
  have hLowerMono : MonotoneOn lower (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hLowerCont
      hLowerDeriv hLowerNonneg
  have hzero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hUpperCompare := hUpperAnti hzero ht ht.1
  have hLowerCompare := hLowerMono hzero ht ht.1
  dsimp only [upper, lower, f] at hUpperCompare hLowerCompare
  change Real.exp (-(2 * C) * t) * (g t).metricInner p v v ≤
      Real.exp (-(2 * C) * 0) * (g 0).metricInner p v v at hUpperCompare
  change Real.exp ((2 * C) * 0) * (g 0).metricInner p v v ≤
      Real.exp ((2 * C) * t) * (g t).metricInner p v v at hLowerCompare
  simp only [mul_zero, Real.exp_zero, one_mul] at hUpperCompare hLowerCompare
  have hcancelUpper :
      Real.exp ((2 * C) * t) * Real.exp (-(2 * C) * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  have hcancelLower :
      Real.exp (-(2 * C) * t) * Real.exp ((2 * C) * t) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  constructor
  · calc
      Real.exp (-(2 * C) * t) * (g 0).metricInner p v v ≤
          Real.exp (-(2 * C) * t) *
            (Real.exp ((2 * C) * t) * (g t).metricInner p v v) :=
        mul_le_mul_of_nonneg_left hLowerCompare (Real.exp_pos _).le
      _ = (g t).metricInner p v v := by
        rw [← mul_assoc, hcancelLower, one_mul]
  · calc
      (g t).metricInner p v v =
          Real.exp ((2 * C) * t) *
            (Real.exp (-(2 * C) * t) * (g t).metricInner p v v) := by
        rw [← mul_assoc, hcancelUpper, one_mul]
      _ ≤ Real.exp ((2 * C) * t) * (g 0).metricInner p v v :=
        mul_le_mul_of_nonneg_left hUpperCompare (Real.exp_pos _).le

/-- **Math.** On `[0,T]`, the time-dependent exponential factors can be
replaced by the single constant `A = exp(2CT)`. -/
theorem metricInner_uniform_exp_comparison_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {T C : ℝ} (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRic : HasAbsoluteRicciBoundOn g (Icc 0 T) C) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ (p : M) (v : TangentSpace I p),
      (Real.exp ((2 * C) * T))⁻¹ * (g 0).metricInner p v v ≤
          (g t).metricInner p v v ∧
        (g t).metricInner p v v ≤
          Real.exp ((2 * C) * T) * (g 0).metricInner p v v := by
  intro t ht p v
  obtain ⟨hlower, hupper⟩ :=
    metricInner_exp_comparison_of_isRicciFlowOn hflow hRic ht p v
  have hmetric0 : 0 ≤ (g 0).metricInner p v v :=
    (g 0).metricInner_self_nonneg p v
  constructor
  · have hcoeff : (Real.exp ((2 * C) * T))⁻¹ ≤
        Real.exp (-(2 * C) * t) := by
      rw [← Real.exp_neg]
      apply Real.exp_le_exp.mpr
      have htime : (2 * C) * t ≤ (2 * C) * T :=
        mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (by norm_num) hC)
      calc
        -(2 * C * T) ≤ -(2 * C * t) := neg_le_neg htime
        _ = -(2 * C) * t := by ring
    exact (mul_le_mul_of_nonneg_right hcoeff hmetric0).trans hlower
  · have hcoeff : Real.exp ((2 * C) * t) ≤
        Real.exp ((2 * C) * T) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left ht.2 (mul_nonneg (by norm_num) hC)
    exact hupper.trans (mul_le_mul_of_nonneg_right hcoeff hmetric0)

/-- **Math.** Under the source hypothesis `|Rm(x,t)| ≤ K`, the metric is
uniformly equivalent to the initial metric with the explicit constant
`A = exp(2 n K T)`. -/
theorem metricInner_distortion_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ} (hK : 0 ≤ K)
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ (p : M) (v : TangentSpace I p),
      (Real.exp
          ((2 * ((Module.finrank ℝ E : ℝ) * K)) * T))⁻¹ *
            (g 0).metricInner p v v ≤ (g t).metricInner p v v ∧
        (g t).metricInner p v v ≤
          Real.exp ((2 * ((Module.finrank ℝ E : ℝ) * K)) * T) *
            (g 0).metricInner p v v := by
  apply metricInner_uniform_exp_comparison_of_isRicciFlowOn
    (C := (Module.finrank ℝ E : ℝ) * K)
  · exact mul_nonneg (Nat.cast_nonneg _) hK
  · exact hflow
  · exact hasAbsoluteRicciBoundOn_of_hasCurvatureOperatorNormLeOnTime hK hRm

/-- **Math.** The metric item of Morgan--Tian's bounded-curvature distortion
lemma, in its stated existential-constant form. -/
theorem exists_metricDistortionConstant_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ} (hK : 0 ≤ K)
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K) :
    ∃ A : ℝ, 0 < A ∧
      ∀ t ∈ Icc (0 : ℝ) T, ∀ (p : M) (v : TangentSpace I p),
        A⁻¹ * (g 0).metricInner p v v ≤ (g t).metricInner p v v ∧
          (g t).metricInner p v v ≤ A * (g 0).metricInner p v v := by
  refine ⟨Real.exp ((2 * ((Module.finrank ℝ E : ℝ) * K)) * T),
    Real.exp_pos _, ?_⟩
  exact metricInner_distortion_of_curvatureOperatorNormLeOnTime hK hflow hRm

end MorganTianLib

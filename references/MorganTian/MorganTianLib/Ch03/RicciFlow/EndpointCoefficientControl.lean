import MorganTianLib.Ch03.RicciFlow.MetricDistortion
import MorganTianLib.Ch03.RicciFlow.EndpointPatching
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Morgan--Tian Ch. 3 - endpoint coefficient control

This module contains the fixed-coefficient part of the finite-time endpoint
argument.  A quadratic Ricci bound gives exponential control of every metric
pairing on closed subintervals.  The Ricci-flow equation then gives a uniform
derivative bound, so each fixed coefficient has a genuine one-sided limit at a
finite endpoint.  The diagonal limits are positive away from the zero vector.

The final endpoint tensor and its smoothness are deliberately supplied by the
restart consumer: this file does not postulate a limiting metric.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Filter Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## Source-facing quadratic control -/

/-- **Math.** A uniform quadratic-form bound for the Ricci tensor on a time
set.  This is the coefficient-level Ricci control used by the endpoint
argument; unlike an endpoint metric assertion it has no hidden limit data. -/
def RicciQuadraticControlOn (g : ℝ → RiemannianMetric I M)
    (J : Set ℝ) (C : ℝ) : Prop :=
  ∀ t ∈ J, ∀ (p : M) (v : TangentSpace I p),
    |ricciTensorAt (g t) p v v| ≤ C * (g t).metricInner p v v

/-- **Math.** The quadratic control is exactly the diagonal Ricci bound consumed by the
metric distortion theorem. -/
theorem hasAbsoluteRicciBoundOn_of_ricciQuadraticControlOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {C : ℝ}
    (h : RicciQuadraticControlOn g J C) :
    HasAbsoluteRicciBoundOn g J C := by
  exact h

/-! ## Restriction to closed subintervals -/

private theorem isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {T s : ℝ}
    (hflow : IsRicciFlowOn g (Ico 0 T)) (hs : 0 < s) (hsT : s < T) :
    IsRicciFlowOn g (Icc 0 s) := by
  have hsub : Icc (0 : ℝ) s ⊆ Ico 0 T := by
    intro u hu
    exact ⟨hu.1, lt_of_le_of_lt hu.2 hsT⟩
  have hnontrivial : (Icc (0 : ℝ) s).Nontrivial := by
    apply nontrivial_of_mem_mem_ne
      (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs.le⟩)
      (show s / 2 ∈ Icc 0 s by constructor <;> linarith)
      (by linarith)
  refine
    { ordConnected := ordConnected_Icc
      nontrivial := hnontrivial
      smooth := hflow.smooth.mono (Set.prod_mono subset_rfl hsub)
      equation := ?_ }
  intro u hu p x y
  exact (hflow.equation u (hsub hu) p x y).mono hsub

/-! ## Polarization and uniform metric control -/

private theorem abs_ricciTensorAt_cross_le_of_ricciQuadraticControlOn
    (g : RiemannianMetric I M) (C : ℝ) (p : M)
    (hRic : ∀ v : TangentSpace I p,
      |ricciTensorAt g p v v| ≤ C * g.metricInner p v v)
    (x y : TangentSpace I p) :
    |ricciTensorAt g p x y| ≤
      C * (g.metricInner p (x + y) (x + y) +
        g.metricInner p x x + g.metricInner p y y) := by
  have hsymm (u v : TangentSpace I p) :
      ricciTensorAt g p u v = ricciTensorAt g p v u := by
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    exact Riemannian.ricciForm_symm
      (g.leviCivitaConnection.isAlgCurvatureForm_curvatureFormAt g
        (g.leviCivitaConnection.isLeviCivita_of_koszulDual g
          (fun X Y W q => g.koszulDualSection_dual X Y W q)) p) u v
  have hpolar :
      2 * ricciTensorAt g p x y =
        ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y := by
    calc
      2 * ricciTensorAt g p x y =
          ricciTensorAt g p x y + ricciTensorAt g p y x := by
            rw [hsymm]
            ring
      _ = ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y := by
            simp only [map_add, LinearMap.add_apply]
            ring
  have htwo :
      |ricciTensorAt g p x y| ≤
        |ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y| := by
    calc
      |ricciTensorAt g p x y| ≤ |2 * ricciTensorAt g p x y| := by
        rw [abs_mul]
        norm_num
        nlinarith [abs_nonneg (ricciTensorAt g p x y)]
      _ = |ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y| := by
        rw [hpolar]
  have htri :
      |ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y| ≤
        |ricciTensorAt g p (x + y) (x + y)| +
          |ricciTensorAt g p x x| + |ricciTensorAt g p y y| := by
    let a : ℝ := ricciTensorAt g p (x + y) (x + y)
    let b : ℝ := ricciTensorAt g p x x
    let c : ℝ := ricciTensorAt g p y y
    change |a - b - c| ≤ |a| + |b| + |c|
    calc
      |a - b - c| ≤ |a - b| + |c| := abs_sub (a - b) c
      _ ≤ (|a| + |b|) + |c| := by
        gcongr
        exact abs_sub a b
      _ = |a| + |b| + |c| := by ring
  calc
    |ricciTensorAt g p x y| ≤
        |ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y| := htwo
    _ ≤ |ricciTensorAt g p (x + y) (x + y)| +
          |ricciTensorAt g p x x| + |ricciTensorAt g p y y| := htri
    _ ≤ C * g.metricInner p (x + y) (x + y) +
          (C * g.metricInner p x x) + (C * g.metricInner p y y) := by
      exact add_le_add (add_le_add (hRic (x + y)) (hRic x)) (hRic y)
    _ = C * (g.metricInner p (x + y) (x + y) +
        g.metricInner p x x + g.metricInner p y y) := by ring

private theorem metricInner_le_endpoint_constant
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRic : RicciQuadraticControlOn g (Ico 0 T) C)
    (t : ℝ) (ht : t ∈ Ico 0 T) (p : M)
    (v : TangentSpace I p) :
    (g t).metricInner p v v ≤
      Real.exp (2 * C * T) * (g 0).metricInner p v v := by
  by_cases ht0 : t = 0
  · subst t
    have hExp : 1 ≤ Real.exp (2 * C * T) := by
      exact Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hC) hT.le)
    simpa only [one_mul] using
      (le_mul_of_one_le_left ((g 0).metricInner_self_nonneg p v) hExp)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hflowIcc := isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    hflow htpos ht.2
  have hsub : Icc (0 : ℝ) t ⊆ Ico 0 T := by
    intro u hu
    exact ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
  have hRicIcc : RicciQuadraticControlOn g (Icc 0 t) C := by
    intro u hu p' x'
    exact hRic u (hsub hu) p' x'
  have hcomp := metricInner_uniform_exp_comparison_of_isRicciFlowOn hC
    hflowIcc (hasAbsoluteRicciBoundOn_of_ricciQuadraticControlOn hRicIcc)
      t ⟨htpos.le, le_rfl⟩ p v
  have hExp : Real.exp (2 * C * t) ≤ Real.exp (2 * C * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg (by norm_num) hC)
  exact hcomp.2.trans
    (mul_le_mul_of_nonneg_right hExp
      ((g 0).metricInner_self_nonneg p v))

private theorem metricInner_ge_endpoint_constant
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRic : RicciQuadraticControlOn g (Ico 0 T) C)
    (t : ℝ) (ht : t ∈ Ico 0 T) (p : M)
    (v : TangentSpace I p) :
    (Real.exp (2 * C * T))⁻¹ * (g 0).metricInner p v v ≤
      (g t).metricInner p v v := by
  by_cases ht0 : t = 0
  · subst t
    have hA : (Real.exp (2 * C * T))⁻¹ ≤ 1 := by
      rw [← Real.exp_neg, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have h : 0 ≤ 2 * C * T := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_right hA
      ((g 0).metricInner_self_nonneg p v)).trans_eq (by simp)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hflowIcc := isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    hflow htpos ht.2
  have hsub : Icc (0 : ℝ) t ⊆ Ico 0 T := by
    intro u hu
    exact ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩
  have hRicIcc : RicciQuadraticControlOn g (Icc 0 t) C := by
    intro u hu p' x'
    exact hRic u (hsub hu) p' x'
  have hcomp := metricInner_uniform_exp_comparison_of_isRicciFlowOn hC
    hflowIcc (hasAbsoluteRicciBoundOn_of_ricciQuadraticControlOn hRicIcc)
      t ⟨htpos.le, le_rfl⟩ p v
  have hExp : (Real.exp (2 * C * T))⁻¹ ≤
      (Real.exp (2 * C * t))⁻¹ := by
    rw [← Real.exp_neg, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have htime : 2 * C * t ≤ 2 * C * T :=
      mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg (by norm_num) hC)
    linarith
  exact (mul_le_mul_of_nonneg_right hExp
      ((g 0).metricInner_self_nonneg p v)).trans hcomp.1

/-- **Math.** A genuine Ricci flow on `[0,T]` with quadratic Ricci control has
the expected two-sided exponential comparison for every metric quadratic
coefficient. -/
theorem metricInner_exp_comparison_of_ricciQuadraticControlOn
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (_hC : 0 ≤ C) (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRic : RicciQuadraticControlOn g (Icc 0 T) C)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (p : M)
    (v : TangentSpace I p) :
    Real.exp (-(2 * C) * t) * (g 0).metricInner p v v ≤
        (g t).metricInner p v v ∧
      (g t).metricInner p v v ≤
        Real.exp ((2 * C) * t) * (g 0).metricInner p v v := by
  exact metricInner_exp_comparison_of_isRicciFlowOn hflow
    (hasAbsoluteRicciBoundOn_of_ricciQuadraticControlOn hRic) ht p v

/-- **Math.** The same comparison on a half-open flow interval, with a single
endpoint-safe constant. -/
theorem metricInner_uniform_exp_comparison_of_ricciQuadraticControlOn
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (_hT : 0 ≤ T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRic : RicciQuadraticControlOn g (Icc 0 T) C) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ (p : M) (v : TangentSpace I p),
      (Real.exp ((2 * C) * T))⁻¹ * (g 0).metricInner p v v ≤
          (g t).metricInner p v v ∧
        (g t).metricInner p v v ≤
          Real.exp ((2 * C) * T) * (g 0).metricInner p v v := by
  exact metricInner_uniform_exp_comparison_of_isRicciFlowOn hC hflow
    (hasAbsoluteRicciBoundOn_of_ricciQuadraticControlOn hRic)

/-! ## One-sided endpoint limits -/

/-- **Math.** Every fixed metric coefficient on a finite half-open Ricci flow
with a uniform quadratic Ricci bound has a genuine left endpoint limit. -/
theorem exists_metricCoefficient_limit_of_ricciQuadraticControlOn
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRic : RicciQuadraticControlOn g (Ico 0 T) C)
    (p : M) (x y : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 L) := by
  let A : ℝ := Real.exp (2 * C * T)
  let S : ℝ :=
    (g 0).metricInner p (x + y) (x + y) +
      (g 0).metricInner p x x + (g 0).metricInner p y y
  let K : ℝ := 2 * C * A * S
  let f : ℝ → ℝ := fun t => (g t).metricInner p x y
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg
      (add_nonneg ((g 0).metricInner_self_nonneg p (x + y))
        ((g 0).metricInner_self_nonneg p x))
      ((g 0).metricInner_self_nonneg p y)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hC) hApos.le) hSnonneg
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt f
        (-2 * ricciTensorAt (g t) p x y) (Ico 0 T) t := by
    intro t ht
    exact hflow.equation t ht p x y
  have hbound : ∀ t ∈ Ico (0 : ℝ) T,
      |(-2 * ricciTensorAt (g t) p x y)| ≤ K := by
    intro t ht
    have hcross := abs_ricciTensorAt_cross_le_of_ricciQuadraticControlOn
      (g t) C p (fun v => hRic t ht p v) x y
    have hsum :
        (g t).metricInner p (x + y) (x + y) +
            (g t).metricInner p x x + (g t).metricInner p y y ≤ A * S := by
      have hxy := metricInner_le_endpoint_constant hT hC hflow hRic t ht p (x + y)
      have hxx := metricInner_le_endpoint_constant hT hC hflow hRic t ht p x
      have hyy := metricInner_le_endpoint_constant hT hC hflow hRic t ht p y
      dsimp [A, S] at hxy hxx hyy ⊢
      calc
        (g t).metricInner p (x + y) (x + y) +
              (g t).metricInner p x x + (g t).metricInner p y y ≤
            A * (g 0).metricInner p (x + y) (x + y) +
              A * (g 0).metricInner p x x +
              A * (g 0).metricInner p y y := by
          exact add_le_add (add_le_add hxy hxx) hyy
        _ = A * ((g 0).metricInner p (x + y) (x + y) +
              (g 0).metricInner p x x + (g 0).metricInner p y y) := by ring
    have hcross' :
        |ricciTensorAt (g t) p x y| ≤ C * (A * S) := hcross.trans
      (mul_le_mul_of_nonneg_left hsum hC)
    have htwo :
        |(-2 * ricciTensorAt (g t) p x y)| ≤ 2 * (C * (A * S)) := by
      calc
        |(-2 * ricciTensorAt (g t) p x y)| =
            2 * |ricciTensorAt (g t) p x y| := by
          rw [abs_mul]
          norm_num
        _ ≤ 2 * (C * (A * S)) :=
          mul_le_mul_of_nonneg_left hcross' (by norm_num)
    dsimp [K]
    convert htwo using 1
    ring
  let Cnn : NNReal := ⟨K, hK⟩
  have hboundNN : ∀ t ∈ Ico (0 : ℝ) T,
      ‖(-2 * ricciTensorAt (g t) p x y : ℝ)‖₊ ≤ Cnn := by
    intro t ht
    apply (NNReal.coe_le_coe).mp
    change ‖(-2 * ricciTensorAt (g t) p x y : ℝ)‖ ≤ K
    simpa [Real.norm_eq_abs] using hbound t ht
  have hLip : LipschitzOnWith Cnn f (Ico 0 T) :=
    Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Ico (0 : ℝ) T) hderiv hboundNN
  obtain ⟨F, hFL, hEq⟩ := hLip.extend_real
  refine ⟨F T, ?_⟩
  have hFT : Tendsto F (nhdsWithin T (Iio T)) (𝓝 (F T)) :=
    hFL.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply hFT.congr'
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
  exact (hEq ⟨le_of_lt ht0, htT⟩).symm

/-- **Math.** Every nonzero diagonal coefficient has a strictly positive
endpoint limit under the same hypotheses. -/
theorem exists_pos_metricCoefficient_limit_of_ricciQuadraticControlOn
    {g : ℝ → RiemannianMetric I M} {T C : ℝ}
    (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRic : RicciQuadraticControlOn g (Ico 0 T) C)
    (p : M) (x : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x x)
        (nhdsWithin T (Iio T)) (𝓝 L) ∧
      (x ≠ 0 → 0 < L) := by
  obtain ⟨L, hL⟩ := exists_metricCoefficient_limit_of_ricciQuadraticControlOn
    hT hC hflow hRic p x x
  refine ⟨L, hL, ?_⟩
  intro hx
  let A : ℝ := Real.exp (2 * C * T)
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  letI : NeBot (nhdsWithin T (Iio T)) := by
    exact nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  let c : ℝ := A⁻¹ * (g 0).metricInner p x x
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (inv_pos.mpr hApos)
      ((g 0).metricInner_self_pos p x hx)
  have hclower : ∀ᶠ t in nhdsWithin T (Iio T),
      c ≤ (g t).metricInner p x x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
    exact metricInner_ge_endpoint_constant hT hC hflow hRic t
      ⟨le_of_lt ht0, htT⟩ p x
  have hcL : c ≤ L := ge_of_tendsto hL hclower
  exact lt_of_lt_of_le hcpos hcL

/-! ## Endpoint patching adapter -/

/-- **Math.** Supplied right-endpoint metric and Ricci coefficient limits are
exactly the `EndpointCoefficientLimits` certificate used by smooth patching.
The two filters are identified by `nhdsWithin_Ioo_eq_nhdsLT`. -/
theorem endpointCoefficientLimits_of_supplied_endpoint_limits
    {T : ℝ} (hT : 0 < T)
    {gLeft gRight : ℝ → RiemannianMetric I M}
    (hMetric : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => (gLeft t).metricInner p x y)
        (nhdsWithin T (Iio T))
        (𝓝 ((gRight T).metricInner p x y)))
    (hRicci : ∀ (p : M) (x y : TangentSpace I p),
      Tendsto (fun t => ricciTensorAt (gLeft t) p x y)
        (nhdsWithin T (Iio T))
        (𝓝 (ricciTensorAt (gRight T) p x y))) :
    EndpointCoefficientLimits 0 T gLeft gRight := by
  refine ⟨?_, ?_⟩
  · intro p x y
    rw [nhdsWithin_Ioo_eq_nhdsLT hT]
    exact hMetric p x y
  · intro p x y
    rw [nhdsWithin_Ioo_eq_nhdsLT hT]
    exact hRicci p x y

/-! ## Curvature-bound endpoint adapters -/

/-- **Math.** The curvature-operator bound used in Chapter 3 supplies the
quadratic Ricci control consumed by the endpoint coefficient theorem. -/
theorem ricciQuadraticControlOn_of_hasCurvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hRm : HasCurvatureOperatorNormLeOnTime g J K) :
    RicciQuadraticControlOn g J ((Module.finrank ℝ E : ℝ) * K) := by
  exact hasAbsoluteRicciBoundOn_of_hasCurvatureOperatorNormLeOnTime hK hRm

/-- **Math.** A bounded-curvature Ricci flow has a one-sided limit for every
fixed metric coefficient at its finite endpoint. -/
theorem exists_metricCoefficient_limit_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Ico 0 T) K)
    (p : M) (x y : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 L) := by
  exact exists_metricCoefficient_limit_of_ricciQuadraticControlOn hT
    (mul_nonneg (Nat.cast_nonneg _) hK) hflow
    (ricciQuadraticControlOn_of_hasCurvatureOperatorNormLeOnTime hK hRm)
    p x y

/-- **Math.** A bounded-curvature Ricci flow has a strictly positive limit for
every nonzero diagonal metric coefficient. -/
theorem exists_pos_metricCoefficient_limit_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K)
    (hflow : IsRicciFlowOn g (Ico 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Ico 0 T) K)
    (p : M) (x : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x x)
        (nhdsWithin T (Iio T)) (𝓝 L) ∧
      (x ≠ 0 → 0 < L) := by
  exact exists_pos_metricCoefficient_limit_of_ricciQuadraticControlOn hT
    (mul_nonneg (Nat.cast_nonneg _) hK) hflow
    (ricciQuadraticControlOn_of_hasCurvatureOperatorNormLeOnTime hK hRm)
    p x

#print axioms RicciQuadraticControlOn
#print axioms metricInner_exp_comparison_of_ricciQuadraticControlOn
#print axioms exists_metricCoefficient_limit_of_ricciQuadraticControlOn
#print axioms exists_pos_metricCoefficient_limit_of_ricciQuadraticControlOn
#print axioms endpointCoefficientLimits_of_supplied_endpoint_limits

end MorganTianLib

end

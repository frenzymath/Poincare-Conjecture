import Topping.RicciFlow.Existence.CurvatureRicciBound

/-!
# Metric coefficients at a bounded-curvature endpoint

This file isolates the part of the finite-time extension argument which is
already forced by the Ricci-flow equation and a uniform Ricci bound.  For a
fixed point and pair of tangent vectors, the equation gives a scalar derivative.
The quadratic Ricci estimate and the metric distortion estimate give a uniform
bound for that derivative on `[0,T)`.  A mean-value/Lipschitz argument then
produces an honest one-sided endpoint limit.  The diagonal limit is positive
for every nonzero vector; no endpoint metric or smooth extension is postulated.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Filter Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [Nonempty M] [CompactSpace M]

/-! Restrict the genuine flow structure from `[0,T)` to a closed subinterval
`[0,s]`, with `s` strictly between the two endpoints. -/

private theorem isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    {g : ℝ → RiemannianMetric I M} {T s : ℝ}
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hs : 0 < s) (hsT : s < T) :
    MorganTianLib.IsRicciFlowOn g (Icc 0 s) := by
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

/-! Polarization turns the diagonal quadratic estimate into a (coarse but
uniform) estimate for a mixed Ricci coefficient. -/

private theorem abs_ricciTensorAt_cross_le_of_quadratic_bound
    (g : RiemannianMetric I M) (M0 : ℝ)
    (hM : 0 ≤ M0) (p : M)
    (hRic : ∀ v : TangentSpace I p,
      |ricciTensorAt g p v v| ≤ M0 * g.metricInner p v v)
    (x y : TangentSpace I p) :
    |ricciTensorAt g p x y| ≤
      M0 * (g.metricInner p (x + y) (x + y) +
        g.metricInner p x x + g.metricInner p y y) := by
  have hpolar :
      2 * ricciTensorAt g p x y =
        ricciTensorAt g p (x + y) (x + y) -
          ricciTensorAt g p x x - ricciTensorAt g p y y := by
    calc
      2 * ricciTensorAt g p x y =
          ricciTensorAt g p x y + ricciTensorAt g p y x := by
            rw [ricciTensorAt_symm]
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
      |a - b - c| ≤ |a - b| + |c| := by
        exact abs_sub (a - b) c
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
    _ ≤ M0 * g.metricInner p (x + y) (x + y) +
          (M0 * g.metricInner p x x) + (M0 * g.metricInner p y y) := by
      exact add_le_add (add_le_add (hRic (x + y)) (hRic x)) (hRic y)
    _ = M0 * (g.metricInner p (x + y) (x + y) +
        g.metricInner p x x + g.metricInner p y y) := by ring

/-! The metric-equivalence estimate can be used on every closed subinterval
strictly below the endpoint.  The resulting upper bound is uniform in time. -/

private theorem metricInner_le_endpoint_constant
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (t : ℝ) (ht : t ∈ Ico 0 T) (p : M)
    (v : TangentSpace I p) :
    (g t).metricInner p v v ≤
      Real.exp (2 * M0 * T) * (g 0).metricInner p v v := by
  by_cases ht0 : t = 0
  · subst t
    have hExp : 1 ≤ Real.exp (2 * M0 * T) := by
      exact Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hM) hT.le)
    simpa only [one_mul] using
      (le_mul_of_one_le_left ((g 0).metricInner_self_nonneg p v) hExp)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hflowIcc := isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    hflow htpos ht.2
  have hRicIcc : HasPointwiseRicciQuadraticBoundOn g M0 (Icc 0 t) := by
    intro u hu p' x'
    exact hRic u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩ p' x'
  have hcomp := metric_equivalence_of_pointwise_ricci_bound
    (s := t) (M0 := M0) htpos.le hM hflowIcc hRicIcc t
      ⟨htpos.le, le_rfl⟩
  have hupper :
      (g t).metricInner p v v ≤
        Real.exp (2 * M0 * t) * (g 0).metricInner p v v := by
    simpa only [one_mul] using hcomp.2 p v
  have hExp : Real.exp (2 * M0 * t) ≤ Real.exp (2 * M0 * T) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg (by norm_num) hM)
  exact hupper.trans
    (mul_le_mul_of_nonneg_right hExp
      ((g 0).metricInner_self_nonneg p v))

private theorem metricInner_ge_endpoint_constant
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (t : ℝ) (ht : t ∈ Ico 0 T) (p : M)
    (v : TangentSpace I p) :
    (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p v v ≤
      (g t).metricInner p v v := by
  by_cases ht0 : t = 0
  · subst t
    have hA : (Real.exp (2 * M0 * T))⁻¹ ≤ 1 := by
      rw [← Real.exp_neg, ← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      have h : 0 ≤ 2 * M0 * T := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_right hA
      ((g 0).metricInner_self_nonneg p v)).trans_eq (by simp)
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hflowIcc := isRicciFlowOn_Icc_of_isRicciFlowOn_Ico
    hflow htpos ht.2
  have hRicIcc : HasPointwiseRicciQuadraticBoundOn g M0 (Icc 0 t) := by
    intro u hu p' x'
    exact hRic u ⟨hu.1, lt_of_le_of_lt hu.2 ht.2⟩ p' x'
  have hcomp := metric_equivalence_of_pointwise_ricci_bound
    (s := t) (M0 := M0) htpos.le hM hflowIcc hRicIcc t
      ⟨htpos.le, le_rfl⟩
  have hlower :
      Real.exp (-(2 * M0 * t)) * (g 0).metricInner p v v ≤
        (g t).metricInner p v v := by
    convert hcomp.1 p v using 1 <;> ring
  have hExp : (Real.exp (2 * M0 * T))⁻¹ ≤
      Real.exp (-(2 * M0 * t)) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    have htime : 2 * M0 * t ≤ 2 * M0 * T :=
      mul_le_mul_of_nonneg_left ht.2.le (mul_nonneg (by norm_num) hM)
    linarith
  exact (mul_le_mul_of_nonneg_right hExp
      ((g 0).metricInner_self_nonneg p v)).trans hlower

/-! Main endpoint coefficient producer. -/

/-- **Math.** A uniform quadratic Ricci bound on a finite half-open flow makes
every fixed metric coefficient the restriction of a globally Lipschitz real
function.  The Lipschitz constant is obtained directly from the Ricci-flow
derivative and the metric-equivalence estimate, so this is a quantitative
endpoint-control statement rather than an assumed extension. -/
theorem exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (p : M) (x y : TangentSpace I p) :
    ∃ C : NNReal, ∃ F : ℝ → ℝ,
      LipschitzWith C F ∧
        EqOn (fun t => (g t).metricInner p x y) F (Ico 0 T) := by
  let A : ℝ := Real.exp (2 * M0 * T)
  let S : ℝ :=
    (g 0).metricInner p (x + y) (x + y) +
      (g 0).metricInner p x x + (g 0).metricInner p y y
  let K : ℝ := 2 * M0 * A * S
  let f : ℝ → ℝ := fun t => (g t).metricInner p x y
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  have hSnonneg : 0 ≤ S := by
    dsimp [S]
    have hxy := (g 0).metricInner_self_nonneg p (x + y)
    have hxx := (g 0).metricInner_self_nonneg p x
    have hyy := (g 0).metricInner_self_nonneg p y
    exact add_nonneg (add_nonneg hxy hxx) hyy
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hM) hApos.le) hSnonneg
  have hderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt f
        (-2 * ricciTensorAt (g t) p x y) (Ico 0 T) t := by
    intro t ht
    exact hflow.equation t ht p x y
  have hbound : ∀ t ∈ Ico (0 : ℝ) T,
      |(-2 * ricciTensorAt (g t) p x y)| ≤ K := by
    intro t ht
    have hcross := abs_ricciTensorAt_cross_le_of_quadratic_bound
      (g t) M0 hM p (fun v => hRic t ht p v) x y
    have hsum :
        (g t).metricInner p (x + y) (x + y) +
            (g t).metricInner p x x + (g t).metricInner p y y ≤ A * S := by
      have hxy := metricInner_le_endpoint_constant hT hM hflow hRic t ht p (x + y)
      have hxx := metricInner_le_endpoint_constant hT hM hflow hRic t ht p x
      have hyy := metricInner_le_endpoint_constant hT hM hflow hRic t ht p y
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
        |ricciTensorAt (g t) p x y| ≤ M0 * (A * S) := hcross.trans
      (mul_le_mul_of_nonneg_left hsum hM)
    have htwo :
        |(-2 * ricciTensorAt (g t) p x y)| ≤
          2 * (M0 * (A * S)) := by
      calc
        |(-2 * ricciTensorAt (g t) p x y)| =
            2 * |ricciTensorAt (g t) p x y| := by
          rw [abs_mul]
          norm_num
        _ ≤ 2 * (M0 * (A * S)) :=
          mul_le_mul_of_nonneg_left hcross' (by norm_num)
    dsimp [K]
    convert htwo using 1 <;> ring
  let C : NNReal := ⟨K, hK⟩
  have hboundNN : ∀ t ∈ Ico (0 : ℝ) T,
      ‖(-2 * ricciTensorAt (g t) p x y : ℝ)‖₊ ≤ C := by
    intro t ht
    apply (NNReal.coe_le_coe).mp
    change ‖(-2 * ricciTensorAt (g t) p x y : ℝ)‖ ≤ K
    simpa [Real.norm_eq_abs] using hbound t ht
  have hLip : LipschitzOnWith C f (Ico (0 : ℝ) T) :=
    Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (convex_Ico (0 : ℝ) T) hderiv hboundNN
  obtain ⟨F, hFL, hEq⟩ := hLip.extend_real
  exact ⟨C, F, hFL, hEq⟩

/-- **Math.** The quantitative Lipschitz extension gives a genuine one-sided
endpoint limit for every fixed metric coefficient. -/
theorem exists_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (p : M) (x y : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 L) := by
  obtain ⟨C, F, hFL, hEq⟩ :=
    exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_pointwiseRicciBound
      hT hM hflow hRic p x y
  refine ⟨F T, ?_⟩
  have hFT : Tendsto F (nhdsWithin T (Iio T)) (𝓝 (F T)) :=
    hFL.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply hFT.congr'
  filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
  exact (hEq ⟨le_of_lt ht0, htT⟩).symm

/-- **Math.** The diagonal endpoint coefficient is strictly positive for every
nonzero tangent vector.  This is the positive-definiteness part of the
endpoint argument at the fixed-coefficient level. -/
theorem exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (p : M) (x : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x x)
        (nhdsWithin T (Iio T)) (𝓝 L) ∧
      (x ≠ 0 → 0 < L) := by
  obtain ⟨L, hL⟩ := exists_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow hRic p x x
  refine ⟨L, hL, ?_⟩
  intro hx
  let A : ℝ := Real.exp (2 * M0 * T)
  have hApos : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  haveI : NeBot (nhdsWithin T (Iio T)) := by
    exact nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  let c : ℝ := A⁻¹ * (g 0).metricInner p x x
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos (inv_pos.mpr hApos) ((g 0).metricInner_self_pos p x hx)
  have hclower : ∀ᶠ t in nhdsWithin T (Iio T),
      c ≤ (g t).metricInner p x x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
    exact metricInner_ge_endpoint_constant hT hM hflow hRic t
      ⟨le_of_lt ht0, htT⟩ p x
  have hcL : c ≤ L := ge_of_tendsto hL hclower
  exact lt_of_lt_of_le hcpos hcL

/-! The coefficient limit also inherits the two-sided metric-equivalence
bound.  Keeping this quantitative statement next to the limit producer makes
the coercivity available to the endpoint-fibre and restart consumers without
repeating the filter argument. -/

/-- **Math.** A uniformly Ricci-bounded flow has an endpoint coefficient whose
quadratic value remains between the two metric-equivalence multiples of the
initial metric. -/
theorem exists_metricCoefficient_limit_with_metric_bounds_of_isRicciFlowOn_of_pointwiseRicciBound
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasPointwiseRicciQuadraticBoundOn g M0 (Ico 0 T))
    (p : M) (x : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x x)
        (nhdsWithin T (Iio T)) (𝓝 L) ∧
      (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤ L ∧
      L ≤ Real.exp (2 * M0 * T) * (g 0).metricInner p x x := by
  obtain ⟨L, hL⟩ :=
    exists_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
      hT hM hflow hRic p x x
  letI : NeBot (nhdsWithin T (Iio T)) :=
    nhdsLT_neBot_of_exists_lt ⟨0, hT⟩
  have hLower : ∀ᶠ t in nhdsWithin T (Iio T),
      (Real.exp (2 * M0 * T))⁻¹ * (g 0).metricInner p x x ≤
        (g t).metricInner p x x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
    exact metricInner_ge_endpoint_constant hT hM hflow hRic t
      ⟨le_of_lt ht0, htT⟩ p x
  have hUpper : ∀ᶠ t in nhdsWithin T (Iio T),
      (g t).metricInner p x x ≤
        Real.exp (2 * M0 * T) * (g 0).metricInner p x x := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hT)] with t htT ht0
    exact metricInner_le_endpoint_constant hT hM hflow hRic t
      ⟨le_of_lt ht0, htT⟩ p x
  exact ⟨L, hL, ge_of_tendsto hL hLower, le_of_tendsto hL hUpper⟩

/-! The same endpoint conclusions can be consumed directly from the source's
Hilbert--Schmidt Ricci norm bound. -/

/-- **Math.** A Hilbert--Schmidt Ricci bound supplies the quantitative
Lipschitz extension of each fixed metric coefficient. -/
theorem exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T))
    (p : M) (x y : TangentSpace I p) :
    ∃ C : NNReal, ∃ F : ℝ → ℝ,
      LipschitzWith C F ∧
        EqOn (fun t => (g t).metricInner p x y) F (Ico 0 T) := by
  exact exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic) p x y

/-- **Math.** A Ricci norm bound on a half-open flow gives every fixed metric
coefficient a genuine one-sided endpoint limit. -/
theorem exists_metricCoefficient_limit_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T))
    (p : M) (x y : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 L) := by
  exact exists_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic) p x y

/-- **Math.** Under the same source norm bound, every nonzero diagonal
coefficient has a strictly positive endpoint limit. -/
theorem exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_hasRicciNormBoundOn
    {g : ℝ → RiemannianMetric I M} {T M0 : ℝ}
    (hT : 0 < T) (hM : 0 ≤ M0)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRic : HasRicciNormBoundOn g M0 (Ico 0 T))
    (p : M) (x : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x x)
        (nhdsWithin T (Iio T)) (𝓝 L) ∧
      (x ≠ 0 → 0 < L) := by
  exact exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
    hT hM hflow
    (hasPointwiseRicciQuadraticBoundOn_of_hasRicciNormBoundOn
      g M0 (Ico 0 T) hRic) p x

/-! The source-facing curvature-bound adapter. -/

/-- **Math.** A uniform pre-endpoint Riemann bound supplies the same
quantitative Lipschitz extension for each fixed metric coefficient. -/
theorem exists_lipschitz_metricCoefficient_extension_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) (p : M)
    (x y : TangentSpace I p) :
    ∃ C : NNReal, ∃ F : ℝ → ℝ,
      LipschitzWith C F ∧
        EqOn (fun t => (g t).metricInner p x y) F (Ico 0 T) := by
  obtain ⟨M0, hM, hRicNorm⟩ :=
    exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore hRm
  exact exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_hasRicciNormBoundOn
    hT hM hflow hRicNorm p x y

/-- **Math.** A uniform pre-endpoint Riemann bound therefore produces the
metric-coefficient endpoint limits and positive diagonal limits above. -/
theorem exists_metricCoefficient_limit_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) (p : M)
    (x y : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (nhdsWithin T (Iio T)) (𝓝 L) := by
  obtain ⟨M0, hM, hRicNorm⟩ :=
    exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore hRm
  exact exists_metricCoefficient_limit_of_isRicciFlowOn_of_hasRicciNormBoundOn
    hT hM hflow hRicNorm p x y

/-! The restart consumers use the interior-left filter `𝓝[Ioo 0 T] T`,
whereas the coefficient producer naturally returns `nhdsWithin T (Iio T)`.
The following corollaries keep that harmless filter conversion at the API
boundary. -/

/-- **Math.** A uniform pre-endpoint Riemann bound produces a metric-coefficient
limit on the interior approach filter used by endpoint patching. -/
theorem exists_metricCoefficient_limit_Ioo_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) (p : M)
    (x y : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x y)
        (𝓝[Ioo (0 : ℝ) T] T) (𝓝 L) := by
  obtain ⟨L, hL⟩ :=
    exists_metricCoefficient_limit_of_hasUniformCurvatureBoundBefore
      hT hflow hRm p x y
  refine ⟨L, ?_⟩
  rw [nhdsWithin_Ioo_eq_nhdsLT hT]
  exact hL

/-- **Math.** The positive diagonal endpoint coefficient has the same
interior-left-filter form. -/
theorem exists_pos_metricCoefficient_limit_Ioo_of_hasUniformCurvatureBoundBefore
    {g : ℝ → RiemannianMetric I M} {T : ℝ}
    (hT : 0 < T)
    (hflow : MorganTianLib.IsRicciFlowOn g (Ico 0 T))
    (hRm : HasUniformCurvatureBoundBefore g T) (p : M)
    (x : TangentSpace I p) :
    ∃ L : ℝ,
      Tendsto (fun t => (g t).metricInner p x x)
        (𝓝[Ioo (0 : ℝ) T] T) (𝓝 L) ∧
      (x ≠ 0 → 0 < L) := by
  obtain ⟨M0, hM, hRicNorm⟩ :=
    exists_hasRicciNormBoundOn_of_hasUniformCurvatureBoundBefore hRm
  obtain ⟨L, hL, hLpos⟩ :=
    exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_hasRicciNormBoundOn
      hT hM hflow hRicNorm p x
  refine ⟨L, ?_, hLpos⟩
  rw [nhdsWithin_Ioo_eq_nhdsLT hT]
  exact hL

#print axioms exists_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_pointwiseRicciBound
#print axioms exists_lipschitz_metricCoefficient_extension_of_isRicciFlowOn_of_hasRicciNormBoundOn
#print axioms exists_metricCoefficient_limit_of_isRicciFlowOn_of_hasRicciNormBoundOn
#print axioms exists_pos_metricCoefficient_limit_of_isRicciFlowOn_of_hasRicciNormBoundOn
#print axioms exists_lipschitz_metricCoefficient_extension_of_hasUniformCurvatureBoundBefore
#print axioms exists_metricCoefficient_limit_of_hasUniformCurvatureBoundBefore
#print axioms exists_metricCoefficient_limit_Ioo_of_hasUniformCurvatureBoundBefore
#print axioms exists_pos_metricCoefficient_limit_Ioo_of_hasUniformCurvatureBoundBefore

end Topping

end

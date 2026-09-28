import MorganTianLib.Ch01.IndexFormFundamental
import MorganTianLib.Ch01.MinimalGeodesicNoConjugate

/-!
# Poincare Ch. 1 - null second variation and the Jacobi equation

This file packages the analytic core of the statement that a null direction of
the second variation along a minimizing geodesic is a Jacobi field. The
curvature operator furnished by a parallel frame is naturally continuous only
on the compact geodesic interval, so the fundamental-lemma argument is stated
with `ContinuousOn` hypotheses throughout.
-/

open Set Filter Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

noncomputable section

namespace MorganTianLib

/-! ### The weak Jacobi equation on a closed interval -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- **Math.** A continuous vector-valued function on `[a,b]` which pairs to zero against
every smooth compactly supported scalar test function vanishes on `[a,b]`.
This is the closed-interval form of
`eq_zero_of_forall_inner_integral_smooth_test`. -/
theorem eq_zero_on_Icc_of_forall_inner_integral_smooth_test
    {a b : ℝ} (hab : a < b) {q : ℝ → F} (hq : ContinuousOn q (Icc a b))
    (htest : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ w : F,
        (∫ t in a..b, f t * (⟪q t, w⟫ : ℝ)) = 0) :
    ∀ t ∈ Icc a b, q t = 0 := by
  have hinter : Set.EqOn q (fun _ => 0) (Ioo a b) := by
    intro t ht
    by_contra hqt
    let w : F := q t
    have hinner : 0 < (⟪q t, w⟫ : ℝ) := by
      simpa [w] using (real_inner_self_pos.mpr hqt)
    have hinnerCont : ContinuousAt (fun s : ℝ => (⟪q s, w⟫ : ℝ)) t :=
      ((hq t (Ioo_subset_Icc_self ht)).continuousAt (Icc_mem_nhds ht.1 ht.2)).inner
        continuousAt_const
    have hpos_nhds : {s : ℝ | 0 < (⟪q s, w⟫ : ℝ)} ∈ 𝓝 t :=
      hinnerCont (isOpen_Ioi.mem_nhds hinner)
    have hSnhds : Ioo a b ∩ {s : ℝ | 0 < (⟪q s, w⟫ : ℝ)} ∈ 𝓝 t :=
      inter_mem (isOpen_Ioo.mem_nhds ht) hpos_nhds
    obtain ⟨f, hfs, hfc, hf, hfr, hft⟩ :=
      exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) hSnhds
    have hcont : ContinuousOn (fun s : ℝ => f s * (⟪q s, w⟫ : ℝ)) (Icc a b) :=
      hf.continuous.continuousOn.mul (hq.inner continuousOn_const)
    have hnonneg : ∀ x ∈ Ioc a b, 0 ≤ f x * (⟪q x, w⟫ : ℝ) := by
      intro x hx
      by_cases hfx : f x = 0
      · simp [hfx]
      · have hxsupp : x ∈ Function.support f := Function.mem_support.mpr hfx
        have hxts : x ∈ tsupport f := subset_closure hxsupp
        have hxin := hfs hxts
        exact mul_nonneg (hfr ⟨x, rfl⟩ |>.1) (le_of_lt hxin.2)
    have hpos : 0 < ∫ x in a..b, f x * (⟪q x, w⟫ : ℝ) :=
      intervalIntegral.integral_pos hab hcont hnonneg
        ⟨t, ⟨ht.1.le, ht.2.le⟩, by simpa [hft] using hinner⟩
    have hzero := htest f hf hfc (hfs.trans inter_subset_left) w
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos
  have hclosure : closure (Ioo a b) = Icc a b := closure_Ioo (ne_of_lt hab)
  exact hinter.of_subset_closure hq continuousOn_const Ioo_subset_Icc_self
    (by rw [hclosure])

/-- **Math.** Weak index orthogonality against smooth compactly supported tests implies
the Jacobi ODE, assuming only continuity on the closed interval. -/
theorem isJacobiSolOn_of_indexForm_eq_zero_smooth_tests_on
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} (hab : a < b)
    {y v dv : ℝ → F}
    (hR : ContinuousOn R (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hdv : ContinuousOn dv (Icc a b))
    (hy' : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv' : ∀ t ∈ Icc a b, HasDerivWithinAt v (dv t) (Icc a b) t)
    (horth : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ w : F,
        indexForm R a b y v (fun t => f t • w)
          (fun t => deriv f t • w) = 0) :
    IsJacobiSolOn R a b y v := by
  let q : ℝ → F := fun t => dv t + R t (y t)
  have hq : ContinuousOn q (Icc a b) := hdv.add (hR.clm_apply hy)
  have htest : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ w : F,
        (∫ t in a..b, f t * (⟪q t, w⟫ : ℝ)) = 0 := by
    intro f hf hfc hfs w
    have hfd : ∀ t : ℝ, HasDerivAt f (deriv f t) t := fun t =>
      (hf.differentiable (by simp) t).hasDerivAt
    have hz' : ∀ t ∈ Icc a b,
        HasDerivWithinAt (fun s => f s • w) (deriv f t • w) (Icc a b) t := by
      intro t _
      exact (hfd t).smul_const w |>.hasDerivWithinAt
    have hzc : ContinuousOn (fun t => f t • w) (Icc a b) :=
      (hf.continuous.smul continuous_const).continuousOn
    have hwc : ContinuousOn (fun t => deriv f t • w) (Icc a b) :=
      ((hf.continuous_deriv (by simp)).smul continuous_const).continuousOn
    have hfa : f a = 0 := by
      by_contra hne
      exact (lt_irrefl a) (hfs (subset_closure (Function.mem_support.mpr hne))).1
    have hfb : f b = 0 := by
      by_contra hne
      exact (lt_irrefl b) (hfs (subset_closure (Function.mem_support.mpr hne))).2
    have hparts := indexForm_eq_boundary_sub_integral_residual hab.le hR
      hv' hz' hy hv hdv hzc hwc
    have hzero := horth f hf hfc hfs w
    rw [hzero, hfa, hfb] at hparts
    have hint : (∫ t in a..b,
        (⟪dv t + R t (y t), f t • w⟫ : ℝ)) = 0 := by
      simpa using hparts.symm
    simpa only [q, real_inner_smul_right] using hint
  have hqzero : ∀ t ∈ Icc a b, q t = 0 :=
    eq_zero_on_Icc_of_forall_inner_integral_smooth_test hab hq htest
  refine ⟨hy', ?_⟩
  intro t ht
  have heq : dv t = -(R t) (y t) := eq_neg_of_add_eq_zero_left (hqzero t ht)
  exact heq ▸ hv' t ht

/-- **Math.** A null direction of a nonnegative index form solves the Jacobi equation,
with all regularity assumptions confined to the closed interval. -/
theorem isJacobiSolOn_of_indexForm_self_eq_zero_of_nonneg_smooth_tests_on
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} (hab : a < b)
    {y v dv : ℝ → F}
    (hRsymm : ∀ t, ∀ x x' : F, ⟪R t x, x'⟫ = ⟪x, R t x'⟫)
    (hR : ContinuousOn R (Icc a b)) (hy : ContinuousOn y (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (hdv : ContinuousOn dv (Icc a b))
    (hy' : ∀ t ∈ Icc a b, HasDerivWithinAt y (v t) (Icc a b) t)
    (hv' : ∀ t ∈ Icc a b, HasDerivWithinAt v (dv t) (Icc a b) t)
    (hself : indexForm R a b y v y v = 0)
    (hnonneg : ∀ (f : ℝ → ℝ), ContDiff ℝ ∞ f → HasCompactSupport f →
      tsupport f ⊆ Ioo a b → ∀ (w : F) (c : ℝ),
        0 ≤ indexForm R a b
          (y + c • fun t => f t • w)
          (v + c • fun t => deriv f t • w)
          (y + c • fun t => f t • w)
          (v + c • fun t => deriv f t • w)) :
    IsJacobiSolOn R a b y v := by
  apply isJacobiSolOn_of_indexForm_eq_zero_smooth_tests_on hab hR hy hv hdv hy' hv'
  intro f hf hfc hfs w
  have hz : Continuous (fun t => f t • w) := hf.continuous.smul continuous_const
  have hdz : Continuous (fun t => deriv f t • w) :=
    (hf.continuous_deriv (by simp)).smul continuous_const
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab.le
  have hyy : IntervalIntegrable (indexIntegrand R y v y v) volume a b :=
    intervalIntegrable_indexIntegrand
      (huIcc ▸ hR) (huIcc ▸ hy) (huIcc ▸ hv) (huIcc ▸ hy) (huIcc ▸ hv)
  have hyz : IntervalIntegrable
      (indexIntegrand R y v (fun t => f t • w) (fun t => deriv f t • w))
      volume a b :=
    intervalIntegrable_indexIntegrand
      (huIcc ▸ hR) (huIcc ▸ hy) (huIcc ▸ hv)
      (huIcc ▸ hz.continuousOn) (huIcc ▸ hdz.continuousOn)
  have hzz : IntervalIntegrable
      (indexIntegrand R (fun t => f t • w) (fun t => deriv f t • w)
        (fun t => f t • w) (fun t => deriv f t • w)) volume a b :=
    intervalIntegrable_indexIntegrand
      (huIcc ▸ hR) (huIcc ▸ hz.continuousOn) (huIcc ▸ hdz.continuousOn)
      (huIcc ▸ hz.continuousOn) (huIcc ▸ hdz.continuousOn)
  exact indexForm_cross_eq_zero_of_nonneg hRsymm hyy hyz hzz hself
    (hnonneg f hf hfc hfs w)

/-- **Math.** The coefficient Jacobi predicate is invariant under pointwise
replacement of both components on the defining interval. -/
theorem IsJacobiSolOn.congr_on
    {R : ℝ → F →L[ℝ] F} {a b : ℝ} {y v y' v' : ℝ → F}
    (h : IsJacobiSolOn R a b y v)
    (hy : Set.EqOn y' y (Icc a b)) (hv : Set.EqOn v' v (Icc a b)) :
    IsJacobiSolOn R a b y' v' where
  hasDerivWithinAt_fst t ht := by
    rw [hv ht]
    exact (h.hasDerivWithinAt_fst t ht).congr (fun _ hs => hy hs) (hy ht)
  hasDerivWithinAt_snd t ht := by
    rw [hy ht]
    exact (h.hasDerivWithinAt_snd t ht).congr (fun _ hs => hv hs) (hv ht)

/-! ### Minimizing geodesics -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]
  [CompleteSpace E] [T2Space (TangentBundle I M)]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** The manifold Jacobi-field predicate is invariant under replacing
both fields by pointwise equal fields on the defining interval. -/
theorem IsJacobiFieldAlongOn.congr_on
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ J' DJ' : ℝ → E} {a b : ℝ}
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hJ : Set.EqOn J' J (Icc a b)) (hDJ : Set.EqOn DJ' DJ (Icc a b)) :
    IsJacobiFieldAlongOn (I := I) g γ J' DJ' a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht₀', hsub, hnhds, hsrc, hJac⟩ := h t₀ ht₀
  refine ⟨α, a', b', hab', ht₀', hsub, hnhds, hsrc, hJac.congr ?_ ?_⟩
  · intro t ht
    simp only [chartVectorRep_apply, hJ (hsub ht)]
  · intro t ht
    simp only [chartVectorRep_apply, hDJ (hsub ht)]

/-- **Math.** A solution of the frame Jacobi ODE lifts to a manifold Jacobi
field. The proof constructs a manifold solution with the same data at the
interior time `0`, then uses uniqueness of the frame ODE. -/
theorem isJacobiFieldAlongOn_frameFieldOf_of_isJacobiSolOn
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W V : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0)
    (hsol : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 1 W V) :
    IsJacobiFieldAlongOn (I := I) g γ
      (frameFieldOf (I := I) g γ e W) (frameFieldOf (I := I) g γ e V) 0 1 := by
  have hab : a < b := ha.trans (by linarith)
  have h0ab : (0 : ℝ) ∈ Icc a b := ⟨ha.le, le_trans zero_le_one hb.le⟩
  obtain ⟨J, DJ, hJac, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn_mem (I := I) hab hgeo hγc h0ab
      (frameLift (I := I) g γ e 0 (W 0)) (frameLift (I := I) g γ e 0 (V 0))
  have hframeSol : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 1
      (frameVec (I := I) g γ e J) (frameVec (I := I) g γ e DJ) :=
    isJacobiSolOn_frameVec hJac hPar hgeo hγc horth ha hb
  have hW0 : frameVec (I := I) g γ e J 0 = W 0 :=
    frameVec_frameLift (I := I) (horth 0 h0ab) (W 0) J (by rw [hJ0])
  have hV0 : frameVec (I := I) g γ e DJ 0 = V 0 :=
    frameVec_frameLift (I := I) (horth 0 h0ab) (V 0) DJ (by rw [hDJ0])
  have hR : ContinuousOn (frameCurvOp (I := I) g γ e) (Icc (0 : ℝ) 1) :=
    (continuousOn_frameCurvOp hPar hgeo hγc).mono fun t ht =>
      ⟨le_trans ha.le ht.1, le_trans ht.2 hb.le⟩
  have hagree := hframeSol.eqOn_of_left hR hsol hW0 hV0
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc a b := fun t ht =>
    ⟨le_trans ha.le ht.1, le_trans ht.2 hb.le⟩
  have hfieldW : Set.EqOn (frameFieldOf (I := I) g γ e W) J (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [frameFieldOf, ← hagree.1 ht]
    exact frameLift_frameVec (I := I) (horth t (hsub ht)) J
  have hfieldV : Set.EqOn (frameFieldOf (I := I) g γ e V) DJ (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [frameFieldOf, ← hagree.2 ht]
    exact frameLift_frameVec (I := I) (horth t (hsub ht)) DJ
  exact (hJac.mono ha.le (by norm_num) hb.le).congr_on hfieldW hfieldV

/-- **Math.** A frame-lifted pair is a manifold Jacobi field exactly when its
coefficients solve the frame Jacobi ODE. This direction re-solves the manifold
equation on the larger interval and uses manifold uniqueness before reading the
result back in the frame. -/
theorem isJacobiSolOn_of_isJacobiFieldAlongOn_frameFieldOf
    (g : RiemannianMetric I M) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E} {W V : ℝ → 𝔼}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ
      (frameFieldOf (I := I) g γ e W) (frameFieldOf (I := I) g γ e V) 0 1) :
    IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 1 W V := by
  have hab : a < b := ha.trans (by linarith)
  have h0ab : (0 : ℝ) ∈ Icc a b := ⟨ha.le, le_trans zero_le_one hb.le⟩
  obtain ⟨J, DJ, hJacLarge, hJ0, hDJ0⟩ :=
    exists_isJacobiFieldAlongOn_mem (I := I) hab hgeo hγc h0ab
      (frameLift (I := I) g γ e 0 (W 0)) (frameLift (I := I) g γ e 0 (V 0))
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc a b := fun t ht =>
    ⟨le_trans ha.le ht.1, le_trans ht.2 hb.le⟩
  have hgeo01 : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) 1) := hgeo.mono hsub
  have hγc01 : ∀ t ∈ Icc (0 : ℝ) 1, ContinuousAt γ t := fun t ht => hγc t (hsub ht)
  have hJacLarge01 := hJacLarge.mono ha.le (show (0 : ℝ) < 1 by norm_num) hb.le
  have hagree : ∀ t ∈ Icc (0 : ℝ) 1,
      frameFieldOf (I := I) g γ e W t = J t ∧
        frameFieldOf (I := I) g γ e V t = DJ t :=
    IsJacobiFieldAlongOn.eqOn_of_initial (I := I) (by norm_num) hgeo01 hγc01
      hJac hJacLarge01 (by rw [frameFieldOf, hJ0]) (by rw [frameFieldOf, hDJ0])
  have hframeSol : IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 1
      (frameVec (I := I) g γ e J) (frameVec (I := I) g γ e DJ) :=
    isJacobiSolOn_frameVec hJacLarge hPar hgeo hγc horth ha hb
  have hcoeffW : Set.EqOn W (frameVec (I := I) g γ e J) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (frameVec_frameLift (I := I) (horth t (hsub ht)) (W t) J
      (by rw [← (hagree t ht).1]; rfl)).symm
  have hcoeffV : Set.EqOn V (frameVec (I := I) g γ e DJ) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact (frameVec_frameLift (I := I) (horth t (hsub ht)) (V t) DJ
      (by rw [← (hagree t ht).2]; rfl)).symm
  exact hframeSol.congr_on hcoeffW hcoeffV

/-- **Math.** The index form of every globally `C^3`, fixed-endpoint coefficient field is
nonnegative along a minimizing geodesic. -/
theorem indexForm_nonneg_smooth_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    {W : ℝ → 𝔼} (hW : ContDiff ℝ 3 W) (hW0 : W 0 = 0) (hW1 : W 1 = 0) :
    0 ≤ indexForm (frameCurvOp (I := I) g γ e) 0 1
      W (deriv W) W (deriv W) := by
  let c : ℝ := 1 / 2
  have hc0 : 0 < c := by norm_num [c]
  have hc1 : c < 1 := by norm_num [c]
  have hsplit := indexForm_nonneg_of_minimizing (I := I) g hg ha hb hc0 hc1
    hgeo hγc hPar horth hmin hW.contDiffOn hW hW0 hW1 rfl
  have hR : ContinuousOn (frameCurvOp (I := I) g γ e) (Icc a b) :=
    continuousOn_frameCurvOp hPar hgeo hγc
  have hWd : Continuous (deriv W) := hW.continuous_deriv (by norm_num)
  have hsub0 : Icc (0 : ℝ) c ⊆ Icc a b := fun t ht =>
    ⟨le_trans ha.le ht.1, le_trans ht.2 (le_trans hc1.le hb.le)⟩
  have hsub1 : Icc c (1 : ℝ) ⊆ Icc a b := fun t ht =>
    ⟨le_trans ha.le (le_trans hc0.le ht.1), le_trans ht.2 hb.le⟩
  have hint0 : IntervalIntegrable
      (indexIntegrand (frameCurvOp (I := I) g γ e) W (deriv W) W (deriv W))
      volume 0 c := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;>
      rw [uIcc_of_le hc0.le]
    exacts [hR.mono hsub0, hW.continuous.continuousOn, hWd.continuousOn,
      hW.continuous.continuousOn, hWd.continuousOn]
  have hint1 : IntervalIntegrable
      (indexIntegrand (frameCurvOp (I := I) g γ e) W (deriv W) W (deriv W))
      volume c 1 := by
    refine intervalIntegrable_indexIntegrand ?_ ?_ ?_ ?_ ?_ <;>
      rw [uIcc_of_le hc1.le]
    exacts [hR.mono hsub1, hW.continuous.continuousOn, hWd.continuousOn,
      hW.continuous.continuousOn, hWd.continuousOn]
  rwa [indexForm_add_adjacent hint0 hint1] at hsplit

/-- **Math.** Along a minimizing geodesic, a globally `C^3` coefficient field
vanishing at `0` and `1` has zero index if and only if it satisfies the Jacobi
equation in the parallel frame. -/
theorem indexForm_self_eq_zero_iff_isJacobiSolOn_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    {W : ℝ → 𝔼} (hW : ContDiff ℝ 3 W) (hW0 : W 0 = 0) (hW1 : W 1 = 0) :
    indexForm (frameCurvOp (I := I) g γ e) 0 1
        W (deriv W) W (deriv W) = 0 ↔
      IsJacobiSolOn (frameCurvOp (I := I) g γ e) 0 1 W (deriv W) := by
  have hR : ContinuousOn (frameCurvOp (I := I) g γ e) (Icc (0 : ℝ) 1) :=
    (continuousOn_frameCurvOp hPar hgeo hγc).mono fun t ht =>
      ⟨le_trans ha.le ht.1, le_trans ht.2 hb.le⟩
  constructor
  · intro hself
    have hWd : ContDiff ℝ 2 (deriv W) := by
      simpa using hW.deriv'
    apply isJacobiSolOn_of_indexForm_self_eq_zero_of_nonneg_smooth_tests_on
      (show (0 : ℝ) < 1 by norm_num) (frameCurvOp_selfAdjoint (I := I) g γ e)
      hR hW.continuous.continuousOn
      (hW.continuous_deriv (by norm_num)).continuousOn
      (hWd.continuous_deriv (by norm_num)).continuousOn
      (fun t _ => (hW.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt)
      (fun t _ => (hWd.differentiable (by norm_num) t).hasDerivAt.hasDerivWithinAt)
      hself
    intro f hf hfc hfs w c
    let Z : ℝ → 𝔼 := fun t => f t • w
    have hf3 : ContDiff ℝ 3 f :=
      hf.of_le (ENat.natCast_le_of_coe_top_le_withTop (by rfl) 3)
    have hZ : ContDiff ℝ 3 Z := hf3.smul contDiff_const
    have hsum : ContDiff ℝ 3 (W + c • Z) := hW.add (hZ.const_smul c)
    have hfa : f 0 = 0 := by
      by_contra hne
      exact (lt_irrefl (0 : ℝ))
        (hfs (subset_closure (Function.mem_support.mpr hne))).1
    have hfb : f 1 = 0 := by
      by_contra hne
      exact (lt_irrefl (1 : ℝ))
        (hfs (subset_closure (Function.mem_support.mpr hne))).2
    have hsum0 : (W + c • Z) 0 = 0 := by simp [Z, hW0, hfa]
    have hsum1 : (W + c • Z) 1 = 0 := by simp [Z, hW1, hfb]
    have hZderiv : ∀ t : ℝ, HasDerivAt Z (deriv f t • w) t := fun t => by
      exact ((hf.differentiable (by simp) t).hasDerivAt).smul_const w
    have hderiv : deriv (W + c • Z) =
        deriv W + c • fun t => deriv f t • w := by
      funext t
      exact ((hW.differentiable (by norm_num) t).hasDerivAt.add
        ((hZderiv t).const_smul c)).deriv
    have hnonneg := indexForm_nonneg_smooth_of_minimizing (I := I) g hg ha hb
      hgeo hγc hPar horth hmin hsum hsum0 hsum1
    rw [hderiv] at hnonneg
    simpa only [Z] using hnonneg
  · intro hsol
    exact hsol.indexForm_self_eq_zero (by norm_num) hR hW0 hW1

/-- **Math.** Along a minimizing geodesic, the index of a globally `C^3`
fixed-endpoint field is zero if and only if its frame lift is a manifold Jacobi
field. This is the null-index/Jacobi equivalence; identifying the index with the
second derivative of a caller's arbitrary variation is a separate interface. -/
theorem indexForm_self_eq_zero_iff_isJacobiFieldAlongOn_of_minimizing
    [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) {γ : ℝ → M} {a b : ℝ}
    {e : Fin (finrank ℝ E) → ℝ → E}
    (ha : a < 0) (hb : 1 < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hPar : ∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
    (horth : ∀ t ∈ Icc a b, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    {W : ℝ → 𝔼} (hW : ContDiff ℝ 3 W) (hW0 : W 0 = 0) (hW1 : W 1 = 0) :
    indexForm (frameCurvOp (I := I) g γ e) 0 1
        W (deriv W) W (deriv W) = 0 ↔
      IsJacobiFieldAlongOn (I := I) g γ
        (frameFieldOf (I := I) g γ e W)
        (frameFieldOf (I := I) g γ e (deriv W)) 0 1 := by
  have hcoeff := indexForm_self_eq_zero_iff_isJacobiSolOn_of_minimizing
    (I := I) g hg ha hb hgeo hγc hPar horth hmin hW hW0 hW1
  constructor
  · intro hzero
    exact isJacobiFieldAlongOn_frameFieldOf_of_isJacobiSolOn (I := I) g ha hb
      hgeo hγc hPar horth (hcoeff.mp hzero)
  · intro hJac
    apply hcoeff.mpr
    exact isJacobiSolOn_of_isJacobiFieldAlongOn_frameFieldOf (I := I) g ha hb
      hgeo hγc hPar horth hJac

end MorganTianLib

import DoCarmoLib.Riemannian.Variation.BonnetMyers
import MorganTianLib.Ch01.MinimalGeodesicNoConjugate

/-!
# Lee Chapter 12: the minimizing-index input to Myers' theorem

Morgan--Tian's second-variation theorem proves that a distance-minimizing
geodesic has nonnegative index form for smooth fields vanishing at its
endpoints.  This file translates that result to the intrinsic index-form
convention used by DoCarmoLib's Bonnet--Myers assembly.

The translation is explicit about the two convention differences: Morgan--Tian
uses coefficients in a parallel frame and writes the curvature term with the
opposite first-slot order, while DoCarmoLib uses model-space fields along the
curve.  The final theorem specializes to the standard field
`sin(pi t) e_j(t)`.
-/

open Set Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace LeeLib.Ch12

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

private theorem morgan_curvatureFormAt_eq_doCarmo
    (g : RiemannianMetric I M) (nabla : AffineConnection I M) (p : M)
    (v w z t : TangentSpace I p) :
    MorganTianLib.curvatureFormAt g nabla p v w z t =
      nabla.curvatureFormAt g p v w z t := by
  rw [MorganTianLib.curvatureFormAt_def,
    nabla.curvatureFormAt_eq g p
      (X := MorganTianLib.extendVector p v)
      (Y := MorganTianLib.extendVector p w)
      (Z := MorganTianLib.extendVector p z)
      (T := MorganTianLib.extendVector p t)]
  all_goals simp

private theorem indexIntegrand_eq_morgan_frame
    (g : RiemannianMetric I M) {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {V DV : ℝ → E} {t : ℝ}
    (horth : ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0) :
    g.metricInner (γ t) (DV t : TangentSpace I (γ t)) (DV t) -
        g.leviCivitaConnection.curvatureFormAt g (γ t)
          (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
          (DCVelocity (I := I) γ t) (V t) =
      MorganTianLib.indexIntegrand
        (MorganTianLib.frameCurvOp (I := I) g γ e)
        (MorganTianLib.frameVec (I := I) g γ e V)
        (MorganTianLib.frameVec (I := I) g γ e DV)
        (MorganTianLib.frameVec (I := I) g γ e V)
        (MorganTianLib.frameVec (I := I) g γ e DV) t := by
  rw [← MorganTianLib.indexIntegrand_frameVec (I := I) horth]
  rw [morgan_curvatureFormAt_eq_doCarmo]
  have hanti := Riemannian.Jacobi.curvatureFormAt_antisymm_fst (I := I) g (γ t)
    (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
    (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
  change _ - _ = _ +
    g.leviCivitaConnection.curvatureFormAt g (γ t)
      (V t : TangentSpace I (γ t)) (DCVelocity (I := I) γ t)
      (DCVelocity (I := I) γ t) (V t : TangentSpace I (γ t))
  rw [← neg_eq_iff_eq_neg.mpr hanti]
  ring

private theorem indexForm_eq_morgan_frame
    (g : RiemannianMetric I M) {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {V DV : ℝ → E}
    (horth : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i j,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t) =
        if i = j then 1 else 0) :
    Riemannian.Variation.indexForm (I := I) g γ V DV 0 1 =
      MorganTianLib.indexForm (MorganTianLib.frameCurvOp (I := I) g γ e) 0 1
        (MorganTianLib.frameVec (I := I) g γ e V)
        (MorganTianLib.frameVec (I := I) g γ e DV)
        (MorganTianLib.frameVec (I := I) g γ e V)
        (MorganTianLib.frameVec (I := I) g γ e DV) := by
  rw [Riemannian.Variation.indexForm_def, MorganTianLib.indexForm_def]
  exact intervalIntegral.integral_congr (fun t ht =>
    indexIntegrand_eq_morgan_frame (I := I) g
      (horth t (by simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht)))

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

private theorem frameVec_smul_frame
    (g : RiemannianMetric I M) {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ} (c : ℝ → ℝ)
    (horth : ∀ i k,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e k t) =
        if i = k then 1 else 0)
    (j : Fin (Module.finrank ℝ E)) :
    MorganTianLib.frameVec (I := I) g γ e (fun s => c s • e j s) t =
      c t • (𝔟 j : 𝔼) := by
  classical
  have hcoeff : ∀ i,
      MorganTianLib.frameCoeff (I := I) g γ e (fun s => c s • e j s) i t =
        c t * (if j = i then 1 else 0) := by
    intro i
    unfold MorganTianLib.frameCoeff
    change g.metricInner (γ t) ((c t • e j t : E) : TangentSpace I (γ t))
      (e i t : TangentSpace I (γ t)) = _
    have hv : c t • (e j t : TangentSpace I (γ t)) =
        ((c t • e j t : E) : TangentSpace I (γ t)) := rfl
    calc
      g.metricInner (γ t) ((c t • e j t : E) : TangentSpace I (γ t)) (e i t) =
          c t * g.metricInner (γ t) (e j t : TangentSpace I (γ t)) (e i t) := by
            simpa only [hv] using g.metricInner_smul_left (γ t) (c t)
              (e j t : TangentSpace I (γ t)) (e i t : TangentSpace I (γ t))
      _ = c t * (if j = i then 1 else 0) := by rw [horth]
  simp only [MorganTianLib.frameVec, hcoeff]
  simp [apply_ite]

private theorem deriv_smul_const_real
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → ℝ) (hf : Differentiable ℝ f) (v : F) (t : ℝ) :
    deriv (fun s => f s • v) t = deriv f t • v := by
  exact ((hf t).hasDerivAt.smul_const v).deriv

set_option maxHeartbeats 1800000 in
/-- **Math.** A distance-minimizing geodesic has nonnegative index form in
the standard Bonnet--Myers sine direction `V(t) = sin(pi t)e_j(t)`, where
`e_j` belongs to a parallel orthonormal frame.  The frame is assumed on the
larger interval `[-1,2]` because the broken exponential variation proving the
second-variation inequality needs open endpoint room around `[0,1]`. -/
theorem sine_indexForm_nonneg_of_minimizing [CompleteSpace M]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} {ℓ : ℝ}
    (hγc : Continuous γ) (hgeo : Riemannian.Geodesic.IsGeodesic (I := I) g γ)
    (hdist : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * ℓ)
    {e : Fin (Module.finrank ℝ E) → ℝ → E}
    (hpar : ∀ i, Riemannian.Jacobi.IsParallelFieldAlongOn
      (I := I) g γ (e i) (-1) 2)
    (horth : ∀ t ∈ Icc (-1 : ℝ) 2, ∀ i k,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e k t) =
        if i = k then 1 else 0)
    (j : Fin (Module.finrank ℝ E)) :
    0 ≤ Riemannian.Variation.indexForm (I := I) g γ
      (fun t => Real.sin (Real.pi * t) • e j t)
      (fun t => deriv (fun t => Real.sin (Real.pi * t)) t • e j t) 0 1 := by
  classical
  let φ : ℝ → ℝ := fun t => Real.sin (Real.pi * t)
  let W : ℝ → 𝔼 := fun t => φ t • (𝔟 j : 𝔼)
  have hφ : ContDiff ℝ ∞ φ := by
    dsimp [φ]
    fun_prop
  have hW : ContDiff ℝ ∞ W := by
    dsimp [W]
    fun_prop
  have hdW : deriv W = fun t => deriv φ t • (𝔟 j : 𝔼) := by
    funext t
    exact deriv_smul_const_real φ (hφ.differentiable (by simp)) (𝔟 j : 𝔼) t
  have hParMT : ∀ i, MorganTianLib.IsParallelAlongOn (I := I) g γ (e i) (-1) 2 := by
    intro i
    simpa only [MorganTianLib.IsParallelAlongOn,
      Riemannian.Jacobi.IsParallelFieldAlongOn] using hpar i
  have hmin : Real.sqrt (Riemannian.Geodesic.speedSq (I := I) g γ 0) ≤
      dist (γ 0) (γ 1) := by
    have hd01 : dist (γ 0) (γ 1) = ℓ := by
      simpa using hdist 0 (by norm_num) 1 (by norm_num)
    have hdist' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        dist (γ s) (γ t) = |s - t| * dist (γ 0) (γ 1) := by
      intro s hs t ht
      rw [hdist s hs t ht, hd01]
    have hs := Riemannian.Exponential.sqrt_speedSq_eq_dist_of_minimizing
      (I := I) g hg (lo := (-1 : ℝ)) (hi := (2 : ℝ))
      (q₁ := γ 0) (q₂ := γ 1) (by norm_num) (by norm_num)
      (hgeo.isGeodesicOn _) hγc.continuousOn rfl rfl hdist'
    exact hs.le
  have hW3 : ContDiff ℝ 3 W := contDiff_infty.mp hW 3
  have hparts := MorganTianLib.indexForm_nonneg_of_minimizing
    (I := I) g hg (a := (-1 : ℝ)) (b := (2 : ℝ)) (c := (1 / 2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (hgeo.isGeodesicOn _) (fun t _ => hγc.continuousAt)
    hParMT horth hmin hW3.contDiffOn hW3
    (by simp [W, φ]) (by simp [W, φ]) rfl
  have hRwide : ContinuousOn (MorganTianLib.frameCurvOp (I := I) g γ e)
      (Icc (-1 : ℝ) 2) :=
    MorganTianLib.continuousOn_frameCurvOp hParMT (hgeo.isGeodesicOn _)
      (fun t _ => hγc.continuousAt)
  have hWcont : ContinuousOn W (Icc (-1 : ℝ) 2) := hW.continuous.continuousOn
  have hdWcont : ContinuousOn (deriv W) (Icc (-1 : ℝ) 2) := by
    rw [hdW]
    have hdφ : ContDiff ℝ ∞ (deriv φ) := (contDiff_infty_iff_deriv.mp hφ).2
    exact (hdφ.continuous.smul continuous_const).continuousOn
  have hint₀ : IntervalIntegrable
      (MorganTianLib.indexIntegrand (MorganTianLib.frameCurvOp (I := I) g γ e)
        W (deriv W) W (deriv W)) volume 0 (1 / 2 : ℝ) := by
    apply MorganTianLib.intervalIntegrable_indexIntegrand
    all_goals
      first
      | exact hRwide.mono (by
          rw [uIcc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
      | exact hWcont.mono (by
          rw [uIcc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
      | exact hdWcont.mono (by
          rw [uIcc_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
  have hint₁ : IntervalIntegrable
      (MorganTianLib.indexIntegrand (MorganTianLib.frameCurvOp (I := I) g γ e)
        W (deriv W) W (deriv W)) volume (1 / 2 : ℝ) 1 := by
    apply MorganTianLib.intervalIntegrable_indexIntegrand
    all_goals
      first
      | exact hRwide.mono (by
          rw [uIcc_of_le (show (1 / 2 : ℝ) ≤ 1 by norm_num)]
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
      | exact hWcont.mono (by
          rw [uIcc_of_le (show (1 / 2 : ℝ) ≤ 1 by norm_num)]
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
      | exact hdWcont.mono (by
          rw [uIcc_of_le (show (1 / 2 : ℝ) ≤ 1 by norm_num)]
          intro t ht
          constructor <;> linarith [ht.1, ht.2])
  rw [MorganTianLib.indexForm_add_adjacent hint₀ hint₁] at hparts
  have horth01 : ∀ t ∈ Icc (0 : ℝ) 1, ∀ i k,
      g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e k t) =
        if i = k then 1 else 0 := by
    intro t ht
    exact horth t (by constructor <;> linarith [ht.1, ht.2])
  have hframe :
      MorganTianLib.indexForm (MorganTianLib.frameCurvOp (I := I) g γ e) 0 1
        (MorganTianLib.frameVec (I := I) g γ e (fun t => φ t • e j t))
        (MorganTianLib.frameVec (I := I) g γ e (fun t => deriv φ t • e j t))
        (MorganTianLib.frameVec (I := I) g γ e (fun t => φ t • e j t))
        (MorganTianLib.frameVec (I := I) g γ e (fun t => deriv φ t • e j t)) =
      MorganTianLib.indexForm (MorganTianLib.frameCurvOp (I := I) g γ e) 0 1
        W (deriv W) W (deriv W) := by
    unfold MorganTianLib.indexForm
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := by
      simpa [uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using ht
    have horth_t := horth01 t ht'
    unfold MorganTianLib.indexIntegrand
    rw [frameVec_smul_frame (I := I) g φ horth_t j,
      frameVec_smul_frame (I := I) g (deriv φ) horth_t j, hdW]
  rw [indexForm_eq_morgan_frame (I := I) g horth01, hframe]
  simpa only [φ] using hparts

end LeeLib.Ch12

end

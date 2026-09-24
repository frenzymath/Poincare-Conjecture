import MorganTianLib.Ch01.GeodesicCutoffField
import MorganTianLib.Ch01.ScaledVelocityFrame
import MorganTianLib.Ch03.RicciFlow.CurvatureCoordinateVariation
import MorganTianLib.Ch03.RicciFlow.DistanceVariationCutoff

/-! # The traced cutoff index inequality from geodesic minimality

This is the geometric second-variation input of Morgan--Tian Claim 3.24.
The parallel frame has its first vector in the velocity direction; summing
over the remaining vectors gives exactly `dim M - 1` kinetic terms and
the full Ricci curvature term.
-/

open Set Filter Riemannian Riemannian.Geodesic Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace
noncomputable section
namespace MorganTianLib
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

section Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Ricci curvature evaluated twice on the curve velocity. -/
def metricCurveRicci (g : RiemannianMetric I M) (γ : ℝ → M) (u : ℝ) : ℝ :=
  ricciTensorAt g (γ u) (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ))
    (mfderiv 𝓘(ℝ, ℝ) I γ u (1 : ℝ))

/-- **Math.** The traced cutoff second-variation inequality, in a constant-speed
parameter on `[0,1]`. Its parameter radius is the physical radius divided by
the speed. `hasGeodesicCutoffSecondVariation_of_minimizing` derives this
property from minimality, with `N = dim M - 1`. -/
def HasGeodesicCutoffSecondVariation (g : RiemannianMetric I M) (γ : ℝ → M)
    (N : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → 2 * r ≤ 1 →
    0 ≤ -(∫ u in (0 : ℝ)..1, metricCurveRicci g γ u)
      + (∫ u in (0 : ℝ)..r,
          leftDistanceCutoffWeight r u * metricCurveRicci g γ u + N / r ^ 2)
      + (∫ u in (1 - r)..1,
          rightDistanceCutoffWeight 1 r u * metricCurveRicci g γ u + N / r ^ 2)

end Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

local notation "𝔼" => EuclideanSpace ℝ (Fin (finrank ℝ E))
local notation "𝔟" => EuclideanSpace.basisFun (Fin (finrank ℝ E)) ℝ

/-- **Math.** A regular minimizing geodesic satisfies the traced endpoint
cutoff inequality. All variations and both cutoff corners are constructed;
no second-variation or Ricci-integral inequality is assumed. -/
theorem hasGeodesicCutoffSecondVariation_of_minimizing
    [CompleteSpace M] [T2Space (TangentBundle I M)]
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    {γ : ℝ → M} (hγ : IsGeodesic g γ) (hcγ : Continuous γ)
    (hmin : Real.sqrt (speedSq (I := I) g γ 0) ≤ dist (γ 0) (γ 1))
    (hv : mfderivVelocity (I := I) (E := E) γ (-1) ≠ 0) :
    HasGeodesicCutoffSecondVariation g γ ((finrank ℝ E : ℝ) - 1) := by
  classical
  let L := Real.sqrt (speedSq (I := I) g γ (-1))
  have hpos : 0 < L := Real.sqrt_pos.mpr (g.metricInner_self_pos _ _ hv)
  have hsize : g.metricInner (γ (-1)) (mfderivVelocity (I := I) (E := E) γ (-1))
      (mfderivVelocity (I := I) (E := E) γ (-1)) = L ^ 2 :=
    (Real.sq_sqrt (g.metricInner_self_nonneg _ _)).symm
  have hgeo := hγ.isGeodesicOn (Icc (-1 : ℝ) 2)
  obtain ⟨e, hPar, horth, hrad⟩ := exists_orthonormalParallelFrameAlong_scaled_velocity
    (I := I) (by norm_num : (-1 : ℝ) < 2) hpos hgeo (fun _ _ => hcγ.continuousAt) hsize
  let R := frameCurvOp (I := I) g γ e
  let S : Finset (Fin (finrank ℝ E)) := Finset.univ.erase 0
  let Q := fun (i : Fin (finrank ℝ E)) (t : ℝ) => ⟪R t (𝔟 i), 𝔟 i⟫
  have hcard : (S.card : ℝ) = (finrank ℝ E : ℝ) - 1 := by
    simp [S, Finset.card_erase_of_mem, Nat.cast_sub ((NeZero.one_le : 1 ≤ finrank ℝ E))]
  have hsub : Icc (0 : ℝ) 1 ⊆ Icc (-1 : ℝ) 2 := by intro t ht; constructor <;> linarith [ht.1, ht.2]
  have hRc : ContinuousOn R (Icc (0 : ℝ) 1) :=
    (continuousOn_frameCurvOp hPar hgeo (fun _ _ => hcγ.continuousAt)).mono hsub
  have hQc (i : Fin (finrank ℝ E)) : ContinuousOn (Q i) (Icc (0 : ℝ) 1) :=
    (hRc.clm_apply continuousOn_const).inner continuousOn_const
  have htrace (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ∑ i ∈ S, Q i t = metricCurveRicci g γ t := by
    have hLC : g.leviCivitaConnection.IsLeviCivita g :=
      g.leviCivitaConnection.isLeviCivita_of_koszulDual g
        (fun X Y W q => g.koszulDualSection_dual X Y W q)
    have htr := trace_frameCurvOp_eq_ricciAt (I := I) hLC (horth t (hsub ht))
    rw [ricciAt_leviCivita_eq_ricciTensorAt, LinearMap.trace_eq_sum_inner _ 𝔟] at htr
    have hall : ∑ i, Q i t = metricCurveRicci g γ t := by
      simpa only [Q, R, real_inner_comm, metricCurveRicci,
        ContinuousLinearMap.coe_coe, mfderivVelocity] using htr
    have hz : Q 0 t = 0 := by
      dsimp [Q, R]
      rw [frameCurvOp_scaled_radial_eq_zero g γ e t L (hrad t (hsub ht)), inner_zero_left]
    have hs := Finset.sum_erase_add (s := Finset.univ) (f := fun i => Q i t)
      (Finset.mem_univ (0 : Fin (finrank ℝ E)))
    rw [hz, add_zero] at hs
    exact hs.trans hall
  have hq : ContinuousOn (metricCurveRicci g γ) (Icc (0 : ℝ) 1) :=
    (continuousOn_finsetSum S (fun i _ => hQc i)).congr (fun t ht => (htrace t ht).symm)
  intro r hr hr1
  have hsumIntegral {x y A : ℝ} {f : ℝ → ℝ}
      (hxy : uIcc x y ⊆ Icc (0 : ℝ) 1) (hf : ContinuousOn f (uIcc x y)) :
      (∑ i ∈ S, ∫ t in x..y, A - f t * Q i t) =
        ∫ t in x..y, ((finrank ℝ E : ℝ) - 1) * A - f t * metricCurveRicci g γ t := by
    rw [← intervalIntegral.integral_finsetSum (s := S) (μ := volume)
      (f := fun i t => A - f t * Q i t) (fun i _ =>
        (continuousOn_const.sub (hf.mul ((hQc i).mono hxy))).intervalIntegrable)]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
      hcard, htrace t (hxy ht)]
  have hLsub : uIcc (0 : ℝ) r ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le hr.le]; exact Icc_subset_Icc le_rfl (by linarith)
  have hMsub : uIcc r (1 - r) ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by linarith : r ≤ 1 - r)]
    exact Icc_subset_Icc hr.le (by linarith)
  have hRsub : uIcc (1 - r) 1 ⊆ Icc (0 : ℝ) 1 := by
    rw [uIcc_of_le (by linarith : 1 - r ≤ 1)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have hnn := Finset.sum_nonneg (s := S) (fun i _ =>
    cutoff_indexForm_nonneg_of_minimizing (I := I) g hg (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (1 : ℝ) < 2) hr hr1 hgeo (fun _ _ => hcγ.continuousAt)
      hPar horth hmin (𝔟 i))
  simp only [basisFun_inner (E := E), if_true] at hnn
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hnn
  have hIL := hsumIntegral (A := 1 / r ^ 2) (f := fun t => t ^ 2 / r ^ 2)
    hLsub (by fun_prop)
  have hIM := hsumIntegral (A := 0) (f := fun _ => 1) hMsub continuousOn_const
  have hIR := hsumIntegral (A := 1 / r ^ 2) (f := fun t => (1 - t) ^ 2 / r ^ 2)
    hRsub (by fun_prop)
  simp only [mul_zero, one_mul, zero_sub] at hIM
  simp only [mul_one_div] at hIL hIR
  change 0 ≤ (∑ i ∈ S, ∫ t in (0 : ℝ)..r, 1 / r ^ 2 - t ^ 2 / r ^ 2 * Q i t)
    + (∑ i ∈ S, ∫ t in r..(1 - r), -Q i t)
    + (∑ i ∈ S, ∫ t in (1 - r)..1, 1 / r ^ 2 - (1 - t) ^ 2 / r ^ 2 * Q i t) at hnn
  rw [hIL, hIM, hIR] at hnn
  exact cutoff_secondVariation_of_threePieceIndex hr hr1 hq hnn

end MorganTianLib

import MorganTianLib.Ch03.RicciFlow.VolumeEvolution
import MorganTianLib.Ch03.RicciFlow.MetricDistortion
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Scalar volume-density distortion and curvature-operator notation

This module records the scalar part of Morgan--Tian's metric/volume distortion
argument and the operator notation used in the evolving-frame curvature
equation.  The scalar estimate is deliberately stated for a positive density
with a prescribed evolution law, so it can be applied to chart volume density
after `hasDerivWithinAt_chartVolumeDensity_of_isRicciFlowOn`.
-/

open Set Matrix Riemannian Bundle
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A scalar density satisfies the volume evolution equation on `J`. -/
def IsVolumeDensityEvolution (rho R : ℝ → ℝ) (J : Set ℝ) : Prop :=
  ∀ t ∈ J, HasDerivWithinAt rho (-R t * rho t) J t

/-- **Math.** A uniform scalar-curvature bound on the time interval. -/
def HasAbsoluteScalarBoundOn (R : ℝ → ℝ) (J : Set ℝ) (C : ℝ) : Prop :=
  ∀ t ∈ J, |R t| ≤ C

/-- **Math.** A curvature-operator bound controls the scalar curvature by a
dimension-dependent constant.  The deliberately coarse factor `n^2` is enough
for the volume-distortion estimate: one factor `n` bounds each diagonal Ricci
entry and the second counts the orthonormal trace. -/
theorem abs_scalarCurvatureAt_le_finrank_sq_mul_of_hasCurvatureOperatorNormLeAt
    (g : RiemannianMetric I M) {K : ℝ} (hK : 0 ≤ K) (p : M)
    (hRm : HasCurvatureOperatorNormLeAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p K) :
    |scalarCurvatureAt g g.leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita g) p| ≤
      (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * K := by
  classical
  let hLC := canonicalLeviCivita_isLeviCivita g
  letI : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hscalareq :
      scalarCurvatureAt g g.leviCivitaConnection hLC p =
        ∑ i : Fin (Module.finrank ℝ (TangentSpace I p)),
          ricciTensorAt g p (e i) (e i) := by
    change Riemannian.scalarCurvature
        (isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p) =
        _
    rw [Riemannian.scalarCurvature_eq_sum_ricci _ e]
    congr 1
    funext i
    change ricciAt g g.leviCivitaConnection hLC p (e i) (e i) = _
    exact ricciAt_leviCivita_eq_ricciTensorAt g hLC p (e i) (e i)
  rw [hscalareq]
  calc
    |∑ i, ricciTensorAt g p (e i) (e i)| ≤
        ∑ i, |ricciTensorAt g p (e i) (e i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ (TangentSpace I p)),
        (Module.finrank ℝ E : ℝ) * K := by
      refine Finset.sum_le_sum fun i _hi => ?_
      have hri := abs_ricciTensorAt_le_finrank_mul_of_hasCurvatureOperatorNormLeAt
        g hK p hRm (e i)
      have hei : g.metricInner p (e i) (e i) = 1 := by
        change (inner ℝ (e i) (e i) : ℝ) = 1
        rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i]
        norm_num
      rw [hei] at hri
      simpa using hri
    _ = (Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * K := by
      have hcard : Fintype.card (Fin (Module.finrank ℝ E)) =
          Module.finrank ℝ (TangentSpace I p) := Fintype.card_fin _
      have hdimNat : Module.finrank ℝ (TangentSpace I p) =
          Module.finrank ℝ E := by
        simpa only [Fintype.card_fin] using hcard.symm
      have hdim : (Module.finrank ℝ (TangentSpace I p) : ℝ) =
          (Module.finrank ℝ E : ℝ) := by
        exact_mod_cast hdimNat
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [hdim]
      ring

/-- **Math.** A uniform pointwise scalar-curvature bound for an evolving
metric. -/
def HasAbsoluteScalarCurvatureBoundOnTime
    (g : ℝ → RiemannianMetric I M) (J : Set ℝ) (C : ℝ) : Prop :=
  ∀ t ∈ J, ∀ p : M,
    |scalarCurvatureAt (g t) (g t).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g t)) p| ≤ C

/-- **Math.** A curvature-operator bound gives a uniform scalar-curvature
bound on a time interval. -/
theorem hasAbsoluteScalarCurvatureBoundOnTime_of_hasCurvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hRm : HasCurvatureOperatorNormLeOnTime g J K) :
    HasAbsoluteScalarCurvatureBoundOnTime g J
      ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ) * K) := by
  intro t ht p
  exact abs_scalarCurvatureAt_le_finrank_sq_mul_of_hasCurvatureOperatorNormLeAt
    (g t) hK p (hRm t ht p)

/-- **Math.** Exponential comparison for a positive volume density under `rho' = -R rho`.

The estimate is the scalar analogue of the metric pairing comparison: the
factors are `exp (± C t)` because the volume equation has coefficient `-R`.
-/
theorem volumeDensity_exp_comparison
    {rho R : ℝ → ℝ} {T C t : ℝ}
    (hderiv : IsVolumeDensityEvolution rho R (Icc 0 T))
    (hbound : HasAbsoluteScalarBoundOn R (Icc 0 T) C)
    (hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < rho s)
    (ht : t ∈ Icc (0 : ℝ) T) :
    Real.exp (-C * t) * rho 0 ≤ rho t ∧
      rho t ≤ Real.exp (C * t) * rho 0 := by
  let upper : ℝ → ℝ := fun s => Real.exp (-C * s) * rho s
  let lower : ℝ → ℝ := fun s => Real.exp (C * s) * rho s
  have hcont : ContinuousOn rho (Icc (0 : ℝ) T) := by
    intro s hs
    exact (hderiv s hs).continuousWithinAt
  have hupperCont : ContinuousOn upper (Icc (0 : ℝ) T) := by
    have he : ContinuousOn (fun s : ℝ => Real.exp (-C * s)) (Icc 0 T) := by
      fun_prop
    exact he.mul hcont
  have hlowerCont : ContinuousOn lower (Icc (0 : ℝ) T) := by
    have he : ContinuousOn (fun s : ℝ => Real.exp (C * s)) (Icc 0 T) := by
      fun_prop
    exact he.mul hcont
  have hupperDeriv (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      HasDerivWithinAt upper
        (Real.exp (-C * s) * (-C * rho s - R s * rho s))
        (interior (Icc 0 T)) s := by
    have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have he : HasDerivAt (fun r : ℝ => Real.exp (-C * r))
        (-C * Real.exp (-C * s)) s := by
      convert (((hasDerivAt_id s).const_mul (-C)).exp) using 1 <;> simp [mul_comm]
    have hr : HasDerivAt rho (-R s * rho s) s :=
      (hderiv s hs').hasDerivAt (mem_interior_iff_mem_nhds.mp hs)
    exact ((he.mul hr).congr_deriv (by ring)).hasDerivWithinAt
  have hlowerDeriv (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      HasDerivWithinAt lower
        (Real.exp (C * s) * (C * rho s - R s * rho s))
        (interior (Icc 0 T)) s := by
    have hs' : s ∈ Icc (0 : ℝ) T := interior_subset hs
    have he : HasDerivAt (fun r : ℝ => Real.exp (C * r))
        (C * Real.exp (C * s)) s := by
      convert (((hasDerivAt_id s).const_mul C).exp) using 1 <;> simp [mul_comm]
    have hr : HasDerivAt rho (-R s * rho s) s :=
      (hderiv s hs').hasDerivAt (mem_interior_iff_mem_nhds.mp hs)
    exact ((he.mul hr).congr_deriv (by ring)).hasDerivWithinAt
  have hu (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      Real.exp (-C * s) * (-C * rho s - R s * rho s) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
    have hb := abs_le.mp (hbound s (interior_subset hs))
    have hp := (hpos s (interior_subset hs)).le
    nlinarith
  have hl (s : ℝ) (hs : s ∈ interior (Icc (0 : ℝ) T)) :
      0 ≤ Real.exp (C * s) * (C * rho s - R s * rho s) := by
    apply mul_nonneg (Real.exp_pos _).le
    have hb := abs_le.mp (hbound s (interior_subset hs))
    have hp := (hpos s (interior_subset hs)).le
    nlinarith
  have huanti : AntitoneOn upper (Icc (0 : ℝ) T) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T) hupperCont
      hupperDeriv hu
  have hlmono : MonotoneOn lower (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) hlowerCont
      hlowerDeriv hl
  have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have huc := huanti hz ht ht.1
  have hlc := hlmono hz ht ht.1
  dsimp [upper, lower] at huc hlc
  simp only [mul_zero, Real.exp_zero, one_mul] at huc hlc
  have hcancel₁ : Real.exp (C * t) * Real.exp (-C * t) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
  have hcancel₂ : Real.exp (-C * t) * Real.exp (C * t) = 1 := by
    rw [← Real.exp_add]; convert Real.exp_zero using 1 <;> ring
  constructor
  · calc
      Real.exp (-C * t) * rho 0 ≤
          Real.exp (-C * t) * (Real.exp (C * t) * rho t) :=
        mul_le_mul_of_nonneg_left hlc (Real.exp_pos _).le
      _ = rho t := by rw [← mul_assoc, hcancel₂, one_mul]
  · calc
      rho t = Real.exp (C * t) * (Real.exp (-C * t) * rho t) := by
        rw [← mul_assoc, hcancel₁, one_mul]
      _ ≤ Real.exp (C * t) * rho 0 :=
        mul_le_mul_of_nonneg_left huc (Real.exp_pos _).le

section ChartVolumeDensity

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace M] [BorelSpace M]

/-- **Math.** On a fixed coordinate chart, a curvature-operator bound along
Ricci flow gives exponential distortion of the Riemannian volume density.
The comparison is pointwise in the chart coordinate, with the coarse scalar
curvature constant `n² K`. -/
theorem chartVolumeDensity_exp_comparison_of_curvatureOperatorNormLeOnTime
    {g : ℝ → RiemannianMetric I M} {T K : ℝ}
    (hK : 0 ≤ K) (hflow : IsRicciFlowOn g (Icc 0 T))
    (hRm : HasCurvatureOperatorNormLeOnTime g (Icc 0 T) K)
    (alpha : M) {y : E} (hy : y ∈ (extChartAt I alpha).target)
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    Real.exp (-((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t) *
        chartVolumeDensity (I := I) (g 0) alpha y ≤
      chartVolumeDensity (I := I) (g t) alpha y ∧
    chartVolumeDensity (I := I) (g t) alpha y ≤
      Real.exp (((Module.finrank ℝ E : ℝ) *
          (Module.finrank ℝ E : ℝ) * K) * t) *
        chartVolumeDensity (I := I) (g 0) alpha y := by
  let p : M := (extChartAt I alpha).symm y
  let rho : ℝ → ℝ := fun s => chartVolumeDensity (I := I) (g s) alpha y
  let R : ℝ → ℝ := fun s =>
    scalarCurvatureAt (g s) (g s).leviCivitaConnection
      (canonicalLeviCivita_isLeviCivita (g s)) p
  let C : ℝ := (Module.finrank ℝ E : ℝ) *
    (Module.finrank ℝ E : ℝ) * K
  have hderiv : IsVolumeDensityEvolution rho R (Icc 0 T) := by
    intro s hs
    dsimp [rho, R, p]
    exact hasDerivWithinAt_chartVolumeDensity_of_isRicciFlowOn
      hflow alpha hs hy
  have hbound : HasAbsoluteScalarBoundOn R (Icc 0 T) C := by
    intro s hs
    exact abs_scalarCurvatureAt_le_finrank_sq_mul_of_hasCurvatureOperatorNormLeAt
      (g s) hK p (hRm s hs p)
  have hpos : ∀ s ∈ Icc (0 : ℝ) T, 0 < rho s := by
    intro s _hs
    exact chartVolumeDensity_pos (I := I) (g s) alpha hy
  simpa [rho, C] using volumeDensity_exp_comparison hderiv hbound hpos ht

end ChartVolumeDensity

/-- **Math.** The operator square in the curvature-operator evolution equation. -/
def curvatureOperatorSquare {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) : Matrix ι ι ℝ := T * T

theorem curvatureOperatorSquare_apply {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (a b : ι) :
    curvatureOperatorSquare T a b = ∑ c, T a c * T c b := by
  rfl

/-- **Math.** The operator square preserves matrix symmetry.  This is the finite-index
algebraic fact used when the curvature operator is represented in an
orthonormal wedge basis. -/
theorem curvatureOperatorSquare_isSymm_of_isSymm {ι : Type*} [Fintype ι]
    (T : Matrix ι ι ℝ) (hT : T.IsSymm) :
    (curvatureOperatorSquare T).IsSymm := by
  apply Matrix.IsSymm.ext
  intro a b
  rw [curvatureOperatorSquare_apply, curvatureOperatorSquare_apply]
  apply Finset.sum_congr rfl
  intro c hc
  have hbc : T b c = T c b := by
    simpa [Matrix.transpose_apply] using
      (congrFun (congrFun hT b) c).symm
  have hac : T c a = T a c := by
    simpa [Matrix.transpose_apply] using
      (congrFun (congrFun hT c) a).symm
  rw [hbc, hac]
  ring

/-- **Math.** The Lie-algebra square `T^sharp` from Morgan--Tian's operator equation. -/
def curvatureOperatorSharp {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun a b => ∑ γ, ∑ δ, ∑ ζ, ∑ η,
    c a γ ζ * c b δ η * T γ δ * T ζ η

theorem curvatureOperatorSharp_apply {ι : Type*} [Fintype ι]
    (c : ι → ι → ι → ℝ) (T : Matrix ι ι ℝ) (a b : ι) :
    curvatureOperatorSharp c T a b =
      ∑ γ, ∑ δ, ∑ ζ, ∑ η, c a γ ζ * c b δ η * T γ δ * T ζ η := by
  rfl

/-- **Math.** Componentwise form of the curvature-operator evolution equation. -/
def IsCurvatureOperatorEvolution {ι : Type*} [Fintype ι]
    (T lap : ℝ → Matrix ι ι ℝ) (c : ι → ι → ι → ℝ) : Prop :=
  ∀ t a b, deriv (fun s => T s a b) t =
    lap t a b + curvatureOperatorSquare (T t) a b + curvatureOperatorSharp c (T t) a b

theorem isCurvatureOperatorEvolution_iff {ι : Type*} [Fintype ι]
    (T lap : ℝ → Matrix ι ι ℝ) (c : ι → ι → ι → ℝ) :
    IsCurvatureOperatorEvolution T lap c ↔
      ∀ t a b, deriv (fun s => T s a b) t =
        lap t a b + curvatureOperatorSquare (T t) a b + curvatureOperatorSharp c (T t) a b :=
  Iff.rfl

end MorganTianLib

import PetersenLib.Ch02.ChristoffelSymbols

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.8 (derivatives of the inverse metric)

Exercise 2.5.8: the chart partial derivative of the inverse Gram matrix is
expressed through the metric and the Christoffel symbols,
`∂_k g^{ij} = − g^{iℓ}Γ^j_{kℓ} − g^{jℓ}Γ^i_{kℓ}`.

Proof: differentiate the inverse identity `Σ_m g^{im}g_{mc} = δ^i_c` (constant on
the open chart target, so its derivative vanishes) with the product rule, then
substitute `∂_k g_{mc}` via the metric-compatibility identity
`partialDeriv_chartGramOnE_eq` and contract against the inverse Gram matrix.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5.
-/

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section
namespace PetersenLib
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

open Tensor

omit [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** **Petersen Exercise 2.5.8.** Partial derivative of the inverse Gram
matrix in coordinates: `∂ₖ gⁱʲ = − Σₗ gⁱˡ Γʲₖₗ − Σₗ gʲˡ Γⁱₖₗ`. -/
theorem exercise2_5_8 (g : RiemannianMetric I M) (p : M)
    (i j k : Fin (Module.finrank ℝ E)) {y : E} (hy : y ∈ (extChartAt I p).target) :
    partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i j) y
      = - (∑ l, chartInvGramOnE (I := I) g p i l y * chartChristoffel (I := I) g p k l j y)
        - (∑ l, chartInvGramOnE (I := I) g p j l y * chartChristoffel (I := I) g p k l i y) := by
  classical
  have hsource : (extChartAt I p).symm y ∈ (extChartAt I p).source := (extChartAt I p).map_target hy
  rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
  have hyb : (extChartAt I p).symm y ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]; exact hsource
  have htarget_mem : (extChartAt I p).target ∈ 𝓝 y := (isOpen_extChartAt_target p).mem_nhds hy
  have hGGinv : ∀ a : Fin (Module.finrank ℝ E),
      ∑ c, chartGramOnE (I := I) g p a c y * chartInvGramOnE (I := I) g p c j y
        = if a = j then (1:ℝ) else 0 := by
    intro a
    have h : ∑ c, chartGramOnE (I := I) g p a c y * chartInvGramOnE (I := I) g p c j y
        = (chartGramMatrix (I := I) g p ((extChartAt I p).symm y)
            * chartInvGramMatrix (I := I) g p ((extChartAt I p).symm y)) a j := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun c _ => by rw [chartGramOnE_def, chartInvGramOnE_def]
    rw [h, chartGramMatrix_mul_chartInvGramMatrix (I := I) g p hyb, Matrix.one_apply]
  have hGinvG : ∀ a : Fin (Module.finrank ℝ E),
      ∑ m, chartInvGramOnE (I := I) g p i m y * chartGramOnE (I := I) g p m a y
        = if i = a then (1:ℝ) else 0 := by
    intro a
    have h : ∑ m, chartInvGramOnE (I := I) g p i m y * chartGramOnE (I := I) g p m a y
        = (chartInvGramMatrix (I := I) g p ((extChartAt I p).symm y)
            * chartGramMatrix (I := I) g p ((extChartAt I p).symm y)) i a := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [chartInvGramOnE_def, chartGramOnE_def]
    rw [h, chartInvGramMatrix_mul_chartGramMatrix (I := I) g p hyb, Matrix.one_apply]
  have hsymInv : ∀ a b : Fin (Module.finrank ℝ E),
      chartInvGramOnE (I := I) g p a b y = chartInvGramOnE (I := I) g p b a y := by
    intro a b
    rw [chartInvGramOnE_def, chartInvGramOnE_def]
    simp only [chartInvGramMatrix]
    have hHerm := (chartGramMatrix_isHermitian (I := I) g p ((extChartAt I p).symm y)).inv
    simpa using (hHerm.apply a b).symm
  have starC : ∀ c : Fin (Module.finrank ℝ E),
      ∑ m, (chartInvGramOnE (I := I) g p i m y * partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y
          + chartGramOnE (I := I) g p m c y * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y) = 0 := by
    intro c
    have hInv_diff : ∀ m, DifferentiableAt ℝ (chartInvGramOnE (I := I) g p i m) y := fun m =>
      ((chartInvGramOnE_contDiffOn (I := I) g p i m).contDiffAt htarget_mem).differentiableAt (by simp)
    have hGram_diff : ∀ m, DifferentiableAt ℝ (chartGramOnE (I := I) g p m c) y := fun m =>
      ((chartGramOnE_contDiffOn (I := I) g p m c).contDiffAt htarget_mem).differentiableAt (by simp)
    have hprod : ∀ m, HasFDerivAt
        (fun z => chartInvGramOnE (I := I) g p i m z * chartGramOnE (I := I) g p m c z)
        ((chartInvGramOnE (I := I) g p i m y) • (fderiv ℝ (chartGramOnE (I := I) g p m c) y)
          + (chartGramOnE (I := I) g p m c y) • (fderiv ℝ (chartInvGramOnE (I := I) g p i m) y)) y :=
      fun m => (hInv_diff m).hasFDerivAt.mul (hGram_diff m).hasFDerivAt
    have hsum : HasFDerivAt
        (fun z => ∑ m, chartInvGramOnE (I := I) g p i m z * chartGramOnE (I := I) g p m c z)
        (∑ m, ((chartInvGramOnE (I := I) g p i m y) • (fderiv ℝ (chartGramOnE (I := I) g p m c) y)
          + (chartGramOnE (I := I) g p m c y) • (fderiv ℝ (chartInvGramOnE (I := I) g p i m) y))) y :=
      HasFDerivAt.fun_sum (fun m _ => hprod m)
    set c0 : ℝ := (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) i c with hc0
    have hconst : (fun z => ∑ m, chartInvGramOnE (I := I) g p i m z * chartGramOnE (I := I) g p m c z)
        =ᶠ[𝓝 y] (fun _ => c0) := by
      filter_upwards [htarget_mem] with z hz
      have hsource' : (extChartAt I p).symm z ∈ (extChartAt I p).source := (extChartAt I p).map_target hz
      rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource'
      have hzb : (extChartAt I p).symm z ∈ (trivializationAt E (TangentSpace I) p).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]; exact hsource'
      have hmm : ∑ m, chartInvGramOnE (I := I) g p i m z * chartGramOnE (I := I) g p m c z
          = (chartInvGramMatrix (I := I) g p ((extChartAt I p).symm z)
              * chartGramMatrix (I := I) g p ((extChartAt I p).symm z)) i c := by
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun m _ => by rw [chartInvGramOnE_def, chartGramOnE_def]
      rw [hmm, chartInvGramMatrix_mul_chartGramMatrix (I := I) g p hzb]
    have hφ0 : HasFDerivAt
        (fun z => ∑ m, chartInvGramOnE (I := I) g p i m z * chartGramOnE (I := I) g p m c z) 0 y :=
      (hasFDerivAt_const (𝕜 := ℝ) c0 y).congr_of_eventuallyEq hconst
    have happ := DFunLike.congr_fun (hsum.unique hφ0) (Module.finBasis ℝ E k)
    rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at happ
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at happ
    simp only [partialDeriv]
    exact happ
  have hpar : ∀ m c : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y
        = ∑ a, (chartGramOnE (I := I) g p a c y * chartChristoffel (I := I) g p k m a y
              + chartGramOnE (I := I) g p m a y * chartChristoffel (I := I) g p k c a y) := fun m c =>
    partialDeriv_chartGramOnE_eq (I := I) g p m c k y hyb
  have h0 : ∑ c, chartInvGramOnE (I := I) g p c j y
      * (∑ m, (chartInvGramOnE (I := I) g p i m y * partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y
          + chartGramOnE (I := I) g p m c y * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y)) = 0 :=
    Finset.sum_eq_zero fun c _ => by rw [starC c, mul_zero]
  have hSsplit : ∑ c, chartInvGramOnE (I := I) g p c j y
      * (∑ m, (chartInvGramOnE (I := I) g p i m y * partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y
          + chartGramOnE (I := I) g p m c y * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y))
      = (∑ c, ∑ m, chartInvGramOnE (I := I) g p c j y
            * (chartInvGramOnE (I := I) g p i m y * partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y))
        + (∑ c, ∑ m, chartInvGramOnE (I := I) g p c j y
            * (chartGramOnE (I := I) g p m c y * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun m _ => by ring
  have hS2 : (∑ c, ∑ m, chartInvGramOnE (I := I) g p c j y
        * (chartGramOnE (I := I) g p m c y * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y))
      = partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i j) y := by
    rw [Finset.sum_comm]
    have hstep : ∀ m, ∑ c, chartInvGramOnE (I := I) g p c j y
          * (chartGramOnE (I := I) g p m c y * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y)
        = (if m = j then (1:ℝ) else 0) * partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i m) y := by
      intro m
      rw [← hGGinv m, Finset.sum_mul]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun m _ => hstep m]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have key : partialDeriv (E := E) k (chartInvGramOnE (I := I) g p i j) y
      = - (∑ c, ∑ m, chartInvGramOnE (I := I) g p c j y
            * (chartInvGramOnE (I := I) g p i m y * partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y)) := by
    have hh := h0
    rw [hSsplit, hS2] at hh
    linarith
  have hexpand : (∑ c, ∑ m, chartInvGramOnE (I := I) g p c j y
        * (chartInvGramOnE (I := I) g p i m y * partialDeriv (E := E) k (chartGramOnE (I := I) g p m c) y))
      = (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g p c j y * chartInvGramOnE (I := I) g p i m y
            * chartGramOnE (I := I) g p a c y * chartChristoffel (I := I) g p k m a y)
        + (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g p c j y * chartInvGramOnE (I := I) g p i m y
            * chartGramOnE (I := I) g p m a y * chartChristoffel (I := I) g p k c a y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hpar m c, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hPA : (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g p c j y * chartInvGramOnE (I := I) g p i m y
        * chartGramOnE (I := I) g p a c y * chartChristoffel (I := I) g p k m a y)
      = ∑ m, chartInvGramOnE (I := I) g p i m y * chartChristoffel (I := I) g p k m j y := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_comm]
    have hstep : ∀ a, ∑ c, chartInvGramOnE (I := I) g p c j y * chartInvGramOnE (I := I) g p i m y
          * chartGramOnE (I := I) g p a c y * chartChristoffel (I := I) g p k m a y
        = (chartInvGramOnE (I := I) g p i m y * chartChristoffel (I := I) g p k m a y)
          * (∑ c, chartGramOnE (I := I) g p a c y * chartInvGramOnE (I := I) g p c j y) := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl fun a _ => hstep a]
    simp_rw [hGGinv]
    simp [Finset.sum_ite_eq']
  have hPB : (∑ c, ∑ m, ∑ a, chartInvGramOnE (I := I) g p c j y * chartInvGramOnE (I := I) g p i m y
        * chartGramOnE (I := I) g p m a y * chartChristoffel (I := I) g p k c a y)
      = ∑ c, chartInvGramOnE (I := I) g p j c y * chartChristoffel (I := I) g p k c i y := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    have hstep : ∀ a, ∑ m, chartInvGramOnE (I := I) g p c j y * chartInvGramOnE (I := I) g p i m y
          * chartGramOnE (I := I) g p m a y * chartChristoffel (I := I) g p k c a y
        = (chartInvGramOnE (I := I) g p c j y * chartChristoffel (I := I) g p k c a y)
          * (∑ m, chartInvGramOnE (I := I) g p i m y * chartGramOnE (I := I) g p m a y) := by
      intro a
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [Finset.sum_congr rfl fun a _ => hstep a]
    simp_rw [hGinvG]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [hsymInv c j]
  rw [key, hexpand, hPA, hPB]
  ring

end PetersenLib
end

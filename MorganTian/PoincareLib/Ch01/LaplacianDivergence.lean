import PoincareLib.Ch02.LaplacianCoord
import PoincareLib.Ch01.MatrixCalculus

/-!
# Morgan–Tian Ch. 1 — the Laplacian in divergence form

Blueprint `lem:laplacian-local-formula`: in a coordinate chart at `α`, the
Laplacian of a smooth function is the **divergence form**
`Δ = (det g)^{-1/2} ∂_a (g^{ab} (det g)^{1/2} ∂_b)`.

This upgrades the Christoffel form `Δf = g^{ab}(∂_a∂_bF − Γ^k_{ab}∂_kF)`
(`laplacianAt_eq_chart_formula`, already formalized) to the divergence form, by
carrying out the product-rule expansion flagged as "not yet formalized" in
`LaplacianCoord.lean`.  The analytic inputs are Jacobi's formula for the
determinant (`detCMM_linearDeriv_eq_smul_trace`) and metric compatibility in
chart components (`partialDeriv_chartGramOnE_eq`).
-/

open Matrix Riemannian Riemannian.Tensor
open scoped ContDiff Manifold Topology Bundle Matrix

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** The chart Gram matrix pulled back to `E` as a function of the
chart point `y`; its `(i,j)` entry is `chartGramOnE g α i j y`, so it is
defeq to `chartGramMatrix g α ((extChartAt I α).symm y)`. -/
private def gramFun (g : RiemannianMetric I M) (α : M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun y i j => chartGramOnE (I := I) g α i j y

private lemma gramFun_apply (g : RiemannianMetric I M) (α : M)
    (y : E) (i j : Fin (Module.finrank ℝ E)) :
    gramFun (I := I) g α y i j = chartGramOnE (I := I) g α i j y := rfl

/-! ### Arithmetic of the coordinate partial derivative -/

private lemma partialDeriv_add {a : Fin (Module.finrank ℝ E)} {u v : E → ℝ} {y : E}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    Riemannian.partialDeriv (E := E) a (fun z => u z + v z) y
      = Riemannian.partialDeriv a u y + Riemannian.partialDeriv a v y := by
  unfold Riemannian.partialDeriv
  rw [fderiv_fun_add hu hv, ContinuousLinearMap.add_apply]

private lemma partialDeriv_mul {a : Fin (Module.finrank ℝ E)} {u v : E → ℝ} {y : E}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) :
    Riemannian.partialDeriv (E := E) a (fun z => u z * v z) y
      = Riemannian.partialDeriv a u y * v y + u y * Riemannian.partialDeriv a v y := by
  unfold Riemannian.partialDeriv
  rw [fderiv_fun_mul hu hv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

private lemma partialDeriv_fun_sum {a : Fin (Module.finrank ℝ E)}
    {ι : Type*} (s : Finset ι) (u : ι → E → ℝ) {y : E}
    (hu : ∀ i ∈ s, DifferentiableAt ℝ (u i) y) :
    Riemannian.partialDeriv (E := E) a (fun z => ∑ i ∈ s, u i z) y
      = ∑ i ∈ s, Riemannian.partialDeriv a (u i) y := by
  unfold Riemannian.partialDeriv
  rw [fderiv_fun_sum hu, ContinuousLinearMap.sum_apply]

private lemma partialDeriv_mul3 {a : Fin (Module.finrank ℝ E)} {u v w : E → ℝ} {y : E}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) (hw : DifferentiableAt ℝ w y) :
    Riemannian.partialDeriv (E := E) a (fun z => u z * v z * w z) y
      = Riemannian.partialDeriv a u y * v y * w y
        + u y * Riemannian.partialDeriv a v y * w y
        + u y * v y * Riemannian.partialDeriv a w y := by
  rw [partialDeriv_mul (show DifferentiableAt ℝ (fun z => u z * v z) y from hu.mul hv) hw,
    partialDeriv_mul hu hv]
  ring

/-! ### The derivative of the coordinate determinant (Jacobi's formula on `E`) -/

private lemma differentiableAt_chartGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) x :=
  ((chartGramOnE_contDiffOn (I := I) g α i j).differentiableOn (by norm_num)).differentiableAt
    ((isOpen_extChartAt_target (I := I) α).mem_nhds hx)

/-- **Math.** The chart determinant `det(G(y))` is differentiable, and its
coordinate partial derivative is **Jacobi's formula**:
`∂_a det(G) = det(G) · Σ_{ij} G^{ij} ∂_a G_{ji}`. -/
private lemma partialDeriv_det_gramFun (g : RiemannianMetric I M) (α : M)
    (a : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    Riemannian.partialDeriv (E := E) a
        (fun y => (gramFun (I := I) g α y).det) x
      = (gramFun (I := I) g α x).det
        * ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
            * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α j i) x := by
  classical
  -- each entry is differentiable at `x`
  have hEntry : ∀ i j, HasFDerivAt (fun y => chartGramOnE (I := I) g α i j y)
      (fderiv ℝ (chartGramOnE (I := I) g α i j) x) x :=
    fun i j => (differentiableAt_chartGramOnE (I := I) g α i j hx).hasFDerivAt
  -- assemble the matrix-valued derivative of `gramFun`
  have hMat : HasFDerivAt (gramFun (I := I) g α)
      (ContinuousLinearMap.pi fun i =>
        ContinuousLinearMap.pi fun j => fderiv ℝ (chartGramOnE (I := I) g α i j) x) x :=
    hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j => hEntry i j
  -- chain with the determinant
  have hbase : (extChartAt I α).symm x ∈
      (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source_eq_chartAt_source (I := I)]
    exact (extChartAt I α).map_target hx
  have hdet : IsUnit (gramFun (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (chartGramMatrix_det_pos (I := I) g α hbase))
  have hcomp : HasFDerivAt (fun y => (gramFun (I := I) g α y).det)
      ((detCMM.linearDeriv (gramFun (I := I) g α x)).comp
        (ContinuousLinearMap.pi fun i =>
          ContinuousLinearMap.pi fun j => fderiv ℝ (chartGramOnE (I := I) g α i j) x)) x :=
    (hasFDerivAt_det (gramFun (I := I) g α x)).comp x hMat
  have hpd : Riemannian.partialDeriv (E := E) a
      (fun y => (gramFun (I := I) g α y).det) x
      = detCMM.linearDeriv (gramFun (I := I) g α x)
          (fun i j => Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α i j) x) := by
    unfold Riemannian.partialDeriv
    rw [hcomp.fderiv, ContinuousLinearMap.comp_apply]
    rfl
  -- `(G⁻¹ · ∂G).trace = Σ_i Σ_j G^{ij} ∂_a G_{ji}` holds definitionally
  rw [hpd, detCMM_linearDeriv_eq_smul_trace _ _ hdet, smul_eq_mul]
  congr 1

/-! ### The contracted Christoffel identity -/

private lemma symm_mem_baseSet (g : RiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ (extChartAt I α).target) :
    (extChartAt I α).symm x ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  rw [trivializationAt_baseSet_eq_chartAt_source, ← extChartAt_source_eq_chartAt_source (I := I)]
  exact (extChartAt I α).map_target hx

/-- `Σ_k G_{ik} G^{kj} = δ_{ij}` — the Gram/inverse-Gram contraction on `E`. -/
private lemma sum_gram_invGram (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    ∑ k, chartGramOnE (I := I) g α i k x * chartInvGramOnE (I := I) g α k j x
      = if i = j then (1 : ℝ) else 0 := by
  have h : ∑ k, chartGramOnE (I := I) g α i k x * chartInvGramOnE (I := I) g α k j x
      = (chartGramMatrix (I := I) g α ((extChartAt I α).symm x) *
          chartInvGramMatrix (I := I) g α ((extChartAt I α).symm x)) i j := by
    rw [Matrix.mul_apply]; rfl
  rw [h, chartGramMatrix_mul_chartInvGramMatrix (I := I) g α (symm_mem_baseSet g α hx),
    Matrix.one_apply]

/-- `Σ_k G^{ik} G_{kj} = δ_{ij}` — the inverse-Gram/Gram contraction on `E`. -/
private lemma sum_invGram_gram (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    ∑ k, chartInvGramOnE (I := I) g α i k x * chartGramOnE (I := I) g α k j x
      = if i = j then (1 : ℝ) else 0 := by
  have h : ∑ k, chartInvGramOnE (I := I) g α i k x * chartGramOnE (I := I) g α k j x
      = (chartInvGramMatrix (I := I) g α ((extChartAt I α).symm x) *
          chartGramMatrix (I := I) g α ((extChartAt I α).symm x)) i j := by
    rw [Matrix.mul_apply]; rfl
  rw [h, chartInvGramMatrix_mul_chartGramMatrix (I := I) g α (symm_mem_baseSet g α hx),
    Matrix.one_apply]

/-- **Math.** **The contracted Christoffel identity**: `Σ_{ij} G^{ij} ∂_a G_{ji}
= 2 Σ_m Γ^m_{am}`, obtained by contracting metric compatibility
(`partialDeriv_chartGramOnE_eq`) against the inverse Gram matrix. -/
private lemma sum_invGram_partialDeriv_gram (g : RiemannianMetric I M) (α : M)
    (a : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
        * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α j i) x
      = 2 * ∑ m, chartChristoffel (I := I) g α a m m x := by
  classical
  have hbase := symm_mem_baseSet g α hx
  -- expand each metric derivative via metric compatibility
  have hstep : ∀ i j,
      Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α j i) x
        = ∑ m, (chartGramOnE (I := I) g α m i x * chartChristoffel (I := I) g α a j m x
            + chartGramOnE (I := I) g α j m x * chartChristoffel (I := I) g α a i m x) :=
    fun i j => partialDeriv_chartGramOnE_eq (I := I) g α j i a x hbase
  -- the two contracted pieces, each equal to `Σ_m Γ^m_{am}`
  have hA : ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
        * ∑ m, chartGramOnE (I := I) g α m i x * chartChristoffel (I := I) g α a j m x
      = ∑ m, chartChristoffel (I := I) g α a m m x := by
    calc ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
            * ∑ m, chartGramOnE (I := I) g α m i x * chartChristoffel (I := I) g α a j m x
        = ∑ i, ∑ j, ∑ m, chartInvGramOnE (I := I) g α i j x
            * (chartGramOnE (I := I) g α m i x * chartChristoffel (I := I) g α a j m x) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ j, ∑ m, ∑ i, chartInvGramOnE (I := I) g α i j x
            * (chartGramOnE (I := I) g α m i x * chartChristoffel (I := I) g α a j m x) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j, ∑ m, (∑ i, chartInvGramOnE (I := I) g α i j x
            * chartGramOnE (I := I) g α m i x) * chartChristoffel (I := I) g α a j m x := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ j, ∑ m, (if m = j then (1 : ℝ) else 0) * chartChristoffel (I := I) g α a j m x := by
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
          congr 1
          rw [show (∑ i, chartInvGramOnE (I := I) g α i j x * chartGramOnE (I := I) g α m i x)
                = ∑ i, chartGramOnE (I := I) g α m i x * chartInvGramOnE (I := I) g α i j x from
              Finset.sum_congr rfl fun i _ => mul_comm _ _]
          exact sum_gram_invGram (I := I) g α m j hx
      _ = ∑ m, chartChristoffel (I := I) g α a m m x := by
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  have hB : ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
        * ∑ m, chartGramOnE (I := I) g α j m x * chartChristoffel (I := I) g α a i m x
      = ∑ m, chartChristoffel (I := I) g α a m m x := by
    calc ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
            * ∑ m, chartGramOnE (I := I) g α j m x * chartChristoffel (I := I) g α a i m x
        = ∑ i, ∑ j, ∑ m, chartInvGramOnE (I := I) g α i j x
            * (chartGramOnE (I := I) g α j m x * chartChristoffel (I := I) g α a i m x) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ i, ∑ m, ∑ j, chartInvGramOnE (I := I) g α i j x
            * (chartGramOnE (I := I) g α j m x * chartChristoffel (I := I) g α a i m x) := by
          exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i, ∑ m, (∑ j, chartInvGramOnE (I := I) g α i j x
            * chartGramOnE (I := I) g α j m x) * chartChristoffel (I := I) g α a i m x := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ i, ∑ m, (if i = m then (1 : ℝ) else 0) * chartChristoffel (I := I) g α a i m x := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => ?_
          congr 1
          exact sum_invGram_gram (I := I) g α i m hx
      _ = ∑ m, chartChristoffel (I := I) g α a m m x := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  calc ∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α j i) x
      = (∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
            * ∑ m, chartGramOnE (I := I) g α m i x * chartChristoffel (I := I) g α a j m x)
        + (∑ i, ∑ j, chartInvGramOnE (I := I) g α i j x
            * ∑ m, chartGramOnE (I := I) g α j m x * chartChristoffel (I := I) g α a i m x) := by
        simp only [hstep]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_add_distrib, mul_add]
    _ = 2 * ∑ m, chartChristoffel (I := I) g α a m m x := by rw [hA, hB, two_mul]

/-! ### The derivative of the inverse Gram matrix -/

private lemma differentiableAt_chartInvGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ (chartInvGramOnE (I := I) g α i j) x :=
  ((chartInvGramOnE_contDiffOn (I := I) g α i j).differentiableOn (by norm_num)).differentiableAt
    ((isOpen_extChartAt_target (I := I) α).mem_nhds hx)

/-- **Math.** **The derivative of the inverse Gram matrix**:
`∂_a G^{cb} = − Σ_{p,q} G^{cp} (∂_a G_{pq}) G^{qb}`, from differentiating the
identity `Σ_p G^{cp} G_{pb} = δ_{cb}` (which is constant near `x`). -/
private lemma partialDeriv_chartInvGramOnE (g : RiemannianMetric I M) (α : M)
    (a c b : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c b) x
      = - ∑ p, ∑ q, chartInvGramOnE (I := I) g α c p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) x
          * chartInvGramOnE (I := I) g α q b x := by
  classical
  -- `Σ_p G^{c p} G_{p d}` is locally constant (= δ_{cd}), so its derivative vanishes
  have hrel : ∀ d, ∑ p, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c p) x
        * chartGramOnE (I := I) g α p d x
      = - ∑ p, chartInvGramOnE (I := I) g α c p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p d) x := by
    intro d
    have hdiff : ∀ p ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))),
        DifferentiableAt ℝ
          (fun y => chartInvGramOnE (I := I) g α c p y * chartGramOnE (I := I) g α p d y) x :=
      fun p _ => (differentiableAt_chartInvGramOnE (I := I) g α c p hx).mul
        (differentiableAt_chartGramOnE (I := I) g α p d hx)
    have hconst : (fun y => ∑ p, chartInvGramOnE (I := I) g α c p y
          * chartGramOnE (I := I) g α p d y)
        =ᶠ[nhds x] (fun _ => if c = d then (1 : ℝ) else 0) :=
      Filter.eventuallyEq_of_mem
        ((isOpen_extChartAt_target (I := I) α).mem_nhds hx)
        (fun y hy => sum_invGram_gram (I := I) g α c d hy)
    have h0 : Riemannian.partialDeriv (E := E) a
        (fun y => ∑ p, chartInvGramOnE (I := I) g α c p y
          * chartGramOnE (I := I) g α p d y) x = 0 := by
      unfold Riemannian.partialDeriv
      rw [hconst.fderiv_eq]; simp
    rw [partialDeriv_fun_sum Finset.univ
      (fun p y => chartInvGramOnE (I := I) g α c p y * chartGramOnE (I := I) g α p d y) hdiff] at h0
    have h0' : ∑ p, (Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c p) x
          * chartGramOnE (I := I) g α p d x
        + chartInvGramOnE (I := I) g α c p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p d) x) = 0 := by
      rw [← h0]
      exact Finset.sum_congr rfl fun p _ =>
        (partialDeriv_mul (differentiableAt_chartInvGramOnE (I := I) g α c p hx)
          (differentiableAt_chartGramOnE (I := I) g α p d hx)).symm
    rw [Finset.sum_add_distrib] at h0'
    linarith [h0']
  -- extract `∂_a G^{cb}` by multiplying `hrel` with `G^{db}` and summing
  calc Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c b) x
      = ∑ p, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c p) x
          * (if p = b then (1 : ℝ) else 0) := by
        simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = ∑ p, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c p) x
          * ∑ d, chartGramOnE (I := I) g α p d x * chartInvGramOnE (I := I) g α d b x := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← sum_gram_invGram (I := I) g α p b hx]
    _ = ∑ p, ∑ d, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c p) x
          * chartGramOnE (I := I) g α p d x * chartInvGramOnE (I := I) g α d b x := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => by ring
    _ = ∑ d, (∑ p, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α c p) x
          * chartGramOnE (I := I) g α p d x) * chartInvGramOnE (I := I) g α d b x := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ d, (- ∑ p, chartInvGramOnE (I := I) g α c p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p d) x)
          * chartInvGramOnE (I := I) g α d b x := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hrel d]
    _ = - ∑ p, ∑ q, chartInvGramOnE (I := I) g α c p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) x
          * chartInvGramOnE (I := I) g α q b x := by
        rw [Finset.sum_congr rfl fun d (_ : d ∈ Finset.univ) => by
          rw [neg_mul, Finset.sum_mul], Finset.sum_neg_distrib, Finset.sum_comm]

/-! ### The derivative of the chart volume density `√det g` -/

/-- **Math.** The chart volume density `√det(G(y))` as a function on `E`. -/
private def chartSqrtDetGramOnE (g : RiemannianMetric I M) (α : M) : E → ℝ :=
  fun y => Real.sqrt (gramFun (I := I) g α y).det

private lemma chartSqrtDetGramOnE_pos (g : RiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ (extChartAt I α).target) : 0 < chartSqrtDetGramOnE (I := I) g α x :=
  Real.sqrt_pos.mpr (chartGramMatrix_det_pos (I := I) g α (symm_mem_baseSet g α hx))

/-- **Math.** **The derivative of the volume density**: `∂_a √det(G) =
√det(G) · Σ_m Γ^m_{am}`, from Jacobi's formula (`partialDeriv_det_gramFun`),
the contracted Christoffel identity (`sum_invGram_partialDeriv_gram`) and the
chain rule for the square root. -/
private lemma partialDeriv_chartSqrtDetGramOnE (g : RiemannianMetric I M) (α : M)
    (a : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    Riemannian.partialDeriv (E := E) a (chartSqrtDetGramOnE (I := I) g α) x
      = chartSqrtDetGramOnE (I := I) g α x * ∑ m, chartChristoffel (I := I) g α a m m x := by
  have hDpos : 0 < (gramFun (I := I) g α x).det :=
    chartGramMatrix_det_pos (I := I) g α (symm_mem_baseSet g α hx)
  have hgramDiff : DifferentiableAt ℝ (gramFun (I := I) g α) x :=
    (hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j =>
      (differentiableAt_chartGramOnE (I := I) g α i j hx).hasFDerivAt).differentiableAt
  have hDdiff : DifferentiableAt ℝ (fun y => (gramFun (I := I) g α y).det) x :=
    ((hasFDerivAt_det (gramFun (I := I) g α x)).comp x hgramDiff.hasFDerivAt).differentiableAt
  have hchain : HasFDerivAt (fun y => Real.sqrt (gramFun (I := I) g α y).det)
      ((1 / (2 * Real.sqrt (gramFun (I := I) g α x).det))
        • fderiv ℝ (fun y => (gramFun (I := I) g α y).det) x) x :=
    (Real.hasDerivAt_sqrt (ne_of_gt hDpos)).comp_hasFDerivAt x hDdiff.hasFDerivAt
  have hpd : Riemannian.partialDeriv (E := E) a (chartSqrtDetGramOnE (I := I) g α) x
      = (1 / (2 * Real.sqrt (gramFun (I := I) g α x).det))
        * Riemannian.partialDeriv (E := E) a (fun y => (gramFun (I := I) g α y).det) x := by
    unfold Riemannian.partialDeriv chartSqrtDetGramOnE
    rw [hchain.fderiv, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have arith : ∀ D S s : ℝ, s ≠ 0 → s * s = D → 1 / (2 * s) * (D * (2 * S)) = s * S := by
    intro D S s hs hsD
    rw [← hsD]; field_simp
  rw [hpd, partialDeriv_det_gramFun (I := I) g α a hx,
    sum_invGram_partialDeriv_gram (I := I) g α a hx]
  unfold chartSqrtDetGramOnE
  exact arith _ _ _ (ne_of_gt (Real.sqrt_pos.mpr hDpos)) (Real.mul_self_sqrt hDpos.le)

/-! ### The divergence identity for the weighted inverse metric -/

/-- **Math.** **The divergence identity** `Σ_a ∂_a G^{ab} + Σ_a G^{ab} Σ_m Γ^m_{am}
= − Σ_{cd} G^{cd} Γ^b_{cd}`, combining the inverse-Gram derivative
(`partialDeriv_chartInvGramOnE`) with metric compatibility. This is the
coefficient identity making the divergence form of the Laplacian agree with the
Christoffel form. -/
private lemma div_invGram_identity (g : RiemannianMetric I M) (α : M)
    (b : Fin (Module.finrank ℝ E)) {x : E} (hx : x ∈ (extChartAt I α).target) :
    ∑ a, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
      + ∑ a, chartInvGramOnE (I := I) g α a b x
          * ∑ m, chartChristoffel (I := I) g α a m m x
      = - ∑ c, ∑ d, chartInvGramOnE (I := I) g α c d x
          * chartChristoffel (I := I) g α c d b x := by
  classical
  have hbase := symm_mem_baseSet g α hx
  -- `Σ_a ∂_a G^{ab} = − Σ_a Σ_p Σ_q G^{ap} (∂_a G_{pq}) G^{qb}`
  have hCsum : ∑ a, Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
      = - ∑ a, ∑ p, ∑ q, chartInvGramOnE (I := I) g α a p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) x
          * chartInvGramOnE (I := I) g α q b x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => partialDeriv_chartInvGramOnE (I := I) g α a a b hx
  -- expand `∂_a G_{pq}` by metric compatibility, then contract the two pieces
  have hexpand : ∑ a, ∑ p, ∑ q, chartInvGramOnE (I := I) g α a p x
        * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) x
        * chartInvGramOnE (I := I) g α q b x
      = (∑ c, ∑ d, chartInvGramOnE (I := I) g α c d x
            * chartChristoffel (I := I) g α c d b x)
        + ∑ a, chartInvGramOnE (I := I) g α a b x
            * ∑ m, chartChristoffel (I := I) g α a m m x := by
    -- rewrite the inner metric derivative and split into the two contracted pieces
    have hpw : ∀ a p q, chartInvGramOnE (I := I) g α a p x
          * Riemannian.partialDeriv (E := E) a (chartGramOnE (I := I) g α p q) x
          * chartInvGramOnE (I := I) g α q b x
        = (∑ m, chartInvGramOnE (I := I) g α a p x * chartChristoffel (I := I) g α a p m x
              * (chartGramOnE (I := I) g α m q x * chartInvGramOnE (I := I) g α q b x))
          + (∑ m, chartInvGramOnE (I := I) g α a p x * chartChristoffel (I := I) g α a q m x
              * (chartGramOnE (I := I) g α p m x * chartInvGramOnE (I := I) g α q b x)) := by
      intro a p q
      rw [partialDeriv_chartGramOnE_eq (I := I) g α p q a x hbase, Finset.mul_sum,
        Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => by ring
    simp only [hpw, Finset.sum_add_distrib]
    congr 1
    · -- Term I: `Σ_a Σ_p Σ_q Σ_m G^{ap} Γ^m_{ap} G_{mq} G^{qb} = Σ_{cd} G^{cd} Γ^b_{cd}`
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
      calc ∑ q, ∑ m, chartInvGramOnE (I := I) g α a p x * chartChristoffel (I := I) g α a p m x
              * (chartGramOnE (I := I) g α m q x * chartInvGramOnE (I := I) g α q b x)
          = ∑ m, chartInvGramOnE (I := I) g α a p x * chartChristoffel (I := I) g α a p m x
              * ∑ q, chartGramOnE (I := I) g α m q x * chartInvGramOnE (I := I) g α q b x := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun m _ => by rw [Finset.mul_sum]
        _ = ∑ m, chartInvGramOnE (I := I) g α a p x * chartChristoffel (I := I) g α a p m x
              * (if m = b then (1 : ℝ) else 0) := by
            exact Finset.sum_congr rfl fun m _ => by rw [sum_gram_invGram (I := I) g α m b hx]
        _ = chartInvGramOnE (I := I) g α a p x * chartChristoffel (I := I) g α a p b x := by
            simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    · -- Term II: `Σ_a Σ_p Σ_q Σ_m G^{ap} Γ^m_{aq} G_{pm} G^{qb} = Σ_a G^{ab} Σ_m Γ^m_{am}`
      calc ∑ a, ∑ p, ∑ q, ∑ m, chartInvGramOnE (I := I) g α a p x
              * chartChristoffel (I := I) g α a q m x
              * (chartGramOnE (I := I) g α p m x * chartInvGramOnE (I := I) g α q b x)
          = ∑ a, ∑ q, ∑ m, (∑ p, chartInvGramOnE (I := I) g α a p x
              * chartGramOnE (I := I) g α p m x)
              * (chartChristoffel (I := I) g α a q m x * chartInvGramOnE (I := I) g α q b x) := by
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun p _ => by ring
        _ = ∑ a, ∑ q, ∑ m, (if a = m then (1 : ℝ) else 0)
              * (chartChristoffel (I := I) g α a q m x * chartInvGramOnE (I := I) g α q b x) := by
            exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun q _ =>
              Finset.sum_congr rfl fun m _ => by rw [sum_invGram_gram (I := I) g α a m hx]
        _ = ∑ a, ∑ q, chartChristoffel (I := I) g α a q a x * chartInvGramOnE (I := I) g α q b x := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun q _ => ?_
            simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        _ = ∑ a, chartInvGramOnE (I := I) g α a b x
              * ∑ m, chartChristoffel (I := I) g α a m m x := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun q _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun a _ => by
              rw [chartChristoffel_symm (I := I) g α q a a]; ring
  rw [hCsum, hexpand]; ring

/-! ### The divergence form of the Laplacian -/

private lemma differentiableAt_chartSqrtDetGramOnE (g : RiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ (extChartAt I α).target) :
    DifferentiableAt ℝ (chartSqrtDetGramOnE (I := I) g α) x := by
  have hDpos : 0 < (gramFun (I := I) g α x).det :=
    chartGramMatrix_det_pos (I := I) g α (symm_mem_baseSet g α hx)
  have hgramDiff : DifferentiableAt ℝ (gramFun (I := I) g α) x :=
    (hasFDerivAt_pi.mpr fun i => hasFDerivAt_pi.mpr fun j =>
      (differentiableAt_chartGramOnE (I := I) g α i j hx).hasFDerivAt).differentiableAt
  have hDdiff : DifferentiableAt ℝ (fun y => (gramFun (I := I) g α y).det) x :=
    ((hasFDerivAt_det (gramFun (I := I) g α x)).comp x hgramDiff.hasFDerivAt).differentiableAt
  exact ((Real.hasDerivAt_sqrt (ne_of_gt hDpos)).comp_hasFDerivAt x
    hDdiff.hasFDerivAt).differentiableAt

/-- **Math.** **The flux computation.** For the coordinate representation `F` of a
function whose first partials are differentiable at `x`, the coordinate divergence
of the density-weighted gradient equals `√det` times the Christoffel-form
Laplacian: `Σ_a ∂_a(Σ_b G^{ab} √det ∂_b F) = √det Σ_{ab} G^{ab}(∂_a∂_b F −
Σ_k Γ^k_{ab} ∂_k F)`. This is the product-rule expansion assembled through the
divergence identity `div_invGram_identity`. -/
private lemma sum_partialDeriv_flux (g : RiemannianMetric I M) (α : M) {x : E}
    (hx : x ∈ (extChartAt I α).target) (F : E → ℝ)
    (hF1 : ∀ b, DifferentiableAt ℝ (fun y => Riemannian.partialDeriv (E := E) b F y) x) :
    ∑ a, Riemannian.partialDeriv (E := E) a
        (fun y => ∑ b, chartInvGramOnE (I := I) g α a b y
            * chartSqrtDetGramOnE (I := I) g α y * Riemannian.partialDeriv (E := E) b F y) x
      = chartSqrtDetGramOnE (I := I) g α x * ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
          * (Riemannian.partialDeriv (E := E) a
                (fun y => Riemannian.partialDeriv (E := E) b F y) x
            - ∑ k, chartChristoffel (I := I) g α a b k x
                * Riemannian.partialDeriv (E := E) k F x) := by
  classical
  have hsdiff := differentiableAt_chartSqrtDetGramOnE (I := I) g α hx
  -- per-`a` product-rule expansion of the flux
  have hWa : ∀ a, Riemannian.partialDeriv (E := E) a
      (fun y => ∑ b, chartInvGramOnE (I := I) g α a b y
          * chartSqrtDetGramOnE (I := I) g α y * Riemannian.partialDeriv (E := E) b F y) x
      = ∑ b, ((Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
              + chartInvGramOnE (I := I) g α a b x * ∑ m, chartChristoffel (I := I) g α a m m x)
            * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x)
          + chartSqrtDetGramOnE (I := I) g α x
            * (chartInvGramOnE (I := I) g α a b x
              * Riemannian.partialDeriv (E := E) a
                  (fun y => Riemannian.partialDeriv (E := E) b F y) x)) := by
    intro a
    rw [partialDeriv_fun_sum Finset.univ
      (fun b y => chartInvGramOnE (I := I) g α a b y
        * chartSqrtDetGramOnE (I := I) g α y * Riemannian.partialDeriv (E := E) b F y)
      (fun b _ => ((differentiableAt_chartInvGramOnE (I := I) g α a b hx).mul hsdiff).mul (hF1 b))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [partialDeriv_mul3 (differentiableAt_chartInvGramOnE (I := I) g α a b hx) hsdiff (hF1 b),
      partialDeriv_chartSqrtDetGramOnE (I := I) g α a hx]
    ring
  -- the divergence identity, per index `b`
  have hstar : ∀ b, ∑ a, (Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
        + chartInvGramOnE (I := I) g α a b x * ∑ m, chartChristoffel (I := I) g α a m m x)
      = - ∑ c, ∑ d, chartInvGramOnE (I := I) g α c d x
          * chartChristoffel (I := I) g α c d b x := by
    intro b
    rw [Finset.sum_add_distrib]
    exact div_invGram_identity (I := I) g α b hx
  simp only [hWa]
  calc ∑ a, ∑ b, ((Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
            + chartInvGramOnE (I := I) g α a b x * ∑ m, chartChristoffel (I := I) g α a m m x)
          * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x)
        + chartSqrtDetGramOnE (I := I) g α x
          * (chartInvGramOnE (I := I) g α a b x
            * Riemannian.partialDeriv (E := E) a
                (fun y => Riemannian.partialDeriv (E := E) b F y) x))
      = (∑ b, (∑ a, (Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
              + chartInvGramOnE (I := I) g α a b x * ∑ m, chartChristoffel (I := I) g α a m m x))
            * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x))
        + chartSqrtDetGramOnE (I := I) g α x * ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
            * Riemannian.partialDeriv (E := E) a
                (fun y => Riemannian.partialDeriv (E := E) b F y) x := by
        have hsplit : ∑ a, ∑ b, ((Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
              + chartInvGramOnE (I := I) g α a b x * ∑ m, chartChristoffel (I := I) g α a m m x)
            * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x)
          + chartSqrtDetGramOnE (I := I) g α x
            * (chartInvGramOnE (I := I) g α a b x
              * Riemannian.partialDeriv (E := E) a
                  (fun y => Riemannian.partialDeriv (E := E) b F y) x))
          = (∑ a, ∑ b, (Riemannian.partialDeriv (E := E) a (chartInvGramOnE (I := I) g α a b) x
              + chartInvGramOnE (I := I) g α a b x * ∑ m, chartChristoffel (I := I) g α a m m x)
            * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x))
          + (∑ a, ∑ b, chartSqrtDetGramOnE (I := I) g α x
            * (chartInvGramOnE (I := I) g α a b x
              * Riemannian.partialDeriv (E := E) a
                  (fun y => Riemannian.partialDeriv (E := E) b F y) x)) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_add_distrib]
        rw [hsplit]
        congr 1
        · rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_mul]
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
    _ = (∑ b, (- ∑ c, ∑ d, chartInvGramOnE (I := I) g α c d x
              * chartChristoffel (I := I) g α c d b x)
            * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x))
        + chartSqrtDetGramOnE (I := I) g α x * ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
            * Riemannian.partialDeriv (E := E) a
                (fun y => Riemannian.partialDeriv (E := E) b F y) x := by
        rw [Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => by rw [hstar b]]
    _ = chartSqrtDetGramOnE (I := I) g α x * ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
          * (Riemannian.partialDeriv (E := E) a
                (fun y => Riemannian.partialDeriv (E := E) b F y) x
            - ∑ k, chartChristoffel (I := I) g α a b k x
                * Riemannian.partialDeriv (E := E) k F x) := by
        -- reindex the Christoffel piece: `Σ_b (Σ_{cd} G^{cd} Γ^b_{cd}) √det ∂_bF
        --   = √det Σ_a Σ_b G^{ab} Σ_k Γ^k_{ab} ∂_kF`
        have hChris : ∑ b, (- ∑ c, ∑ d, chartInvGramOnE (I := I) g α c d x
              * chartChristoffel (I := I) g α c d b x)
            * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x)
            = - (chartSqrtDetGramOnE (I := I) g α x * ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
                * ∑ k, chartChristoffel (I := I) g α a b k x
                    * Riemannian.partialDeriv (E := E) k F x) := by
          have e1 : ∑ b, (- ∑ c, ∑ d, chartInvGramOnE (I := I) g α c d x
                * chartChristoffel (I := I) g α c d b x)
              * (chartSqrtDetGramOnE (I := I) g α x * Riemannian.partialDeriv (E := E) b F x)
              = ∑ b, ∑ c, ∑ d, - (chartSqrtDetGramOnE (I := I) g α x
                  * (chartInvGramOnE (I := I) g α c d x
                    * (chartChristoffel (I := I) g α c d b x
                      * Riemannian.partialDeriv (E := E) b F x))) := by
            refine Finset.sum_congr rfl fun b _ => ?_
            rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun d _ => ?_
            ring
          have e2 : - (chartSqrtDetGramOnE (I := I) g α x * ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
                * ∑ k, chartChristoffel (I := I) g α a b k x
                    * Riemannian.partialDeriv (E := E) k F x)
              = ∑ c, ∑ d, ∑ b, - (chartSqrtDetGramOnE (I := I) g α x
                  * (chartInvGramOnE (I := I) g α c d x
                    * (chartChristoffel (I := I) g α c d b x
                      * Riemannian.partialDeriv (E := E) b F x))) := by
            simp only [Finset.mul_sum, ← Finset.sum_neg_distrib]
          rw [e1, e2, Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
        have hExpand : ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
              * (Riemannian.partialDeriv (E := E) a
                  (fun y => Riemannian.partialDeriv (E := E) b F y) x
                - ∑ k, chartChristoffel (I := I) g α a b k x
                    * Riemannian.partialDeriv (E := E) k F x)
            = (∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
                * Riemannian.partialDeriv (E := E) a
                    (fun y => Riemannian.partialDeriv (E := E) b F y) x)
              - ∑ a, ∑ b, chartInvGramOnE (I := I) g α a b x
                * ∑ k, chartChristoffel (I := I) g α a b k x
                    * Riemannian.partialDeriv (E := E) k F x := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun b _ => by rw [mul_sub]
        rw [hChris, hExpand, mul_sub]
        ring

/-- **Math.** **The Laplacian in divergence form** (blueprint
`lem:laplacian-local-formula`). In a chart at `α`, writing `F = f ∘ φ⁻¹` for the
coordinate representation (`φ = extChartAt I α`), `g^{ab}` for the inverse chart
Gram matrix and `√det g` for the chart volume density,

`Δf = (det g)^{-1/2} ∂_a (g^{ab} (det g)^{1/2} ∂_b F)`.

Obtained from the Christoffel form `laplacianAt_eq_chart_formula` by the
product-rule expansion carried out in `sum_partialDeriv_flux`, the analytic
input being Jacobi's formula and metric compatibility. -/
theorem laplacianAt_eq_chart_divergence [SigmaCompactSpace M] [T2Space M]
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {α p : M} (hp : p ∈ (chartAt H α).source) :
    laplacianAt g g.leviCivitaConnection f p
      = (chartSqrtDetGramOnE (I := I) g α (extChartAt I α p))⁻¹
        * ∑ a, Riemannian.partialDeriv (E := E) a
            (fun y => ∑ b, chartInvGramOnE (I := I) g α a b y
                * chartSqrtDetGramOnE (I := I) g α y
                * Riemannian.partialDeriv (E := E) b (f ∘ (extChartAt I α).symm) y)
            (extChartAt I α p) := by
  classical
  have hxsource : p ∈ (extChartAt I α).source := by rw [extChartAt_source]; exact hp
  have hx : extChartAt I α p ∈ (extChartAt I α).target := (extChartAt I α).map_source hxsource
  have hsymmp : (extChartAt I α).symm (extChartAt I α p) = p := (extChartAt I α).left_inv hxsource
  have hspos : 0 < chartSqrtDetGramOnE (I := I) g α (extChartAt I α p) :=
    chartSqrtDetGramOnE_pos (I := I) g α hx
  -- the coordinate representation `F = f ∘ φ⁻¹` is smooth, so its first partials are
  -- differentiable at `x`
  have hFsmooth : ContDiffOn ℝ ∞ (f ∘ (extChartAt I α).symm) (extChartAt I α).target :=
    (hf.comp_contMDiffOn (contMDiffOn_extChartAt_symm (I := I) α)).contDiffOn
  have hFat : ContDiffAt ℝ ∞ (f ∘ (extChartAt I α).symm) (extChartAt I α p) :=
    hFsmooth.contDiffAt ((isOpen_extChartAt_target (I := I) α).mem_nhds hx)
  have hF1 : ∀ b, DifferentiableAt ℝ
      (fun y => Riemannian.partialDeriv (E := E) b (f ∘ (extChartAt I α).symm) y)
      (extChartAt I α p) := by
    intro b
    have hfd : DifferentiableAt ℝ (fderiv ℝ (f ∘ (extChartAt I α).symm)) (extChartAt I α p) :=
      (hFat.fderiv_right (m := 1) (by decide)).differentiableAt (by norm_num)
    exact hfd.clm_apply (differentiableAt_const _)
  -- the flux computation gives `Σ_a ∂_a(flux) = √det · (Christoffel-form Laplacian)`
  rw [sum_partialDeriv_flux (I := I) g α hx (f ∘ (extChartAt I α).symm) hF1,
    ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hspos), one_mul,
    laplacianAt_eq_chart_formula g hf hp]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [chartInvGramOnE_def, hsymmp]

end PoincareLib

end

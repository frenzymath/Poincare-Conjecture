import MorganTianLib.Ch02.HopfChart
import MorganTianLib.Ch03.RicciFlow.PDE.LocalExistence

/-!
# Morgan--Tian Ch. 3 -- the metric-chart DeTurck symbol

The fixed-frame symbol in `RicciDeTurckSymbol` records the gauge cancellation
algebra, but the local existence argument uses the inverse metric coefficients
in a coordinate chart.  This file supplies that coefficient-level bridge:
the scalar chart quadratic form is positive on every nonzero covector and its
scalar action on matrix components is coercive.

This is deliberately a principal-symbol certificate, not an assertion that a
nonlinear Ricci--DeTurck solver has been constructed.  Identifying the chart
model with the full geometric linearisation and supplying the analytic solver
remain separate hypotheses in `PDE.LocalExistence`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]

/-! ## Chart coefficient and symbol -/

/-- **Math.** The inverse-metric quadratic form appearing in the chart principal part. -/
def ricciDeTurckChartQuadratic (g : RiemannianMetric I M) (α : M)
    (y : E) (xi : RicciCovector (Module.finrank ℝ E)) : ℝ :=
  ∑ a, ∑ c, chartInvGramOnE (I := I) g α a c y * xi a * xi c

/-- **Math.** The scalar chart symbol acting on a matrix-valued variation. -/
def ricciDeTurckChartSymbol (g : RiemannianMetric I M) (α : M)
    (y : E) (xi : RicciCovector (Module.finrank ℝ E))
    (h : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  ricciDeTurckChartQuadratic g α y xi • h

/-! The coefficient regularity needed before compactness or uniformisation is
recorded directly on the chart target. -/

omit [CompleteSpace E] in
/-- **Math.** The metric-chart quadratic coefficient is continuous on the
chart target for every fixed covector. -/
theorem ricciDeTurckChartQuadratic_continuousOn
    (g : RiemannianMetric I M) (α : M)
    (xi : RicciCovector (Module.finrank ℝ E)) :
    ContinuousOn (ricciDeTurckChartQuadratic g α · xi)
      (extChartAt I α).target := by
  classical
  unfold ricciDeTurckChartQuadratic
  exact continuousOn_finsetSum _ (fun a _ =>
    continuousOn_finsetSum _ (fun c _ =>
      ((chartInvGramOnE_continuousOn g α a c).mul continuousOn_const).mul
        continuousOn_const))

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** The metric Riesz vector of a cotangent vector has the inverse-Gram
expansion in a chart frame.  This is the intrinsic-to-coordinate bridge used
by the chart principal symbol. -/
theorem metricRiesz_eq_chartInvGram_sum
    (g : RiemannianMetric I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    (phi : TangentSpace I p →L[ℝ] ℝ) :
    g.metricRiesz p phi =
      ∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
              phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
        Tensor.chartBasisVecFiber (I := I) alpha i p := by
  classical
  have hbase : p ∈ (trivializationAt E (TangentSpace I) alpha).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hp
  have hinner : ∀ k,
      g.inner p
          (∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                  phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
              Tensor.chartBasisVecFiber (I := I) alpha i p)
          (Tensor.chartBasisVecFiber (I := I) alpha k p) =
        phi (Tensor.chartBasisVecFiber (I := I) alpha k p) := by
    intro k
    rw [show g.inner p
          (∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                  phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
              Tensor.chartBasisVecFiber (I := I) alpha i p)
        = ∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                  phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
              g.inner p (Tensor.chartBasisVecFiber (I := I) alpha i p) from by
          rw [map_sum]
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [map_smul]]
    rw [sum_apply Finset.univ
      (fun i => (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
          phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
        g.inner p (Tensor.chartBasisVecFiber (I := I) alpha i p))
      (Tensor.chartBasisVecFiber (I := I) alpha k p)]
    have hsmul : ∀ i,
        ((∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
            phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
              g.inner p (Tensor.chartBasisVecFiber (I := I) alpha i p))
            (Tensor.chartBasisVecFiber (I := I) alpha k p) =
          (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
              phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) *
            Tensor.chartGramMatrix (I := I) g alpha p i k := by
      intro i
      rw [smul_apply, smul_eq_mul]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hsmul i)]
    have hdistrib : ∀ i,
        (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
            phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) *
          Tensor.chartGramMatrix (I := I) g alpha p i k
            = ∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                phi (Tensor.chartBasisVecFiber (I := I) alpha j p) *
              Tensor.chartGramMatrix (I := I) g alpha p i k := by
      intro i
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun i _ => hdistrib i)]
    rw [Finset.sum_comm]
    have hfact : ∀ j,
        (∑ i, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
            phi (Tensor.chartBasisVecFiber (I := I) alpha j p) *
          Tensor.chartGramMatrix (I := I) g alpha p i k)
          = (∑ i, Tensor.chartGramMatrix (I := I) g alpha p i k *
              Tensor.chartInvGramMatrix (I := I) g alpha p i j) *
            phi (Tensor.chartBasisVecFiber (I := I) alpha j p) := by
      intro j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [Finset.sum_congr rfl (fun j _ => hfact j)]
    have hsym : ∀ i j,
        Tensor.chartGramMatrix (I := I) g alpha p i k *
          Tensor.chartInvGramMatrix (I := I) g alpha p i j =
        Tensor.chartGramMatrix (I := I) g alpha p k i *
            Tensor.chartInvGramMatrix (I := I) g alpha p i j := by
      intro i j
      have h := (Tensor.chartGramMatrix_isHermitian (I := I) g alpha p).apply k i
      simp only [star_trivial] at h
      rw [h]
    have hkj : ∀ j,
        (∑ i, Tensor.chartGramMatrix (I := I) g alpha p i k *
            Tensor.chartInvGramMatrix (I := I) g alpha p i j) =
          (1 : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ) k j := by
      intro j
      rw [Finset.sum_congr rfl (fun i _ => hsym i j)]
      have hmul :=
        Tensor.chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hbase
      have hprod_eq :
          (Tensor.chartGramMatrix (I := I) g alpha p *
              Tensor.chartInvGramMatrix (I := I) g alpha p) k j =
            (1 : Matrix (Fin (Module.finrank ℝ E))
                (Fin (Module.finrank ℝ E)) ℝ) k j := by
        rw [hmul]
      rw [← hprod_eq]
      rfl
    rw [Finset.sum_congr rfl (fun j _ => by rw [hkj j])]
    rw [Finset.sum_eq_single k]
    · simp [Matrix.one_apply_eq]
    · intro j _ hjk
      rw [Matrix.one_apply_ne (Ne.symm hjk), zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  symm
  apply g.metricRiesz_unique
  intro W
  change g.inner p
      (∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
              phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
          Tensor.chartBasisVecFiber (I := I) alpha i p) W = phi W
  let B := Tensor.chartBasisFamily (I := I) alpha hbase
  calc
    g.inner p
        (∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
            Tensor.chartBasisVecFiber (I := I) alpha i p) W
        = g.inner p
            (∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                    phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
                Tensor.chartBasisVecFiber (I := I) alpha i p)
            (∑ k, (B.repr W k) • B k) := by rw [B.sum_repr]
    _ = ∑ k, B.repr W k *
          g.inner p
            (∑ i, (∑ j, Tensor.chartInvGramMatrix (I := I) g alpha p i j *
                    phi (Tensor.chartBasisVecFiber (I := I) alpha j p)) •
                Tensor.chartBasisVecFiber (I := I) alpha i p) (B k) := by
          rw [map_sum]
          refine Finset.sum_congr rfl fun k _ => by
            rw [map_smul, smul_eq_mul]
    _ = ∑ k, B.repr W k * phi (B k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show B k = Tensor.chartBasisVecFiber (I := I) alpha k p from
            Tensor.chartBasisFamily_apply (I := I) alpha hbase k]
          rw [hinner k]
    _ = phi (∑ k, (B.repr W k) • B k) := by
          rw [map_sum]
          refine (Finset.sum_congr rfl fun k _ => by
            rw [map_smul, smul_eq_mul]).symm
    _ = phi W := by rw [B.sum_repr]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** On the components of a genuine cotangent vector, the chart
quadratic form is the intrinsic squared metric-dual norm. -/
theorem ricciDeTurckChartQuadratic_cotangent
    (g : RiemannianMetric I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    (phi : TangentSpace I p →L[ℝ] ℝ) :
    ricciDeTurckChartQuadratic g alpha (extChartAt I alpha p)
        (fun i => phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) =
      g.metricInner p (g.metricRiesz p phi) (g.metricRiesz p phi) := by
  have hp' : p ∈ (extChartAt I alpha).source := by
    rwa [extChartAt_source]
  unfold ricciDeTurckChartQuadratic
  simp only [chartInvGramOnE_def, (extChartAt I alpha).left_inv hp']
  rw [g.metricRiesz_inner, metricRiesz_eq_chartInvGram_sum g alpha hp phi]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
/-- **Math.** The intrinsic chart quadratic is strictly positive on every
nonzero cotangent vector. -/
theorem ricciDeTurckChartQuadratic_cotangent_pos
    (g : RiemannianMetric I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    {phi : TangentSpace I p →L[ℝ] ℝ} (hphi : phi ≠ 0) :
    0 < ricciDeTurckChartQuadratic g alpha (extChartAt I alpha p)
        (fun i => phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) := by
  rw [ricciDeTurckChartQuadratic_cotangent g alpha hp phi]
  apply g.metricInner_self_pos
  intro hriesz
  apply hphi
  ext v
  have h := g.metricRiesz_inner p phi v
  rw [hriesz] at h
  simpa using h.symm

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] in
theorem ricciDeTurckChartSymbol_pairing_self
    (g : RiemannianMetric I M) (α : M) (y : E)
    (xi : RicciCovector (Module.finrank ℝ E))
    (h : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :
    ricciMatrixPairing h (ricciDeTurckChartSymbol g α y xi h) =
      ricciDeTurckChartQuadratic g α y xi * ricciMatrixNormSq h := by
  classical
  rw [ricciDeTurckChartSymbol]
  simp only [ricciMatrixPairing, ricciMatrixNormSq, Matrix.smul_apply,
    smul_eq_mul]
  calc
    (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
        h ij.1 ij.2 * (ricciDeTurckChartQuadratic g α y xi * h ij.1 ij.2)) =
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ricciDeTurckChartQuadratic g α y xi *
            (h ij.1 ij.2 * h ij.1 ij.2) := by
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    _ = ricciDeTurckChartQuadratic g α y xi *
        ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          h ij.1 ij.2 * h ij.1 ij.2 := by
      rw [Finset.mul_sum]
    _ = ricciDeTurckChartQuadratic g α y xi * ricciMatrixNormSq h := by
      apply congrArg (fun z : ℝ => ricciDeTurckChartQuadratic g α y xi * z)
      apply Finset.sum_congr rfl
      intro ij hij
      ring

/-! ## Strict-parabolic certificate in a metric chart -/

omit [CompleteSpace E] in
/-- **Math.** Coercivity of the metric-chart scalar symbol on matrix variations. -/
theorem ricciDeTurckChartSymbol_coercive
    (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ (extChartAt I α).target)
    {xi : RicciCovector (Module.finrank ℝ E)} (hxi : xi ≠ 0)
    {h : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ}
    (hh : h ≠ 0) :
    0 < ricciMatrixPairing h (ricciDeTurckChartSymbol g α y xi h) := by
  rw [ricciDeTurckChartSymbol_pairing_self]
  exact mul_pos (chartInvGramOnE_quadratic_pos g α hy hxi)
    (ricciMatrixNormSq_pos hh)

/-- **Math.** A bundled certificate for the chart principal symbol used by the
strict-parabolic local-existence interface. -/
structure RicciDeTurckChartStrictParabolic
    (g : RiemannianMetric I M) (α : M) : Prop where
  coercive :
    ∀ {y : E}, y ∈ (extChartAt I α).target →
      ∀ {xi : RicciCovector (Module.finrank ℝ E)}, xi ≠ 0 →
        ∀ {h : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ},
          h ≠ 0 →
            0 < ricciMatrixPairing h
              (ricciDeTurckChartSymbol g α y xi h)

omit [CompleteSpace E] in
/-- **Math.** The inverse Gram matrix supplies the chart strict-parabolic certificate
without an additional existence assumption. -/
theorem canonicalRicciDeTurckChartStrictParabolic
    (g : RiemannianMetric I M) (α : M) :
    RicciDeTurckChartStrictParabolic g α where
  coercive := by
    intro y hy xi hxi h hh
    exact ricciDeTurckChartSymbol_coercive g α hy hxi hh

end MorganTianLib

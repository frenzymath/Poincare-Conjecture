import Topping.ParabolicPDE.Scalar
import Topping.MaximumPrinciple.Riemannian
import MorganTianLib.Ch01.LaplacianDivergence
import MorganTianLib.Ch02.HopfChart

open scoped ContDiff Manifold Topology Bundle Matrix
open Riemannian

noncomputable section

namespace Topping
namespace ParabolicPDE

/-! ### The local scalar operator of the Laplace--Beltrami operator

The coefficient field below is pulled back to the model space of a chart.  It
keeps the inverse Gram matrix as the leading coefficient and the contracted
Christoffel symbols as the first-order coefficient.  Thus the definition is
an adapter around Morgan--Tian's genuine coordinate producers, rather than a
predicate assuming a desired local formula.
-/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The scalar second-order coefficients of `Δ` in the chart at `alpha`. -/
def laplaceBeltramiChartCoefficients
    (g : RiemannianMetric I M) (alpha : M) :
    ScalarSecondOrderCoefficients E (Module.finrank ℝ E) where
  a := fun y i j => chartInvGramOnE (I := I) g alpha i j y
  b := fun y k => MorganTianLib.chartLaplaceB (I := I) g alpha k y
  c := fun _ => 0

/-- **Math.** The coordinate two-jet used by the chart operator. -/
def coordinateSecondOrderJet (u : E → ℝ) (y : E) :
    ScalarSecondOrderJet (Module.finrank ℝ E) where
  value := u y
  first := fun k =>
    fderiv ℝ u y ((Module.finBasis ℝ E) k)
  second := fun i j =>
    fderiv ℝ (fun z => fderiv ℝ u z ((Module.finBasis ℝ E) j)) y
      ((Module.finBasis ℝ E) i)

omit [NeZero (Module.finrank ℝ E)] in
theorem laplaceBeltramiChartCoefficients_applyJet
    (g : RiemannianMetric I M) (alpha : M) (u : E → ℝ) (y : E) :
    (laplaceBeltramiChartCoefficients g alpha).applyJet y
        (coordinateSecondOrderJet u y) =
      MorganTianLib.chartLaplaceOp (I := I) g alpha u y := by
  simp [laplaceBeltramiChartCoefficients, coordinateSecondOrderJet,
    ScalarSecondOrderCoefficients.applyJet, MorganTianLib.chartLaplaceOp]

omit [NeZero (Module.finrank ℝ E)] in
theorem laplaceBeltramiChartCoefficients_principalSymbol
    (g : RiemannianMetric I M) (alpha : M) (y : E)
    (xi : Fin (Module.finrank ℝ E) → ℝ) :
    (laplaceBeltramiChartCoefficients g alpha).principalSymbol y xi =
      ∑ i, ∑ j, chartInvGramOnE (I := I) g alpha i j y
        * xi i * xi j := by
  unfold ScalarSecondOrderCoefficients.principalSymbol
  rw [symbol_eq_sum]
  rfl

theorem laplaceBeltramiChartCoefficients_principalSymbol_pos
    (g : RiemannianMetric I M) (alpha : M) {y : E}
    (hy : y ∈ (extChartAt I alpha).target)
    {xi : Fin (Module.finrank ℝ E) → ℝ} (hxi : xi ≠ 0) :
    0 < (laplaceBeltramiChartCoefficients g alpha).principalSymbol y xi := by
  rw [laplaceBeltramiChartCoefficients_principalSymbol]
  exact MorganTianLib.chartInvGramOnE_quadratic_pos g alpha hy hxi

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The metric Riesz vector of a cotangent vector has the expected
inverse-Gram expansion in a chart basis. -/
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
          (Tensor.chartBasisVecFiber (I := I) alpha k p)
        = phi (Tensor.chartBasisVecFiber (I := I) alpha k p) := by
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
          Tensor.chartInvGramMatrix (I := I) g alpha p i j
          = Tensor.chartGramMatrix (I := I) g alpha p k i *
            Tensor.chartInvGramMatrix (I := I) g alpha p i j := by
      intro i j
      have h := (Tensor.chartGramMatrix_isHermitian (I := I) g alpha p).apply k i
      simp only [star_trivial] at h
      rw [h]
    have hkj : ∀ j,
        (∑ i, Tensor.chartGramMatrix (I := I) g alpha p i k *
            Tensor.chartInvGramMatrix (I := I) g alpha p i j)
          = (1 : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ) k j := by
      intro j
      rw [Finset.sum_congr rfl (fun i _ => hsym i j)]
      have hmul :=
        Tensor.chartGramMatrix_mul_chartInvGramMatrix (I := I) g alpha hbase
      have hprod_eq :
          (Tensor.chartGramMatrix (I := I) g alpha p *
              Tensor.chartInvGramMatrix (I := I) g alpha p) k j
            = (1 : Matrix (Fin (Module.finrank ℝ E))
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

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** On chart components of a genuine cotangent vector, the scalar
principal symbol of the Laplace--Beltrami operator is its metric dual norm
squared. -/
theorem laplaceBeltramiChartCoefficients_principalSymbol_cotangent
    (g : RiemannianMetric I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    (phi : TangentSpace I p →L[ℝ] ℝ) :
    (laplaceBeltramiChartCoefficients g alpha).principalSymbol
        (extChartAt I alpha p)
        (fun i => phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) =
      g.metricInner p (g.metricRiesz p phi) (g.metricRiesz p phi) := by
  have hp' : p ∈ (extChartAt I alpha).source := by
    rwa [extChartAt_source]
  rw [laplaceBeltramiChartCoefficients_principalSymbol]
  simp only [chartInvGramOnE_def, (extChartAt I alpha).left_inv hp']
  rw [g.metricRiesz_inner, metricRiesz_eq_chartInvGram_sum g alpha hp phi]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => by ring

omit [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The Laplace--Beltrami principal symbol is strictly positive on
every nonzero cotangent vector, intrinsically as well as in coordinates. -/
theorem laplaceBeltramiChartCoefficients_principalSymbol_cotangent_pos
    (g : RiemannianMetric I M) (alpha : M) {p : M}
    (hp : p ∈ (chartAt H alpha).source)
    {phi : TangentSpace I p →L[ℝ] ℝ} (hphi : phi ≠ 0) :
    0 < (laplaceBeltramiChartCoefficients g alpha).principalSymbol
        (extChartAt I alpha p)
        (fun i => phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) := by
  rw [laplaceBeltramiChartCoefficients_principalSymbol_cotangent g alpha hp phi]
  apply g.metricInner_self_pos
  intro hriesz
  apply hphi
  ext v
  have h := g.metricRiesz_inner p phi v
  rw [hriesz] at h
  simpa using h.symm

/-- **Math.** Restricting the pulled-back coefficient field to the chart target gives a
genuine pointwise-parabolic scalar coefficient field. -/
def laplaceBeltramiChartTargetCoefficients
    (g : RiemannianMetric I M) (alpha : M) :
    ScalarSecondOrderCoefficients
      {y : E // y ∈ (extChartAt I alpha).target} (Module.finrank ℝ E) where
  a := fun y => (laplaceBeltramiChartCoefficients g alpha).a y.1
  b := fun y => (laplaceBeltramiChartCoefficients g alpha).b y.1
  c := fun y => (laplaceBeltramiChartCoefficients g alpha).c y.1

theorem laplaceBeltramiChartTargetCoefficients_pointwiseParabolic
    (g : RiemannianMetric I M) (alpha : M) :
    PointwiseParabolic (laplaceBeltramiChartTargetCoefficients g alpha) := by
  intro y xi hxi
  exact laplaceBeltramiChartCoefficients_principalSymbol_pos g alpha y.property hxi

/-! ### Intrinsic-to-coordinate bridges

The next statements use Morgan--Tian's proved Christoffel and divergence
formulae.  They are stated for a chart-source point, where the coordinate
representation is an actual smooth function.
-/

variable [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

theorem laplacianAt_eq_laplaceBeltramiChart_applyJet
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {alpha p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    MorganTianLib.laplacianAt g g.leviCivitaConnection f p =
      (laplaceBeltramiChartCoefficients g alpha).applyJet
        (extChartAt I alpha p)
        (coordinateSecondOrderJet (f ∘ (extChartAt I alpha).symm)
          (extChartAt I alpha p)) := by
  rw [MorganTianLib.laplacianAt_eq_chartLaplaceOp g hf hp]
  exact (laplaceBeltramiChartCoefficients_applyJet g alpha _ _).symm

theorem metricLaplacianAt_eq_laplaceBeltramiChart_applyJet
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {alpha p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    metricLaplacianAt g f p =
      (laplaceBeltramiChartCoefficients g alpha).applyJet
        (extChartAt I alpha p)
        (coordinateSecondOrderJet (f ∘ (extChartAt I alpha).symm)
          (extChartAt I alpha p)) := by
  have hdim : Module.finrank ℝ E ≠ 0 := NeZero.ne _
  simp only [metricLaplacianAt, hdim, ↓reduceDIte]
  exact laplacianAt_eq_laplaceBeltramiChart_applyJet g hf hp

/-- **Math.** The chart volume density `sqrt (det g_ij)`. -/
def laplaceBeltramiChartDensity
    (g : RiemannianMetric I M) (alpha : M) : E → ℝ :=
  fun y => Real.sqrt
    (Matrix.det (fun i j => chartGramOnE (I := I) g alpha i j y))

theorem metricLaplacianAt_eq_laplaceBeltramiChart_divergence
    (g : RiemannianMetric I M) {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {alpha p : M}
    (hp : p ∈ (chartAt H alpha).source) :
    metricLaplacianAt g f p =
      (laplaceBeltramiChartDensity g alpha
          (extChartAt I alpha p))⁻¹
        * ∑ i, partialDeriv (E := E) i
            (fun y => ∑ j, chartInvGramOnE (I := I) g alpha i j y
                * laplaceBeltramiChartDensity g alpha y
                * partialDeriv (E := E) j
                    (f ∘ (extChartAt I alpha).symm) y)
            (extChartAt I alpha p) := by
  have hdim : Module.finrank ℝ E ≠ 0 := NeZero.ne _
  simp only [metricLaplacianAt, hdim, ↓reduceDIte]
  with_unfolding_all exact
    MorganTianLib.laplacianAt_eq_chart_divergence g hf hp

end ParabolicPDE
end Topping

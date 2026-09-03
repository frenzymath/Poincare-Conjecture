import MorganTianLib.Ch03.RicciFlow.ExactSolutions
import DoCarmoLib.Riemannian.Jacobi.JacobiConstantCurvature

/-!
# Morgan--Tian Ch. 3 -- constant curvature is Einstein

The do Carmo pointwise constant-curvature formula is contracted in an
orthonormal basis.  This supplies the general space-form calculation used by
the spherical and hyperbolic Ricci-flow examples.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A Levi--Civita metric of constant sectional curvature `K` is
Einstein with constant `(dim M - 1) K`.  The proof contracts do Carmo's
pointwise constant-curvature `(0,4)` formula in a standard orthonormal basis;
the Parseval term is the trace of the rank-one contraction. -/
theorem isEinsteinTensor_of_isConstantCurvature
    (g : RiemannianMetric I M) (K : ℝ)
    (hK : g.leviCivitaConnection.IsConstantCurvature g K) :
    IsEinsteinTensor g ((((Module.finrank ℝ E : ℕ) : ℝ) - 1) * K) := by
  intro p v w
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y W q => g.koszulDualSection_dual X Y W q)
  rw [← ricciAt_leviCivita_eq_ricciTensorAt g hLC p v w]
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  rw [ricciAt, Riemannian.ricciForm_eq_sum _ v w b]
  have hdiag (i : Fin (Module.finrank ℝ (TangentSpace I p))) :
      g.metricInner p (b i) (b i) = 1 := by
    exact (orthonormal_iff_ite.mp b.orthonormal i i).trans (by simp)
  have hparseval :
      (∑ i, inner ℝ v (b i) * inner ℝ (b i) w) = inner ℝ v w :=
    OrthonormalBasis.sum_inner_mul_inner b v w
  have hparseval' :
      (∑ i, g.metricInner p v (b i) * g.metricInner p (b i) w) =
      g.metricInner p v w := by
    change (∑ i, inner ℝ v (b i) * inner ℝ (b i) w) = inner ℝ v w
    exact hparseval
  have hparseval'' :
      (∑ i, g.metricInner p (b i) w * g.metricInner p v (b i)) =
      g.metricInner p v w := by
    calc
      _ = ∑ i, g.metricInner p v (b i) * g.metricInner p (b i) w := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = _ := hparseval'
  simp_rw [curvatureFormAt_eq_affineCurvatureFormAt]
  simp_rw [Riemannian.Jacobi.curvatureFormAt_isConstantCurvature (I := I) g hK p]
  simp_rw [hdiag]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hsecond :
      (∑ i, K * (g.metricInner p (b i) w * g.metricInner p v (b i))) =
      K * g.metricInner p v w := by
    rw [← Finset.mul_sum, hparseval'']
  rw [hsecond]
  simp only [mul_one, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have hfr : Module.finrank ℝ (TangentSpace I p) =
      Module.finrank ℝ E := rfl
  rw [hfr]
  ring

end MorganTianLib

end

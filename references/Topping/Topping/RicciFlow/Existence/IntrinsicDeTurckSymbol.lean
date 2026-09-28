import Topping.RicciFlow.Existence.IntrinsicSymbolBridge
import Topping.RicciFlow.Existence.Linearisation
import MorganTianLib.Ch03.RicciFlow.PDE.ChartSymbol

/-!
# Intrinsic metric-chart symbol on the DeTurck tensor fibre

`IntrinsicSymbolBridge` supplies the inverse-Gram chart operator for an
arbitrary coefficient fibre.  This file fixes the fibre to the symmetric
two-tensors used by the DeTurck linearisation, so the strict-parabolic symbol
producer is directly usable by a geometric Ricci-flow consumer.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping
namespace IntrinsicSymbolBridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## The concrete tensor-fibre operator -/

abbrev metricChartDeTurckOperator
    (g : RiemannianMetric I M) (alpha : M) :=
  metricChartOperator (I := I) g alpha
    (FixedFrameSym2 (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
theorem metricChartDeTurckOperator_symbol
    (g : RiemannianMetric I M) (alpha : M)
    (y : ChartTarget I alpha) (xi : Fin (Module.finrank ℝ E) → ℝ) :
    (metricChartDeTurckOperator (I := I) g alpha).symbol y xi =
      (metricChartInverseGramQuadratic (I := I) g alpha y xi) •
        ContinuousLinearMap.id ℝ (FixedFrameSym2 (Module.finrank ℝ E)) := by
  exact metricChartOperator_symbol g alpha
    (FixedFrameSym2 (Module.finrank ℝ E)) y xi

/-! ## Connection with the Morgan--Tian chart symbol -/

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** The inverse-Gram quadratic form used by the generic Topping
operator is definitionally the chart quadratic form exported by the
Morgan--Tian PDE interface.  The subtype coercion records that the Topping
operator is evaluated on an actual chart-target point. -/
theorem metricChartInverseGramQuadratic_eq_ricciDeTurckChartQuadratic
    (g : RiemannianMetric I M) (alpha : M)
    (y : ChartTarget I alpha)
    (xi : Fin (Module.finrank ℝ E) → ℝ) :
    metricChartInverseGramQuadratic (I := I) g alpha y xi =
      MorganTianLib.ricciDeTurckChartQuadratic g alpha y.1 xi := by
  rfl

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** After applying the matrix representation of the symmetric
two-tensor fibre, the Topping intrinsic symbol is exactly the
Morgan--Tian chart symbol.  This is the atlas-level instantiation of the
generic symbol bridge. -/
theorem matrixOfSym2_metricChartDeTurckOperator_symbol_eq_chartSymbol
    (g : RiemannianMetric I M) (alpha : M)
    (y : ChartTarget I alpha)
    (xi : Fin (Module.finrank ℝ E) → ℝ)
    (h : FixedFrameSym2 (Module.finrank ℝ E)) :
    matrixOfSym2
        ((metricChartDeTurckOperator (I := I) g alpha).symbol y xi h) =
    MorganTianLib.ricciDeTurckChartSymbol g alpha y.1 xi
        (matrixOfSym2 h) := by
  rw [metricChartDeTurckOperator_symbol]
  change matrixOfSym2
      (metricChartInverseGramQuadratic (I := I) g alpha y xi • h) = _
  rw [matrixOfSym2_smul]
  rw [metricChartInverseGramQuadratic_eq_ricciDeTurckChartQuadratic]
  rfl

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
theorem metricChartDeTurckOperator_strictlyParabolic
    (g : RiemannianMetric I M) (alpha : M) :
    StrictlyParabolic
      (metricChartDeTurckOperator (I := I) g alpha).symbol
      (metricChartInverseGramQuadratic (I := I) g alpha) := by
  exact metricChartOperator_strictlyParabolic g alpha
    (FixedFrameSym2 (Module.finrank ℝ E))

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
theorem metricChartDeTurckOperator_symbol_cotangent
    (g : RiemannianMetric I M) (alpha : M)
    {p : M} (hp : p ∈ (chartAt H alpha).source)
    (phi : TangentSpace I p →L[ℝ] ℝ) :
    (metricChartDeTurckOperator (I := I) g alpha).symbol
        ⟨(extChartAt I alpha) p,
          (extChartAt I alpha).map_source (by
            rwa [extChartAt_source])⟩
        (fun i => phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) =
      (g.metricInner p (g.metricRiesz p phi) (g.metricRiesz p phi)) •
        ContinuousLinearMap.id ℝ (FixedFrameSym2 (Module.finrank ℝ E)) := by
  exact metricChartOperator_symbol_cotangent g alpha
    (FixedFrameSym2 (Module.finrank ℝ E)) hp phi

omit [CompleteSpace E] [I.Boundaryless] [SigmaCompactSpace M] in
/-- **Math.** The intrinsic chart symbol and the fixed-frame DeTurck symbol
agree on the same cotangent vector, after the latter is expressed in the
canonical metric-orthonormal frame at the chart point.  Thus the chart symbol
bridge is unconditional: its scalar is identified by the Riesz norm identity,
not by a separately postulated symbol-compatibility predicate. -/
theorem metricChartDeTurckOperator_symbol_eq_fixedFrameDeTurckSymbol_orthonormal
    (g : RiemannianMetric I M) (alpha : M)
    {p : M} (hp : p ∈ (chartAt H alpha).source)
    (phi : TangentSpace I p →L[ℝ] ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (metricChartDeTurckOperator (I := I) g alpha).symbol
        ⟨(extChartAt I alpha) p,
          (extChartAt I alpha).map_source (by
            rwa [extChartAt_source])⟩
        (fun i : Fin (Module.finrank ℝ E) =>
          phi (Tensor.chartBasisVecFiber (I := I) alpha i p)) =
      fixedFrameDeTurckSymbol ()
        (fun i : Fin (Module.finrank ℝ E) =>
          phi (MorganTianLib.orthoFrameBasis g p
            (MorganTianLib.mem_orthoFrameSet_self p) i)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := MorganTianLib.orthoFrameBasis g p
    (MorganTianLib.mem_orthoFrameSet_self p)
  have hcomp : ∀ i : Fin (Module.finrank ℝ E),
      phi (b i) = inner ℝ (b i) (g.metricRiesz p phi) := by
    intro i
    rw [MorganTianLib.inner_tangentSpace_eq_metricInner, g.metricInner_comm,
      g.metricRiesz_inner]
  have hnorm :
      ∑ i, phi (b i) ^ 2 =
        g.metricInner p (g.metricRiesz p phi) (g.metricRiesz p phi) := by
    calc
      ∑ i, phi (b i) ^ 2 =
          ∑ i, (inner ℝ (b i) (g.metricRiesz p phi)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [hcomp]
      _ = ‖g.metricRiesz p phi‖ ^ 2 := b.sum_sq_inner_right _
      _ = inner ℝ (g.metricRiesz p phi) (g.metricRiesz p phi) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = g.metricInner p (g.metricRiesz p phi) (g.metricRiesz p phi) :=
        MorganTianLib.inner_tangentSpace_eq_metricInner g p _ _
  rw [metricChartDeTurckOperator_symbol_cotangent g alpha hp phi]
  rw [fixedFrameDeTurckSymbol_eq_covectorNormSq_smul_id]
  congr 1
  unfold covectorNormSq
  exact hnorm.symm

omit [CompleteSpace E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
theorem metricChartDeTurckOperator_exponentialJet_normalized_tendsto
    (g : RiemannianMetric I M) (alpha : M)
    (x : ChartTarget I alpha) (xi : Fin (Module.finrank ℝ E) → ℝ)
    (v : FixedFrameSym2 (Module.finrank ℝ E))
    (firstData : Fin (Module.finrank ℝ E) → FixedFrameSym2 (Module.finrank ℝ E))
    (secondData : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      FixedFrameSym2 (Module.finrank ℝ E))
    (phiSecond : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
    Filter.Tendsto
      (fun s : ℝ => s⁻¹ ^ 2 •
        (metricChartDeTurckOperator (I := I) g alpha).toVectorSecondOrderCoefficients.applyJet
          x (VectorSecondOrderCoefficients.exponentialJet s xi v
            firstData secondData phiSecond))
      Filter.atTop
      (nhds ((metricChartDeTurckOperator (I := I) g alpha).symbol x xi v)) := by
  exact metricChartOperator_exponentialJet_normalized_tendsto g alpha
    (FixedFrameSym2 (Module.finrank ℝ E)) x xi v firstData secondData phiSecond

#print axioms metricChartDeTurckOperator_strictlyParabolic
#print axioms metricChartDeTurckOperator_symbol_cotangent
#print axioms metricChartDeTurckOperator_exponentialJet_normalized_tendsto

end IntrinsicSymbolBridge
end Topping

end

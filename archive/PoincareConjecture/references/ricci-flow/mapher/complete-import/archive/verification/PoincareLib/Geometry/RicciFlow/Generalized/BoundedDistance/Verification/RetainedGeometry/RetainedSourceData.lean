import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.RetainedGeometry.RetainedFinalSourceData
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.RetainedGeometry.RetainedPositiveRecutData
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.SourceGeometry.CriticalBall.SourceCriticalBallNonnegative

/-!
# Direct audits of the retained actual source and recut packets

The original counterexamples construct both packets and the curvature
sign on the same first spatial limit. The closed lower M04 theorem
also supplies the exact Type0 theory for the terminal obstruction.
Source: MT pp. 253-255 and 263-265; M28 derivations 161a-161b.
-/

set_option autoImplicit false

example : PoincareMT.RicciFlowCurvatureTheory.{0} :=
  PoincareMT.ricciFlowCurvatureTheory.{0}

#print axioms PoincareMT.ricciFlowCurvatureTheory
#print axioms PoincareMT.M28.CounterexampleNeckFamily.FinalSourceDiagonalReadouts
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.stage_guard
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.scale_error
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.base_lower
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.normalization_lower
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.metric_bounds
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.scalar_error
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.inverse_center
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedFinalSourceData.core_capture
#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_retained_final_source_data_accuracy
#print axioms PoincareMT.M28.CounterexampleNeckFamily.RetainedPositiveRecutData
#print axioms PoincareMT.M28.CounterexampleNeckFamily.exists_retained_positive_recut_data_accuracy
#print axioms PoincareMT.M28.intrinsicOpenMetric_nonnegativeCurvatureOperator_iff
#print axioms PoincareMT.M28.intrinsicOpenMetric_nonnegativeSectionalCurvature_of_operator
#print axioms
  PoincareMT.M28.CounterexampleNeckFamily.exists_source_criticalBall_nonnegative_accuracy

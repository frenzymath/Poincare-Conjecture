import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Exclusion

/-!
# Final M28 assembly axiom checks

The published entry and the actual counterexample exclusion are checked
after their final assembly. Source: Morgan--Tian Theorem 10.2, pp. 245-265;
M28 derivation 161e.
-/

set_option autoImplicit false

#print axioms PoincareMT.M28.exists_actual_counterexample_exclusion_accuracy
#print axioms PoincareMT.M28.no_selected_end_source_chart_limit
#print axioms PoincareMT.M28.SelectedEndSourceChartObstructionStatement

import PetersenLib.Ch05.LocalIsometryCovering
import PetersenLib.Ch05.UniformInjectivityRadiusDiffeo

open Bundle Manifold Set Filter Function
open scoped Manifold Topology ContDiff ENNReal

noncomputable section

namespace PetersenLib

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)] [T2Space M]
variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [CompleteSpace E'] [T2Space (TangentBundle I' M')] [T2Space M']

#check compactSet_uniformCInftyDiffeo
#check IsOpen.trivializationDiscrete
#check IsLocalRiemannianIsometry.isLocalDiffeomorph
#check IsLocalDiffeomorph.isLocalHomeomorph
#check IsLocalHomeomorph.isOpenEmbedding_of_comp
#check IsLocalHomeomorph.eqOn_lift
#check IsLocalHomeomorph.continuous_lift
#check IsLocalRiemannianIsometry.preservesMetric
#check localIsometry_expNaturality
#check exists_geodesicMaximal_reverse
#check geodesicMaximalCurve_spec
#check geodesicMaximalCurve_eqOn
#check IsGeodesicWithInitialOn.shift
#check Geodesic.IsGeodesicOn
#check isOpen_geodesicMaximalDomain
#check ordConnected_geodesicMaximalDomain

end PetersenLib

end

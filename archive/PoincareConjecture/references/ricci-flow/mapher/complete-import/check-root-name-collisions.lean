import PoincareLib.Geometry.RicciFlow.Pinching.GeometricPreservation.Coordinates
import PoincareLib.Geometry.RicciFlow.Pinching.GeometricPreservation.TransportCoordinates
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.GraphShift
import PoincareLib.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.GraphShift
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.Cylinder.SmoothGraphTransport
import PoincareLib.Topology.Manifold.NeckCap.Overlap.SmoothGraphTransport

/-! Import-pair regression check for the combined production root.
The original modules failed on the coordinate definition and graph-shift name.
The distinct graph-transport types were masked by that prerequisite failure.
-/

#check PoincareMT.RicciFlow.Frame.transportedTensorCoordinateSection
#check PoincareMT.CylinderGluing.exists_supported_graph_shift
#check PoincareMT.CylinderGluing.exists_supported_graph_shift_of_strict_bounds
#check PoincareMT.EpsilonNeck.exists_smooth_graph_transport
#check PoincareMT.EpsilonNeck.exists_compactly_supported_smooth_graph_transport

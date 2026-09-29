import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.Meridian
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.Rotation
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.Axis
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.RoundedBody
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.DefiningFunction
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.RegularCircle
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.NeckFrontier
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.Parametrization
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.RoundedAxis
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.FilledMeridian
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Connected
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Regularity
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Filling
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Compression
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Inward.Ellipse
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Matching
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Recovery
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Normalization
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.UpperArc.Transport
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.PairUpper.Equator.Replacement

#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.profileCapShear_body_iff
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.profileCapPair_body_iff_meridian
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.profileCapPair_body_mem_iff_of_meridian_eq
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.rotationalLift
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.rotationalLift_image_meridian
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.rotationalLift_image_upper
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_profileCapPair_elliptical_axis_tube
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.profileCapPair_body_iff_neck_on_tail
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.isCompact_roundedPairBody
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedPairBody_iff_neck_in_box
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.contactDisk_subset_interior_roundedPairBody
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.contDiff_roundedPairDefining
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedPairDefining_nonpos_iff
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedPairBody_frontier_iff_neck_in_box
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_smooth_circle_of_compact_connected_planar_regular_level
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.isConnected_profileCap_left_cut
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.isCompact_roundedMeridian_zeroLevel
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.fderiv_roundedMeridianDefining_ne_zero
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.isConnected_mergedMeridianCurve
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedMeridian_zeroLevel_eq_mergedCurve
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_smooth_rounded_meridian_circle
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_roundedPairBody_elliptical_axis_tube
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_filled_rounded_meridian_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.isConnected_roundedMeridian_zeroLevel_upper
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedMeridianDefining_axis_zero_iff
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedMeridianDefining_axis_nonpos_iff
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.upperMeridianDefining_zero_iff
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.fderiv_upperMeridianDefining_ne_zero
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_filled_upper_meridian_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_upper_meridian_compression
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_upward_height_diffeomorph
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.inwardMeridianCompression
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_inward_upper_meridian_compression
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_compressed_upper_meridian_matching_region
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_supported_compressed_upper_meridian_matching
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.image_upper_meridian_of_compressed_matching
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_upper_meridian_normalization
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_supported_compressed_upper_meridian_isotopy
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_upper_meridian_normalizing_isotopy
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.contDiff_rotationalLift_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_rotated_pair_surface_normalization
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_filled_rounded_pair
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.roundedPairBody_frontier
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_relative_upper_pair_normalization
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_relative_transported_upper_pair_normalization
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.rotationalPlaneMap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.calibratedRotation_family_smooth
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_equator_fixed_upper_pair_replacement
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.endpoint_circle_of_equator_fixed_upper_replacement
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.PairUpper.exists_transported_upper_pair_replacement_with_endpoint

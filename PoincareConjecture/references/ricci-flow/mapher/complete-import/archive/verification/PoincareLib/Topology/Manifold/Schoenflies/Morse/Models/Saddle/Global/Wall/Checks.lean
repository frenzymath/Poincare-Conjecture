import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Certificate
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.SurfaceChart
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.ActualCorner
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Disk
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.ProfileCap
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.PlanarPair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.ProfilePair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.LocalAttachment
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.LocalNesting
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.CapAgreement.Upper
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.CapAgreement.Continued
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.CapAgreement.TerminalLower
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Collar.Common.Matching
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Collar.Common.RadialField
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.UnionFrontier
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Correction.PrescribedFrontier
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.SlabAttachment
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.ClosedSides
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.JoinedWidth
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.WeightedEnergy
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.PlaneLift
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.BodyTransport
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.ProtectedEnergy
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.WallDisk.PhysicalProtected
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Transport.NeckMark
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Transport.Gap.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.RelativePair.Protected.InteriorBall
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.TerminalComparison.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.TerminalComparison.Surface.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.TerminalComparison.Surface.ComparisonChecks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.TerminalSurface.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Transport.Pair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.RelativePair.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.RelativePair.Protected.Disjoint
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.ProfileSide
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.ProfileSideSetwise
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.ContinuedProfileSide
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.ConjugatedContinuation
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.MovingProfileSide
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.NormalizedPair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.AffineProfileSide
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.PlanarNormalization
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.RelativeSelectedPair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.SelectedNestedPair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.UpperEnd.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.MovingCollar.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.CappedDisjoint
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.BoundaryIntersection
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Placement.SelectedClassification
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.PairContact
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.PairEndpoint
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Placement.SelectedExterior
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Placement.SelectedCapPair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.PairCylinderChecks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Placement.Selected
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.ContactCollarChecks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.ContactSlices
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.WholeCap
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.SidePair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.ProfileCap
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.GraphMarking
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.ProfileMarking
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Touching
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.PrescribedCap
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Removal.Disk
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.ActualCut.Producer
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Nested.Actual
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Filling.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Filling.Side
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.Pair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Flattening.Normalization
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.ActualCut.Normalized
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Continuation.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Filling.Lower
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Filling.Upper
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.CorrectedSign
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Disjoint
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.CirclePair
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.RelativeGraph
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Nested
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Ribbon
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Square.Extension
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Square.Normalized
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Square.Rounded
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Square.Signed
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.CompactSign
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.StripAvoidance
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Surface
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Family
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Ball
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Critical
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.CriticalFamily
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Side.Filled
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Corner.Local
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.AttachmentGeometry
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Slices
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Collars
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.TailSplice
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Parameters
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Pasting.Family
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor.Source
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor.Labels
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Anchor.Terminal
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Ball
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Collar
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.UpperBelt
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Body
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Negative
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Negative.Annular
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Correction.Frontier
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Collar.Prescribed
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Collar.Marked
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Obstruction
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Boundary
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.GraphCorrection
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Attachment.Removal.Boundary
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Terminal
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.Side
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.UpperFilling
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Preparation.HeightCuts
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Side
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.Checks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Matching.ProfilePatch
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Nested.Vertical
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.PositiveAnchors
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.Reflection
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Arc.Separation.Orientation.EndSelection
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.ConstructionChecks
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Filling.ExtendedSide
import PoincareLib.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.ShearPair

#print axioms Poincare.Manifold.Schoenflies.Saddle.Global.Wall.exists_vertical_wall_arc_and_exterior_disks
#print axioms Poincare.Manifold.Schoenflies.Saddle.Global.Wall.frontier_range_of_smooth_embedding
#print axioms Poincare.Manifold.Schoenflies.Saddle.Global.Wall.frontier_union_eq_range_of_side_frontiers
#print axioms Poincare.Manifold.Schoenflies.Saddle.Global.Wall.frontier_union_eq_range_of_wall_interior
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Side.CircleFamily.exists_disk_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Side.exists_ambient_ball_of_disk_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Global.Wall.Side.Critical.leftZeroLevel_inter_wall
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Corner.straighten
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Corner.frontier_union_eq_side_frontiers_diff_wall
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Corner.side_frontier_not_subset_union_frontier
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Side.CircleFamily.not_both_corners_mem_leftZeroLevel
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Corner.frontier_union_inter_eq_of_corner_coordinates
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Corner.sphere_image_sdiff_closure_eq_of_body_agreement
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.exists_smooth_profile
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.exists_rounded_left_side
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.exists_physical_contact_threshold
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.exists_rounded_sides
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.sliceParam_isSmoothEmbedding
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.sliceAtHeight_image_range
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_fixed_strip_end_collars
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_actual_rounded_patch_splice
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Correction.diagonalProfileDiffeomorph
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Correction.diagonalGraph_eq_saddleGraph_of_le
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Correction.exists_supported_saddle_patch_correction
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Correction.exists_local_saddle_frontier_correction
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_negative_anchor_circles_of_first_pairing
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_strip_tail_parameter_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_separating_wall_of_disjoint_disks
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_separating_wall_or_nested_of_smooth_circles
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.not_separated_of_nested_disks
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_relative_separating_wall_of_graph_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.proper_wall_meets_exterior_of_nested_cut
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_vertical_wall_of_disjoint_ribbon
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.exists_ball_parametrization_with_transverse_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.exists_outward_field_of_compact_patch
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.exists_ball_parametrization_with_prescribed_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.exists_marked_ball_parametrization_with_prescribed_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_slab_attachment_with_graph
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_attachment_with_edge_germ
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_boundary_changing_perturbation
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.not_nonempty_attachmentData
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.frontier_eq_of_selected_graph_push
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_attachment_with_boundary
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_surface_graph_correction
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_ambient_ball_of_surface_graph_correction
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_removal_with_boundary
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Side.coordinate_bound_of_frontier_bound
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Side.filled_disks_inter_eq_boundary_inter_of_opposite_wall_sides
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_projected_strip_wall_clearance_of_flattened_cut
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_uniform_vertical_wall_of_disjoint_cut_circles
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_uniform_projected_fiber_morse_equation
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_signed_wall_of_disjoint_cut_circles
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.rounded_slice_coordinate_nonpositive
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.correctedStrip_zero_eq_of_fixed_level
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.coordinate_margin_of_boundary_range
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_rounded_anchor_circle_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_negative_anchor_source_circles_of_first_pairing
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_lower_end_ball_with_cylindrical_coordinates
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_upper_end_truncated_cap_decomposition
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split.wallSection_eq_radial_halfDisk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.roundedPatch_eq_actual_below
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.exists_actual_annular_collar_of_ambient_slices
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.exists_ambient_ball_of_attachment
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_ambient_ball_of_terminal_saddle_leaf_by_wall
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.terminal_wall_certificate_of_direct_pair_joining
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_terminal_wall_certificate

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for root in #[
      ``Poincare.Manifold.Schoenflies.SphereMorseReduction.terminal_wall_certificate_of_direct_pair_joining,
      ``Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_terminal_wall_certificate,
      ``Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_ambient_ball_of_terminal_saddle_leaf_by_wall] do
    unless (← collectAxioms root).all standard.contains do
      throwError "Nonstandard axioms in conditional wall composition {root}"
    let mut pending := #[root]
    let mut seen : NameSet := {}
    while !pending.isEmpty do
      let name := pending.back!
      pending := pending.pop
      if seen.contains name then continue
      seen := seen.insert name
      let some info := env.checked.get.find? name
        | throwError "Cannot inspect {name}"
      if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
        throwError "Admission reachable from {root}: {name}"
      pending := pending ++ info.getUsedConstantsAsSet.toArray
    logInfo m!"{root}: no reachable admissions; compatible joining remains an explicit hypothesis"

#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_terminal_wall_flattened_band
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_actual_saddle_graph_neighborhood
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_corrected_strip_signed_clearance_of_flattened_cut
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_actual_saddle_corner_chart
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_actual_local_corner_correction
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Corner.exists_dilation_image_subset
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_attachment_of_boundary_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_removal_of_boundary_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_actual_signed_wall_or_nested_with_corrected_clearance
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_compact_separator_scale_for_actual_nested_cut
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_ambient_lower_capped_side_ball
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split.exists_compatible_flat_marked_pair
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.exists_normalized_flattened_patch
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_normalized_actual_negative_anchors_with_clearance
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_canonically_closed_lower_end
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_canonically_closed_upper_end
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_normalized_saddle_chart
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.regular_on_strip_target
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_normalized_terminal_saddle_band
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_lower_end_containing_anchor
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_physical_lower_end_chart
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_terminal_rounded_side_with_lower_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.exists_vertical_compact_separator_of_nested_disks
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_extended_lower_capped_side_ball
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_filled_side_of_actual_negative_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_filled_side_of_actual_positive_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.range_eq_band_union_capped_ends
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.cap_centers_outside_interior_band
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.capped_ends_eq_physical_cuts
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.filled_side_boundary_inter_band
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_terminal_rounded_side_with_upper_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.eventually_circleFamily_range_iff_wall_of_profile
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_profile_cap_markings
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_profile_cap_pair
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_supported_touching_disk_pair_isotopy
#print axioms Poincare.Manifold.Schoenflies.SphereMorseReduction.exists_terminal_synchronized_rounded_sides
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.exists_common_filled_neighborhood_of_arc
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.eventually_range_iff_graph_of_graph_image_subset
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.exists_profile_cap_common_filled_neighborhood
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.exists_graph_arc_marking
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.exists_profile_cap_common_markings
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation.exists_touching_fillings_of_synchronized_profiles
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_lower_side_ball_with_prescribed_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_actual_profile_cap_pair_isotopy
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.profilePlanarDiffeomorph_neg_closedBall
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.isPreconnected_sphere_sdiff_marked_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.filled_intersection_of_common_boundary_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.filled_intersection_of_local_contact
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_attachment_of_local_boundary_contact
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_actual_profile_cap_pair_isotopy_of_exterior_rays
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_relative_canonical_cap_replacement_of_cylindrical_coordinates
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.exists_profile_pair_fixed_contact_slices
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.coordinate_bound_of_boundary_slice
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.intersection_in_slab_subset_boundaries
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_rounded_attachment_of_opposite_boundary_slabs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_lower_side_ball_with_profile_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.exists_physical_relative_cap_replacement
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation.exists_selected_disk_families_with_exterior_rays_or_nested
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.weightedWallDisk_injective_fderiv
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_smooth_wall_disk_of_width_profile
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_smooth_wall_disk_of_height_profile
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_smooth_joined_wall_disk
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation.exists_selected_cap_pair_matching_or_nested
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Arc.Separation.Orientation.exists_selected_cap_pair_matching_or_positive_nesting
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.disjoint_actual_lower_capped_images
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.closed_side_boundaries_intersection
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.height_band_intersection
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_lower_side_ball_of_setwise_profile_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Matching.cylindrical_profile_cap_pair_intersections
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_common_disk_of_profile_closed_sides
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_continued_lower_side_with_profile_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.continued_bands_wall_intersection
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.conjugatedUpperContinuation_properties
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_lower_side_ball_with_moving_profile_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_normalized_lower_side_with_profile_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.continued_band_lower_section
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.continued_band_upper_section
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.rescaled_upper_cap_lower_section
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_profile_closed_pair
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.commonWallNormalizer_height
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.normalized_circles_wall_contact
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_closed_pair_of_selected_planar_matching
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_closed_pair_of_relative_selected_sides
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.filled_subset_of_common_disk_and_one_interior_point
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.filled_regions_of_piecewise_upper_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_normalized_lower_side_with_affine_profile_cap
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_common_disk_and_containment_of_nested_closed_sides
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_nested_profile_closed_pair
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Preparation.exists_actual_nested_pair_of_selected_planar_matching
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.filled_band_of_cylindrical_boundary
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.actual_filled_sections_of_disk_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_actual_filled_disk_family
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.actual_filled_sections_of_continued_side
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Correction.exists_prescribed_saddle_frontier_correction
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.frontier_removal_away_common_boundary
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.sphere_of_rounded_union_away_contact
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.sphere_of_rounded_removal_away_contact
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.sphere_of_rounded_pair_below_band
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.frontier_symmetricProfileBody
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.symmetricProfileBody_frontier_wall
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.rounded_pair_eq_terminal_sphere_below
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.exists_marked_ball_parametrization_with_prescribed_collar_radius
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.Common.exists_common_marked_collar_parametrizations
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.Common.exists_relative_ball_matching_of_shared_boundary_patch
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.Common.normal_derivative_pos_of_local_inward
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.Common.radialField_outward_of_common_germs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.Common.exists_common_collar_of_shared_body_germs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Collar.Common.exists_relative_ball_matching_of_shared_body_germs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_exact_wall_energy_collar
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_exact_wall_energy_matching
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_matching_of_weighted_wall_energies
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_positive_wall_radius_factor_near_interval
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_exact_wall_energy_matching_with_fixed_germs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_matching_of_physical_wall_energies
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.wallPlaneLift_profile_germs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_matching_of_physical_wall_profiles
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.wallPlaneLift_subgraph_image_germ
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_weighted_wall_energy_matching_fixing_compact
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.exists_disjoint_pair_matching_after_ambient_transport
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.RelativePair.exists_protected_matching_of_disjoint_pair_germs
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.exists_physical_wall_energy_matching_with_prescribed_patch
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.RelativePair.exists_local_correction_fixing_marked_ball
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.RelativePair.exists_outer_matching_fixing_auxiliary_ball
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.filled_union_of_protected_added_part
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.circularProfileMark_injective_fderiv
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.circularProfileMark_subset_sphere
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.inserted_neck_left_trace_subset_mark
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.inserted_neck_right_trace_subset_mark
#print axioms Poincare.Manifold.Schoenflies.Saddle.Wall.Attachment.Transport.exists_neck_mark_radii

import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.SourceMeridianBoundaryData
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.CommensurablePlanarPair
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.PositionedFailureExclusion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.SourceMeridianBandDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Disks.OriginalSlabCompressionAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.OriginalLowerPhaseIncompressible
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.OriginalIncompressiblePhaseProducts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.OriginalIrreducibleSlab
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.OriginalPhaseGroups
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.OriginalFiberwisePhaseProducts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.MinimalFiberwisePhaseProducts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.RetainedSlab
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.CollaredRegion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.PointedFiberTails
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.BoundaryCoverLocalGeometry
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Paths.EmbeddedConcatenation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Paths.PLConcatenation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.FrontierComponents.ComponentCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.FrontierComponents.RestrictedPhaseCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Orientation.LocalProjection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.ExtendedFailureArc
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.OrientationTransport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.BoundaryComponentObstruction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.ComponentBoundaryGroups
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.SelectedComponentBoundaries
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.SourceBoundaryAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.NonfoldedFaces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.FirstRectangleFaces
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.TerminalCoordinatePL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.TerminalLocalGeometry
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.TerminalLocalGluing
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.DiskBoundaryReflection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.SourceTerminalCoverings
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.TerminalSourceBalls
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.TerminalBallHomotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.FiniteCellGluing
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.LocalRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.TerminalTargetCells
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.SourceTerminalBallPasting
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.ComplementaryRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.FirstSlabRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.FirstSlabDiskAlternatives
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.InstalledFirstSlabDiskAlternatives
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.FirstSlabAlternativeRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Regluing.SquareMapRigidityAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.OriginalAnnulusCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.TorusBandAnnulus
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.CoordinateGenerator
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.SwappedSquareMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.SourceAnnularMark
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.SignedAnnularDegree
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.CommensurableAnnularMark
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.TerminalAnnularMark
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.OriginalAnnularDegree
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.IteratedCoreDegree
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Original.SurfaceStraightening
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Original.SurfaceTrack
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.FinitePL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.RectangleIsotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.Twist
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.DiskReplacement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.Lift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.Contacts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.Excursion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Bigons.DiskMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Disks.SupportedExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.OriginalExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.CutEndpoint
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.TerminalLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.RadialAlignment
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.HighestAxis
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.PeriodicReduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.SignedReduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.NoContacts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.ContactReflection
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.RadialIsotopy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.ZeroWindingEndpoint
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.WindingInvariance
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.ProjectedDiskMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Annuli.PhaseContactTransfer
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.OriginalRegionMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.OriginalAnnularMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.AnnularStraightening
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.CoordinateSpanningAnnuli
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Intersections.SingleSpanningComponent
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.CoordinateComplementDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.SpanningCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Collars.CoordinateAnnuliComplement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.RelativePredicateClauses
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.ContactInduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Arcs.MovedGeometry
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Bigons.ResidualMotion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Bigons.FlattenedTube
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.Isotopy.Bigons.ShiftedDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Cancellation.ProductFailureExclusion
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.LocalPLInvariance
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.SimultaneousTerminalGroups
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.SourceDiskFamilyInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.TerminalDiskInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.Boundary.SquareExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.DiskFamilyAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.SourceDiskAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.SimultaneousTerminalDiskInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.ResidualComponents
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.DiskFailureArc
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Maps.Boundary.RetainedRectangleEdges
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FoldedFailureArc
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FailureArcBoundaryGroups
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FailureArcRegionGroups
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FailureArcBoundaryCover
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.InstalledFailureArcCover
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.BoundaryLoopPowers
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.CircleInjectivity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.OneSheet.OriginalAtlas
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Maps.Adjustments.Tangential
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.LinearTorus.IntegerMatrix
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.LinearTorus.InjectiveFundamentalGroup
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.LinearTorus.HomotopyToCovering
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.Translations.DisplacementLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.General.IndexTwoRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Maps.Adjustments.PhaseMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.ParametrizedSurface
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.Phase.FiniteComponents
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coverings.LinearTorus.OriginalTargetPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SecondCoordinateBoundaryLifts
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.PhaseCoveringInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.FiniteMarkedSurface
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.BoundaryLevelNonempty
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Collars.Bicollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.RelativeCut
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.Reduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.EulerChange
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.ProtectedCollar
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.MarkedSurfaceResidualCount
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.MinimalLower
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.Upper.Reduction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.RegularResidualModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Collars.RimRestriction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.ResidualModelInvariance
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SourceIncompressiblePhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.InstalledBoundaryHierarchy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.TwoPhaseCoveringInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.DisjointPhaseCollars
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.PhaseBoundaryGeometry
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.CyclicSurfaceEulerCount
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SquareSecondHierarchy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.CyclicTwoBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.MarkedCircleModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.RetainedRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Spheres.SupportedBall
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Spheres.ClosedComponent
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SourceComponentPhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.ComponentCircleRims
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.CompressedCircleModel
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.CyclicBoundaryAnnulus
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Spheres.SlabExcision
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Spheres.BoundaryArcBall
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.SquareAnnulusHierarchy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.WholeComponentFamily
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.ComponentRim
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.CylinderLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.LiftedRimPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.MarkedCoveringPL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.MarkedStraightening
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.SourceRimLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Coverings.SourceRimExtension
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FoldedContraction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.NormalizedMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.SourceAnnulusInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.SourceAnnulusDisplacement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.NormalDisplacementBound
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.RetainedArcDisplacement
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.SourceFamilyInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.RetainedSourceAnnulusInstallation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.FinitePhaseCovering
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.LatticeRigidity
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.ThirdPhaseDisk
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.ThirdPhaseAlternative
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.RegularThirdCoordinate
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Compression.PhaseMap
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.SourceComponentPhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Compression.MinimalLower
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.InstalledSecondSlabHierarchy
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Spheres.OriginalArcRemoval
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Spheres.PhaseRemoval
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Spheres.ClosedComponent
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Spheres.ConnectedCover
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.Spheres.MinimalRemoval
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Disks.IrreducibleSlabs
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Regions.IrreducibleSphericalBoundaryBall
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.NonemptyCoveringBranch
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Maps.TargetCoordinates
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Polyhedra.Mathlib.LocallyInjectivePLLift
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Models.Orientation.SimultaneousChartStars
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.IncompressiblePhases
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Compression.Complement.Endpoint
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Coordinates.PeriodicSquare
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualEdges
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPairedCycles
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusBoundaryInventory
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPrimalContraction
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualWordSupport
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualOrientation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusResidualLabelOrder
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusContractedBoundary
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusPeriodicSquareBoundary
import Lean.Util.CollectAxioms

/-! Recursive admission audit for the constructed source meridian disks,
both slab-side disk alternatives, and compression into both closed sides. -/

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let roots := #[
    ``PoincareMT.M76.LinearTorus.surjective_of_homotopy_id,
    ``PoincareMT.M76.surjective_hamiltonZero_first_second_coordinates,
    ``PoincareMT.M76.exists_hamiltonZero_covering_annulus_of_complete_phase,
    ``PoincareMT.M76.exists_hamiltonZero_third_phase_disk,
    ``PoincareMT.M76.exists_hamiltonZero_third_phase_disk_or_interior_ball,
    ``PoincareMT.M76.exists_hamiltonZero_third_coordinate_finite_regular_values,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_third_scalar_homotopy,
    ``PoincareMT.M76.exists_hamiltonZero_third_coordinate_compression_map,
    ``PoincareMT.M76.exists_hamiltonZero_lower_third_phase_kernel_control,
    ``PoincareMT.M76.exists_hamiltonZero_both_third_phase_kernel_control,
    ``PoincareMT.M76.exists_hamiltonZero_complementary_third_phase_kernel_control,
    ``PoincareMT.M76.marked_phase_pi1_injective_of_kernel_control,
    ``PoincareMT.M76.exists_hamiltonZero_complementary_third_phases_injective,
    ``PoincareMT.M76.exists_hamiltonZero_complementary_third_slabs,
    ``PoincareMT.M76.exists_hamiltonZero_third_whole_component_alternatives,
    ``PoincareMT.M76.exists_hamiltonZero_incompressible_third_hierarchy,
    ``PoincareMT.M76.exists_hamiltonZero_third_component_hierarchy,
    ``PoincareMT.M76.exists_hamiltonZero_boundary_meeting_third_hierarchy,
    ``PoincareMT.M76.exists_hamiltonZero_terminal_third_disk_families,
    ``PoincareMT.M76.exists_hamiltonZero_source_simultaneous_terminal_hierarchies,
    ``PoincareMT.M76.exists_hamiltonZero_source_simultaneous_terminal_trivial_groups,
    ``PoincareMT.M76.hamiltonZero_third_slabs_pi1_injective,
    ``PoincareMT.M76.hamiltonZero_box_pi1_subsingleton,
    ``PoincareMT.M76.hamiltonZero_terminal_third_slabs_pi1_subsingleton,
    ``PoincareMT.M76.exists_hamiltonZero_source_disk_rectangular_normal_form,
    ``PoincareMT.M76.exists_hamiltonZero_retained_source_disk_installation,
    ``PoincareMT.M76.exists_hamiltonZero_source_disk_family_installation,
    ``PoincareMT.M76.exists_hamiltonZero_source_terminal_disk_installation,
    ``PoincareMT.M76.exists_finitePL_square_extension_of_injective_rim,
    ``PoincareMT.M76.exists_hamiltonZero_source_disk_homeomorphic_normal_form,
    ``PoincareMT.M76.exists_hamiltonZero_homeomorphic_disk_family_installation,
    ``PoincareMT.M76.exists_hamiltonZero_disk_failure_arc_of_not_injective_rim,
    ``PoincareMT.M76.exists_hamiltonZero_disk_family_homeomorphic_or_failure_arc,
    ``PoincareMT.M76.exists_hamiltonZero_source_simultaneous_terminal_disk_installation,
    ``PoincareMT.M76.FrontierResidualModel.isCoveringMap_component,
    ``PoincareMT.M76.exists_unit_square_proper_PL_arc,
    ``PoincareMT.M76.exists_hamiltonZero_rectangular_path_contraction,
    ``PoincareMT.M76.exists_hamiltonZero_source_disk_failure_arc,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_normal_form_with_failure_arc,
    ``PoincareMT.M76.hamiltonZero_failure_arc_not_boundary_homotopic,
    ``IsCoveringMap.fundamentalGroup_range_finiteIndex_of_finite_fiber,
    ``IsCoveringMap.fundamentalGroup_range_finiteIndex_of_compact,
    ``PoincareMT.M76.hamiltonZero_boundary_groups_commensurable_of_failure_arc,
    ``PoincareMT.M76.hamiltonZero_region_boundary_groups_commensurable_of_failure_arc,
    ``IsCoveringMap.pullback_fst,
    ``PoincareMT.M76.boundaryCoverDiagonal_connectedComponent,
    ``PoincareMT.M76.exists_failure_arc_in_boundary_cover,
    ``PoincareMT.M76.HamiltonZeroSecondPhaseGeometry.frontier_rectangle_edges,
    ``PoincareMT.M76.hamiltonZero_retained_third_disk_rim_rectangle_edges,
    ``PoincareMT.M76.FrontierResidualModel.count_eq_of_same_surface,
    ``PoincareMT.M76.exists_hamiltonZero_minimal_incompressible_phase_count,
    ``PoincareMT.M76.exists_hamiltonZero_minimal_fiberwise_phase_products,
    ``AddCircle.surjective_of_continuous_injective,
    ``PoincareMT.M76.exists_hamiltonZero_source_second_slabs_third_hierarchies,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_supported_ball_third_phase_homotopy,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_original_ball_third_arc_removal,
    ``PoincareMT.M76.exists_hamiltonZero_closed_third_component_sphere,
    ``PoincareMT.M76.exists_hamiltonZero_closed_third_component_boundary_arc_ball,
    ``PoincareMT.M76.exists_hamiltonZero_closed_third_component_removal,
    ``PoincareMT.M76.exists_hamiltonZero_compressed_third_paired_phase_connected_cover,
    ``PoincareMT.M76.exists_hamiltonZero_third_phases_without_closed_components,
    ``PoincareMT.M76.isPLIrreducible_hamiltonZero_complementary_third_slabs,
    ``PoincareMT.M76.IsPLIrreducible.nonempty_ball_of_spherical_frontier,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_normal_form_with_PL_arcs,
    ``PoincareMT.M76.hamiltonZero_installed_second_slabs_pi1_injective,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_normal_form,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_normal_displacement,
    ``PoincareMT.M76.exists_original_retained_annulus_displacement_extension_within,
    ``PoincareMT.M76.exists_original_finite_annulus_displacement_extension,
    ``PoincareMT.M76.exists_hamiltonZero_retained_source_annulus_installation,
    ``PoincareMT.M76.exists_hamiltonZero_finite_marked_annulus_installation,
    ``PoincareMT.M76.exists_hamiltonZero_terminal_annulus_installation,
    ``PoincareMT.M76.HamiltonZeroSecondPhaseGeometry.of_secondCircleMap_eq,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_family_installation,
    ``PoincareMT.M76.exists_hamiltonZero_phase_covering_of_finite_annuli,
    ``PoincareMT.M76.exists_indexOne_lattice_rigidity,
    ``PoincareMT.M76.exists_hamiltonZero_retained_arc_displacement,
    ``PoincareMT.M76.exists_source_standard_meridian_boundary_data,
    ``PoincareMT.M76.exists_source_standard_meridian_marked_disk,
    ``PoincareMT.M76.exists_source_meridian_open_band_disk,
    ``PoincareMT.M76.injective_or_exists_marked_proper_disk,
    ``PoincareMT.M76.exists_hamiltonZero_slab_proper_disk_alternative,
    ``PoincareMT.M76.exists_hamiltonZero_physical_compression_alternative,
    ``PoincareMT.M76.residualComplexity_decreases_of_euler_change,
    ``PoincareMT.M76.PLDomain.nonempty_frontier_residual_model,
    ``PoincareMT.M76.OriginalDiskProduct.frontierResidualModel_complexity_decreases,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_residual_decrease,
    ``PoincareMT.M76.exists_hamiltonZero_incompressible_lower_slab,
    ``PoincareMT.M76.exists_hamiltonZero_both_sides_incompressible_slab,
    ``PoincareMT.M76.exists_hamiltonZero_incompressible_phase_products,
    ``PoincareMT.M76.exists_hamiltonZero_nonspherical_incompressible_slab,
    ``PoincareMT.M76.exists_hamiltonZero_nontrivial_incompressible_frontier,
    ``PoincareMT.M76.exists_hamiltonZero_irreducible_incompressible_slab,
    ``PoincareMT.M76.exists_hamiltonZero_injective_phase_maps,
    ``PoincareMT.M76.exists_hamiltonZero_fiberwise_phase_products,
    ``PoincareMT.M76.exists_lattice_handle_rigidity_of_covering,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_tangential_homotopy,
    ``PoincareMT.M76.LinearTorus.isCoveringMap_integerMatrixMap,
    ``PoincareMT.M76.LinearTorus.det_ne_zero_of_fundamentalGroup_map_injective,
    ``PoincareMT.M76.LinearTorus.det_ne_zero_of_affine_fundamentalGroup_map_injective,
    ``PoincareMT.M76.LinearTorus.exists_homotopy_affine_covering,
    ``PoincareMT.M76.StandardLatticeHandleAtlas.finitePiecewiseAffineOn_displacement,
    ``PoincareMT.M76.exists_supported_original_collar_displacement,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_collar_phase_adjustment,
    ``PoincareMT.M76.exists_parametrized_torus_covering,
    ``PoincareMT.M76.PhaseCovering.exists_coveringMap_with_component_formulas,
    ``PoincareMT.M76.StandardLatticeHandleAtlas.polyhedralPL_hamiltonZeroTargetAffine,
    ``PoincareMT.M76.exists_hamiltonZero_second_coordinate_boundary_lift,
    ``PoincareMT.M76.exists_hamiltonZero_recognized_phase_covering,
    ``Geometry.PolyhedralPLInCharts.exists_image_of_finitePL_embedding,
    ``PoincareMT.M76.PeriodicSquare.polyhedralPL_descent,
    ``PoincareMT.M76.exists_PL_torus_parametrization_of_square_map,
    ``PoincareMT.M76.exists_hamiltonZero_phase_covering_of_square_maps,
    ``PoincareMT.M76.exists_hamiltonZero_second_coordinate_slab,
    ``PoincareMT.M76.finitePiecewiseAffineOn_hamiltonZero_second_coordinate_lift,
    ``PoincareMT.M76.finitePiecewiseAffineOn_hamiltonZeroSecondSlabHeight,
    ``PoincareMT.M76.exists_hamiltonZero_second_surface_relative_bicollar,
    ``PoincareMT.M76.exists_hamiltonZero_second_slab_compression_disks,
    ``PoincareMT.M76.hamiltonZero_second_slab_disk_alternative,
    ``PoincareMT.M76.exists_hamiltonZero_second_slab_relative_compression,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_second_coordinate_homotopy,
    ``PoincareMT.M76.exists_hamiltonZero_shifted_lower_second_slab_coordinate,
    ``PoincareMT.M76.exists_hamiltonZero_second_coordinate_compression_map,
    ``PoincareMT.M76.exists_hamiltonZero_lower_second_slab_map,
    ``PoincareMT.M76.exists_hamiltonZero_second_phase_finite_model,
    ``PoincareMT.M76.exists_hamiltonZero_second_compression_euler_change,
    ``PoincareMT.M76.exists_hamiltonZero_second_slab_reduction,
    ``PoincareMT.M76.hamiltonZero_second_slab_reduction,
    ``Poincare.Topology.exists_bicollar_fixed_by_supported_homotopy,
    ``PoincareMT.M76.exists_original_marked_surface_finite_incidence,
    ``PoincareMT.M76.nonempty_residual_model_of_compact_marked_surface,
    ``PoincareMT.M76.HamiltonZeroSecondCoordinateRegularity.nonempty_residual_model,
    ``PoincareMT.M76.FrontierResidualModel.complexity_eq_of_same_surface,
    ``PoincareMT.M76.marked_surface_charts_after_interior_change,
    ``PoincareMT.M76.OriginalDiskProduct.marked_frontier_cut,
    ``PoincareMT.M76.OriginalDiskProduct.marked_face_residual_complexity_decreases,
    ``PoincareMT.M76.hamiltonZero_upper_second_slab_reduction,
    ``PoincareMT.M76.exists_hamiltonZero_lower_second_phase_kernel_control,
    ``Poincare.Topology.exists_collar_interior_push,
    ``Poincare.Topology.fundamentalGroup_collar_rim_complement_surjective,
    ``Poincare.Topology.exists_phase_rim_collar,
    ``Poincare.Topology.fundamentalGroup_phase_rim_complement_surjective,
    ``Poincare.Topology.fundamentalGroup_map_injective_of_collar_kernel_control,
    ``Poincare.Topology.exists_phase_constant_bicollar_of_eq_off_compact,
    ``Poincare.Topology.fundamentalGroup_whole_phase_injective_of_kernel_control,
    ``PoincareMT.M76.exists_hamiltonZero_both_second_phase_kernel_control,
    ``PoincareMT.M76.exists_hamiltonZero_second_slab_incompressible_phases,
    ``PoincareMT.M76.exists_hamiltonZero_second_slab_marked_corner_of_supported_map,
    ``PoincareMT.M76.hamiltonZero_complementary_second_slab_of_supported_cut,
    ``PoincareMT.M76.exists_hamiltonZero_complementary_second_phase_kernel_control,
    ``PoincareMT.M76.exists_hamiltonZero_complementary_second_phases_injective,
    ``PoincareMT.M76.exists_hamiltonZero_complementary_second_slabs,
    ``PoincareMT.M76.hamiltonZero_installed_second_boundary_levels_nonempty,
    ``PoincareMT.M76.exists_hamiltonZero_incompressible_second_hierarchy,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_two_covering_phase_adjustments,
    ``PoincareMT.M76.exists_hamiltonZero_two_phase_coverings_of_square_maps,
    ``PoincareMT.M76.hamiltonZeroSecondPhaseCircleMap_pi1_injective,
    ``PoincareMT.M76.hamiltonZeroSecondPhaseCircleMap_pi1_injective_of_region,
    ``PoincareMT.M76.exists_hamiltonZero_injective_circle_second_hierarchy,
    ``PoincareMT.M76.exists_hamiltonZero_disjoint_boundary_bicollar,
    ``PoincareMT.M76.exists_hamiltonZero_injective_circle_hierarchy_of_disjoint_boundary,
    ``PoincareMT.M76.exists_disjoint_inward_phase_collar_radius,
    ``PoincareMT.M76.hamiltonZero_phase_boundary_geometry,
    ``Geometry.SimplicialComplex.surfaceEulerCount_nonneg_of_isCyclic,
    ``PoincareMT.M76.exists_hamiltonZero_second_hierarchy_of_square_maps,
    ``PoincareMT.M76.surfaceEulerCount_nonpos_of_two_boundaries,
    ``PoincareMT.M76.exists_annulus_of_isCyclic_and_two_boundaries,
    ``PoincareMT.M76.boundary_circle_count_le_two_of_isCyclic,
    ``PoincareMT.M76.exists_original_marked_surface_circle_incidence,
    ``PoincareMT.M76.hamiltonZero_installed_boundary_rim_circle_covering,
    ``PoincareMT.M76.nontrivial_hamiltonZero_boundary_rim_group,
    ``PoincareMT.M76.hamiltonZero_boundary_rim_covering_of_supported_map,
    ``PoincareMT.M76.exists_nontrivial_hamiltonZero_retained_phase_component,
    ``PoincareMT.M76.nontrivial_hamiltonZero_retained_rim_connectedComponent,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_supported_ball_second_displacement,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_supported_ball_second_phase_homotopy,
    ``PoincareMT.M76.exists_hamiltonZero_closed_second_component_sphere,
    ``PoincareMT.M76.exists_hamiltonZero_second_hierarchy_component_alternatives,
    ``Geometry.SimplicialComplex.exists_component_circle_rims,
    ``PoincareMT.M76.exists_hamiltonZero_compressed_circle_incidence,
    ``PoincareMT.M76.isFinitePLBallPair_of_isCyclic_and_one_oriented_boundary,
    ``PoincareMT.M76.boundary_circle_count_eq_two_of_nontrivial_isCyclic_and_geometric_signs,
    ``PoincareMT.M76.exists_marked_annulus_of_nontrivial_isCyclic_and_geometric_signs,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_original_ball_arc_removal,
    ``PoincareMT.M76.plDomains_hamiltonZero_second_slabs_of_supported_phase_avoidance,
    ``PoincareMT.M76.exists_hamiltonZero_closed_second_component_boundary_arc_ball,
    ``PoincareMT.M76.exists_hamiltonZero_closed_second_component_removal,
    ``Geometry.SimplicialComplex.exists_finite_connected_cover_of_continuousOn_image,
    ``PoincareMT.M76.exists_hamiltonZero_compressed_paired_phase_connected_cover,
    ``PoincareMT.M76.exists_hamiltonZero_second_phases_without_closed_components,
    ``PoincareMT.M76.IsPLIrreducible.of_boundary_meeting_cut,
    ``PoincareMT.M76.isPLIrreducible_hamiltonZero_complementary_second_slabs,
    ``PoincareMT.M76.exists_hamiltonZero_boundary_meeting_second_hierarchy,
    ``PoincareMT.M76.exists_hamiltonZero_original_cyclic_marked_annulus,
    ``PoincareMT.M76.exists_hamiltonZero_compressed_component_annulus,
    ``PoincareMT.M76.exists_hamiltonZero_terminal_component_annuli,
    ``PoincareMT.M76.exists_hamiltonZero_compressed_whole_component_family,
    ``PoincareMT.M76.exists_hamiltonZero_terminal_finite_annulus_family,
    ``PoincareMT.M76.Dehn.isOpenEmbedding_componentAnnulusRim,
    ``PoincareMT.M76.Dehn.isCoveringMap_componentAnnulusRim,
    ``PoincareMT.M76.hamiltonZero_compressed_annulus_rim_circle_covering,
    ``IsCoveringMap.exists_cylinder_lift_homeomorph,
    ``IsCoveringMap.exists_addCircle_cylinder_lift_homeomorph,
    ``PoincareMT.M76.finitePiecewiseAffineOn_hamiltonZero_lifted_annulus_rims,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_rim_lift,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_rim_extension,
    ``PoincareMT.M76.Dehn.exists_annulus_homotopic_rim_extension,
    ``PoincareMT.M76.Dehn.exists_annulus_winding_correction,
    ``PoincareMT.M76.Dehn.exists_relative_annulus_covering_of_rim_extension,
    ``PoincareMT.M76.exists_hamiltonZero_marked_annulus_covering_PL,
    ``PoincareMT.M76.exists_hamiltonZero_oriented_marked_annulus_covering_PL,
    ``PoincareMT.M76.exists_hamiltonZero_annulus_marked_or_folded,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_marked_or_folded,
    ``PoincareMT.M76.exists_hamiltonZero_relative_annulus_displacement,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_displacement,
    ``PoincareMT.M76.exists_original_retained_annulus_displacement_extension,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_second_phase_adjustment,
    ``PoincareMT.M76.exists_hamiltonZero_marked_annulus_installation,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_installation,
    ``PoincareMT.M76.hamiltonZero_annulus_normal_displacement_bound,
    ``PoincareMT.M76.isCoveringMap_hamiltonZero_target_annulus,
    ``PoincareMT.M76.ChartwisePLMap.exists_hamiltonZero_folded_annulus_contraction,
    ``PoincareMT.M76.exists_hamiltonZero_source_annulus_components,
    ``PoincareMT.M76.exists_hamiltonZero_source_annuli_of_disjoint_boundary,
    ``PoincareMT.M76.exists_hamiltonZero_annulus_hierarchy_of_square_maps,
    ``Geometry.PolyhedralPLInCharts.exists_full_simultaneous_compatible_chart_stars,
    ``Geometry.SimplicialComplex.surfaceEulerCount_le_one_of_boundary_edge,
    ``Geometry.SimplicialComplex.exists_residual_count_of_marked_surface,
    ``Geometry.SimplicialComplex.exists_component_residual_counts_of_marked_surface,
    ``PoincareMT.M76.exists_hamiltonZero_regular_second_coordinate,
    ``PoincareMT.M76.exists_hamiltonZero_second_surface_finite_marked_model,
    ``PoincareMT.M76.hamiltonZero_second_boundary_level_nonempty,
    ``PoincareMT.M76.PLDomain.nonempty_original_finite_collar_model,
    ``PoincareMT.M76.exists_source_proper_meridian,
    ``PoincareMT.M76.exists_fixed_indexTwo_rigidity,
    ``PoincareMT.M76.exists_indexTwo_lattice_rigidity,
    ``PoincareMT.M76.PeriodicSquare.projection_eq_iff,
    ``PoincareMT.M76.PeriodicSquare.quotientHomeomorph,
    ``PoincareMT.M76.PeriodicSquare.exists_homeomorph_of_square_map,
    ``PoincareMT.M76.exists_original_torus_residual_edges,
    ``PoincareMT.M76.exists_original_torus_essential_polygon,
    ``PoincareMT.M76.exists_original_torus_two_paired_cycles,
    ``PoincareMT.M76.exists_original_torus_boundary_inventory,
    ``PoincareMT.M76.primalTreeContraction_eq_all,
    ``PoincareMT.M76.primalTreeContraction_eq_of_any_edge_endpoints,
    ``PoincareMT.M76.exists_paired_cycle_contracted_support,
    ``PoincareMT.M76.exists_residual_dart_endpoint_reversal,
    ``PoincareMT.M76.exists_residual_dart_orientation_data,
    ``PoincareMT.M76.residual_dart_orientation_endpoint_sets,
    ``PoincareMT.M76.contracted_boundary_side_endpoint_eq,
    ``PoincareMT.M76.PeriodicSquare.sidePoint_sidePair,
    ``PoincareMT.M76.PeriodicSquare.sidePoint_projection_eq_opposite,
    ``PoincareMT.M76.PeriodicSquare.sidePoint_projection_eq_opposite_residual,
    ``PoincareMT.M76.exists_hamiltonZero_source_disk_alternatives,
    ``PoincareMT.M76.FrontierResidualModel.exists_installed_failure_arc_cover,
    ``PoincareMT.M76.FrontierResidualModel.installed_boundary_component_of_collar,
    ``PoincareMT.M76.boundaryCoverFullDiagonalHomeomorph,
    ``PoincareMT.M76.boundaryCoverFullDiagonal_connectedComponent,
    ``PoincareMT.M76.exists_boundary_loop_power_homotopy,
    ``PoincareMT.M76.hamiltonZero_boundary_loop_power_homotopy_of_failure_arc,
    ``PoincareMT.M76.FrontierResidualModel.exists_retained_model_after_closed_excision,
    ``PoincareMT.M76.FrontierResidualModel.count_lt_of_component_deletion,
    ``PoincareMT.M76.FrontierResidualModel.nonspherical_of_component_deletion,
    ``PoincareMT.M76.FrontierResidualModel.nontrivial_groups_of_component_deletion,
    ``PoincareMT.M76.exists_hamiltonZero_closed_phase_pair_cancellation,
    ``PoincareMT.M76.exists_hamiltonZero_smaller_phase_count_of_closed_region,
    ``PoincareMT.M76.compact_signed_two_collar_enlargement,
    ``PoincareMT.M76.compact_phase_collar_enlargement,
    ``PoincareMT.M76.exists_hamiltonZero_smaller_phase_count_of_collared_region,
    ``PoincareMT.M76.exists_hamiltonZero_smaller_phase_count_of_complementary_collared_region,
    ``PoincareMT.M76.HamiltonZeroInstalledAnnulusPLArcFibers.exists_pointed_interior_tails,
    ``PoincareMT.M76.hamiltonZero_boundary_cover_plDomain,
    ``Path.isEmbedding_trans_trans_of_range_inter_subset,
    ``Path.range_inter_subset_endpoint_of_frontier,
    ``Geometry.PolyhedralPLInCharts.interval_concatenation,
    ``Geometry.intervalConcatenation_eq_path_trans,
    ``PoincareMT.M76.signed_collar_side_on_connectedComponentIn,
    ``PoincareMT.M76.PLDomain.restrict_phase_collar_to_component,
    ``PoincareMT.M76.exists_hamiltonZero_local_projection_atlas_labels,
    ``PoincareMT.M76.exists_hamiltonZero_extended_second_slab_disk_failure_arc,
    ``Geometry.OriginalPLTower.MarkedTerminalRegion.exists_hamiltonZero_boundary_signs,
    ``PoincareMT.M76.hamiltonZero_component_frontier_not_subset_single_phase,
    ``PoincareMT.M76.hamiltonZero_component_has_other_boundary_phase,
    ``PoincareMT.M76.hamiltonZero_installed_component_boundary_groups,
    ``PoincareMT.M76.IsPLIrreducible.connectedComponentIn,
    ``PoincareMT.M76.exists_hamiltonZero_selected_component_boundaries,
    ``PoincareMT.M76.exists_hamiltonZero_source_boundary_disk_alternative,
    ``PoincareMT.M76.HamiltonZeroHomeomorphicDiskInstallation.opposite_labels_of_terminal_family,
    ``PoincareMT.M76.exists_hamiltonZero_original_annulus_rectangle_faces,
    ``PoincareMT.M76.exists_hamiltonZero_installed_first_rectangle_faces,
    ``PoincareMT.M76.exists_hamiltonZero_second_slab_terminal_boundary_map,
    ``PoincareMT.M76.exists_hamiltonZero_finitePL_boundary_coordinates,
    ``PoincareMT.M76.HamiltonZeroSourceBoundaryDiskData.exists_terminal_face_endpoints,
    ``PoincareMT.M76.isLocallyInjective_of_finite_saturated_closed_faces,
    ``PoincareMT.M76.hamiltonZero_disk_rectangle_target_edges_iff,
    ``Geometry.LocallyPiecewiseAffineOn.isLocalHomeomorphOn_of_locallyInjective,
    ``PoincareMT.M76.not_hamiltonZero_boundary_failure_of_component_products,
    ``PoincareMT.M76.hamiltonZero_terminal_frontier_union_locally_injective,
    ``PoincareMT.M76.hamiltonZero_second_slab_frontier_locally_injective,
    ``PoincareMT.M76.HamiltonZeroSourceBoundaryDiskData.exists_locally_injective_terminal_endpoints,
    ``PoincareMT.M76.plDomain_terminalBox,
    ``PoincareMT.M76.isLocalHomeomorph_frontier_of_polyhedral_model,
    ``PoincareMT.M76.isCoveringMap_hamiltonZero_terminal_boundary,
    ``PoincareMT.M76.exists_hamiltonZero_terminal_spherical_frontier,
    ``PoincareMT.M76.HamiltonZeroSourceBoundaryDiskData.exists_terminal_spherical_coverings,
    ``PoincareMT.M76.IsPLIrreducible.nonempty_ball_of_spherical_boundary_component,
    ``PoincareMT.M76.exists_hamiltonZero_terminal_source_balls,
    ``PoincareMT.M76.ChartwisePLBall.exists_terminalBox_extension,
    ``PoincareMT.M76.ChartwisePLBall.exists_terminalBox_relative_replacement,
    ``PoincareMT.M76.isLocallyInjective_of_finite_marked_cells,
    ``PoincareMT.M76.ChartwisePLMap.isLocalHomeomorph_of_open,
    ``PoincareMT.M76.exists_hamiltonZero_rigidity_of_locallyInjective,
    ``PoincareMT.M76.hamiltonZero_terminal_target_cell_projected_frontier,
    ``PoincareMT.M76.hamiltonZero_terminal_target_cells_inter_frontier,
    ``PoincareMT.M76.hamiltonZero_terminal_target_cells_disjoint_interiors,
    ``PoincareMT.M76.ChartwisePLMap.mem_interior_image_of_locallyInjective,
    ``PoincareMT.M76.ChartwisePLMap.restrict_compact_domain,
    ``PoincareMT.M76.ChartwisePLMap.closed_paste,
    ``PoincareMT.M76.exists_finite_originalPL_relative_pasting,
    ``PoincareMT.M76.HamiltonZeroTerminalSphericalCover.exists_ball_map_family,
    ``PoincareMT.M76.HamiltonZeroSourceBoundaryDiskData.exists_terminal_ball_maps,
    ``PoincareMT.M76.HamiltonZeroTerminalBallMapFamily.exists_paired_components,
    ``PoincareMT.M76.HamiltonZeroTerminalBallMapFamily.exists_relative_pasting,
    ``PoincareMT.M76.HamiltonZeroSourceBoundaryDiskData.exists_pasted_terminal_balls,
    ``PoincareMT.M76.hamiltonZero_locally_injective_of_complementary_slabs,
    ``PoincareMT.M76.exists_hamiltonZero_rigidity_of_complementary_endpoints,
    ``PoincareMT.M76.exists_hamiltonZero_rigidity_of_first_slab_endpoints,
    ``PoincareMT.M76.exists_hamiltonZero_first_boundary_collars,
    ``PoincareMT.M76.exists_hamiltonZero_first_slab_disk_alternatives,
    ``PoincareMT.M76.HamiltonZeroPastedTerminalBalls.exists_locally_injective_endpoint,
    ``PoincareMT.M76.exists_hamiltonZero_paired_slab_rigid_map,
    ``PoincareMT.M76.HamiltonZeroSourceBoundaryDiskData.exists_relative_locally_injective_map,
    ``PoincareMT.M76.exists_hamiltonZero_rigidity_or_first_boundary_failure,
    ``PoincareMT.M76.exists_hamiltonZero_first_slab_disk_alternatives_of_installed_coverings,
    ``PoincareMT.M76.exists_hamiltonZero_rigidity_or_boundary_failure_of_square_maps,
    ``PoincareMT.M76.LinearTorus.isEmbedding_primitiveTorusBand,
    ``PoincareMT.M76.LinearTorus.primitiveTorusBand_inner_mem_nhds,
    ``PoincareMT.M76.LinearTorus.finitePiecewiseAffineOn_primitiveTorusBandLift,
    ``PoincareMT.M76.LinearTorus.primitive_periodLoop_not_isOfFinOrder,
    ``PoincareMT.M76.band_center_periodLoop_not_isOfFinOrder,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_coordinate_band,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_coordinate_bands,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_finitePL_coordinate_annulus,
    ``PoincareMT.M76.Dehn.exists_essential_polygon_signed_radial_lift,
    ``PoincareMT.M76.Dehn.exists_finitePL_essential_annulus_core_homotopy,
    ``PoincareMT.M76.Dehn.exists_originalPL_annulus_core_homotopy,
    ``PoincareMT.M76.Dehn.exists_originalPL_annular_mark_core_homotopy,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_coordinate_annulus,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_annular_mark,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_annular_marks,
    ``PoincareMT.M76.PeriodicSquare.sourceAnnularCore_periodLoop_not_isOfFinOrder,
    ``PoincareMT.M76.Dehn.exists_finitePL_essential_annulus_signed_radial_lift,
    ``PoincareMT.M76.Dehn.finitePL_essential_annulus_positive_degree_eq_one,
    ``FundamentalGroup.index_range_map_eq_of_path,
    ``FundamentalGroup.finiteIndex_range_map_all_basepoints,
    ``PoincareMT.M76.PLDomain.frontier_locallyPathConnectedSpace,
    ``PoincareMT.M76.PLDomain.isClopen_preimage_frontier_component,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_essential_annulus_in_original_mark,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_essential_annuli_in_original_marks,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_terminal_annulus_in_original_mark,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_terminal_annuli_in_original_marks,
    ``PoincareMT.M76.Dehn.exists_original_annular_projection_homeomorph_homotopy,
    ``PoincareMT.M76.Dehn.original_annular_positive_degree_eq_one_of_not_nullhomotopic,
    ``PoincareMT.M76.Dehn.original_annular_iterated_core_degree_eq_one,
    ``PoincareMT.M76.exists_real_lift_boundaryLoopIterate_periodLoop,
    ``PoincareMT.M76.Dehn.homotopic_nsmul_of_squareRimLoop_iterate,
    ``PoincareMT.M76.Dehn.homotopic_nsmul_of_periodLoop_iterate,
    ``PoincareMT.M76.Dehn.exists_finitePL_annular_straightening,
    ``PoincareMT.M76.Dehn.exists_originalPL_annular_straightening,
    ``PoincareMT.M76.Dehn.exists_original_surface_annular_straightening,
    ``PoincareMT.M76.Dehn.exists_original_surface_annular_straightening_of_mark,
    ``PoincareMT.M76.exists_finitePL_original_annular_coordinates,
    ``PoincareMT.M76.original_annular_coordinate_mark_iff,
    ``PoincareMT.M76.Dehn.originalAnnularHomotopyRel,
    ``PoincareMT.M76.Dehn.exists_originalAnnularExtension_joint_originalPL,
    ``PoincareMT.M76.Dehn.exists_originalAnnularExtension_joint_originalPL_symm,
    ``Homeomorph.IsFinitePL.exists_square_joint_PL_isotopy,
    ``PoincareMT.M76.Dehn.exists_joint_PL_annulus_isotopy_of_cut_rectangle,
    ``PoincareMT.M76.CollarIsotopy.collarHomotopyRelInner,
    ``PoincareMT.M76.CollarIsotopy.isFinitePL_collarExtensionOnCarrier,
    ``PoincareMT.M76.CollarIsotopy.isFinitePL_collarExtensionOnCarrier_symm,
    ``PoincareMT.M76.Dehn.annularIntegerTwist_finitePL,
    ``PoincareMT.M76.Dehn.annularIntegerTwist_symm_finitePL,
    ``PoincareMT.M76.Dehn.annularIntegerTwist_rim,
    ``PoincareMT.M76.Dehn.annularIntegerTwist_core_image,
    ``PoincareMT.M76.Dehn.annularTwistRadialLift_one,
    ``PoincareMT.M76.Dehn.exists_finitePL_annularTwist_radial_arc,
    ``PoincareMT.M76.Dehn.exists_finitePL_proper_arc_replacement_fix_rim,
    ``Set.IsFinitePLBallPair.exists_joint_PL_isotopy,
    ``Set.IsFinitePLBallPair.exists_supported_joint_PL_isotopy,
    ``PoincareMT.M76.Dehn.exists_joint_PL_proper_arc_isotopy_fix_rim,
    ``PoincareMT.M76.Dehn.exists_finitePL_annular_arc_lift,
    ``PoincareMT.M76.Dehn.exists_finite_annular_axis_contacts,
    ``PoincareMT.M76.Dehn.exists_finitePL_annular_returning_subarc,
    ``PoincareMT.M76.Dehn.exists_annular_returning_bigon_support,
    ``PoincareMT.M76.Dehn.exists_annular_returning_bigon_disk_motion,
    ``PoincareMT.M76.CollarIsotopy.exists_original_collar_motion,
    ``PoincareMT.M76.CollarIsotopy.collar_image_relative_frontier_subset_inner,
    ``PoincareMT.M76.Dehn.exists_zero_winding_annular_arc_lift,
    ``PoincareMT.M76.Dehn.exists_generic_annular_axis,
    ``PoincareMT.M76.Dehn.exists_finite_positive_excursion_family,
    ``PoincareMT.M76.Dehn.exists_complete_positive_interval_family,
    ``PoincareMT.M76.Dehn.exists_complete_upper_arc_family,
    ``PoincareMT.M76.Dehn.exists_generic_complete_upper_arc_families,
    ``PoincareMT.M76.Dehn.exists_empty_returning_bigon_of_lift,
    ``PoincareMT.M76.Dehn.exists_narrow_empty_returning_bigon_of_lift,
    ``PoincareMT.M76.Dehn.exists_zero_winding_lift_with_terminal_straightening,
    ``PoincareMT.M76.Dehn.exists_joint_PL_annular_radial_parameter_alignment,
    ``PoincareMT.M76.Dehn.exists_finitePL_cut_rectangle_of_fixed_radial,
    ``PoincareMT.M76.Dehn.exists_joint_PL_annulus_isotopy_of_fixed_radial,
    ``PoincareMT.M76.Dehn.exists_returning_arc_motion_fixing_residual,
    ``PoincareMT.M76.Dehn.exists_extended_finitePL_returning_arc,
    ``PoincareMT.M76.Dehn.exists_flattened_excursion_in_convex_tube,
    ``PoincareMT.M76.Dehn.exists_finitePL_returning_disk_above_level,
    ``PoincareMT.M76.Dehn.exists_lower_tail_complex_and_distant_remainder,
    ``PoincareMT.M76.Dehn.exists_periodic_empty_bigon_residual,
    ``PoincareMT.M76.Dehn.exists_periodic_empty_bigon_flattening,
    ``PoincareMT.M76.Dehn.exists_flattened_excursion_contact_deletion,
    ``PoincareMT.M76.Dehn.exists_periodic_empty_bigon_two_moves,
    ``PoincareMT.M76.Dehn.exists_strict_plane_periodic_contact_reduction,
    ``PoincareMT.M76.Dehn.exists_strict_plane_periodic_contact_reduction_of_nonempty,
    ``PoincareMT.M76.Dehn.periodic_contact_count_decreases_of_selected_copy_deletion,
    ``PoincareMT.M76.Dehn.periodic_axis_germs_of_selected_copy_deletion,
    ``PoincareMT.M76.Dehn.hasJointPLRadialStraightening_of_no_periodic_contacts,
    ``PoincareMT.M76.Dehn.contact_has_positive_or_reflected_excursion,
    ``PoincareMT.M76.Dehn.reflectedAnnularLift_zero_winding_geometry,
    ``PoincareMT.M76.Dehn.exists_zero_winding_annular_lift_after_joint_PL_isotopy,
    ``PoincareMT.M76.Dehn.exists_zero_winding_annular_endpoint,
    ``PoincareMT.M76.Dehn.hasJointPLAnnularIsotopy_of_radial_straightening,
    ``PoincareMT.M76.Dehn.exists_projected_annular_disk_motion,
    ``PoincareMT.M76.Dehn.exists_projected_annular_disk_motion_at_phase,
    ``PoincareMT.M76.Dehn.projected_two_moves_radial_contact_iff,
    ``PoincareMT.M76.Dehn.exists_projected_two_moves,
    ``PoincareMT.M76.Dehn.exists_affine_lift_germ_of_common_window,
    ``PoincareMT.M76.Dehn.exists_strict_annular_periodic_contact_reduction,
    ``PoincareMT.M76.Dehn.hasJointPLRadialStraightening_of_zero_winding_lift,
    ``PoincareMT.M76.Dehn.exists_proper_zero_winding_lift_after_joint_PL_isotopy,
    ``PoincareMT.M76.CollarIsotopy.exists_prepared_original_boundary_collar_motion,
    ``PoincareMT.M76.CollarIsotopy.exists_original_annular_circle_collar_motion_of_endpoint,
    ``PoincareMT.M76.CollarIsotopy.exists_original_annular_circle_collar_straightening,
    ``PoincareMT.M76.ChartwisePLHomeomorph.exists_polyhedralPL_parameter_transport,
    ``PoincareMT.M76.Dehn.ProtectedAnnulus.exists_original_embedded_cylinder_transport,
    ``PoincareMT.M76.CollarIsotopy.exists_original_spanning_annulus_core_straightening,
    ``PoincareMT.M76.coordinate_rim_intersection,
    ``PoincareMT.M76.Dehn.ProtectedAnnulus.coordinate_proper_annuli_intersection_on_mark,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_coordinate_spanning_annuli_of_commensurable_with_unique_rim_intersection,
    ``PoincareMT.M76.Dehn.ProtectedAnnulus.exists_planar_spanning_pair_with_marked_intersection,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_planar_spanning_pair_of_commensurable,
    ``PoincareMT.M76.PLDomain.exists_original_torus_candidate_on_frontier,
    ``PoincareMT.M76.exists_marked_product_of_incompressible_positioned_annulus_pair,
    ``PoincareMT.M76.not_hamiltonZero_boundary_failure_of_product_with_original_marks,
    ``PoincareMT.M76.not_hamiltonZero_boundary_failure_of_incompressible_positioned_annulus_pair,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_coordinate_spanning_annuli_with_unique_intersection,
    ``PoincareMT.M76.SurfaceIntersectionComponents.component_card_eq_one_of_single_mark,
    ``PoincareMT.M76.SurfaceIntersectionComponents.exists_marked_spanning_interval_parametrization,
    ``PoincareMT.M76.Dehn.ProtectedAnnulus.exists_coordinate_annuli_spanning_interval,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_halfTranslate,
    ``PoincareMT.M76.PeriodicSquare.exists_coordinate_cross_neighborhood,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_finitePL_inner_rectangle_disk,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_original_coordinate_cross_complement_disk,
    ``PoincareMT.M76.exists_PL_torus_parametrization_of_source_square_map,
    ``PoincareMT.M76.exists_hamiltonZero_phase_covering_of_source_square_maps,
    ``PoincareMT.M76.Dehn.exists_finitePL_spanning_arc_straightening,
    ``PoincareMT.M76.PeriodicSquare.SourceSquareMap.exists_two_original_coordinate_annuli_and_complement_disk,
    ``PoincareMT.M76.hasHamiltonRelativeTorusRigidity_of_card_one_two,
    ``PoincareMT.M76.hasHamiltonRelativeTorusRigidity_of_card_two_one,
    ``PoincareMT.M76.CollarIsotopy.exists_original_annular_collar_motion]
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut pending : Array Name := roots
  let mut seen : NameSet := {}
  let mut admissions : NameSet := {}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name
      | throwError "Cannot inspect {name}"
    if info.type.hasSorry || (info.value? (allowOpaque := true)).any Expr.hasSorry then
      admissions := admissions.insert name
    pending := pending ++ info.getUsedConstantsAsSet.toArray
  let mut badAxiom := false
  for root in roots do
    let axioms ← collectAxioms root
    logInfo m!"{root}: axioms: {axioms}"
    for ax in axioms do
      if !standard.contains ax then badAxiom := true
  logInfo m!"source disk producers: {seen.size} reachable declarations; direct admissions: {admissions.toArray.qsort Name.lt}"
  unless admissions.isEmpty && !badAxiom do
    throwError "Source disk producers have an unproved dependency"

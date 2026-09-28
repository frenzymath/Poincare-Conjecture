-- LeeLib: Lean formalization of John M. Lee, *Introduction to Riemannian Manifolds* (2nd ed., GTM 176).

-- Chapter 1: What Is Curvature?
import LeeLib.Ch01.RigidMotion
import LeeLib.Ch01.DistancePreservingLinear
import LeeLib.Ch01.EuclideanTriangles
import LeeLib.Ch01.CircleClassification
import LeeLib.Ch01.Circumference

-- Chapter 2: Riemannian Metrics
import LeeLib.Ch02.InnerProducts
import LeeLib.Ch02.RiemannianMetric
import LeeLib.Ch02.MetricExistence
import LeeLib.Ch02.OrthonormalFrame
import LeeLib.Ch02.OrthonormalCoframe
import LeeLib.Ch02.VolumeForm
import LeeLib.Ch02.Density
import LeeLib.Ch02.DensityOrthonormalFrame
import LeeLib.Ch02.PullbackBundle
import LeeLib.Ch02.PullbackMetric
import LeeLib.Ch02.ProductMetric
import LeeLib.Ch02.MusicalIsomorphism
import LeeLib.Ch02.AdaptedFrame
import LeeLib.Ch02.NormalBundle
import LeeLib.Ch02.Sphere
import LeeLib.Ch02.Distance
import LeeLib.Ch02.MetricComparison
import LeeLib.Ch02.DistanceComparison
import LeeLib.Ch02.OpenSubmanifold
import LeeLib.Ch02.PolarCoordinates
import LeeLib.Ch02.Isometry
import LeeLib.Ch02.HypersurfaceVolumeForm
import LeeLib.Ch02.HypersurfaceOrientation
import LeeLib.Ch02.HypersurfaceNormal
import LeeLib.Ch02.IsometryVolumeForm
import LeeLib.Ch02.ScalarProduct
import LeeLib.Ch02.PseudoGramSchmidt
import LeeLib.Ch02.PseudoRiemannianMetric
import LeeLib.Ch02.PseudoOrthonormalFrame
import LeeLib.Ch02.PseudoAdaptedFrame
import LeeLib.Ch02.PseudoPullbackMetric
import LeeLib.Ch02.PseudoNormalBundle
import LeeLib.Ch02.HypersurfaceSignature
import LeeLib.Ch02.PseudoHypersurface
import LeeLib.Ch02.EmbeddingCriterion
import LeeLib.Ch02.PseudoLevelSet
import LeeLib.Ch02.HorizontalLift
import LeeLib.Ch02.HorizontalNonLift
import LeeLib.Ch02.GradientCharacterization
import LeeLib.Ch02.HorizontalSplitting
import LeeLib.Ch02.RiemannianCovering
import LeeLib.Ch02.RiemannianSubmersion
import LeeLib.Ch02.SubmersionMetric
import LeeLib.Ch02.SurfaceOfRevolution
import LeeLib.Ch02.GraphMetric
import LeeLib.Ch02.LevelSetStraightening
import LeeLib.Ch02.LorentzForm
import LeeLib.Ch02.FormProduct
import LeeLib.Ch02.LorentzMetric
import LeeLib.Ch02.EigenSelection
import LeeLib.Ch02.SignatureSpectrum
import LeeLib.Ch02.LocalIsometry
import LeeLib.Ch02.LorentzDistribution
import LeeLib.Ch02.LevelSetAdaptedChart
import LeeLib.Ch02.LevelSetChartedSpace
import LeeLib.Ch02.RegularLevelSet
import LeeLib.Ch02.RegularSetHypersurface
import LeeLib.Ch02.InnerForms
import LeeLib.Ch02.InnerFormsBundle
import LeeLib.Ch02.FiberMetricForms
import LeeLib.Ch02.WedgeProduct
import LeeLib.Ch02.HodgeStar
import LeeLib.Ch02.EuclideanHodge
import LeeLib.Ch02.BasisWedgeHodge
import LeeLib.Ch02.SmoothCoframeWedge
import LeeLib.Ch02.SmoothHodgeStar
import LeeLib.Ch02.FlatTorus
import LeeLib.Ch02.RiemannianSubmersionExamples
import LeeLib.Ch02.ArcLengthReparametrization

-- Chapter 4: Connections
import LeeLib.Ch04.Connection
import LeeLib.Ch04.Locality
import LeeLib.Ch04.DifferenceTensor
import LeeLib.Ch04.ConnectionCoefficients
import LeeLib.Ch04.ConnectionFromCoefficients
import LeeLib.Ch04.TransformationLaw
import LeeLib.Ch04.Torsion
import LeeLib.Ch04.CovariantHessian
import LeeLib.Ch04.LinearODE
import LeeLib.Ch04.ChartConnection
import LeeLib.Ch04.ParallelTransport
import LeeLib.Ch04.ParallelTransportDetermines
import LeeLib.Ch04.DifferenceTensorTorsion
import LeeLib.Ch04.Geodesic
import LeeLib.Ch04.GeodesicSpray
import LeeLib.Ch04.GeodesicEquationReadback
import LeeLib.Ch04.DifferenceTensorGeodesics
import LeeLib.Ch04.ParallelReparametrization
import LeeLib.Ch04.PullbackConnection

-- Chapter 6: Geodesics and Distance
import LeeLib.Ch06.HopfRinow
import LeeLib.Ch06.NormalBalls
import LeeLib.Ch06.CompleteLocalIsometry

-- Chapter 10: Jacobi Fields
import LeeLib.Ch10.CriticalPointsConjugacy

-- Chapter 11: Comparison Theory
import LeeLib.Ch11.ConjugatePointComparison

-- Chapter 12: Curvature and Topology
import LeeLib.Ch12.CartanHadamard
import LeeLib.Ch12.Myers

-- Appendix A: Review of Smooth Manifolds
import LeeLib.AppendixA.AlternatingSmooth
import LeeLib.AppendixA.AlternatingBundle
import LeeLib.AppendixA.InverseFunctionTheorem
import LeeLib.AppendixA.LocalFrameCriterion
import LeeLib.AppendixA.LocalSection
import LeeLib.AppendixA.NonvanishingSection
import LeeLib.AppendixA.SliceChart
import LeeLib.AppendixA.SubbundleCriterion
import LeeLib.AppendixA.VectorFieldExtension
import LeeLib.AppendixA.CoveringLifting

-- Appendix B: Review of Tensors
import LeeLib.AppendixB.CauchyBinet
import LeeLib.AppendixB.Laplace

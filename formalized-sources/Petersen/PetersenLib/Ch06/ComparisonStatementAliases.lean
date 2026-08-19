import PetersenLib.Ch06.CartanHadamardCore
import PetersenLib.Ch06.RemainingInterfaces
import PetersenLib.Ch06.ComparisonInterfaces
import PetersenLib.Ch06.ConjugateRadiusInjectivity

/-!
# Petersen Ch. 6, Sections 6.2--6.4 -- statement-level aliases

The current Ch. 6 development proves the analytic and domain-certified cores
of several comparison theorems.  This module exposes the names used in the
chapter's statement inventory without concealing those necessary hypotheses:
each declaration below is exactly an alias of its documented conditional core.
In particular, these are not claims that the missing global exponential-map
or Jacobi-to-`D exp` bridges have been completed.
-/

namespace PetersenLib

/-! ## Section 6.2 -/

alias cartanHadamard := cartanHadamard_coveringCore

alias cartanHadamard_fails_forRicci := cartanHadamard_failure_of_notEuclidean

/-! ## Section 6.3 -/

alias closedParallelFieldAroundClosedGeodesic := closedParallelField_holonomyFixedVector

/-! ## Section 6.4 -/

alias rauchComparisonViaIndexForm := rauchComparisonViaIndexForm_jacobiBoundary

alias conjugateRadiusLowerBound := conjugateRadiusLowerBound_of_jacobiDomainCertificates

alias injectivityRadius_nonpositiveCurvature := injectivityRadius_nonpositiveCurvature_modelCore

alias klingenbergInjectivityEstimate := klingenbergInjectivityEstimate_of_domainCertificates

alias convexityRadiusCriterion := convexityRadiusCriterion_of_secondDerivative

end PetersenLib

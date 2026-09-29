import PoincareMT.Statements.M12GeneralizedEquation
import PoincareMT.Proofs.M11
import PoincareMT.Proofs.M03.ConnectionExistence
import PoincareMT.Proofs.M03.ConnectionRegularity
import PoincareMT.Proofs.M04.CurvatureCalculus

/-!
# M12 intrinsic Ricci equation proof

The single milestone admission owns horizontal calculus, coordinate transport
and ordinary-flow realization. The checked assembly supplies only M11 geometry
and the three required M03/M04 metric components, at both carrier universes.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

/-- M12's narrow inputs: every smooth metric on a Hausdorff second-countable
n-manifold has Levi-Civita data; each retained connection acts smoothly on
local smooth fields and has the stated curvature tensor calculus. These are
the existing M03 connection and M04 tensor components at the chosen universe.
Sources: Morgan-Tian Theorem 1.2 and formula (1.1), pp. 3-4, and Definition 1.4
with its curvature contractions, pp. 5-7. Their retained connection choices
are compared only on regular fields; no new proof placeholder is added. -/
theorem m12MetricPredecessors (n : ℕ) : M12MetricPredecessors.{u} n where
  connection_exists _ _ _ _ _ _ g := exists_leviCivitaData g
  connection_regular _ _ _ _ _g D _ hU Y hY := D.contMDiffOn_connection hU Y hY
  curvature_calculus _ _ _ _ _g D := D.curvatureTensorCalculus

/-- warning: declaration uses `sorry` -/
#guard_msgs in
/-- M12: given M11's geometric construction and the M03 connection-existence,
local-regularity and M04 tensor-calculus inputs at the carrier and coordinate
universes, every realized spacetime with its actual adapted cover has retained
slice connections, smooth horizontal Lie/Riemann/Ricci tensors, smooth scalar
and squared curvature norm, and a continuous full curvature norm. These
evaluations are independent of connection choices. The canonical horizontal
connection agrees on local smooth fields with the slice derivative plus the
time bracket; its metric defect is dt(Z) times Lie_chi(G).
The intrinsic equation Lie_chi(G) = -2 Ric_G is equivalent to the ordinary
Ricci PDE on the adapted cover. Every supplied compatible cylinder satisfying
the intrinsic equation on its actual image gives an ordinary RicciFlow with
exactly its supplied pullback metric. Actual covering families give the
converse. For a moving time-preserving gauge, the actual drift beta satisfies
De(positive-time-vector,beta) = chi; the pulled-back equation is
partial_t k = -2 Ric(k) - Lie_beta(k), with the stated curvature and connection
transport identities. A given smooth metric family on a nonempty smooth
n-manifold has this geometry on exactly I times that manifold, and its ordinary
Ricci PDE is equivalent to the intrinsic equation there. All claims include
n=0 and within-interval derivatives at every included endpoint.

Sources: Morgan-Tian Theorem 1.2 and formula (1.1), pp. 3-4; Definition 1.4
and curvature contractions, pp. 5-7; Definitions 3.1-3.2, p. 35;
Definitions 3.34-3.38 and Remark 3.37, pp. 59-61; Definition 14.7 and
Remark 14.9, pp. 348-349, for the horizontal connection and endpoint convention.
The complete coordinate derivation is in `reviews/contracts/M12-repair-contract.md`.
Apply MT-DETURCK-PULLBACK-SIGN in `reviews/errata/2026-09-10-source-audit.md`;
the 2015 Chapter 19 correction does not replace these definitions. -/
theorem generalizedRicciGaugeGeometry (n : ℕ)
    (hGeometry : GeneralizedSpacetimeGeometryTheory.{u} n)
    (hMetric : M12MetricPredecessors.{u} n)
    (hCoordinates : M12MetricPredecessors.{0} n) :
    GeneralizedRicciGaugeTheory.{u} n := by
  sorry

/-- M12 assembled from the actual M11 geometry theorem and the M03/M04 metric
components in both required universes. The conclusion is the complete
horizontal-calculus, adapted-equation, moving-gauge and product theorem stated
above, with the same actual maps, metrics and endpoint conventions.
Sources: Morgan-Tian Theorem 1.2, pp. 3-4, Definition 1.4, pp. 5-7, and
Definitions 3.34-3.38 with Remark 3.37, pp. 59-61; apply
MT-DETURCK-PULLBACK-SIGN as in the core milestone statement. -/
theorem generalizedRicciGaugeGeometry_from_M03_M04_M11 (n : ℕ) :
    GeneralizedRicciGaugeTheory.{u} n :=
  generalizedRicciGaugeGeometry n (generalizedSpacetimeGeometry n)
    (m12MetricPredecessors.{u} n) (m12MetricPredecessors.{0} n)

/-- An ordinary Ricci flow on a nonempty smooth n-manifold realizes the
intrinsic equation on its exact product spacetime and given metric family,
using a supplied M12 theory. This is the ordinary-product observation after
Morgan-Tian Remark 3.37, p. 61, with within derivatives at included endpoints;
it is a checked consequence and adds no admission. -/
theorem GeneralizedRicciGaugeTheory.ordinary_flow {n : ℕ}
    (h : GeneralizedRicciGaugeTheory.{u} n) (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] [Nonempty M]
    (I : SpacetimeInterval) (F : RicciFlow n M I.domain) :
    ∃ R : OrdinaryProductRicciGeometry F.metric I,
      IntrinsicGeneralizedRicciEquation R.leafwiseConnection := by
  obtain ⟨R⟩ := h.ordinary_product M F.metric I F.smooth
  exact ⟨R, (R.equation_iff F.connection).mpr F.equation⟩

end PoincareMT

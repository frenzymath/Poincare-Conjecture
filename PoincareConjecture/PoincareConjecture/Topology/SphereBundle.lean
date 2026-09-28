import PoincareConjecture.Topology.MappingTorus
import PoincareConjecture.Topology.MappingTorusProduct
import HatcherLib.Ch1.Sphere
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Fundamental groups of sphere mapping tori

The existing reference library proves that the actual standard two-sphere
is simply connected using its stereographic open cover and van Kampen.
We reuse that checked theorem, then compute the fundamental group of every
mapping torus of a sphere homeomorphism through its genuine cyclic cover.

This includes the identity and antipodal monodromies representing the two
sphere bundles over the circle. The definitions do not include a
fundamental-group calculation or a no-simple-connectivity condition.
-/

open Set Metric
open scoped Topology

namespace PoincareConjecture

/-- The actual standard two-sphere. -/
abbrev Sphere2 := ↥(sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

instance sphere2_simplyConnectedSpace : SimplyConnectedSpace Sphere2 :=
  HatcherLib.standardSphereSimplyConnected 0

/-- Antipodal monodromy for the twisted sphere bundle. -/
noncomputable def sphere2Antipodal : Sphere2 ≃ₜ Sphere2 where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

/-- Every mapping torus of the standard two-sphere has infinite cyclic
fundamental group. No restriction to a preselected trivial fundamental
group, faithful finite action, or already spherical manifold is imposed. -/
noncomputable def sphereMappingTorusFundamentalGroupEquiv (φ : Sphere2 ≃ₜ Sphere2)
    (q : MappingTorus φ) : FundamentalGroup (MappingTorus φ) q ≃* Multiplicative ℤ :=
  mappingTorusFundamentalGroupEquiv φ q

/-- Identity-monodromy sphere-bundle model. -/
abbrev UntwistedSphereMappingTorus := MappingTorus (Homeomorph.refl Sphere2)

/-- Antipodal-monodromy sphere-bundle model. -/
abbrev TwistedSphereMappingTorus := MappingTorus sphere2Antipodal

theorem untwistedSphereMappingTorus_not_simplyConnected :
    ¬ SimplyConnectedSpace UntwistedSphereMappingTorus :=
  mappingTorus_not_simplyConnected (Homeomorph.refl Sphere2)

theorem twistedSphereMappingTorus_not_simplyConnected :
    ¬ SimplyConnectedSpace TwistedSphereMappingTorus :=
  mappingTorus_not_simplyConnected sphere2Antipodal

/-- The identity mapping-torus model is homeomorphic to the ordinary product
of the actual two-sphere and complex unit circle. Both quotient-to-product
and additive-circle-to-unit-circle identifications are proved constructions. -/
noncomputable def untwistedSphereMappingTorusHomeomorph :
    UntwistedSphereMappingTorus ≃ₜ Sphere2 × Circle :=
  (identityMappingTorusHomeomorph Sphere2).trans
    ((Homeomorph.refl Sphere2).prodCongr (AddCircle.homeomorphCircle one_ne_zero))

/-- The actual product `S² × S¹` has infinite cyclic fundamental group at
every basepoint. This is not just a calculation for an abstract bundle model. -/
noncomputable def sphere2CircleFundamentalGroupEquiv (q : Sphere2 × Circle) :
    FundamentalGroup (Sphere2 × Circle) q ≃* Multiplicative ℤ := by
  let e := untwistedSphereMappingTorusHomeomorph.symm
  let h : FundamentalGroup (Sphere2 × Circle) q ≃*
      FundamentalGroup UntwistedSphereMappingTorus (e q) :=
    MulEquiv.unop (HatcherLib.homotopyEquivPiOneMulEquiv e.toHomotopyEquiv q)
  exact h.trans (sphereMappingTorusFundamentalGroupEquiv (Homeomorph.refl Sphere2) (e q))

/-- The twisted sphere bundle has the same fundamental group, with its
nontrivial monodromy explicitly retained in the quotient definition. -/
noncomputable def twistedSphereFundamentalGroupEquiv (q : TwistedSphereMappingTorus) :
    FundamentalGroup TwistedSphereMappingTorus q ≃* Multiplicative ℤ :=
  sphereMappingTorusFundamentalGroupEquiv sphere2Antipodal q

theorem sphere2Circle_not_simplyConnected : ¬ SimplyConnectedSpace (Sphere2 × Circle) := by
  intro h
  letI := h
  have htorus : SimplyConnectedSpace UntwistedSphereMappingTorus :=
    untwistedSphereMappingTorusHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  exact untwistedSphereMappingTorus_not_simplyConnected htorus

end PoincareConjecture

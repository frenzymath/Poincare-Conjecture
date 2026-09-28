import HatcherLib.Ch0.CWPairHEPLimit
import HatcherLib.Ch0.AttachingHomotopyEquivMaps
import HatcherLib.Ch0.QuotientContractible

/-!
# Chapter 0 - consequences of the CW-pair homotopy extension theorem

The skeletal limit theorem proves the HEP for a CW pair.  This file records the
chapter-facing consequences that Hatcher states separately: the deformation
retraction formulation, collapse of a contractible subcomplex, and invariance
of an attaching space under homotopy of the attaching map (including the
relative-to-the-base refinement).
-/

namespace HatcherLib

open scoped unitInterval

universe u v

variable {X : Type u} [TopologicalSpace X] [T2Space X]

namespace IsCWPair

/-- Every CW pair has the homotopy extension property. -/
theorem hasHEP {A : Set X} [Topology.CWComplex (Set.univ : Set X)]
    (hA : IsCWPair A) : HasHEP.{u, v} A := by
  obtain ⟨d⟩ := HasHEP.hepBase_deformationRetract
    (CWSkeletonHEPLimit.IsCWPair.hasHEP hA)
  exact hasHEP_of_isRetract hA.isClosed ⟨d.retraction, d.mapsInto, d.fixes⟩

/-- For a CW pair `(X,A)`, the HEP base `X x {0} union A x I` is a deformation
retract of `X x I`. -/
theorem hepBase_deformationRetract {A : Set X}
    [Topology.CWComplex (Set.univ : Set X)] (hA : IsCWPair A) :
    Nonempty (DeformationRetract (hepBase A)) :=
  HasHEP.hepBase_deformationRetract (IsCWPair.hasHEP hA)

end IsCWPair

/-- Collapsing a contractible CW subcomplex is a homotopy equivalence. -/
theorem collapseMk_homotopyEquiv_of_cwPair {A : Set X}
    [Topology.CWComplex (Set.univ : Set X)] (hA : IsCWPair A)
    [ContractibleSpace ↥A] :
    ∃ g : C(collapseQuotient A, X),
      (g.comp (collapseMk A)).Homotopic (ContinuousMap.id X) ∧
        ((collapseMk A).comp g).Homotopic
          (ContinuousMap.id (collapseQuotient A)) :=
  collapseMk_homotopyEquiv hA.hasHEP

variable {X0 X1 : Type u} [TopologicalSpace X0] [TopologicalSpace X1]
  [T2Space X1]

/-- Homotopic attaching maps on a CW pair give homotopy equivalent attaching
spaces. -/
theorem attachingSpace_homotopyEquiv_of_cwPair {A : Set X1}
    [Topology.CWComplex (Set.univ : Set X1)] (hA : IsCWPair A)
    {f g : C(↥A, X0)} (hfg : f.Homotopic g) :
    Nonempty (ContinuousMap.HomotopyEquiv (AttachingSpace A f)
      (AttachingSpace A g)) :=
  attachingSpace_homotopyEquiv_of_homotopic hA.isClosed hA.hasHEP hfg

/-- The attaching-space equivalence for homotopic maps of a CW pair can be
chosen relative to the base `X0`. -/
theorem attachingSpace_homotopyEquiv_rel_of_cwPair {A : Set X1}
    [Topology.CWComplex (Set.univ : Set X1)] (hA : IsCWPair A)
    {f g : C(↥A, X0)} (hfg : f.Homotopic g) :
    ∃ (phi : C(AttachingSpace A f, AttachingSpace A g))
      (psi : C(AttachingSpace A g, AttachingSpace A f)),
      (∀ x0 : X0, phi (attachInclBase A f x0) = attachInclBase A g x0) ∧
      (∀ x0 : X0, psi (attachInclBase A g x0) = attachInclBase A f x0) ∧
      Nonempty ((psi.comp phi).HomotopyRel (ContinuousMap.id _)
        (Set.range (attachInclBase A f))) ∧
      Nonempty ((phi.comp psi).HomotopyRel (ContinuousMap.id _)
        (Set.range (attachInclBase A g))) :=
  attachingSpace_homotopyEquiv_rel_of_homotopic hA.isClosed hA.hasHEP hfg

end HatcherLib

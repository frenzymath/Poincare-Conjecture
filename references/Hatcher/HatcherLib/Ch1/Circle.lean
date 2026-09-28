import HatcherLib.Ch1.CoveringSpaces
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Algebra.Group.Equiv.Opposite
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# Chapter 1: the fundamental group of the circle

This file computes the fundamental group of the additive unit circle using
the universal covering `ℝ → AddCircle (1 : ℝ)`.  The endpoint of a lifted
based loop is the corresponding integer, and path lifting supplies the group
law and the inverse construction.
-/

namespace HatcherLib

noncomputable section

open scoped unitInterval

open AddSubgroup
open CategoryTheory

/-- The additive unit circle `ℝ / ℤ`. -/
abbrev UnitCircle := AddCircle (1 : ℝ)

/-- The fiber of `ℝ → UnitCircle` over `0`, represented as the integer multiples of `1`. -/
abbrev CircleFiber := AddSubgroup.zmultiples (1 : ℝ)

/-- The universal covering map from the real line to the additive unit circle. -/
def unitCircleCover : C(ℝ, UnitCircle) :=
  ⟨(↑), AddCircle.continuous_mk' 1⟩

/-- The covering-map structure on `unitCircleCover`. -/
def unitCircleCov : IsCoveringMap ((↑) : ℝ → UnitCircle) :=
  AddCircle.isCoveringMap_coe 1

def fiberPoint (e : ((↑) : ℝ → UnitCircle) ⁻¹' ({0} : Set UnitCircle)) : CircleFiber := by
  refine ⟨e.1, ?_⟩
  rw [AddSubgroup.mem_zmultiples_iff]
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff 1).mp e.2
  exact ⟨n, by simpa using hn⟩

/-- Send a based loop class to the endpoint of its lift starting at `0`. -/
def endpointFiber (g : FundamentalGroup UnitCircle 0) : CircleFiber :=
  fiberPoint (unitCircleCov.monodromy (FundamentalGroup.toPath g) ⟨0, by simp⟩)

theorem endpointFiber_one : endpointFiber (1 : FundamentalGroup UnitCircle 0) = 0 := by
  apply Subtype.ext
  change (unitCircleCov.monodromy (Path.Homotopic.Quotient.refl 0)
      ⟨0, by simp⟩).1 = 0
  rw [unitCircleCov.monodromy_refl]
  rfl

/-- Project a path in `ℝ` from `0` to an integer fiber point to a based circle loop. -/
def fiberLoop (z : CircleFiber) : FundamentalGroup UnitCircle 0 := by
  have hz : ((z : ℝ) : UnitCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr (AddSubgroup.mem_zmultiples_iff.mp z.property)
  let γ : Path (0 : ℝ) (z : ℝ) :=
    PathConnectedSpace.somePath (0 : ℝ) (z : ℝ)
  let q : Path (0 : UnitCircle) 0 :=
    (γ.map unitCircleCover.continuous).cast (by simp [unitCircleCover]) hz.symm
  exact FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk q)

theorem endpointFiber_fiberLoop (z : CircleFiber) :
    endpointFiber (fiberLoop z) = z := by
  apply Subtype.ext
  unfold endpointFiber fiberLoop
  dsimp only [fiberPoint]
  let hz : ((z : ℝ) : UnitCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr (AddSubgroup.mem_zmultiples_iff.mp z.property)
  let γ : Path (0 : ℝ) (z : ℝ) :=
    PathConnectedSpace.somePath (0 : ℝ) (z : ℝ)
  let q : Path (0 : UnitCircle) 0 :=
    (γ.map unitCircleCover.continuous).cast (by simp [unitCircleCover]) hz.symm
  change (unitCircleCov.monodromy (Path.Homotopic.Quotient.mk q)
      ⟨0, by simp⟩).1 = z
  let ey : ((↑) : ℝ → UnitCircle) ⁻¹' ({0} : Set UnitCircle) := ⟨z, hz⟩
  have heq : (Path.Homotopic.Quotient.mk γ).map unitCircleCover =
      (Path.Homotopic.Quotient.mk q).cast (by simp [unitCircleCover]) ey.2 := by
    simp [q, ey, Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.cast_cast]
    exact eq_of_heq (Path.Homotopic.Quotient.cast_heq _ _).symm
  have hm : unitCircleCov.monodromy (Path.Homotopic.Quotient.mk q)
      ⟨0, by simp⟩ = ey :=
    unitCircleCov.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk γ) heq
  exact congrArg Subtype.val hm

theorem fiberLoop_endpointFiber (g : FundamentalGroup UnitCircle 0) :
    fiberLoop (endpointFiber g) = g := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  unfold fiberLoop
  change FundamentalGroup.fromPath _ = FundamentalGroup.fromPath (FundamentalGroup.toPath g)
  congr 1
  rw [← hγ, Path.Homotopic.Quotient.eq]
  have he0 : (((endpointFiber g : CircleFiber) : ℝ) : UnitCircle) = 0 :=
    (AddCircle.coe_eq_zero_iff 1).mpr
      (AddSubgroup.mem_zmultiples_iff.mp (endpointFiber g).property)
  let q0 : Path (0 : UnitCircle) 0 :=
    ((PathConnectedSpace.somePath (0 : ℝ) (endpointFiber g : ℝ)).map
      unitCircleCover.continuous).cast (by simp [unitCircleCover]) he0.symm
  change q0.Homotopic γ
  let Γ : C(↑unitInterval, ℝ) := unitCircleCov.liftPath γ 0 (by simp)
  have hmonoΓ :
      (unitCircleCov.monodromy (Path.Homotopic.Quotient.mk γ) ⟨0, by simp⟩).1 = Γ 1 := by
    rfl
  have hend : ((endpointFiber g : CircleFiber) : ℝ) = Γ 1 := by
    change (unitCircleCov.monodromy (FundamentalGroup.toPath g) ⟨0, by simp⟩).1 = Γ 1
    rw [← hγ]
    exact hmonoΓ
  have hΓend : ((Γ 1 : ℝ) : UnitCircle) = 0 := by
    have h := congrFun (unitCircleCov.liftPath_lifts γ 0 (by simp)) 1
    simpa [Γ, Function.comp_apply] using h
  let δ : Path (0 : ℝ) (Γ 1) := PathConnectedSpace.somePath 0 (Γ 1)
  let Γp : Path (0 : ℝ) (Γ 1) :=
    ⟨Γ, unitCircleCov.liftPath_zero γ 0 (by simp), rfl⟩
  have hδΓ : δ.Homotopic Γp := SimplyConnectedSpace.paths_homotopic δ Γp
  have hδmap := hδΓ.map unitCircleCover
  have hΓmap :
      (Γp.map unitCircleCover.continuous).cast (by simp [unitCircleCover]) hΓend.symm = γ := by
    apply Path.ext
    funext t
    have h := congrFun (unitCircleCov.liftPath_lifts γ 0 (by simp)) t
    simpa [Γp, unitCircleCover, Function.comp_apply] using h
  let qΓ : Path (0 : UnitCircle) 0 :=
    (Γp.map unitCircleCover.continuous).cast (by simp [unitCircleCover]) hΓend.symm
  let qδ : Path (0 : UnitCircle) 0 :=
    (δ.map unitCircleCover.continuous).cast (by simp [unitCircleCover]) hΓend.symm
  have hcast :
      qδ.Homotopic qΓ := by
    rcases hδmap with ⟨F⟩
    refine ⟨F.cast ?_ ?_⟩
    · apply Path.ext
      rfl
    · apply Path.ext
      rfl
  have hq0 : q0 = qδ := by
    apply Path.ext
    dsimp [q0, qδ, δ]
    rw [hend]
  rw [hq0]
  have hqΓ : qΓ = γ := by
    dsimp [qΓ]
    exact hΓmap
  rw [hqΓ] at hcast
  exact hcast

theorem circleFiber_coe_eq_zero (z : CircleFiber) :
    ((z : ℝ) : UnitCircle) = 0 :=
  (AddCircle.coe_eq_zero_iff 1).mpr
    (AddSubgroup.mem_zmultiples_iff.mp z.property)

theorem liftPath_add_fiber_endpoint (γ : C(↑unitInterval, UnitCircle))
    (hγ : γ 0 = 0) (z : CircleFiber) :
    unitCircleCov.liftPath γ (z : ℝ)
        (hγ.trans (circleFiber_coe_eq_zero z).symm) 1 =
      (z : ℝ) + unitCircleCov.liftPath γ 0 (by simpa using hγ) 1 := by
  let Γ : C(↑unitInterval, ℝ) := unitCircleCov.liftPath γ 0 (by simpa using hγ)
  let T : C(↑unitInterval, ℝ) :=
    ⟨fun t => (z : ℝ) + Γ t, by fun_prop⟩
  have hTlift : (fun t => ((T t : ℝ) : UnitCircle)) = γ := by
    funext t
    calc
      ((T t : ℝ) : UnitCircle) = (z : UnitCircle) + (Γ t : UnitCircle) := by
        simp [T]
      _ = (Γ t : UnitCircle) := by rw [circleFiber_coe_eq_zero z, zero_add]
      _ = γ t := by
        have h := congrFun (unitCircleCov.liftPath_lifts γ 0 (by simpa using hγ)) t
        simpa [Γ, Function.comp_apply] using h
  have hTzero : T 0 = (z : ℝ) := by
    simp [T, Γ, unitCircleCov.liftPath_zero]
  have hT := (unitCircleCov.eq_liftPath_iff'
    (hγ.trans (circleFiber_coe_eq_zero z).symm)).mpr ⟨hTlift, hTzero⟩
  have hT1 := DFunLike.congr_fun hT 1
  simpa [T, Γ] using hT1.symm

theorem endpointFiber_fromPath (γ : Path (0 : UnitCircle) 0) :
    ((endpointFiber (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) : CircleFiber) : ℝ) =
      unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 := by
  rfl

theorem endpointFiber_trans (γ δ : Path (0 : UnitCircle) 0) :
    endpointFiber (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (δ.trans γ))) =
      endpointFiber (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) +
        endpointFiber (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) :
          FundamentalGroup UnitCircle 0) := by
  apply Subtype.ext
  change unitCircleCov.liftPath (δ.trans γ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 =
    ((endpointFiber (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)) : CircleFiber) : ℝ) +
      ((endpointFiber (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)) : CircleFiber) : ℝ)
  rw [endpointFiber_fromPath, endpointFiber_fromPath]
  have htrans := unitCircleCov.liftPath_trans (e := (0 : ℝ)) (by simp) δ γ
  let Γδ : Path (0 : ℝ)
      (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) :=
    ⟨unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp),
      unitCircleCov.liftPath_zero (δ : C(↑unitInterval, UnitCircle)) 0 (by simp), rfl⟩
  have hδend :
      ((unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 : ℝ) :
        UnitCircle) = 0 := by
    have h := congrFun (unitCircleCov.liftPath_lifts (δ : C(↑unitInterval, UnitCircle)) 0
      (by simp)) 1
    simpa [Function.comp_apply] using h
  let Γγ : Path
      (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1)
      (unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle))
        (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) (by simp [hδend]) 1) :=
    ⟨unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle))
        (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) (by simp [hδend]),
      unitCircleCov.liftPath_zero (γ : C(↑unitInterval, UnitCircle)) _ _, rfl⟩
  have htrans' :
      unitCircleCov.liftPath (δ.trans γ : C(↑unitInterval, UnitCircle)) 0 (by simp) =
        (Γδ.trans Γγ : Path (0 : ℝ) _) := by
    simpa [Γδ, Γγ] using htrans
  have htrans1 := DFunLike.congr_fun htrans' 1
  have hadd := liftPath_add_fiber_endpoint (γ : C(↑unitInterval, UnitCircle)) (by simp)
    (endpointFiber (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)))
  have hadd' :
      unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle))
          (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) (by simp [hδend]) 1 =
        (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) +
          unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 := by
    simpa [endpointFiber_fromPath, hδend] using hadd
  calc
    unitCircleCov.liftPath (δ.trans γ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 =
        (Γδ.trans Γγ) 1 := htrans1
    _ = Γγ 1 := Path.target _
    _ = unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle))
        (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) (by simp [hδend]) 1 := rfl
    _ = (unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1) +
        unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 := hadd'
    _ = unitCircleCov.liftPath (γ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 +
        unitCircleCov.liftPath (δ : C(↑unitInterval, UnitCircle)) 0 (by simp) 1 := by rw [add_comm]

theorem endpointFiber_mul (g h : FundamentalGroup UnitCircle 0) :
    endpointFiber (g * h) = endpointFiber g + endpointFiber h := by
  obtain ⟨γ, hγ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath g)
  obtain ⟨δ, hδ⟩ := Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath h)
  have hg : g = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
    change FundamentalGroup.fromPath (FundamentalGroup.toPath g) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
    rw [hγ]
  have hh : h = FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ) := by
    change FundamentalGroup.fromPath (FundamentalGroup.toPath h) =
      FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk δ)
    rw [hδ]
  rw [hg, hh]
  change endpointFiber (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (δ.trans γ))) = _
  exact endpointFiber_trans γ δ

def endpointEquiv : FundamentalGroup UnitCircle 0 ≃ CircleFiber where
  toFun := endpointFiber
  invFun := fiberLoop
  left_inv := fiberLoop_endpointFiber
  right_inv := endpointFiber_fiberLoop

def endpointMulEquiv : FundamentalGroup UnitCircle 0 ≃* Multiplicative CircleFiber where
  toEquiv := endpointEquiv.trans (Multiplicative.ofAdd : CircleFiber ≃ Multiplicative CircleFiber)
  map_mul' := by
    intro g h
    change endpointFiber (g * h) = endpointFiber g + endpointFiber h
    exact endpointFiber_mul g h

def intFiberHom : ℤ →+ ℝ := (zmultiplesHom ℝ) 1

theorem intFiberHom_injective : Function.Injective intFiberHom := by
  intro a b h
  exact_mod_cast (show (a : ℝ) = b by
    simpa only [intFiberHom, zmultiplesHom_apply, zsmul_one] using h)

def intFiberAddEquiv : ℤ ≃+ CircleFiber := by
  let f : ℤ →+ CircleFiber := intFiberHom.codRestrict CircleFiber (fun n => by
    change (zmultiplesHom ℝ) 1 n ∈ zmultiples (1 : ℝ)
    rw [← AddSubgroup.range_zmultiplesHom]
    exact ⟨n, rfl⟩)
  apply AddEquiv.ofBijective f
  constructor
  · intro a b hab
    apply intFiberHom_injective
    exact congrArg Subtype.val hab
  · intro z
    have hz : z.1 ∈ intFiberHom.range := by
      change z.1 ∈ ((zmultiplesHom ℝ) 1).range
      rw [AddSubgroup.range_zmultiplesHom]
      exact z.2
    rcases hz with ⟨n, hn⟩
    exact ⟨n, Subtype.ext hn⟩

theorem intFiberAddEquiv_coe (n : ℤ) :
    ((intFiberAddEquiv n : CircleFiber) : ℝ) = n := by
  change intFiberHom n = n
  simp [intFiberHom, zmultiplesHom_apply]

def intFiberMulEquiv : Multiplicative ℤ ≃* Multiplicative CircleFiber :=
  intFiberAddEquiv.toMultiplicative

/-- The fundamental group of the additive unit circle is infinite cyclic. -/
def circleFundamentalGroupMulEquiv :
    FundamentalGroup UnitCircle 0 ≃* Multiplicative ℤ :=
  endpointMulEquiv.trans intFiberMulEquiv.symm

/-- The loop on `ℝ / ℤ` with winding number `n`. -/
def unitCircleWindingLoop (n : ℤ) : Path (0 : UnitCircle) 0 where
  toFun t := (((t : ℝ) * (n : ℝ) : ℝ) : UnitCircle)
  continuous_toFun := AddCircle.continuous_mk' 1 |>.comp
    (continuous_subtype_val.mul continuous_const)
  source' := by simp
  target' := by
    rw [show ((1 : unitInterval) : ℝ) * (n : ℝ) = n by simp]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨n, by simp⟩

private def realWindingLift (n : ℤ) : C(↑unitInterval, ℝ) :=
  ⟨fun t => (t : ℝ) * (n : ℝ), continuous_subtype_val.mul continuous_const⟩

/-- The lift of the winding-`n` loop ends at the integer `n`. -/
theorem endpointFiber_windingLoop (n : ℤ) :
    endpointFiber (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (unitCircleWindingLoop n))) =
      intFiberAddEquiv n := by
  apply Subtype.ext
  rw [endpointFiber_fromPath]
  have hLift : realWindingLift n =
      unitCircleCov.liftPath
        (unitCircleWindingLoop n : C(↑unitInterval, UnitCircle)) 0 (by simp) := by
    apply (unitCircleCov.eq_liftPath_iff' (by simp)).mpr
    constructor
    · funext t
      rfl
    · simp [realWindingLift]
  rw [← hLift]
  rw [show realWindingLift n 1 = (n : ℝ) by simp [realWindingLift]]
  exact (intFiberAddEquiv_coe n).symm

/-- The winding-`n` loop represents the integer `n` in `π₁(ℝ / ℤ, 0)`. -/
theorem circleFundamentalGroupMulEquiv_windingLoop (n : ℤ) :
    circleFundamentalGroupMulEquiv
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (unitCircleWindingLoop n))) =
      Multiplicative.ofAdd n := by
  change Multiplicative.ofAdd
      (intFiberAddEquiv.symm
        (endpointFiber (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (unitCircleWindingLoop n))))) = _
  rw [endpointFiber_windingLoop]
  simp

def unitCircleGeometricMulEquiv :
    FundamentalGroup UnitCircle 0 ≃* FundamentalGroup Circle (1 : Circle) := by
  let e := FundamentalGroupoidFunctor.equivOfHomotopyEquiv
    (AddCircle.homeomorphCircle one_ne_zero).toHomotopyEquiv
  let πe : FundamentalGroup UnitCircle 0 ≃*
      FundamentalGroup Circle (AddCircle.homeomorphCircle one_ne_zero 0) :=
    e.fullyFaithfulFunctor.mulEquivEnd (FundamentalGroupoid.mk 0)
  have h0 : AddCircle.homeomorphCircle one_ne_zero (0 : UnitCircle) = (1 : Circle) := by
    simp [AddCircle.homeomorphCircle_apply]
  exact πe.trans (MulEquiv.cast (M := fun z : Circle => FundamentalGroup Circle z) h0)

/-- The fundamental group of the geometric complex unit circle is infinite cyclic. -/
def geometricCircleFundamentalGroupMulEquiv :
    FundamentalGroup Circle (1 : Circle) ≃* Multiplicative ℤ :=
  unitCircleGeometricMulEquiv.symm.trans circleFundamentalGroupMulEquiv

/-- Hatcher's path-order fundamental group of the geometric circle is infinite
cyclic. -/
def geometricCirclePiOneMulEquiv : PiOne (1 : Circle) ≃* Multiplicative ℤ :=
  (MulEquiv.op geometricCircleFundamentalGroupMulEquiv).trans
    MulOpposite.opMulEquiv.symm

/-- The geometric loop `t ↦ exp(2πint)` on the complex unit circle. -/
def geometricCircleWindingLoop (n : ℤ) : Path (1 : Circle) 1 where
  toFun t := Circle.exp (2 * Real.pi * ((t : ℝ) * (n : ℝ)))
  continuous_toFun := Circle.exp.continuous.comp
    (continuous_const.mul (continuous_subtype_val.mul continuous_const))
  source' := by simp
  target' := by simpa using Circle.exp_two_pi_mul_int n

private def geometricCircleWindingLoopFromUnit (n : ℤ) : Path (1 : Circle) 1 :=
  ((unitCircleWindingLoop n).map
      (AddCircle.homeomorphCircle one_ne_zero).continuous).cast
    (by simp [AddCircle.homeomorphCircle_apply])
    (by simp [AddCircle.homeomorphCircle_apply])

private theorem geometricCircleWindingLoopFromUnit_eq (n : ℤ) :
    geometricCircleWindingLoopFromUnit n = geometricCircleWindingLoop n := by
  apply Path.ext
  funext t
  simp [geometricCircleWindingLoopFromUnit, geometricCircleWindingLoop,
    unitCircleWindingLoop, AddCircle.homeomorphCircle_apply,
    AddCircle.toCircle_apply_mk]

private theorem cast_fundamentalGroup_eq_pathCast
    {X : Type*} [TopologicalSpace X] {x y : X} (h : x = y)
    (q : FundamentalGroup X x) :
    cast (congrArg (fun z => FundamentalGroup X z) h) q =
      (FundamentalGroup.toPath q).cast h.symm h.symm := by
  cases h
  change q = (FundamentalGroup.toPath q).cast rfl rfl
  exact (Path.Homotopic.Quotient.cast_rfl_rfl q).symm

/-- The homeomorphism `ℝ / ℤ ≃ S¹` sends the additive winding loop to the
geometric exponential loop with the same winding number. -/
theorem unitCircleGeometricMulEquiv_windingLoop (n : ℤ) :
    unitCircleGeometricMulEquiv
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (unitCircleWindingLoop n))) =
    FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop n)) := by
  rw [← geometricCircleWindingLoopFromUnit_eq]
  dsimp [unitCircleGeometricMulEquiv,
    FundamentalGroupoidFunctor.equivOfHomotopyEquiv,
    CategoryTheory.Equivalence.mk,
    CategoryTheory.Functor.FullyFaithful.mulEquivEnd,
    CategoryTheory.Functor.FullyFaithful.homEquiv]
  let e := AddCircle.homeomorphCircle one_ne_zero
  let f : C(UnitCircle, Circle) := e.toHomotopyEquiv.toFun
  have h0 : f (0 : UnitCircle) = (1 : Circle) := by
    simp [f, e, AddCircle.homeomorphCircle_apply]
  change cast (congrArg (fun z => FundamentalGroup Circle z) h0)
      ((Path.Homotopic.Quotient.mk (unitCircleWindingLoop n)).map f) = _
  rw [cast_fundamentalGroup_eq_pathCast h0,
    ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast]
  rfl

/-- The explicit loop `t ↦ exp(2πint)` represents `n` in `π₁(S¹, 1)`. -/
theorem geometricCircleFundamentalGroupMulEquiv_windingLoop (n : ℤ) :
    geometricCircleFundamentalGroupMulEquiv
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop n))) =
      Multiplicative.ofAdd n := by
  change circleFundamentalGroupMulEquiv
    (unitCircleGeometricMulEquiv.symm
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop n)))) = _
  rw [← unitCircleGeometricMulEquiv_windingLoop n]
  simpa using circleFundamentalGroupMulEquiv_windingLoop n

/-- In Hatcher's multiplication convention, the geometric winding loop still
represents exactly its signed winding number. -/
theorem geometricCirclePiOneMulEquiv_windingLoop (n : ℤ) :
    geometricCirclePiOneMulEquiv (piOneClass (geometricCircleWindingLoop n)) =
      Multiplicative.ofAdd n := by
  change geometricCircleFundamentalGroupMulEquiv
    (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop n))) = _
  exact geometricCircleFundamentalGroupMulEquiv_windingLoop n

/-- The fundamental group of the two-dimensional torus is `ℤ × ℤ`. -/
def torusFundamentalGroupMulEquiv :
    FundamentalGroup (Circle × Circle) ((1 : Circle), (1 : Circle)) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).symm.trans
    (MulEquiv.prodCongr geometricCircleFundamentalGroupMulEquiv
      geometricCircleFundamentalGroupMulEquiv)

/-- Hatcher's path-order fundamental group of the two-dimensional torus is
`ℤ × ℤ`. -/
def torusPiOneMulEquiv :
    PiOne ((1 : Circle), (1 : Circle)) ≃*
      Multiplicative ℤ × Multiplicative ℤ :=
  (piOneProdMulEquiv (1 : Circle) (1 : Circle)).symm.trans
    (MulEquiv.prodCongr geometricCirclePiOneMulEquiv
      geometricCirclePiOneMulEquiv)

/-- The torus loop whose two coordinates have winding numbers `p` and `q`. -/
def torusWindingLoop (p q : ℤ) :
    Path ((1 : Circle), (1 : Circle)) ((1 : Circle), (1 : Circle)) :=
  (geometricCircleWindingLoop p).prod (geometricCircleWindingLoop q)

/-- The coordinate winding loop on the torus represents `(p, q)`. -/
theorem torusFundamentalGroupMulEquiv_windingLoop (p q : ℤ) :
    torusFundamentalGroupMulEquiv
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (torusWindingLoop p q))) =
      (Multiplicative.ofAdd p, Multiplicative.ofAdd q) := by
  change (geometricCircleFundamentalGroupMulEquiv
      ((fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).symm
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (torusWindingLoop p q)))).1,
    geometricCircleFundamentalGroupMulEquiv
      ((fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)).symm
        (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (torusWindingLoop p q)))).2) = _
  rw [← show fundamentalGroupProdMulEquiv (1 : Circle) (1 : Circle)
      (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop p)),
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop q))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (torusWindingLoop p q)) by rfl]
  simp only [MulEquiv.symm_apply_apply]
  rw [geometricCircleFundamentalGroupMulEquiv_windingLoop,
    geometricCircleFundamentalGroupMulEquiv_windingLoop]

/-- In Hatcher's convention, the coordinate winding loop represents `(p,q)`. -/
theorem torusPiOneMulEquiv_windingLoop (p q : ℤ) :
    torusPiOneMulEquiv (piOneClass (torusWindingLoop p q)) =
      (Multiplicative.ofAdd p, Multiplicative.ofAdd q) := by
  change (geometricCirclePiOneMulEquiv
      ((piOneProdMulEquiv (1 : Circle) (1 : Circle)).symm
        (piOneClass (torusWindingLoop p q))).1,
    geometricCirclePiOneMulEquiv
      ((piOneProdMulEquiv (1 : Circle) (1 : Circle)).symm
        (piOneClass (torusWindingLoop p q))).2) = _
  rw [← show piOneProdMulEquiv (1 : Circle) (1 : Circle)
      (piOneClass (geometricCircleWindingLoop p),
        piOneClass (geometricCircleWindingLoop q)) =
      piOneClass (torusWindingLoop p q) by rfl]
  simp only [MulEquiv.symm_apply_apply]
  rw [geometricCirclePiOneMulEquiv_windingLoop,
    geometricCirclePiOneMulEquiv_windingLoop]

/-- The fundamental group of a product of spaces is the product of their
fundamental groups, for an arbitrary indexed family. -/
def fundamentalGroupPiMulEquiv {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (x₀ : ∀ i, X i) :
    (∀ i, FundamentalGroup (X i) (x₀ i)) ≃*
      FundamentalGroup (∀ i, X i) x₀ where
  toFun p := Path.Homotopic.pi p
  invFun g := fun i => Path.Homotopic.proj i (FundamentalGroup.toPath g)
  left_inv p := by
    funext i
    exact Path.Homotopic.proj_pi i p
  right_inv g := Path.Homotopic.pi_proj _
  map_mul' p q := (Path.Homotopic.comp_pi_eq_pi_comp q p).symm

/-- Opposite groups commute with arbitrary products. -/
def mulOppositePiMulEquiv {ι : Type*} (G : ι → Type*) [∀ i, Group (G i)] :
    (∀ i, MulOpposite (G i)) ≃* MulOpposite (∀ i, G i) where
  toFun x := MulOpposite.op (fun i => (x i).unop)
  invFun x i := MulOpposite.op (x.unop i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Hatcher's path-order fundamental group commutes with arbitrary products. -/
def piOnePiMulEquiv {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] (x₀ : ∀ i, X i) :
    (∀ i, PiOne (x₀ i)) ≃* PiOne x₀ :=
  (mulOppositePiMulEquiv
    (fun i => FundamentalGroup (X i) (x₀ i))).trans
      (MulEquiv.op (fundamentalGroupPiMulEquiv x₀))

/-- A finite product of complex unit circles. -/
abbrev FiniteTorus (n : ℕ) := Fin n → Circle

/-- The fundamental group of the `n`-torus is `ℤⁿ`. -/
def finiteTorusFundamentalGroupMulEquiv (n : ℕ) :
    FundamentalGroup (FiniteTorus n) (fun _ => (1 : Circle)) ≃*
      (Fin n → Multiplicative ℤ) :=
  (fundamentalGroupPiMulEquiv (fun _ : Fin n => (1 : Circle))).symm.trans
    (MulEquiv.piCongrRight fun _ => geometricCircleFundamentalGroupMulEquiv)

/-- In Hatcher's convention, the fundamental group of the `n`-torus is `ℤⁿ`. -/
def finiteTorusPiOneMulEquiv (n : ℕ) :
    PiOne (fun _ : Fin n => (1 : Circle)) ≃*
      (Fin n → Multiplicative ℤ) :=
  (piOnePiMulEquiv (fun _ : Fin n => (1 : Circle))).symm.trans
    (MulEquiv.piCongrRight fun _ => geometricCirclePiOneMulEquiv)

/-- The loop on the `n`-torus with coordinate winding vector `w`. -/
def finiteTorusWindingLoop {n : ℕ} (w : Fin n → ℤ) :
    Path (fun _ : Fin n => (1 : Circle)) (fun _ : Fin n => (1 : Circle)) :=
  Path.pi (fun i => geometricCircleWindingLoop (w i))

/-- A coordinate winding vector represents the same integer vector in
`π₁((S¹)ⁿ)`. -/
theorem finiteTorusFundamentalGroupMulEquiv_windingLoop
    {n : ℕ} (w : Fin n → ℤ) :
    finiteTorusFundamentalGroupMulEquiv n
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (finiteTorusWindingLoop w))) =
      fun i => Multiplicative.ofAdd (w i) := by
  change (fun i => geometricCircleFundamentalGroupMulEquiv
    (((fundamentalGroupPiMulEquiv (fun _ : Fin n => (1 : Circle))).symm
      (FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (finiteTorusWindingLoop w)))) i)) = _
  rw [← show fundamentalGroupPiMulEquiv (fun _ : Fin n => (1 : Circle))
      (fun i => FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (geometricCircleWindingLoop (w i)))) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk (finiteTorusWindingLoop w)) by
      exact Path.Homotopic.pi_lift _]
  simp only [MulEquiv.symm_apply_apply]
  funext i
  exact geometricCircleFundamentalGroupMulEquiv_windingLoop (w i)

/-- Coordinate winding vectors give the corresponding elements of `ℤⁿ` in
Hatcher's path-order convention. -/
theorem finiteTorusPiOneMulEquiv_windingLoop {n : ℕ} (w : Fin n → ℤ) :
    finiteTorusPiOneMulEquiv n (piOneClass (finiteTorusWindingLoop w)) =
      fun i => Multiplicative.ofAdd (w i) := by
  change (fun i => geometricCirclePiOneMulEquiv
    (((piOnePiMulEquiv (fun _ : Fin n => (1 : Circle))).symm
      (piOneClass (finiteTorusWindingLoop w))) i)) = _
  rw [← show piOnePiMulEquiv (fun _ : Fin n => (1 : Circle))
      (fun i => piOneClass (geometricCircleWindingLoop (w i))) =
      piOneClass (finiteTorusWindingLoop w) by
      apply MulOpposite.unop_injective
      exact Path.Homotopic.pi_lift _]
  simp only [MulEquiv.symm_apply_apply]
  funext i
  exact geometricCirclePiOneMulEquiv_windingLoop (w i)

end
end HatcherLib

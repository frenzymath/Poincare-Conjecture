import HatcherLib.Ch0.HomotopyTheory
import HatcherLib.Ch1.BasicConstructions
import HatcherLib.Ch1.BasedHomotopy
import HatcherLib.Ch1.Circle
import HatcherLib.Ch1.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Chapter 1: fundamental-group functoriality applications

These are the elementary consequences used around the retract and homotopy
equivalence examples in Hatcher's first chapter.
-/

namespace HatcherLib

noncomputable section

open scoped ContinuousMap RealInnerProductSpace
open CategoryTheory

universe u v

variable {X : Type u} {Y : Type v}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- A homotopy equivalence induces an isomorphism on fundamental groups. -/
def homotopyEquivPiOneMulEquiv (e : X ≃ₕ Y) (x : X) :
    PiOne x ≃* PiOne (e x) :=
  MulEquiv.op
    ((FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
      (FundamentalGroupoid.mk x))

theorem homotopyEquivPiOneMulEquiv_apply (e : X ≃ₕ Y) (x : X)
    (g : PiOne x) :
    homotopyEquivPiOneMulEquiv e x g = inducedPiOne e.toFun x g :=
  rfl

variable {f g : C(X, Y)}

theorem fundamentalGroupoid_inv {a b : Y}
    (h : Path.Homotopic.Quotient a b) :
    (Groupoid.inv (h : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) :
      FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk a) =
      (h.symm : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk a) := by
  induction h using Path.Homotopic.Quotient.ind with
  | mk p => rfl

private theorem fundamentalGroup_map_homotopy_eq_changeBasepoint
    (F : f.Homotopy g) (x : X) :
    FundamentalGroup.map f x =
      (FundamentalGroup.fundamentalGroupMulEquivOfPath
        (F.evalAt x).symm).toMonoidHom.comp
        (FundamentalGroup.map g x) := by
  ext z
  apply (cancel_mono (Path.Homotopic.Quotient.mk (F.evalAt x))).1
  have hn := (FundamentalGroupoidFunctor.homotopicMapsNatIso F).naturality z
  have hn' :
      (FundamentalGroup.map f x) z ≫ Path.Homotopic.Quotient.mk (F.evalAt x) =
        Path.Homotopic.Quotient.mk (F.evalAt x) ≫ (FundamentalGroup.map g x) z := by
    convert hn using 1 <;> rfl
  rw [hn']
  change Path.Homotopic.Quotient.mk (F.evalAt x) ≫ (FundamentalGroup.map g x) z =
    (Groupoid.inv ((Path.Homotopic.Quotient.mk (F.evalAt x)).symm) ≫
      (FundamentalGroup.map g x) z ≫
      (Path.Homotopic.Quotient.mk (F.evalAt x)).symm) ≫
        Path.Homotopic.Quotient.mk (F.evalAt x)
  rw [← Path.Homotopic.Quotient.mk_symm]
  simp [FundamentalGroupoid.comp_eq]
  have hsymm :
      ((Path.Homotopic.Quotient.mk (F.evalAt x)).symm :
        Path.Homotopic.Quotient (g x) (f x)) =
      (Groupoid.inv
        (Path.Homotopic.Quotient.mk (F.evalAt x) :
          FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk (g x)) :
        FundamentalGroupoid.mk (g x) ⟶ FundamentalGroupoid.mk (f x)) := by
    rfl
  rw [hsymm]
  simp

/-- An unbased homotopy changes the induced map by conjugation along the path
traced by the basepoint. -/
theorem inducedPiOne_homotopy_eq_changeBasepoint
    (F : f.Homotopy g) (x : X) :
    inducedPiOne f x =
      (changeBasepoint (F.evalAt x)).toMonoidHom.comp
        (inducedPiOne g x) := by
  ext z
  apply MulOpposite.unop_injective
  exact DFunLike.congr_fun
    (fundamentalGroup_map_homotopy_eq_changeBasepoint F x) (MulOpposite.unop z)

variable {A : Type u} [TopologicalSpace A]

private theorem fundamentalGroup_retract_map_injective
    (i : C(A, X)) (r : C(X, A)) (hri : r.comp i = ContinuousMap.id A) (a₀ : A) :
    Function.Injective (FundamentalGroup.map i a₀) := by
  intro g h hgh
  have hbase : r (i a₀) = a₀ := by
    simpa using congrArg (fun f : C(A, A) => f a₀) hri
  have hcomp :
      FundamentalGroup.mapOfEq r hbase (FundamentalGroup.map i a₀ g) =
        FundamentalGroup.mapOfEq r hbase (FundamentalGroup.map i a₀ h) :=
    congrArg (FundamentalGroup.mapOfEq r hbase) hgh
  have hhom :
      (FundamentalGroup.mapOfEq r hbase).comp (FundamentalGroup.map i a₀) =
        FundamentalGroup.map (ContinuousMap.id A) a₀ := by
    apply MonoidHom.ext
    intro z
    obtain ⟨γ, rfl⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath z)
    change FundamentalGroup.mapOfEq r hbase
        (FundamentalGroup.map i a₀ (FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk γ))) =
      FundamentalGroup.map (ContinuousMap.id A) a₀
        (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ))
    rw [FundamentalGroup.map_apply, FundamentalGroup.map_apply]
    rw [← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map]
    rw [FundamentalGroup.mapOfEq_apply]
    apply Quotient.sound
    change (((γ.map i.continuous).map r.continuous).cast hbase.symm hbase.symm).Homotopic
      (γ.map (ContinuousMap.id A).continuous)
    rw [show ((γ.map i.continuous).map r.continuous).cast hbase.symm hbase.symm =
        γ.map (ContinuousMap.id A).continuous by
      apply Path.ext
      funext t
      have ht := congrArg (fun f : C(A, A) => f (γ t)) hri
      change r (i (γ t)) = γ t
      exact ht]
  have hid (z : FundamentalGroup A a₀) :
      FundamentalGroup.map (ContinuousMap.id A) a₀ z = z := by
    obtain ⟨γ, rfl⟩ :=
      Path.Homotopic.Quotient.mk_surjective (FundamentalGroup.toPath z)
    rw [FundamentalGroup.map_apply, ← Path.Homotopic.Quotient.mk_map]
    apply congrArg Path.Homotopic.Quotient.mk
    apply Path.ext
    rfl
  have hcomp' :
      FundamentalGroup.mapOfEq r hbase (FundamentalGroup.map i a₀ g) = g := by
    rw [show FundamentalGroup.mapOfEq r hbase (FundamentalGroup.map i a₀ g) =
      ((FundamentalGroup.mapOfEq r hbase).comp (FundamentalGroup.map i a₀)) g by rfl,
      hhom]
    exact hid g
  have hcomp'' :
      FundamentalGroup.mapOfEq r hbase (FundamentalGroup.map i a₀ h) = h := by
    rw [show FundamentalGroup.mapOfEq r hbase (FundamentalGroup.map i a₀ h) =
      ((FundamentalGroup.mapOfEq r hbase).comp (FundamentalGroup.map i a₀)) h by rfl,
      hhom]
    exact hid h
  rw [hcomp', hcomp''] at hcomp
  exact hcomp

/-- A retraction induces a left inverse, hence an injection, on fundamental groups. -/
theorem retract_inducedPiOne_injective
    (i : C(A, X)) (r : C(X, A)) (hri : r.comp i = ContinuousMap.id A) (a₀ : A) :
    Function.Injective (inducedPiOne i a₀) := by
  intro g h hgh
  apply MulOpposite.unop_injective
  apply fundamentalGroup_retract_map_injective i r hri a₀
  exact congrArg MulOpposite.unop hgh

/-- A deformation-retract inclusion induces an isomorphism on fundamental groups. -/
def deformationRetractPiOneMulEquiv
    (i : C(A, X)) (hi : IsDeformationRetractIncl i) (a₀ : A) :
    PiOne a₀ ≃* PiOne (i a₀) :=
  homotopyEquivPiOneMulEquiv hi.isHmtpyEquiv.toHomotopyEquiv a₀

/-! ## The circle is not a retract of the disk -/

/-- The closed unit disk in the complex plane. -/
abbrev ComplexClosedUnitDisk := Metric.closedBall (0 : ℂ) 1

/-!
The real Euclidean model of the two-dimensional closed disk.  The explicit
coordinate identification below uses the orthonormal basis `1, I` of `ℂ`.
-/

/-- The closed unit disk in `EuclideanSpace ℝ (Fin 2)`. -/
abbrev EuclideanClosedUnitDisk :=
  Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The orthonormal-basis identification restricts to a homeomorphism of
the real and complex closed unit disks. -/
noncomputable def euclideanClosedUnitDiskHomeomorphComplexClosedUnitDisk :
    EuclideanClosedUnitDisk ≃ₜ ComplexClosedUnitDisk :=
  (Complex.orthonormalBasisOneI.repr.symm.toHomeomorph).subtype (by
    intro x
    constructor
    · intro hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
      change ‖Complex.orthonormalBasisOneI.repr.symm x‖ ≤ 1
      rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
      exact hx
    · intro hx
      rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
      change ‖Complex.orthonormalBasisOneI.repr.symm x‖ ≤ 1 at hx
      rw [Complex.orthonormalBasisOneI.repr.symm.norm_map] at hx
      exact hx)

/-- The boundary-circle inclusion into the closed unit disk. -/
def circleInclComplexClosedUnitDisk : C(Circle, ComplexClosedUnitDisk) where
  toFun z := ⟨z, by
    rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]⟩
  continuous_toFun :=
    continuous_subtype_val.subtype_mk fun z => by
      rw [Metric.mem_closedBall, dist_zero_right, Circle.norm_coe]

/-- The unit circle is not a retract of the closed unit disk.  A retraction
would inject the infinite cyclic fundamental group of the circle into the
trivial fundamental group of the contractible disk. -/
theorem circle_not_retract_complexClosedUnitDisk
    (r : C(ComplexClosedUnitDisk, Circle))
    (hri : r.comp circleInclComplexClosedUnitDisk = ContinuousMap.id Circle) : False := by
  have hinj : Function.Injective
      (inducedPiOne circleInclComplexClosedUnitDisk (1 : Circle)) :=
    retract_inducedPiOne_injective circleInclComplexClosedUnitDisk r hri (1 : Circle)
  letI : ContractibleSpace ComplexClosedUnitDisk :=
    Metric.contractibleSpace_closedBall (x := (0 : ℂ)) (r := 1) (by norm_num)
  let a : PiOne (1 : Circle) :=
    MulOpposite.op
      (geometricCircleFundamentalGroupMulEquiv.symm
        (Multiplicative.ofAdd (0 : ℤ)))
  let b : PiOne (1 : Circle) :=
    MulOpposite.op
      (geometricCircleFundamentalGroupMulEquiv.symm
        (Multiplicative.ofAdd (1 : ℤ)))
  have hab : a = b := hinj
    ((contractible_piOne_subsingleton
      (circleInclComplexClosedUnitDisk (1 : Circle))).elim _ _)
  have hz := congrArg
    (fun q : PiOne (1 : Circle) =>
      geometricCircleFundamentalGroupMulEquiv (MulOpposite.unop q)) hab
  dsimp only [a, b, MulOpposite.unop_op] at hz
  simp only [MulEquiv.apply_symm_apply] at hz
  have hz' : (0 : ℤ) = 1 :=
    congrArg (fun z : Multiplicative ℤ => z.toAdd) hz
  exact zero_ne_one hz'

/-! ## Brouwer's fixed-point theorem for the complex disk -/

/-
The ray from a point `a` in the disk through a distinct point `b` meets the
unit circle at the parameter below.  The formula is useful here because its
denominator is nonzero precisely under the fixed-point-free hypothesis.
-/
noncomputable def complexDiskRayExitParam (a b : ℂ) : ℝ :=
  let v := b - a
  let A := ‖v‖ ^ 2
  let d := ⟪a, v⟫
  (-d + Real.sqrt (d ^ 2 + A * (1 - ‖a‖ ^ 2))) / A

private theorem norm_add_real_smul_sq (a v : ℂ) (t : ℝ) :
    ‖a + t • v‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * t * ⟪a, v⟫ + t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
  simp only [Real.norm_eq_abs]
  nlinarith [sq_abs t]

private theorem complexDiskRayExitParam_mem_sphere {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hab : a ≠ b) :
    ‖a + complexDiskRayExitParam a b • (b - a)‖ = 1 := by
  let v := b - a
  let A := ‖v‖ ^ 2
  let d := ⟪a, v⟫
  let q := d ^ 2 + A * (1 - ‖a‖ ^ 2)
  have hv : v ≠ 0 := sub_ne_zero.mpr hab.symm
  have hA : 0 < A := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hq : 0 ≤ q := by
    dsimp only [q]
    positivity
  have hsqrt : (Real.sqrt q)^2 = q := Real.sq_sqrt hq
  have hcalc :
      ‖a‖^2 + 2*((-d+Real.sqrt q)/A)*d +
          ((-d+Real.sqrt q)/A)^2*A = 1 := by
    field_simp [ne_of_gt hA]
    nlinarith
  have hnormsq :
      ‖a + complexDiskRayExitParam a b • (b-a)‖ ^ 2 = 1 := by
    dsimp only [complexDiskRayExitParam, v, A, d, q]
    rw [norm_add_real_smul_sq]
    exact hcalc
  nlinarith [hnormsq,
    norm_nonneg (a + complexDiskRayExitParam a b • (b-a))]

private theorem complexDiskRayExitParam_eq_one {a b : ℂ}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ = 1) (hab : a ≠ b) :
    complexDiskRayExitParam a b = 1 := by
  let v := b - a
  let A := ‖v‖ ^ 2
  let d := ⟪a, v⟫
  let q := d ^ 2 + A * (1 - ‖a‖ ^ 2)
  have hv : v ≠ 0 := sub_ne_zero.mpr hab.symm
  have hA : 0 < A := sq_pos_of_pos (norm_pos_iff.mpr hv)
  have ha2 : ‖a‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg a]
  have hboundaryEq : ‖a‖ ^ 2 + 2*d + A = 1 := by
    have hh := norm_add_sq_real a v
    have hh' : ‖b‖ ^ 2 = ‖a‖ ^ 2 + 2*d + A := by
      simpa [v, A, d] using hh
    rw [hb] at hh'
    nlinarith [hh']
  have hAd : 0 ≤ A + d := by
    nlinarith [sq_nonneg (‖v‖), ha2]
  have hqeq : q = (A+d)^2 := by
    dsimp only [q]
    nlinarith [hboundaryEq]
  change (-d + Real.sqrt q) / A = 1
  rw [hqeq, Real.sqrt_sq hAd]
  field_simp [ne_of_gt hA]
  ring

private noncomputable def complexDiskRayBoundaryPoint
    (h : C(ComplexClosedUnitDisk, ComplexClosedUnitDisk))
    (hfix : ∀ x, h x ≠ x) (x : ComplexClosedUnitDisk) : Circle :=
  ⟨(h x : ℂ) + complexDiskRayExitParam (h x : ℂ) (x : ℂ) •
      ((x : ℂ) - (h x : ℂ)), by
    change (h x : ℂ) + complexDiskRayExitParam (h x : ℂ) (x : ℂ) •
      ((x : ℂ) - (h x : ℂ)) ∈ Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm]
    apply complexDiskRayExitParam_mem_sphere
    · have hx := Metric.mem_closedBall.mp (h x).property
      simpa [dist_zero_right] using hx
    · intro heq
      apply hfix x
      apply Subtype.ext
      exact heq⟩

private noncomputable def complexDiskFixedPointFreeRetraction
    (h : C(ComplexClosedUnitDisk, ComplexClosedUnitDisk))
    (hfix : ∀ x, h x ≠ x) : C(ComplexClosedUnitDisk, Circle) where
  toFun := complexDiskRayBoundaryPoint h hfix
  continuous_toFun := by
    change Continuous (fun x : ComplexClosedUnitDisk =>
      (⟨(h x : ℂ) + complexDiskRayExitParam (h x : ℂ) (x : ℂ) •
        ((x : ℂ) - (h x : ℂ)), _⟩ : Circle))
    apply Continuous.subtype_mk
    have hp : Continuous (fun x : ComplexClosedUnitDisk =>
        complexDiskRayExitParam (h x : ℂ) (x : ℂ)) := by
      unfold complexDiskRayExitParam
      apply Continuous.div
      · have hd : Continuous (fun x : ComplexClosedUnitDisk =>
            ⟪(h x : ℂ), (x : ℂ) - (h x : ℂ)⟫) := by
          simp only [Complex.inner]
          fun_prop
        fun_prop (disch := exact hd)
      · fun_prop
      · intro x
        apply pow_ne_zero 2
        apply norm_ne_zero_iff.mpr
        apply sub_ne_zero.mpr
        intro heq
        apply hfix x
        apply Subtype.ext
        exact heq.symm
    fun_prop (disch := exact hp)

private theorem complexDiskFixedPointFreeRetraction_comp
    (h : C(ComplexClosedUnitDisk, ComplexClosedUnitDisk))
    (hfix : ∀ x, h x ≠ x) :
    (complexDiskFixedPointFreeRetraction h hfix).comp
        circleInclComplexClosedUnitDisk = ContinuousMap.id Circle := by
  apply ContinuousMap.ext
  intro z
  apply Circle.ext
  have ha : ‖(h (circleInclComplexClosedUnitDisk z) : ℂ)‖ ≤ 1 := by
    have hx := Metric.mem_closedBall.mp (h (circleInclComplexClosedUnitDisk z)).property
    simpa [dist_zero_right] using hx
  have hb : ‖(z : ℂ)‖ = 1 := Circle.norm_coe z
  have hab : (h (circleInclComplexClosedUnitDisk z) : ℂ) ≠ (z : ℂ) := by
    intro heq
    apply hfix (circleInclComplexClosedUnitDisk z)
    apply Subtype.ext
    exact heq
  change (h (circleInclComplexClosedUnitDisk z) : ℂ) +
      complexDiskRayExitParam (h (circleInclComplexClosedUnitDisk z) : ℂ)
        (z : ℂ) • ((z : ℂ) - (h (circleInclComplexClosedUnitDisk z) : ℂ)) = (z : ℂ)
  rw [complexDiskRayExitParam_eq_one ha hb hab]
  simp

/-- Every continuous self-map of the closed complex unit disk has a fixed point.

This is the two-dimensional Brouwer fixed-point theorem, obtained by sending a
hypothetical fixed-point-free map to the ray exit retraction of the disk onto
its boundary and applying the no-retraction theorem above.
-/
theorem complexClosedUnitDisk_exists_fixedPoint
    (h : C(ComplexClosedUnitDisk, ComplexClosedUnitDisk)) :
    ∃ x, h x = x := by
  by_contra hn
  have hfix : ∀ x, h x ≠ x := by
    intro x hx
    exact hn ⟨x, hx⟩
  exact circle_not_retract_complexClosedUnitDisk
    (complexDiskFixedPointFreeRetraction h hfix)
    (complexDiskFixedPointFreeRetraction_comp h hfix)

/-! ## Brouwer's fixed-point theorem in the real Euclidean plane -/

/-- Every continuous self-map of the real Euclidean closed unit disk has a
fixed point.  This is obtained by conjugating the complex-disk theorem along
the orthonormal-basis homeomorphism above. -/
theorem euclideanClosedUnitDisk_exists_fixedPoint
    (h : C(EuclideanClosedUnitDisk, EuclideanClosedUnitDisk)) :
    ∃ x, h x = x := by
  let e : EuclideanClosedUnitDisk ≃ₜ ComplexClosedUnitDisk :=
    euclideanClosedUnitDiskHomeomorphComplexClosedUnitDisk
  let e' : C(EuclideanClosedUnitDisk, ComplexClosedUnitDisk) :=
    ⟨e, e.continuous⟩
  let eInv' : C(ComplexClosedUnitDisk, EuclideanClosedUnitDisk) :=
    ⟨e.symm, e.symm.continuous⟩
  let g : C(ComplexClosedUnitDisk, ComplexClosedUnitDisk) :=
    e'.comp (h.comp eInv')
  obtain ⟨z, hz⟩ := complexClosedUnitDisk_exists_fixedPoint g
  refine ⟨e.symm z, ?_⟩
  have hz' := congrArg e.symm hz
  simp [g, e', eInv', ContinuousMap.comp_apply] at hz'
  exact hz'

end
end HatcherLib

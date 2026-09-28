import Mathlib.Analysis.Normed.Module.Basic
import HatcherLib.Ch0.HomotopyExtension

/-!
# Chapter 0 — The boundary of a cell has the homotopy extension property

This file proves the point-set input used when cells are attached: the boundary
of the closed unit ball in a real normed space has the homotopy extension
property.  The proof is Hatcher's radial retraction of `D × I` onto
`D × {0} ∪ S × I`, projecting from the external point `(0, 2)`.
-/

namespace HatcherLib

open scoped unitInterval

universe u v

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed unit ball, regarded as the model closed cell. -/
abbrev ClosedUnitBall := Metric.closedBall (0 : E) 1

/-- The boundary sphere as a subset of the model closed cell. -/
def CellBoundary : Set (ClosedUnitBall E) :=
  {x | ‖(x : E)‖ = 1}

section Coordinates

variable {E}

/-- The globally nonzero denominator used in the side-exit branch of the radial
projection.  On that branch it is exactly `‖x‖`. -/
noncomputable def cellHepDenom (p : ClosedUnitBall E × I) : ℝ :=
  max ‖(p.1 : E)‖ ((2 - (p.2 : ℝ)) / 2)

omit [NormedSpace ℝ E] in
theorem cellHepDenom_pos (p : ClosedUnitBall E × I) : 0 < cellHepDenom p := by
  apply lt_max_of_lt_right
  have ht := unitInterval.le_one p.2
  linarith

omit [NormedSpace ℝ E] in
theorem continuous_cellHepDenom : Continuous (cellHepDenom : ClosedUnitBall E × I → ℝ) := by
  unfold cellHepDenom
  exact Continuous.max
    (continuous_norm.comp (continuous_subtype_val.comp continuous_fst)) (by fun_prop)

/-- The vector coordinate when the ray exits through the bottom face. -/
noncomputable def cellHepDownDenom (p : ClosedUnitBall E × I) : ℝ :=
  max (2 - (p.2 : ℝ)) (2 * ‖(p.1 : E)‖)

omit [NormedSpace ℝ E] in
theorem cellHepDownDenom_pos (p : ClosedUnitBall E × I) : 0 < cellHepDownDenom p := by
  apply lt_max_of_lt_left
  have ht := unitInterval.le_one p.2
  linarith

omit [NormedSpace ℝ E] in
theorem continuous_cellHepDownDenom :
    Continuous (cellHepDownDenom : ClosedUnitBall E × I → ℝ) := by
  unfold cellHepDownDenom
  exact Continuous.max (by fun_prop)
    (continuous_const.mul (continuous_norm.comp
      (continuous_subtype_val.comp continuous_fst)))

/-- The vector coordinate when the ray exits through the bottom face.  As for
the side formula, a maximum extends the geometric formula continuously to the
whole cylinder while keeping it in the closed ball. -/
noncomputable def cellHepDownVec (p : ClosedUnitBall E × I) : E :=
  (2 / cellHepDownDenom p) • (p.1 : E)

theorem continuous_cellHepDownVec :
    Continuous (cellHepDownVec : ClosedUnitBall E × I → E) := by
  unfold cellHepDownVec
  apply Continuous.smul
    (Continuous.div continuous_const continuous_cellHepDownDenom fun p =>
      ne_of_gt (cellHepDownDenom_pos p))
    (continuous_subtype_val.comp continuous_fst)

theorem norm_cellHepDownVec_le_one (p : ClosedUnitBall E × I) :
    ‖cellHepDownVec p‖ ≤ 1 := by
  have hd : 0 < cellHepDownDenom p := cellHepDownDenom_pos p
  have hnorm : ‖(p.1 : E)‖ ≤ 1 := by
    have hnorm' := Metric.mem_closedBall.mp p.1.2
    simpa only [dist_zero_right] using hnorm'
  have hle : 2 * ‖(p.1 : E)‖ ≤ cellHepDownDenom p :=
    le_max_right _ _
  unfold cellHepDownVec
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos (by norm_num) hd)]
  rw [div_mul_eq_mul_div, div_le_one hd]
  exact hle

/-- The vector coordinate when the ray exits through the side face.  The
regularized denominator makes this formula continuous even away from its branch. -/
noncomputable def cellHepAcrossVec (p : ClosedUnitBall E × I) : E :=
  (cellHepDenom p)⁻¹ • (p.1 : E)

theorem continuous_cellHepAcrossVec :
    Continuous (cellHepAcrossVec : ClosedUnitBall E × I → E) := by
  apply Continuous.smul (Continuous.inv₀ continuous_cellHepDenom fun p =>
    ne_of_gt (cellHepDenom_pos p)) (continuous_subtype_val.comp continuous_fst)

theorem norm_cellHepAcrossVec_le_one (p : ClosedUnitBall E × I) :
    ‖cellHepAcrossVec p‖ ≤ 1 := by
  have hd : 0 < cellHepDenom p := cellHepDenom_pos p
  have hle : ‖(p.1 : E)‖ ≤ cellHepDenom p := le_max_left _ _
  unfold cellHepAcrossVec
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hd)]
  rw [inv_mul_eq_div, div_le_one hd]
  exact hle

/-- The time coordinate when the ray exits through the side face, clipped to
the unit interval outside the branch where its geometric value is used. -/
noncomputable def cellHepAcrossTime : C(ClosedUnitBall E × I, I) where
  toFun p := Set.projIcc 0 1 zero_le_one
    (((p.2 : ℝ) + 2 * ‖(p.1 : E)‖ - 2) / cellHepDenom p)
  continuous_toFun := continuous_projIcc.comp <| Continuous.div (by fun_prop)
    continuous_cellHepDenom fun p => ne_of_gt (cellHepDenom_pos p)

omit [NormedSpace ℝ E] in
theorem cellHepDownDenom_eq {p : ClosedUnitBall E × I}
    (h : 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) ≤ 2) :
    cellHepDownDenom p = 2 - (p.2 : ℝ) := by
  unfold cellHepDownDenom
  rw [max_eq_left]
  linarith

omit [NormedSpace ℝ E] in
theorem cellHepDenom_eq {p : ClosedUnitBall E × I}
    (h : 2 ≤ 2 * ‖(p.1 : E)‖ + (p.2 : ℝ)) :
    cellHepDenom p = ‖(p.1 : E)‖ := by
  unfold cellHepDenom
  rw [max_eq_left]
  linarith

theorem norm_cellHepAcrossVec_eq_one {p : ClosedUnitBall E × I}
    (h : 2 ≤ 2 * ‖(p.1 : E)‖ + (p.2 : ℝ)) :
    ‖cellHepAcrossVec p‖ = 1 := by
  have ht := unitInterval.le_one p.2
  have hr : 0 < ‖(p.1 : E)‖ := by linarith
  unfold cellHepAcrossVec
  rw [cellHepDenom_eq h, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr),
    inv_mul_cancel₀ (ne_of_gt hr)]

omit [NormedSpace ℝ E] in
theorem cellHepAcrossTime_coe {p : ClosedUnitBall E × I}
    (h : 2 ≤ 2 * ‖(p.1 : E)‖ + (p.2 : ℝ)) :
    (cellHepAcrossTime p : ℝ) =
      ((p.2 : ℝ) + 2 * ‖(p.1 : E)‖ - 2) / ‖(p.1 : E)‖ := by
  have ht0 := unitInterval.nonneg p.2
  have ht1 := unitInterval.le_one p.2
  have hr0 : 0 < ‖(p.1 : E)‖ := by linarith
  have hr1 : ‖(p.1 : E)‖ ≤ 1 := by
    have hr1' := Metric.mem_closedBall.mp p.1.2
    simpa only [dist_zero_right] using hr1'
  show (Set.projIcc (0 : ℝ) 1 zero_le_one _ : ℝ) = _
  rw [cellHepDenom_eq h, Set.projIcc_of_mem]
  rw [Set.mem_Icc]
  constructor
  · exact div_nonneg (by linarith) (le_of_lt hr0)
  · rw [div_le_one hr0]
    linarith

/-- The bottom-face branch of the radial projection, extended continuously to
all of the cylinder. -/
noncomputable def cellHepDown : C(ClosedUnitBall E × I, ClosedUnitBall E × I) where
  toFun p :=
    (⟨cellHepDownVec p, Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using norm_cellHepDownVec_le_one p)⟩, 0)
  continuous_toFun :=
    (continuous_cellHepDownVec.subtype_mk fun p => Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using norm_cellHepDownVec_le_one p)).prodMk continuous_const

/-- The side-face branch of the radial projection, extended continuously to all
of the cylinder. -/
noncomputable def cellHepAcross : C(ClosedUnitBall E × I, ClosedUnitBall E × I) where
  toFun p :=
    (⟨cellHepAcrossVec p, Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using norm_cellHepAcrossVec_le_one p)⟩,
      cellHepAcrossTime p)
  continuous_toFun :=
    (continuous_cellHepAcrossVec.subtype_mk fun p => Metric.mem_closedBall.mpr (by
      simpa only [dist_zero_right] using norm_cellHepAcrossVec_le_one p)).prodMk
        (map_continuous cellHepAcrossTime)

theorem cellHepDown_eq_across_of_seam {p : ClosedUnitBall E × I}
    (h : 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) = 2) :
    cellHepDown p = cellHepAcross p := by
  apply Prod.ext
  · apply Subtype.ext
    change cellHepDownVec p = cellHepAcrossVec p
    unfold cellHepDownVec cellHepAcrossVec
    rw [cellHepDownDenom_eq h.le, cellHepDenom_eq h.ge]
    have ht := unitInterval.le_one p.2
    have hr : 0 < ‖(p.1 : E)‖ := by linarith
    have hden : 2 - (p.2 : ℝ) = 2 * ‖(p.1 : E)‖ := by linarith
    rw [hden]
    congr 1
    field_simp
  · apply Subtype.ext
    change (0 : ℝ) = (cellHepAcrossTime p : ℝ)
    rw [cellHepAcrossTime_coe h.ge]
    rw [show (p.2 : ℝ) + 2 * ‖(p.1 : E)‖ - 2 = 0 by linarith, zero_div]

theorem cellHepDown_zero (x : ClosedUnitBall E) :
    cellHepDown (x, 0) = (x, 0) := by
  apply Prod.ext
  · apply Subtype.ext
    change cellHepDownVec (x, 0) = (x : E)
    have hx : ‖(x : E)‖ ≤ 1 := by
      have hx' := Metric.mem_closedBall.mp x.2
      simpa only [dist_zero_right] using hx'
    unfold cellHepDownVec cellHepDownDenom
    rw [show ((0 : I) : ℝ) = 0 by rfl, sub_zero, max_eq_left (by linarith)]
    norm_num
  · rfl

theorem cellHepAcross_of_mem_boundary {p : ClosedUnitBall E × I}
    (hp : p.1 ∈ CellBoundary E) : cellHepAcross p = p := by
  have hnorm : ‖(p.1 : E)‖ = 1 := hp
  have ht0 := unitInterval.nonneg p.2
  have hside : 2 ≤ 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) := by linarith
  apply Prod.ext
  · apply Subtype.ext
    change cellHepAcrossVec p = (p.1 : E)
    unfold cellHepAcrossVec cellHepDenom
    rw [hnorm, max_eq_left (by linarith)]
    norm_num
  · apply Subtype.ext
    change (cellHepAcrossTime p : ℝ) = (p.2 : ℝ)
    rw [cellHepAcrossTime_coe hside, hnorm]
    ring

end Coordinates

section Retraction

variable {E}

/-- Radial projection of the cell cylinder from `(0, 2)` onto its bottom and
side.  The inequality says that the ray meets the bottom before the side. -/
noncomputable def cellBoundaryHepRetraction :
    C(ClosedUnitBall E × I, ClosedUnitBall E × I) where
  toFun p := if 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) ≤ 2 then cellHepDown p else cellHepAcross p
  continuous_toFun := by
    refine Continuous.if_le (map_continuous cellHepDown) (map_continuous cellHepAcross)
      (by fun_prop) continuous_const ?_
    intro p hp
    exact cellHepDown_eq_across_of_seam hp

theorem cellBoundaryHepRetraction_mapsInto (p : ClosedUnitBall E × I) :
    cellBoundaryHepRetraction p ∈ hepBase (CellBoundary E) := by
  change (if 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) ≤ 2 then cellHepDown p else cellHepAcross p) ∈
    hepBase (CellBoundary E)
  split_ifs with h
  · exact mem_hepBase_right rfl
  · apply mem_hepBase_left
    change ‖((cellHepAcross p).1 : E)‖ = 1
    exact norm_cellHepAcrossVec_eq_one (le_of_lt (lt_of_not_ge h))

theorem cellBoundaryHepRetraction_fixes (p : ClosedUnitBall E × I)
    (hp : p ∈ hepBase (CellBoundary E)) : cellBoundaryHepRetraction p = p := by
  rcases hp with hpS | hp0
  · change (if 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) ≤ 2 then cellHepDown p else cellHepAcross p) = p
    split_ifs with h
    · have hnorm : ‖(p.1 : E)‖ = 1 := hpS
      have ht0 := unitInterval.nonneg p.2
      have htime : p.2 = 0 := by
        apply Subtype.ext
        change (p.2 : ℝ) = 0
        linarith
      have hpEq : p = (p.1, 0) := Prod.ext rfl htime
      rw [hpEq, cellHepDown_zero]
    · exact cellHepAcross_of_mem_boundary hpS
  · have hnorm : ‖(p.1 : E)‖ ≤ 1 := by
      have hnorm' := Metric.mem_closedBall.mp p.1.2
      simpa only [dist_zero_right] using hnorm'
    have hdown : 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) ≤ 2 := by
      rw [hp0]
      norm_num
      linarith
    change (if 2 * ‖(p.1 : E)‖ + (p.2 : ℝ) ≤ 2 then cellHepDown p else cellHepAcross p) = p
    rw [if_pos hdown]
    have hpEq : p = (p.1, 0) := Prod.ext rfl hp0
    rw [hpEq, cellHepDown_zero]

omit [NormedSpace ℝ E] in
theorem isClosed_cellBoundary : IsClosed (CellBoundary E) := by
  exact isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const

/-- The bottom-plus-boundary subspace is a retract of the cell cylinder. -/
theorem isRetract_hepBase_cellBoundary :
    IsRetract (hepBase (CellBoundary E)) :=
  ⟨cellBoundaryHepRetraction, cellBoundaryHepRetraction_mapsInto,
    cellBoundaryHepRetraction_fixes⟩

/-- The boundary of a closed unit ball in a real normed space has the homotopy
extension property.  This is the core cell-pair fact used in CW constructions. -/
theorem hasHEP_cellBoundary : HasHEP.{u, v} (CellBoundary E) :=
  hasHEP_of_isRetract isClosed_cellBoundary isRetract_hepBase_cellBoundary

end Retraction

end HatcherLib

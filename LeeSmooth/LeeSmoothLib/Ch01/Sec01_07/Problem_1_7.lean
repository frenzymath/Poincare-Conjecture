import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import LeeSmoothLib.Ch01.Sec01_02.Proposition_1_17
-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ChartedSpace
open scoped Manifold ContDiff

-- Semantic search note: no `lean_leansearch` tool was available in this environment, so the
-- stereographic-coordinate API is stated with explicit coordinate formulas and the smooth-structure
-- comparison is phrased via `StructureGroupoid.maximalAtlas`.

section Problem17

variable (n : ℕ)

local notation "AmbientSpace" => EuclideanSpace ℝ (Fin (n + 1))
local notation "ModelSpace" => EuclideanSpace ℝ (Fin n)
local notation "UnitSphere" => Metric.sphere (0 : AmbientSpace) 1

/-- The north pole `(0, …, 0, 1)` of the unit sphere in `ℝ^(n+1)`. -/
def northPoleVec : AmbientSpace :=
  (WithLp.toLp 2 (Fin.snoc (0 : Fin n → ℝ) (1 : ℝ)) : AmbientSpace)

/-- The south pole `(0, …, 0, -1)` of the unit sphere in `ℝ^(n+1)`. -/
def southPoleVec : AmbientSpace :=
  (WithLp.toLp 2 (Fin.snoc (0 : Fin n → ℝ) (-1 : ℝ)) : AmbientSpace)

/-- The north pole lies on the unit sphere. -/
theorem northPoleVec_mem_unitSphere :
    northPoleVec n ∈ UnitSphere := by
  -- Compute the Euclidean norm of the standard basis vector with last coordinate `1`.
  simp [Metric.sphere, dist_eq_norm, EuclideanSpace.norm_eq, northPoleVec,
    Fin.sum_univ_castSucc, Fin.snoc]

/-- The south pole lies on the unit sphere. -/
theorem southPoleVec_mem_unitSphere :
    southPoleVec n ∈ UnitSphere := by
  -- The south pole has the same norm computation, with last coordinate `-1`.
  simp [Metric.sphere, dist_eq_norm, EuclideanSpace.norm_eq, southPoleVec,
    Fin.sum_univ_castSucc, Fin.snoc]

/-- The north pole as a point of the unit sphere. -/
def northPolePoint : UnitSphere :=
  ⟨northPoleVec n, northPoleVec_mem_unitSphere n⟩

/-- The south pole as a point of the unit sphere. -/
def southPolePoint : UnitSphere :=
  ⟨southPoleVec n, southPoleVec_mem_unitSphere n⟩

/-- The complement of the north pole in the unit sphere. -/
def northPoleComplement : TopologicalSpace.Opens UnitSphere :=
  ⟨{x | x ≠ northPolePoint n}, isOpen_compl_singleton⟩

/-- The complement of the south pole in the unit sphere. -/
def southPoleComplement : TopologicalSpace.Opens UnitSphere :=
  ⟨{x | x ≠ southPolePoint n}, isOpen_compl_singleton⟩

/-- The inclusion `ℝ^n → ℝ^(n+1)` obtained by adjoining a last coordinate equal to `0`. -/
def equatorialInclusion (u : ModelSpace) : AmbientSpace :=
  (WithLp.toLp 2 (Fin.snoc u (0 : ℝ)) : AmbientSpace)

/-- The explicit stereographic projection from the north pole, viewed as a total map on the
underlying sphere. -/
def stereographicNorthMap : UnitSphere → ModelSpace :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x.1 (Fin.castSucc i) / (1 - x.1 (Fin.last n))

/-- The explicit stereographic projection from the south pole, viewed as a total map on the
underlying sphere. -/
def stereographicSouthMap : UnitSphere → ModelSpace :=
  fun x ↦ WithLp.toLp 2 fun i ↦ x.1 (Fin.castSucc i) / (1 + x.1 (Fin.last n))

/-- The north-pole stereographic projection restricted to its natural domain. -/
def stereographicNorth : northPoleComplement n → ModelSpace :=
  fun x ↦ stereographicNorthMap n x.1

/-- The south-pole stereographic projection restricted to its natural domain. -/
def stereographicSouth : southPoleComplement n → ModelSpace :=
  fun x ↦ stereographicSouthMap n x.1

/-- The explicit vector formula for the inverse of stereographic projection from the north pole. -/
def stereographicNorthInvVector (u : ModelSpace) : AmbientSpace :=
  (‖u‖ ^ 2 + 1)⁻¹ •
    (WithLp.toLp 2 (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace)

/-- The explicit vector formula for the inverse of stereographic projection from the south pole. -/
def stereographicSouthInvVector (u : ModelSpace) : AmbientSpace :=
  (‖u‖ ^ 2 + 1)⁻¹ •
    (WithLp.toLp 2 (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (1 - ‖u‖ ^ 2)) : AmbientSpace)

/-- Helper for Problem 1-7: the numerator in the north inverse formula has squared norm
`(‖u‖² + 1)²`. -/
lemma stereographicNorthInvNumerator_norm_sq (u : ModelSpace) :
    ‖(WithLp.toLp 2
        (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace)‖ ^ 2 =
      (‖u‖ ^ 2 + 1) ^ 2 := by
  -- Expand the Euclidean squared norm into coordinates and simplify the polynomial identity.
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [EuclideanSpace.real_norm_sq_eq u]
  simp [Fin.sum_univ_castSucc, Fin.snoc]
  set s : ℝ := ∑ x, u.ofLp x ^ 2
  have hsum : ∑ x, (2 * u.ofLp x) ^ 2 = 4 * s := by
    calc
      ∑ x, (2 * u.ofLp x) ^ 2 = ∑ x, 4 * (u.ofLp x) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = 4 * s := by
        simp [s, Finset.mul_sum]
  rw [show ∑ x, (2 * u.ofLp x) ^ 2 = 4 * s by exact hsum]
  ring

/-- Helper for Problem 1-7: the numerator in the south inverse formula has squared norm
`(‖u‖² + 1)²`. -/
lemma stereographicSouthInvNumerator_norm_sq (u : ModelSpace) :
    ‖(WithLp.toLp 2
        (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (1 - ‖u‖ ^ 2)) : AmbientSpace)‖ ^ 2 =
      (‖u‖ ^ 2 + 1) ^ 2 := by
  -- The sign change in the last coordinate disappears after squaring.
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [EuclideanSpace.real_norm_sq_eq u]
  simp [Fin.sum_univ_castSucc, Fin.snoc]
  set s : ℝ := ∑ x, u.ofLp x ^ 2
  have hsum : ∑ x, (2 * u.ofLp x) ^ 2 = 4 * s := by
    calc
      ∑ x, (2 * u.ofLp x) ^ 2 = ∑ x, 4 * (u.ofLp x) ^ 2 := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
      _ = 4 * s := by
        simp [s, Finset.mul_sum]
  rw [show ∑ x, (2 * u.ofLp x) ^ 2 = 4 * s by exact hsum]
  ring

/-- The explicit inverse vector for north-pole stereographic projection lies on the unit sphere. -/
theorem stereographicNorthInvVector_mem_unitSphere (u : ModelSpace) :
    stereographicNorthInvVector n u ∈ UnitSphere := by
  -- Compute the squared norm of the explicit inverse vector and then recover norm `1`.
  rw [mem_sphere_zero_iff_norm]
  have hpos : 0 < ‖u‖ ^ 2 + 1 := by
    positivity
  have hsq :
      ‖stereographicNorthInvVector n u‖ ^ 2 =
        ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) ^ 2 * (‖u‖ ^ 2 + 1) ^ 2 := by
    calc
      ‖stereographicNorthInvVector n u‖ ^ 2
          =
            (‖((‖u‖ ^ 2 + 1 : ℝ)⁻¹)‖ *
              ‖(WithLp.toLp 2
                  (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i)
                    (‖u‖ ^ 2 - 1)) : AmbientSpace)‖) ^ 2 := by
              rw [stereographicNorthInvVector, norm_smul]
      _ =
            ‖((‖u‖ ^ 2 + 1 : ℝ)⁻¹)‖ ^ 2 *
              ‖(WithLp.toLp 2
                  (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i)
                    (‖u‖ ^ 2 - 1)) : AmbientSpace)‖ ^ 2 := by
            ring
      _ = ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) ^ 2 * (‖u‖ ^ 2 + 1) ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
              stereographicNorthInvNumerator_norm_sq]
  have hmul : (((‖u‖ ^ 2 + 1 : ℝ)⁻¹) ^ 2) * (‖u‖ ^ 2 + 1) ^ 2 = 1 := by
    field_simp [hpos.ne']
  have hnonneg : 0 ≤ ‖stereographicNorthInvVector n u‖ := norm_nonneg _
  nlinarith [hsq.trans hmul]

/-- The explicit inverse vector for south-pole stereographic projection lies on the unit sphere. -/
theorem stereographicSouthInvVector_mem_unitSphere (u : ModelSpace) :
    stereographicSouthInvVector n u ∈ UnitSphere := by
  -- The south inverse has the same norm computation because the final sign disappears on squaring.
  rw [mem_sphere_zero_iff_norm]
  have hpos : 0 < ‖u‖ ^ 2 + 1 := by
    positivity
  have hsq :
      ‖stereographicSouthInvVector n u‖ ^ 2 =
        ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) ^ 2 * (‖u‖ ^ 2 + 1) ^ 2 := by
    calc
      ‖stereographicSouthInvVector n u‖ ^ 2
          =
            (‖((‖u‖ ^ 2 + 1 : ℝ)⁻¹)‖ *
              ‖(WithLp.toLp 2
                  (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i)
                    (1 - ‖u‖ ^ 2)) : AmbientSpace)‖) ^ 2 := by
              rw [stereographicSouthInvVector, norm_smul]
      _ =
            ‖((‖u‖ ^ 2 + 1 : ℝ)⁻¹)‖ ^ 2 *
              ‖(WithLp.toLp 2
                  (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i)
                    (1 - ‖u‖ ^ 2)) : AmbientSpace)‖ ^ 2 := by
            ring
      _ = ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) ^ 2 * (‖u‖ ^ 2 + 1) ^ 2 := by
            rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
              stereographicSouthInvNumerator_norm_sq]
  have hmul : (((‖u‖ ^ 2 + 1 : ℝ)⁻¹) ^ 2) * (‖u‖ ^ 2 + 1) ^ 2 = 1 := by
    field_simp [hpos.ne']
  have hnonneg : 0 ≤ ‖stereographicSouthInvVector n u‖ := norm_nonneg _
  nlinarith [hsq.trans hmul]

/-- Helper for Problem 1-7: the north and south poles are distinct points of `S^n`. -/
theorem northPolePoint_ne_southPolePoint :
    northPolePoint n ≠ southPolePoint n := by
  -- Compare the last coordinates of the two sphere points.
  intro h
  have hlast := congrArg
    (fun y : UnitSphere => (((y : UnitSphere) : AmbientSpace) (Fin.last n))) h
  norm_num [northPolePoint, southPolePoint, northPoleVec, southPoleVec, Fin.snoc] at hlast

/-- The explicit inverse of north-pole stereographic projection as a point of the sphere. -/
def stereographicNorthInv (u : ModelSpace) : UnitSphere :=
  ⟨stereographicNorthInvVector n u, stereographicNorthInvVector_mem_unitSphere n u⟩

/-- The explicit inverse of south-pole stereographic projection as a point of the sphere. -/
def stereographicSouthInv (u : ModelSpace) : UnitSphere :=
  ⟨stereographicSouthInvVector n u, stereographicSouthInvVector_mem_unitSphere n u⟩

/-- The inverse of north-pole stereographic projection never lands at the north pole. -/
theorem stereographicNorthInv_ne_northPole (u : ModelSpace) :
    stereographicNorthInv n u ≠ northPolePoint n := by
  -- The last coordinate of the inverse formula is strictly less than `1`.
  intro h
  have hlast := congrArg
    (fun y => (((y : UnitSphere) : AmbientSpace) (Fin.last n))) h
  have hpos : 0 < ‖u‖ ^ 2 + 1 := by
    positivity
  have hne : (‖u‖ ^ 2 + 1 : ℝ) ≠ 0 := hpos.ne'
  simp [stereographicNorthInv, stereographicNorthInvVector, northPolePoint, northPoleVec,
    Fin.snoc] at hlast
  field_simp [hne] at hlast
  linarith

/-- The inverse of south-pole stereographic projection never lands at the south pole. -/
theorem stereographicSouthInv_ne_southPole (u : ModelSpace) :
    stereographicSouthInv n u ≠ southPolePoint n := by
  -- The south inverse has last coordinate strictly greater than `-1`.
  intro h
  have hlast := congrArg
    (fun y => (((y : UnitSphere) : AmbientSpace) (Fin.last n))) h
  have hpos : 0 < ‖u‖ ^ 2 + 1 := by
    positivity
  have hne : (‖u‖ ^ 2 + 1 : ℝ) ≠ 0 := hpos.ne'
  simp [stereographicSouthInv, stereographicSouthInvVector, southPolePoint, southPoleVec,
    Fin.snoc] at hlast
  field_simp [hne] at hlast
  linarith

/-- Helper for Problem 1-7: away from the north pole, the denominator `1 - x_{n+1}` is nonzero. -/
lemma northDenominator_ne_zero {x : UnitSphere}
    (hx : x ∈ (northPoleComplement n : Set UnitSphere)) :
    (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n)) : ℝ) ≠ 0 := by
  -- If the denominator vanished, the last coordinate would be `1`,
  -- forcing `x` to be the north pole.
  have hxne : x ≠ northPolePoint n := by
    simpa [northPoleComplement] using hx
  intro hzero
  have hv : ‖northPoleVec n‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using northPoleVec_mem_unitSphere n
  have hxnorm : ‖(((x : UnitSphere) : AmbientSpace))‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using (x : UnitSphere).2
  have hlast : (((x : UnitSphere) : AmbientSpace) (Fin.last n)) = 1 := by
    linarith
  have hEq : (((x : UnitSphere) : AmbientSpace)) = northPoleVec n := by
    have hInner : inner ℝ (northPoleVec n) (((x : UnitSphere) : AmbientSpace)) = 1 := by
      simp [PiLp.inner_apply, northPoleVec, Fin.sum_univ_castSucc, Fin.snoc, hlast]
    have hNorth : northPoleVec n = (((x : UnitSphere) : AmbientSpace)) :=
      (inner_eq_one_iff_of_norm_eq_one hv hxnorm).mp hInner
    exact hNorth.symm
  exact hxne (by simpa [northPolePoint] using Subtype.ext hEq)

/-- Helper for Problem 1-7: away from the south pole, the denominator `1 + x_{n+1}` is nonzero. -/
lemma southDenominator_ne_zero {x : UnitSphere}
    (hx : x ∈ (southPoleComplement n : Set UnitSphere)) :
    (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n)) : ℝ) ≠ 0 := by
  -- Vanishing of the south denominator would force the last coordinate to be `-1`, hence `x = S`.
  have hxne : x ≠ southPolePoint n := by
    simpa [southPoleComplement] using hx
  intro hzero
  have hv : ‖southPoleVec n‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using southPoleVec_mem_unitSphere n
  have hxnorm : ‖(((x : UnitSphere) : AmbientSpace))‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using (x : UnitSphere).2
  have hlast : (((x : UnitSphere) : AmbientSpace) (Fin.last n)) = -1 := by
    linarith
  have hEq : (((x : UnitSphere) : AmbientSpace)) = southPoleVec n := by
    have hInner : inner ℝ (southPoleVec n) (((x : UnitSphere) : AmbientSpace)) = 1 := by
      simp [PiLp.inner_apply, southPoleVec, Fin.sum_univ_castSucc, Fin.snoc, hlast]
    have hSouth : southPoleVec n = (((x : UnitSphere) : AmbientSpace)) :=
      (inner_eq_one_iff_of_norm_eq_one hv hxnorm).mp hInner
    exact hSouth.symm
  exact hxne (by simpa [southPolePoint] using Subtype.ext hEq)

/-- The explicit inverse of north-pole stereographic projection as a map into the open complement
of the north pole. -/
def stereographicNorthInvToOpen (u : ModelSpace) : northPoleComplement n :=
  ⟨stereographicNorthInv n u, stereographicNorthInv_ne_northPole n u⟩

/-- Helper for Problem 1-7: on the unit sphere, the first `n` coordinate squares sum to
`1 - x_{n+1}^2`. -/
lemma unitSphere_castSucc_sum_sq (x : UnitSphere) :
    ∑ i : Fin n, (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) ^ 2 =
      1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n)) ^ 2 := by
  -- Split the sphere equation into the first `n` coordinates and the final coordinate.
  have hxnorm : ‖(((x : UnitSphere) : AmbientSpace))‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using (x : UnitSphere).2
  have hxsum :
      ∑ i : Fin n, (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) ^ 2 +
          (((x : UnitSphere) : AmbientSpace) (Fin.last n)) ^ 2 = 1 := by
    have hxnormsq : ‖(((x : UnitSphere) : AmbientSpace))‖ ^ 2 = 1 := by
      nlinarith
    rw [EuclideanSpace.real_norm_sq_eq] at hxnormsq
    simpa [Fin.sum_univ_castSucc] using hxnormsq
  linarith

/-- Helper for Problem 1-7: the north-pole stereographic coordinates have squared norm
`(1 + x_{n+1}) / (1 - x_{n+1})`. -/
lemma stereographicNorthMap_normSq {x : UnitSphere}
    (hx : x ∈ (northPoleComplement n : Set UnitSphere)) :
    ‖stereographicNorthMap n x‖ ^ 2 =
      (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
        (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
  -- Expand the coordinate formula, factor out the common denominator, and use the sphere
  -- relation for the first `n` coordinates.
  set d : ℝ := 1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))
  set xLast : ℝ := (((x : UnitSphere) : AmbientSpace) (Fin.last n))
  have hd : d ≠ 0 := by
    simpa [d] using northDenominator_ne_zero n hx
  have hsplit := unitSphere_castSucc_sum_sq n x
  calc
    ‖stereographicNorthMap n x‖ ^ 2
        = ∑ i : Fin n, ((((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) / d) ^ 2 := by
            rw [EuclideanSpace.real_norm_sq_eq]
            simp [stereographicNorthMap, d]
    _ =
        ∑ i : Fin n,
          ((((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) ^ 2) * d⁻¹ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            field_simp [hd]
    _ =
        (∑ i : Fin n, (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) ^ 2) * d⁻¹ ^ 2 := by
            rw [Finset.sum_mul]
    _ = (1 - xLast ^ 2) * d⁻¹ ^ 2 := by
            rw [hsplit]
    _ = (1 + xLast) / d := by
            field_simp [hd]
            ring
    _ =
        (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
          (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
            simp [d, xLast]

/-- Helper for Problem 1-7: the south-pole stereographic coordinates have squared norm
`(1 - x_{n+1}) / (1 + x_{n+1})`. -/
lemma stereographicSouthMap_normSq {x : UnitSphere}
    (hx : x ∈ (southPoleComplement n : Set UnitSphere)) :
    ‖stereographicSouthMap n x‖ ^ 2 =
      (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
        (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
  -- This is the same denominator-factorization argument with `1 + x_{n+1}`.
  set d : ℝ := 1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))
  set xLast : ℝ := (((x : UnitSphere) : AmbientSpace) (Fin.last n))
  have hd : d ≠ 0 := by
    simpa [d] using southDenominator_ne_zero n hx
  have hsplit := unitSphere_castSucc_sum_sq n x
  calc
    ‖stereographicSouthMap n x‖ ^ 2
        = ∑ i : Fin n, ((((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) / d) ^ 2 := by
            rw [EuclideanSpace.real_norm_sq_eq]
            simp [stereographicSouthMap, d]
    _ =
        ∑ i : Fin n,
          ((((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) ^ 2) * d⁻¹ ^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            field_simp [hd]
    _ =
        (∑ i : Fin n, (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) ^ 2) * d⁻¹ ^ 2 := by
            rw [Finset.sum_mul]
    _ = (1 - xLast ^ 2) * d⁻¹ ^ 2 := by
            rw [hsplit]
    _ = (1 - xLast) / d := by
            field_simp [hd]
            ring
    _ =
        (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
          (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
            simp [d, xLast]

/-- The explicit inverse formula really is the coordinate formula displayed in the text. -/
theorem stereographicNorthInv_apply (u : ModelSpace) :
    ((stereographicNorthInv n u : UnitSphere) : AmbientSpace) = stereographicNorthInvVector n u :=
  by
  -- The subtype coercion of the explicitly defined inverse is definitionally its vector field.
  rfl

/-- North-pole stereographic projection inverts its explicit inverse on the complement of the north
pole. -/
theorem stereographicNorth_left_inv {x : UnitSphere}
    (hx : x ∈ (northPoleComplement n : Set UnitSphere)) :
    stereographicNorthInv n (stereographicNorthMap n x) = x := by
  -- Use the norm-squared formula to simplify the explicit inverse coordinates one by one.
  apply Subtype.ext
  ext i
  refine Fin.lastCases ?_ ?_ i
  · -- The last coordinate reduces to the sphere parameter `x_{n+1}`.
    have hnormSq := stereographicNorthMap_normSq n hx
    have hne := northDenominator_ne_zero n hx
    have hnormSq' :
        ‖(WithLp.toLp 2
            fun i ↦ (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) /
              (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) : ModelSpace)‖ ^ 2 =
          (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
            (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
      simpa [stereographicNorthMap] using hnormSq
    simp [stereographicNorthInv, stereographicNorthInvVector, stereographicNorthMap, Fin.snoc]
    rw [hnormSq']
    field_simp [hne]
    ring_nf
  · intro j
    -- The first `n` coordinates cancel the common stereographic denominator.
    have hnormSq := stereographicNorthMap_normSq n hx
    have hne := northDenominator_ne_zero n hx
    have hnormSq' :
        ‖(WithLp.toLp 2
            fun i ↦ (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) /
              (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) : ModelSpace)‖ ^ 2 =
          (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
            (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
      simpa [stereographicNorthMap] using hnormSq
    simp [stereographicNorthInv, stereographicNorthInvVector, stereographicNorthMap, Fin.snoc]
    rw [hnormSq']
    field_simp [hne]
    ring_nf

/-- The explicit inverse inverts north-pole stereographic projection on all of `ℝ^n`. -/
theorem stereographicNorth_right_inv (u : ModelSpace) :
    stereographicNorthMap n (stereographicNorthInv n u) = u := by
  -- Read off each coordinate of the explicit inverse formula and cancel the common denominator.
  ext i
  have hne : (‖u‖ ^ 2 + 1 : ℝ) ≠ 0 := by
    positivity
  simp [stereographicNorthMap, stereographicNorthInv, stereographicNorthInvVector, Fin.snoc]
  field_simp [hne]
  ring

/-- South-pole stereographic projection inverts its explicit inverse on the complement of the south
pole. -/
theorem stereographicSouth_left_inv {x : UnitSphere}
    (hx : x ∈ (southPoleComplement n : Set UnitSphere)) :
    stereographicSouthInv n (stereographicSouthMap n x) = x := by
  -- Mirror the north-pole computation with the south norm-squared formula.
  apply Subtype.ext
  ext i
  refine Fin.lastCases ?_ ?_ i
  · -- The last coordinate simplifies to `x_{n+1}` after clearing denominators.
    have hnormSq := stereographicSouthMap_normSq n hx
    have hne := southDenominator_ne_zero n hx
    have hnormSq' :
        ‖(WithLp.toLp 2
            fun i ↦ (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) /
              (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) : ModelSpace)‖ ^ 2 =
          (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
            (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
      simpa [stereographicSouthMap] using hnormSq
    simp [stereographicSouthInv, stereographicSouthInvVector, stereographicSouthMap, Fin.snoc]
    rw [hnormSq']
    field_simp [hne]
    ring_nf
  · intro j
    -- The equatorial coordinates again cancel the common denominator.
    have hnormSq := stereographicSouthMap_normSq n hx
    have hne := southDenominator_ne_zero n hx
    have hnormSq' :
        ‖(WithLp.toLp 2
            fun i ↦ (((x : UnitSphere) : AmbientSpace) (Fin.castSucc i)) /
              (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) : ModelSpace)‖ ^ 2 =
          (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n))) /
            (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n))) := by
      simpa [stereographicSouthMap] using hnormSq
    simp [stereographicSouthInv, stereographicSouthInvVector, stereographicSouthMap, Fin.snoc]
    rw [hnormSq']
    field_simp [hne]
    ring_nf

/-- The explicit inverse inverts south-pole stereographic projection on all of `ℝ^n`. -/
theorem stereographicSouth_right_inv (u : ModelSpace) :
    stereographicSouthMap n (stereographicSouthInv n u) = u := by
  -- The south-pole inverse has the same coordinate cancellation as the north-pole one.
  ext i
  have hne : (‖u‖ ^ 2 + 1 : ℝ) ≠ 0 := by
    positivity
  simp [stereographicSouthMap, stereographicSouthInv, stereographicSouthInvVector, Fin.snoc]
  field_simp [hne]
  ring

/-- The explicit north-pole stereographic formula is continuous away from the north pole. -/
theorem continuousOn_stereographicNorthMap :
    ContinuousOn (stereographicNorthMap n) (northPoleComplement n : Set UnitSphere) := by
  -- Each coordinate is a quotient of continuous functions, and the denominator stays nonzero away
  -- from the north pole.
  have hcoord :
      ContinuousOn
        (fun x : UnitSphere => fun i : Fin n ↦
          x.1 (Fin.castSucc i) / (1 - x.1 (Fin.last n)))
        (northPoleComplement n : Set UnitSphere) := by
    rw [continuousOn_pi]
    intro i
    refine
      (((PiLp.continuous_apply 2 _ (Fin.castSucc i)).comp continuous_subtype_val).continuousOn.div
        ((continuous_const.sub
          ((PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val)).continuousOn)
        fun x hx ↦ northDenominator_ne_zero n hx)
  simpa [stereographicNorthMap] using
    (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn hcoord

/-- The explicit inverse to north-pole stereographic projection is continuous. -/
theorem continuous_stereographicNorthInv :
    Continuous (stereographicNorthInv n) := by
  -- Route correction: this proof uses the explicit formula directly instead of the stalled
  -- `stereographic'` transport bridge.
  -- First prove the ambient vector formula is continuous coordinatewise.
  have hvec : Continuous (stereographicNorthInvVector n) := by
    have hscalar : Continuous fun u : ModelSpace => ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) := by
      refine ((continuous_norm.pow 2).add continuous_const).inv₀ ?_
      intro u hzero
      have hzero' : (‖u‖ ^ 2 + 1 : ℝ) = 0 := by
        simpa using hzero
      have hsqnonneg : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg ‖u‖
      nlinarith
    have hnumerator :
        Continuous fun u : ModelSpace =>
          (WithLp.toLp 2
            (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace) := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) ↦ ℝ)).comp ?_
      refine continuous_pi ?_
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa [Fin.snoc] using (continuous_norm.pow 2).sub continuous_const
      · intro j
        simpa [Fin.snoc] using
          continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) j).comp continuous_id)
    simpa [stereographicNorthInvVector] using hscalar.smul hnumerator
  -- Then lift the ambient continuity to the sphere-valued map via the proved membership theorem.
  exact Continuous.subtype_mk hvec (fun u ↦ stereographicNorthInvVector_mem_unitSphere n u)

/-- The explicit south-pole stereographic formula is continuous away from the south pole. -/
theorem continuousOn_stereographicSouthMap :
    ContinuousOn (stereographicSouthMap n) (southPoleComplement n : Set UnitSphere) := by
  -- The south formula is the same quotient argument with denominator `1 + x_{n+1}`.
  have hcoord :
      ContinuousOn
        (fun x : UnitSphere => fun i : Fin n ↦
          x.1 (Fin.castSucc i) / (1 + x.1 (Fin.last n)))
        (southPoleComplement n : Set UnitSphere) := by
    rw [continuousOn_pi]
    intro i
    refine
      (((PiLp.continuous_apply 2 _ (Fin.castSucc i)).comp continuous_subtype_val).continuousOn.div
        ((continuous_const.add
          ((PiLp.continuous_apply 2 _ (Fin.last n)).comp continuous_subtype_val)).continuousOn)
        fun x hx ↦ southDenominator_ne_zero n hx)
  simpa [stereographicSouthMap] using
    (PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).comp_continuousOn hcoord

/-- The explicit inverse to south-pole stereographic projection is continuous. -/
theorem continuous_stereographicSouthInv :
    Continuous (stereographicSouthInv n) := by
  -- Route correction: as in the north-pole case, use the explicit formula directly.
  -- First show the ambient south inverse vector depends continuously on `u`.
  have hvec : Continuous (stereographicSouthInvVector n) := by
    have hscalar : Continuous fun u : ModelSpace => ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) := by
      refine ((continuous_norm.pow 2).add continuous_const).inv₀ ?_
      intro u hzero
      have hzero' : (‖u‖ ^ 2 + 1 : ℝ) = 0 := by
        simpa using hzero
      have hsqnonneg : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg ‖u‖
      nlinarith
    have hnumerator :
        Continuous fun u : ModelSpace =>
          (WithLp.toLp 2
            (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (1 - ‖u‖ ^ 2)) : AmbientSpace) := by
      refine (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) ↦ ℝ)).comp ?_
      refine continuous_pi ?_
      intro i
      refine Fin.lastCases ?_ ?_ i
      · simpa [Fin.snoc] using continuous_const.sub (continuous_norm.pow 2)
      · intro j
        simpa [Fin.snoc] using
          continuous_const.mul ((PiLp.continuous_apply 2 (fun _ : Fin n ↦ ℝ) j).comp continuous_id)
    simpa [stereographicSouthInvVector] using hscalar.smul hnumerator
  -- Then package the ambient continuity as a sphere-valued map.
  exact Continuous.subtype_mk hvec (fun u ↦ stereographicSouthInvVector_mem_unitSphere n u)

/-- The north-pole stereographic chart as an open partial homeomorphism. -/
def stereographicNorthChart : OpenPartialHomeomorph UnitSphere ModelSpace where
  toFun := stereographicNorthMap n
  invFun := stereographicNorthInv n
  source := northPoleComplement n
  target := Set.univ
  map_source' := fun _ _ ↦ Set.mem_univ _
  map_target' := fun _ _ ↦ stereographicNorthInv_ne_northPole n _
  left_inv' := fun _ hx ↦ stereographicNorth_left_inv n hx
  right_inv' := fun _ _ ↦ stereographicNorth_right_inv n _
  open_source := (northPoleComplement n).2
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_stereographicNorthMap n
  continuousOn_invFun := (continuous_stereographicNorthInv n).continuousOn

/-- The south-pole stereographic chart as an open partial homeomorphism. -/
def stereographicSouthChart : OpenPartialHomeomorph UnitSphere ModelSpace where
  toFun := stereographicSouthMap n
  invFun := stereographicSouthInv n
  source := southPoleComplement n
  target := Set.univ
  map_source' := fun _ _ ↦ Set.mem_univ _
  map_target' := fun _ _ ↦ stereographicSouthInv_ne_southPole n _
  left_inv' := fun _ hx ↦ stereographicSouth_left_inv n hx
  right_inv' := fun _ _ ↦ stereographicSouth_right_inv n _
  open_source := (southPoleComplement n).2
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_stereographicSouthMap n
  continuousOn_invFun := (continuous_stereographicSouthInv n).continuousOn

/-- The chosen chart in the two-chart stereographic atlas: use the south-pole chart at the north
pole and the north-pole chart everywhere else. -/
def stereographicSphereChartAt (x : UnitSphere) : OpenPartialHomeomorph UnitSphere ModelSpace :=
  if x = northPolePoint n then stereographicSouthChart n else stereographicNorthChart n

/-- Every point lies in the source of its chosen chart in the two-chart stereographic atlas. -/
theorem mem_stereographicSphereChartAt_source (x : UnitSphere) :
    x ∈ (stereographicSphereChartAt n x).source := by
  -- Split on whether the chosen chart is the south-pole or north-pole chart.
  by_cases hx : x = northPolePoint n
  · simpa [stereographicSphereChartAt, hx, stereographicSouthChart, southPoleComplement] using
      northPolePoint_ne_southPolePoint n
  · simp [stereographicSphereChartAt, hx, stereographicNorthChart, northPoleComplement]

/-- The chosen chart at each point belongs to the two-chart stereographic atlas. -/
theorem stereographicSphereChartAt_mem_atlas (x : UnitSphere) :
    stereographicSphereChartAt n x ∈
      {f | f = stereographicNorthChart n ∨ f = stereographicSouthChart n} := by
  -- The `if` defining `chartAt` picks exactly one of the two generators.
  by_cases hx : x = northPolePoint n
  · simp [stereographicSphereChartAt, hx]
  · simp [stereographicSphereChartAt, hx]

/-- The charted-space structure on the sphere generated by the north- and south-pole stereographic
charts. -/
abbrev stereographicSphereChartedSpace : ChartedSpace ModelSpace UnitSphere where
  atlas := {f | f = stereographicNorthChart n ∨ f = stereographicSouthChart n}
  chartAt := stereographicSphereChartAt n
  mem_chart_source := mem_stereographicSphereChartAt_source n
  chart_mem_atlas := stereographicSphereChartAt_mem_atlas n

/-- For Problem 1-7, part (1): for a point away from the north pole, the explicit stereographic coordinates
are the coordinates of the intersection of the line through the north pole and the point with the
equatorial hyperplane. -/
theorem stereographicNorth_eq_line_intersection (x : northPoleComplement n) :
    AffineMap.lineMap (northPoleVec n) (((x : UnitSphere) : AmbientSpace))
        (1 / (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n)))) =
      equatorialInclusion n (stereographicNorth n x) := by
  -- The line-map formula becomes the displayed affine interpolation once the denominator is known
  -- to be nonzero on the north-pole complement.
  have hv : ‖northPoleVec n‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using northPoleVec_mem_unitSphere n
  have hxne : (((x : UnitSphere) : AmbientSpace)) ≠ northPoleVec n := by
    intro h
    apply x.2
    apply Subtype.ext
    simpa using h
  have hxnorm : ‖(((x : UnitSphere) : AmbientSpace))‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using (x : UnitSphere).2
  have hxlt : inner ℝ (northPoleVec n) (((x : UnitSphere) : AmbientSpace)) < 1 := by
    exact (inner_lt_one_iff_real_of_norm_eq_one hv hxnorm).mpr hxne.symm
  have hne : (1 - (((x : UnitSphere) : AmbientSpace) (Fin.last n)) : ℝ) ≠ 0 := by
    intro h
    apply ne_of_lt hxlt
    have hlast : (((x : UnitSphere) : AmbientSpace) (Fin.last n)) = 1 := by
      linarith
    simp [PiLp.inner_apply, northPoleVec, Fin.sum_univ_castSucc, Fin.snoc, hlast]
  ext i
  refine Fin.lastCases ?_ ?_ i
  · -- The last coordinate vanishes because the intersection lies in the equatorial hyperplane.
    simp [AffineMap.lineMap_apply, equatorialInclusion, stereographicNorth,
      stereographicNorthMap, northPoleVec, Fin.snoc]
    field_simp [hne]
    ring
  · intro j
    -- The non-last coordinates are the displayed quotient coordinates.
    simp [AffineMap.lineMap_apply, equatorialInclusion, stereographicNorth,
      stereographicNorthMap, northPoleVec, Fin.snoc]
    field_simp [hne]

/-- For Problem 1-7, part (2): for a point away from the south pole, the south-pole stereographic
coordinates are the coordinates of the intersection of the line through the south pole and the
point with the equatorial hyperplane. -/
theorem stereographicSouth_eq_line_intersection (x : southPoleComplement n) :
    AffineMap.lineMap (southPoleVec n) (((x : UnitSphere) : AmbientSpace))
        (1 / (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n)))) =
      equatorialInclusion n (stereographicSouth n x) := by
  -- The south-pole computation is the same affine interpolation,
  -- now with denominator `1 + x_{n+1}`.
  have hv : ‖southPoleVec n‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using southPoleVec_mem_unitSphere n
  have hxne : (((x : UnitSphere) : AmbientSpace)) ≠ southPoleVec n := by
    intro h
    apply x.2
    apply Subtype.ext
    simpa using h
  have hxnorm : ‖(((x : UnitSphere) : AmbientSpace))‖ = 1 := by
    simpa [Metric.sphere, dist_eq_norm] using (x : UnitSphere).2
  have hxlt : inner ℝ (southPoleVec n) (((x : UnitSphere) : AmbientSpace)) < 1 := by
    exact (inner_lt_one_iff_real_of_norm_eq_one hv hxnorm).mpr hxne.symm
  have hne : (1 + (((x : UnitSphere) : AmbientSpace) (Fin.last n)) : ℝ) ≠ 0 := by
    intro h
    apply ne_of_lt hxlt
    have hlast : (((x : UnitSphere) : AmbientSpace) (Fin.last n)) = -1 := by
      linarith
    simp [PiLp.inner_apply, southPoleVec, Fin.sum_univ_castSucc, Fin.snoc, hlast]
  ext i
  refine Fin.lastCases ?_ ?_ i
  · -- The last coordinate is zero on the equatorial hyperplane.
    simp [AffineMap.lineMap_apply, equatorialInclusion, stereographicSouth,
      stereographicSouthMap, southPoleVec, Fin.snoc]
    field_simp [hne]
    ring
  · intro j
    -- The non-last coordinates again match the displayed quotient formula.
    simp [AffineMap.lineMap_apply, equatorialInclusion, stereographicSouth,
      stereographicSouthMap, southPoleVec, Fin.snoc]
    field_simp [hne]

/-- For Problem 1-7, part (3): stereographic projection from the north pole is bijective. -/
theorem stereographicNorth_bijective :
    Function.Bijective (stereographicNorth n) := by
  -- Package the already proved inverse formulas as left and right inverses on the open domain.
  have hleft : Function.LeftInverse (stereographicNorthInvToOpen n) (stereographicNorth n) := by
    intro x
    apply Subtype.ext
    simpa [stereographicNorth, stereographicNorthInvToOpen] using
      stereographicNorth_left_inv n x.2
  have hright : Function.RightInverse (stereographicNorthInvToOpen n) (stereographicNorth n) := by
    intro u
    exact stereographicNorth_right_inv n u
  exact ⟨hleft.injective, hright.surjective⟩

/-- For Problem 1-7, part (4): the inverse of north-pole stereographic projection is given by the explicit
formula `u ↦ (2u, ‖u‖² - 1) / (‖u‖² + 1)`. -/
theorem stereographicNorth_inverse_formula (u : ModelSpace) :
    ((stereographicNorthInv n u : UnitSphere) : AmbientSpace) =
      (‖u‖ ^ 2 + 1)⁻¹ •
        (WithLp.toLp 2
          (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace) := by
  -- Unpack the explicit inverse definition and read off its ambient-space coordinates.
  rfl

/-- For Problem 1-7, part (5): the transition map from north-pole to south-pole stereographic coordinates is
the inversion `u ↦ ‖u‖⁻² • u` on `ℝ^n \ {0}`. -/
theorem stereographic_transition (u : ModelSpace) (hu : u ≠ 0) :
    stereographicSouthMap n (stereographicNorthInv n u) = (‖u‖ ^ 2)⁻¹ • u := by
  -- Substitute the explicit north inverse into the south coordinate formula and cancel the common
  -- factor `‖u‖²`.
  ext i
  have hne1 : (‖u‖ ^ 2 + 1 : ℝ) ≠ 0 := by
    positivity
  have hne2 : (‖u‖ ^ 2 : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hu)
  simp [stereographicSouthMap, stereographicNorthInv, stereographicNorthInvVector, Fin.snoc]
  field_simp [hne1, hne2]
  ring

/-- Helper for Problem 1-7: the south-to-north stereographic transition is the same punctured-space
inversion `u ↦ ‖u‖⁻² • u`. -/
theorem stereographicSouth_transition (u : ModelSpace) (hu : u ≠ 0) :
    stereographicNorthMap n (stereographicSouthInv n u) = (‖u‖ ^ 2)⁻¹ • u := by
  -- The south inverse substituted into the north chart produces the same inversion formula.
  ext i
  have hne1 : (‖u‖ ^ 2 + 1 : ℝ) ≠ 0 := by
    positivity
  have hne2 : (‖u‖ ^ 2 : ℝ) ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hu)
  have hnorm : (‖u‖ ^ 2 : ℝ) * ‖u‖⁻¹ ^ 2 = 1 := by
    have hnorm0 : (‖u‖ : ℝ) ≠ 0 := norm_ne_zero_iff.2 hu
    field_simp [hnorm0]
  simp [stereographicNorthMap, stereographicSouthInv, stereographicSouthInvVector, Fin.snoc]
  field_simp [hne1, hne2]
  ring_nf
  calc
    ‖u‖ ^ 2 * u.ofLp i * ‖u‖⁻¹ ^ 2 = u.ofLp i * ((‖u‖ ^ 2 : ℝ) * ‖u‖⁻¹ ^ 2) := by
      ring
    _ = u.ofLp i := by
      rw [hnorm, mul_one]

/-- Helper for Problem 1-7: the north inverse hits the south pole exactly at `u = 0`. -/
lemma stereographicNorthInv_eq_southPole_iff (u : ModelSpace) :
    stereographicNorthInv n u = southPolePoint n ↔ u = 0 := by
  -- Apply the north chart and use its explicit right inverse to detect the unique zero.
  constructor
  · intro h
    have hmap :
        stereographicNorthMap n (stereographicNorthInv n u) =
          stereographicNorthMap n (southPolePoint n) := congrArg (stereographicNorthMap n) h
    rw [stereographicNorth_right_inv] at hmap
    simpa [stereographicNorthMap, southPolePoint, southPoleVec, Fin.snoc] using hmap
  · intro hu
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ ?_ i
    · simp [hu, stereographicNorthInv, stereographicNorthInvVector, southPolePoint,
        southPoleVec, Fin.snoc]
    · intro j
      simp [hu, stereographicNorthInv, stereographicNorthInvVector, southPolePoint,
        southPoleVec, Fin.snoc]

/-- Helper for Problem 1-7: the south inverse hits the north pole exactly at `u = 0`. -/
lemma stereographicSouthInv_eq_northPole_iff (u : ModelSpace) :
    stereographicSouthInv n u = northPolePoint n ↔ u = 0 := by
  -- The south chart detects the unique zero in the same way.
  constructor
  · intro h
    have hmap :
        stereographicSouthMap n (stereographicSouthInv n u) =
          stereographicSouthMap n (northPolePoint n) := congrArg (stereographicSouthMap n) h
    rw [stereographicSouth_right_inv] at hmap
    simpa [stereographicSouthMap, northPolePoint, northPoleVec, Fin.snoc] using hmap
  · intro hu
    apply Subtype.ext
    ext i
    refine Fin.lastCases ?_ ?_ i
    · simp [hu, stereographicSouthInv, stereographicSouthInvVector, northPolePoint,
        northPoleVec, Fin.snoc]
    · intro j
      simp [hu, stereographicSouthInv, stereographicSouthInvVector, northPolePoint,
        northPoleVec, Fin.snoc]

/-- Helper for Problem 1-7: the punctured-space inversion `u ↦ ‖u‖⁻² • u` is smooth on
`ℝⁿ \ {0}`. -/
lemma contDiffOn_stereographicInversion :
    ContDiffOn ℝ ∞ (fun u : ModelSpace => (‖u‖ ^ 2 : ℝ)⁻¹ • u) ({0}ᶜ : Set ModelSpace) := by
  -- Smoothness comes from inversion on `ℝ` composed with the smooth norm-squared function.
  have hscalar :
      ContDiffOn ℝ ∞ (fun u : ModelSpace => ((‖u‖ ^ 2 : ℝ)⁻¹)) ({0}ᶜ : Set ModelSpace) := by
    refine (contDiff_norm_sq ℝ).contDiffOn.inv ?_
    intro u hu
    exact pow_ne_zero 2 (norm_ne_zero_iff.2 hu)
  simpa using hscalar.smul contDiffOn_id

/-- For Problem 1-7, part (6): the two explicit stereographic charts define a smooth structure on `S^n`. -/
theorem stereographic_two_chart_isManifold :
    letI : ChartedSpace ModelSpace UnitSphere := stereographicSphereChartedSpace n
    IsManifold (𝓡 n) ∞ UnitSphere := by
  -- Route correction: prove smoothness directly from the north-south transition map instead of
  -- routing through the standard sphere atlas first.
  letI : ChartedSpace ModelSpace UnitSphere := stereographicSphereChartedSpace n
  apply isManifold_of_contDiffOn (𝓡 n) ∞ UnitSphere
  intro e e' he he'
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl
  · -- The north-to-north transition is the identity on all of `ℝⁿ`.
    have hsource :
        ((stereographicNorthChart n).symm.trans (stereographicNorthChart n)).source =
          (Set.univ : Set ModelSpace) := by
      ext u
      simp [stereographicNorthChart, northPoleComplement, stereographicNorthInv_ne_northPole]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    rw [hsource]
    refine contDiffOn_id.congr ?_
    intro u hu
    simpa using stereographicNorth_right_inv n u
  · -- The north-to-south transition is the punctured-space inversion formula.
    have hsource :
        ((stereographicNorthChart n).symm.trans (stereographicSouthChart n)).source =
          ({0}ᶜ : Set ModelSpace) := by
      ext u
      simp [stereographicNorthChart, stereographicSouthChart, northPoleComplement,
        southPoleComplement, stereographicNorthInv_eq_southPole_iff]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    rw [hsource]
    refine (contDiffOn_stereographicInversion n).congr ?_
    intro u hu
    simpa using stereographic_transition n u hu
  · -- The south-to-north transition is the same inversion formula.
    have hsource :
        ((stereographicSouthChart n).symm.trans (stereographicNorthChart n)).source =
          ({0}ᶜ : Set ModelSpace) := by
      ext u
      simp [stereographicNorthChart, stereographicSouthChart, northPoleComplement,
        southPoleComplement, stereographicSouthInv_eq_northPole_iff]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    rw [hsource]
    refine (contDiffOn_stereographicInversion n).congr ?_
    intro u hu
    simpa using stereographicSouth_transition n u hu
  · -- The south-to-south transition is again the identity.
    have hsource :
        ((stereographicSouthChart n).symm.trans (stereographicSouthChart n)).source =
          (Set.univ : Set ModelSpace) := by
      ext u
      simp [stereographicSouthChart, southPoleComplement, stereographicSouthInv_ne_southPole]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.preimage_id,
      Set.range_id, Set.inter_univ]
    rw [hsource]
    refine contDiffOn_id.congr ?_
    intro u hu
    simpa using stereographicSouth_right_inv n u

/-- Helper for Problem 1-7: a model-space partial homeomorphism belongs to
`contDiffGroupoid ∞ (𝓡 n)` once it is `C^∞` in both directions on its source and target. -/
lemma mem_contDiffGroupoid_of_contMDiffOn
    {e : OpenPartialHomeomorph ModelSpace ModelSpace}
    (he : ContDiffOn ℝ ∞ e e.source)
    (heSymm : ContDiffOn ℝ ∞ e.symm e.target) :
    e ∈ contDiffGroupoid ∞ (𝓡 n) := by
  -- For the self model with corners, membership in the groupoid is exactly two-sided
  -- `ContDiffOn` on source and target.
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  simpa using And.intro he heSymm

/-- Helper for Problem 1-7: the ambient north stereographic rational formula is smooth away from
the hyperplane `x_{n+1} = 1`. -/
lemma contDiffOn_stereographicNorthAmbient :
    ContDiffOn ℝ ∞
      (fun x : AmbientSpace ↦
        WithLp.toLp 2 fun i : Fin n ↦ x (Fin.castSucc i) / (1 - x (Fin.last n)))
      {x : AmbientSpace | (1 - x (Fin.last n) : ℝ) ≠ 0} := by
  -- Each coordinate is a quotient of smooth linear coordinates by a nowhere-vanishing denominator.
  refine contDiffOn_piLp' (p := 2) ?_
  intro i
  refine
    ((contDiff_piLp_apply (p := 2) (i := Fin.castSucc i)).contDiffOn.div
      ((contDiff_const.sub
        (contDiff_piLp_apply (p := 2) (i := Fin.last n))).contDiffOn)
      fun x hx ↦ hx)

/-- Helper for Problem 1-7: the ambient south stereographic rational formula is smooth away from
the hyperplane `x_{n+1} = -1`. -/
lemma contDiffOn_stereographicSouthAmbient :
    ContDiffOn ℝ ∞
      (fun x : AmbientSpace ↦
        WithLp.toLp 2 fun i : Fin n ↦ x (Fin.castSucc i) / (1 + x (Fin.last n)))
      {x : AmbientSpace | (1 + x (Fin.last n) : ℝ) ≠ 0} := by
  -- The south-pole formula is the same coordinatewise quotient argument.
  refine contDiffOn_piLp' (p := 2) ?_
  intro i
  refine
    ((contDiff_piLp_apply (p := 2) (i := Fin.castSucc i)).contDiffOn.div
      ((contDiff_const.add
        (contDiff_piLp_apply (p := 2) (i := Fin.last n))).contDiffOn)
      fun x hx ↦ hx)

/-- Helper for Problem 1-7: the ambient vector formula for the north inverse is smooth on
`ℝ^n`. -/
lemma contDiff_stereographicNorthInvVector :
    ContDiff ℝ ∞ (stereographicNorthInvVector n) := by
  -- The scalar factor `(‖u‖² + 1)⁻¹` and the vector numerator are both smooth.
  have hscalar : ContDiff ℝ ∞ fun u : ModelSpace => ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) := by
    refine ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ fun u : ModelSpace ↦ ‖u‖ ^ 2).add
      contDiff_const).inv ?_
    intro u
    positivity
  have hnumerator :
      ContDiff ℝ ∞
        (fun u : ModelSpace ↦
          (WithLp.toLp 2
            (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (‖u‖ ^ 2 - 1)) : AmbientSpace)) := by
    refine PiLp.contDiff_toLp.comp ?_
    refine contDiff_pi.2 ?_
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [Fin.snoc] using
        ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ fun u : ModelSpace ↦ ‖u‖ ^ 2).sub contDiff_const)
    · intro j
      simpa [Fin.snoc] using
        contDiff_const.mul (contDiff_piLp_apply (p := 2) (i := j))
  -- Multiplying the numerator by the scalar factor gives the explicit inverse vector field.
  simpa [stereographicNorthInvVector] using hscalar.smul hnumerator

/-- Helper for Problem 1-7: the ambient vector formula for the south inverse is smooth on
`ℝ^n`. -/
lemma contDiff_stereographicSouthInvVector :
    ContDiff ℝ ∞ (stereographicSouthInvVector n) := by
  -- The south inverse differs only in the last coordinate of the numerator.
  have hscalar : ContDiff ℝ ∞ fun u : ModelSpace => ((‖u‖ ^ 2 + 1 : ℝ)⁻¹) := by
    refine ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ fun u : ModelSpace ↦ ‖u‖ ^ 2).add
      contDiff_const).inv ?_
    intro u
    positivity
  have hnumerator :
      ContDiff ℝ ∞
        (fun u : ModelSpace ↦
          (WithLp.toLp 2
            (Fin.snoc (fun i : Fin n ↦ (2 : ℝ) * u i) (1 - ‖u‖ ^ 2)) : AmbientSpace)) := by
    refine PiLp.contDiff_toLp.comp ?_
    refine contDiff_pi.2 ?_
    intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa [Fin.snoc] using
        (contDiff_const.sub
          (contDiff_norm_sq ℝ : ContDiff ℝ ∞ fun u : ModelSpace ↦ ‖u‖ ^ 2))
    · intro j
      simpa [Fin.snoc] using
        contDiff_const.mul (contDiff_piLp_apply (p := 2) (i := j))
  -- The same scalar factor smooths the south numerator as well.
  simpa [stereographicSouthInvVector] using hscalar.smul hnumerator

/-- Helper for Problem 1-7: the explicit north stereographic map is `C^∞` for the standard sphere
smooth structure. -/
lemma contMDiffOn_stereographicNorthMap_standard :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (stereographicNorthMap n)
      (northPoleComplement n : Set UnitSphere) := by
  -- Route correction: use the explicit ambient rational formula and compose it with the smooth
  -- inclusion `S^n ↪ ℝ^(n+1)` instead of unfolding the standard pole chart.
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  simpa [stereographicNorthMap] using
    (contDiffOn_stereographicNorthAmbient (n := n)).contMDiffOn.comp
      ((contMDiff_coe_sphere (E := AmbientSpace) (m := (∞ : ℕ∞ω)) (n := n)).contMDiffOn)
      (fun x hx ↦ by simpa using northDenominator_ne_zero n hx)

/-- Helper for Problem 1-7: the explicit south stereographic map is `C^∞` for the standard sphere
smooth structure. -/
lemma contMDiffOn_stereographicSouthMap_standard :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (stereographicSouthMap n)
      (southPoleComplement n : Set UnitSphere) := by
  -- Route correction: as in the north-pole case, compose the ambient rational formula with the
  -- smooth sphere inclusion.
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  simpa [stereographicSouthMap] using
    (contDiffOn_stereographicSouthAmbient (n := n)).contMDiffOn.comp
      ((contMDiff_coe_sphere (E := AmbientSpace) (m := (∞ : ℕ∞ω)) (n := n)).contMDiffOn)
      (fun x hx ↦ by simpa using southDenominator_ne_zero n hx)

/-- Helper for Problem 1-7: the explicit north inverse map is `C^∞` for the standard sphere
smooth structure. -/
lemma contMDiff_stereographicNorthInv_standard :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (stereographicNorthInv n) := by
  -- Route correction: build the sphere-valued inverse by codomain-restricting the smooth ambient
  -- inverse vector formula.
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  simpa [stereographicNorthInv] using
    (ContMDiff.codRestrict_sphere (E := AmbientSpace) (n := n)
      ((contDiff_stereographicNorthInvVector (n := n)).contMDiff)
      (fun u ↦ stereographicNorthInvVector_mem_unitSphere n u))

/-- Helper for Problem 1-7: the explicit south inverse map is `C^∞` for the standard sphere
smooth structure. -/
lemma contMDiff_stereographicSouthInv_standard :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (stereographicSouthInv n) := by
  -- Route correction: the south inverse is the same codomain-restriction argument.
  haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
  simpa [stereographicSouthInv] using
    (ContMDiff.codRestrict_sphere (E := AmbientSpace) (n := n)
      ((contDiff_stereographicSouthInvVector (n := n)).contMDiff)
      (fun u ↦ stereographicSouthInvVector_mem_unitSphere n u))

/-- Helper for Problem 1-7: the explicit north stereographic chart belongs to the standard smooth
maximal atlas on `S^n`. -/
lemma stereographicNorthChart_mem_standardMaximalAtlas :
    stereographicNorthChart n ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
  let c : ChartedSpace ModelSpace UnitSphere := inferInstance
  letI := c
  haveI : IsManifold (𝓡 n) ∞ UnitSphere := by
    letI : IsManifold (𝓡 n) ω UnitSphere := by infer_instance
    exact IsManifold.of_le (I := 𝓡 n) (M := UnitSphere) (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω))
      (by simp)
  have hc : OpenPartialHomeomorph.IsSmoothAtlas (𝓡 n) c.atlas := by
    infer_instance
  -- Route correction: use Proposition 1.17's maximal-atlas criterion and prove every transition
  -- to a standard atlas chart is smooth in both directions.
  change stereographicNorthChart n ∈ (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas UnitSphere
  rw [(smooth_structure_determined_by_atlas (I := 𝓡 n) c hc).2.2 (e := stereographicNorthChart n)]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
    exact IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'
  have hforward :
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ ((stereographicNorthChart n).symm.trans e')
        (((stereographicNorthChart n).symm.trans e').source) := by
    -- The forward transition is `e' ∘ stereographicNorthInv`, smooth by composition.
    simpa [stereographicNorthChart, OpenPartialHomeomorph.trans_source] using
      (contMDiffOn_of_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'max).comp
        ((contMDiff_stereographicNorthInv_standard n).contMDiffOn)
        (fun u hu ↦ hu)
  have hreverse :
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (((stereographicNorthChart n).symm.trans e').symm)
        (((stereographicNorthChart n).symm.trans e').target) := by
    -- The inverse transition is `stereographicNorthMap ∘ e'.symm`, again smooth by composition.
    simpa [stereographicNorthChart, OpenPartialHomeomorph.trans_source] using
      (contMDiffOn_stereographicNorthMap_standard n).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'max)
  exact mem_contDiffGroupoid_of_contMDiffOn n hforward.contDiffOn hreverse.contDiffOn

/-- Helper for Problem 1-7: the explicit south stereographic chart belongs to the standard smooth
maximal atlas on `S^n`. -/
lemma stereographicSouthChart_mem_standardMaximalAtlas :
    stereographicSouthChart n ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
  let c : ChartedSpace ModelSpace UnitSphere := inferInstance
  letI := c
  haveI : IsManifold (𝓡 n) ∞ UnitSphere := by
    letI : IsManifold (𝓡 n) ω UnitSphere := by infer_instance
    exact IsManifold.of_le (I := 𝓡 n) (M := UnitSphere) (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω))
      (by simp)
  have hc : OpenPartialHomeomorph.IsSmoothAtlas (𝓡 n) c.atlas := by
    infer_instance
  -- Route correction: use the same maximal-atlas criterion, now for the south chart.
  change stereographicSouthChart n ∈ (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas UnitSphere
  rw [(smooth_structure_determined_by_atlas (I := 𝓡 n) c hc).2.2 (e := stereographicSouthChart n)]
  intro e' he'
  have he'max : e' ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
    exact IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'
  have hforward :
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ ((stereographicSouthChart n).symm.trans e')
        (((stereographicSouthChart n).symm.trans e').source) := by
    -- The forward transition is `e' ∘ stereographicSouthInv`.
    simpa [stereographicSouthChart, OpenPartialHomeomorph.trans_source] using
      (contMDiffOn_of_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'max).comp
        ((contMDiff_stereographicSouthInv_standard n).contMDiffOn)
        (fun u hu ↦ hu)
  have hreverse :
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ (((stereographicSouthChart n).symm.trans e').symm)
        (((stereographicSouthChart n).symm.trans e').target) := by
    -- The inverse transition is `stereographicSouthMap ∘ e'.symm`.
    simpa [stereographicSouthChart, OpenPartialHomeomorph.trans_source] using
      (contMDiffOn_stereographicSouthMap_standard n).comp'
        (contMDiffOn_symm_of_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'max)
  exact mem_contDiffGroupoid_of_contMDiffOn n hforward.contDiffOn hreverse.contDiffOn

/-- Problem 1-7: the smooth structure defined by the two stereographic charts has the same
maximal smooth atlas as the standard sphere smooth structure from Example 1.31. -/
theorem stereographic_two_chart_same_smooth_structure :
    (letI := stereographicSphereChartedSpace n
      ; (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas UnitSphere) =
      (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas UnitSphere := by
  let c : ChartedSpace ModelSpace UnitSphere := stereographicSphereChartedSpace n
  let cStd : ChartedSpace ModelSpace UnitSphere :=
    instChartedSpaceEuclideanSpaceRealFinElemHAddNatOfNatSphere n
  have hstdManifold : IsManifold (𝓡 n) ∞ UnitSphere := by
    letI := cStd
    haveI := Fact.mk (@finrank_euclideanSpace_fin ℝ _ (n + 1))
    letI : IsManifold (𝓡 n) ω UnitSphere := EuclideanSpace.instIsManifoldSphere (n := n)
    exact IsManifold.of_le (I := 𝓡 n) (M := UnitSphere) (m := (∞ : ℕ∞ω)) (n := (⊤ : ℕ∞ω))
      (by simp)
  have hcStd :
      OpenPartialHomeomorph.IsSmoothAtlas (𝓡 n) cStd.atlas := by
    letI := cStd
    letI : IsManifold (𝓡 n) ∞ UnitSphere := hstdManifold
    infer_instance
  have hc : OpenPartialHomeomorph.IsSmoothAtlas (𝓡 n) c.atlas := by
    letI := c
    letI : IsManifold (𝓡 n) ∞ UnitSphere := stereographic_two_chart_isManifold n
    infer_instance
  have hunion :
      OpenPartialHomeomorph.IsSmoothAtlas (𝓡 n)
        (c.atlas ∪ cStd.atlas) := by
    refine ⟨?_, ?_⟩
    · intro x
      letI := c
      exact ⟨chartAt ModelSpace x, Or.inl (chart_mem_atlas ModelSpace x),
        mem_chart_source ModelSpace x⟩
    · intro e e' he he'
      rcases he with he | he
      · rcases he' with he' | he'
        · letI := c
          exact hc.compatible he he'
        · letI : IsManifold (𝓡 n) ∞ UnitSphere := hstdManifold
          letI := cStd
          have hem : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
            rcases he with rfl | rfl
            · simpa [cStd] using stereographicNorthChart_mem_standardMaximalAtlas n
            · simpa [cStd] using stereographicSouthChart_mem_standardMaximalAtlas n
          have he'm : e' ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
            exact IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he'
          exact IsManifold.compatible_of_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω))
            hem he'm
      · rcases he' with he' | he'
        · letI : IsManifold (𝓡 n) ∞ UnitSphere := hstdManifold
          letI := cStd
          have hem : e ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
            exact IsManifold.subset_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω)) he
          have he'm : e' ∈ IsManifold.maximalAtlas (𝓡 n) ∞ UnitSphere := by
            rcases he' with rfl | rfl
            · simpa [cStd] using stereographicNorthChart_mem_standardMaximalAtlas n
            · simpa [cStd] using stereographicSouthChart_mem_standardMaximalAtlas n
          exact IsManifold.compatible_of_mem_maximalAtlas (I := 𝓡 n) (n := (∞ : ℕ∞ω))
            hem he'm
        · letI := cStd
          exact hcStd.compatible he he'
  exact (same_smooth_structure_iff_union_is_smooth_atlas c cStd hc hcStd).2 hunion

end Problem17

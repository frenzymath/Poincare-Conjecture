import PetersenLib.Ch04.BiinvariantMetrics

/-!
# Curvature of a general left-invariant metric on a Lie group

Petersen §3.4, Exercises 3.4.27 and 3.4.31. We work at the level of the Lie
algebra `𝔤`, modelled as a finite-dimensional real inner-product space `V`
carrying the bracket as an explicit bilinear map `bracket : V →ₗ[ℝ] V →ₗ[ℝ] V`
(the same device as `PetersenLib.Ch04.BiinvariantMetrics`, avoiding the
`AddCommGroup` diamond between `LieRing` and `InnerProductSpace`).

For a **left-invariant** metric — the inner product is constant along the group,
so all `X⟪Y,Z⟫`-type terms in Koszul's formula vanish — the Levi-Civita
connection of left-invariant fields is entirely algebraic:
`∇_X Y = ½([X,Y] − ad*_X Y − ad*_Y X)`, where `ad*_X` is the metric adjoint of
`ad_X = [X, ·]`.  (Petersen states this with a `+ad*_X Y`; with the *standard*
adjoint convention `⟪ad*_X Y, Z⟫ = ⟪Y, [X,Z]⟫` used here and in Mathlib the
correct sign is `−ad*_X Y`, as one checks by specialising to a biinvariant
metric, where `ad*_X = −ad_X` and the formula must reduce to `∇_X Y = ½[X,Y]`.)

Here the metric is positive definite (an honest `InnerProductSpace`), the case
needed for Mathlib's `LinearMap.adjoint`; Petersen allows an indefinite
nondegenerate metric, of which this is the Riemannian special case.

Main results:
* `leftInvariantConnection_torsionFree`, `leftInvariantConnection_metricCompat`:
  the algebraic connection really is the Levi-Civita connection (torsion-free
  and metric-compatible) — Exercise 3.4.31(1).
* `exercise3_4_27`: in a `g`-orthonormal frame with structure constants
  `cᵏᵢⱼ = ⟪[Eᵢ,Eⱼ],Eₖ⟫`, the Christoffel symbols and curvature components are
  `Γᵏᵢⱼ = ½(cᵏᵢⱼ − cʲᵢₖ − cⁱⱼₖ)` and
  `Rˡᵢⱼₖ = ∑ₘ (ΓᵐⱼₖΓˡᵢₘ − ΓᵐᵢₖΓˡⱼₘ − cᵐᵢⱼΓˡₘₖ)`.
-/

open scoped RealInnerProductSpace
open Finset

noncomputable section

namespace PetersenLib

section LeftInvariant

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- `ad*_x`, the metric adjoint of `ad_x = bracket x : V →ₗ V`. -/
def adStar (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x : V) : V →ₗ[ℝ] V :=
  LinearMap.adjoint (bracket x)

/-- Defining property of the adjoint: `⟪ad*_x y, z⟫ = ⟪y, [x, z]⟫`. -/
@[simp] theorem adStar_inner (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y z : V) :
    ⟪adStar bracket x y, z⟫ = ⟪y, bracket x z⟫ :=
  LinearMap.adjoint_inner_left (bracket x) z y

/-- Defining property of the adjoint in the right slot: `⟪y, ad*_x z⟫ = ⟪[x, y], z⟫`. -/
@[simp] theorem inner_adStar (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y z : V) :
    ⟪y, adStar bracket x z⟫ = ⟪bracket x y, z⟫ :=
  LinearMap.adjoint_inner_right (bracket x) y z

/-- The **left-invariant Levi-Civita connection**
`∇_x y = ½([x,y] − ad*_x y − ad*_y x)`. -/
def leftInvariantConnection (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y : V) : V :=
  (2⁻¹ : ℝ) • (bracket x y - adStar bracket x y - adStar bracket y x)

@[inherit_doc] scoped notation "∇[" b "]" => leftInvariantConnection b

/-- The connection is additive in its second (differentiated) argument. -/
theorem leftInvariantConnection_add_right (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y y' : V) :
    leftInvariantConnection bracket x (y + y')
      = leftInvariantConnection bracket x y + leftInvariantConnection bracket x y' := by
  simp only [leftInvariantConnection, adStar, map_add, LinearMap.add_apply]
  module

/-- The connection is `ℝ`-homogeneous in its second argument. -/
theorem leftInvariantConnection_smul_right (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (a : ℝ) (x y : V) :
    leftInvariantConnection bracket x (a • y)
      = a • leftInvariantConnection bracket x y := by
  simp only [leftInvariantConnection, adStar, map_smul, LinearMap.smul_apply]
  module

/-- Expansion of the connection over a finite sum in the second argument. -/
theorem leftInvariantConnection_sum_right {ι : Type*} (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (x : V) (s : Finset ι) (f : ι → ℝ) (v : ι → V) :
    leftInvariantConnection bracket x (∑ i ∈ s, f i • v i)
      = ∑ i ∈ s, f i • leftInvariantConnection bracket x (v i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [leftInvariantConnection, adStar]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, leftInvariantConnection_add_right,
      leftInvariantConnection_smul_right, ih]

/-- **Exercise 3.4.31(1), torsion-freeness.** `∇_x y − ∇_y x = [x, y]`. -/
theorem leftInvariantConnection_torsionFree (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (hskew : ∀ x : V, bracket x x = 0) (x y : V) :
    leftInvariantConnection bracket x y - leftInvariantConnection bracket y x = bracket x y := by
  have hsk : bracket y x = -bracket x y := bracket_skew hskew y x
  simp only [leftInvariantConnection, hsk]
  module

/-- **Exercise 3.4.31(1), metric compatibility.** For a left-invariant metric the
Koszul connection is compatible with the (constant) inner product:
`⟪∇_x y, z⟫ + ⟪y, ∇_x z⟫ = 0`. Needs only skew-symmetry of the bracket. -/
theorem leftInvariantConnection_metricCompat (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (hskew : ∀ x : V, bracket x x = 0) (x y z : V) :
    ⟪leftInvariantConnection bracket x y, z⟫ + ⟪y, leftInvariantConnection bracket x z⟫ = 0 := by
  have e1 : ⟪leftInvariantConnection bracket x y, z⟫
      = 2⁻¹ * (⟪bracket x y, z⟫ - ⟪y, bracket x z⟫ - ⟪x, bracket y z⟫) := by
    simp only [leftInvariantConnection, inner_sub_left, real_inner_smul_left, adStar_inner]
  have e2 : ⟪y, leftInvariantConnection bracket x z⟫
      = 2⁻¹ * (⟪y, bracket x z⟫ - ⟪bracket x y, z⟫ - ⟪bracket z y, x⟫) := by
    simp only [leftInvariantConnection, inner_sub_right, real_inner_smul_right, inner_adStar]
  have hc : ⟪bracket z y, x⟫ = -⟪x, bracket y z⟫ := by
    rw [bracket_skew hskew z y, inner_neg_left, real_inner_comm]
  rw [e1, e2, hc]
  ring

/-- The connection is additive in its first (direction) argument. -/
theorem leftInvariantConnection_add_left (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x x' y : V) :
    leftInvariantConnection bracket (x + x') y
      = leftInvariantConnection bracket x y + leftInvariantConnection bracket x' y := by
  simp only [leftInvariantConnection, adStar, map_add, LinearMap.add_apply]
  module

/-- The connection is `ℝ`-homogeneous in its first argument. -/
theorem leftInvariantConnection_smul_left (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (a : ℝ) (x y : V) :
    leftInvariantConnection bracket (a • x) y = a • leftInvariantConnection bracket x y := by
  simp only [leftInvariantConnection, adStar, map_smul, LinearMap.smul_apply]
  module

/-- Expansion of the connection over a finite sum in the first argument. -/
theorem leftInvariantConnection_sum_left {ι : Type*} (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (y : V) (s : Finset ι) (f : ι → ℝ) (v : ι → V) :
    leftInvariantConnection bracket (∑ i ∈ s, f i • v i) y
      = ∑ i ∈ s, f i • leftInvariantConnection bracket (v i) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [leftInvariantConnection, adStar]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, leftInvariantConnection_add_left,
      leftInvariantConnection_smul_left, ih]

/-- Frame expansion of `⟪∇_a u, w⟫` in the second argument. -/
theorem inner_leftInvariantConnection_right_expand (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (a u w : V) :
    ⟪leftInvariantConnection bracket a u, w⟫
      = ∑ m, ⟪u, stdOrthonormalBasis ℝ V m⟫
          * ⟪leftInvariantConnection bracket a (stdOrthonormalBasis ℝ V m), w⟫ := by
  set e := stdOrthonormalBasis ℝ V with he
  conv_lhs => rw [← e.sum_repr u]
  rw [leftInvariantConnection_sum_right, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [real_inner_smul_left, e.repr_apply_apply, real_inner_comm (e m) u]

/-- Frame expansion of `⟪∇_u a, w⟫` in the first argument. -/
theorem inner_leftInvariantConnection_left_expand (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (u a w : V) :
    ⟪leftInvariantConnection bracket u a, w⟫
      = ∑ m, ⟪u, stdOrthonormalBasis ℝ V m⟫
          * ⟪leftInvariantConnection bracket (stdOrthonormalBasis ℝ V m) a, w⟫ := by
  set e := stdOrthonormalBasis ℝ V with he
  conv_lhs => rw [← e.sum_repr u]
  rw [leftInvariantConnection_sum_left, sum_inner]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [real_inner_smul_left, e.repr_apply_apply, real_inner_comm (e m) u]

/-! ## The curvature of the left-invariant connection -/

/-- `R(x,y)z = ∇_x(∇_y z) − ∇_y(∇_x z) − ∇_{[x,y]}z`. -/
def leftInvariantCurvature (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y z : V) : V :=
  leftInvariantConnection bracket x (leftInvariantConnection bracket y z)
    - leftInvariantConnection bracket y (leftInvariantConnection bracket x z)
    - leftInvariantConnection bracket (bracket x y) z

/-- The `(0,4)`-curvature `R(x,y,z,w) = ⟪R(x,y)z, w⟫`. -/
def leftInvariantCurvatureFour (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (x y z w : V) : ℝ :=
  ⟪leftInvariantCurvature bracket x y z, w⟫

/-- **Exercise 3.4.31(2).** For a left-invariant metric the `(0,4)`-curvature is
`R(X,Y,Z,W) = −(∇_Y Z, ∇_X W) + (∇_X Z, ∇_Y W) − (∇_{[X,Y]}Z, W)`, obtained by
moving `∇_X`, `∇_Y` across the metric (compatibility) in the second-covariant
derivatives. -/
theorem leftInvariantCurvatureFour_eq (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (hskew : ∀ x : V, bracket x x = 0) (x y z w : V) :
    leftInvariantCurvatureFour bracket x y z w
      = -⟪leftInvariantConnection bracket y z, leftInvariantConnection bracket x w⟫
        + ⟪leftInvariantConnection bracket x z, leftInvariantConnection bracket y w⟫
        - ⟪leftInvariantConnection bracket (bracket x y) z, w⟫ := by
  unfold leftInvariantCurvatureFour leftInvariantCurvature
  rw [inner_sub_left, inner_sub_left]
  have m1 : ⟪leftInvariantConnection bracket x (leftInvariantConnection bracket y z), w⟫
      = -⟪leftInvariantConnection bracket y z, leftInvariantConnection bracket x w⟫ := by
    have := leftInvariantConnection_metricCompat bracket hskew x
      (leftInvariantConnection bracket y z) w
    linarith
  have m2 : ⟪leftInvariantConnection bracket y (leftInvariantConnection bracket x z), w⟫
      = -⟪leftInvariantConnection bracket x z, leftInvariantConnection bracket y w⟫ := by
    have := leftInvariantConnection_metricCompat bracket hskew y
      (leftInvariantConnection bracket x z) w
    linarith
  rw [m1, m2]; ring

omit [FiniteDimensional ℝ V] in
/-- Difference-of-squares identity for a real inner product:
`⟪u − v, u + v⟫ = ⟪u, u⟫ − ⟪v, v⟫`. -/
private theorem inner_sub_add_diff (u v : V) :
    ⟪u - v, u + v⟫ = ⟪u, u⟫ - ⟪v, v⟫ := by
  rw [inner_sub_left, inner_add_right, inner_add_right, real_inner_comm v u]
  ring

/-- **Exercise 3.4.31(3).** The sectional-curvature numerator of a left-invariant
metric:
`R(X,Y,Y,X) = ¼|ad*_X Y + ad*_Y X|² − (ad*_X X, ad*_Y Y) − ¾|[X,Y]|²
              − ½([[X,Y],Y],X) − ½([[Y,X],X],Y)`. -/
theorem leftInvariantCurvatureFour_self (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (hskew : ∀ x : V, bracket x x = 0) (x y : V) :
    leftInvariantCurvatureFour bracket x y y x
      = 4⁻¹ * ⟪adStar bracket x y + adStar bracket y x, adStar bracket x y + adStar bracket y x⟫
        - ⟪adStar bracket x x, adStar bracket y y⟫
        - 4⁻¹ * 3 * ⟪bracket x y, bracket x y⟫
        - 2⁻¹ * ⟪bracket (bracket x y) y, x⟫
        - 2⁻¹ * ⟪bracket (bracket y x) x, y⟫ := by
  rw [leftInvariantCurvatureFour_eq bracket hskew x y y x]
  have hself : ∀ a : V, leftInvariantConnection bracket a a = -adStar bracket a a := by
    intro a; simp only [leftInvariantConnection, hskew a]; module
  -- (II) `⟪∇_y y, ∇_x x⟫ = (ad*_x x, ad*_y y)`
  have hII : ⟪leftInvariantConnection bracket y y, leftInvariantConnection bracket x x⟫
      = ⟪adStar bracket x x, adStar bracket y y⟫ := by
    rw [hself y, hself x]
    simp only [inner_neg_left, inner_neg_right, neg_neg]
    rw [real_inner_comm]
  -- (I) `⟪∇_x y, ∇_y x⟫ = ¼|ad*_x y + ad*_y x|² − ¼|[x,y]|²`
  have hI : ⟪leftInvariantConnection bracket x y, leftInvariantConnection bracket y x⟫
      = 4⁻¹ * ⟪adStar bracket x y + adStar bracket y x, adStar bracket x y + adStar bracket y x⟫
        - 4⁻¹ * ⟪bracket x y, bracket x y⟫ := by
    have h1 : leftInvariantConnection bracket x y
        = (2⁻¹ : ℝ) • (bracket x y - (adStar bracket x y + adStar bracket y x)) := by
      simp only [leftInvariantConnection]; rw [sub_sub]
    have h2 : leftInvariantConnection bracket y x
        = -((2⁻¹ : ℝ) • (bracket x y + (adStar bracket x y + adStar bracket y x))) := by
      simp only [leftInvariantConnection, bracket_skew hskew y x]; module
    rw [h1, h2, real_inner_smul_left, inner_neg_right, real_inner_smul_right,
      inner_sub_add_diff]
    ring
  -- (III) `⟪∇_{[x,y]}y, x⟫ = ½([[x,y],y],x) − ½([[x,y],x],y) + ½|[x,y]|²`
  have hIII : ⟪leftInvariantConnection bracket (bracket x y) y, x⟫
      = 2⁻¹ * ⟪bracket (bracket x y) y, x⟫ - 2⁻¹ * ⟪bracket (bracket x y) x, y⟫
        + 2⁻¹ * ⟪bracket x y, bracket x y⟫ := by
    simp only [leftInvariantConnection, inner_sub_left, real_inner_smul_left, adStar_inner]
    rw [real_inner_comm y (bracket (bracket x y) x), bracket_skew hskew y x, inner_neg_right]
    ring
  have hlast : ⟪bracket (bracket y x) x, y⟫ = -⟪bracket (bracket x y) x, y⟫ := by
    rw [bracket_skew hskew y x, map_neg, LinearMap.neg_apply, inner_neg_left]
  rw [hI, hII, hIII, hlast]
  ring

/-- **Exercise 3.4.31.** Let `G` be a Lie group with a (positive-definite)
left-invariant metric on `𝔤`, and `ad*_X` the metric adjoint of `ad_X = [X,·]`.
Then, for left-invariant fields:

1. `∇_X Y = ½([X,Y] − ad*_X Y − ad*_Y X)` (`leftInvariantConnection`) is the
   Levi-Civita connection: it is torsion-free and metric-compatible (and lands in
   `𝔤`). *(Petersen prints `+ad*_X Y`; with the standard/Mathlib adjoint
   convention `⟪ad*_X Y, Z⟫ = ⟪Y, [X,Z]⟫` the sign must be `−ad*_X Y`, as the
   biinvariant specialisation `∇_X Y = ½[X,Y]` shows.)*
2. `R(X,Y,Z,W) = −(∇_Y Z, ∇_X W) + (∇_X Z, ∇_Y W) − (∇_{[X,Y]}Z, W)`.
3. `R(X,Y,Y,X) = ¼|ad*_X Y + ad*_Y X|² − (ad*_X X, ad*_Y Y) − ¾|[X,Y]|²
                 − ½([[X,Y],Y],X) − ½([[Y,X],X],Y)`. -/
theorem exercise3_4_31 (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V) (hskew : ∀ x : V, bracket x x = 0) :
    (∀ x y : V, leftInvariantConnection bracket x y
        - leftInvariantConnection bracket y x = bracket x y)
    ∧ (∀ x y z : V, ⟪leftInvariantConnection bracket x y, z⟫
        + ⟪y, leftInvariantConnection bracket x z⟫ = 0)
    ∧ (∀ x y z w : V, leftInvariantCurvatureFour bracket x y z w
        = -⟪leftInvariantConnection bracket y z, leftInvariantConnection bracket x w⟫
          + ⟪leftInvariantConnection bracket x z, leftInvariantConnection bracket y w⟫
          - ⟪leftInvariantConnection bracket (bracket x y) z, w⟫)
    ∧ (∀ x y : V, leftInvariantCurvatureFour bracket x y y x
        = 4⁻¹ * ⟪adStar bracket x y + adStar bracket y x, adStar bracket x y + adStar bracket y x⟫
          - ⟪adStar bracket x x, adStar bracket y y⟫
          - 4⁻¹ * 3 * ⟪bracket x y, bracket x y⟫
          - 2⁻¹ * ⟪bracket (bracket x y) y, x⟫
          - 2⁻¹ * ⟪bracket (bracket y x) x, y⟫) :=
  ⟨leftInvariantConnection_torsionFree bracket hskew,
   leftInvariantConnection_metricCompat bracket hskew,
   leftInvariantCurvatureFour_eq bracket hskew,
   leftInvariantCurvatureFour_self bracket hskew⟩

/-! ## Exercise 3.4.27 — structure constants of an orthonormal left-invariant frame -/

variable (bracket : V →ₗ[ℝ] V →ₗ[ℝ] V)

/-- Structure constants of an orthonormal frame `Eᵢ = stdOrthonormalBasis`:
`cᵏᵢⱼ = ⟪[Eᵢ,Eⱼ], Eₖ⟫`, so `[Eᵢ,Eⱼ] = ∑ₖ cᵏᵢⱼ Eₖ`. -/
def structureConstant (i j k : Fin (Module.finrank ℝ V)) : ℝ :=
  ⟪bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j), stdOrthonormalBasis ℝ V k⟫

/-- Christoffel symbols of the left-invariant connection in the orthonormal frame:
`Γᵏᵢⱼ = ⟪∇_{Eᵢ}Eⱼ, Eₖ⟫`. -/
def christoffel (i j k : Fin (Module.finrank ℝ V)) : ℝ :=
  ⟪leftInvariantConnection bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j),
    stdOrthonormalBasis ℝ V k⟫

/-- Curvature components in the orthonormal frame: `Rˡᵢⱼₖ = ⟪R(Eᵢ,Eⱼ)Eₖ, Eₗ⟫`. -/
def curvatureComponent (i j k l : Fin (Module.finrank ℝ V)) : ℝ :=
  ⟪leftInvariantCurvature bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j)
    (stdOrthonormalBasis ℝ V k), stdOrthonormalBasis ℝ V l⟫

/-- **Exercise 3.4.27, Christoffel symbols.** `Γᵏᵢⱼ = ½(cᵏᵢⱼ − cʲᵢₖ − cⁱⱼₖ)`; this is
Koszul's formula for an orthonormal frame, where the metric-derivative terms
vanish. -/
theorem christoffel_eq (i j k : Fin (Module.finrank ℝ V)) :
    christoffel bracket i j k
      = 2⁻¹ * (structureConstant bracket i j k - structureConstant bracket i k j
        - structureConstant bracket j k i) := by
  simp only [christoffel, structureConstant, leftInvariantConnection, inner_sub_left,
    real_inner_smul_left, adStar_inner]
  rw [real_inner_comm (stdOrthonormalBasis ℝ V j)
      (bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V k)),
    real_inner_comm (stdOrthonormalBasis ℝ V i)
      (bracket (stdOrthonormalBasis ℝ V j) (stdOrthonormalBasis ℝ V k))]

/-- **Exercise 3.4.27, curvature components.**
`Rˡᵢⱼₖ = ∑ₘ (ΓᵐⱼₖΓˡᵢₘ − ΓᵐᵢₖΓˡⱼₘ − cᵐᵢⱼΓˡₘₖ)`, from expanding
`R(Eᵢ,Eⱼ)Eₖ = ∇_{Eᵢ}∇_{Eⱼ}Eₖ − ∇_{Eⱼ}∇_{Eᵢ}Eₖ − ∇_{[Eᵢ,Eⱼ]}Eₖ` in the frame. -/
theorem curvatureComponent_eq (i j k l : Fin (Module.finrank ℝ V)) :
    curvatureComponent bracket i j k l
      = ∑ m, (christoffel bracket j k m * christoffel bracket i m l
              - christoffel bracket i k m * christoffel bracket j m l
              - structureConstant bracket i j m * christoffel bracket m k l) := by
  have t1 : ⟪leftInvariantConnection bracket (stdOrthonormalBasis ℝ V i)
        (leftInvariantConnection bracket (stdOrthonormalBasis ℝ V j) (stdOrthonormalBasis ℝ V k)),
        stdOrthonormalBasis ℝ V l⟫
      = ∑ m, christoffel bracket j k m * christoffel bracket i m l := by
    rw [inner_leftInvariantConnection_right_expand]; rfl
  have t2 : ⟪leftInvariantConnection bracket (stdOrthonormalBasis ℝ V j)
        (leftInvariantConnection bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V k)),
        stdOrthonormalBasis ℝ V l⟫
      = ∑ m, christoffel bracket i k m * christoffel bracket j m l := by
    rw [inner_leftInvariantConnection_right_expand]; rfl
  have t3 : ⟪leftInvariantConnection bracket
        (bracket (stdOrthonormalBasis ℝ V i) (stdOrthonormalBasis ℝ V j))
        (stdOrthonormalBasis ℝ V k), stdOrthonormalBasis ℝ V l⟫
      = ∑ m, structureConstant bracket i j m * christoffel bracket m k l := by
    rw [inner_leftInvariantConnection_left_expand]; rfl
  simp only [curvatureComponent, leftInvariantCurvature, inner_sub_left]
  rw [t1, t2, t3, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

/-- **Exercise 3.4.27.** For a Lie group with a left-invariant metric and an
orthonormal frame `Eᵢ` with structure constants `cᵏᵢⱼ = ⟪[Eᵢ,Eⱼ], Eₖ⟫`, the
Christoffel symbols and curvature components of the Levi-Civita connection are
computed purely from the `cᵏᵢⱼ`:
`Γᵏᵢⱼ = ½(cᵏᵢⱼ − cʲᵢₖ − cⁱⱼₖ)` and
`Rˡᵢⱼₖ = ∑ₘ (ΓᵐⱼₖΓˡᵢₘ − ΓᵐᵢₖΓˡⱼₘ − cᵐᵢⱼΓˡₘₖ)`. On a Lie group the `cᵏᵢⱼ` for a
left-invariant frame are constant, so all derivative terms drop out (as reflected
by the algebraic, position-free connection here). -/
theorem exercise3_4_27 :
    (∀ i j k : Fin (Module.finrank ℝ V), christoffel bracket i j k
        = 2⁻¹ * (structureConstant bracket i j k - structureConstant bracket i k j
          - structureConstant bracket j k i))
    ∧ (∀ i j k l : Fin (Module.finrank ℝ V), curvatureComponent bracket i j k l
        = ∑ m, (christoffel bracket j k m * christoffel bracket i m l
                - christoffel bracket i k m * christoffel bracket j m l
                - structureConstant bracket i j m * christoffel bracket m k l)) :=
  ⟨christoffel_eq bracket, curvatureComponent_eq bracket⟩

end LeftInvariant

end PetersenLib

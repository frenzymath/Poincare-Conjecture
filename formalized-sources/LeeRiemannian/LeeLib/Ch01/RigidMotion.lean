import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Topology.MetricSpace.Congruence

/-!
# Rigid motions and the isometry extension theorem

Lee introduces congruence of plane figures through *rigid motions*: a rigid motion of the plane is a
bijective transformation of the plane onto itself that preserves distances, and two figures are
congruent when a rigid motion carries one onto the other. In a real inner product space `E` a rigid
motion is modelled by an `AffineIsometryEquiv`, `E ≃ᵃⁱ[ℝ] E`; by the Mazur-Ulam theorem every
distance-preserving bijection of `E` is automatically affine, so nothing is lost by building
affineness into the model.

The main result is the *isometry extension theorem*: a correspondence between two families of points
that preserves all pairwise distances is realised by a rigid motion of the whole ambient space,
provided the space is finite-dimensional. This is the substance behind the classical congruence
criteria — it converts the numerical statement "corresponding distances agree" into the geometric
statement "a rigid motion carries one figure onto the other".

## Main statements

* `LeeLib.Ch01.exists_linearIsometryEquiv_of_inner_eq`: a correspondence between two families of
  vectors preserving all pairwise inner products extends to a linear isometry of the whole space.
* `LeeLib.Ch01.exists_affineIsometryEquiv_of_dist_eq`: the isometry extension theorem — a
  correspondence between two families of points preserving all pairwise distances extends to a rigid
  motion of the whole space.

## Implementation notes

The extension is built in three steps. Fixing a base point reduces distances to inner products by
polarisation. A family of vectors with prescribed inner products then determines an isometry on the
span of the family: the linear combinations of the two families have equal norms, so the two
coefficient maps `(ι →₀ ℝ) → E` have the same kernel and the induced map on the span is well defined
and norm-preserving. Finally `LinearIsometry.extend` carries the isometry off the span to the whole
space, which requires finite-dimensionality.
-/

noncomputable section

namespace LeeLib.Ch01

open Finsupp Submodule LinearMap Module
open scoped RealInnerProductSpace

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Linear combinations of a family with prescribed inner products -/

/-- The inner product of two linear combinations of a family expands as the corresponding double sum
of pairwise inner products, weighted by the coefficients. -/
theorem inner_linearCombination_linearCombination (v : ι → E) (c d : ι →₀ ℝ) :
    ⟪linearCombination ℝ v c, linearCombination ℝ v d⟫
      = ∑ i ∈ c.support, ∑ j ∈ d.support, c i * d j * ⟪v i, v j⟫ := by
  rw [linearCombination_apply, linearCombination_apply, Finsupp.sum, Finsupp.sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right, mul_assoc]

/-- If two families have the same pairwise inner products, then corresponding linear combinations of
them have the same norm. -/
theorem norm_linearCombination_eq_of_inner_eq {v w : ι → E}
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) (c : ι →₀ ℝ) :
    ‖linearCombination ℝ v c‖ = ‖linearCombination ℝ w c‖ := by
  have hinner : ⟪linearCombination ℝ v c, linearCombination ℝ v c⟫
      = ⟪linearCombination ℝ w c, linearCombination ℝ w c⟫ := by
    rw [inner_linearCombination_linearCombination, inner_linearCombination_linearCombination]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [h]
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, hinner]

/-- If two families have the same pairwise inner products, then the linear combination maps attached
to them have the same kernel. -/
theorem ker_linearCombination_eq_of_inner_eq {v w : ι → E}
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    ker (linearCombination ℝ v) = ker (linearCombination ℝ w) := by
  have key : ∀ {a b : ι → E}, (∀ i j, ⟪a i, a j⟫ = ⟪b i, b j⟫) →
      ker (linearCombination ℝ a) ≤ ker (linearCombination ℝ b) := by
    intro a b hab c hc
    rw [mem_ker] at hc ⊢
    rw [← norm_eq_zero] at hc ⊢
    rwa [← norm_linearCombination_eq_of_inner_eq hab]
  exact le_antisymm (key h) (key fun i j => (h i j).symm)

/-- The isometry of the span of a family of vectors determined by sending it to a second family with
the same pairwise inner products. It is defined on the range of the coefficient map, which is the
span of the family. -/
def spanIsometryOfInnerEq {v w : ι → E} (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    (range (linearCombination ℝ v)) →ₗᵢ[ℝ] E where
  toLinearMap :=
    ((ker (linearCombination ℝ v)).liftQ (linearCombination ℝ w)
        (le_of_eq (ker_linearCombination_eq_of_inner_eq h))).comp
      (linearCombination ℝ v).quotKerEquivRange.symm.toLinearMap
  norm_map' := by
    rintro ⟨-, c, rfl⟩
    rw [LinearMap.comp_apply]
    rw [LinearEquiv.coe_coe, quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply,
      Submodule.liftQ_apply]
    exact (norm_linearCombination_eq_of_inner_eq h c).symm

/-- `spanIsometryOfInnerEq` sends a linear combination of the first family to the corresponding
linear combination of the second. -/
theorem spanIsometryOfInnerEq_apply {v w : ι → E} (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫)
    (c : ι →₀ ℝ) (hc : linearCombination ℝ v c ∈ range (linearCombination ℝ v)) :
    spanIsometryOfInnerEq h ⟨linearCombination ℝ v c, hc⟩ = linearCombination ℝ w c := by
  show (((ker (linearCombination ℝ v)).liftQ (linearCombination ℝ w) _).comp
    (linearCombination ℝ v).quotKerEquivRange.symm.toLinearMap) _ = _
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, quotKerEquivRange_symm_apply_image,
    Submodule.mkQ_apply, Submodule.liftQ_apply]

/-! ### The isometry extension theorem -/

/-- **Linear isometry extension.** In a finite-dimensional real inner product space, a
correspondence between two families of vectors that preserves all pairwise inner products is
realised by a linear isometry of the whole space. -/
theorem exists_linearIsometryEquiv_of_inner_eq [FiniteDimensional ℝ E] {v w : ι → E}
    (h : ∀ i j, ⟪v i, v j⟫ = ⟪w i, w j⟫) :
    ∃ f : E ≃ₗᵢ[ℝ] E, ∀ i, f (v i) = w i := by
  refine ⟨(spanIsometryOfInnerEq h).extend.toLinearIsometryEquiv rfl, fun i => ?_⟩
  have hv : v i = linearCombination ℝ v (Finsupp.single i 1) := by
    rw [linearCombination_single, one_smul]
  have hw : w i = linearCombination ℝ w (Finsupp.single i 1) := by
    rw [linearCombination_single, one_smul]
  have hmem : linearCombination ℝ v (Finsupp.single i 1) ∈ range (linearCombination ℝ v) :=
    LinearMap.mem_range_self _ _
  rw [LinearIsometry.toLinearIsometryEquiv_apply, hw]
  conv_lhs => rw [hv]
  rw [show (linearCombination ℝ v) (Finsupp.single i 1)
      = ((⟨linearCombination ℝ v (Finsupp.single i 1), hmem⟩ :
          range (linearCombination ℝ v)) : E) from rfl,
    LinearIsometry.extend_apply, spanIsometryOfInnerEq_apply]

/-- Fixing a base point, a correspondence preserving all pairwise distances preserves the inner
products of the difference vectors based at that point. This is the polarisation step. -/
theorem inner_vsub_eq_of_dist_eq {v w : ι → E} (i₀ : ι)
    (h : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) (i j : ι) :
    ⟪v i - v i₀, v j - v i₀⟫ = ⟪w i - w i₀, w j - w i₀⟫ := by
  have expand : ∀ u : ι → E, ⟪u i - u i₀, u j - u i₀⟫
      = (dist (u i) (u i₀) ^ 2 + dist (u j) (u i₀) ^ 2 - dist (u i) (u j) ^ 2) / 2 := by
    intro u
    have hsub : (u i - u i₀) - (u j - u i₀) = u i - u j := by abel
    have := norm_sub_sq_real (u i - u i₀) (u j - u i₀)
    rw [hsub] at this
    simp only [dist_eq_norm]
    linarith
  rw [expand v, expand w, h i i₀, h j i₀, h i j]

/-- **The isometry extension theorem.** In a finite-dimensional real inner product space, a
correspondence between two families of points that preserves all pairwise distances is realised by a
rigid motion of the whole space.

This is the geometric substance behind the classical congruence criteria: it upgrades the numerical
hypothesis that corresponding distances agree to the existence of a rigid motion carrying one figure
onto the other. -/
theorem exists_affineIsometryEquiv_of_dist_eq [FiniteDimensional ℝ E] [Nonempty ι] {v w : ι → E}
    (h : ∀ i j, dist (v i) (v j) = dist (w i) (w j)) :
    ∃ f : E ≃ᵃⁱ[ℝ] E, ∀ i, f (v i) = w i := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  obtain ⟨g, hg⟩ := exists_linearIsometryEquiv_of_inner_eq (inner_vsub_eq_of_dist_eq i₀ h)
  refine ⟨((AffineIsometryEquiv.constVAdd ℝ E (-v i₀)).trans
    g.toAffineIsometryEquiv).trans (AffineIsometryEquiv.constVAdd ℝ E (w i₀)), fun i => ?_⟩
  simp only [AffineIsometryEquiv.coe_trans, Function.comp_apply,
    AffineIsometryEquiv.coe_constVAdd, LinearIsometryEquiv.coe_toAffineIsometryEquiv]
  have hvi : -v i₀ +ᵥ v i = v i - v i₀ := by
    rw [vadd_eq_add]; abel
  rw [hvi, hg i, vadd_eq_add]
  abel

/-- In a finite-dimensional real inner product space, the numerical notion of congruence — all
corresponding distances agree — coincides with the classical geometric one: some rigid motion of the
ambient space carries one family of points onto the other.

The two notions are not interchangeable by definition. `Congruent` is *defined* as equality of all
corresponding distances, so it is the geometric description that carries information here; supplying
it is exactly the isometry extension theorem. -/
theorem congruent_iff_exists_affineIsometryEquiv [FiniteDimensional ℝ E] [Nonempty ι]
    (v w : ι → E) : Congruent v w ↔ ∃ f : E ≃ᵃⁱ[ℝ] E, ∀ i, f (v i) = w i := by
  rw [congruent_iff_dist_eq]
  refine ⟨exists_affineIsometryEquiv_of_dist_eq, ?_⟩
  rintro ⟨f, hf⟩ i j
  rw [← hf i, ← hf j, f.isometry.dist_eq]

end LeeLib.Ch01

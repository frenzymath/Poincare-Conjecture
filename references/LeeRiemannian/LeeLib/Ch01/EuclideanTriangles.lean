import LeeLib.Ch01.RigidMotion

/-!
# Congruence of Euclidean triangles

Lee opens his survey of curvature with two theorems of Euclidean plane geometry, presented as the
prototypes of the two kinds of result that pervade the subject: a *classification theorem* and a
*local-to-global theorem*. This file formalises the classification theorem, the side-side-side
criterion, in the form Lee states it: two triangles are congruent — that is, some rigid motion of the
plane carries one onto the other — precisely when their corresponding side lengths agree.

The content of the criterion lies entirely in the "if" direction, which produces a rigid motion out
of three numerical equalities; it is an instance of the isometry extension theorem
`LeeLib.Ch01.exists_affineIsometryEquiv_of_dist_eq`. The "only if" direction merely records that
rigid motions preserve distances.

## Main statements

* `LeeLib.Ch01.side_side_side_iff`: the side-side-side criterion (Lee, Theorem 1.1).

## Implementation notes

Mathlib's `Congruent` (and hence `EuclideanGeometry.side_side_side`) *defines* congruence of point
families as equality of all corresponding pairwise distances, so the mathlib statement of
side-side-side does not by itself express Lee's theorem: with that definition the equivalence proved
here would be a tautology. Lee's notion of congruence is instead "related by a rigid motion of the
ambient plane", and that is what is used below, so the equivalence has genuine geometric content.
-/

noncomputable section

namespace LeeLib.Ch01

open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Side-Side-Side** (Lee, Theorem 1.1). Two Euclidean triangles are congruent — some rigid motion
of the ambient space carries the vertices of one onto the corresponding vertices of the other — if
and only if the lengths of their corresponding sides are equal.

Congruence is understood in Lee's sense: a rigid motion is a distance-preserving bijection of the
space onto itself, modelled here by an `AffineIsometryEquiv`. -/
theorem side_side_side_iff [FiniteDimensional ℝ E] (a b c a' b' c' : E) :
    (∃ f : E ≃ᵃⁱ[ℝ] E, f a = a' ∧ f b = b' ∧ f c = c') ↔
      dist a b = dist a' b' ∧ dist b c = dist b' c' ∧ dist c a = dist c' a' := by
  constructor
  · rintro ⟨f, rfl, rfl, rfl⟩
    exact ⟨(f.isometry.dist_eq a b).symm, (f.isometry.dist_eq b c).symm,
      (f.isometry.dist_eq c a).symm⟩
  · rintro ⟨hab, hbc, hca⟩
    have hba : dist b a = dist b' a' := by rw [dist_comm b a, dist_comm b' a']; exact hab
    have hcb : dist c b = dist c' b' := by rw [dist_comm c b, dist_comm c' b']; exact hbc
    have hac : dist a c = dist a' c' := by rw [dist_comm a c, dist_comm a' c']; exact hca
    have hdist : ∀ i j : Fin 3, dist (![a, b, c] i) (![a, b, c] j)
        = dist (![a', b', c'] i) (![a', b', c'] j) := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp only [dist_self] <;> assumption
    obtain ⟨f, hf⟩ := exists_affineIsometryEquiv_of_dist_eq hdist
    exact ⟨f, hf 0, hf 1, hf 2⟩

end LeeLib.Ch01

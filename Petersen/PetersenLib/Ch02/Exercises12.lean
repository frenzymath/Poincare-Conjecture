import PetersenLib.Ch01.IsometryGroups

/-!
# Petersen Ch. 2, §2.5 — Exercise 2.5.12 (isometries of Euclidean space)

Exercise 2.5.12 has two parts: (1) for an isometry `F`, the connection is natural,
`F_*(∇_Y X) = ∇_{F_*Y} F_*X`; (2) *deduce* that the isometries of `(ℝⁿ, g_eu)` are
exactly the affine-orthogonal maps `F(x) = O x + b` with `O ∈ O(n)`.

We formalize **part 2** — the concrete characterization — as `exercise2_5_12`,
obtained directly from the Chapter-1 result `isometryGroup_euclideanSpace`
(proved via arc length + the Mazur–Ulam theorem). **Part 1** (naturality of the
covariant derivative under an isometry, `Φ_*(∇_YX) = ∇_{Φ_*Y}(Φ_*X)`) is
`exercise2_5_12_naturality` in `PetersenLib.Ch02.ConnectionNaturality`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5.
-/

noncomputable section

open scoped Manifold

namespace PetersenLib

/-- **Math.** **Exercise 2.5.12 (part 2).** The isometries of Euclidean space
`(ℝⁿ, g_eu)` are exactly the affine-orthogonal maps `F(x) = v + O(x)` with
`O` a linear isometry (an element of `O(n)`) and `v` a translation. (Part 1,
naturality of the connection under an isometry, is `exercise2_5_12_naturality`
in `PetersenLib.Ch02.ConnectionNaturality`.) -/
theorem exercise2_5_12 {n : ℕ} (F : Equiv.Perm (EuclideanSpace ℝ (Fin n))) :
    F ∈ IsometryGroup (euclideanMetric n) ↔
      ∃ (v : EuclideanSpace ℝ (Fin n))
        (O : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n)),
        ∀ x, F x = v + O x :=
  isometryGroup_euclideanSpace F

end PetersenLib

end

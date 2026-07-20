/-
Chapter 2, "Riemannian Metrics", §"Riemannian Submersions": **Exercise 2.26**,
*a horizontal vector field that is not the horizontal lift of any vector field on
the base*.

Lee, Proposition 2.25(b) says that a smooth vector field on the base of a
Riemannian submersion has a unique horizontal lift; Exercise 2.26 asks for a
horizontal vector field on the total space that is *not* the lift of anything.
The obstruction is that a lift is `π`-related to a field on the base — its image
`dπ_x W_x` depends on `x` only through `π x` — while a general horizontal field
need not be.

The concrete model is Example 2.27(a) in the smallest interesting case:

* base `= ` fibre `= ℝ`, total space `ℝ × ℝ`;
* the metric `ḡ ⊕ ḡ` (`prodMetric` of two `euclideanMetric ℝ`);
* the submersion `π = ` first projection `ContMDiffMap.fst : ℝ × ℝ → ℝ`.

The witness is `W̃(x,y) = (y, 0) ∈ T_{(x,y)}(ℝ × ℝ) = ℝ × ℝ`.

* **Horizontal** (`horizontalNonLiftField_mem_horizontalSpace`): its vertical
  (second) component is `0`, and for the product metric the horizontal space of
  `π_M` is exactly the `M`-factor `{v | v.2 = 0}`
  (`mem_horizontalSpace_prodMetric_fst_iff`).
* **Not a lift** (`not_isHorizontalLift_horizontalNonLiftField`): if
  `W̃ = ` horizontal lift of `X`, then applying `dπ` gives
  `dπ_{(x,y)} W̃_{(x,y)} = X(π(x,y)) = X(x)`.  But `dπ_{(x,y)} = fst`
  (`mfderiv_contMDiffMap_fst`), so the left side is the first component `y`,
  forcing `X(x) = y` for *every* `y`.  Evaluating at `(0,0)` and `(0,1)` gives
  `X(0) = 0` and `X(0) = 1`, a contradiction.

Only pointwise facts are used; the whole file is `RiemannianSubmersionExamples`
(for the horizontal-space computation of the product projection) together with
the pointwise horizontal-lift API of `RiemannianSubmersion`.
-/
import LeeLib.Ch02.RiemannianSubmersionExamples

namespace LeeLib.Ch02

open Manifold
open scoped Manifold ContDiff

noncomputable section

-- The first projection `ℝ × ℝ → ℝ`, as a smooth map (a submersion by
-- `isSubmersion_contMDiffMap_fst`).
set_option quotPrecheck false in
local notation "π₁" =>
  (ContMDiffMap.fst : C^∞⟮𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ), ℝ × ℝ; 𝓘(ℝ, ℝ), ℝ⟯)

-- The product Euclidean metric `ḡ ⊕ ḡ` on `ℝ × ℝ` (Lee, Example 2.27(a) with
-- `n = k = 1`).
set_option quotPrecheck false in
local notation "gΠ" => prodMetric (euclideanMetric ℝ) (euclideanMetric ℝ)

/-- **Math.** The vector field `W̃(x,y) = (y, 0)` on `ℝ × ℝ`, viewed through the
canonical identification `T_{(x,y)}(ℝ × ℝ) = ℝ × ℝ`.  This is the witness for
Lee's Exercise 2.26: it is horizontal but is not the horizontal lift of any
vector field on the base. -/
def horizontalNonLiftField : ∀ p : ℝ × ℝ, TangentSpace (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) p :=
  fun p => (p.2, 0)

@[simp] theorem horizontalNonLiftField_apply (p : ℝ × ℝ) :
    horizontalNonLiftField p = (p.2, 0) := rfl

/-- **Math.** `W̃` is horizontal.  Its vertical (second) component is `0`, and for
the product metric the horizontal space of the first projection is exactly the
`M`-factor `{v | v.2 = 0}` (`mem_horizontalSpace_prodMetric_fst_iff`). -/
theorem horizontalNonLiftField_mem_horizontalSpace (p : ℝ × ℝ) :
    horizontalNonLiftField p ∈ horizontalSpace gΠ π₁ p := by
  rw [mem_horizontalSpace_prodMetric_fst_iff (euclideanMetric ℝ) (euclideanMetric ℝ)]
  rfl

/-- **Lee, Exercise 2.26.**  `W̃` is *not* the horizontal lift of any vector field
`X` on the base `ℝ`.

If it were, then `dπ_{(x,y)} W̃_{(x,y)} = X(π(x,y)) = X(x)` by
`mfderiv_horizontalLiftAt`; but `dπ_{(x,y)} = fst` (`mfderiv_contMDiffMap_fst`),
so the left side is the first component `y`.  Hence `X(x) = y` for every `y`,
which at `(0,0)` and `(0,1)` gives `X(0) = 0` and `X(0) = 1`. -/
theorem not_isHorizontalLift_horizontalNonLiftField :
    ¬ ∃ X : ∀ y : ℝ, TangentSpace 𝓘(ℝ, ℝ) y,
      ∀ p : ℝ × ℝ, horizontalNonLiftField p = horizontalLiftAt gΠ π₁ p (X (π₁ p)) := by
  rintro ⟨X, hX⟩
  -- `dπ` of the lift is `X ∘ π`, while `dπ` of `W̃` is the first component: so `y = X x`.
  have key : ∀ x y : ℝ, y = X x := by
    intro x y
    have hmf := mfderiv_horizontalLiftAt gΠ π₁ isSubmersion_contMDiffMap_fst (x, y)
      (X (π₁ (x, y)))
    have hlhs : mfderiv (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) π₁ (x, y)
        (horizontalNonLiftField (x, y)) = y := by
      rw [mfderiv_contMDiffMap_fst]; rfl
    rw [hX (x, y)] at hlhs
    exact hlhs.symm.trans hmf
  -- Evaluate at `(0,0)` and `(0,1)`: `0 = X 0` and `1 = X 0`.
  exact absurd ((key 0 0).trans (key 0 1).symm) (by norm_num)

end

end LeeLib.Ch02

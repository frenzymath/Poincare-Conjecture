import DoCarmoLib.Riemannian.Manifold.DoCarmoCh4Ricci

/-!
# Ricci as a sum of sectional curvatures

do Carmo, *Riemannian Geometry*, Ch. 4, §4 — the identity that turns a **sectional**
curvature bound into a **Ricci** curvature bound:
$$Q(v,v) = \sum_{i \ne i_0} K(v, e_i), \qquad v = e_{i_0},$$
for an orthonormal basis $\{e_i\}$ of $V$.

This is the step do Carmo takes without comment when he deduces `cor:dc-ch9-3-3`
(*`K ≥ 1/r² > 0` gives the Bonnet–Myers conclusions*) from `thm:dc-ch9-3-1` (*Bonnet–Myers
under `Ric ≥ 1/r²`*): a sectional curvature bound bounds Ricci below, because Ricci **is**
a sum of `n-1` sectional curvatures.

## Why this file exists

`ricciForm` (`DoCarmoCh4Ricci.lean`) and `sectionalCurvature` (`DoCarmoCh4Sectional.lean`)
were both proved and had never been related: before this file the two identifiers did not
co-occur in a single statement anywhere in DoCarmoLib, and `ricciForm` had **no consumers
at all**.

The mathematics is one line, because the two sides' numerators are already syntactically
the same: `ricciForm_eq_sum` gives `Q(v,v) = ∑_i B v e_i v e_i`, and
`sectionalCurvature B v (e i) = B v (e i) v (e i) / wedgeSq v (e i)`, where for
orthonormal `v ⊥ e i` the denominator `wedgeSq v (e i) = ⟨v,v⟩⟨e i,e i⟩ - ⟨v,e i⟩²` is
`1·1 - 0 = 1`. The diagonal term `i = i₀` contributes `B v v v v = 0`
(`IsAlgCurvatureForm.self_left`), which is what makes the sum run over `n-1` terms rather
than `n`.

## Contents

* `sectionalCurvature_eq_of_orthonormal` — `K(x,y) = B x y x y` for orthonormal `x, y`:
  the bridge lemma, and the reusable one (it removes `sectionalCurvature`'s division).
* `ricciForm_self_eq_sum_sectionalCurvature` — `Q(v,v) = ∑_{i ≠ i₀} K(v, e_i)`.
* `card_nsmul_le_ricciForm_self` / `ricciForm_self_ge_of_sectionalCurvature_ge` — the
  consequence Bonnet–Myers uses: if every sectional curvature `K(v, e_i) ≥ k` then
  `Q(v,v) ≥ (n-1)·k`.

## A note on normalization

**DoCarmoLib's convention is unnormalized throughout**: `ricciForm` is the raw trace
`∑_i B x e_i y e_i`, with no `1/(n-1)`. do Carmo's `Ric_p(v)` in `thm:dc-ch9-3-1` is the
**normalized** quantity `Q(v,v)/(n-1)`; that division is not performed anywhere in the
library, and no `Ric_p` at a tangent space exists. So a statement of Bonnet–Myers must
either divide explicitly or hypothesise the bound in the unnormalized form `Q(v,v) ≥
(n-1)/r²`. The results below are stated on `Q` (unnormalized) and are exactly the shape
that makes the conversion a single division; `ricciForm_self_ge_of_sectionalCurvature_ge`
already produces the `(n-1)·k` right-hand side that normalizing would divide away.

Reference: do Carmo, *Riemannian Geometry*, Ch. 4, §4 (the Ricci form `Q`) and Ch. 4, §3
(sectional curvature `K`); consumed by Ch. 9, `cor:dc-ch9-3-3`.
-/

open Set Finset

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-! ### The bridge: orthonormal pairs have unit wedge -/

/-- **Math.** For an **orthonormal pair** `x, y`, the sectional curvature is the bare
numerator: `K(x,y) = B x y x y`.  The denominator `wedgeSq x y = ⟨x,x⟩⟨y,y⟩ - ⟨x,y⟩²`
is `1·1 - 0² = 1`.

This is the lemma that removes `sectionalCurvature`'s division, and it is why relating
`K` to the Ricci form `Q` — whose orthonormal-basis formula `ricciForm_eq_sum` is a sum of
exactly such numerators — costs nothing. -/
theorem sectionalCurvature_eq_of_orthonormal (B : V → V → V → V → ℝ) {x y : V}
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : (inner ℝ x y : ℝ) = 0) :
    sectionalCurvature B x y = B x y x y := by
  have hw : wedgeSq x y = 1 := by
    unfold wedgeSq
    rw [hxy, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hx, hy]
    norm_num
  rw [sectionalCurvature, hw, div_one]

/-! ### Ricci is a sum of `n-1` sectional curvatures -/

/-- **Math.** do Carmo Ch. 4, §4: for an orthonormal basis `{e_i}` and `v = e_{i₀}`,
$$Q(v,v) = \sum_{i \ne i_0} K(v, e_i).$$

The diagonal term drops because `B v v v v = 0` (`IsAlgCurvatureForm.self_left`), so the
sum runs over the `n-1` basis vectors orthogonal to `v` — each pair `(v, e_i)`, `i ≠ i₀`,
being orthonormal, contributes exactly `K(v, e_i)` by
`sectionalCurvature_eq_of_orthonormal`.

This is do Carmo's unstated step in `cor:dc-ch9-3-3`: it is what makes a *sectional*
bound imply a *Ricci* bound. -/
theorem ricciForm_self_eq_sum_sectionalCurvature {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (i₀ : ι) :
    ricciForm hB (e i₀) (e i₀)
      = ∑ i ∈ Finset.univ.erase i₀, sectionalCurvature B (e i₀) (e i) := by
  rw [ricciForm_eq_sum hB _ _ e]
  -- split off the diagonal term, which vanishes
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i₀), hB.self_left, add_zero]
  -- on the remaining terms, each pair `(e i₀, e i)` is orthonormal
  refine Finset.sum_congr rfl fun i hi => ?_
  have hne : i₀ ≠ i := (Finset.ne_of_mem_erase hi).symm
  rw [sectionalCurvature_eq_of_orthonormal B (e.orthonormal.1 i₀) (e.orthonormal.1 i)
    (e.orthonormal.2 hne)]

/-! ### The Bonnet–Myers input: a sectional bound bounds Ricci below -/

/-- **Math.** If every sectional curvature `K(v, e_i)`, `i ≠ i₀`, is at least `k`, then
`Q(v,v) ≥ (n-1)·k`, where `n - 1` is the number of basis vectors orthogonal to
`v = e_{i₀}`.

This is the inequality `cor:dc-ch9-3-3` runs on: it converts do Carmo's hypothesis
`K ≥ 1/r²` into the Ricci hypothesis `thm:dc-ch9-3-1` demands.  Stated with the cardinal
as an `nsmul` on the `erase` set to avoid truncated subtraction on `ℕ`;
`ricciForm_self_ge_of_sectionalCurvature_ge` is the `(n-1)·k` form. -/
theorem card_nsmul_le_ricciForm_self {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (i₀ : ι) {k : ℝ}
    (hK : ∀ i ∈ Finset.univ.erase i₀, k ≤ sectionalCurvature B (e i₀) (e i)) :
    (Finset.univ.erase i₀).card • k ≤ ricciForm hB (e i₀) (e i₀) := by
  rw [ricciForm_self_eq_sum_sectionalCurvature hB e i₀]
  exact Finset.card_nsmul_le_sum _ _ _ hK

/-- **Math.** do Carmo Ch. 9, the step from `cor:dc-ch9-3-3`'s hypothesis to
`thm:dc-ch9-3-1`'s: a sectional curvature bound `K ≥ k` at `v` gives the **Ricci** bound
$$Q(v,v) \ge (n-1)\,k,$$
`n = \dim V`.

Note the right-hand side carries the factor `n-1` that do Carmo's *normalized* `Ric_p(v) =
Q(v,v)/(n-1)` divides away: in do Carmo's normalization this reads `Ric_p(v) ≥ k`, which
is literally his hypothesis in `thm:dc-ch9-3-1`.  DoCarmoLib's `ricciForm` is the
unnormalized `Q`, so the factor is explicit here. -/
theorem ricciForm_self_ge_of_sectionalCurvature_ge {B : V → V → V → V → ℝ}
    (hB : IsAlgCurvatureForm B) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : OrthonormalBasis ι ℝ V) (i₀ : ι) {k : ℝ}
    (hK : ∀ i ∈ Finset.univ.erase i₀, k ≤ sectionalCurvature B (e i₀) (e i)) :
    ((Fintype.card ι : ℝ) - 1) * k ≤ ricciForm hB (e i₀) (e i₀) := by
  have h := card_nsmul_le_ricciForm_self hB e i₀ hK
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  rwa [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ, nsmul_eq_mul,
    Nat.cast_sub hpos, Nat.cast_one] at h

end Riemannian

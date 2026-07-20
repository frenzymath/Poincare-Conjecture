import PetersenLib.Ch06.ConvexFunctions
import PetersenLib.Ch05.HopfRinowSegment

/-!
# Petersen Ch. 6, §6.2 — maxima of convex functions and unique minima

Petersen §6.2 (p. 259), `rem:pet-ch6-max-of-convex-functions`, in two halves:

* **the maximum of finitely many convex functions is convex** — `max_isConvex`.  Petersen's
  one-line justification ("this reduces to the one-dimensional statement by restricting to
  geodesics") is literally the proof: restrict the whole family to a common test geodesic and
  run a `Finset` induction over mathlib's *binary* `ConvexOn.sup`.  `Ch06/ConvexFunctions.lean`
  already records the binary case (`IsConvexOn.max`); mathlib has no `sup'`/`iSup` version of
  `ConvexOn.sup`, so the finite case needs the induction done here.

* **a proper, nonnegative, strictly convex function on a complete manifold has a unique
  minimum** — `strictlyConvex_uniqueMinimum`.  Existence is properness plus boundedness below;
  uniqueness is `strictlyConvexOn_univ_unique_min` (`Ch06/ConvexFunctions.lean`) fed the
  joining geodesic that Hopf–Rinow supplies.

Both are consumed by `def:pet-ch6-linfty-center-of-mass`, which needs the max over a finite
orbit `p₁, …, p_k` to be strictly convex with a unique minimum.

## The `Finset.sup'` encoding of "max of finitely many"

`max_isConvex` is stated with `Finset.sup'` over a *nonempty* `Finset ι`.  Nonemptiness is
forced, not incidental: a maximum over an empty family has no value in `ℝ` (there is no `⊥`),
and `Finset.sup'` is precisely mathlib's max-over-a-nonempty-Finset.  The `k`-point family of
`def:pet-ch6-linfty-center-of-mass` is nonempty, so this costs its consumer nothing.

## Two hypotheses Petersen leaves implicit, and why they are here

**Continuity.**  Petersen says "properness and boundedness below give a minimum".  That needs
`f` continuous — properness alone does not (an arbitrary function with compact sublevel sets
need not attain its infimum).  Petersen's `f` is a max of the smooth `f_{0,pᵢ} = ½r_{pᵢ}²`, so
continuity is free at the point of use; it is a hypothesis here rather than a derivation
because convex ⟹ locally Lipschitz ⟹ continuous is a real theorem that this project has not
formalized, and assuming it would be circular.

**Properness as compact sublevel sets.**  `hproper : ∀ c, IsCompact {x | f x ≤ c}` is the form
the existence argument actually consumes.  For a nonnegative `f` it is equivalent to `f` being
a proper *map* (preimages of compacts are compact), since a compact `K ⊆ ℝ` sits in some
`Iic c` and `f ⁻¹' K` is then a closed subset of the compact `{f ≤ c}`.

Note that `strictlyConvex_uniqueMinimum` does **not** need nonnegativity as such — only that
some sublevel set is nonempty, which any `f` with a value has.  It is kept in the statement to
stay 1-to-1 with Petersen's wording; it is genuinely unused, and the proof says so.
-/

open Set
open scoped Manifold Topology ContDiff

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-! ### The maximum of finitely many convex functions -/

/-- **Math.** Petersen §6.2 (p. 259), the first half of `rem:pet-ch6-max-of-convex-functions`:
**the maximum of finitely many convex functions is convex.**

The family is indexed by a nonempty `Finset ι` and the maximum is `Finset.sup'`; see the module
docstring for why nonemptiness is forced rather than incidental.

**Proof.**  Petersen: "this reduces to the one-dimensional statement by restricting to
geodesics".  Exactly that — `IsConvexOn` is a `∀` over test geodesics, so it suffices to fix
one and induct over the `Finset` with mathlib's binary `ConvexOn.sup` (`Finset.sup'_cons`
splits off one member at each step). -/
theorem max_isConvex {g : RiemannianMetric I M} {U : Set M} {ι : Type*}
    {s : Finset ι} (hs : s.Nonempty) {f : ι → M → ℝ}
    (h : ∀ i ∈ s, IsConvexOn (I := I) g U (f i)) :
    IsConvexOn (I := I) g U (fun x => s.sup' hs fun i => f i x) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa using h i (by simp)
  | cons i t hi ht ih =>
      have hi' : IsConvexOn (I := I) g U (f i) := h i (Finset.mem_cons_self i t)
      have ht' : IsConvexOn (I := I) g U (fun x => t.sup' ht fun j => f j x) :=
        ih fun j hj => h j (Finset.mem_cons_of_mem hj)
      have hmax := hi'.max ht'
      intro γ J hJ hγ hm
      have := hmax γ J hJ hγ hm
      -- `Finset.sup'_cons` splits off `i`; the rewrite is under the `fun t_1 =>` binder,
      -- which is why this is a `convert` rather than a `simpa`.
      convert this using 2 with t_1
      exact Finset.sup'_cons ht _

/-! ### Existence and uniqueness of the minimum -/

/-- **Math.** Petersen §6.2 (p. 259), the second half of `rem:pet-ch6-max-of-convex-functions`:
**any proper, nonnegative, strictly convex function `f` on a complete manifold has a unique
minimum.**

**Proof.**  *Existence*: the sublevel set `{f ≤ f x₀}` at any base point `x₀` is nonempty and,
by properness, compact; a continuous function attains its minimum on it
(`IsCompact.exists_isMinOn`), and a minimum there is a global minimum since points outside the
sublevel set already have `f > f x₀ ≥ f p`.  *Uniqueness*: Petersen's argument — "if there were
two minima, strict convexity restricted to a geodesic joining them would force smaller values
on the interior of the segment than at either endpoint" — is `strictlyConvexOn_univ_unique_min`
(`Ch06/ConvexFunctions.lean`); the geodesic joining the two minima is produced by Hopf–Rinow
(`Exponential.exists_minimizing_geodesic_unitInterval`, the clause that also returns
`IsGeodesic`, fed by `Geodesic.exists_global_geodesic` on the complete `M`).

Nonnegativity (`hnonneg`) is stated for fidelity to Petersen and is not used; see the module
docstring. -/
theorem strictlyConvex_uniqueMinimum (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    [CompleteSpace M] [ConnectedSpace M] {f : M → ℝ}
    (hcont : Continuous f) (_hnonneg : ∀ x, 0 ≤ f x)
    (hproper : ∀ c : ℝ, IsCompact {x : M | f x ≤ c})
    (hconv : IsStrictlyConvexOn (I := I) g Set.univ f) :
    ∃! p : M, IsMinOn f Set.univ p := by
  classical
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  haveI hRM : IsRiemannianManifold I M := hg
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  -- EXISTENCE: minimize over the compact sublevel set at `x₀`
  set S : Set M := {x : M | f x ≤ f x₀} with hS_def
  have hSne : S.Nonempty := ⟨x₀, by simp [hS_def]⟩
  obtain ⟨p, hpS, hpmin⟩ := (hproper (f x₀)).exists_isMinOn hSne hcont.continuousOn
  have hpx₀ : f p ≤ f x₀ := hpS
  have hp : IsMinOn f Set.univ p := by
    rw [isMinOn_iff]
    intro x _
    by_cases hx : x ∈ S
    · exact isMinOn_iff.mp hpmin x hx
    · -- outside the sublevel set `f p ≤ f x₀ < f x`
      have hx' : f x₀ < f x := lt_of_not_ge (by simpa [hS_def] using hx)
      exact hpx₀.trans hx'.le
  -- UNIQUENESS: two minima are joined by a geodesic, and strict convexity collapses it
  refine ⟨p, hp, fun q hq => ?_⟩
  have hgeo : ∀ v : TangentSpace I q, ∃ γ : ℝ → M, γ 0 = q ∧
      HasDerivAt (fun s => extChartAt I q (γ s)) (v : E) 0 ∧ Continuous γ ∧
        IsGeodesic (I := I) g γ := by
    intro v
    obtain ⟨γ, h0, hv, hc, hg'⟩ := Geodesic.exists_global_geodesic (I := I) g hg q v
    exact ⟨γ, h0, hv, hc, hg'⟩
  obtain ⟨γ, hγ0, hγ1, hγc, hγgeo, -⟩ :=
    Exponential.exists_minimizing_geodesic_unitInterval (I := I) g hg q hgeo p
  exact (strictlyConvexOn_univ_unique_min (I := I) hconv hq hp γ
    (Geodesic.IsGeodesic.isGeodesicOn hγgeo (Icc 0 1)) hγ0 hγ1)

end PetersenLib

end

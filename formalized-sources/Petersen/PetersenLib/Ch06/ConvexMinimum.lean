import PetersenLib.Ch06.ConvexFunctions
import PetersenLib.Ch05.HopfRinowSegment
import PetersenLib.Ch05.FixedPointTotallyGeodesic

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

/-! ### The `L∞` center of mass -/

/-- **Math.** Petersen §6.2 (pp. 259–260), `def:pet-ch6-linfty-center-of-mass`: the
objective whose minimum is the `L∞` center of a nonempty finite set `s`. It is the maximum
of the modified distance functions `f₀,p(x) = ½r(p,x)²` over `p ∈ s`.

Minimizing this function is equivalent to minimizing the radius of a closed ball containing
`s`, since `r ↦ ½r²` is strictly increasing on nonnegative radii. -/
def linftyCenterObjective (g : RiemannianMetric I M) (s : Finset M) (hs : s.Nonempty)
    (x : M) : ℝ :=
  s.sup' hs fun p => (riemannianDistance (I := I) g p x) ^ 2 / 2

open Classical in
/-- **Math.** Petersen §6.2 (pp. 259–260), `def:pet-ch6-linfty-center-of-mass`: the
`L∞` center of mass of a nonempty finite set, chosen as a minimizer of
`linftyCenterObjective`.

On the complete simply connected nonpositively curved manifolds of Petersen's statement, the
objective is proper and strictly convex, so `strictlyConvex_uniqueMinimum` supplies a unique
minimizer. The definition is total: before those geometric hypotheses are supplied, it falls
back to an element of `s`. The specification theorem below shows that whenever the unique
minimum exists, this choice is exactly that minimum. -/
noncomputable def centerOfMassLinfty (g : RiemannianMetric I M) (s : Finset M)
    (hs : s.Nonempty) : M :=
  if h : ∃ p : M, IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ p then
    h.choose
  else
    hs.choose

/-- **Math.** The `L∞` center selector realizes the unique minimum whenever it exists. This
is the interface used after properness and strict convexity have supplied the geometric
existence-and-uniqueness result. -/
theorem centerOfMassLinfty_isMin (g : RiemannianMetric I M) (s : Finset M)
    (hs : s.Nonempty)
    (hmin : ∃! p : M, IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ p) :
    IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ
      (centerOfMassLinfty (I := I) g s hs) := by
  rw [centerOfMassLinfty, dif_pos hmin.exists]
  exact hmin.exists.choose_spec

/-- **Math.** Any point satisfying the unique-minimum characterization is the selected
`L∞` center. -/
theorem centerOfMassLinfty_eq_of_isMin (g : RiemannianMetric I M) (s : Finset M)
    (hs : s.Nonempty)
    (hmin : ∃! p : M, IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ p)
    {p : M} (hp : IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ p) :
    centerOfMassLinfty (I := I) g s hs = p :=
  hmin.unique (centerOfMassLinfty_isMin (I := I) g s hs hmin) hp

/-! ### Cartan's finite-orbit argument -/

/- The curvature-to-properness/strict-convexity argument that supplies `hmin` is kept
   explicit here.  This makes the fixed-point theorem useful as soon as that analytic
   bridge is available, without turning the gap into an implicit or vacuous premise. -/

open Classical in
/-- **Math.** Petersen §6.2 (p. 260), `thm:pet-ch6-cartan-fixed-point`: the finite-orbit
argument behind Cartan's center-of-mass theorem.  The orbit is supplied as a nonempty
`Finset` `s`; `horbit` identifies it with the orbit of `p` under a finite-order isometry.
The hypothesis `hmin` is the unique-minimum conclusion for the orbit objective.  On a
complete simply connected nonpositively curved manifold it is supplied by the preceding
convexity and properness argument; keeping it explicit records that remaining geometric
bridge honestly. -/
theorem cartan_finiteOrderIsometry_fixedPoint [ConnectedSpace M]
    (g : RiemannianMetric I M) (F : M → M)
    (hF : IsRiemannianIsometry g g F)
    (n : ℕ) (hn : 0 < n) (horder : F^[n] = id) (p : M)
    (s : Finset M) (hs : s.Nonempty)
    (horbit : s = (Finset.range n).image (fun i => (F^[i]) p))
    (hmin : ∃! z : M,
      IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ z) :
    ∃ x : M, F x = x := by
  classical
  have hinj : Function.Injective F := by
    obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hF
    intro x y hxy
    have hxy' : Φ x = Φ y := by
      simpa only [hΦ] using hxy
    exact Φ.toEquiv.injective hxy'
  have hsurj : Function.Surjective F := by
    obtain ⟨⟨Φ, hΦ⟩, hpres⟩ := hF
    intro y
    obtain ⟨x, hx⟩ := Φ.toEquiv.surjective y
    refine ⟨x, ?_⟩
    have hx' : Φ x = y := hx
    simpa only [hΦ] using hx'
  have hdist : ∀ p q : M,
      riemannianDistance (I := I) g (F p) (F q) =
        riemannianDistance (I := I) g p q := by
    have hFloc : IsLocalRiemannianIsometry g g F :=
      hF.isLocalRiemannianIsometry
    obtain ⟨G, hGloc, hGF⟩ :=
      hF.exists_leftInverse_isLocalRiemannianIsometry
    exact fun p q => localIsometry_distancePreserving hFloc hGloc hGF p q
  have hsubset : s.image F ⊆ s := by
    rw [horbit]
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨i, hi, rfl⟩
    have hi_lt : i < n := Finset.mem_range.mp hi
    by_cases hnext : i + 1 < n
    · refine Finset.mem_image.mpr ⟨i + 1, Finset.mem_range.mpr hnext, ?_⟩
      rw [Function.iterate_succ_apply']
    · have hieq : i + 1 = n := by omega
      refine Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hn, ?_⟩
      have hperp : (F^[n]) p = p := by
        rw [horder]
        rfl
      rw [show F ((F^[i]) p) = (F^[i + 1]) p by
        rw [Function.iterate_succ_apply']]
      rw [hieq, hperp]
      simp
  have hcard : (s.image F).card = s.card :=
    Finset.card_image_of_injective s hinj
  have himage : s.image F = s :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [hcard])
  have hobj : ∀ x : M,
      linftyCenterObjective (I := I) g s hs (F x) =
        linftyCenterObjective (I := I) g s hs x := by
    intro x
    unfold linftyCenterObjective
    have hsup := Finset.sup'_comp_eq_image (f := F) hs
      (fun q : M => (riemannianDistance (I := I) g q (F x)) ^ 2 / 2)
    have hrew : (s.image F).sup' (hs.image F)
        (fun q : M => (riemannianDistance (I := I) g q (F x)) ^ 2 / 2) =
        s.sup' hs (fun q : M =>
          (riemannianDistance (I := I) g q (F x)) ^ 2 / 2) := by
      simpa [himage]
    rw [← hrew, ← hsup]
    simp_rw [Function.comp_apply, hdist]
  let c : M := centerOfMassLinfty (I := I) g s hs
  have hcmin : IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ c := by
    exact centerOfMassLinfty_isMin (I := I) g s hs hmin
  have hFcmin : IsMinOn (linftyCenterObjective (I := I) g s hs) Set.univ (F c) := by
    rw [isMinOn_iff]
    intro y hy
    obtain ⟨z, hz⟩ := hsurj y
    rw [← hz, hobj c, hobj z]
    exact isMinOn_iff.mp hcmin z (mem_univ _)
  refine ⟨c, ?_⟩
  exact (hmin.unique hcmin hFcmin).symm

end PetersenLib

end

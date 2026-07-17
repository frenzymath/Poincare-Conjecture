import PoincareLib.Ch02.Ends
import PoincareLib.Ch02.GeodesicLimits
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Poincaré Ch. 2, §2.1/2.4 — Minimizing lines from two ends

The second half of Morgan–Tian's lemma "non-compact manifolds have ends" (blueprint
`lem:ends-exist`), in its metric form: a proper metric space with minimizing segments and
two distinct ends contains a unit-speed minimizing geodesic line, i.e. a map `γ : ℝ → M`
with `dist (γ s) (γ t) = |s - t|` for all `s, t : ℝ`.

## Main declarations

* `ConnectedComponents.mk_eq_mk_iff_connectedComponentIn_eq`: two points of a set `F` have
  the same class in `ConnectedComponents F` (the quotient of the subtype) iff their
  connected components in `F` (`connectedComponentIn`, subsets of the ambient space)
  coincide.
* `disjoint_connectedComponentIn_of_mk_ne_mk`: points of `F` in distinct classes have
  disjoint connected components in `F`.
* `IsPreconnected.exists_notMem_of_notMem_connectedComponentIn`: a map continuous on a
  preconnected set, whose value at one point escapes the component in `F` of its value at
  another point, must leave `F` somewhere.
* `SpaceOfEnds.exists_apply_ne`: distinct ends select distinct components of `X \ K` for
  some compact `K`.
* `SpaceOfEnds.exists_mem_connectedComponentIn_forall_le_dist`: **ends reach infinity** —
  in a proper metric space, the component of `M \ K` selected by an end contains points
  arbitrarily far from `K`.
* `exists_isMinGeodesicOn_univ_of_ends_ne`: the main result (blueprint `lem:ends-exist`,
  second half) — a proper metric space with minimizing segments and two distinct ends
  contains a unit-speed minimizing geodesic line.

## Design notes

* Two views of `π₀(M \ K)` coexist: the space of ends packages components as classes in the
  quotient `ConnectedComponents ((K : Set X)ᶜ)` of the subtype, while the geometric
  arguments (disjointness, crossing, unboundedness) are naturally about the subsets
  `connectedComponentIn ((K : Set X)ᶜ) x` of the ambient space. The bridge is
  `ConnectedComponents.mk_eq_mk_iff_connectedComponentIn_eq`, obtained from mathlib's
  `connectedComponentIn_eq_image` and the injectivity of `Subtype.val`.
* "Ends reach infinity" is Morgan–Tian's observation that each complementary component `U`
  recorded by an end contains points arbitrarily far from `K`: otherwise `U` would be
  bounded, `closure U` compact by properness, and the component the same end selects beyond
  the larger compact set `K ∪ closure U` would have to lie inside `U` yet outside
  `closure U` — a contradiction.
* The line is produced by `exists_isMinGeodesicOn_hyperfilter_limit`: minimizing segments
  `σ k` between points of the two components at distance `≥ k + 1` from `K` must cross `K`
  at some time `t₀ k` (their images are connected, and the two components are disjoint);
  recentering each segment at its crossing time yields minimizing geodesics on windows
  containing `[-(k+1), k+1]`, anchored in the compact set `K`, and the ultrafilter limit is
  a minimizing geodesic on all of `ℝ`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.1.
-/

open Filter Topology Metric Set
open TopologicalSpace (Compacts)

namespace PoincareLib

/-! ## Bridging the quotient and subset views of `π₀` -/

section Bridge

variable {X : Type*} [TopologicalSpace X]

/-- Two points of `F` represent the same class in `ConnectedComponents F` (the quotient of
the subtype) iff their connected components **in** `F` (`connectedComponentIn`, as subsets
of the ambient space) coincide. -/
theorem ConnectedComponents.mk_eq_mk_iff_connectedComponentIn_eq {F : Set X} (x y : F) :
    ConnectedComponents.mk x = ConnectedComponents.mk y ↔
      connectedComponentIn F ↑x = connectedComponentIn F ↑y := by
  rw [ConnectedComponents.coe_eq_coe, connectedComponentIn_eq_image x.2,
    connectedComponentIn_eq_image y.2, Subtype.coe_eta, Subtype.coe_eta,
    Set.image_eq_image Subtype.val_injective]

/-- Points of `F` representing distinct classes of `ConnectedComponents F` have disjoint
connected components in `F`. -/
theorem disjoint_connectedComponentIn_of_mk_ne_mk {F : Set X} {x y : F}
    (hne : ConnectedComponents.mk x ≠ ConnectedComponents.mk y) :
    Disjoint (connectedComponentIn F ↑x) (connectedComponentIn F ↑y) :=
  Set.disjoint_left.2 fun _z hzx hzy =>
    hne ((ConnectedComponents.mk_eq_mk_iff_connectedComponentIn_eq x y).mpr
      ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm))

/-- A map continuous on a preconnected set `s`, whose value at some point `b ∈ s` lies
outside the connected component in `F` of its value at `a ∈ s`, must leave `F` somewhere on
`s`. (Applied below: a minimizing segment between two distinct components of `M \ K` must
cross `K`.) -/
theorem IsPreconnected.exists_notMem_of_notMem_connectedComponentIn {α : Type*}
    [TopologicalSpace α] {s : Set α} (hs : IsPreconnected s) {f : α → X}
    (hf : ContinuousOn f s) {a b : α} (ha : a ∈ s) (hb : b ∈ s) {F : Set X}
    (hfb : f b ∉ connectedComponentIn F (f a)) :
    ∃ t ∈ s, f t ∉ F := by
  by_contra h
  push Not at h
  have himg : f '' s ⊆ connectedComponentIn F (f a) :=
    (hs.image f hf).subset_connectedComponentIn (Set.mem_image_of_mem f ha)
      (Set.image_subset_iff.mpr h)
  exact hfb (himg (Set.mem_image_of_mem f hb))

/-- Distinct ends are distinguished by some compact set: they select distinct components of
its complement. -/
theorem SpaceOfEnds.exists_apply_ne {e₁ e₂ : SpaceOfEnds X} (hne : e₁ ≠ e₂) :
    ∃ K : Compacts X, e₁.1 K ≠ e₂.1 K :=
  Function.ne_iff.mp fun h => hne (Subtype.ext h)

end Bridge

/-! ## Ends reach infinity -/

section Metric

variable {M : Type*} [MetricSpace M]

/-- **Ends reach infinity** (Morgan–Tian §2.1): in a proper metric space, the component of
`M \ K` selected by an end contains points arbitrarily far from `K`. Otherwise that
component `U` would be bounded, its closure compact by properness, and the component the
same end selects beyond the larger compact set `K ∪ closure U` would have to lie inside `U`
yet outside `closure U`. -/
theorem SpaceOfEnds.exists_mem_connectedComponentIn_forall_le_dist [ProperSpace M]
    (e : SpaceOfEnds M) (K : Compacts M) (x : ((K : Set M)ᶜ : Set M))
    (hx : ConnectedComponents.mk x = e.1 K) (R : ℝ) :
    ∃ z ∈ connectedComponentIn ((K : Set M)ᶜ) ↑x, ∀ w ∈ (K : Set M), R ≤ dist z w := by
  set U : Set M := connectedComponentIn ((K : Set M)ᶜ) ↑x
  by_contra h
  push Not at h
  -- every point of `U` would be within `R` of `K`, so `U` would be bounded …
  obtain ⟨r, hr⟩ := K.2.isBounded.subset_closedBall (↑x : M)
  have hUb : Bornology.IsBounded U := by
    apply (isBounded_closedBall (x := (↑x : M)) (r := r + R)).subset
    intro z hz
    obtain ⟨w, hwK, hw⟩ := h z hz
    have h1 : dist w (↑x : M) ≤ r := hr hwK
    have h2 := dist_triangle z w (↑x : M)
    rw [mem_closedBall]
    linarith
  -- … its closure compact, and `K' := K ∪ closure U` a larger compact set
  have hUc : IsCompact (closure U) := hUb.isCompact_closure
  set K' : Compacts M := ⟨(K : Set M) ∪ closure U, K.2.union hUc⟩
  have hKK' : K ≤ K' := SetLike.coe_subset_coe.mp Set.subset_union_left
  -- a representative of the end at `K'` must lie in `U` — yet outside `closure U`
  obtain ⟨y, hy⟩ := ConnectedComponents.surjective_coe (e.1 K')
  have hcompat : ConnectedComponents.mk (Set.inclusion (compl_subset_compl_of_le hKK') y) =
      ConnectedComponents.mk x := by
    rw [← endsTransition_mk hKK', hy, e.2 hKK', hx]
  have hcomp : connectedComponentIn ((K : Set M)ᶜ) ↑y = U := by
    have hbridge :=
      (ConnectedComponents.mk_eq_mk_iff_connectedComponentIn_eq _ _).mp hcompat
    rwa [Set.coe_inclusion] at hbridge
  have hyU : (↑y : M) ∈ U := by
    rw [← hcomp]
    exact mem_connectedComponentIn (compl_subset_compl_of_le hKK' y.2)
  exact y.2 (Set.mem_union_right _ (subset_closure hyU))

/-! ## The minimizing line -/

/-- A proper metric space with minimizing segments and two distinct ends contains a
unit-speed minimizing geodesic line (blueprint `lem:ends-exist`, second half). Following
Morgan–Tian: minimizing segments between points of the two ends' components at distance
`≥ k + 1` from the separating compact set `K` must cross `K`; recentered at their crossing
times, they subconverge to a minimizing geodesic defined on all of `ℝ`. -/
theorem exists_isMinGeodesicOn_univ_of_ends_ne [ProperSpace M]
    (hseg : HasMinSegments M) {e₁ e₂ : SpaceOfEnds M} (hne : e₁ ≠ e₂) :
    ∃ γ : ℝ → M, IsMinGeodesicOn γ Set.univ := by
  classical
  -- the two ends select distinct components of the complement of some compact `K`
  obtain ⟨K, hK⟩ := SpaceOfEnds.exists_apply_ne hne
  obtain ⟨x₁, hx₁⟩ := ConnectedComponents.surjective_coe (e₁.1 K)
  obtain ⟨x₂, hx₂⟩ := ConnectedComponents.surjective_coe (e₂.1 K)
  have hne' : ConnectedComponents.mk x₁ ≠ ConnectedComponents.mk x₂ := by
    rw [hx₁, hx₂]
    exact hK
  have hdisj : Disjoint (connectedComponentIn ((K : Set M)ᶜ) ↑x₁)
      (connectedComponentIn ((K : Set M)ᶜ) ↑x₂) :=
    disjoint_connectedComponentIn_of_mk_ne_mk hne'
  -- points of the two components at distance at least `k + 1` from `K`
  choose xs hxsU hxsfar using fun k : ℕ =>
    SpaceOfEnds.exists_mem_connectedComponentIn_forall_le_dist e₁ K x₁ hx₁ ((k : ℝ) + 1)
  choose ys hysU hysfar using fun k : ℕ =>
    SpaceOfEnds.exists_mem_connectedComponentIn_forall_le_dist e₂ K x₂ hx₂ ((k : ℝ) + 1)
  -- minimizing segments joining them
  choose σ hσ0 hσL hσgeo using fun k : ℕ => hseg (xs k) (ys k)
  -- each segment crosses `K`, because its image is connected and the components disjoint
  have hcross : ∀ k : ℕ, ∃ t ∈ Set.Icc (0 : ℝ) (dist (xs k) (ys k)),
      σ k t ∈ (K : Set M) := by
    intro k
    have hnotin : σ k (dist (xs k) (ys k)) ∉
        connectedComponentIn ((K : Set M)ᶜ) (σ k 0) := by
      rw [hσ0 k, hσL k, ← connectedComponentIn_eq (hxsU k)]
      exact fun hmem => Set.disjoint_left.mp hdisj hmem (hysU k)
    obtain ⟨t, htmem, htnot⟩ :=
      IsPreconnected.exists_notMem_of_notMem_connectedComponentIn isPreconnected_Icc
        (hσgeo k).continuousOn (Set.left_mem_Icc.mpr dist_nonneg)
        (Set.right_mem_Icc.mpr dist_nonneg) hnotin
    exact ⟨t, htmem, Set.notMem_compl_iff.mp htnot⟩
  choose t₀ ht₀mem ht₀K using hcross
  -- the crossing time is at distance at least `k + 1` from both ends of the window
  have hfar₁ : ∀ k : ℕ, (k : ℝ) + 1 ≤ t₀ k := by
    intro k
    have hmem := Set.mem_Icc.mp (ht₀mem k)
    have h1 : dist (σ k 0) (σ k (t₀ k)) = |0 - t₀ k| :=
      hσgeo k (Set.left_mem_Icc.mpr dist_nonneg) (ht₀mem k)
    rw [hσ0 k, zero_sub, abs_neg, abs_of_nonneg hmem.1] at h1
    calc (k : ℝ) + 1 ≤ dist (xs k) (σ k (t₀ k)) := hxsfar k _ (ht₀K k)
      _ = t₀ k := h1
  have hfar₂ : ∀ k : ℕ, (k : ℝ) + 1 ≤ dist (xs k) (ys k) - t₀ k := by
    intro k
    have hmem := Set.mem_Icc.mp (ht₀mem k)
    have h1 : dist (σ k (t₀ k)) (σ k (dist (xs k) (ys k))) = |t₀ k - dist (xs k) (ys k)| :=
      hσgeo k (ht₀mem k) (Set.right_mem_Icc.mpr dist_nonneg)
    rw [hσL k, abs_of_nonpos (sub_nonpos.mpr hmem.2), neg_sub] at h1
    calc (k : ℝ) + 1 ≤ dist (ys k) (σ k (t₀ k)) := hysfar k _ (ht₀K k)
      _ = dist (σ k (t₀ k)) (ys k) := dist_comm _ _
      _ = dist (xs k) (ys k) - t₀ k := h1
  -- recenter each segment at its crossing time
  have hτgeo : ∀ k : ℕ, IsMinGeodesicOn (fun t => σ k (t + t₀ k))
      (Set.Icc (0 - t₀ k) (dist (xs k) (ys k) - t₀ k)) := by
    intro k
    have h := (hσgeo k).comp_add_right (t₀ k)
    rwa [Set.preimage_add_const_Icc] at h
  have h0In : ∀ k : ℕ, (0 : ℝ) ∈ Set.Icc (0 - t₀ k) (dist (xs k) (ys k) - t₀ k) := by
    intro k
    have hmem := Set.mem_Icc.mp (ht₀mem k)
    exact Set.mem_Icc.mpr ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  -- the recentered windows exhaust `ℝ`
  have hexh : ∀ t ∈ (Set.univ : Set ℝ), ∀ᶠ k in atTop,
      t ∈ Set.Icc (0 - t₀ k) (dist (xs k) (ys k) - t₀ k) := by
    intro t _
    filter_upwards [eventually_ge_atTop ⌈|t|⌉₊] with k hk
    have hkt : |t| ≤ (k : ℝ) + 1 := by
      calc |t| ≤ (⌈|t|⌉₊ : ℝ) := Nat.le_ceil _
        _ ≤ (k : ℝ) := Nat.cast_le.mpr hk
        _ ≤ (k : ℝ) + 1 := by linarith
    have h1 := hfar₁ k
    have h2 := hfar₂ k
    have h3 := neg_abs_le t
    have h4 := le_abs_self t
    exact Set.mem_Icc.mpr ⟨by linarith, by linarith⟩
  -- the recentered geodesics are anchored in the compact set `K` at time `0`
  have hanchor : ∀ k : ℕ, (fun t => σ k (t + t₀ k)) 0 ∈ (K : Set M) := by
    intro k
    simpa using ht₀K k
  have hKcpt : IsCompact (K : Set M) := K.2
  obtain ⟨γ, hγ, -, -⟩ := exists_isMinGeodesicOn_hyperfilter_limit (Set.mem_univ (0 : ℝ))
    hτgeo h0In hexh hKcpt hanchor
  exact ⟨γ, hγ⟩

end Metric

end PoincareLib

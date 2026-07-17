import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Morgan–Tian Ch. 2, §2.6 — Forward difference quotients

The comparison lemma for forward difference quotients: a continuous function
`f` whose forward (upper right Dini) difference quotient satisfies
`df/dt (t) ≤ ψ(t, f(t))` on `[a, b)` is dominated on `[a, b]` by any solution
`G` of the ODE `G' = ψ(t, G)` with `f a ≤ G a`, provided `ψ` is `C¹` on the
strip `[a, b] × ℝ` (`le_of_forwardDiffQuotientLE`). Building on it, the
product case of Morgan–Tian's "forward difference maximum property": the
maximum `F_max(t) = ⨆ x, F x t` of a compact family is continuous
(`continuous_iSup_of_compact`), has forward difference quotient controlled by
the time derivative at maximizers (`forwardDiffQuotientLE_iSup`), and hence is
dominated by solutions of `G' = ψ(t, G)` (`iSup_le_of_forwardDiff_max`).

## Design notes

* `ForwardDiffQuotientLE f t c` encodes "the forward difference quotient of
  `f` at `t` is at most `c`", i.e. `limsup_{Δt → 0⁺} (f (t+Δt) - f t)/Δt ≤ c`,
  in the robust eventual form: for every `r > c`, eventually
  `slope f t z < r` as `z → t⁺`. This avoids junk values of `limsup` for
  quotients that are unbounded near `t` and plugs directly into the
  one-dimensional fencing lemmas of `Mathlib.Analysis.Calculus.MeanValue`.
* The proof of the comparison lemma is the classical barrier argument: for
  `ε > 0` small, fence `f` by `B_ε t = G t + ε · exp (2K(t - a))`, where `K`
  is a Lipschitz constant of `ψ` in its second variable on a compact strip
  containing the graphs of `f` and `G`; at a contact point `f x = B_ε x` the
  strict inequality `ψ x (f x) < B_ε' x` holds, so
  `image_le_of_liminf_slope_right_lt_deriv_boundary'` applies. Let `ε → 0⁺`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.6.
-/

open Set Filter Real Function
open scoped Topology NNReal

namespace PoincareLib

/-- The **forward difference quotient** of `f : ℝ → ℝ` at `t` is **at most** `c`:
for every `r > c`, the right slopes `(f z - f t) / (z - t)` are eventually `< r`
as `z → t⁺`. Equivalently, `limsup_{Δt → 0⁺} (f (t + Δt) - f t)/Δt ≤ c`, with the
limsup condition read as this family of eventual bounds, which is robust even
when the quotients are unbounded near `t`. -/
def ForwardDiffQuotientLE (f : ℝ → ℝ) (t c : ℝ) : Prop :=
  ∀ r, c < r → ∀ᶠ z in 𝓝[>] t, slope f t z < r

/-- Weakening the bound on a forward difference quotient. -/
theorem ForwardDiffQuotientLE.mono {f : ℝ → ℝ} {t c c' : ℝ}
    (h : ForwardDiffQuotientLE f t c) (hcc' : c ≤ c') :
    ForwardDiffQuotientLE f t c' :=
  fun r hr => h r (lt_of_le_of_lt hcc' hr)

/-- A function with right derivative `c` at `t` has forward difference quotient
at most `c` there. -/
theorem HasDerivWithinAt.forwardDiffQuotientLE {f : ℝ → ℝ} {t c : ℝ}
    (h : HasDerivWithinAt f c (Ici t) t) : ForwardDiffQuotientLE f t c := by
  intro r hr
  have h' : Tendsto (slope f t) (𝓝[>] t) (𝓝 c) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).1 h.Ioi_of_Ici
  exact h' (Iio_mem_nhds hr)

/-- **Forward difference quotient comparison lemma** (Morgan–Tian, §2.6).
Let `f` be continuous on `[a, b]` with forward difference quotient at most
`ψ (t, f t)` at every `t ∈ [a, b)`, where `ψ` is `C¹` on the strip `[a, b] × ℝ`.
If `G` is continuous on `[a, b]`, solves `G' t = ψ (t, G t)` (as a right
derivative) on `[a, b)`, and `f a ≤ G a`, then `f t ≤ G t` on all of `[a, b]`. -/
theorem le_of_forwardDiffQuotientLE {f G : ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hfd : ∀ t ∈ Ico a b, ForwardDiffQuotientLE f t (ψ t (f t)))
    (hψ : ContDiffOn ℝ 1 (uncurry ψ) (Icc a b ×ˢ (univ : Set ℝ)))
    (hG : ContinuousOn G (Icc a b))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hab : f a ≤ G a) :
    ∀ t ∈ Icc a b, f t ≤ G t := by
  -- Trivial case: empty interval.
  rcases le_or_gt a b with hle | hlt
  swap
  · intro t ht
    exact absurd ht (by simp [Icc_eq_empty_of_lt hlt])
  -- A compact strip `S` containing the graphs of `f` and `G` over `[a, b]`.
  obtain ⟨Cf, hCf⟩ : ∃ C, ∀ x ∈ Icc a b, ‖f x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hf
  obtain ⟨Cg, hCg⟩ : ∃ C, ∀ x ∈ Icc a b, ‖G x‖ ≤ C :=
    isCompact_Icc.exists_bound_of_continuousOn hG
  set C : ℝ := max Cf Cg with hC
  have hfC : ∀ x ∈ Icc a b, |f x| ≤ C := fun x hx => (hCf x hx).trans (le_max_left _ _)
  have hgC : ∀ x ∈ Icc a b, |G x| ≤ C := fun x hx => (hCg x hx).trans (le_max_right _ _)
  set S : Set (ℝ × ℝ) := Icc a b ×ˢ Icc (-(C + 1)) (C + 1) with hS
  -- A Lipschitz constant for `ψ` on the strip, bumped to be at least 1.
  obtain ⟨K₀, hK₀⟩ : ∃ K, LipschitzOnWith K (uncurry ψ) S :=
    ContDiffOn.exists_lipschitzOnWith (hψ.mono (prod_mono_right (subset_univ _))) one_ne_zero
      ((convex_Icc a b).prod (convex_Icc _ _)) (isCompact_Icc.prod isCompact_Icc)
  set K : ℝ≥0 := K₀ + 1 with hK
  have hKlip : LipschitzOnWith K (uncurry ψ) S := hK₀.weaken (self_le_add_right K₀ 1)
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have h1 : (1 : ℝ≥0) ≤ K := le_add_self
    exact_mod_cast h1
  have hKpos : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le one_pos hK1
  -- The barrier estimate, for every sufficiently small `ε > 0`.
  have key : ∀ ε : ℝ, 0 < ε → ε * exp (2 * K * (b - a)) ≤ 1 →
      ∀ t ∈ Icc a b, f t ≤ G t + ε * exp (2 * K * (t - a)) := by
    intro ε hε hεsmall
    have hexp : ∀ x : ℝ, HasDerivAt (fun s : ℝ => ε * exp (2 * K * (s - a)))
        (ε * (exp (2 * K * (x - a)) * (2 * K))) x := by
      intro x
      have h1 : HasDerivAt (fun s : ℝ => 2 * (K : ℝ) * (s - a)) (2 * K) x := by
        simpa using ((hasDerivAt_id x).sub_const a).const_mul (2 * (K : ℝ))
      exact h1.exp.const_mul ε
    have hexp_mono : ∀ x ∈ Icc a b, ε * exp (2 * K * (x - a)) ≤ 1 := by
      intro x hx
      have h1 : exp (2 * K * (x - a)) ≤ exp (2 * K * (b - a)) := by
        have : 2 * (K : ℝ) * (x - a) ≤ 2 * K * (b - a) := by nlinarith [hx.2]
        exact exp_le_exp.2 this
      calc ε * exp (2 * K * (x - a)) ≤ ε * exp (2 * K * (b - a)) := by
            exact mul_le_mul_of_nonneg_left h1 hε.le
        _ ≤ 1 := hεsmall
    intro t ht
    refine image_le_of_liminf_slope_right_lt_deriv_boundary' (f' := fun x => ψ x (f x))
      (B := fun x => G x + ε * exp (2 * K * (x - a)))
      (B' := fun x => ψ x (G x) + ε * (exp (2 * K * (x - a)) * (2 * K)))
      hf ?_ ?_ ?_ ?_ ?_ ht
    · -- the Dini-derivative hypothesis, as a `Frequently`
      intro x hx r hr
      exact ((hfd x hx) r hr).frequently
    · -- `f a ≤ B a`
      have h0 : (0 : ℝ) < ε * exp (2 * K * (a - a)) := by positivity
      linarith
    · -- continuity of the barrier
      exact hG.add (Continuous.continuousOn (by fun_prop))
    · -- right derivative of the barrier
      exact fun x hx => (hG' x hx).add (hexp x).hasDerivWithinAt
    · -- the strict inequality at contact points
      intro x hx hcontact
      have hxI : x ∈ Icc a b := Ico_subset_Icc_self hx
      have hEpos : (0 : ℝ) < exp (2 * K * (x - a)) := exp_pos _
      have hεE : 0 < ε * exp (2 * K * (x - a)) := by positivity
      have hg := abs_le.1 (hgC x hxI)
      -- both `(x, f x)` and `(x, G x)` lie in the strip `S`
      have hGmem : (x, G x) ∈ S := ⟨hxI, by constructor <;> linarith⟩
      have hfmem : (x, f x) ∈ S := by
        have hle1 : ε * exp (2 * K * (x - a)) ≤ 1 := hexp_mono x hxI
        exact ⟨hxI, by rw [hcontact]; constructor <;> linarith⟩
      -- the Lipschitz bound at the contact point
      have habs : |ψ x (f x) - ψ x (G x)| ≤ K * (ε * exp (2 * K * (x - a))) := by
        have hdist := hKlip.dist_le_mul (x, f x) hfmem (x, G x) hGmem
        have hprod : dist ((x, f x) : ℝ × ℝ) ((x, G x) : ℝ × ℝ)
            = ε * exp (2 * K * (x - a)) := by
          rw [Prod.dist_eq, dist_self, Real.dist_eq, hcontact, add_sub_cancel_left,
            abs_of_pos hεE, max_eq_right hεE.le]
        rw [hprod] at hdist
        simpa [uncurry, Real.dist_eq] using hdist
      have hψle : ψ x (f x) - ψ x (G x) ≤ K * (ε * exp (2 * K * (x - a))) :=
        (abs_le.1 habs).2
      have hpos : 0 < (K : ℝ) * (ε * exp (2 * K * (x - a))) := by positivity
      calc ψ x (f x) ≤ ψ x (G x) + K * (ε * exp (2 * K * (x - a))) := by linarith
        _ < ψ x (G x) + 2 * ((K : ℝ) * (ε * exp (2 * K * (x - a)))) := by linarith
        _ = ψ x (G x) + ε * (exp (2 * K * (x - a)) * (2 * K)) := by ring
  -- Let `ε → 0⁺`.
  intro t ht
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hEmax : (0 : ℝ) < exp (2 * K * (b - a)) := exp_pos _
  set ε : ℝ := min (exp (2 * K * (b - a)))⁻¹ (δ / exp (2 * K * (b - a))) with hε_def
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have h1 : ε * exp (2 * K * (b - a)) ≤ 1 := by
    calc ε * exp (2 * K * (b - a)) ≤ (exp (2 * K * (b - a)))⁻¹ * exp (2 * K * (b - a)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hEmax.le
      _ = 1 := inv_mul_cancel₀ hEmax.ne'
  have h2 := key ε hε h1 t ht
  have h3 : ε * exp (2 * K * (t - a)) ≤ δ := by
    have hexp_le : exp (2 * K * (t - a)) ≤ exp (2 * K * (b - a)) := by
      have : 2 * (K : ℝ) * (t - a) ≤ 2 * K * (b - a) := by nlinarith [ht.2]
      exact exp_le_exp.2 this
    calc ε * exp (2 * K * (t - a)) ≤ (δ / exp (2 * K * (b - a))) * exp (2 * K * (b - a)) :=
          mul_le_mul (min_le_right _ _) hexp_le (exp_pos _).le (by positivity)
      _ = δ := div_mul_cancel₀ δ hEmax.ne'
  linarith

/-! ### The maximum over a compact family

The product-case core of Morgan–Tian's "forward difference maximum property":
for a family `F : X → ℝ → ℝ` over a compact space `X`, the maximum function
`u(s) = ⨆ x, F x s` is continuous, its forward difference quotient at `t` is
controlled by the time derivative `F' x t` at the maximizers `x` of `F · t`,
and consequently `u` is dominated by any solution of `G' = ψ(t, G)` dominating
it initially. This is the case of the general statement (for a vector field
`χ` on a manifold with `χ(t) = 1`) obtained by trivializing along the flow of
`χ`; it is the form used for Ricci flow on compact manifolds. -/

section SupFamily

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The maximum function `s ↦ ⨆ x, F x s` of a jointly continuous family over a
compact space is continuous. -/
theorem continuous_iSup_of_compact {F : X → ℝ → ℝ} (hF : Continuous ↿F) :
    Continuous fun s : ℝ => ⨆ x, F x s := by
  have h : Continuous ↿(fun (s : ℝ) (x : X) => F x s) := hF.comp continuous_swap
  have := isCompact_univ.continuous_sSup (f := fun (s : ℝ) (x : X) => F x s) h
  simpa [Set.image_univ, iSup] using this

/-- For fixed `s`, the family values `F x s` are bounded above. -/
theorem bddAbove_range_family {F : X → ℝ → ℝ} (hF : Continuous ↿F) (s : ℝ) :
    BddAbove (Set.range fun x : X => F x s) :=
  (isCompact_range (hF.comp (continuous_id.prodMk continuous_const))).bddAbove

/-- **Forward difference quotient of a maximum over a compact family.**
Let `F : X → ℝ → ℝ` be a jointly continuous family over a compact space, with
jointly continuous time derivative `F'` on `(t, b)`. If every maximizer `x` of
`F · t` satisfies `F' x t ≤ c`, then the maximum function `s ↦ ⨆ x, F x s` has
forward difference quotient at most `c` at `t`. -/
theorem forwardDiffQuotientLE_iSup [Nonempty X] {F F' : X → ℝ → ℝ} {t b c : ℝ} (htb : t < b)
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x : X, ∀ s ∈ Ioo t b, HasDerivAt (F x) (F' x s) s)
    (hc : ∀ x : X, F x t = (⨆ y, F y t) → F' x t ≤ c) :
    ForwardDiffQuotientLE (fun s => ⨆ x, F x s) t c := by
  set u : ℝ → ℝ := fun s => ⨆ x, F x s with hu_def
  have hucont : Continuous u := continuous_iSup_of_compact hF
  intro r hr
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  -- The "bad" set of right-hand points where the slope of `u` is at least `r`.
  set W : Set ℝ := {z | z ∈ Ioo t b ∧ r ≤ slope u t z} with hW_def
  set L : Filter ℝ := 𝓝[>] t ⊓ 𝓟 W with hL_def
  have hLne : L.NeBot := by
    rw [hL_def, ← frequently_iff_neBot]
    have hIoo : ∀ᶠ z in 𝓝[>] t, z ∈ Ioo t b := Ioo_mem_nhdsGT htb
    exact (hcon.and_eventually hIoo).mono fun z hz => ⟨hz.2, not_lt.1 hz.1⟩
  have hWL : W ∈ L := mem_inf_of_right (mem_principal_self W)
  -- For each bad `z`, choose a maximizer of `F · z` and a mean-value point in `(t, z)`.
  have hex : ∀ z : ℝ, ∃ (x : X) (s : ℝ), z ∈ W →
      F x z = u z ∧ s ∈ Ioo t z ∧ r ≤ F' x s := by
    intro z
    by_cases hz : z ∈ W
    swap
    · exact ⟨Classical.arbitrary X, 0, fun h => absurd h hz⟩
    obtain ⟨htz, hslope⟩ := hz
    -- the maximizer
    obtain ⟨x, -, hxmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty
      (show Continuous fun x : X => F x z from
        hF.comp (continuous_id.prodMk continuous_const)).continuousOn
    have hxu : F x z = u z :=
      le_antisymm (le_ciSup (bddAbove_range_family hF z) x)
        (ciSup_le fun y => hxmax (mem_univ y))
    -- the slope of `F x` on `[t, z]` dominates the slope of `u`
    have hzt : (0 : ℝ) < z - t := sub_pos.2 htz.1
    have hslopeF : r ≤ (F x z - F x t) / (z - t) := by
      rw [slope_def_field] at hslope
      refine hslope.trans ?_
      have hFxt : F x t ≤ u t := le_ciSup (bddAbove_range_family hF t) x
      have hnum : u z - u t ≤ F x z - F x t := by rw [hxu]; linarith
      exact (div_le_div_iff_of_pos_right hzt).2 hnum
    -- mean value theorem on `[t, z]`
    obtain ⟨s, hs, hs'⟩ := exists_hasDerivAt_eq_slope (F x) (F' x) htz.1
      (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
      (fun s hs => hderiv x s ⟨hs.1, hs.2.trans htz.2⟩)
    exact ⟨x, s, fun _ => ⟨hxu, hs, hslopeF.trans_eq hs'.symm⟩⟩
  choose ξ σ hξσ using hex
  set φ : ℝ → X × ℝ × ℝ := fun z => (ξ z, σ z, z) with hφ_def
  -- The image filter lives in a compact set, so it has a cluster point.
  have hmapK : Filter.map φ L ≤ 𝓟 ((univ : Set X) ×ˢ Icc t b ×ˢ Icc t b) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    filter_upwards [hWL] with z hz
    obtain ⟨-, hsIoo, -⟩ := hξσ z hz
    exact ⟨trivial, ⟨hsIoo.1.le, (hsIoo.2.trans hz.1.2).le⟩, hz.1.1.le, hz.1.2.le⟩
  obtain ⟨⟨x₀, s₀, z₀⟩, -, hclust⟩ :=
    (isCompact_univ.prod (isCompact_Icc.prod isCompact_Icc)).exists_clusterPt hmapK
  -- Cluster points lie in every closed set the image filter eventually inhabits.
  have hmem_closed : ∀ C : Set (X × ℝ × ℝ), IsClosed C →
      (∀ z ∈ W, φ z ∈ C) → (x₀, s₀, z₀) ∈ C := by
    intro C hC hev
    have hle : Filter.map φ L ≤ 𝓟 C := by
      rw [Filter.le_principal_iff, Filter.mem_map]
      filter_upwards [hWL] with z hz using hev z hz
    have := hclust.mono hle
    rwa [← mem_closure_iff_clusterPt, hC.closure_eq] at this
  -- (i) `t ≤ s₀ ≤ z₀`.
  have hs₀ : t ≤ s₀ ∧ s₀ ≤ z₀ := by
    have := hmem_closed {p : X × ℝ × ℝ | t ≤ p.2.1 ∧ p.2.1 ≤ p.2.2}
      ((isClosed_le continuous_const continuous_snd.fst).inter
        (isClosed_le continuous_snd.fst continuous_snd.snd)) ?_
    · exact this
    · intro z hz
      obtain ⟨-, hsIoo, -⟩ := hξσ z hz
      exact ⟨hsIoo.1.le, hsIoo.2.le⟩
  -- (ii) `r ≤ F' x₀ s₀`.
  have hF'r : r ≤ F' x₀ s₀ := by
    have := hmem_closed {p : X × ℝ × ℝ | r ≤ F' p.1 p.2.1}
      (isClosed_le continuous_const (hF'.comp (continuous_fst.prodMk continuous_snd.fst))) ?_
    · exact this
    · intro z hz
      obtain ⟨-, -, hr'⟩ := hξσ z hz
      exact hr'
  -- (iii) `F x₀ z₀ = u z₀`.
  have hmax₀ : F x₀ z₀ = u z₀ := by
    have := hmem_closed {p : X × ℝ × ℝ | F p.1 p.2.2 = u p.2.2}
      (isClosed_eq (hF.comp (continuous_fst.prodMk continuous_snd.snd))
        (hucont.comp continuous_snd.snd)) ?_
    · exact this
    · intro z hz
      obtain ⟨hzu, -, -⟩ := hξσ z hz
      exact hzu
  -- (iv) `z₀ = t`: the third coordinate of the image filter is `L`, which tends to `t`.
  have hz₀ : z₀ = t := by
    have h1 : Filter.map (fun p : X × ℝ × ℝ => p.2.2) (𝓝 (x₀, s₀, z₀) ⊓ Filter.map φ L) ≤
        𝓝 z₀ ⊓ L := by
      refine le_trans Filter.map_inf_le (inf_le_inf ?_ ?_)
      · exact (continuous_snd.snd.tendsto _)
      · rw [Filter.map_map]
        simp only [hφ_def, Function.comp_def]
        exact le_of_eq Filter.map_id
    have h2 : (𝓝 z₀ ⊓ L).NeBot := hclust.neBot.map _ |>.mono h1
    have h3 : (𝓝 z₀ ⊓ 𝓝 t).NeBot :=
      h2.mono (inf_le_inf le_rfl (le_trans inf_le_left nhdsWithin_le_nhds))
    exact eq_of_nhds_neBot h3
  -- Conclude: `x₀` is a maximizer at time `t` with `F' x₀ t ≥ r > c`.
  have hs₀t : s₀ = t := le_antisymm (hs₀.2.trans_eq hz₀) hs₀.1
  rw [hz₀] at hmax₀
  rw [hs₀t] at hF'r
  exact absurd ((hc x₀ hmax₀).trans_lt hr) (not_lt.2 hF'r)

/-- **Forward difference maximum property, product case** (Morgan–Tian, §2.6).
Let `F : X → ℝ → ℝ` be a jointly continuous family over a compact space with
jointly continuous time derivative `F'` on `(a, b)`. Suppose that at every
`t ∈ [a, b)` and every maximizer `x` of `F · t` we have
`F' x t ≤ ψ (t, F_max t)`, where `F_max t = ⨆ x, F x t` and `ψ` is `C¹` on the
strip `[a, b] × ℝ`. If `G` solves `G' = ψ (t, G)` on `[a, b)` with
`F_max a ≤ G a`, then `F_max t ≤ G t` on all of `[a, b]`. -/
theorem iSup_le_of_forwardDiff_max [Nonempty X]
    {F F' : X → ℝ → ℝ} {ψ : ℝ → ℝ → ℝ} {G : ℝ → ℝ} {a b : ℝ}
    (hF : Continuous ↿F) (hF' : Continuous ↿F')
    (hderiv : ∀ x : X, ∀ s ∈ Ioo a b, HasDerivAt (F x) (F' x s) s)
    (hψ : ContDiffOn ℝ 1 (uncurry ψ) (Icc a b ×ˢ (univ : Set ℝ)))
    (hmax : ∀ t ∈ Ico a b, ∀ x : X, F x t = (⨆ y, F y t) → F' x t ≤ ψ t (⨆ y, F y t))
    (hG : ContinuousOn G (Icc a b))
    (hG' : ∀ t ∈ Ico a b, HasDerivWithinAt G (ψ t (G t)) (Ici t) t)
    (hab : (⨆ x, F x a) ≤ G a) :
    ∀ t ∈ Icc a b, (⨆ x, F x t) ≤ G t := by
  refine le_of_forwardDiffQuotientLE (continuous_iSup_of_compact hF).continuousOn
    (fun t ht => ?_) hψ hG hG' hab
  exact forwardDiffQuotientLE_iSup ht.2 hF hF'
    (fun x s hs => hderiv x s ⟨ht.1.trans_lt hs.1, hs.2⟩)
    (fun x hx => hmax t ht x hx)

end SupFamily

end PoincareLib

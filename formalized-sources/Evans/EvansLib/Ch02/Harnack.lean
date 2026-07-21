import EvansLib.Ch02.MeanValue
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Evans, Ch. 2 §2.2.3 Theorem 11 — Harnack's inequality (global form)

Evans, *Partial Differential Equations* (2nd ed.), §2.2.3 Theorem 11: for each
connected `V ⋐ U` there is a constant `C = C(V)` such that `sup_V u ≤ C · inf_V u`
for **all** nonnegative harmonic functions `u` on `U`.

Following the strategy of `EvansLib.Ch02.MeanValue`, we take the (solid-ball)
mean-value property `HasBallMeanValueProperty` as the working hypothesis — the
bridge `harmonic ⟹ MVP` (Evans Thm 2) is the one step still gated on the
divergence theorem for balls. The one-step comparison `u y ≤ 2ⁿ u x` for
`dist x y ≤ r`, `closedBall x (2r) ⊆ U` is `EvansLib.harnack_local`; this file
performs Evans's chain-of-balls argument:

* cover the compact set `closure V` by finitely many balls `B(zᵢ, r/2)` with
  centres `zᵢ ∈ closure V` (`IsCompact.finite_cover_balls`);
* form the intersection graph `ballChainGraph` on the centres — two centres are
  adjacent when their balls overlap *at a point of `V`* — and show by a clopen
  argument that preconnectedness of `V` makes every centre whose ball meets `V`
  reachable from every other one (`exists_reachable_center`);
* iterate `harnack_local` along a walk in this graph (`le_pow_mul_of_walk`);
  shortcutting the walk to a path bounds its length by `N := #centres`, giving
  `u x ≤ (2ⁿ)^N u y` for all `x, y ∈ V`.

Main result: `EvansLib.exists_harnack_const` — the constant `C` is produced
*before* the function `u` is quantified, so it depends only on `V` (and `U`, `n`)
as in Evans's statement.

Reference: Evans, *Partial Differential Equations* (2nd ed., AMS GSM 19), §2.2.3.
-/

open MeasureTheory Metric Set

noncomputable section

namespace EvansLib

variable {n : ℕ}

/-- The **intersection graph** on a set `Z` of ball centres: two centres are adjacent
when they are distinct and their `ρ`-balls overlap at a point of `V`. Walks in this
graph are Evans's "chains of overlapping balls" (§2.2.3, proof of Thm 11). -/
def ballChainGraph (Z : Set (EuclideanSpace ℝ (Fin n))) (ρ : ℝ)
    (V : Set (EuclideanSpace ℝ (Fin n))) : SimpleGraph Z where
  Adj z w := z ≠ w ∧
    (ball (z : EuclideanSpace ℝ (Fin n)) ρ ∩ ball (w : EuclideanSpace ℝ (Fin n)) ρ ∩
      V).Nonempty
  symm := by
    rintro z w ⟨hne, v, ⟨hvz, hvw⟩, hvV⟩
    exact ⟨hne.symm, v, ⟨hvw, hvz⟩, hvV⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

lemma ballChainGraph_adj {Z : Set (EuclideanSpace ℝ (Fin n))} {ρ : ℝ}
    {V : Set (EuclideanSpace ℝ (Fin n))} {z w : Z} :
    (ballChainGraph Z ρ V).Adj z w ↔ z ≠ w ∧
      (ball (z : EuclideanSpace ℝ (Fin n)) ρ ∩ ball (w : EuclideanSpace ℝ (Fin n)) ρ ∩
        V).Nonempty :=
  Iff.rfl

/-- **Chain step.** If `V` is preconnected and covered by the `ρ`-balls centred at `Z`,
then from any centre `z₀` whose ball meets `V`, every point `y ∈ V` lies in the ball of
some centre reachable from `z₀` in the intersection graph. This is the "chain of
overlapping balls" existence in Evans's proof of Harnack's inequality, obtained here by
a clopen argument from preconnectedness. -/
lemma exists_reachable_center {V Z : Set (EuclideanSpace ℝ (Fin n))} {ρ : ℝ}
    (hVconn : IsPreconnected V) (hcov : V ⊆ ⋃ z ∈ Z, ball z ρ)
    {z₀ : Z} (h₀ : (ball (z₀ : EuclideanSpace ℝ (Fin n)) ρ ∩ V).Nonempty) :
    ∀ y ∈ V, ∃ z : Z, y ∈ ball (z : EuclideanSpace ℝ (Fin n)) ρ ∧
      (ballChainGraph Z ρ V).Reachable z₀ z := by
  obtain ⟨x₀, hx₀ball, hx₀V⟩ := h₀
  intro y hyV
  haveI : PreconnectedSpace V := Subtype.preconnectedSpace hVconn
  -- the set of points of `V` covered by a reachable centre; it is clopen and nonempty
  set S : Set V := {p | ∃ z : Z, (p : EuclideanSpace ℝ (Fin n)) ∈
    ball (z : EuclideanSpace ℝ (Fin n)) ρ ∧ (ballChainGraph Z ρ V).Reachable z₀ z} with hS
  have hSopen : IsOpen S := by
    rw [Metric.isOpen_iff]
    rintro p ⟨z, hpz, hreach⟩
    rw [mem_ball] at hpz
    refine ⟨ρ - dist (p : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)),
      by linarith, ?_⟩
    rintro q hq
    rw [mem_ball, Subtype.dist_eq] at hq
    refine ⟨z, ?_, hreach⟩
    rw [mem_ball]
    calc dist (q : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n))
        ≤ dist (q : EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) +
          dist (p : EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin n)) :=
        dist_triangle _ _ _
      _ < ρ := by linarith
  have hSclosed : IsClosed S := by
    refine isClosed_of_closure_subset ?_
    intro p hp
    -- cover the limit point by one of the balls
    have hpcov : (p : EuclideanSpace ℝ (Fin n)) ∈ ⋃ z ∈ Z, ball z ρ := hcov p.2
    rw [mem_iUnion₂] at hpcov
    obtain ⟨z', hz'Z, hpz'⟩ := hpcov
    rw [mem_ball] at hpz'
    -- find a point of `S` within the leftover distance
    obtain ⟨q, hqS, hpq⟩ := Metric.mem_closure_iff.1 hp _
      (show 0 < ρ - dist (p : EuclideanSpace ℝ (Fin n)) z' by linarith)
    obtain ⟨zq, hqzq, hreachq⟩ := hqS
    rw [Subtype.dist_eq, dist_comm] at hpq
    have hqz' : (q : EuclideanSpace ℝ (Fin n)) ∈ ball z' ρ := by
      rw [mem_ball]
      calc dist (q : EuclideanSpace ℝ (Fin n)) z'
          ≤ dist (q : EuclideanSpace ℝ (Fin n)) (p : EuclideanSpace ℝ (Fin n)) +
            dist (p : EuclideanSpace ℝ (Fin n)) z' := dist_triangle _ _ _
        _ < ρ := by linarith
    refine ⟨⟨z', hz'Z⟩, mem_ball.2 hpz', ?_⟩
    -- the witness `q` makes `zq` and `z'` adjacent (or equal)
    rcases eq_or_ne zq ⟨z', hz'Z⟩ with heq | hne
    · exact heq ▸ hreachq
    · exact hreachq.trans (SimpleGraph.Adj.reachable ⟨hne, q, ⟨hqzq, hqz'⟩, q.2⟩)
  have hSne : S.Nonempty :=
    ⟨⟨x₀, hx₀V⟩, z₀, hx₀ball, SimpleGraph.Reachable.refl z₀⟩
  have hSuniv : S = univ := IsClopen.eq_univ ⟨hSclosed, hSopen⟩ hSne
  exact show (⟨y, hyV⟩ : V) ∈ S from hSuniv ▸ mem_univ _

/-- **Iterating the one-step Harnack bound along a chain of balls.** If `step` is the
local comparison `u q ≤ 2ⁿ u p` for points of `V` at distance `≤ r`, then along a walk
of length `ℓ` in the intersection graph of `(r/2)`-balls, values at points of `V`
covered by the two endpoint balls satisfy `u a ≤ (2ⁿ)^(ℓ+1) u b`. -/
lemma le_pow_mul_of_walk {V Z : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (step : ∀ p ∈ V, ∀ q, dist p q ≤ r → u q ≤ 2 ^ n * u p)
    {z w : Z} (p : (ballChainGraph Z (r / 2) V).Walk z w) :
    ∀ a ∈ ball (z : EuclideanSpace ℝ (Fin n)) (r / 2) ∩ V,
    ∀ b ∈ ball (w : EuclideanSpace ℝ (Fin n)) (r / 2) ∩ V,
      u a ≤ ((2 : ℝ) ^ n) ^ (p.length + 1) * u b := by
  induction p with
  | @nil z₁ =>
    rintro a ⟨haz, haV⟩ b ⟨hbz, hbV⟩
    have hab : dist b a ≤ r := by
      rw [mem_ball] at haz hbz
      calc dist b a
          ≤ dist b (z₁ : EuclideanSpace ℝ (Fin n)) + dist a (z₁ : EuclideanSpace ℝ (Fin n)) :=
          dist_triangle_right _ _ _
        _ ≤ r := by linarith
    simpa using step b hbV a hab
  | @cons z₁ z₂ w₁ h q ih =>
    rintro a ⟨haz, haV⟩ b hb
    rw [SimpleGraph.Walk.length_cons]
    obtain ⟨-, v, ⟨hvz, hvz'⟩, hvV⟩ := h
    have hav : dist v a ≤ r := by
      rw [mem_ball] at haz hvz
      calc dist v a
          ≤ dist v (z₁ : EuclideanSpace ℝ (Fin n)) + dist a (z₁ : EuclideanSpace ℝ (Fin n)) :=
          dist_triangle_right _ _ _
        _ ≤ r := by linarith
    have h1 : u a ≤ 2 ^ n * u v := step v hvV a hav
    have h2 := ih v ⟨hvz', hvV⟩ b hb
    calc u a ≤ 2 ^ n * u v := h1
      _ ≤ 2 ^ n * (((2 : ℝ) ^ n) ^ (q.length + 1) * u b) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ((2 : ℝ) ^ n) ^ (q.length + 1 + 1) * u b := by ring

/-- **Harnack's inequality** (`thm:harnacks-inequality`, Evans §2.2.3 Thm 11), for
functions with the ball mean-value property. For every preconnected bounded `V` whose
closure lies in the open set `U`, there is a constant `C > 0`, depending only on `V`
(not on `u`!), such that `u x ≤ C * u y` for all `x, y ∈ V` and all nonnegative
continuous `u` having the ball mean-value property on `U`. Equivalently
`sup_V u ≤ C · inf_V u`: the values of a nonnegative harmonic function on `V` are all
comparable. -/
theorem exists_harnack_const [Nonempty (Fin n)]
    {U V : Set (EuclideanSpace ℝ (Fin n))}
    (hUopen : IsOpen U) (hVconn : IsPreconnected V)
    (hVbdd : Bornology.IsBounded V) (hVU : closure V ⊆ U) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : EuclideanSpace ℝ (Fin n) → ℝ,
      HasBallMeanValueProperty u U → ContinuousOn u U → (∀ z ∈ U, 0 ≤ u z) →
      ∀ x ∈ V, ∀ y ∈ V, u x ≤ C * u y := by
  classical
  have hK : IsCompact (closure V) := hVbdd.isCompact_closure
  -- a margin `r > 0` such that `closedBall z (2r) ⊆ U` for every `z ∈ closure V`
  obtain ⟨δ, hδpos, hδsub⟩ := hK.exists_cthickening_subset_open hUopen hVU
  set r : ℝ := δ / 2 with hr_def
  have hrpos : 0 < r := by positivity
  have hball2r : ∀ z ∈ closure V, closedBall z (2 * r) ⊆ U := by
    intro z hz
    have h2r : 2 * r = δ := by rw [hr_def]; ring
    calc closedBall z (2 * r) = closedBall z δ := by rw [h2r]
      _ ⊆ cthickening δ (closure V) := closedBall_subset_cthickening hz δ
      _ ⊆ U := hδsub
  -- finite cover of the compact closure by balls of radius `r/2` centred in it
  obtain ⟨Z, hZsub, hZfin, hZcov⟩ := hK.finite_cover_balls (e := r / 2) (by positivity)
  haveI : Fintype Z := hZfin.fintype
  have hcovV : V ⊆ ⋃ z ∈ Z, ball z (r / 2) := subset_closure.trans hZcov
  -- the constant: `(2ⁿ)^(number of balls)`
  refine ⟨((2 : ℝ) ^ n) ^ Fintype.card Z, by positivity, ?_⟩
  intro u hu hcont hnonneg x hxV y hyV
  -- one Harnack step: points of `V` within distance `r` have comparable values
  have step : ∀ p ∈ V, ∀ q, dist p q ≤ r → u q ≤ 2 ^ n * u p := fun p hp q hpq =>
    harnack_local hu hcont hnonneg hrpos hpq (hball2r p (subset_closure hp))
  -- cover `x` by a ball centre, and reach the centre covering `y`
  have hxcov : x ∈ ⋃ z ∈ Z, ball z (r / 2) := hcovV hxV
  rw [mem_iUnion₂] at hxcov
  obtain ⟨zx, hzxZ, hxzx⟩ := hxcov
  obtain ⟨zy, hyzy, hreach⟩ :=
    exists_reachable_center hVconn hcovV (z₀ := ⟨zx, hzxZ⟩) ⟨x, hxzx, hxV⟩ y hyV
  -- extract a walk, shortcut it to a path, and iterate the local bound along it
  obtain ⟨p⟩ := hreach
  have hlen : p.bypass.length + 1 ≤ Fintype.card Z :=
    Nat.succ_le_of_lt (SimpleGraph.Walk.IsPath.length_lt p.bypass_isPath)
  have hb := le_pow_mul_of_walk step p.bypass x ⟨hxzx, hxV⟩ y ⟨hyzy, hyV⟩
  have hone : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ one_le_two
  calc u x ≤ ((2 : ℝ) ^ n) ^ (p.bypass.length + 1) * u y := hb
    _ ≤ ((2 : ℝ) ^ n) ^ Fintype.card Z * u y :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hone hlen)
          (hnonneg y (hVU (subset_closure hyV)))

end EvansLib

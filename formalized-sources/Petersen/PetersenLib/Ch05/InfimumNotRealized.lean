import PetersenLib.Ch05.PuncturedPlane

/-!
# Petersen Ch. 5, §5.3 — Example 5.3.1: in `ℝ² − {0}` the distance is not realized

Petersen's Example 5.3.1: in `ℝ² − {(0,0)}` with the induced (flat) metric the
two points `p = (-1, 0)` and `q = (1, 0)` satisfy `|pq| = 2`, but **no curve from
`p` to `q` inside `ℝ² − {0}` has length `2`** — the infimum defining `|pq|` is
approached (by the detours through `(0, δ)`, `δ ↓ 0`) but never attained.  In the
language developed later in the chapter, `ℝ² − {0}` is incomplete.

Contents:

* `norm_sub_le_curveLength_opensFlatMetric_Icc` — the chord bound of
  `Ch05/OpenSubmanifoldFlat.lean` on an arbitrary domain `[a, b]` (the landed
  version is normalized to `[0, 1]`);
* `puncturedPlane_coord_one_eq_zero_of_curveLength_eq_two` — the geometric heart:
  a length-`2` curve from `p` to `q` is *pinned to the `x`-axis*, i.e. its second
  coordinate vanishes identically;
* `no_curve_of_length_two_pLeft_pRight` — no piecewise `C^∞` curve from `p` to `q`
  in `ℝ² − {0}` has length `2`;
* `example_infimum_not_realized` — **Example 5.3.1**: `|pq| = 2` *and* the
  infimum is not realized.

## The proof

Let `γ : [a, b] → ℝ² − {0}` run from `p` to `q` with `L(γ) = 2`.  Fix `t ∈ [a,b]`
and write `m = γ(t)`.  Additivity of length splits `2 = L|_a^t + L|_t^b`, and the
ambient chord bound (`norm_sub_le_curveLength_opensFlatMetric_Icc`, valid because
an open subset of `ℝⁿ` can only make curves *longer*) gives

  `‖m − p‖ + ‖q − m‖ ≤ L|_a^t + L|_t^b = 2 = ‖q − p‖ ≤ ‖m − p‖ + ‖q − m‖`,

so the triangle inequality for `A = m − p`, `C = q − m` is an *equality*.  The
Cauchy–Schwarz equality case (`inner_eq_norm_mul_iff_real`) then yields
`‖C‖ • A = ‖A‖ • C`; reading off the second coordinate (`A 1 = m 1`, `C 1 = −m 1`)
gives `(‖A‖ + ‖C‖) · m 1 = 0`, and `‖A‖ + ‖C‖ = 2 ≠ 0`, so `m 1 = 0`.  Thus the
whole curve lies on the `x`-axis.

Now the first coordinate `f(t) = γ(t) 0` is continuous on `[a, b]` with
`f(a) = −1` and `f(b) = 1`, so the intermediate value theorem produces `t₀` with
`f(t₀) = 0`.  Both coordinates of `γ(t₀)` vanish, i.e. `γ(t₀) = (0,0)` — which is
not a point of the punctured plane.  Contradiction.

Note the intermediate value theorem is applied to the *coordinate function* of
the curve, not to `t ↦ L(γ)|_a^t`; this is what makes the argument work for an
arbitrary parametrization, with no proportional-arc-length hypothesis (contrast
`no_segment_pLeft_pRight` in `Ch05/PuncturedPlane.lean`, which is about segments
and does use that clause).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §5.3, Example 5.3.1.
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bornology TopologicalSpace Set
open scoped ContDiff Manifold Topology

namespace PetersenLib

/-! ## The chord bound on an arbitrary domain -/

section Euclidean

variable {n : ℕ} [NeZero n]

/-- **Math.** **Chord bound on `[a, b]`.** For a piecewise `C^∞` curve
`γ : [a, b] → s` inside an open subset `s ⊆ ℝⁿ` carrying the flat metric, the
ambient Euclidean chord `‖γ(a) − γ(b)‖` is at most the intrinsic length of `γ`.
This is `norm_sub_le_curveLength_opensFlatMetric` (which is normalized to the
domain `[0, 1]`) transported along the affine reparametrization
`s ↦ γ((b − a) s + a)`. -/
theorem norm_sub_le_curveLength_opensFlatMetric_Icc
    (s : Opens (EuclideanSpace ℝ (Fin n))) {γ : ℝ → s} {a b : ℝ} (hab : a ≤ b)
    (hγ : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) γ a b) :
    ‖(γ a : EuclideanSpace ℝ (Fin n)) - (γ b : EuclideanSpace ℝ (Fin n))‖
      ≤ curveLength (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
          (opensFlatMetric (EuclideanSpace ℝ (Fin n)) s) γ a b := by
  rcases hab.eq_or_lt with rfl | hlt
  · simp
  · have hc : 0 < b - a := by linarith
    have he1 : (b - a) * 0 + a = a := by ring
    have he2 : (b - a) * 1 + a = b := by ring
    have hpw' : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (fun r => γ ((b - a) * r + a)) 0 1 := by
      refine isPiecewiseSmoothCurve_comp_mul_add (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) hc ?_
      rw [he1, he2]; exact hγ
    have hchord := norm_sub_le_curveLength_opensFlatMetric (n := n) s
      (γ := fun r => γ ((b - a) * r + a)) (x := γ a) (y := γ b) hpw'
      (by show γ ((b - a) * 0 + a) = γ a; rw [he1])
      (by show γ ((b - a) * 1 + a) = γ b; rw [he2])
    rwa [curveLength_comp_mul_add (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (opensFlatMetric (EuclideanSpace ℝ (Fin n)) s) γ hc.le a 0 1, he1, he2] at hchord

end Euclidean

/-! ## Coordinates of `vec` -/

/-- **Math.** The first coordinate of `(a, b)` is `a`. -/
@[simp] theorem vec_apply_zero (a b : ℝ) : (vec a b) 0 = a := by
  simp [vec]

/-- **Math.** The second coordinate of `(a, b)` is `b`. -/
@[simp] theorem vec_apply_one (a b : ℝ) : (vec a b) 1 = b := by
  simp [vec]

/-- **Math.** A plane vector both of whose coordinates vanish is `0`. -/
theorem eq_zero_of_coords_eq_zero {v : E2} (h0 : v 0 = 0) (h1 : v 1 = 0) : v = 0 := by
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1

/-- **Math.** Evaluating a curve into an open subset of `E²` at a fixed
coordinate is continuous: it is the continuous linear functional
`EuclideanSpace.proj i` composed with the (continuous) inclusion `s ↪ E²`. -/
theorem continuousOn_coord_of_continuousOn {s : Opens E2} {γ : ℝ → s} {A : Set ℝ}
    (h : ContinuousOn γ A) (i : Fin 2) :
    ContinuousOn (fun t => (γ t : E2) i) A :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp continuous_subtype_val).comp_continuousOn h

/-! ## A length-`2` curve from `(-1,0)` to `(1,0)` is pinned to the `x`-axis -/

section

variable {γ : ℝ → puncturedPlane} {a b : ℝ}

/-- **Math.** The domain of a piecewise `C^∞` curve on `[a, b]` is nondegenerate:
`a ≤ b` (read off the endpoints of the partition). -/
theorem le_of_isPiecewiseSmoothCurve
    (hpw : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) γ a b) : a ≤ b := by
  obtain ⟨-, n, u, hmono, hu0, hun, -⟩ := hpw
  rw [← hu0, ← hun]
  exact hmono (Fin.zero_le _)

/-- **Math.** **The rigidity step of Example 5.3.1.** If a piecewise `C^∞` curve
`γ : [a, b] → ℝ² − {0}` runs from `(-1, 0)` to `(1, 0)` and has length exactly
`2 = |pq|`, then it lies on the `x`-axis: `γ(t) 1 = 0` for every `t ∈ [a, b]`.

Splitting the length at `t` and bounding each half below by its ambient chord
turns the triangle inequality `‖q − p‖ ≤ ‖γ(t) − p‖ + ‖q − γ(t)‖` into an
equality; Cauchy–Schwarz equality (`inner_eq_norm_mul_iff_real`) then forces
`‖C‖ • A = ‖A‖ • C` for `A = γ(t) − p`, `C = q − γ(t)`, whose second coordinate
reads `(‖A‖ + ‖C‖) · γ(t) 1 = 0` with `‖A‖ + ‖C‖ = 2`. -/
theorem puncturedPlane_coord_one_eq_zero_of_curveLength_eq_two
    (hpw : IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) γ a b)
    (ha : γ a = pLeft) (hb : γ b = pRight)
    (hlen : curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ a b = 2)
    {t : ℝ} (ht : t ∈ Icc a b) :
    (γ t : E2) 1 = 0 := by
  obtain ⟨hat, htb⟩ := ht
  -- split the length at `t`
  have hsplit := hpw.curveLength_add (I := 𝓘(ℝ, E2)) puncturedPlaneMetric hat htb
  rw [hlen] at hsplit
  -- each half is bounded below by its ambient chord
  have hfst : ‖(γ a : E2) - (γ t : E2)‖
      ≤ curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ a t :=
    norm_sub_le_curveLength_opensFlatMetric_Icc (n := 2) puncturedPlane hat
      (hpw.mono (I := 𝓘(ℝ, E2)) le_rfl hat htb)
  have hsnd : ‖(γ t : E2) - (γ b : E2)‖
      ≤ curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ t b :=
    norm_sub_le_curveLength_opensFlatMetric_Icc (n := 2) puncturedPlane htb
      (hpw.mono (I := 𝓘(ℝ, E2)) hat htb le_rfl)
  set m : E2 := (γ t : E2) with hm
  set A : E2 := m - (pLeft : E2) with hA
  set C : E2 := (pRight : E2) - m with hC
  have hnA : ‖A‖ ≤ curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ a t := by
    rw [hA, ← norm_neg]
    simpa [ha] using hfst
  have hnC : ‖C‖ ≤ curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ t b := by
    rw [hC, ← norm_neg]
    simpa [hb] using hsnd
  have hsum : ‖A‖ + ‖C‖ ≤ 2 := by rw [hsplit]; exact add_le_add hnA hnC
  have hAC : A + C = (pRight : E2) - (pLeft : E2) := by rw [hA, hC]; abel
  have hnAC : ‖A + C‖ = 2 := by
    rw [hAC, ← norm_neg, neg_sub]; exact norm_pLeft_sub_pRight
  have htri : ‖A + C‖ ≤ ‖A‖ + ‖C‖ := norm_add_le A C
  -- the triangle inequality is an equality
  have hsum2 : ‖A‖ + ‖C‖ = 2 := by rw [hnAC] at htri; linarith
  -- Cauchy–Schwarz equality
  have hinner : (inner ℝ A C : ℝ) = ‖A‖ * ‖C‖ := by
    have hexp := norm_add_sq_real A C
    rw [hnAC] at hexp
    nlinarith [hexp, hsum2]
  have heq : ‖C‖ • A = ‖A‖ • C := (inner_eq_norm_mul_iff_real).mp hinner
  -- read off the second coordinate
  have hcoord : ‖C‖ * A 1 = ‖A‖ * C 1 := by
    have hc := congrArg (fun v : E2 => v 1) heq
    simpa using hc
  have hA1 : A 1 = m 1 := by rw [hA]; simp
  have hC1 : C 1 = -m 1 := by rw [hC]; simp
  rw [hA1, hC1] at hcoord
  nlinarith [hcoord, hsum2]

end

/-! ## No curve of length `2` -/

/-- **Math.** **Petersen Example 5.3.1 (the unrealized half).** No piecewise
`C^∞` curve from `(-1, 0)` to `(1, 0)` inside `ℝ² − {(0,0)}` has length `2`,
whatever its domain `[a, b]`.

Such a curve would lie on the `x`-axis
(`puncturedPlane_coord_one_eq_zero_of_curveLength_eq_two`), and its first
coordinate is a continuous function on `[a, b]` running from `−1` to `1`; by the
intermediate value theorem it vanishes at some `t₀`, so `γ(t₀) = (0,0)`, which is
not a point of the punctured plane. -/
theorem no_curve_of_length_two_pLeft_pRight :
    ¬ ∃ (γ : ℝ → puncturedPlane) (a b : ℝ),
        IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) γ a b ∧ γ a = pLeft ∧ γ b = pRight ∧
        curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ a b = 2 := by
  rintro ⟨γ, a, b, hpw, ha, hb, hlen⟩
  have hab : a ≤ b := le_of_isPiecewiseSmoothCurve hpw
  -- the curve lies on the `x`-axis
  have haxis : ∀ t ∈ Icc a b, (γ t : E2) 1 = 0 := fun t ht =>
    puncturedPlane_coord_one_eq_zero_of_curveLength_eq_two hpw ha hb hlen ht
  -- the first coordinate is continuous and runs from `-1` to `1`
  have hcont : ContinuousOn (fun t => (γ t : E2) 0) (Icc a b) :=
    continuousOn_coord_of_continuousOn hpw.1 0
  have hfa : (γ a : E2) 0 = -1 := by rw [ha]; simp
  have hfb : (γ b : E2) 0 = 1 := by rw [hb]; simp
  have hivt := intermediate_value_Icc hab hcont
  have hmem : (0 : ℝ) ∈ Icc ((γ a : E2) 0) ((γ b : E2) 0) := by
    rw [hfa, hfb]; constructor <;> norm_num
  obtain ⟨t₀, ht₀, hft₀⟩ := hivt hmem
  -- both coordinates of `γ(t₀)` vanish, so `γ(t₀) = (0,0) ∉ ℝ² − {0}`
  exact (γ t₀).2 (eq_zero_of_coords_eq_zero hft₀ (haxis t₀ ht₀))

/-- **Math.** **Example 5.3.1** (Petersen §5.3, `ex:pet-ch5-infimum-not-realized`).
In `ℝ² − {(0,0)}` with the induced metric the distance between `(-1, 0)` and
`(1, 0)` is `|(-1,0)(1,0)| = 2`, **but no curve joining them has length `2`** — so
this distance is not realized by any curve.  (In the sense developed later in the
chapter, `ℝ² − {0}` is therefore incomplete: by Hopf–Rinow a complete manifold
realizes every distance by a segment.)

The infimum *is* approached: the detours through `(0, δ)` have length
`2√(1 + δ²) → 2` as `δ ↓ 0` (`riemannianDistance_le_detour`).  It is simply never
attained, because a competitor of length `2` would have to be the straight
segment from `(-1,0)` to `(1,0)`, which passes through the deleted origin. -/
theorem example_infimum_not_realized :
    riemannianDistance (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft pRight = 2 ∧
      ¬ ∃ (γ : ℝ → puncturedPlane) (a b : ℝ),
          IsPiecewiseSmoothCurve (I := 𝓘(ℝ, E2)) γ a b ∧ γ a = pLeft ∧ γ b = pRight ∧
          curveLength (I := 𝓘(ℝ, E2)) puncturedPlaneMetric γ a b
            = riemannianDistance (I := 𝓘(ℝ, E2)) puncturedPlaneMetric pLeft pRight := by
  refine ⟨riemannianDistance_pLeft_pRight, ?_⟩
  rw [riemannianDistance_pLeft_pRight]
  exact no_curve_of_length_two_pLeft_pRight

end PetersenLib

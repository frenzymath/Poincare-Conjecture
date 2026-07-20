import MorganTianLib.Ch02.GeodesicLimits

/-!
# Poincaré Ch. 2, §2.5 — The Busemann pair of a minimizing line

The metric preamble to the Cheeger–Gromoll splitting theorem (blueprint
`lem:minimizing-line-implies-product`): a minimizing geodesic line `γ : ℝ → M` determines
two minimizing geodesic rays `λ₊(t) = γ(t)` and `λ₋(t) = γ(-t)`, hence two Busemann
functions `B₊ = busemann γ` and `B₋ = busemann (fun t => γ (-t))`. Because `γ` is
minimizing on all of `ℝ`,

* `B₊(γ(u)) = -u` for **every** `u ∈ ℝ`, not just `u ≥ 0` (`busemann_apply_line`);
* `B₊ + B₋ ≥ 0` everywhere on `M` (`busemann_add_busemann_neg_nonneg`), by the triangle
  inequality through `dist (γ t) (γ (-s)) = t + s`;
* `B₊ + B₋ = 0` at every point of the line (`busemann_add_busemann_neg_apply_line`).

In the splitting theorem these combine with `Δ B₊ ≤ 0`, `Δ B₋ ≤ 0` (non-negative Ricci
curvature) and the maximum principle to force `B₋ = -B₊` globally, whence `B₊` is
harmonic. The facts in this file are purely metric.

## Design notes

* Rays and lines are total maps `ℝ → M` constrained only on their windows (`Set.Ici 0`,
  `Set.univ`), matching `Busemann.lean` and `GeodesicLimits.lean`; the backward ray of the
  line `γ` is literally `fun t => γ (-t)`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §2.5.
-/

open Set

namespace MorganTianLib

variable {M : Type*} [MetricSpace M]

/-- A minimizing geodesic line is in particular a minimizing geodesic ray. -/
theorem IsMinGeodesicOn.isGeodesicRay {γ : ℝ → M} (hγ : IsMinGeodesicOn γ Set.univ) :
    IsGeodesicRay γ :=
  fun s _ t _ => hγ (mem_univ s) (mem_univ t)

/-- The reversal `t ↦ γ(-t)` of a minimizing geodesic line is again a minimizing
geodesic line. -/
theorem IsMinGeodesicOn.neg_comp {γ : ℝ → M} (hγ : IsMinGeodesicOn γ Set.univ) :
    IsMinGeodesicOn (fun t => γ (-t)) Set.univ := by
  intro s _ t _
  have h := hγ (mem_univ (-s)) (mem_univ (-t))
  rwa [neg_sub_neg, abs_sub_comm] at h

/-- The backward ray `t ↦ γ(-t)` of a minimizing geodesic line is a minimizing geodesic
ray. -/
theorem IsMinGeodesicOn.isGeodesicRay_neg {γ : ℝ → M} (hγ : IsMinGeodesicOn γ Set.univ) :
    IsGeodesicRay (fun t => γ (-t)) :=
  hγ.neg_comp.isGeodesicRay

/-- **The Busemann function along a minimizing line**: `B_γ(γ(u)) = -u` for every real
`u`, extending `busemann_apply_ray` from `u ≥ 0` to all of `ℝ`. For `t ≥ max u 0` the
approximant is exactly `B_{γ,t}(γ(u)) = (t - u) - t = -u`, and no approximant dips below
`-u` since `|t - u| ≥ t - u`. -/
theorem busemann_apply_line {γ : ℝ → M} (hγ : IsMinGeodesicOn γ Set.univ) (u : ℝ) :
    busemann γ (γ u) = -u := by
  apply le_antisymm
  · have ht : (0 : ℝ) ≤ max u 0 := le_max_right u 0
    have haux : busemannAux γ (max u 0) (γ u) = -u := by
      show dist (γ (max u 0)) (γ u) - max u 0 = -u
      rw [hγ (mem_univ _) (mem_univ _)]
      rcases le_total u 0 with hu | hu
      · rw [max_eq_right hu, zero_sub, abs_neg, abs_of_nonpos hu]
        ring
      · rw [max_eq_left hu, sub_self, abs_zero]
        ring
    have h := busemann_le_busemannAux hγ.isGeodesicRay (γ u) ht
    rwa [haux] at h
  · apply le_ciInf
    rintro ⟨t, ht⟩
    show -u ≤ dist (γ t) (γ u) - t
    rw [hγ (mem_univ t) (mem_univ u)]
    have h := le_abs_self (t - u)
    linarith

/-- **The Busemann pair of a minimizing line is non-negative**: if `γ` is a minimizing
geodesic line with forward Busemann function `B₊ = busemann γ` and backward Busemann
function `B₋ = busemann (fun t => γ (-t))`, then `B₊ + B₋ ≥ 0` everywhere. Indeed, for
`s, t ≥ 0` minimality gives `dist (γ t) (γ (-s)) = t + s`, so the triangle inequality
through any `x` yields `B_{γ,t}(x) + B_{γ⁻,s}(x) ≥ 0`; take the infimum over `t`, then
over `s`. -/
theorem busemann_add_busemann_neg_nonneg {γ : ℝ → M} (hγ : IsMinGeodesicOn γ Set.univ)
    (x : M) : 0 ≤ busemann γ x + busemann (fun t => γ (-t)) x := by
  have h : ∀ t : Set.Ici (0 : ℝ), ∀ s : Set.Ici (0 : ℝ),
      0 ≤ busemannAux γ t x + busemannAux (fun r => γ (-r)) s x := by
    rintro ⟨t, ht⟩ ⟨s, hs⟩
    rw [mem_Ici] at ht hs
    show 0 ≤ (dist (γ t) x - t) + (dist (γ (-s)) x - s)
    have hd : dist (γ t) (γ (-s)) = t + s := by
      rw [hγ (mem_univ t) (mem_univ (-s)), sub_neg_eq_add,
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ t + s)]
    have htri : dist (γ t) (γ (-s)) ≤ dist (γ t) x + dist x (γ (-s)) :=
      dist_triangle _ _ _
    rw [hd, dist_comm x (γ (-s))] at htri
    linarith
  have h2 : ∀ t : Set.Ici (0 : ℝ),
      -busemannAux γ t x ≤ busemann (fun r => γ (-r)) x :=
    fun t => le_ciInf fun s => by linarith [h t s]
  have h3 : -busemann (fun r => γ (-r)) x ≤ busemann γ x :=
    le_ciInf fun t => by linarith [h2 t]
  linarith

/-- **The Busemann pair vanishes on its line**: `B₊(γ(u)) + B₋(γ(u)) = 0` for every point
`γ(u)` of a minimizing geodesic line, since `B₊(γ(u)) = -u` and `B₋(γ(u)) = u`. Together
with `busemann_add_busemann_neg_nonneg` this exhibits `-(B₊ + B₋)` as a non-positive
function attaining its maximum `0` on the line — the input to the maximum-principle step
of the splitting theorem. -/
theorem busemann_add_busemann_neg_apply_line {γ : ℝ → M}
    (hγ : IsMinGeodesicOn γ Set.univ) (u : ℝ) :
    busemann γ (γ u) + busemann (fun t => γ (-t)) (γ u) = 0 := by
  have h1 := busemann_apply_line hγ u
  have h2 : busemann (fun t => γ (-t)) (γ u) = u := by
    have h := busemann_apply_line hγ.neg_comp (-u)
    simpa using h
  rw [h1, h2]
  ring

end MorganTianLib

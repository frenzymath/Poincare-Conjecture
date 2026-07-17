import PoincareLib.Ch01.JacobiManifold

/-!
# Poincaré Ch. 1, §1.4 — restriction of a manifold Jacobi field to a subinterval

`IsJacobiFieldAlongOn g γ J DJ a b` is a *local* (sheaf-like) property: at every
`t₀ ∈ [a, b]` the field is, on some relative neighborhood, the chart reading of a
chart Jacobi field. For the composition-chain assembly of
`lem:exponential-differential-jacobi` a *single* manifold Jacobi field along the
whole compact geodesic must be fed piece-by-piece to the within-chart flow-step
transports, one nondegenerate partition piece `[τ_i, τ_{i+1}]` at a time. This
file supplies that restriction.

* `IsJacobiFieldAlongOn.mono` — restrict a manifold Jacobi field from `[a, b]` to
  any nondegenerate subinterval `[a', b'] ⊆ [a, b]`.

The relative neighborhood filters satisfy
`𝓝[Icc a' b'] t₀ = 𝓝[Icc a b] t₀ ⊓ 𝓟 (Icc a' b')` when `Icc a' b' ⊆ Icc a b`,
so the chart witness of the global field, intersected with `[a', b']`, is a valid
witness for the restricted field; the nondegenerate chart interval is carved out
of the ambient open neighborhood exactly as in the difference lemma
`IsJacobiFieldAlongOn.sub`.

Blueprint: `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter Metric
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **Restriction of a manifold Jacobi field to a subinterval.** If
`(J, DJ)` is a manifold Jacobi field along `γ` on `[a, b]`, then it is a manifold
Jacobi field on every nondegenerate subinterval `[a', b'] ⊆ [a, b]`.

Blueprint: `lem:exponential-differential-jacobi`. -/
theorem IsJacobiFieldAlongOn.mono {g : RiemannianMetric I M} {γ : ℝ → M}
    {J DJ : ℝ → E} {a b a' b' : ℝ}
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (ha : a ≤ a') (hab' : a' < b') (hb : b' ≤ b) :
    IsJacobiFieldAlongOn (I := I) g γ J DJ a' b' := by
  intro t₀ ht₀
  have ht₀ab : t₀ ∈ Icc a b := ⟨le_trans ha ht₀.1, le_trans ht₀.2 hb⟩
  obtain ⟨α, a₀, b₀, hab₀, ht₀', hsub₀, hnbhd₀, hsrc₀, hJF₀⟩ := h t₀ ht₀ab
  -- an open set `U ∋ t₀` with `U ∩ [a, b] ⊆ [a₀, b₀]`
  obtain ⟨U, hU, htU, hsU⟩ := mem_nhdsWithin.1 hnbhd₀
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hU t₀ htU
  -- the refined chart interval, centered at `t₀` inside `[a', b']`
  set a₁ : ℝ := max a' (t₀ - δ / 2) with ha₁def
  set b₁ : ℝ := min b' (t₀ + δ / 2) with hb₁def
  have hmemsub : ∀ σ ∈ Icc a₁ b₁, σ ∈ U ∩ Icc a b := by
    intro σ hσ
    have h1 : t₀ - δ / 2 ≤ σ := le_trans (le_max_right _ _) hσ.1
    have h2 : σ ≤ t₀ + δ / 2 := le_trans hσ.2 (min_le_right _ _)
    have hσab : σ ∈ Icc a b :=
      ⟨le_trans ha (le_trans (le_max_left _ _) hσ.1),
        le_trans (le_trans hσ.2 (min_le_left _ _)) hb⟩
    have hmem : σ ∈ Metric.ball t₀ δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have : |σ - t₀| ≤ δ / 2 := abs_le.2 ⟨by linarith, by linarith⟩
      linarith
    exact ⟨hball hmem, hσab⟩
  have hsubab₀ : Icc a₁ b₁ ⊆ Icc a₀ b₀ := fun σ hσ => hsU (hmemsub σ hσ)
  have hab₁ : a₁ < b₁ :=
    max_lt (lt_min hab' (by linarith [ht₀.1, hδ]))
      (lt_min (by linarith [ht₀.2, hδ]) (by linarith [hδ]))
  have ht₀₁ : t₀ ∈ Icc a₁ b₁ :=
    ⟨max_le ht₀.1 (by linarith [hδ]), le_min ht₀.2 (by linarith [hδ])⟩
  have hsuba'b' : Icc a₁ b₁ ⊆ Icc a' b' :=
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  -- the refined interval is a relative neighborhood of `t₀` in `[a', b']`
  have hnbhd₁ : Icc a₁ b₁ ∈ 𝓝[Icc a' b'] t₀ := by
    refine mem_nhdsWithin.2 ⟨Ioo (t₀ - δ / 2) (t₀ + δ / 2), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, fun σ hσ => ?_⟩
    exact ⟨max_le hσ.2.1 hσ.1.1.le, le_min hσ.2.2 hσ.1.2.le⟩
  -- restrict the chart certificate and the chart-source confinement
  refine ⟨α, a₁, b₁, hab₁, ht₀₁, hsuba'b', hnbhd₁, ?_, ?_⟩
  · exact fun τ hτ => hsrc₀ τ (hsubab₀ hτ)
  · exact hJF₀.mono (hsubab₀ (left_mem_Icc.2 hab₁.le)).1
      (hsubab₀ (right_mem_Icc.2 hab₁.le)).2

end PoincareLib

end

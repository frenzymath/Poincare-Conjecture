import DoCarmoLib.Riemannian.Jacobi.JacobiManifold

/-!
# Time reversal of Jacobi fields

The Jacobi/geodesic system is invariant under `t ↦ -t`, provided the
covariant-derivative field flips sign: given a Jacobi pair `(J, DJ)` along a
curve on `[a, b]`, the reversed data
`γ⁻(t) = γ (-t)`, `J⁻(t) = J (-t)`, `DJ⁻(t) = -(DJ (-t))`
is a Jacobi pair along `γ⁻` on `[-b, -a]`.

The sign bookkeeping is entirely local. Under reversal the chart velocity
`u̇` flips sign, so the Christoffel term `Γ(u̇, ·)(u)` — odd in its velocity
slot — flips sign, matching the flip of `J⁻' = -(J' ∘ neg)`. In the second
equation the curvature term `ℛ(J, u̇)u̇` carries `u̇` in **two** slots, so the
two sign flips cancel and the term is unchanged, while the `Γ(u̇, DJ)(u)` term
flips twice (once for `u̇`, once for the `-` sitting on `DJ⁻`) and is likewise
unchanged.

## Contents

* `chartChristoffelContraction_neg_left` — `Γ(-v, w)(y) = -Γ(v, w)(y)`, the
  first-slot oddness (from the slot symmetry plus second-slot homogeneity).
  Complements `Geodesic.chartChristoffelContraction_neg`, which negates
  *both* slots.
* `chartCurvature_neg_middle_right` — `ℛ(y)(X, -v, -v) = ℛ(y)(X, v, v)`: the
  two sign flips of the reversed velocity cancel.
* `IsJacobiFieldOn.comp_neg` — **chart level**: `(J ∘ neg, -(DJ ∘ neg))` is a
  Jacobi pair along `u ∘ neg` on `[-b, -a]`.
* `IsJacobiFieldAlongOn.comp_neg` — **manifold level**: the same statement for
  the chart-local manifold notion, obtained by reflecting each chart
  certificate `[a', b'] ↦ [-b', -a']` and transporting the
  `𝓝[Icc a b]`-membership along the homeomorphism `t ↦ -t`.

The geodesic side of the reversal already exists:
`Riemannian.Geodesic.isGeodesicOn_comp_neg` / `hasGeodesicEquationAt_comp_neg`
(`DoCarmoLib.Riemannian.Geodesic.Equation`).

Blueprint: do Carmo Ch. 5 (Jacobi field infrastructure); consumer
`thm:dc-ch8-2-1` (E. Cartan).
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The Christoffel contraction is odd in its **first** (velocity) slot. -/
theorem chartChristoffelContraction_neg_left (g : RiemannianMetric I M) (α : M)
    (v w y : E) :
    Geodesic.chartChristoffelContraction (I := I) g α (-v) w y
      = -(Geodesic.chartChristoffelContraction (I := I) g α v w y) := by
  rw [Geodesic.chartChristoffelContraction_symm (I := I) g α (-v) w y,
    show (-v : E) = (-1 : ℝ) • v by simp,
    Geodesic.chartChristoffelContraction_smul_right (I := I) g α w (-1 : ℝ) v y,
    Geodesic.chartChristoffelContraction_symm (I := I) g α w v y]
  simp

/-- **Math.** Chart curvature with both the middle and the right slot negated. -/
theorem chartCurvature_neg_middle_right (g : RiemannianMetric I M) (α : M)
    (y X v : E) :
    chartCurvature (I := I) g α y X (-v) (-v)
      = chartCurvature (I := I) g α y X v v := by
  simp only [chartCurvature_def, christoffelCurvature, map_neg,
    ContinuousLinearMap.neg_apply, neg_neg]

theorem IsJacobiFieldOn.comp_neg {g : RiemannianMetric I M} {α : M}
    {u J DJ : ℝ → E} {a b : ℝ}
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b) :
    IsJacobiFieldOn (I := I) g α (fun t => u (-t)) (fun t => J (-t))
      (fun t => -(DJ (-t))) (-b) (-a) := by
  have hmaps : MapsTo (fun t : ℝ => -t) (Icc (-b) (-a)) (Icc a b) := by
    intro t ht
    simp only [mem_Icc] at ht ⊢
    constructor <;> linarith [ht.1, ht.2]
  have hderiv : ∀ t : ℝ, deriv (fun s => u (-s)) t = -(deriv u (-t)) :=
    fun t => deriv_comp_neg u t
  constructor
  · intro t ht
    have hmem : -t ∈ Icc a b := hmaps ht
    have hbase := h.hasDerivWithinAt_fst (-t) hmem
    have hneg : HasDerivWithinAt (fun s : ℝ => -s) (-1 : ℝ) (Icc (-b) (-a)) t :=
      (hasDerivAt_neg t).hasDerivWithinAt
    have hcomp := hbase.scomp t hneg hmaps
    simp only [Function.comp_def] at hcomp
    have hval : ((-1 : ℝ) • (DJ (-t) - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u (-t)) (J (-t)) (u (-t))))
        = -(DJ (-t)) - Geodesic.chartChristoffelContraction (I := I) g α
            (-(deriv u (-t))) (J (-t)) (u (-t)) := by
      rw [chartChristoffelContraction_neg_left (I := I) g α (deriv u (-t)) (J (-t)) (u (-t))]
      simp only [neg_one_smul, neg_sub]
      abel
    rw [hval] at hcomp
    simpa only [hderiv] using hcomp
  · intro t ht
    have hmem : -t ∈ Icc a b := hmaps ht
    have hbase := h.hasDerivWithinAt_snd (-t) hmem
    have hneg : HasDerivWithinAt (fun s : ℝ => -s) (-1 : ℝ) (Icc (-b) (-a)) t :=
      (hasDerivAt_neg t).hasDerivWithinAt
    have hcomp := (hbase.scomp t hneg hmaps).neg
    simp only [Function.comp_def] at hcomp
    have hval : -((-1 : ℝ) •
          (-(chartCurvature (I := I) g α (u (-t)) (J (-t)) (deriv u (-t)) (deriv u (-t)))
            - Geodesic.chartChristoffelContraction (I := I) g α
              (deriv u (-t)) (DJ (-t)) (u (-t))))
        = -(chartCurvature (I := I) g α (u (-t)) (J (-t))
              (-(deriv u (-t))) (-(deriv u (-t))))
            - Geodesic.chartChristoffelContraction (I := I) g α
              (-(deriv u (-t))) (-(DJ (-t))) (u (-t)) := by
      rw [chartCurvature_neg_middle_right (I := I) g α (u (-t)) (J (-t)) (deriv u (-t)),
        chartChristoffelContraction_neg_left (I := I) g α (deriv u (-t)) (-(DJ (-t))) (u (-t)),
        show (-(DJ (-t)) : E) = (-1 : ℝ) • DJ (-t) by simp,
        Geodesic.chartChristoffelContraction_smul_right (I := I) g α
          (deriv u (-t)) (-1 : ℝ) (DJ (-t)) (u (-t))]
      simp only [neg_one_smul, neg_neg, neg_sub]
    rw [hval] at hcomp
    simpa only [hderiv] using hcomp

theorem IsJacobiFieldAlongOn.comp_neg {g : RiemannianMetric I M} {γ : ℝ → M}
    {J DJ : ℝ → E} {a b : ℝ}
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ a b) :
    IsJacobiFieldAlongOn (I := I) g (fun t => γ (-t)) (fun t => J (-t))
      (fun t => -(DJ (-t))) (-b) (-a) := by
  intro t₀ ht₀
  have ht₀' : -t₀ ∈ Icc a b := by
    simp only [mem_Icc] at ht₀ ⊢
    constructor <;> linarith [ht₀.1, ht₀.2]
  obtain ⟨α, a', b', hab', hmem', hsub', hnhds', hchart', hjac'⟩ := h (-t₀) ht₀'
  have hpre : ∀ c d : ℝ, (fun t : ℝ => -t) ⁻¹' (Icc c d) = Icc (-d) (-c) := by
    intro c d
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor <;> (intro hx; exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩)
  refine ⟨α, -b', -a', by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mem_Icc] at hmem' ⊢
    constructor <;> linarith [hmem'.1, hmem'.2]
  · intro t ht
    simp only [mem_Icc] at ht ⊢
    have : -t ∈ Icc a' b' := by simp only [mem_Icc]; constructor <;> linarith [ht.1, ht.2]
    have := hsub' this
    simp only [mem_Icc] at this
    constructor <;> linarith [this.1, this.2]
  · -- neighbourhood transfer along the homeomorphism `t ↦ -t`
    have htend : Tendsto (fun t : ℝ => -t) (𝓝[Icc (-b) (-a)] t₀) (𝓝[Icc a b] (-t₀)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_neg.tendsto t₀).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [mem_Icc] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    have hmap := htend hnhds'
    rw [Filter.mem_map, hpre a' b'] at hmap
    exact hmap
  · intro τ hτ
    refine hchart' (-τ) ?_
    simp only [mem_Icc] at hτ ⊢
    constructor <;> linarith [hτ.1, hτ.2]
  · have hJ : chartVectorRep (I := I) (fun t => γ (-t)) α (fun t => J (-t))
        = fun t => chartVectorRep (I := I) γ α J (-t) := rfl
    have hDJ : chartVectorRep (I := I) (fun t => γ (-t)) α (fun t => -(DJ (-t)))
        = fun t => -(chartVectorRep (I := I) γ α DJ (-t)) := by
      funext t
      simp only [chartVectorRep_apply, map_neg]
    rw [hJ, hDJ]
    exact hjac'.comp_neg

end Riemannian.Jacobi

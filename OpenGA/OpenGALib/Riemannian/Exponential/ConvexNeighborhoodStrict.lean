import OpenGALib.Riemannian.Exponential.ConvexNeighborhoodAssembly

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

/-!
# Strict form of `lem:dc-ch3-4-1` (do Carmo Ch. 3, §4)

`ConvexNeighborhoodAssembly.lean` closes `lem:dc-ch3-4-1` with the **non-strict** conclusion
`F 0 ≤ F s` (a local minimum): a geodesic tangent to the geodesic sphere `S_r(p)` does not
re-enter the open ball `B_r(p)`. do Carmo's proof of the **convex neighborhood** proposition
(`prop:dc-ch3-4-2`) needs a *strict* separation: at the point where the distance from `p` to the
joining geodesic attains its interior maximum, the tangent geodesic must lie **strictly** outside
`B_r(p)` for `s ≠ 0`, which contradicts that maximum. This file supplies that upgrade.

The analytic heart is the **strict second-derivative test**
(`eventually_lt_of_deriv_deriv_pos`): a curve `F` with `F'(0) = 0` and `F''(0) > 0` satisfies
`F 0 < F s` for **every** `s ≠ 0` near `0` (a strict punctured minimum), not merely `F 0 ≤ F s`.
It is built from the mathlib sign-of-derivative machinery
(`eventually_nhdsWithin_sign_eq_of_deriv_pos`): `F'` is `> 0` just to the right of `0` and `< 0`
just to the left, so `F` is strictly increasing on the right and strictly decreasing on the left,
hence `F 0 < F s` on both punctured sides.

Feeding this into the exact assembly of `exists_forall_geodesic_tangent_stays_outside_ball`
(the Gauss-lemma tangency `∂F/∂t(0) = 0`, the strict positivity of `∂²F/∂t²(0, q, v)` from
`exists_secondDerivChartForm_pos_nhds_ne`, and the F-identity
`hasDerivAt_and_deriv_deriv_sqNorm_flowReading`) yields the strict statement
`exists_forall_geodesic_tangent_stays_strictly_outside_ball`.
-/

noncomputable section

open Bundle Manifold Set Filter Function Metric SignType
open scoped Manifold Topology ContDiff NNReal

namespace Riemannian

/-- **Math.** **The strict second-derivative test.** A curve `F : ℝ → ℝ` with `F'(0) = 0`,
`F''(0) > 0` and continuous at `0` has a **strict punctured minimum** at `0`:
`F 0 < F s` for every `s ≠ 0` near `0`. This strengthens `eventually_ge_of_deriv_deriv_pos`
(which gives only `F 0 ≤ F s`) and is the strict separation do Carmo's convex-neighborhood
argument needs. Proof: by `eventually_nhdsWithin_sign_eq_of_deriv_pos` the sign of `deriv F s`
matches the sign of `s` near `0`, so `deriv F > 0` on a right interval `(0, c)` and
`deriv F < 0` on a left interval `(a, 0)`; `strictMonoOn_of_deriv_pos` /
`strictAntiOn_of_deriv_neg` then give `F 0 < F s` on each punctured side. -/
theorem eventually_lt_of_deriv_deriv_pos {F : ℝ → ℝ}
    (hF'' : deriv (deriv F) 0 > 0) (hF' : deriv F 0 = 0) (hFc : ContinuousAt F 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℝ), F 0 < F s := by
  -- sign of `deriv F` near `0` matches the sign of `s`
  have hsign : ∀ᶠ x in 𝓝 (0 : ℝ), sign (deriv F x) = sign (x - 0) :=
    eventually_nhdsWithin_sign_eq_of_deriv_pos hF'' hF'
  have hsignNE : ∀ᶠ x in 𝓝[≠] (0 : ℝ), sign (deriv F x) = sign (x - 0) :=
    nhdsWithin_le_nhds hsign
  have hposR : ∀ᶠ b in 𝓝[>] (0 : ℝ), deriv F b > 0 :=
    deriv_pos_right_of_sign_deriv hsignNE
  have hnegL : ∀ᶠ b in 𝓝[<] (0 : ℝ), deriv F b < 0 :=
    deriv_neg_left_of_sign_deriv hsignNE
  -- right side: `F` is strictly increasing
  have hright : ∀ᶠ s in 𝓝[>] (0 : ℝ), F 0 < F s := by
    obtain ⟨c, hc0, hc⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp hposR
    have hderivpos : ∀ x ∈ Ioo (0 : ℝ) c, 0 < deriv F x := fun x hx => hc hx
    have hcont : ContinuousOn F (Ico (0 : ℝ) c) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with h | h
      · subst h; exact hFc.continuousWithinAt
      · exact (differentiableAt_of_deriv_ne_zero
          (ne_of_gt (hderivpos x ⟨h, hx.2⟩))).continuousAt.continuousWithinAt
    have hmono : StrictMonoOn F (Ico (0 : ℝ) c) := by
      apply strictMonoOn_of_deriv_pos (convex_Ico 0 c) hcont
      rw [interior_Ico]; exact hderivpos
    filter_upwards [Ioo_mem_nhdsGT hc0] with s hs
    exact hmono ⟨le_refl 0, hc0⟩ ⟨hs.1.le, hs.2⟩ hs.1
  -- left side: `F` is strictly decreasing
  have hleft : ∀ᶠ s in 𝓝[<] (0 : ℝ), F 0 < F s := by
    obtain ⟨a, ha0, ha⟩ := (nhdsLT_basis (0 : ℝ)).eventually_iff.mp hnegL
    have hderivneg : ∀ x ∈ Ioo a (0 : ℝ), deriv F x < 0 := fun x hx => ha hx
    have hcont : ContinuousOn F (Ioc a (0 : ℝ)) := by
      intro x hx
      rcases eq_or_lt_of_le hx.2 with h | h
      · rw [h]; exact hFc.continuousWithinAt
      · exact (differentiableAt_of_deriv_ne_zero
          (ne_of_lt (hderivneg x ⟨hx.1, h⟩))).continuousAt.continuousWithinAt
    have hanti : StrictAntiOn F (Ioc a (0 : ℝ)) := by
      apply strictAntiOn_of_deriv_neg (convex_Ioc a 0) hcont
      rw [interior_Ioc]; exact hderivneg
    filter_upwards [Ioo_mem_nhdsLT ha0] with s hs
    exact hanti ⟨hs.1, hs.2.le⟩ ⟨ha0, le_refl 0⟩ hs.2
  rw [← nhdsLT_sup_nhdsGT, eventually_sup]
  exact ⟨hleft, hright⟩

namespace Exponential

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [T2Space (TangentBundle I M)]

/-- **Math.** **do Carmo Ch. 3, §4, Lemma 4.1 — strict form.** Identical data to
`exists_forall_geodesic_tangent_stays_outside_ball`, but with the **strict** separation
`F 0 < F s` for every `s ≠ 0` near `0`: a geodesic tangent (`∂F/∂t(0) = 0`, the Gauss lemma) to
the geodesic sphere `S_r(p)` stays **strictly** outside the open ball `B_r(p)` in a punctured
neighborhood of its base point. This is the form do Carmo's convex-neighborhood proof
(`prop:dc-ch3-4-2`) consumes: if the distance from `p` to a joining geodesic attained an interior
maximum, the strict inequality here would contradict it. The proof is the assembly of
`exists_forall_geodesic_tangent_stays_outside_ball` with the strict second-derivative test
`eventually_lt_of_deriv_deriv_pos` in place of the non-strict `eventually_ge_of_deriv_deriv_pos`. -/
theorem exists_forall_geodesic_tangent_stays_strictly_outside_ball [T2Space M]
    (g : RiemannianMetric I M) (p : M) :
    ∃ (finv : E → E) (V : Set E) (r ε T : ℝ) (Z : E × E → ℝ → E × E),
      IsOpen V ∧ extChartAt I p p ∈ V ∧ V ⊆ (extChartAt I p).target ∧
      finv (extChartAt I p p) = 0 ∧
      0 < r ∧ 0 < ε ∧ 0 < T ∧ T < ε ∧
      (∀ z ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r,
        Z z 0 = z ∧
        (∀ t ∈ Icc (-ε) ε, HasDerivWithinAt (Z z)
          (geodesicSprayCoord (I := I) g p (Z z t).1 (Z z t).2) (Icc (-ε) ε) t) ∧
        (∀ t ∈ Icc (-ε) ε, Z z t ∈ (extChartAt I p).target ×ˢ (univ : Set E))) ∧
      (∃ εL : ℝ, 0 < εL ∧ ∀ w : E, ‖w‖ < εL →
        finv (extChartAt I p (expMap (I := I) g p (w : TangentSpace I p))) = w) ∧
      ∀ (y w : E), y ∈ V → w ≠ 0 →
        ((y, T⁻¹ • w) : E × E) ∈ closedBall ((extChartAt I p p, (0 : E)) : E × E) r →
        deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
            (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
              ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
            (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
              ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))) 0 = 0 →
        ∀ᶠ s in 𝓝[≠] (0 : ℝ),
          chartMetricInner (I := I) g p (extChartAt I p p)
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) 0))
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) 0))
            < chartMetricInner (I := I) g p (extChartAt I p p)
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
              (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
                ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s)) := by
  obtain ⟨finv, V, hVopen, hpV, hVsub, hf0, hfinvC2, hpos, hleftinv⟩ :=
    exists_secondDerivChartForm_pos_nhds_ne (I := I) g p
  obtain ⟨r, ε, T, Z, hr, hε, hT, hTε, hflow, _, _⟩ :=
    exists_pairMap_hasStrictFDerivAt (I := I) g p
  refine ⟨finv, V, r, ε, T, Z, hVopen, hpV, hVsub, hf0, hr, hε, hT, hTε, hflow,
    hleftinv, ?_⟩
  intro y w hyV hwne hmem htang
  obtain ⟨hF', hF''⟩ :=
    hasDerivAt_and_deriv_deriv_sqNorm_flowReading (I := I) g p hT hTε hflow hVopen hfinvC2 hyV hmem
  have hF''pos : deriv (deriv (fun s : ℝ => chartMetricInner (I := I) g p (extChartAt I p p)
      (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s))
      (finv ((fun σ : ℝ => extChartAt I p ((extChartAt I p).symm
        ((Z ((y, T⁻¹ • w) : E × E) (σ * T)).1))) s)))) 0 > 0 := by
    rw [hF'']; exact hpos y hyV w hwne
  exact eventually_lt_of_deriv_deriv_pos hF''pos htang hF'.continuousAt

end Exponential

end Riemannian

end

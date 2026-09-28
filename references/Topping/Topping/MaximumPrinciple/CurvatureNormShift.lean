import Topping.RicciFlow.CurvatureNormVariation

/-!
# Curvature bounds on a shifted time interval

Topping's curvature comparison is stated on an interval starting at zero.  This
file transports that estimate through the affine time map `s \mapsto a + s`.
The resulting bound on `[a,b]` is expressed in terms of the elapsed time
`t - a` and the curvature bound at the anchor time `a`.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private theorem const_add_mem_Icc {a b s : ℝ} (hs : s ∈ Icc 0 (b - a)) :
    a + s ∈ Icc a b := by
  constructor <;> linarith [hs.1, hs.2]

private theorem hasDerivWithinAt_comp_const_add_Icc
    {f : ℝ → ℝ} {f' a b s : ℝ}
    (hf : HasDerivWithinAt f f' (Icc a b) (a + s)) :
    HasDerivWithinAt (fun u => f (a + u)) f' (Icc 0 (b - a)) s := by
  have hshift : HasDerivWithinAt (fun u : ℝ => a + u) 1 (Icc 0 (b - a)) s :=
    ((hasDerivAt_id s).const_add a).hasDerivWithinAt
  have hmaps : MapsTo (fun u : ℝ => a + u) (Icc 0 (b - a)) (Icc a b) := by
    intro u hu
    exact const_add_mem_Icc hu
  have hcomp := hf.comp s hshift hmaps
  convert hcomp using 1
  all_goals try rfl
  all_goals try simp [mul_one]

/-- **Math.** The uniform curvature comparison on `[0,T]` is invariant under
translation of time.  Thus, if the norm-square evolution ingredients hold on
`[a,b]`, the curvature at time `t` is bounded by the comparison solution based
at `a`, with elapsed time `t-a`.

The joint `ContinuousOn` hypothesis and the derivative hypothesis are stated on
the original space-time cylinder; the proof transports both through
`(p,s) \mapsto (p,a+s)` rather than assuming regularity of a new family.
-/
theorem exists_uniform_riemannNormAt_le_on_Icc_of_ingredients [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (m a b : ℝ),
        a < b → 0 < m →
        ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
          ((Set.univ : Set M) ×ˢ Icc a b) →
        (∀ p t, t ∈ Icc a b →
          HasDerivWithinAt (fun s => riemannNormAt (g s) p ^ 2)
            (derivWithin (fun s => riemannNormAt (g s) p ^ 2) (Icc a b) t)
            (Icc a b) t) →
        HasCurvatureNormSqNamedPairingBoundOn g (Icc a b) →
        (∀ t ∈ Icc a b, 0 < 1 - c * m * (t - a) / 2) →
        (∀ p, riemannNormAt (g a) p ≤ m) →
        ∀ p t, t ∈ Icc a b →
          riemannNormAt (g t) p ≤ m / (1 - c * m * (t - a) / 2) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_riemannNormAt_le_of_ingredients (I := I) (M := M)
  refine ⟨c, hc, fun g m a b hab hm hcont hderiv hpair hdenom ha => ?_⟩
  let ghat : ℝ → RiemannianMetric I M := fun s => g (a + s)
  have hdelta : 0 ≤ b - a := le_of_lt (sub_pos.mpr hab)
  have hcont' :
      ContinuousOn (fun z : M × ℝ => riemannNormAt (ghat z.2) z.1 ^ 2)
        ((Set.univ : Set M) ×ˢ Icc 0 (b - a)) := by
    have htime : Continuous (fun z : M × ℝ => a + z.2) :=
      continuous_const.add continuous_snd
    have hmap : Continuous (fun z : M × ℝ => (z.1, a + z.2)) :=
      continuous_fst.prodMk htime
    have hmaps : MapsTo (fun z : M × ℝ => (z.1, a + z.2))
        ((Set.univ : Set M) ×ˢ Icc 0 (b - a))
        ((Set.univ : Set M) ×ˢ Icc a b) := by
      rintro z ⟨hz, hs⟩
      exact ⟨hz, const_add_mem_Icc hs⟩
    simpa only [ghat] using hcont.comp' hmap.continuousOn hmaps
  have hderiv' : ∀ p s, s ∈ Icc 0 (b - a) →
      HasDerivWithinAt (fun u => riemannNormAt (ghat u) p ^ 2)
        (derivWithin (fun u => riemannNormAt (ghat u) p ^ 2)
          (Icc 0 (b - a)) s)
        (Icc 0 (b - a)) s := by
    intro p s hs
    have horig := hderiv p (a + s) (const_add_mem_Icc hs)
    have hcomp := hasDerivWithinAt_comp_const_add_Icc horig
    have hu : UniqueDiffWithinAt ℝ (Icc 0 (b - a)) s :=
      uniqueDiffOn_Icc (sub_pos.mpr hab) s hs
    have hcomp' := hcomp.congr_deriv (hcomp.derivWithin hu).symm
    simpa only [ghat] using hcomp'
  have hpair' :
      HasCurvatureNormSqNamedPairingBoundOn ghat (Icc 0 (b - a)) := by
    intro s hs p
    have horig := hderiv p (a + s) (const_add_mem_Icc hs)
    have hcomp := hasDerivWithinAt_comp_const_add_Icc horig
    have hu : UniqueDiffWithinAt ℝ (Icc 0 (b - a)) s :=
      uniqueDiffOn_Icc (sub_pos.mpr hab) s hs
    have hderiv_eq := hcomp.derivWithin hu
    simpa only [ghat, hderiv_eq] using hpair (a + s) (const_add_mem_Icc hs) p
  have hdenom' : ∀ s ∈ Icc 0 (b - a), 0 < 1 - c * m * s / 2 := by
    intro s hs
    simpa only [add_sub_cancel_left] using
      hdenom (a + s) (const_add_mem_Icc hs)
  have ha' : ∀ p, riemannNormAt (ghat 0) p ≤ m := by
    simpa only [ghat, add_zero] using ha
  intro p t ht
  have ht' : t - a ∈ Icc 0 (b - a) := by
    constructor <;> linarith [ht.1, ht.2]
  have htime : a + (t - a) = t := by ring
  simpa only [ghat, htime] using
    hbound ghat m (b - a) hdelta hm hcont' hderiv' hpair' hdenom' ha'
      p (t - a) ht'

/-- **Math.** A Ricci flow with the component curvature evolution equation on
`[a,b]` satisfies the shifted curvature comparison.  Nondegeneracy of the
interval supplies derivative uniqueness at both endpoints, so no separate
`UniqueDiffWithinAt` premise is exposed.
-/
theorem exists_uniform_riemannNormAt_le_on_Icc_of_components [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (m a b : ℝ),
        a < b → 0 < m →
        ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
          ((Set.univ : Set M) ×ˢ Icc a b) →
        IsRicciFlowOn g (Icc a b) →
        HasCurvatureEvolutionComponentsOn g (Icc a b) →
        (∀ t ∈ Icc a b, 0 < 1 - c * m * (t - a) / 2) →
        (∀ p, riemannNormAt (g a) p ≤ m) →
        ∀ p t, t ∈ Icc a b →
          riemannNormAt (g t) p ≤ m / (1 - c * m * (t - a) / 2) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_riemannNormAt_le_on_Icc_of_ingredients (I := I) (M := M)
  refine ⟨c, hc, fun g m a b hab hm hcont hflow hcurv hdenom ha => ?_⟩
  refine hbound g m a b hab hm hcont ?_ ?_ hdenom ha
  · intro p t ht
    have h := hasDerivWithinAt_riemannNormSq_namedPairing_of_components
      hflow hcurv ht p
    exact h.congr_deriv (h.derivWithin (uniqueDiffOn_Icc hab t ht)).symm
  · exact hasCurvatureNormSqNamedPairingBoundOn_of_isRicciFlowOn_of_components
      hflow hcurv (fun t ht => uniqueDiffOn_Icc hab t ht)

/-- **Math.** If a genuine Morgan--Tian Ricci flow is defined on an ambient
time set containing `[a,b]`, then the curvature at time `t \in [a,b]` is
controlled by its curvature at `a` and the elapsed time `t-a`.

The constant is chosen before the flow and the interval, hence depends only on
the dimension.  The positive-denominator hypothesis is the genuine lifespan
restriction of the comparison ODE.
-/
theorem
    exists_uniform_riemannNormAt_le_on_Icc_of_morganTian_isRicciFlowOn_of_subset
    [CompactSpace M] :
    ∃ c : ℝ, 0 ≤ c ∧
      ∀ (g : ℝ → RiemannianMetric I M) (J : Set ℝ) (m a b : ℝ),
        a < b → 0 < m →
        ContinuousOn (fun z : M × ℝ => riemannNormAt (g z.2) z.1 ^ 2)
          ((Set.univ : Set M) ×ˢ Icc a b) →
        MorganTianLib.IsRicciFlowOn g J →
        Icc a b ⊆ J →
        (∀ t ∈ Icc a b, 0 < 1 - c * m * (t - a) / 2) →
        (∀ p, riemannNormAt (g a) p ≤ m) →
        ∀ p t, t ∈ Icc a b →
          riemannNormAt (g t) p ≤ m / (1 - c * m * (t - a) / 2) := by
  obtain ⟨c, hc, hbound⟩ :=
    exists_uniform_riemannNormAt_le_on_Icc_of_components (I := I) (M := M)
  refine ⟨c, hc, fun g J m a b hab hm hcont hflow hIcc hdenom ha => ?_⟩
  exact hbound g m a b hab hm hcont
    (isRicciFlowOn_of_morganTian_isRicciFlowOn_of_subset hflow hIcc)
    (hasCurvatureEvolutionComponentsOn_of_isRicciFlowOn_of_subset hflow hIcc)
    hdenom ha

#print axioms Topping.exists_uniform_riemannNormAt_le_on_Icc_of_ingredients
#print axioms Topping.exists_uniform_riemannNormAt_le_on_Icc_of_components
#print axioms
  Topping.exists_uniform_riemannNormAt_le_on_Icc_of_morganTian_isRicciFlowOn_of_subset

end Topping

end

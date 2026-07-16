import OpenGALib.Riemannian.Manifold.ExpandingMap

/-!
# Relatively compact lifts under a metric-expanding map (do Carmo Ch. 7, §3, Lemma 3.3, compactness core)

do Carmo's proof that a local diffeomorphism `f : M → N` out of a *complete*
manifold with `|df_p(v)| ≥ |v|` everywhere is a covering map (Lemma 3.3) rests on
two independent ingredients:

* the **metric estimate** (`ExpandingMap.lean`), `d(c̄(t), c̄(a)) ≤ ℓ(f∘c̄)`, and
* the **compactness** it buys: because `M` is complete it is *proper*
  (Hopf–Rinow), so the lifted points `c̄(t_n)` — which the estimate keeps inside
  a metric ball of radius `ℓ(f∘c̄) < ∞` — stay inside a **compact** set, and
  therefore have an accumulation point.

This file isolates the second ingredient. Given the landed edist estimate
`DCExpandsMetric.riemannianEDist_le_pathELength_comp` and the standing
Riemannian-distance compatibility `IsRiemannianDist` (`edist = riemannianEDist`),
it produces the real-distance bound

  `dist (c̄ a) (c̄ t) ≤ (ℓ(f∘c̄)).toReal`

for every `t ∈ [a,b]` (with the image length `ℓ(f∘c̄)` assumed finite — automatic
for the `C¹` base curve `c = f∘c̄` do Carmo lifts), hence

  `c̄ t ∈ closedBall (c̄ a) (ℓ(f∘c̄)).toReal`,

a set that is **compact** whenever `M` is a proper metric space (`ProperSpace M`,
the Hopf–Rinow conclusion for a complete Riemannian manifold). This is exactly
do Carmo's sentence *"the sequence `{c̄(t_n)}` is contained in a compact set
`K ⊂ M` … [otherwise] the length of `c` between `0` and `t₀` would be arbitrarily
large, which is absurd."*

Reference: do Carmo, *Riemannian Geometry*, Ch. 7 §3, proof of Lemma 3.3.
-/

open Bundle Manifold MeasureTheory Set Metric
open scoped Manifold Topology ContDiff ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']

/-- **Math.** **Real-distance form of the displayed estimate** (do Carmo Ch. 7,
Lemma 3.3 proof). Let `f : M → M'` expand the metric, let `gM` be the Riemannian
distance of the metric space `M` (`IsRiemannianDist`, i.e. `edist = riemannianEDist`),
and let `c : [a,b] → M` be a `C¹` curve whose image `f ∘ c` has finite length.
Then for every `t ∈ [a,b]` the *source* distance from the start point is bounded
by the length of the image curve:
`dist (c a) (c t) ≤ (ℓ(f∘c))_ℝ`.
Proof: `edist (c a) (c t) = riemannianEDist (c a) (c t)` (`IsRiemannianDist`),
`≤ ℓ(f∘c) a t` (`riemannianEDist_le_pathELength_comp`) `≤ ℓ(f∘c) a b`
(`pathELength_mono`); pass to `.toReal` (both sides finite). -/
theorem DCExpandsMetric.dist_le_pathELength_comp
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : MDifferentiable I I' f) {c : ℝ → M} {a b t : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hL : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
            ⟨gN.toRiemannianMetric⟩
          Manifold.pathELength I' (f ∘ c) a b ≠ ⊤)
    (ht : t ∈ Icc a b) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    dist (c a) (c t) ≤ (Manifold.pathELength I' (f ∘ c) a b).toReal := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨gM.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  -- the Riemannian-distance compatibility of `gM`
  have hRM : IsRiemannianManifold I M := hgM
  -- estimate on the sub-interval `[a, t]`
  have hct : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a t) := hc.mono (Icc_subset_Icc le_rfl ht.2)
  have hstep : Manifold.riemannianEDist I (c a) (c t)
      ≤ Manifold.pathELength I' (f ∘ c) a t :=
    hexp.riemannianEDist_le_pathELength_comp hf hct ht.1
  -- monotonicity of length in the right endpoint
  have hmono : Manifold.pathELength I' (f ∘ c) a t
      ≤ Manifold.pathELength I' (f ∘ c) a b :=
    Manifold.pathELength_mono le_rfl ht.2
  -- combine and translate to `edist`
  have hedist : edist (c a) (c t) ≤ Manifold.pathELength I' (f ∘ c) a b := by
    rw [hRM.out]
    exact hstep.trans hmono
  have hfin : edist (c a) (c t) ≠ ⊤ := (hedist.trans_lt hL.lt_top).ne
  rw [dist_edist]
  exact (ENNReal.toReal_le_toReal hfin hL).mpr hedist

/-- **Math.** **The lifted point lies in a fixed closed ball** (do Carmo Ch. 7,
Lemma 3.3 proof). Under the hypotheses of `dist_le_pathELength_comp`, every value
`c t` (`t ∈ [a,b]`) of a `C¹` lift-candidate `c` sits inside the metric closed
ball around the start point `c a` of radius `(ℓ(f∘c))_ℝ`. -/
theorem DCExpandsMetric.lift_mem_closedBall
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : MDifferentiable I I' f) {c : ℝ → M} {a b t : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hL : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
            ⟨gN.toRiemannianMetric⟩
          Manifold.pathELength I' (f ∘ c) a b ≠ ⊤)
    (ht : t ∈ Icc a b) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    c t ∈ Metric.closedBall (c a) (Manifold.pathELength I' (f ∘ c) a b).toReal := by
  rw [Metric.mem_closedBall, dist_comm]
  exact hexp.dist_le_pathELength_comp hgM hf hc hL ht

/-- **Math.** **The lift stays in a compact set** (do Carmo Ch. 7, Lemma 3.3
proof: *"the sequence `{c̄(t_n)}` is contained in a compact set `K ⊂ M`"*).
Because `M` is proper — the Hopf–Rinow conclusion for a complete Riemannian
manifold, `properSpace_of_forall_geodesic` — the closed ball that
`lift_mem_closedBall` traps the lift inside is compact. Hence the entire image
`c '' (Icc a b)` of a `C¹` lift-candidate of finite image length is contained in
a single compact set. This is precisely the boundedness that, in the covering-map
argument, forces an accumulation point of the lifted sequence. -/
theorem DCExpandsMetric.lift_image_subset_isCompact [ProperSpace M]
    {gM : RiemannianMetric I M} {gN : RiemannianMetric I' M'} {f : M → M'}
    (hexp : DCExpandsMetric gM gN f) (hgM : gM.IsRiemannianDist)
    (hf : MDifferentiable I I' f) {c : ℝ → M} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b))
    (hL : letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
            ⟨gN.toRiemannianMetric⟩
          Manifold.pathELength I' (f ∘ c) a b ≠ ⊤) :
    letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
      ⟨gN.toRiemannianMetric⟩
    ∃ K : Set M, IsCompact K ∧ c '' (Icc a b) ⊆ K := by
  letI : Bundle.RiemannianBundle (fun x : M' ↦ TangentSpace I' x) :=
    ⟨gN.toRiemannianMetric⟩
  refine ⟨Metric.closedBall (c a) (Manifold.pathELength I' (f ∘ c) a b).toReal,
    isCompact_closedBall _ _, ?_⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hexp.lift_mem_closedBall hgM hf hc hL ht

/-! ### Local liftability of a curve through a local homeomorphism

The second ingredient of do Carmo's Lemma 3.3 proof is purely topological: because
`f` is a local diffeomorphism (in particular a local homeomorphism) at a point `e`
lying over `c(s)`, the curve `c` lifts through `e` on a small interval to the right
of `s`. This is the sentence *"since `f` is a local diffeomorphism at `q`, there
exists `ε > 0` such that it is possible to define `c̄ : [0,ε] → M` with `c̄(0) = q`
and `f ∘ c̄ = c`."* It also provides the openness that keeps the set of liftable
parameters open to the right. -/

/-- **Math.** **Local rightward lift through a local homeomorphism** (do Carmo Ch. 7,
Lemma 3.3 proof). If `f : M → N` is a local homeomorphism, `c` is a continuous curve
in `N`, and `e` is a point of `M` lying over `c(s)` (`f e = c s`), then `c` lifts
through `e` on a nondegenerate interval `[s, s+δ]`: there is a continuous
`g : [s, s+δ] → M` with `g s = e` and `f ∘ g = c` on `[s, s+δ]`. Proof: choose an
open partial homeomorphism `φ` of `f` around `e`; then `c(s) = f(e) = φ(e)` is an
interior point of `φ.target`, so `c⁻¹(φ.target)` is an open neighbourhood of `s`
containing some `[s, s+δ]`, and `g := φ⁻¹ ∘ c` is the required lift there. -/
theorem IsLocalHomeomorph.exists_rightward_lift {f : M → M'} (hf : IsLocalHomeomorph f)
    {c : ℝ → M'} (hc : Continuous c) {s : ℝ} {e : M} (he : f e = c s) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℝ → M, g s = e ∧ ContinuousOn g (Icc s (s + δ)) ∧
      ∀ t ∈ Icc s (s + δ), f (g t) = c t := by
  obtain ⟨φ, he_src, rfl⟩ := hf e
  -- `c s = φ e` is an interior point of `φ.target`
  have hsU : c s ∈ φ.target := he ▸ φ.map_source he_src
  have hUopen : IsOpen (c ⁻¹' φ.target) := φ.open_target.preimage hc
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hsU)
  -- on `[s, s+δ/2]` the curve stays inside `φ.target`
  have hmaps : MapsTo c (Icc s (s + δ / 2)) φ.target := by
    intro t ht
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  refine ⟨δ / 2, half_pos hδ, φ.symm ∘ c, ?_, ?_, ?_⟩
  · show φ.symm (c s) = e
    rw [← he, φ.left_inv he_src]
  · exact φ.continuousOn_symm.comp hc.continuousOn hmaps
  · intro t ht
    show φ (φ.symm (c t)) = c t
    exact φ.right_inv (hmaps ht)

/-- **Math.** **The set of liftable parameters is open to the right** (do Carmo
Ch. 7, Lemma 3.3 proof: *"the set `A ⊂ [0,1]` of values such that `c` can be
lifted on `A` starting from `q` is an open interval on the right"*). If `f` is a
local homeomorphism, `c` is continuous, and `c` already lifts to a continuous
`g₀ : [a,t] → M` (`f ∘ g₀ = c` there), then the lift extends to `[a, t+δ]` for
some `δ>0`: there is a continuous `g` on `[a,t+δ]` agreeing with `g₀` on `[a,t]`
with `f ∘ g = c` throughout. Proof: lift `c` rightward through the endpoint value
`g₀(t)` (`exists_rightward_lift`) and glue the two continuous lifts at `t`, where
they agree. -/
theorem IsLocalHomeomorph.exists_extend_lift {f : M → M'} (hf : IsLocalHomeomorph f)
    {c : ℝ → M'} (hc : Continuous c) {a t : ℝ} (hat : a ≤ t) {g₀ : ℝ → M}
    (hg₀ : ContinuousOn g₀ (Icc a t)) (hlift : ∀ x ∈ Icc a t, f (g₀ x) = c x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℝ → M, ContinuousOn g (Icc a (t + δ)) ∧
      Set.EqOn g g₀ (Icc a t) ∧ ∀ x ∈ Icc a (t + δ), f (g x) = c x := by
  classical
  -- lift `c` rightward through the endpoint value `g₀ t`
  have hft : f (g₀ t) = c t := hlift t ⟨hat, le_rfl⟩
  obtain ⟨δ, hδ, g₁, hg₁t, hg₁cont, hg₁lift⟩ :=
    IsLocalHomeomorph.exists_rightward_lift hf hc hft
  refine ⟨δ, hδ, (Set.Iic t).piecewise g₀ g₁, ?_, ?_, ?_⟩
  · -- continuity by gluing the two lifts on the closed cover `[a,t] ∪ [t,t+δ]`
    apply ContinuousOn.piecewise
    · intro x hx
      have hxt : x = t := by
        have := hx.2; rw [frontier_Iic] at this; simpa using this
      subst hxt; exact hg₁t.symm
    · refine hg₀.mono fun x hx => ⟨hx.1.1, ?_⟩
      have := hx.2; rw [closure_Iic] at this; exact this
    · refine hg₁cont.mono fun x hx => ⟨?_, hx.1.2⟩
      have := hx.2; rw [compl_Iic, closure_Ioi] at this; exact this
  · intro x hx
    rw [Set.piecewise_eq_of_mem _ _ _ (show x ∈ Set.Iic t from hx.2)]
  · intro x hx
    by_cases hxt : x ∈ Set.Iic t
    · rw [Set.piecewise_eq_of_mem _ _ _ hxt]
      exact hlift x ⟨hx.1, hxt⟩
    · rw [Set.piecewise_eq_of_notMem _ _ _ hxt]
      rw [Set.mem_Iic, not_le] at hxt
      exact hg₁lift x ⟨hxt.le, hx.2⟩

end Riemannian

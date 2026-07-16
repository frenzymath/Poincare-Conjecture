import OpenGALib.Riemannian.Manifold.ExpandingMap
import OpenGALib.Riemannian.Metric.RiemannianDistance

/-!
# Closed submanifolds of a complete manifold are complete (do Carmo Ch. 7, Corollary 2.10)

do Carmo, *Riemannian Geometry*, Ch. 7, Corollary 2.10: a closed submanifold of a
complete Riemannian manifold is complete in the induced metric; in particular the
closed subsets of Euclidean space are complete.

We formalize a *submanifold with its induced metric* as a smooth map `ι : N → M`
which is

* **metric-preserving** (`DCPreservesMetric gN gM ι`): the metric `gN` of `N` is the
  pullback `ι^* gM` — this is exactly what "the induced metric" means, and it makes `ι`
  an immersion (its differential is injective, since it preserves inner products);
* a **closed topological embedding** (`IsClosedEmbedding ι`): `ι` is a homeomorphism onto
  its range and the range is closed — this is precisely a *closed embedded submanifold*.

Under the standing do Carmo hypothesis that both metric-space structures are the
Riemannian distances of their metrics (`gN.IsRiemannianDist`, `gM.IsRiemannianDist`) and
that `M` is metrically complete (`CompleteSpace M`), we prove `CompleteSpace N`.

The argument is more elementary than do Carmo's (which routes through the properness half
of Hopf–Rinow): a metric-preserving map is **1-Lipschitz for the Riemannian distances**
(`DCPreservesMetric.riemannianEDist_le`), because the image of any curve has the same
length, so a Cauchy sequence in `N` maps to a Cauchy sequence in the complete `M`, whose
limit lies in the closed range `ι(N)`; the topological embedding pulls the limit back to a
limit in `N`. Taking `M = ℝⁿ` recovers "closed subsets of Euclidean space are complete".

## Main results

* `Riemannian.DCPreservesMetric.enorm_mfderiv_eq` — a metric-preserving
  map preserves fibre enorms `‖df v‖ₑ = ‖v‖ₑ`;
* `Riemannian.DCPreservesMetric.pathELength_comp_eq` — hence the length
  of `ι ∘ c` equals the length of `c`;
* `Riemannian.DCPreservesMetric.riemannianEDist_le` — hence
  `d_M(ι a, ι b) ≤ d_N(a, b)` (the 1-Lipschitz property);
* `Riemannian.completeSpace_of_isClosedEmbedding_dcPreservesMetric` — **Corollary 2.10**.
-/

open Bundle Manifold MeasureTheory Set Topology
open scoped Manifold Topology ContDiff ENNReal

noncomputable section

-- the chart/bundle machinery pulls in `Module.Finite ℝ E` etc. that some thin lemmas never name
set_option linter.unusedSectionVars false

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {N : Type*} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [InnerProductSpace ℝ E']
  [Module.Finite ℝ E'] [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [MetricSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M]

/-- **Math.** A metric-preserving map (do Carmo Def. 2.2) preserves fibre enorms:
`‖df_p(v)‖ₑ = ‖v‖ₑ`. This is the equality strengthening of
`DCExpandsMetric.enorm_mfderiv_le`: the pulled-back inner product agrees with the source
inner product, so the square roots (hence the enorms) agree. -/
theorem DCPreservesMetric.enorm_mfderiv_eq {gN : RiemannianMetric I N}
    {gM : RiemannianMetric I' M} {ι : N → M} (hpres : DCPreservesMetric gN gM ι)
    (p : N) (v : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
    ‖v‖ₑ = ‖mfderiv I I' ι p v‖ₑ := by
  letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
  rw [enorm_tangent_eq_sqrt_metricInner gN p v,
    enorm_tangent_eq_sqrt_metricInner gM (ι p) (mfderiv I I' ι p v), hpres p v v]

/-- **Math.** **Length preservation** (do Carmo Ch. 7): if `ι` preserves the metric and
`c : [a, b] → N` is `C¹`, then the `M`-length of `ι ∘ c` equals the `N`-length of `c`,
`ℓ(ι ∘ c) = ℓ(c)`. Both lengths are the tangent integrals `∫ ‖γ'‖ₑ`; the integrands agree
pointwise by the chain rule `(ι ∘ c)' = dι(c')` and `‖dι(c')‖ₑ = ‖c'‖ₑ`
(`enorm_mfderiv_eq`). This is the equality strengthening of `DCExpandsMetric.pathELength_le`
(the `Manifold.pathELength` counterpart of `DCPreservesMetric.dcArcLength`). -/
theorem DCPreservesMetric.pathELength_comp_eq {gN : RiemannianMetric I N}
    {gM : RiemannianMetric I' M} {ι : N → M} (hpres : DCPreservesMetric gN gM ι)
    (hι : MDifferentiable I I' ι) {c : ℝ → N} {a b : ℝ}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I 1 c (Icc a b)) :
    letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
    Manifold.pathELength I c a b = Manifold.pathELength I' (ι ∘ c) a b := by
  letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo,
    Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  refine MeasureTheory.lintegral_congr_ae ?_
  refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall fun t ht => ?_)
  simp only []
  have hct : MDifferentiableAt 𝓘(ℝ, ℝ) I c t :=
    ((hc t (Ioo_subset_Icc_self ht)).contMDiffAt
      (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hchain : mfderiv 𝓘(ℝ, ℝ) I' (ι ∘ c) t 1
      = mfderiv I I' ι (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1) :=
    DCVelocity_comp t (hι (c t)) hct
  rw [hchain]
  exact hpres.enorm_mfderiv_eq (c t) (mfderiv 𝓘(ℝ, ℝ) I c t 1)

/-- **Math.** A metric-preserving smooth map is **1-Lipschitz for the Riemannian
distances**: `d_M(ι a, ι b) ≤ d_N(a, b)`. Every `C¹` path `c` from `a` to `b` in `N` maps
to a path `ι ∘ c` from `ι a` to `ι b` in `M` of the same length, so the infimum defining
`d_M(ι a, ι b)` is `≤` the length of every such image, hence `≤ d_N(a, b)`. (The reverse
inequality can fail: a short-cut in `M` between `ι a` and `ι b` need not stay in the
submanifold `ι(N)`.) This is do Carmo's observation that the inclusion of a submanifold
does not increase ambient distance. -/
theorem DCPreservesMetric.riemannianEDist_le {gN : RiemannianMetric I N}
    {gM : RiemannianMetric I' M} {ι : N → M} (hpres : DCPreservesMetric gN gM ι)
    (hι : ContMDiff I I' ∞ ι) (a b : N) :
    letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
    letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
    Manifold.riemannianEDist I' (ι a) (ι b) ≤ Manifold.riemannianEDist I a b := by
  letI : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
  by_contra hle
  have hlt := not_le.mp hle
  obtain ⟨c, hc0, hc1, hcC1, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hlt
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) I' 1 (ι ∘ c) (Icc 0 1) :=
    (hι.of_le (by norm_num)).comp_contMDiffOn hcC1
  have hle' : Manifold.riemannianEDist I' (ι a) (ι b)
      ≤ Manifold.pathELength I' (ι ∘ c) 0 1 := by
    refine Manifold.riemannianEDist_le_pathELength hcomp ?_ ?_ zero_le_one
    · simp [Function.comp, hc0]
    · simp [Function.comp, hc1]
  rw [← hpres.pathELength_comp_eq (hι.mdifferentiable (by norm_num)) hcC1] at hle'
  exact absurd (hle'.trans_lt hlen) (lt_irrefl _)

/-- **Math.** **do Carmo Ch. 7, Corollary 2.10.** A *closed submanifold with its induced
metric* — a smooth closed embedding `ι : N → M` that preserves the metric (`gN = ι^* gM`)
— of a *complete* Riemannian manifold `M` is itself complete. In particular the closed
subsets of Euclidean space are complete (take `M = ℝⁿ`).

Proof: a metric-preserving map is `1`-Lipschitz for the Riemannian distances
(`riemannianEDist_le`), so it carries a Cauchy sequence `u` of `N` to a Cauchy sequence
`ι ∘ u` of the complete space `M`, which converges to some `y`. Because the range of a
closed embedding is closed, `y ∈ ι(N)`, say `y = ι x`; because a closed embedding is a
homeomorphism onto its range, `ι ∘ u → ι x` forces `u → x` in `N`. Thus every Cauchy
sequence of `N` converges, i.e. `N` is complete. -/
theorem completeSpace_of_isClosedEmbedding_dcPreservesMetric
    (gN : RiemannianMetric I N) (gM : RiemannianMetric I' M)
    (hgN : gN.IsRiemannianDist) (hgM : gM.IsRiemannianDist) [CompleteSpace M]
    {ι : N → M} (hι : ContMDiff I I' ∞ ι) (hpres : DCPreservesMetric gN gM ι)
    (hemb : IsClosedEmbedding ι) :
    CompleteSpace N := by
  letI bN : Bundle.RiemannianBundle (fun x : N ↦ TangentSpace I x) := ⟨gN.toRiemannianMetric⟩
  letI bM : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I' x) := ⟨gM.toRiemannianMetric⟩
  haveI hrN : IsRiemannianManifold I N := hgN
  haveI hrM : IsRiemannianManifold I' M := hgM
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hlip : LipschitzWith 1 ι := by
    intro x y
    rw [ENNReal.coe_one, one_mul, IsRiemannianManifold.out (I := I') (ι x) (ι y),
      IsRiemannianManifold.out (I := I) x y]
    exact hpres.riemannianEDist_le hι x y
  have hcu : CauchySeq (fun n => ι (u n)) := hlip.uniformContinuous.comp_cauchySeq hu
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcu
  have hymem : y ∈ Set.range ι :=
    hemb.isClosed_range.mem_of_tendsto hy
      (Filter.Eventually.of_forall fun n => Set.mem_range_self (u n))
  obtain ⟨x, hx⟩ := hymem
  refine ⟨x, ?_⟩
  rw [hemb.tendsto_nhds_iff, hx]
  exact hy

end Riemannian

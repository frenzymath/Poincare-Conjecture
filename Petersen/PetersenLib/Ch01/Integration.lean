import PetersenLib.Ch01.VolumeForm
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Petersen Ch. 1, §1.2 — Integration on Riemannian manifolds

The mechanics of Petersen §1.2's integration remark around the definition
`integrateOnRiemannianManifold` (in `PetersenLib.Ch01.VolumeForm`):

* the reduction of integration over `M` to integration over an open dense
  subset `O ⊆ M` — Petersen: every manifold contains an open dense `O` with
  trivial (hence orientable) tangent bundle carrying an orthonormal frame,
  so integrating over `O` integrates over all of `M`
  (`integrateOnRiemannianManifold_eq_setIntegral_of_dense`);

* the decomposition of the integral through a (finite) smooth partition of
  unity, `∫ f = ∑ᵢ ∫ ρᵢ f`
  (`integrateOnRiemannianManifold_eq_sum_smoothPartitionOfUnity`), and its
  chart-subordinate refinement expressing the integral as a finite sum of
  integrals over chart domains
  (`integrateOnRiemannianManifold_eq_sum_charts`) — the standard mechanism
  by which integration of `f · vol` is computed in local coordinates;

* the existence, on a compact manifold, of a finite smooth partition of
  unity subordinate to chart domains
  (`exists_finite_smoothPartitionOfUnity_isSubordinate_chartAt_source`),
  which feeds the previous decomposition.

## Design notes (the honest gap)

Mathlib has *no* integration of top-degree differential forms on manifolds
and *no* canonical Riemannian volume measure (see the module docstring of
`PetersenLib.Ch01.VolumeForm` and the TODO on
`integrateOnRiemannianManifold`), so as there, all statements are relative
to an explicit measure `μ` on `M` standing in for the measure induced by
`vol_g`. Two consequences:

* In `integrateOnRiemannianManifold_eq_setIntegral_of_dense`, the fact that
  the complement of Petersen's trivializing open dense set is `vol_g`-null
  is *not* a theorem about an arbitrary `μ` (an open dense set can have a
  fat complement), nor is the existence of the trivializing set itself
  formalizable today (no tangent-bundle triviality machinery); nullity of
  the complement is therefore a hypothesis, as is the open-dense-ness
  carried for faithfulness to the remark.

* The partition-of-unity decomposition is stated for a *finite* partition
  (which suffices for compact manifolds, and exists there by
  `exists_finite_smoothPartitionOfUnity_isSubordinate_chartAt_source`);
  the locally-finite infinite case is a routine dominated-convergence
  argument orthogonal to the Riemannian content.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §1.2.
-/

open Bundle Function MeasureTheory Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Unfolding -/

/-- **Eng.** Unfolding lemma: `integrateOnRiemannianManifold` is the Bochner
integral against the measure `μ` standing in for the Riemannian volume
measure of `g`. -/
@[simp]
theorem integrateOnRiemannianManifold_eq_integral [MeasurableSpace M]
    (g : RiemannianMetric I M) (μ : Measure M) (f : M → ℝ) :
    integrateOnRiemannianManifold g μ f = ∫ x, f x ∂μ :=
  rfl

/-! ## Integration over an open dense subset (Petersen §1.2) -/

set_option linter.unusedVariables false in
/-- **Math.** Petersen §1.2: every manifold contains an open dense set
`O ⊆ M` on which `TO ≅ O × ℝⁿ` is trivial — in particular `O` is orientable
and carries an orthonormal frame — and integrating over `O` integrates
functions over all of `M`. This lemma is the integration step: if the
complement of `O` is null for the (stand-in) Riemannian measure `μ`, then
the integral over `M` equals the integral over `O`.

The hypotheses `IsOpen O` and `Dense O` record Petersen's setting; the
analytically operative hypothesis is nullity of `Oᶜ` (which holds for the
trivializing set Petersen constructs, its complement being a countable
union of lower-dimensional submanifolds, but *not* for an arbitrary open
dense set — the complement can be a fat Cantor-type set). The existence of
the trivializing `O` itself (a tangent-bundle triviality statement) has no
Mathlib infrastructure and is not formalized here. -/
theorem integrateOnRiemannianManifold_eq_setIntegral_of_dense [MeasurableSpace M]
    (g : RiemannianMetric I M) (μ : Measure M) (f : M → ℝ) {O : Set M}
    (hO_open : IsOpen O) (hO_dense : Dense O) (hO_null : μ Oᶜ = 0) :
    integrateOnRiemannianManifold g μ f = ∫ x in O, f x ∂μ := by
  have hae : ∀ᵐ x ∂μ, x ∈ O := by
    rw [ae_iff]
    simpa using hO_null
  rw [integrateOnRiemannianManifold]
  conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]

/-! ## Integration through a partition of unity (Petersen §1.2) -/

section PartitionOfUnity

variable [MeasurableSpace M] [OpensMeasurableSpace M] {ι : Type*} [Fintype ι]

omit [IsManifold I ∞ M] [Fintype ι] in
/-- **Eng.** Each member of a smooth partition of unity multiplied into an
integrable function stays integrable: `ρ i` is continuous and bounded by
`1`. -/
theorem SmoothPartitionOfUnity.integrable_mul {μ : Measure M}
    (ρ : SmoothPartitionOfUnity ι I M univ) {f : M → ℝ} (hf : Integrable f μ)
    (i : ι) : Integrable (fun x => ρ i x * f x) μ := by
  refine hf.bdd_mul (c := 1) (map_continuous (ρ i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (ρ.nonneg i x)]
  exact ρ.le_one i x

/-- **Math.** Petersen §1.2 (integration mechanism): through a (finite)
smooth partition of unity `ρ` on `M`, the integral of `f` decomposes as
`∫_M f = ∑ᵢ ∫_M ρᵢ f`, since `∑ᵢ ρᵢ = 1` pointwise. Each summand `ρᵢ f` is
supported where `ρᵢ` is, so — for a partition subordinate to an atlas
(`integrateOnRiemannianManifold_eq_sum_charts`) — each term is an integral
over a single chart domain, where `f · vol_g` can be computed in
coordinates. -/
theorem integrateOnRiemannianManifold_eq_sum_smoothPartitionOfUnity
    (g : RiemannianMetric I M) (μ : Measure M)
    (ρ : SmoothPartitionOfUnity ι I M univ)
    {f : M → ℝ} (hf : Integrable f μ) :
    integrateOnRiemannianManifold g μ f = ∑ i, ∫ x, ρ i x * f x ∂μ := by
  have hpt : ∀ x : M, f x = ∑ i, ρ i x * f x := by
    intro x
    have hsum : ∑ i, ρ i x = 1 := by
      have h := ρ.sum_eq_one (mem_univ x)
      rwa [finsum_eq_sum_of_fintype] at h
    rw [← Finset.sum_mul, hsum, one_mul]
  calc integrateOnRiemannianManifold g μ f
      = ∫ x, ∑ i, ρ i x * f x ∂μ := by
        rw [integrateOnRiemannianManifold]
        exact integral_congr_ae (Filter.Eventually.of_forall hpt)
    _ = ∑ i, ∫ x, ρ i x * f x ∂μ :=
        integral_finset_sum _ fun i _ =>
          SmoothPartitionOfUnity.integrable_mul ρ hf i

/-- **Math.** Petersen §1.2 (integration in local charts): if the finite
smooth partition of unity is subordinate to chart domains — `ρ i` supported
in the chart around `c i` — then the integral of `f` over `M` is a finite
sum of integrals over chart domains:
`∫_M f = ∑ᵢ ∫_{chart at cᵢ} ρᵢ f`. Together with
`exists_finite_smoothPartitionOfUnity_isSubordinate_chartAt_source` this
reduces integration on a compact Riemannian manifold to integrals over
coordinate charts. -/
theorem integrateOnRiemannianManifold_eq_sum_charts
    (g : RiemannianMetric I M) (μ : Measure M)
    (ρ : SmoothPartitionOfUnity ι I M univ) (c : ι → M)
    (hρ : ρ.IsSubordinate fun i => (chartAt H (c i)).source)
    {f : M → ℝ} (hf : Integrable f μ) :
    integrateOnRiemannianManifold g μ f
      = ∑ i, ∫ x in (chartAt H (c i)).source, ρ i x * f x ∂μ := by
  rw [integrateOnRiemannianManifold_eq_sum_smoothPartitionOfUnity g μ ρ hf]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  have hzero : ρ i x = 0 := by
    by_contra h
    exact hx (hρ i (subset_tsupport _ (mem_support.mpr h)))
  rw [hzero, zero_mul]

end PartitionOfUnity

/-! ## Existence of chart-subordinate partitions on compact manifolds -/

/-- **Math.** On a compact (Hausdorff) manifold there is a *finite* smooth
partition of unity subordinate to chart domains: finitely many charts cover
`M` by compactness, and Mathlib's `SmoothPartitionOfUnity.exists_isSubordinate`
produces a partition indexed by those charts. This supplies the hypothesis
of `integrateOnRiemannianManifold_eq_sum_charts`, so on a compact Riemannian
manifold integration is always computable chartwise. -/
theorem exists_finite_smoothPartitionOfUnity_isSubordinate_chartAt_source
    [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] :
    ∃ (s : Finset M) (ρ : SmoothPartitionOfUnity s I M univ),
      ρ.IsSubordinate fun x : s => (chartAt H (x : M)).source := by
  obtain ⟨s, hs⟩ := IsCompact.elim_finite_subcover isCompact_univ
    (fun x : M => (chartAt H x).source)
    (fun x => (chartAt H x).open_source)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_chart_source H x⟩)
  have hcov : univ ⊆ ⋃ x : s, (chartAt H (x : M)).source := by
    intro y hy
    obtain ⟨x, hxs, hyx⟩ := mem_iUnion₂.mp (hs hy)
    exact mem_iUnion.mpr ⟨⟨x, hxs⟩, hyx⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := I)
    isClosed_univ (fun x : s => (chartAt H (x : M)).source)
    (fun x => (chartAt H _).open_source) hcov
  exact ⟨s, ρ, hρ⟩

end PetersenLib

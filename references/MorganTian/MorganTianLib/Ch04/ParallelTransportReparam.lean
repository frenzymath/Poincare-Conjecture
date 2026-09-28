import MorganTianLib.Ch04.TensorParallelTransport
import MorganTianLib.Ch04.ConstantTensorTransport

/-!
# Reparameterization of the parallel transport equation

The within-derivative chart equation is preserved by differentiable changes
of the curve parameter, including ones whose derivative vanishes. This is
the radial compatibility input for the smooth-transition chart curves used
in local tensor supports.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The parallel equation in a fixed chart is invariant under a
parameter change mapping the new interval into the original interval.
Neither monotonicity nor a nonzero parameter derivative is needed. -/
theorem isParallelWithinSolOn_reparam
    {g : RiemannianMetric I M} {α : M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b l u : ℝ}
    (hV : IsParallelWithinSolOn (I := I) g α c V a b)
    {r r' : ℝ → ℝ} (hrange : MapsTo r (Icc l u) (Icc a b))
    (hr : ∀ t ∈ Icc l u, HasDerivWithinAt r (r' t) (Icc l u) t) :
    IsParallelWithinSolOn (I := I) g α (c ∘ r) (fun t => V (r t)) l u := by
  intro t ht
  obtain ⟨velocity, hc, hfield⟩ := hV (r t) (hrange ht)
  refine ⟨r' t • velocity, hc.scomp t (hr t ht) hrange, ?_⟩
  have hcomp := hfield.scomp t (hr t ht) hrange
  have hscale : Geodesic.chartChristoffelContraction (I := I) g α
      (r' t • velocity) (chartFieldRep (I := I) c α V (r t))
      (extChartAt I α (c (r t))) =
      r' t • Geodesic.chartChristoffelContraction (I := I) g α velocity
        (chartFieldRep (I := I) c α V (r t)) (extChartAt I α (c (r t))) := by
    rw [Geodesic.chartChristoffelContraction_symm,
      Geodesic.chartChristoffelContraction_smul_right,
      Geodesic.chartChristoffelContraction_symm g α _ velocity]
  change HasDerivWithinAt ((chartFieldRep (I := I) c α V) ∘ r)
    (-Geodesic.chartChristoffelContraction (I := I) g α
      (r' t • velocity) (chartFieldRep (I := I) c α V (r t))
      (extChartAt I α (c (r t)))) (Icc l u) t
  rw [hscale, ← smul_neg]
  exact hcomp

/-- **Math.** A chartwise parallel field on an entire nondegenerate interval
is intrinsically parallel on that interval. -/
theorem isParallelAlongWithinOn_of_single_chart
    {g : RiemannianMetric I M} {α : M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b : ℝ} (hab : a < b)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hV : IsParallelWithinSolOn (I := I) g α c V a b) :
    IsParallelAlongWithinOn (I := I) g c V a b := by
  intro t ht
  exact ⟨α, a, b, hab, ht, Subset.rfl, self_mem_nhdsWithin, hsrc, hV⟩

/-- **Math.** Reparameterization of a chartwise parallel field gives an
intrinsic parallel field along the reparameterized curve. -/
theorem isParallelAlongWithinOn_reparam_of_single_chart
    {g : RiemannianMetric I M} {α : M} {c : ℝ → M}
    {V : ∀ t, TangentSpace I (c t)} {a b l u : ℝ} (hlu : l < u)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hV : IsParallelWithinSolOn (I := I) g α c V a b)
    {r r' : ℝ → ℝ} (hrange : MapsTo r (Icc l u) (Icc a b))
    (hr : ∀ t ∈ Icc l u, HasDerivWithinAt r (r' t) (Icc l u) t) :
    IsParallelAlongWithinOn (I := I) g (c ∘ r) (fun t => V (r t)) l u :=
  isParallelAlongWithinOn_of_single_chart hlu
    (fun t ht => hsrc (r t) (hrange ht)) (isParallelWithinSolOn_reparam hV hrange hr)

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]

/-- **Math.** The actual endpoint map along a reparameterized curve evaluates
the original parallel field at the new endpoint parameters. The original
curve need only have a chartwise parallel solution on its closed interval;
global C1 regularity is required only of the reparameterized curve. -/
theorem parallelTransportTangentEquiv_reparam_apply_of_single_chart
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ → M} {V : ∀ t, TangentSpace I (c t)} {r r' : ℝ → ℝ}
    {a b l u : ℝ} (hlu : l < u)
    (hcr : ContMDiff 𝓘(ℝ, ℝ) I 1 (c ∘ r))
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hV : IsParallelWithinSolOn (I := I) g α c V a b)
    (hrange : MapsTo r (Icc l u) (Icc a b))
    (hr : ∀ t ∈ Icc l u, HasDerivWithinAt r (r' t) (Icc l u) t) :
    parallelTransportTangentEquiv g hlu hcr (V (r l)) = V (r u) :=
  parallelTransportTangentEquiv_apply_eq_of_isParallelAlongWithinOn g hlu hcr
    (isParallelAlongWithinOn_reparam_of_single_chart hlu hsrc hV hrange hr)

/-- **Math.** A C1 reparameterization with the same endpoints gives the same
actual Levi-Civita endpoint map when the original curve stays in one chart.
This includes smooth reparameterizations stationary at either endpoint. -/
theorem parallelTransportTangentBetween_reparam_of_single_chart
    (g : RiemannianMetric I M) (α : M)
    {c : ℝ → M} {r : ℝ → ℝ} {a b l u : ℝ}
    (hab : a < b) (hlu : l < u)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (hr : ContDiff ℝ 1 r)
    (hsrc : ∀ t ∈ Icc a b, c t ∈ (chartAt H α).source)
    (hrange : MapsTo r (Icc l u) (Icc a b))
    (hl : r l = a) (hu : r u = b) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    parallelTransportTangentBetween g hlu (hc.comp hr.contMDiff)
      (congrArg c hl) (congrArg c hu) =
      parallelTransportTangentIsometryEquiv g hab hc := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  subst a b
  apply LinearIsometryEquiv.ext
  intro v
  change parallelTransportTangentEquiv g hlu (hc.comp hr.contMDiff) v =
    parallelTransportTangentEquiv g hab hc v
  obtain ⟨V, hV, hVa⟩ := exists_isParallelAlongWithinOn (g := g) hab hc.contMDiffOn v
  have hVr : IsParallelAlongWithinOn (I := I) g (c ∘ r) (fun t => V (r t)) l u :=
    isParallelAlongWithinOn_reparam_of_single_chart hlu hsrc
      (hV.isParallelWithinSolOn_of_mem_source Subset.rfl hsrc) hrange
      (fun t _ => (hr.differentiable (by simp) t).hasDerivAt.hasDerivWithinAt)
  calc
    parallelTransportTangentEquiv g hlu (hc.comp hr.contMDiff) v =
        parallelTransportTangentEquiv g hlu (hc.comp hr.contMDiff) (V (r l)) :=
      congrArg _ hVa.symm
    _ = V (r u) := parallelTransportTangentEquiv_apply_eq_of_isParallelAlongWithinOn
      g hlu (hc.comp hr.contMDiff) hVr
    _ = parallelTransportTangentEquiv g hab hc v := by
      rw [← hVa]
      exact (parallelTransportTangentEquiv_apply_eq_of_isParallelAlongWithinOn
        g hab hc hV).symm

end MorganTianLib

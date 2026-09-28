import MorganTianLib.Ch04.LeviCivitaTensorTransport

/-!
# Parallel transport along constant curves

Uniqueness of parallel fields identifies the canonical endpoint transport with
the endpoint value of any interval-parallel field. In particular, a constant
curve has identity transport.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** Endpoint transport evaluates any parallel field at the right endpoint. -/
theorem parallelTransportTangentEquiv_apply_eq_of_isParallelAlongWithinOn
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c)
    {V : ∀ t, TangentSpace I (c t)}
    (hV : IsParallelAlongWithinOn (I := I) g c V a b) :
    parallelTransportTangentEquiv g hab hc (V a) = V b := by
  let W : ∀ t, TangentSpace I (c t) := fun t =>
    Variation.parallelCovariantFieldSeed (I := I) (E := E) g hab hc (V a : E) t
  have hW : IsParallelAlongWithinOn (I := I) g c W a b :=
    (isParallelAlongWithinOn_iff_isParallelFieldAlongOn hc).2
      (Variation.parallelCovariantFieldSeed_isParallel (I := I) (E := E)
        g hab hc (V a : E)).isParallelFieldAlongOn
  have hWa : W a = V a :=
    Variation.parallelCovariantFieldSeed_left (I := I) (E := E) g hab hc (V a : E)
  rw [parallelTransportTangentEquiv_apply, Variation.parallelCovariantTransportAlong_apply]
  change W b = V b
  exact hW.eqOn_of_eq_at hV (left_mem_Icc.2 hab.le) hWa (right_mem_Icc.2 hab.le)

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **Math.** A constant tangent vector is parallel along a constant curve. -/
theorem isParallelAlongWithinOn_const (g : RiemannianMetric I M)
    (p : M) {a b : ℝ} (hab : a < b) (v : TangentSpace I p) :
    IsParallelAlongWithinOn (I := I) g (fun _ => p) (fun _ => v) a b := by
  intro t ht
  refine ⟨p, a, b, hab, ht, subset_rfl, self_mem_nhdsWithin,
    fun _ _ => mem_chart_source H p, ?_⟩
  intro s hs
  refine ⟨0, hasDerivWithinAt_const _ _ _, ?_⟩
  simp only [Geodesic.chartChristoffelContraction_zero_left, neg_zero]
  exact hasDerivWithinAt_const _ _ _

/-- **Math.** Levi-Civita transport along a constant curve fixes every vector. -/
@[simp] theorem parallelTransportTangentEquiv_const_apply
    (g : RiemannianMetric I M) (p : M) {a b : ℝ} (hab : a < b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun _ : ℝ => p)) (v : TangentSpace I p) :
    parallelTransportTangentEquiv g hab hc v = v :=
  parallelTransportTangentEquiv_apply_eq_of_isParallelAlongWithinOn g hab hc
    (isParallelAlongWithinOn_const g p hab v)

/-- **Math.** Identifying both endpoints of a constant curve with its value
gives the identity tangent isometry. -/
theorem parallelTransportTangentBetween_eq_refl_of_constant
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hab : a < b) (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (p : M)
    (hx : c a = p) (hy : c b = p) (hconstant : ∀ t, c t = p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    parallelTransportTangentBetween g hab hc hx hy =
      LinearIsometryEquiv.refl ℝ (TangentSpace I p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hcurve : c = fun _ => p := funext hconstant
  subst c
  apply LinearIsometryEquiv.ext
  intro v
  change parallelTransportTangentEquiv g hab hc v = v
  exact parallelTransportTangentEquiv_const_apply g p hab hc v

/-- **Math.** The canonical local tangent transport is the identity at its
centre. -/
@[simp] theorem localLeviCivitaTangentTransport_self
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x) (hpU : p ∈ U) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    localLeviCivitaTangentTransport g p hC ⟨p, hpU⟩ =
      LinearIsometryEquiv.refl ℝ (TangentSpace I p) :=
  parallelTransportTangentBetween_eq_refl_of_constant g
    (by norm_num : (0 : ℝ) < 1) (hC p hpU).1 p
    (hC p hpU).2.1 (hC p hpU).2.2 (localTransportCurve_self p)

end MorganTianLib

import MorganTianLib.Ch04.TensorHilbertSupport
import MorganTianLib.Ch04.ConvexInvariant
import MorganTianLib.Ch04.LocalTransportCurves
import MorganTianLib.Ch04.SpatialTensorTransport

/-!
# Local Levi-Civita transport of convex tensor carriers

The declared transport family consists of the actual endpoint maps of
Levi-Civita parallel transport along C1 curves. Parallel invariance is
stated for an independently specified tensor carrier.

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

/-- **Math.** The endpoint parallel isometry with its tangent fibres identified
by the stated endpoint equalities. -/
def parallelTransportTangentBetween (g : RiemannianMetric I M)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {x y : M}
    (hx : c a = x) (hy : c b = y) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace I y := by
  subst x y
  exact parallelTransportTangentIsometryEquiv g hab hc

/-- **Math.** Actual Levi-Civita transports on covariant tensor fibres, over
all C1 curves and all nondegenerate closed parameter intervals. -/
def leviCivitaCovariantTensorTransports (g : RiemannianMetric I M) (k : ℕ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    LinearTransportFamily (fun x : M => CovariantTensorFiber k (TangentSpace I x)) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  fun x y => {P | ∃ (c : ℝ → M) (a b : ℝ) (hab : a < b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) (hx : c a = x) (hy : c b = y),
    P = (covariantTensorTransportEquiv k
      (parallelTransportTangentBetween g hab hc hx hy)).toLinearEquiv}

/-- **Math.** Every actual endpoint tensor transport belongs to the declared
Levi-Civita family. -/
theorem parallelTransportTangentBetween_mem
    (g : RiemannianMetric I M) (k : ℕ)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : ContMDiff 𝓘(ℝ, ℝ) I 1 c) {x y : M}
    (hx : c a = x) (hy : c b = y) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (covariantTensorTransportEquiv k
      (parallelTransportTangentBetween g hab hc hx hy)).toLinearEquiv ∈
      leviCivitaCovariantTensorTransports g k x y :=
  ⟨c, a, b, hab, hc, hx, hy, rfl⟩

/-- **Math.** Transport from the centre to an endpoint along the explicit
chart interpolation. The curve formula is fixed, so later spatial regularity
statements can refer to this same family of endpoint maps. -/
def localLeviCivitaTangentTransport (g : RiemannianMetric I M) (p : M)
    {U : Set M}
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x) (x : U) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    TangentSpace I p ≃ₗᵢ[ℝ] TangentSpace I (x : M) :=
  parallelTransportTangentBetween g (by norm_num : (0 : ℝ) < 1)
    (hC x x.property).1 (hC x x.property).2.1 (hC x x.property).2.2

/-- **Math.** Near every point, the actual Levi-Civita maps along the chart
curves give tangent isometries whose induced tensor maps belong to the
curve-generated transport family. No continuity of these endpoint maps is
asserted here. -/
theorem exists_local_leviCivitaTangentTransport
    (g : RiemannianMetric I M) (k : ℕ) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ hC : ∀ x ∈ U,
        ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
        localTransportCurve (I := I) p x 0 = p ∧
        localTransportCurve (I := I) p x 1 = x,
        ∀ x : U, (covariantTensorTransportEquiv k
          (localLeviCivitaTangentTransport g p hC x)).toLinearEquiv ∈
            leviCivitaCovariantTensorTransports g k p x := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨U, hU, hpU, hcurves, _⟩ := exists_open_nhds_localTransportCurve (I := I) p
  have hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x :=
    fun x hx => ⟨(hcurves x hx).1.of_le (by simp), (hcurves x hx).2⟩
  refine ⟨U, hU, hpU, hC, ?_⟩
  intro x
  exact parallelTransportTangentBetween_mem g k (by norm_num : (0 : ℝ) < 1)
    (hC x x.property).1 (hC x x.property).2.1 (hC x x.property).2.2

/-- **Math.** At an exterior local maximum of intrinsic tensor distance,
parallel invariance under the actual Levi-Civita transports produces a local
active scalar support. The local isometries and their carrier preservation
are conclusions; spatial regularity and the Laplacian identity are separate
geometric obligations. -/
theorem exists_local_leviCivitaTensor_support
    (g : RiemannianMetric I M) (k : ℕ) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∀ (Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)))
      (u : ∀ x : M, CovariantTensorFiber k (TangentSpace I x)),
      (Z p).Nonempty → IsClosed (Z p) → Convex ℝ (Z p) →
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      u p ∉ Z p →
      IsLocalMax (fun x => Metric.infDist (WithLp.toLp 2 (u x))
        (hilbertCovariantTensorEquiv ⁻¹' Z x)) p →
      ∃ U : Set M, IsOpen U ∧ ∃ hpU : p ∈ U,
        ∃ hC : ∀ x ∈ U,
          ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
          localTransportCurve (I := I) p x 0 = p ∧
          localTransportCurve (I := I) p x 1 = x,
          let e := localLeviCivitaTangentTransport g p hC
          (∀ x : U, (covariantTensorTransportEquiv k (e x)).toLinearEquiv ∈
            leviCivitaCovariantTensorTransports g k p x) ∧
          ∃ q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p),
            ⟪q.1.2, WithLp.toLp 2
                (covariantTensorTransportEquiv k (e ⟨p, hpU⟩).symm (u p)) - q.1.1⟫_ℝ =
              Metric.infDist (WithLp.toLp 2 (u p)) (hilbertCovariantTensorEquiv ⁻¹' Z p) ∧
            IsLocalMax (fun x : U => ⟪q.1.2, WithLp.toLp 2
              (covariantTensorTransportEquiv k (e x).symm (u x)) - q.1.1⟫_ℝ)
              ⟨p, hpU⟩ := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro Z u hZne hZclosed hZconv hZparallel hp hmax
  obtain ⟨U, hU, hpU, hC, hmem⟩ := exists_local_leviCivitaTangentTransport g k p
  let e := localLeviCivitaTangentTransport g p hC
  have he (x : U) :
      covariantTensorTransportEquiv k (e x).symm '' Z x = Z p := by
    rw [← covariantTensorTransportEquiv_symm]
    have hforward : covariantTensorTransportEquiv k (e x) '' Z p = Z x :=
      hZparallel p x (covariantTensorTransportEquiv k (e x)).toLinearEquiv (hmem x)
    rw [← hforward]
    exact (covariantTensorTransportEquiv k (e x)).toEquiv.symm_image_image (Z p)
  have hmaxU : IsLocalMax (fun x : U => Metric.infDist (WithLp.toLp 2 (u x))
      (hilbertCovariantTensorEquiv ⁻¹' Z x)) ⟨p, hpU⟩ :=
    (continuous_subtype_val.continuousAt :
      Tendsto (fun x : U => (x : M)) (𝓝 ⟨p, hpU⟩) (𝓝 p)).eventually hmax
  obtain ⟨q, hq, hqmax⟩ := exists_covariantTensor_support_isLocalMax
    (fun x : U => Z x) hZne hZclosed hZconv (fun x : U => (e x).symm)
    (fun x : U => u x) ⟨p, hpU⟩ (Eventually.of_forall he) hp hmaxU
  exact ⟨U, hU, hpU, hC, hmem, q, hq, hqmax⟩

end MorganTianLib

import MorganTianLib.Ch04.LocalTensorSupportRegularity
import MorganTianLib.Ch02.Bochner
import MorganTianLib.Ch04.LocalTransportSecondJet
import MorganTianLib.Ch04.TensorialDerivative

/-!
# Laplacians of tensor support contractions

The Hilbert support pairing is a finite contraction. When its vector fields
have zero first and diagonal second covariant jets, tracing its scalar
Hessian gives the same contraction of the rough tensor Laplacian.

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
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A finite tensor contraction with second-order normal fields
has scalar Laplacian equal to the contraction of the tensor rough Laplacian.
The constant support offset contributes zero. -/
theorem laplacianAt_tensor_contraction
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
    {ι : Type*} [Fintype ι] (Y : ι → SmoothVectorField I M)
    (hfirst : ∀ (X : SmoothVectorField I M) i,
      (g.leviCivitaConnection.cov X (Y i)) p = 0)
    (hsecond : ∀ (X : SmoothVectorField I M) i,
      secondCov g.leviCivitaConnection X X (Y i) p = 0)
    (c : (Fin k → ι) → ℝ) (B : ℝ) :
    laplacianAt g g.leviCivitaConnection
      (fun x => (∑ a : Fin k → ι, c a * A (fun j => Y (a j)) x) - B) p =
      ∑ a : Fin k → ι, c a *
        roughLaplacian g g.leviCivitaConnection A (fun j => Y (a j)) p := by
  have hterm (a : Fin k → ι) : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => c a * A (fun j => Y (a j)) x) :=
    contMDiff_const.mul (hA.contMDiff_eval _)
  have hsum : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun x => ∑ a : Fin k → ι, c a * A (fun j => Y (a j)) x) :=
    contMDiff_finsetSum (fun a _ => hterm a)
  simp only [sub_eq_add_neg]
  rw [laplacianAt_add g g.leviCivitaConnection hsum contMDiff_const,
    laplacianAt_const, add_zero,
    laplacianAt_finsetSum g g.leviCivitaConnection Finset.univ
      (fun a _ => hterm a) p]
  apply Finset.sum_congr rfl
  intro a _
  rw [laplacianAt_const_mul g g.leviCivitaConnection (c a)
    (hA.contMDiff_eval _) p]
  congr 1
  symm
  apply roughLaplacian_apply_eq_laplacianAt_of_contact
  exact roughLaplacianContactDefect_eq_zero_of_all_directions g
    g.leviCivitaConnection A (fun j => Y (a j)) p hA
    (hA.covTensorDerivAlong g.leviCivitaConnection)
    (fun X j => hfirst X (a j)) (fun X j => hsecond X (a j))

/-- **Math.** The actual canonical transported support germ has a smooth
representative whose Laplacian is the contraction of the rough tensor
Laplacian. Its vector fields retain the canonical transport germ. -/
theorem exists_contMDiff_localLeviCivitaTensor_support_germ_laplacian
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let b := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∀ N B : HilbertCovariantTensor k (TangentSpace I p),
      ∃ Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M,
        (∀ i, Y i p = b i) ∧
        (∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U, ∀ i,
          Y i x = localLeviCivitaTangentTransport g p hC ⟨x, hx⟩ (b i)) ∧
        ∃ f : M → ℝ, ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
          (∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U,
            f x = ⟪N, WithLp.toLp 2
              (covariantTensorTransportEquiv k
                (localLeviCivitaTangentTransport g p hC ⟨x, hx⟩).symm
                  (hA.toFiber g x)) - B⟫_ℝ) ∧
          laplacianAt g g.leviCivitaConnection f p =
            ∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
              N.ofLp (fun j => b (a j)) *
                roughLaplacian g g.leviCivitaConnection A (fun j => Y (a j)) p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  dsimp only
  intro N B
  obtain ⟨Y, hYp, hY⟩ := exists_smoothVectorFieldFamily_localLeviCivitaTangentTransport
    g p hpU hC b
  have hYi (i) : ∀ᶠ x in 𝓝 p, ∀ hx : x ∈ U,
      Y i x = localLeviCivitaTangentTransport g p hC ⟨x, hx⟩ (b i) := by
    filter_upwards [hY] with x hxY
    exact fun hx => hxY hx i
  have hfirst (X : SmoothVectorField I M) (i) :
      (g.leviCivitaConnection.cov X (Y i)) p = 0 :=
    cov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport
      g p hU hpU hC (b i) (Y i) (hYi i) X
  have hsecond (X : SmoothVectorField I M) (i) :
      secondCov g.leviCivitaConnection X X (Y i) p = 0 :=
    secondCov_eq_zero_of_eventuallyEq_localLeviCivitaTangentTransport
      g p hU hpU hC (b i) (Y i) (hYi i) X
  let f : M → ℝ := fun x =>
    (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      N.ofLp (fun j => b (a j)) * A (fun j => Y (a j)) x) - ⟪N, B⟫_ℝ
  refine ⟨Y, hYp, hY, f, ?_, ?_, ?_⟩
  · exact (contMDiff_finsetSum (fun a _ =>
      contMDiff_const.mul (hA.contMDiff_eval (fun j => Y (a j))))).sub contMDiff_const
  · filter_upwards [hY] with x hxY
    intro hx
    rw [inner_sub_right, hilbertCovariantTensor_inner_eq b]
    change (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      N.ofLp (fun j => b (a j)) * A (fun j => Y (a j)) x) - _ = _
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simp only [covariantTensorTransportEquiv_apply_apply, LinearIsometryEquiv.symm_symm]
    congr 1
    rw [← hA.toFiber_apply g x (fun j => Y (a j))]
    congr 1
    funext j
    exact hxY hx (a j)
  · exact laplacianAt_tensor_contraction g p hA Y hfirst hsecond
      (fun a => N.ofLp (fun j => b (a j))) ⟪N, B⟫_ℝ

/-- **Math.** At an exterior local maximum of distance from a parallel-invariant
closed convex tensor carrier, an active support normal has nonpositive
contraction with the rough Laplacian. The fields realizing the tangent basis
are produced from the actual local Levi-Civita transport. -/
theorem exists_localLeviCivitaTensor_support_roughLaplacian_nonpos
    (g : RiemannianMetric I M) (p : M)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let b := stdOrthonormalBasis ℝ (TangentSpace I p)
    ∀ Z : ∀ x : M, Set (CovariantTensorFiber k (TangentSpace I x)),
      (Z p).Nonempty → IsClosed (Z p) → Convex ℝ (Z p) →
      parallelInvariantFiberSet Z (leviCivitaCovariantTensorTransports g k) →
      hA.toFiber g p ∉ Z p →
      IsLocalMax (fun x => Metric.infDist (hA.toHilbertFiber g x)
        (hilbertCovariantTensorEquiv ⁻¹' Z x)) p →
      ∃ (q : ConvexSupportPair (hilbertCovariantTensorEquiv ⁻¹' Z p))
        (Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M),
        (∀ i, Y i p = b i) ∧
        ⟪q.1.2, hA.toHilbertFiber g p - q.1.1⟫_ℝ =
          Metric.infDist (hA.toHilbertFiber g p) (hilbertCovariantTensorEquiv ⁻¹' Z p) ∧
        (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
          q.1.2.ofLp (fun j => b (a j)) *
            roughLaplacian g g.leviCivitaConnection A (fun j => Y (a j)) p) ≤ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  intro Z hne hclosed hconv hparallel hout hmax
  obtain ⟨U, hU, hpU, hC, q, f, hf, hfmax, hfp, hfeq⟩ :=
    exists_contMDiff_localLeviCivitaTensor_support g p hA Z
      hne hclosed hconv hparallel hout hmax
  obtain ⟨Y, hYp, _, f', hf', hfeq', hlap⟩ :=
    exists_contMDiff_localLeviCivitaTensor_support_germ_laplacian
      g p hU hpU hC hA q.1.2 q.1.1
  have heq : f' =ᶠ[𝓝 p] f := by
    filter_upwards [hU.mem_nhds hpU, hfeq, hfeq'] with x hx he he'
    exact (he' hx).trans (he hx).symm
  have hmax' : IsLocalMax f' p := by
    change ∀ᶠ x in 𝓝 p, f' x ≤ f' p
    filter_upwards [hfmax, heq] with x hx hxeq
    rwa [hxeq, heq.self_of_nhds]
  refine ⟨q, Y, hYp, ?_, ?_⟩
  · have h := hfeq.self_of_nhds hpU
    rw [localLeviCivitaTangentTransport_self] at h
    change f p = ⟪q.1.2, WithLp.toLp 2
      (covariantTensorTransportEquiv k (LinearIsometryEquiv.refl ℝ (TangentSpace I p))
        (hA.toFiber g p)) - q.1.1⟫_ℝ at h
    rw [covariantTensorTransportEquiv_refl] at h
    exact h.symm.trans hfp
  · have hnonpos := (laplacianAt_nonpos_of_isLocalMax g
      g.leviCivitaConnection hf' hmax').2
    rwa [hlap] at hnonpos

end MorganTianLib

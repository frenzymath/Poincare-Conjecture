import MorganTianLib.Ch04.LocalTensorSupportRegularity
import MorganTianLib.Ch04.TensorFiberEvolution

/-!
# Jointly continuous tensor families in a transported frame

A finite family of smooth fields realizes canonical Levi-Civita transport
on one neighborhood. Reconstructing tensors from evaluations on those fields
gives jointly continuous representatives in the centre fibre. The neighborhood
is independent of the tensor, time, and support parameters.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle InnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The tensor in the centre fibre whose orthonormal components are
the evaluations on a specified finite family of smooth fields. -/
def tensorInSmoothFrame (g : RiemannianMetric I M) (p : M)
    (Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
    {k : ℕ} (A : CovTensorField I M k) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    HilbertCovariantTensor k (TangentSpace I p) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  hilbertCovariantTensorEquiv.symm
    (∑ a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p)),
      A (fun j => Y (a j)) x •
        covariantTensorBasisDual (stdOrthonormalBasis ℝ (TangentSpace I p)) a)

/-- **Math.** Joint continuity of all scalar evaluations gives joint continuity
of the reconstructed tensor in the full Hilbert tensor norm. -/
theorem continuous_tensorInSmoothFrame
    (g : RiemannianMetric I M) (p : M)
    (Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
    {T : Type*} [TopologicalSpace T] {k : ℕ} {A : T → CovTensorField I M k}
    (hcont : ∀ Z : Fin k → SmoothVectorField I M,
      Continuous (fun z : T × M => A z.1 Z z.2)) :
    Continuous (fun z : T × M => tensorInSmoothFrame g p Y (A z.1) z.2) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact hilbertCovariantTensorEquiv.symm.continuous.comp
    (continuous_finsetSum _ (fun a _ => (hcont (fun j => Y (a j))).smul
      continuous_const))

/-- **Math.** Differentiating the scalar evaluations differentiates the same
finite-frame representative, with its derivative in that frame. -/
theorem hasDerivAt_tensorInSmoothFrame
    (g : RiemannianMetric I M) (p x : M)
    (Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
    {k : ℕ} {A : ℝ → CovTensorField I M k} {D : CovTensorField I M k} {t : ℝ}
    (hderiv : ∀ Z : Fin k → SmoothVectorField I M,
      HasDerivAt (fun s => A s Z x) (D Z x) t) :
    HasDerivAt (fun s => tensorInSmoothFrame g p Y (A s) x)
      (tensorInSmoothFrame g p Y D x) t := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (a : Fin k → Fin (Module.finrank ℝ (TangentSpace I p))) _ =>
      (hderiv (fun j => Y (a j))).smul_const (covariantTensorBasisDual b a))
  dsimp only [tensorInSmoothFrame]
  exact (hilbertCovariantTensorEquiv (k := k) (V := TangentSpace I p)).symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hsum

variable [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A frame equal to canonical parallel transport reconstructs the
actual inverse-transported tensor. -/
theorem tensorInSmoothFrame_eq_transport
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    (Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M)
    {x : M} (hx : x ∈ U)
    {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    (∀ i, Y i x = localLeviCivitaTangentTransport g p hC ⟨x, hx⟩
      (stdOrthonormalBasis ℝ (TangentSpace I p) i)) →
      tensorInSmoothFrame g p Y A x = WithLp.toLp 2
        (covariantTensorTransportEquiv k
          (localLeviCivitaTangentTransport g p hC ⟨x, hx⟩).symm (hA.toFiber g x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  intro hY
  apply hilbertCovariantTensorEquiv.injective
  apply covariantTensorBasisEvaluation_injective
    (stdOrthonormalBasis ℝ (TangentSpace I p))
  ext a
  simp only [tensorInSmoothFrame, ContinuousLinearEquiv.apply_symm_apply,
    covariantTensorBasisEvaluation_apply, sum_apply,
    smul_apply, smul_eq_mul,
    covariantTensorBasisDual_apply_basis, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true,
    hilbertCovariantTensorEquiv_apply,
    covariantTensorTransportEquiv_apply_apply, LinearIsometryEquiv.symm_symm]
  rw [← hA.toFiber_apply g x (fun j => Y (a j))]
  congr 1
  funext j
  exact hY (a j)

/-- **Math.** One open neighborhood and one smooth frame realize inverse
transport simultaneously for every tensor degree and every tensor field. -/
theorem exists_localLeviCivitaTensor_frame
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ∃ hVU : V ⊆ U,
      ∃ Y : Fin (Module.finrank ℝ (TangentSpace I p)) → SmoothVectorField I M,
        ∀ {k : ℕ} {A : CovTensorField I M k} (hA : IsCovariantTensorField A)
          (x : M) (hx : x ∈ V),
          tensorInSmoothFrame g p Y A x = WithLp.toLp 2
            (covariantTensorTransportEquiv k
              (localLeviCivitaTangentTransport g p hC ⟨x, hVU hx⟩).symm
                (hA.toFiber g x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨Y, _, hY⟩ := exists_smoothVectorFieldFamily_localLeviCivitaTangentTransport
    g p hpU hC (stdOrthonormalBasis ℝ (TangentSpace I p))
  obtain ⟨V, hVsub, hVopen, hpV⟩ := mem_nhds_iff.mp
    (Filter.inter_mem (hU.mem_nhds hpU) hY)
  have hVU : V ⊆ U := fun x hx => (hVsub hx).1
  refine ⟨V, hVopen, hpV, hVU, Y, ?_⟩
  intro k A hA x hx
  exact tensorInSmoothFrame_eq_transport g p hC Y (hVU hx) hA
    ((hVsub hx).2 (hVU hx))

/-- **Math.** A jointly continuous family of tensor evaluations has a jointly
continuous representative in the centre Hilbert fibre, agreeing with canonical
inverse transport on one open neighborhood for all family parameters. -/
theorem exists_continuous_localLeviCivitaTensor_family
    (g : RiemannianMetric I M) (p : M) {U : Set M}
    (hU : IsOpen U) (hpU : p ∈ U)
    (hC : ∀ x ∈ U, ContMDiff 𝓘(ℝ, ℝ) I 1 (localTransportCurve (I := I) p x) ∧
      localTransportCurve (I := I) p x 0 = p ∧
      localTransportCurve (I := I) p x 1 = x)
    {T : Type*} [TopologicalSpace T] {k : ℕ} {A : T → CovTensorField I M k}
    (hA : ∀ t, IsCovariantTensorField (A t))
    (hcont : ∀ Z : Fin k → SmoothVectorField I M,
      Continuous (fun z : T × M => A z.1 Z z.2)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ∃ hVU : V ⊆ U,
      ∃ F : T → M → HilbertCovariantTensor k (TangentSpace I p),
        Continuous (Function.uncurry F) ∧ ∀ t x (hx : x ∈ V),
          F t x = WithLp.toLp 2 (covariantTensorTransportEquiv k
            (localLeviCivitaTangentTransport g p hC ⟨x, hVU hx⟩).symm
              ((hA t).toFiber g x)) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨V, hV, hpV, hVU, Y, hY⟩ := exists_localLeviCivitaTensor_frame g p hU hpU hC
  exact ⟨V, hV, hpV, hVU, (fun t x => tensorInSmoothFrame g p Y (A t) x),
    continuous_tensorInSmoothFrame g p Y hcont, fun t x hx => hY (hA t) x hx⟩

end MorganTianLib

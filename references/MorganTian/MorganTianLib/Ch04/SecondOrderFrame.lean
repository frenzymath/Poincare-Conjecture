import MorganTianLib.Ch04.NormalFrame
import MorganTianLib.Ch04.SecondOrderCorrection
import MorganTianLib.Ch04.TensorialApplications

/-!
# Second-order normal extensions at a point

Smooth quadratic corrections preserve prescribed vector values and first
covariant derivatives while cancelling the diagonal second derivatives used
by the tensor contact formula. This constructs pointwise jets only; local
carrier-preserving transport remains a separate input to the global tensor
maximum principle.

Blueprint: `thm:maximum-principle-tensors-global`.
-/

open Set Filter Function
open Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M] in
private theorem cov_sum_field (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) {ι : Type*} (s : Finset ι)
    (Y : ι → SmoothVectorField I M) :
    nabla.cov X (∑ i ∈ s, Y i) = ∑ i ∈ s, nabla.cov X (Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      ext p
      exact nabla.cov_zero_right X p
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, nabla.add_right, ih]

omit [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M] in
private theorem secondCov_sum_field (nabla : AffineConnection I M)
    (X : SmoothVectorField I M) {ι : Type*} (s : Finset ι)
    (Y : ι → SmoothVectorField I M) :
    secondCov nabla X X (∑ i ∈ s, Y i) =
      ∑ i ∈ s, secondCov nabla X X (Y i) := by
  unfold secondCov
  rw [cov_sum_field, cov_sum_field, cov_sum_field]
  ext p
  simp only [sumField_apply, SmoothVectorField.sub_apply, Finset.sum_sub_distrib]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M] in
private theorem secondCov_sub_field (nabla : AffineConnection I M)
    (X Y Z : SmoothVectorField I M) :
    secondCov nabla X X (Y - Z) =
      secondCov nabla X X Y - secondCov nabla X X Z := by
  have hsub : nabla.cov X (Y - Z) = nabla.cov X Y - nabla.cov X Z := by
    ext p
    exact nabla.cov_sub_right X Y Z p
  ext p
  simp only [secondCov_apply, SmoothVectorField.sub_apply, hsub, nabla.cov_sub_right]
  abel

/-- **Math.** Every tangent vector has a smooth extension with vanishing
first covariant derivative at the chosen point. -/
theorem exists_vectorField_value_cov_zero (g : RiemannianMetric I M) (p : M)
    (v : TangentSpace I p) :
    ∃ Z : SmoothVectorField I M, Z p = v ∧
      ∀ X : SmoothVectorField I M, (g.leviCivitaConnection.cov X Z) p = 0 := by
  obtain ⟨F, hON, hnormal⟩ := exists_isNormalFrameAt g p
  let c : Fin (Module.finrank ℝ E) → ℝ :=
    fun j => g.metricInner p v (F j p)
  let Z : SmoothVectorField I M := ∑ j,
    SmoothVectorField.smul (fun _ => c j) contMDiff_const (F j)
  refine ⟨Z, ?_, ?_⟩
  · change (∑ j, SmoothVectorField.smul (fun _ => c j) contMDiff_const (F j)) p = v
    rw [sumField_apply]
    simp only [SmoothVectorField.smul_apply]
    exact (metricInner_orthonormal_expansion g hON v).symm
  · intro X
    change (g.leviCivitaConnection.cov X
      (∑ j, SmoothVectorField.smul (fun _ => c j) contMDiff_const (F j))) p = 0
    rw [cov_sum_field, sumField_apply]
    apply Finset.sum_eq_zero
    intro j hj
    rw [g.leviCivitaConnection.leibniz]
    have hn : (g.leviCivitaConnection.cov X (F j)) p = 0 := by
      rw [g.leviCivitaConnection.cov_congr_apply_left (F j)
        (X' := extendVector p (X p)) (extendVector_apply p (X p)).symm]
      exact hnormal j (X p)
    rw [hn, dir_const]
    simp only [smul_zero, zero_smul, zero_add]

/-- **Math.** Smooth scalar coordinates with zero value and prescribed dual
derivatives against the orthonormal directions used by tensor contact. -/
theorem exists_scalar_contact_coordinates (g : RiemannianMetric I M) (p : M) :
    ∃ u : Fin (Module.finrank ℝ (TangentSpace I p)) → M → ℝ,
      (∀ j, ContMDiff I 𝓘(ℝ) ∞ (u j)) ∧
      (∀ j, u j p = 0) ∧
      ∀ i j, (canonicalContactFrame g p i).dir (u j) p =
        if i = j then (1 : ℝ) else 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  choose u hu hu0 hdu using fun j =>
    exists_contMDiff_prescribed_value_jet (I := I) p
      (InnerProductSpace.toDual ℝ (TangentSpace I p) (b j)) 0
  refine ⟨u, hu, hu0, ?_⟩
  intro i j
  change dirTangent (u j) ((canonicalContactFrame g p i) p) = _
  rw [hdu]
  simp only [canonicalContactFrame, extendVector_apply]
  change inner ℝ (b j) (b i) = _
  simpa only [eq_comm] using orthonormal_iff_ite.mp b.orthonormal j i

/-- **Math.** A tangent vector has a smooth extension whose first covariant
derivatives vanish at the point and whose diagonal second covariant
derivatives vanish in the canonical orthonormal directions. -/
theorem exists_vectorField_value_cov_secondCov_zero
    (g : RiemannianMetric I M) (p : M) (v : TangentSpace I p) :
    ∃ Y : SmoothVectorField I M, Y p = v ∧
      (∀ X : SmoothVectorField I M, (g.leviCivitaConnection.cov X Y) p = 0) ∧
      ∀ i, secondCov g.leviCivitaConnection (canonicalContactFrame g p i)
        (canonicalContactFrame g p i) Y p = 0 := by
  classical
  obtain ⟨Z, hZval, hZfirst⟩ := exists_vectorField_value_cov_zero g p v
  obtain ⟨u, hu, hu0, hdu⟩ := exists_scalar_contact_coordinates g p
  let W := fun i => secondCov g.leviCivitaConnection
    (canonicalContactFrame g p i) (canonicalContactFrame g p i) Z
  let C : SmoothVectorField I M := ∑ i, quadraticJetCorrection (u i) (hu i) (W i)
  refine ⟨Z - C, ?_, ?_, ?_⟩
  · change Z p - C p = v
    have hC : C p = 0 := by
      dsimp only [C]
      rw [sumField_apply]
      exact Finset.sum_eq_zero fun i hi =>
        quadraticJetCorrection_apply_of_eq_zero (hu i) (W i) (hu0 i)
    rw [hC, sub_zero, hZval]
  · intro X
    rw [g.leviCivitaConnection.cov_sub_right, hZfirst]
    have hC : (g.leviCivitaConnection.cov X C) p = 0 := by
      dsimp only [C]
      rw [cov_sum_field, sumField_apply]
      exact Finset.sum_eq_zero fun i hi =>
        cov_quadraticJetCorrection_of_eq_zero g.leviCivitaConnection X (W i)
          (hu i) (hu0 i)
    rw [hC, sub_self]
  · intro i
    rw [secondCov_sub_field, SmoothVectorField.sub_apply]
    have hC : secondCov g.leviCivitaConnection (canonicalContactFrame g p i)
        (canonicalContactFrame g p i) C p = W i p := by
      dsimp only [C]
      rw [secondCov_sum_field, sumField_apply]
      simp_rw [secondCov_quadraticJetCorrection_of_eq_zero
        g.leviCivitaConnection (canonicalContactFrame g p i) _ (hu _) (hu0 _), hdu]
      simp
    rw [hC]
    exact sub_self _

/-- **Math.** Any prescribed tuple of tangent vectors admits smooth extensions
with the first and second jets required by the tensor contact identity. -/
theorem exists_secondOrder_contact_tuple
    (g : RiemannianMetric I M) (p : M) {k : ℕ}
    (v : Fin k → TangentSpace I p) :
    ∃ Y : Fin k → SmoothVectorField I M,
      (∀ j, Y j p = v j) ∧
      (∀ i j, (g.leviCivitaConnection.cov
        (canonicalContactFrame g p i) (Y j)) p = 0) ∧
      ∀ i j, secondCov g.leviCivitaConnection (canonicalContactFrame g p i)
        (canonicalContactFrame g p i) (Y j) p = 0 := by
  choose Y hval hfirst hsecond using
    fun j => exists_vectorField_value_cov_secondCov_zero g p (v j)
  exact ⟨Y, hval, fun i j => hfirst j _, fun i j => hsecond j i⟩

/-- **Math.** The actual Riemann curvature evaluator has zero traced contact
defect on a smooth tuple extending any four prescribed tangent vectors. -/
theorem exists_riemannTensorField_contact_tuple
    (g : RiemannianMetric I M) (p : M)
    (v : Fin 4 → TangentSpace I p) :
    ∃ Y : Fin 4 → SmoothVectorField I M,
      (∀ j, Y j p = v j) ∧
      roughLaplacianContactDefect g g.leviCivitaConnection
        (riemannTensorField g) Y p = 0 := by
  obtain ⟨Y, hval, hfirst, hsecond⟩ := exists_secondOrder_contact_tuple g p v
  exact ⟨Y, hval,
    riemannTensorField_roughLaplacianContactDefect_eq_zero_of_pointwise_normal
      g Y p hfirst hsecond⟩

end MorganTianLib

#print axioms MorganTianLib.exists_secondOrder_contact_tuple
#print axioms MorganTianLib.exists_riemannTensorField_contact_tuple

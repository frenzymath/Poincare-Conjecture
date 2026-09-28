import MorganTianLib.Ch03.RicciFlow.HamiltonGauge

/-!
# Morgan--Tian Ch. 3 -- Ricci coefficient naturality adapters

The geometric part of the Hamilton gauge argument supplies a curvature-form
identity and transports an orthonormal frame through the time-dependent
diffeomorphism.  This file isolates the finite-dimensional trace step: the
Ricci bilinear form is then transported by a direct finite sum calculation.
The identity-diffeomorphism adapters provide the normalization case without
assuming any geometric naturality theorem.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Bundle Set Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

/-! ## The finite-dimensional trace step -/

theorem ricciBilin_naturality_of_basis_map
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] {ι : Type*} [Fintype ι]
    {B : V → V → V → V → ℝ} {B' : W → W → W → W → ℝ}
    (hB : IsAlgCurvatureForm B) (hB' : IsAlgCurvatureForm B')
    (e : OrthonormalBasis ι ℝ V) (e' : OrthonormalBasis ι ℝ W)
    (L : V →ₗ[ℝ] W)
    (hcurv : ∀ x y z w, B' (L x) (L y) (L z) (L w) = B x y z w)
    (hframe : ∀ i, e' i = L (e i)) (x y : V) :
    Riemannian.ricciBilin hB' (L x) (L y) =
      Riemannian.ricciBilin hB x y := by
  rw [Riemannian.ricciBilin_apply, Riemannian.ricciBilin_apply,
    Riemannian.ricciForm_eq_sum hB' _ _ e',
    Riemannian.ricciForm_eq_sum hB _ _ e]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hframe i]
  exact hcurv x (e i) y (e i)

/-! ## Identity pullback coefficients -/

theorem gaugePullbackRicciValue_refl (g : RiemannianMetric I M)
    (p : M) (v w : TangentSpace I p) :
    gaugePullbackRicciValue g (Diffeomorph.refl I M ∞) p v w =
      ricciTensorAt g p v w := by
  unfold gaugePullbackRicciValue
  rw [Diffeomorph.coe_refl]
  simp only [mfderiv_id]
  rfl

omit [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [SigmaCompactSpace M] [T2Space M] in
theorem isGaugePullbackOn_refl (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    IsGaugePullbackOn g g (fun _ => Diffeomorph.refl I M ∞) J := by
  intro t ht p v w
  exact (gaugePullbackValue_refl (g t) p v w).symm

theorem isRicciPullbackCompatible_refl (g : ℝ → RiemannianMetric I M) (J : Set ℝ) :
    IsRicciPullbackCompatible g g (fun _ => Diffeomorph.refl I M ∞) J := by
  intro t ht p v w
  exact (gaugePullbackRicciValue_refl (g t) p v w).symm

#print axioms ricciBilin_naturality_of_basis_map
#print axioms gaugePullbackRicciValue_refl
#print axioms isGaugePullbackOn_refl
#print axioms isRicciPullbackCompatible_refl

end MorganTianLib

end

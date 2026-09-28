import MorganTianLib.Ch03.RicciFlow.ScalarEvolution

/-!
# Morgan--Tian Ch. 4 - positive Ricci curvature gives positive scalar curvature

This finite-dimensional trace lemma supplies the initial-sign input for the
scalar minimum comparison.  It is independent of the still-open flow
endpoint and tensor-maximum-principle producers.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** Positive Ricci curvature implies positive scalar curvature.
The proof expands scalar curvature as the trace of the Ricci endomorphism and
uses positivity on the nonzero vectors of an orthonormal basis.
Blueprint: `claim:scalar-min-derivative-bound`.
-/
theorem scalarCurvatureAt_pos_of_ricciTensorAt_pos
    (g : RiemannianMetric I M) (p : M)
    (hLC : g.leviCivitaConnection.IsLeviCivita g)
    (hRic : ∀ v : TangentSpace I p, v ≠ 0 →
      0 < ricciTensorAt g p v v) :
    0 < scalarCurvatureAt g g.leviCivitaConnection hLC p := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let e := stdOrthonormalBasis ℝ (TangentSpace I p)
  rw [scalarCurvatureAt_eq_trace_ricciEndomorphismAt g p hLC,
    LinearMap.trace_eq_sum_inner _ e]
  have hn : 0 < Module.finrank ℝ (TangentSpace I p) := by
    change 0 < Module.finrank ℝ E
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))
  letI : Nontrivial (TangentSpace I p) := Module.finrank_pos_iff.mp hn
  have hne : Nonempty (Fin (Module.finrank ℝ (TangentSpace I p))) := by
    exact ⟨⟨0, hn⟩⟩
  letI := hne
  apply Finset.sum_pos
  intro i hi
  rw [real_inner_comm]
  change 0 < inner ℝ (ricciEndomorphismAt g p (e i)) (e i)
  rw [inner_ricciEndomorphismAt]
  apply hRic
  intro hei
  have hnorm : ‖e i‖ = 1 := by
    simpa using e.norm i
  rw [hei, norm_zero] at hnorm
  linarith
  exact Finset.univ_nonempty

end MorganTianLib

#print axioms MorganTianLib.scalarCurvatureAt_pos_of_ricciTensorAt_pos

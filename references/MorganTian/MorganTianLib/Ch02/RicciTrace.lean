import MorganTianLib.Ch01.CurvatureTensor
import MorganTianLib.Ch01.PointwiseCurvature

/-!
# Morgan–Tian Ch. 2 — the Ricci curvature as a trace of the curvature operator

The **Ricci pillar of the Bochner formula**: for any smooth vector field `X`
and any point `p`, summing the metric pairing
`⟨ℛ_MT(Eᵢ, X)X, Eᵢ⟩` of the Morgan–Tian curvature operator over an
orthonormal basis `{eᵢ}` of `(T_pM, g_p)` (each `eᵢ` extended to a global
field `Eᵢ`) yields exactly `Ric_p(X(p), X(p))`
(`sum_metricInner_riemannCurvature_self_eq_ricciAt`).

This is the identity by which the curvature term
`Σᵢ ⟨ℛ(Eᵢ, (∇f)^*)(∇f)^*, Eᵢ⟩` produced by commuting second covariant
derivatives of the gradient field (`MorganTianLib.secondCov_sub_swap`) becomes
the term `Ric((∇f)^*, (∇f)^*)` of the Bochner formula (blueprint
`lem:function-bochner-formula`).

The proof is pure bookkeeping between the conventions already established:
`⟨ℛ_MT(Eᵢ,X)X, Eᵢ⟩(p) = ℛ_MT(eᵢ, X(p), eᵢ, X(p))` by pointwise tensoriality
(`curvatureFormAt_eq`), the two pair antisymmetries move the arguments to
`ℛ_MT(X(p), eᵢ, X(p), eᵢ)`, and the orthonormal-basis formula for the Ricci
trace (`Riemannian.ricciForm_eq_sum`) identifies the sum with
`ricciAt g nabla hLC p (X p) (X p)`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 2
(blueprint `lem:function-bochner-formula`).
-/

open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The summand of the Ricci trace: for tangent vectors
`v, u ∈ T_pM`, the pairing `⟨ℛ_MT(V, U)U, V⟩(p)` — computed from any global
extensions `V, U` of `v, u` — equals the pointwise curvature tensor value
`ℛ_MT(u, v, u, v)`, by tensoriality and the two pair antisymmetries.
Blueprint: `lem:function-bochner-formula` (curvature term). -/
theorem metricInner_riemannCurvature_eq_curvatureFormAt [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hcompat : nabla.IsMetricCompatible g)
    (V U : SmoothVectorField I M) (p : M) :
    g.metricInner p ((riemannCurvature nabla V U U) p) (V p)
      = curvatureFormAt g nabla p (U p) (V p) (U p) (V p) := by
  have h : g.metricInner p ((riemannCurvature nabla V U U) p) (V p)
      = curvatureForm g nabla V U V U p := rfl
  rw [h, curvatureForm_eq g nabla hcompat V U V U p,
    ← curvatureFormAt_eq g nabla V U V U p,
    curvatureFormAt_antisymm_left g nabla p,
    curvatureFormAt_antisymm_right g nabla hcompat p, neg_neg]

/-- **Math.** **The Ricci curvature is the trace of the curvature operator**:
for a Levi-Civita connection, a smooth vector field `X`, a point `p`, and the
chosen orthonormal basis `{eᵢ}` of `(T_pM, g_p)` with global extensions
`Eᵢ = extendVector p eᵢ`,
`Σᵢ ⟨ℛ_MT(Eᵢ, X)X, Eᵢ⟩(p) = Ric_p(X(p), X(p))`.
This converts the curvature term produced by the Ricci commutation identity
into the Ricci term of the Bochner formula.
Blueprint: `lem:function-bochner-formula` (curvature term). -/
theorem sum_metricInner_riemannCurvature_self_eq_ricciAt [I.Boundaryless]
    (g : RiemannianMetric I M) {nabla : AffineConnection I M}
    (hLC : nabla.IsLeviCivita g) (X : SmoothVectorField I M) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∑ i, g.metricInner p
        ((riemannCurvature nabla
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) X X) p)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      = ricciAt g nabla hLC p (X p) (X p) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hsum : ∀ i, g.metricInner p
        ((riemannCurvature nabla
          (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) X X) p)
        (stdOrthonormalBasis ℝ (TangentSpace I p) i)
      = curvatureFormAt g nabla p (X p)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) (X p)
          (stdOrthonormalBasis ℝ (TangentSpace I p) i) := by
    intro i
    have h := metricInner_riemannCurvature_eq_curvatureFormAt g hLC.2
      (extendVector p (stdOrthonormalBasis ℝ (TangentSpace I p) i)) X p
    rw [extendVector_apply] at h
    exact h
  rw [Finset.sum_congr rfl fun i _ => hsum i]
  exact (ricciForm_eq_sum (isAlgCurvatureForm_curvatureFormAt g nabla hLC p)
    (X p) (X p) (stdOrthonormalBasis ℝ (TangentSpace I p))).symm

end MorganTianLib

end

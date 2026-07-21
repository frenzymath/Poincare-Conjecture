import DoCarmoLib.Riemannian.Manifold.DoCarmoCh6

/-!
# do Carmo Chapter 6 §2 — the Koszul formula for the induced connection

The induced connection `∇_X Y = (∇̄_X Y)ᵀ` of an immersed patch (`inducedCov`)
is, restricted to tangent fields, symmetric (`inducedCov_sub_swap`) and metric
compatible for the induced metric (`inducedCov_compat`). By the same argument
as do Carmo Ch. 2, Thm. 3.6 eq. (9), these two facts force `⟨Z, ∇_Y X⟩` to be
expressible purely in terms of the induced metric data on tangent fields —
inner products, directional derivatives, and Lie brackets of tangent fields —
with no reference to the ambient connection `∇̄` or to normal data. This is the
Koszul formula for the induced connection, and it is the precise sense in
which the induced connection, and hence the induced metric's intrinsic
geometry, is *intrinsic* to the patch: it is the engine behind
isometry-invariance results such as the Theorema Egregium (do Carmo Ch. 6 §3).

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2 (cf. Ch. 2, Thm. 3.6,
eq. (9)).
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
variable (nabla : AffineConnection I M)

/-- **Math.** do Carmo Ch. 6 §2, the **Koszul formula for the induced
connection**: for fields `X, Y, Z` tangent to the patch, the inner product
`⟨Z, ∇_Y X⟩` against the induced connection `∇ = inducedCov` is completely
determined by the induced metric and the Lie brackets of `X, Y, Z`:

`2⟨Z, ∇_Y X⟩ = X⟨Y,Z⟩ + Y⟨Z,X⟩ − Z⟨X,Y⟩ − ⟨[X,Z],Y⟩ − ⟨[Y,Z],X⟩ − ⟨[X,Y],Z⟩`,

where `X⟨Y,Z⟩` is the directional derivative of `p ↦ ⟨Y,Z⟩_p` along `X`
(`SmoothVectorField.dir`). The right-hand side mentions only `X, Y, Z`, the
metric `g`, and Lie brackets — none of the ambient connection `∇̄` or the
normal bundle — so for tangent fields this identity exhibits the induced
connection (hence, by uniqueness of the Levi-Civita connection, the whole
intrinsic geometry of the patch) as *intrinsic*: it depends only on the
induced metric, not on the embedding. This is the algebraic core of the
Theorema Egregium (do Carmo Ch. 6 §3). The statement is pointwise at `p`. -/
theorem inducedCov_koszul (hsym : nabla.IsSymmetric)
    (hcompat : nabla.IsMetricCompatible g)
    {X Y Z : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) (hZ : D.IsTangentField Z) (p : M) :
    2 * g.metricInner p (Z p) (D.inducedCov nabla Y X p)
      = X.dir (fun q => g.metricInner q (Y q) (Z q)) p
        + Y.dir (fun q => g.metricInner q (Z q) (X q)) p
        - Z.dir (fun q => g.metricInner q (X q) (Y q)) p
        - g.metricInner p (DCLieBracket X Z p) (Y p)
        - g.metricInner p (DCLieBracket Y Z p) (X p)
        - g.metricInner p (DCLieBracket X Y p) (Z p) := by
  -- metric compatibility of the induced connection for the three cyclic orderings.
  have e6 := D.inducedCov_compat nabla hcompat X hY hZ p
  have e7 := D.inducedCov_compat nabla hcompat Y hZ hX p
  have e8 := D.inducedCov_compat nabla hcompat Z hX hY p
  -- symmetry of the induced connection, rewritten pointwise as `[·,·] = ∇· − ∇·`.
  have hs1 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.inducedCov_sub_swap nabla hsym hX hY)
  have hs2 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.inducedCov_sub_swap nabla hsym hX hZ)
  have hs3 := congrArg (fun F : SmoothVectorField I M => F p)
    (D.inducedCov_sub_swap nabla hsym hY hZ)
  simp only [SmoothVectorField.sub_apply, bracketField_apply] at hs1 hs2 hs3
  have s1 : DCLieBracket X Y p
      = D.inducedCov nabla X Y p - D.inducedCov nabla Y X p := hs1.symm
  have s2 : DCLieBracket X Z p
      = D.inducedCov nabla X Z p - D.inducedCov nabla Z X p := hs2.symm
  have s3 : DCLieBracket Y Z p
      = D.inducedCov nabla Y Z p - D.inducedCov nabla Z Y p := hs3.symm
  -- expand the three bracket inner products via symmetry and bilinearity.
  have b1 : g.metricInner p (DCLieBracket X Y p) (Z p)
      = g.metricInner p (D.inducedCov nabla X Y p) (Z p)
        - g.metricInner p (D.inducedCov nabla Y X p) (Z p) := by
    rw [s1, g.metricInner_sub_left]
  have b2 : g.metricInner p (DCLieBracket X Z p) (Y p)
      = g.metricInner p (D.inducedCov nabla X Z p) (Y p)
        - g.metricInner p (D.inducedCov nabla Z X p) (Y p) := by
    rw [s2, g.metricInner_sub_left]
  have b3 : g.metricInner p (DCLieBracket Y Z p) (X p)
      = g.metricInner p (D.inducedCov nabla Y Z p) (X p)
        - g.metricInner p (D.inducedCov nabla Z Y p) (X p) := by
    rw [s3, g.metricInner_sub_left]
  -- symmetry of the metric to align the remaining inner products.
  have c1 := g.metricInner_comm p (Y p) (D.inducedCov nabla X Z p)
  have c2 := g.metricInner_comm p (X p) (D.inducedCov nabla Z Y p)
  have c3 := g.metricInner_comm p (Z p) (D.inducedCov nabla Y X p)
  linarith [e6, e7, e8, b1, b2, b3, c1, c2, c3]

end DCImmersedPatch

end Riemannian

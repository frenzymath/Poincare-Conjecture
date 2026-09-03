import Topping.RicciFlow.Existence.DeTurckSmoothness
import Topping.RicciFlow.Existence.DeTurckTensoriality

/-!
# Smooth components of the DeTurck one-form

The trace in `divergence` is computed with a pointwise chosen orthonormal
basis.  The pointwise multilinearity bridge in `TraceMultilinear` lets us
replace that basis, locally, by the smooth orthonormal frame supplied by
`MorganTianLib`.  Consequently smooth tensor components are preserved by a
covariant derivative and by metric trace.  The final declarations instantiate
this generic package for `delta G_g(T)` and expose the canonical smooth
DeTurck field needed by the reconstruction layer.
-/

open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
open Set Riemannian

noncomputable section

namespace Topping

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M] in
/-- **Math.** Smooth components are preserved by the displayed-slot covariant
derivative. -/
theorem hasSmoothComponents_covDeriv {k : ℕ}
    (A : CovTensorField I M k) (nabla : AffineConnection I M)
    (hA : HasSmoothComponents A) :
    HasSmoothComponents (covDeriv nabla A) := by
  intro Y
  have hY : Y = Fin.cons (Y 0) (fun i => Y i.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  rw [hY]
  have hEq : covDeriv nabla A (Fin.cons (Y 0) (fun i => Y i.succ)) =
      covDerivAlong nabla (Y 0) A (fun i => Y i.succ) := by
    funext p
    exact covDeriv_cons nabla A (Y 0) (fun i => Y i.succ) p
  rw [hEq]
  exact (hA.covDerivAlong nabla (Y 0)) (fun i => Y i.succ)

/-! A smooth local frame turns the pointwise trace into a finite sum of smooth
component functions. -/

/-- **Math.** If a tensor has smooth components and is pointwise multilinear,
its metric trace has smooth components. -/
theorem hasSmoothComponents_traceFirstTwo {k : ℕ}
    (g : RiemannianMetric I M) (A : CovTensorField I M (k + 2))
    (hA : HasSmoothComponents A)
    (hml : ∀ p : M, IsPointwiseMultilinear A p) :
    HasSmoothComponents (traceFirstTwo g A) := by
  intro Y p
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨F, hON⟩ := MorganTianLib.exists_orthonormalFrame g p
  have hsum : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (fun q => ∑ i, A (Fin.cons (F i) (Fin.cons (F i) Y)) q) := by
    exact MorganTianLib.contMDiff_fun_sum fun i _ =>
      hA (Fin.cons (F i) (Fin.cons (F i) Y))
  have hev : traceFirstTwo g A Y =ᶠ[𝓝 p]
      (fun q => ∑ i, A (Fin.cons (F i) (Fin.cons (F i) Y)) q) := by
    have hall : ∀ᶠ q in 𝓝 p, ∀ i j,
        g.metricInner q (F i q) (F j q) = if i = j then 1 else 0 :=
      (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun i =>
        (Filter.eventually_all (ι := Fin (Module.finrank ℝ E))).2 fun j => hON i j
    filter_upwards [hall] with q hq
    rw [traceFirstTwo_eq_sum_of_frame g (hml q) Y
      (MorganTianLib.frameOrthonormalBasis (I := I) g hq)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pointwiseValue]
    apply (hml q).tensorial
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [Fin.cons_zero]
      rw [MorganTianLib.extendVector_apply]
      exact MorganTianLib.frameOrthonormalBasis_apply (I := I) g hq i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_succ, Fin.cons_zero]
        rw [MorganTianLib.extendVector_apply]
        exact MorganTianLib.frameOrthonormalBasis_apply (I := I) g hq i
      · simp only [Fin.cons_succ]
        rw [MorganTianLib.extendVector_apply]
  exact (hsum p).congr_of_eventuallyEq hev

/-- **Math.** A smooth covariant two-tensor whose covariant derivative is
pointwise multilinear has a divergence with smooth components. -/
theorem hasSmoothComponents_divergence {A : CovTensorField I M 2}
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hA : HasSmoothComponents A)
    (hml : ∀ p : M, IsPointwiseMultilinear (covDeriv nabla A) p) :
    HasSmoothComponents (divergence g nabla A) := by
  intro Y
  change ContMDiff I 𝓘(ℝ, ℝ) ∞
    (fun q => -traceFirstTwo g (covDeriv nabla A) Y q)
  have hCD : HasSmoothComponents (covDeriv nabla A) :=
    hasSmoothComponents_covDeriv A nabla hA
  have htr : ContMDiff I 𝓘(ℝ, ℝ) ∞
      (traceFirstTwo g (covDeriv nabla A) Y) :=
    (hasSmoothComponents_traceFirstTwo g (covDeriv nabla A) hCD hml) Y
  exact htr.neg

/-! ### Canonical DeTurck section -/

/-- **Math.** The intrinsic DeTurck one-form has smooth components for every
pair of Riemannian metrics. -/
theorem hasSmoothComponents_deTurckOneForm
  (g T : RiemannianMetric I M) :
    HasSmoothComponents (deTurckOneForm g T) := by
  let htrace := contMDiff_trace₂_metricTensorField g T
  apply hasSmoothComponents_divergence g g.leviCivitaConnection
  · exact hasSmoothComponents_gravitationTensor_metricTensorField g T
  · intro p
    exact isPointwiseMultilinear_covDeriv_gravitationTensor g T htrace p

/-- **Math.** The canonical metric-dual DeTurck vector field is a smooth global
section, with no target-shaped smooth-field witness in its definition. -/
noncomputable def deTurckVectorFieldCanonical
    (g T : RiemannianMetric I M) : SmoothVectorField I M :=
  deTurckVectorFieldOfSmoothOneForm g T
    (fun p => isPointwiseMultilinear_deTurckOneForm g T p)
    (hasSmoothComponents_deTurckOneForm g T)

/-- **Math.** The canonical DeTurck vector field satisfies the metric-duality
equation used by the DeTurck modification. -/
theorem isDeTurckVectorFieldFor_deTurckVectorFieldCanonical
    (g T : RiemannianMetric I M) :
    IsDeTurckVectorFieldFor g T (deTurckVectorFieldCanonical g T) := by
  exact isDeTurckVectorFieldFor_deTurckVectorFieldOfSmoothOneForm g T
    (fun p => isPointwiseMultilinear_deTurckOneForm g T p)
    (hasSmoothComponents_deTurckOneForm g T)

#print axioms hasSmoothComponents_covDeriv
#print axioms hasSmoothComponents_traceFirstTwo
#print axioms hasSmoothComponents_divergence
#print axioms hasSmoothComponents_deTurckOneForm
#print axioms isDeTurckVectorFieldFor_deTurckVectorFieldCanonical

end Topping

end

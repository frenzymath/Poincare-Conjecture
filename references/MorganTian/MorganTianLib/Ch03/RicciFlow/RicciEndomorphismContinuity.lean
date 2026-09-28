import MorganTianLib.Ch03.RicciFlow.IntrinsicEvolvingTransport
import MorganTianLib.Ch03.RicciFlow.ScalarSpacetimeSmooth

/-!
# Temporal continuity of the intrinsic Ricci endomorphism

The fixed chart-basis coordinates of the Ricci endomorphism are the inverse
Gram matrix times the Ricci coefficients. Joint smoothness of those scalar
coefficients supplies continuity in the fixed tangent-fibre operator norm,
including endpoint times. Compactness then supplies the norm bound required
by the canonical Ricci transport construction.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology Bundle BigOperators NNReal Matrix

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace MorganTianLib

private theorem continuousOn_clm_of_basis
    {V W X ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W]
    [TopologicalSpace X] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ V) {f : X → V →L[ℝ] W} {S : Set X}
    (h : ∀ i, ContinuousOn (fun x => f x (b i)) S) : ContinuousOn f S := by
  let L : (ι → W) ≃L[ℝ] (V →L[ℝ] W) :=
    ((b.constr ℝ).trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := W))).toContinuousLinearEquiv
  have heval (A : V →L[ℝ] W) : L (fun i => A (b i)) = A := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    simp [L]
  simpa only [Function.comp_def, heval] using
    L.continuous.comp_continuousOn (continuousOn_pi.mpr h)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private theorem ricciEndomorphismAt_chart_repr
    (g : RiemannianMetric I M) (p : M)
    (hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet)
    (i l : Fin (Module.finrank ℝ E)) :
    (Tensor.chartBasisFamily (I := I) p hp).repr
        (ricciEndomorphismAt g p ((Tensor.chartBasisFamily (I := I) p hp) l)) i =
      ∑ j, Tensor.chartInvGramMatrix (I := I) g p p i j *
        ricciTensorAt g p ((Tensor.chartBasisFamily (I := I) p hp) l)
          ((Tensor.chartBasisFamily (I := I) p hp) j) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Tensor.chartBasisFamily (I := I) p hp
  let c : Fin (Module.finrank ℝ E) → ℝ := fun k =>
    b.repr (ricciEndomorphismAt g p (b l)) k
  let r : Fin (Module.finrank ℝ E) → ℝ := fun j => ricciTensorAt g p (b l) (b j)
  have hb (j : Fin (Module.finrank ℝ E)) :
      b j = Tensor.chartBasisVecFiber (I := I) p j p :=
    Tensor.chartBasisFamily_apply (I := I) p hp j
  have hGc : Tensor.chartGramMatrix (I := I) g p p *ᵥ c = r := by
    funext j
    have he := congrArg (fun v => (g.inner p (b j)) v)
      (b.sum_repr (ricciEndomorphismAt g p (b l)))
    simp only [map_sum, map_smul, smul_eq_mul] at he
    change ∑ k, Tensor.chartGramMatrix (I := I) g p p j k * c k = r j
    rw [show r j = (g.inner p (b j)) (ricciEndomorphismAt g p (b l)) by
      change ricciTensorAt g p (b l) (b j) =
        g.metricInner p (b j) (ricciEndomorphismAt g p (b l))
      rw [g.metricInner_comm, metricInner_ricciEndomorphismAt]]
    rw [← he]
    apply Finset.sum_congr rfl
    intro k _
    simp only [c, Tensor.chartGramMatrix_apply]
    rw [← hb j, ← hb k]
    ring
  have hinv := congrArg
    (fun v => Tensor.chartInvGramMatrix (I := I) g p p *ᵥ v) hGc
  rw [Matrix.mulVec_mulVec, Tensor.chartInvGramMatrix_mul_chartGramMatrix g p hp,
    Matrix.one_mulVec] at hinv
  exact congrFun hinv i

/-- **Math.** The intrinsic Ricci endomorphism of a smooth metric family is
continuous in the fixed tangent-fibre operator norm on the entire time set. -/
theorem ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hg : IsSmoothMetricFamilyOn g J) (p : M) :
    ContinuousOn (fun t => (ricciEndomorphismAt (g t) p : E →L[ℝ] E)) J := by
  classical
  have hp : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I) p
  have hpchart : p ∈ (extChartAt I p).source := mem_extChartAt_source p
  have hpy := (extChartAt I p).map_source hpchart
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    Tensor.chartBasisFamily (I := I) p hp
  have hb (j : Fin (Module.finrank ℝ E)) :
      b j = Tensor.chartBasisVecFiber (I := I) p j p :=
    Tensor.chartBasisFamily_apply (I := I) p hp j
  have hRic (l j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun t => ricciTensorAt (g t) p (b l) (b j)) J := by
    have hcoord := (contDiffOn_chartRicciCoefOnE_timeSpace hg p l j).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, hpy⟩)
    apply hcoord.congr
    intro t ht
    dsimp only [Function.comp_def, id_eq]
    rw [chartRicciCoefOnE_eq_ricciTensorAt_chartBasis (g t) p l j hpy,
      (extChartAt I p).left_inv hpchart]
    simp only [hb]
  have hInv (i j : Fin (Module.finrank ℝ E)) :
      ContinuousOn (fun t => Tensor.chartInvGramMatrix (I := I) (g t) p p i j) J := by
    have hcoord := (contDiffOn_chartInvGramOnE_timeSpace hg p i j).continuousOn.comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, hpy⟩)
    simpa only [Function.comp_def, id_eq, (extChartAt I p).left_inv hpchart] using hcoord
  apply continuousOn_clm_of_basis (V := E) (W := E) b
  intro l
  have hrepr : ContinuousOn
      (fun t => fun i => b.repr (ricciEndomorphismAt (g t) p (b l)) i) J := by
    apply continuousOn_pi.mpr
    intro i
    change ContinuousOn (fun t => b.repr (ricciEndomorphismAt (g t) p (b l)) i) J
    simp_rw [show ∀ t, b.repr (ricciEndomorphismAt (g t) p (b l)) i =
      ∑ j, Tensor.chartInvGramMatrix (I := I) (g t) p p i j *
        ricciTensorAt (g t) p (b l) (b j) from
      fun t => ricciEndomorphismAt_chart_repr (g t) p hp i l]
    exact continuousOn_finsetSum _ (fun j _ => (hInv i j).mul (hRic l j))
  let L : E ≃L[ℝ] (Fin (Module.finrank ℝ E) → ℝ) :=
    b.equivFun.toContinuousLinearEquiv
  have h := L.symm.continuous.comp_continuousOn hrepr
  have heq (t : ℝ) : L.symm (fun i => b.repr (ricciEndomorphismAt (g t) p (b l)) i) =
      ricciEndomorphismAt (g t) p (b l) := L.symm_apply_apply _
  simp only [Function.comp_def, heq] at h
  convert h using 1
  ext t
  rfl

/-- **Math.** On a compact time slab of a Ricci flow, the intrinsic Ricci
endomorphism has one uniform operator-norm bound. -/
theorem exists_ricciEndomorphismAt_nnnorm_bound_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (p : M) {a b : ℝ}
    (hJ : Icc a b ⊆ J) :
    ∃ K : ℝ≥0, ∀ s ∈ Icc a b,
      @nnnorm (E →L[ℝ] E) _ (ricciEndomorphismAt (g s) p) ≤ K := by
  have hcont := ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn
    hflow.smooth p
  have hcont' : ContinuousOn
      (fun s => @nnnorm (E →L[ℝ] E) _ (ricciEndomorphismAt (g s) p)) (Icc a b) :=
    hcont.mono hJ |>.nnnorm
  obtain ⟨K, hK⟩ := isCompact_Icc.bddAbove_image hcont'
  refine ⟨K, ?_⟩
  intro s hs
  exact hK ⟨s, hs, rfl⟩

/-- **Math.** Ricci transport preserves the evolving metric on a compact slab
of a Ricci flow, with continuity and boundedness discharged intrinsically. -/
theorem intrinsicEvolvingTransport_metricInner_eq_left_of_isRicciFlowOn
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) (p : M) {a b : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ J)
    (v w : E) {t : ℝ} (ht : t ∈ Icc a b) :
    (g t).metricInner p
      (evolvingTransportCurveOn (V := E)
        (fun r => ricciEndomorphismAt (g r) p) hab.le
        (ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn
          hflow.smooth p |>.mono hJ)
        (exists_ricciEndomorphismAt_nnnorm_bound_of_isRicciFlowOn
          hflow p hJ).choose_spec t v)
      (evolvingTransportCurveOn (V := E)
        (fun r => ricciEndomorphismAt (g r) p) hab.le
        (ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn
          hflow.smooth p |>.mono hJ)
        (exists_ricciEndomorphismAt_nnnorm_bound_of_isRicciFlowOn
          hflow p hJ).choose_spec t w) =
      (g a).metricInner p v w := by
  let hcont := ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn
    hflow.smooth p |>.mono hJ
  let hK := (exists_ricciEndomorphismAt_nnnorm_bound_of_isRicciFlowOn
    hflow p hJ).choose_spec
  simpa only [hcont] using intrinsicEvolvingTransport_metricInner_eq_left
    hflow p hab hJ hcont hK v w ht

end MorganTianLib

end

#print axioms MorganTianLib.ricciEndomorphismAt_continuousOn_of_isSmoothMetricFamilyOn
#print axioms MorganTianLib.exists_ricciEndomorphismAt_nnnorm_bound_of_isRicciFlowOn
#print axioms MorganTianLib.intrinsicEvolvingTransport_metricInner_eq_left_of_isRicciFlowOn

import MorganTianLib.Ch03.RicciFlow.Basic

/-!
# Morgan--Tian Ch. 3 -- interior metric derivative adapter

The Ricci-flow equation is recorded with a within-derivative on its time set.
At an interior time this is an ordinary derivative, which is the form needed
by the operator-valued transport and moving-frame calculus.
-/

open Set
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace MorganTianLib

section FiniteDimensional

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W]

/-- **Math.** Differentiability after evaluation determines the operator derivative on a
finite-dimensional domain. -/
theorem hasDerivWithinAt_clm_of_apply
    {f : ℝ → V →L[ℝ] W} {f' : V →L[ℝ] W} {J : Set ℝ} {t : ℝ}
    (h : ∀ v, HasDerivWithinAt (fun s => f s v) (f' v) J t) :
    HasDerivWithinAt f f' J t := by
  let b := Module.finBasis ℝ V
  let L : (Fin (Module.finrank ℝ V) → W) ≃L[ℝ] (V →L[ℝ] W) :=
    ((b.constr ℝ).trans
      (LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := V) (F' := W))).toContinuousLinearEquiv
  have heval (A : V →L[ℝ] W) : L (fun i => A (b i)) = A := by
    apply ContinuousLinearMap.coe_injective
    apply b.ext
    intro i
    simp [L]
  have hc : HasDerivWithinAt (fun s => fun i => f s (b i))
      (fun i => f' (b i)) J t :=
    hasDerivWithinAt_pi.mpr (fun i => h (b i))
  have hr := L.hasFDerivAt.comp_hasDerivWithinAt t hc
  change HasDerivWithinAt (fun s => L (fun i => f s (b i)))
    (L (fun i => f' (b i))) J t at hr
  simpa only [heval] using hr

end FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The Ricci bilinear form as a continuous bilinear map in the
fixed tangent-fibre topology. -/
def ricciContinuousBilinearAt (g : RiemannianMetric I M) (p : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let R : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := ricciTensorAt g p
  LinearMap.toContinuousLinearMap (E := E) (F' := E →L[ℝ] ℝ)
    ((LinearMap.toContinuousLinearMap (𝕜 := ℝ) (E := E) (F' := ℝ)).toLinearMap.comp R)

@[simp] theorem ricciContinuousBilinearAt_apply (g : RiemannianMetric I M) (p : M)
    (v w : TangentSpace I p) :
    ricciContinuousBilinearAt g p v w = ricciTensorAt g p v w := rfl

/-- **Math.** At an interior flow time, the metric pairing satisfies the
ordinary Ricci-flow derivative equation for every fixed tangent pair. -/
theorem IsRicciFlowOn.metricInner_hasDerivAt
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J)
    (p : M) (x y : TangentSpace I p) :
    HasDerivAt (fun s => (g s).metricInner p x y)
      (-2 * ricciTensorAt (g t) p x y) t := by
  exact (hflow.equation t (interior_subset ht) p x y).hasDerivAt
    (mem_interior_iff_mem_nhds.mp ht)

set_option backward.isDefEq.respectTransparency false in
/-- **Math.** The Ricci-flow equation holds in the normed space of continuous
bilinear forms on the tangent fibre, including one-sided time derivatives. -/
theorem IsRicciFlowOn.inner_hasDerivWithinAt
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ J) (p : M) :
    HasDerivWithinAt (fun s => ((g s).inner p : E →L[ℝ] E →L[ℝ] ℝ))
      ((-2 : ℝ) • ricciContinuousBilinearAt (g t) p) J t := by
  apply hasDerivWithinAt_clm_of_apply (V := E) (W := E →L[ℝ] ℝ)
  intro v
  apply hasDerivWithinAt_clm_of_apply (V := E) (W := ℝ)
  intro w
  convert hflow.equation t ht p v w using 1 <;> rfl

/-- **Math.** At an interior time the metric has the ordinary operator-valued
derivative needed by the moving-frame product rule. -/
theorem IsRicciFlowOn.inner_hasDerivAt
    {g : ℝ → RiemannianMetric I M} {J : Set ℝ}
    (hflow : IsRicciFlowOn g J) {t : ℝ} (ht : t ∈ interior J) (p : M) :
    HasDerivAt (fun s => ((g s).inner p : E →L[ℝ] E →L[ℝ] ℝ))
      ((-2 : ℝ) • ricciContinuousBilinearAt (g t) p) t := by
  exact @HasDerivWithinAt.hasDerivAt ℝ _ (E →L[ℝ] E →L[ℝ] ℝ) _ _ _ _ _ _
    (hflow.inner_hasDerivWithinAt (interior_subset ht) p)
    (mem_interior_iff_mem_nhds.mp ht)

end MorganTianLib

end

#print axioms MorganTianLib.IsRicciFlowOn.metricInner_hasDerivAt
#print axioms MorganTianLib.IsRicciFlowOn.inner_hasDerivWithinAt

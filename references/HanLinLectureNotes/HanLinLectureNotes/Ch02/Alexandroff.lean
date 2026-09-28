import HanLinLectureNotes.Ch02.AlexandroffContact
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Han--Lin Chapter 2: the weighted area inequality

The noninjective weighted area inequality needed for the analytic half of
Han--Lin Lemma 2.33.
-/

open Filter MeasureTheory MeasureTheory.Measure Set Topology
open scoped ENNReal

noncomputable section

namespace HanLinLectureNotes.Ch02

/-- The upper contact set of a `C^2` function on an open domain is Borel
measurable.  It is closed in the domain subtype: at a contact point the unique
supporting slope is the gradient, which varies continuously. -/
theorem measurableSet_upperContactSet
    {n : Nat} [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hu : ContDiffOn Real 2 u Omega) :
    MeasurableSet (upperContactSet Omega u) := by
  let S : Set Omega := ⋂ x : Omega, {y : Omega |
    u x <= u y + inner Real (gradient u y)
      ((x : Euclidean n) - (y : Euclidean n))}
  have hgrad : Continuous (fun y : Omega => gradient u y) := by
    rw [continuous_iff_continuousAt]
    intro y
    have huy : ContDiffAt Real 2 u y :=
      hu.contDiffAt (hOmegaOpen.mem_nhds y.property)
    have hf : ContinuousAt (fun z : Omega => fderiv Real u z) y :=
      (huy.continuousAt_fderiv (by norm_num)).comp_of_eq
        continuous_subtype_val.continuousAt rfl
    unfold gradient
    exact (InnerProductSpace.toDual Real (Euclidean n)).symm.continuous.continuousAt.comp hf
  have hSclosed : IsClosed S := by
    dsimp only [S]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    exact hu.continuousOn.restrict.add
      (hgrad.inner (continuous_const.sub continuous_subtype_val))
  have hEq : Subtype.val '' S = upperContactSet Omega u := by
    ext y
    constructor
    · rintro ⟨⟨y, hy⟩, hyS, rfl⟩
      refine ⟨hy, gradient u y, ?_⟩
      intro x hx
      have h := hyS
      simp only [S, mem_iInter, mem_setOf_eq] at h
      exact h ⟨x, hx⟩
    · rintro ⟨hy, p, hp⟩
      have hyInterior : y ∈ interior Omega := by
        simpa only [hOmegaOpen.interior_eq] using hy
      have huy : DifferentiableAt Real u y :=
        (hu y hy).contDiffAt (hOmegaOpen.mem_nhds hy) |>.differentiableAt (by norm_num)
      have hpgrad : p = gradient u y :=
        upperSupportingSlope_eq_gradient hyInterior huy hp
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      simp only [S, mem_iInter, mem_setOf_eq]
      intro x
      simpa only [hpgrad] using hp x x.property
  rw [← hEq]
  exact hOmegaOpen.measurableSet.subtype_image hSclosed.measurableSet

/-- The part of the upper contact set where `u` is strictly above its positive
boundary supremum is measurable. -/
theorem measurableSet_upperContactSet_strictSuperlevel
    {n : Nat} [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hu : ContDiffOn Real 2 u Omega) :
    MeasurableSet (upperContactSet Omega u ∩
      {y | boundaryPositiveSup Omega u < u y}) := by
  have hcontactMeasurable : MeasurableSet (upperContactSet Omega u) :=
    measurableSet_upperContactSet hOmegaOpen hu
  have hsuperOpen : IsOpen
      (Omega ∩ u ⁻¹' Ioi (boundaryPositiveSup Omega u)) :=
    ((continuousOn_open_iff hOmegaOpen).mp hu.continuousOn)
      (Ioi (boundaryPositiveSup Omega u)) isOpen_Ioi
  have hsetEq :
      upperContactSet Omega u ∩ {y | boundaryPositiveSup Omega u < u y} =
        upperContactSet Omega u ∩
          (Omega ∩ u ⁻¹' Ioi (boundaryPositiveSup Omega u)) := by
    ext y
    simp only [mem_inter_iff, mem_setOf_eq, mem_preimage, mem_Ioi]
    constructor
    · rintro ⟨hyContact, hyAboveBoundary⟩
      exact ⟨hyContact, hyContact.1, hyAboveBoundary⟩
    · rintro ⟨hyContact, _hyOmega, hyAboveBoundary⟩
      exact ⟨hyContact, hyAboveBoundary⟩
  rw [hsetEq]
  exact hcontactMeasurable.inter hsuperOpen.measurableSet

/-- In the standard orthonormal basis, the derivative of the gradient is the
Hessian matrix. -/
theorem toMatrix_fderiv_gradient_eq_hessianMatrix
    {n : Nat} {u : Euclidean n -> Real} {x : Euclidean n}
    (hu : ContDiffAt Real 2 u x) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) Real).toBasis
        (EuclideanSpace.basisFun (Fin n) Real).toBasis
        (fderiv Real (gradient u) x).toLinearMap =
      hessianMatrix u x := by
  apply Matrix.ext
  intro i j
  rw [LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply]
  simp only [OrthonormalBasis.coe_toBasis]
  simp only [hessianMatrix, LinearMap.BilinForm.toMatrix_apply, secondDerivativeBilin]
  simp only [OrthonormalBasis.coe_toBasis]
  change inner Real
      (EuclideanSpace.basisFun (Fin n) Real i)
      (fderiv Real (gradient u) x
        (EuclideanSpace.basisFun (Fin n) Real j)) =
    fderiv Real (fderiv Real u) x
      (EuclideanSpace.basisFun (Fin n) Real i)
      (EuclideanSpace.basisFun (Fin n) Real j)
  have hdg : DifferentiableAt Real (gradient u) x := by
    unfold gradient
    exact (InnerProductSpace.toDual Real (Euclidean n)).symm.differentiableAt.comp x
      ((hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
  have hleft :
      fderiv Real (fun y => inner Real (gradient u y)
        (EuclideanSpace.basisFun (Fin n) Real i)) x
          (EuclideanSpace.basisFun (Fin n) Real j) =
        inner Real
          (fderiv Real (gradient u) x
            (EuclideanSpace.basisFun (Fin n) Real j))
          (EuclideanSpace.basisFun (Fin n) Real i) := by
    rw [(hdg.hasFDerivAt.inner Real
      (hasFDerivAt_const (EuclideanSpace.basisFun (Fin n) Real i) x)).fderiv]
    simp
  rw [real_inner_comm, ← hleft]
  rw [show (fun y => inner Real (gradient u y)
      (EuclideanSpace.basisFun (Fin n) Real i)) =
      fun y => fderiv Real u y
        (EuclideanSpace.basisFun (Fin n) Real i) by
        funext y
        exact inner_gradient_left]
  rw [fderiv_apply_eq_fderiv_fderiv hu]
  exact hu.isSymmSndFDerivAt (by norm_num) _ _

/-- The absolute Jacobian of the gradient is the absolute determinant of the
Hessian matrix. -/
theorem det_fderiv_gradient_eq_det_hessianMatrix
    {n : Nat} {u : Euclidean n -> Real} {x : Euclidean n}
    (hu : ContDiffAt Real 2 u x) :
    (fderiv Real (gradient u) x).det = (hessianMatrix u x).det := by
  calc
    (fderiv Real (gradient u) x).det =
        (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) Real).toBasis
          (EuclideanSpace.basisFun (Fin n) Real).toBasis
          (fderiv Real (gradient u) x).toLinearMap).det :=
      (LinearMap.det_toMatrix _ _).symm
    _ = (hessianMatrix u x).det :=
      congrArg Matrix.det (toMatrix_fderiv_gradient_eq_hessianMatrix hu)

/-- The measure of the image of a differentiable map is dominated by the
pushforward of its absolute-Jacobian measure. Injectivity is not required. -/
theorem restrict_image_le_map_withDensity_abs_det_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsAddHaarMeasure mu]
    {s : Set E} {f : E -> E} {f' : E → E →L[Real] E}
    (hs : MeasurableSet s) (hf : Measurable f)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) :
    mu.restrict (f '' s) <=
      Measure.map f
        ((mu.restrict s).withDensity fun x => ENNReal.ofReal |(f' x).det|) := by
  apply Measure.le_iff.2
  intro t ht
  rw [Measure.restrict_apply ht, Measure.map_apply hf ht,
    withDensity_apply _ (hf ht), Measure.restrict_restrict (hf ht)]
  have harea := addHaar_image_le_lintegral_abs_det_fderiv mu
    ((hf ht).inter hs)
    (fun x hx => (hf' x hx.2).mono inter_subset_right)
  simpa only [image_preimage_inter] using harea

/-- Weighted area inequality for a differentiable map, without an injectivity
hypothesis. This is the measure-theoretic inequality used after proving that
the Alexandroff slope ball lies in the gradient image of the upper contact set. -/
theorem lintegral_image_le_lintegral_abs_det_fderiv_mul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) [IsAddHaarMeasure mu]
    {s : Set E} {f : E -> E} {f' : E → E →L[Real] E}
    (hs : MeasurableSet s) (hf : Measurable f)
    (hf' : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x)
    {g : E -> ENNReal} (hg : Measurable g) :
    (∫⁻ y in f '' s, g y ∂mu) <=
      ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂mu := by
  let jac : E -> ENNReal := fun x => ENNReal.ofReal |(f' x).det|
  have hjac : AEMeasurable jac (mu.restrict s) := by
    exact aemeasurable_ofReal_abs_det_fderivWithin mu hs hf'
  have hgf : AEMeasurable (fun x => g (f x)) (mu.restrict s) :=
    (hg.comp hf).aemeasurable
  have hmeasure :=
    restrict_image_le_map_withDensity_abs_det_fderiv mu hs hf hf'
  calc
    (∫⁻ y in f '' s, g y ∂mu) =
        ∫⁻ y, g y ∂mu.restrict (f '' s) := rfl
    _ <= ∫⁻ y, g y ∂Measure.map f ((mu.restrict s).withDensity jac) :=
      lintegral_mono' hmeasure le_rfl
    _ = ∫⁻ x, g (f x) ∂((mu.restrict s).withDensity jac) :=
      lintegral_map hg hf
    _ = ∫⁻ x in s, ENNReal.ofReal |(f' x).det| * g (f x) ∂mu := by
      rw [lintegral_withDensity_eq_lintegral_mul₀ hjac hgf]
      rfl

/-- The weighted area inequality on the Alexandroff slope ball and upper
contact set, in extended-integral form. -/
theorem lintegral_alexandroffSlopeBall_le_upperContactSet
    {n : Nat} [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    {g : Euclidean n -> ENNReal} (hg : Measurable g) :
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u), g p ∂mu) <=
      ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal |(hessianMatrix u x).det| * g (gradient u x) ∂mu := by
  let gradOn : Omega -> Euclidean n := fun x => gradient u x
  let gradExt : Euclidean n -> Euclidean n :=
    Function.extend Subtype.val gradOn (fun _ => 0)
  have hgradOn : Continuous gradOn := by
    rw [continuous_iff_continuousAt]
    intro y
    have huy : ContDiffAt Real 2 u y :=
      hu.contDiffAt (hOmegaOpen.mem_nhds y.property)
    have hf : ContinuousAt (fun z : Omega => fderiv Real u z) y :=
      (huy.continuousAt_fderiv (by norm_num)).comp_of_eq
        continuous_subtype_val.continuousAt rfl
    unfold gradOn gradient
    exact (InnerProductSpace.toDual Real (Euclidean n)).symm.continuous.continuousAt.comp hf
  have hgradExtMeasurable : Measurable gradExt := by
    apply (MeasurableEmbedding.subtype_coe hOmegaOpen.measurableSet).measurable_extend
    · exact hgradOn.measurable
    · exact measurable_const
  have hgradExtOn : ∀ x, x ∈ Omega -> gradExt x = gradient u x := by
    intro x hx
    have hcomp := Function.extend_comp
      (f := @Subtype.val (Euclidean n) (fun x => x ∈ Omega))
      Subtype.val_injective gradOn (fun _ : Euclidean n => 0)
    exact congrFun hcomp ⟨x, hx⟩
  have hcontactMeasurable : MeasurableSet (upperContactSet Omega u) :=
    measurableSet_upperContactSet hOmegaOpen hu
  have hgradExtDeriv :
      ∀ x, x ∈ upperContactSet Omega u ->
        HasFDerivWithinAt gradExt (fderiv Real (gradient u) x)
          (upperContactSet Omega u) x := by
    intro x hx
    have hxOmega : x ∈ Omega := hx.1
    have hux : ContDiffAt Real 2 u x :=
      hu.contDiffAt (hOmegaOpen.mem_nhds hxOmega)
    have hdg : DifferentiableAt Real (gradient u) x := by
      unfold gradient
      exact (InnerProductSpace.toDual Real (Euclidean n)).symm.differentiableAt.comp x
        ((hux.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    have heq : gradExt =ᶠ[nhds x] gradient u := by
      filter_upwards [hOmegaOpen.mem_nhds hxOmega] with y hy
      exact hgradExtOn y hy
    exact (hdg.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have himage :
      gradExt '' upperContactSet Omega u =
        gradient u '' upperContactSet Omega u :=
    Set.image_congr fun x hx => hgradExtOn x hx.1
  have harea := lintegral_image_le_lintegral_abs_det_fderiv_mul
    mu hcontactMeasurable hgradExtMeasurable hgradExtDeriv hg
  rw [himage] at harea
  have hareaRhs :
      (∫⁻ x in upperContactSet Omega u,
          ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
            g (gradExt x) ∂mu) =
        ∫⁻ x in upperContactSet Omega u,
          ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
            g (gradient u x) ∂mu := by
    apply setLIntegral_congr_fun hcontactMeasurable
    intro x hx
    change ENNReal.ofReal |(fderiv Real (gradient u) x).det| * g (gradExt x) =
      ENNReal.ofReal |(fderiv Real (gradient u) x).det| * g (gradient u x)
    rw [hgradExtOn x hx.1]
  rw [hareaRhs] at harea
  have hdu : ∀ y, y ∈ Omega -> DifferentiableAt Real u y := by
    intro y hy
    exact ((hu y hy).contDiffAt (hOmegaOpen.mem_nhds hy)).differentiableAt
      (by norm_num)
  have hslope :
      Metric.ball 0 (alexandroffSlopeRadius Omega u) ⊆
        gradient u '' upperContactSet Omega u := by
    intro p hp
    rcases exists_interior_upperContact_of_mem_alexandroffSlopeBall
        hOmegaOpen hOmegaNe hOmegaBdd huClosure hp with
      ⟨y, hyInterior, hyContact, hsupport⟩
    have hyOmega : y ∈ Omega := hOmegaOpen.interior_eq ▸ hyInterior
    have hpGradient : p = gradient u y :=
      upperSupportingSlope_eq_gradient hyInterior (hdu y hyOmega) hsupport
    exact ⟨y, hyContact, hpGradient.symm⟩
  calc
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u), g p ∂mu) <=
        ∫⁻ p in gradient u '' upperContactSet Omega u, g p ∂mu :=
      lintegral_mono_set hslope
    _ <= ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
          g (gradient u x) ∂mu := harea
    _ = ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal |(hessianMatrix u x).det| *
          g (gradient u x) ∂mu := by
      apply setLIntegral_congr_fun hcontactMeasurable
      intro x hx
      change ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
          g (gradient u x) =
        ENNReal.ofReal |(hessianMatrix u x).det| * g (gradient u x)
      rw [det_fderiv_gradient_eq_det_hessianMatrix
        (hu.contDiffAt (hOmegaOpen.mem_nhds hx.1))]

/-- The weighted area inequality with the integration domain restricted to
contact points where `u` is strictly above its positive boundary supremum. -/
theorem lintegral_alexandroffSlopeBall_le_upperContactSet_strictSuperlevel
    {n : Nat} [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    {g : Euclidean n -> ENNReal} (hg : Measurable g) :
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u), g p ∂mu) <=
      ∫⁻ x in upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y},
        ENNReal.ofReal |(hessianMatrix u x).det| * g (gradient u x) ∂mu := by
  let gradOn : Omega -> Euclidean n := fun x => gradient u x
  let gradExt : Euclidean n -> Euclidean n :=
    Function.extend Subtype.val gradOn (fun _ => 0)
  have hgradOn : Continuous gradOn := by
    rw [continuous_iff_continuousAt]
    intro y
    have huy : ContDiffAt Real 2 u y :=
      hu.contDiffAt (hOmegaOpen.mem_nhds y.property)
    have hf : ContinuousAt (fun z : Omega => fderiv Real u z) y :=
      (huy.continuousAt_fderiv (by norm_num)).comp_of_eq
        continuous_subtype_val.continuousAt rfl
    unfold gradOn gradient
    exact (InnerProductSpace.toDual Real (Euclidean n)).symm.continuous.continuousAt.comp hf
  have hgradExtMeasurable : Measurable gradExt := by
    apply (MeasurableEmbedding.subtype_coe hOmegaOpen.measurableSet).measurable_extend
    · exact hgradOn.measurable
    · exact measurable_const
  have hgradExtOn : ∀ x, x ∈ Omega -> gradExt x = gradient u x := by
    intro x hx
    have hcomp := Function.extend_comp
      (f := @Subtype.val (Euclidean n) (fun x => x ∈ Omega))
      Subtype.val_injective gradOn (fun _ : Euclidean n => 0)
    exact congrFun hcomp ⟨x, hx⟩
  have hstrictContactMeasurable :
      MeasurableSet (upperContactSet Omega u ∩
        {y | boundaryPositiveSup Omega u < u y}) :=
    measurableSet_upperContactSet_strictSuperlevel hOmegaOpen hu
  have hgradExtDeriv :
      ∀ x, x ∈ upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y} ->
        HasFDerivWithinAt gradExt (fderiv Real (gradient u) x)
          (upperContactSet Omega u ∩
            {y | boundaryPositiveSup Omega u < u y}) x := by
    intro x hx
    have hxOmega : x ∈ Omega := hx.1.1
    have hux : ContDiffAt Real 2 u x :=
      hu.contDiffAt (hOmegaOpen.mem_nhds hxOmega)
    have hdg : DifferentiableAt Real (gradient u) x := by
      unfold gradient
      exact (InnerProductSpace.toDual Real (Euclidean n)).symm.differentiableAt.comp x
        ((hux.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero)
    have heq : gradExt =ᶠ[nhds x] gradient u := by
      filter_upwards [hOmegaOpen.mem_nhds hxOmega] with y hy
      exact hgradExtOn y hy
    exact (hdg.hasFDerivAt.congr_of_eventuallyEq heq).hasFDerivWithinAt
  have himage :
      gradExt '' (upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y}) =
        gradient u '' (upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y}) :=
    Set.image_congr fun x hx => hgradExtOn x hx.1.1
  have harea := lintegral_image_le_lintegral_abs_det_fderiv_mul
    mu hstrictContactMeasurable hgradExtMeasurable hgradExtDeriv hg
  rw [himage] at harea
  have hareaRhs :
      (∫⁻ x in upperContactSet Omega u ∩
            {y | boundaryPositiveSup Omega u < u y},
          ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
            g (gradExt x) ∂mu) =
        ∫⁻ x in upperContactSet Omega u ∩
            {y | boundaryPositiveSup Omega u < u y},
          ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
            g (gradient u x) ∂mu := by
    apply setLIntegral_congr_fun hstrictContactMeasurable
    intro x hx
    change ENNReal.ofReal |(fderiv Real (gradient u) x).det| * g (gradExt x) =
      ENNReal.ofReal |(fderiv Real (gradient u) x).det| * g (gradient u x)
    rw [hgradExtOn x hx.1.1]
  rw [hareaRhs] at harea
  have hdu : ∀ y, y ∈ Omega -> DifferentiableAt Real u y := by
    intro y hy
    exact ((hu y hy).contDiffAt (hOmegaOpen.mem_nhds hy)).differentiableAt
      (by norm_num)
  have hslope :
      Metric.ball 0 (alexandroffSlopeRadius Omega u) ⊆
        gradient u '' (upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y}) :=
    alexandroffSlopeBall_subset_gradient_image_upperContactSet_strictSuperlevel
      hOmegaOpen hOmegaNe hOmegaBdd huClosure hdu
  calc
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u), g p ∂mu) <=
        ∫⁻ p in gradient u '' (upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y}), g p ∂mu :=
      lintegral_mono_set hslope
    _ <= ∫⁻ x in upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y},
        ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
          g (gradient u x) ∂mu := harea
    _ = ∫⁻ x in upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y},
        ENNReal.ofReal |(hessianMatrix u x).det| *
          g (gradient u x) ∂mu := by
      apply setLIntegral_congr_fun hstrictContactMeasurable
      intro x hx
      change ENNReal.ofReal |(fderiv Real (gradient u) x).det| *
          g (gradient u x) =
        ENNReal.ofReal |(hessianMatrix u x).det| * g (gradient u x)
      rw [det_fderiv_gradient_eq_det_hessianMatrix
        (hu.contDiffAt (hOmegaOpen.mem_nhds hx.1.1))]

/-- Han--Lin Lemma 2.33. A nonnegative locally integrable weight on the
Alexandroff slope ball is bounded by its Hessian-Jacobian integral over the
upper contact set. The integrals are lower Lebesgue integrals, which retain the
possible infinite value on the right. -/
theorem alexandroff_weighted_contact_integral
    {n : Nat} [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    {g : Euclidean n -> Real} (hg : Measurable g)
    (hgNonneg : ∀ p, 0 <= g p)
    (_hgLocal : LocallyIntegrable g mu) :
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u),
        ENNReal.ofReal (g p) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal
          (g (gradient u x) * |(hessianMatrix u x).det|) ∂mu := by
  calc
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u),
        ENNReal.ofReal (g p) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal |(hessianMatrix u x).det| *
          ENNReal.ofReal (g (gradient u x)) ∂mu :=
      lintegral_alexandroffSlopeBall_le_upperContactSet
        mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu hg.ennreal_ofReal
    _ = ∫⁻ x in upperContactSet Omega u,
        ENNReal.ofReal
          (g (gradient u x) * |(hessianMatrix u x).det|) ∂mu := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul (hgNonneg (gradient u x)), mul_comm]

/-- The weighted contact integral restricted to points where `u` lies strictly
above its positive boundary supremum. -/
theorem alexandroff_weighted_contact_integral_strictSuperlevel
    {n : Nat} [MeasurableSpace (Euclidean n)] [BorelSpace (Euclidean n)]
    (mu : Measure (Euclidean n)) [IsAddHaarMeasure mu]
    {Omega : Set (Euclidean n)} {u : Euclidean n -> Real}
    (hOmegaOpen : IsOpen Omega) (hOmegaNe : Omega.Nonempty)
    (hOmegaBdd : Bornology.IsBounded Omega)
    (huClosure : ContinuousOn u (closure Omega))
    (hu : ContDiffOn Real 2 u Omega)
    {g : Euclidean n -> Real} (hg : Measurable g)
    (hgNonneg : ∀ p, 0 <= g p)
    (_hgLocal : LocallyIntegrable g mu) :
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u),
        ENNReal.ofReal (g p) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y},
        ENNReal.ofReal
          (g (gradient u x) * |(hessianMatrix u x).det|) ∂mu := by
  calc
    (∫⁻ p in Metric.ball 0 (alexandroffSlopeRadius Omega u),
        ENNReal.ofReal (g p) ∂mu) <=
      ∫⁻ x in upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y},
        ENNReal.ofReal |(hessianMatrix u x).det| *
          ENNReal.ofReal (g (gradient u x)) ∂mu :=
      lintegral_alexandroffSlopeBall_le_upperContactSet_strictSuperlevel
        mu hOmegaOpen hOmegaNe hOmegaBdd huClosure hu hg.ennreal_ofReal
    _ = ∫⁻ x in upperContactSet Omega u ∩
          {y | boundaryPositiveSup Omega u < u y},
        ENNReal.ofReal
          (g (gradient u x) * |(hessianMatrix u x).det|) ∂mu := by
      apply lintegral_congr
      intro x
      rw [ENNReal.ofReal_mul (hgNonneg (gradient u x)), mul_comm]

end HanLinLectureNotes.Ch02

import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import MorganTianLib.Ch01.Metric

/-!
# Poincaré Ch. 1, §1.1 — The Levi-Civita connection

Restates Morgan–Tian's Levi-Civita theorem (blueprint
`thm:levi-civita-connection`): given a Riemannian metric `g` on `M` there
uniquely exists a torsion-free connection making `g` parallel. This is
exactly DoCarmoLib's `Riemannian.RiemannianMetric.exists_unique_isLeviCivita`,
where `IsLeviCivita g nabla` packages the torsion-free ("symmetric") and
metric-compatible conditions.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.1
(blueprint `thm:levi-civita-connection`).
-/

open scoped ContDiff Manifold Topology Bundle

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-- **Math.** The **Levi-Civita theorem**: given a Riemannian metric `g` on `M`,
there uniquely exists a torsion-free connection `∇` on `TM` making `g` parallel,
i.e. an affine connection that is both symmetric (torsion-free) and compatible
with the metric `g` (`nabla.IsLeviCivita g`). Direct reuse of
`Riemannian.RiemannianMetric.exists_unique_isLeviCivita`.

Blueprint: `thm:levi-civita-connection`. -/
theorem existsUnique_leviCivita (g : Riemannian.RiemannianMetric I M) :
    ∃! nabla : Riemannian.AffineConnection I M, nabla.IsLeviCivita g :=
  g.exists_unique_isLeviCivita

end MorganTianLib

namespace MorganTianLib

open Set Filter Riemannian TopologicalSpace

section GeneralModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

/-! ## Levi-Civita without a model-space inner product

The Riemannian metric supplies the fibrewise Riesz isomorphism needed by the
Koszul construction. No inner product on the manifold's model space is needed.
This matters for product manifolds, whose standard model carries the max norm.
-/

/-- **Math.** The Koszul-dual section is smooth on any finite-dimensional complete normed
model. This is the relaxed form of DoCarmoLib's smoothness theorem: its proof
uses only the Riemannian metric's fibrewise Riesz isomorphism. -/
theorem koszulDualSection_contMDiffAt_general (g : RiemannianMetric I M)
    (X Y : SmoothVectorField I M) (p : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y => (⟨y, g.koszulDualSection X Y y⟩ : TangentBundle I M)) p := by
  have hx : p ∈ (trivializationAt E (TangentSpace I) p).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' p
  have hbaseopen : IsOpen (trivializationAt E (TangentSpace I) p).baseSet :=
    (trivializationAt E (TangentSpace I) p).open_baseSet
  refine Tensor.metricRiesz_section_contMDiffAt_of_within g (α := p) hx
    (Φ := fun y => (1 / 2 : ℝ) • g.koszulCovec X Y y) ?_
  intro j
  obtain ⟨Z, hZ⟩ := exists_smoothVectorField_eventuallyEq (I := I)
    (σ := fun q => Tensor.chartBasisVecFiber (I := I) p j q)
    (s := (trivializationAt E (TangentSpace I) p).baseSet) hbaseopen
    (Tensor.chartBasisVec_contMDiffOn (I := I) p j) hx
  have hsmooth : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ (g.koszulRHS X Y Z)
      (trivializationAt E (TangentSpace I) p).baseSet p :=
    (g.koszulRHS_contMDiff X Y Z p).contMDiffWithinAt
  have heq :
      (fun y => g.koszulCovec X Y y (Tensor.chartBasisVecFiber (I := I) p j y))
        =ᶠ[nhds p] (fun y => g.koszulRHS X Y Z y) := by
    filter_upwards [hZ] with y hy
    rw [← hy]
    exact g.koszulCovec_apply X Y Z y
  have hcrux : ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞
      (fun y => g.koszulCovec X Y y (Tensor.chartBasisVecFiber (I := I) p j y))
      (trivializationAt E (TangentSpace I) p).baseSet p :=
    hsmooth.congr_of_eventuallyEq
      (heq.filter_mono nhdsWithin_le_nhds) heq.self_of_nhds
  simp only [smul_apply, smul_eq_mul]
  exact (contMDiffWithinAt_const).mul hcrux

/-- **Math.** The Koszul covariant derivative, bundled as a smooth vector field without
an inner-product-space assumption on the model. -/
noncomputable def leviCivitaCovFieldGeneral (g : RiemannianMetric I M)
    (A B : SmoothVectorField I M) : SmoothVectorField I M where
  toFun := fun p => g.koszulDualSection B A p
  smooth := fun p => koszulDualSection_contMDiffAt_general g B A p

@[simp] theorem leviCivitaCovFieldGeneral_apply (g : RiemannianMetric I M)
    (A B : SmoothVectorField I M) (p : M) :
    leviCivitaCovFieldGeneral g A B p = g.koszulDualSection B A p :=
  rfl

/-- **Math.** The Levi-Civita connection supplied by the Koszul construction for an
arbitrary finite-dimensional complete normed model. -/
noncomputable def leviCivitaConnectionGeneral (g : RiemannianMetric I M) :
    AffineConnection I M where
  cov := fun A B => leviCivitaCovFieldGeneral g A B
  add_left := by
    intro X Y Z
    refine SmoothVectorField.ext (fun p => ?_)
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p (g.koszulDualSection Z (X + Y) p) (W p)
      = g.metricInner p ((leviCivitaCovFieldGeneral g X Z
          + leviCivitaCovFieldGeneral g Y Z) p) (W p)
    rw [SmoothVectorField.add_apply, g.metricInner_add_left]
    have hL := g.koszulDualSection_dual Z (X + Y) W p
    have hX := g.koszulDualSection_dual Z X W p
    have hY := g.koszulDualSection_dual Z Y W p
    have hk := g.koszulRHS_add_middle Z X Y W p
    show g.metricInner p (g.koszulDualSection Z (X + Y) p) (W p)
      = g.metricInner p (g.koszulDualSection Z X p) (W p)
        + g.metricInner p (g.koszulDualSection Z Y p) (W p)
    linarith [hL, hX, hY, hk]
  smul_left := by
    intro f hf X Z
    refine SmoothVectorField.ext (fun p => ?_)
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p
        (g.koszulDualSection Z (SmoothVectorField.smul f hf X) p) (W p)
      = g.metricInner p
          ((SmoothVectorField.smul f hf (leviCivitaCovFieldGeneral g X Z)) p) (W p)
    rw [SmoothVectorField.smul_apply, g.metricInner_smul_left]
    have hL := g.koszulDualSection_dual Z (SmoothVectorField.smul f hf X) W p
    have hX := g.koszulDualSection_dual Z X W p
    have hk := g.koszulRHS_smul_middle hf Z X W p
    show g.metricInner p
        (g.koszulDualSection Z (SmoothVectorField.smul f hf X) p) (W p)
      = f p * g.metricInner p (g.koszulDualSection Z X p) (W p)
    linear_combination (1 / 2 : ℝ) * hL + (1 / 2 : ℝ) * hk - (f p / 2) * hX
  add_right := by
    intro X Y Z
    refine SmoothVectorField.ext (fun p => ?_)
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p (g.koszulDualSection (Y + Z) X p) (W p)
      = g.metricInner p ((leviCivitaCovFieldGeneral g X Y
          + leviCivitaCovFieldGeneral g X Z) p) (W p)
    rw [SmoothVectorField.add_apply, g.metricInner_add_left]
    have hL := g.koszulDualSection_dual (Y + Z) X W p
    have hY := g.koszulDualSection_dual Y X W p
    have hZ := g.koszulDualSection_dual Z X W p
    have hk := g.koszulRHS_add_left Y Z X W p
    show g.metricInner p (g.koszulDualSection (Y + Z) X p) (W p)
      = g.metricInner p (g.koszulDualSection Y X p) (W p)
        + g.metricInner p (g.koszulDualSection Z X p) (W p)
    linarith [hL, hY, hZ, hk]
  leibniz := by
    intro f hf X Y p
    refine (g.metricInner_eq_iff_eq p _ _).mp (fun w => ?_)
    obtain ⟨W, hW⟩ := exists_smoothVectorField_eq p w
    rw [← hW]
    show g.metricInner p
        (g.koszulDualSection (SmoothVectorField.smul f hf Y) X p) (W p)
      = g.metricInner p
          (f p • leviCivitaCovFieldGeneral g X Y p
            + (SmoothVectorField.dir X f p) • Y p) (W p)
    rw [g.metricInner_add_left, g.metricInner_smul_left, g.metricInner_smul_left]
    have hL := g.koszulDualSection_dual (SmoothVectorField.smul f hf Y) X W p
    have hXY := g.koszulDualSection_dual Y X W p
    have hk := g.koszulRHS_leibniz_left hf Y X W p
    show g.metricInner p
        (g.koszulDualSection (SmoothVectorField.smul f hf Y) X p) (W p)
      = f p * g.metricInner p (g.koszulDualSection Y X p) (W p)
        + SmoothVectorField.dir X f p * g.metricInner p (Y p) (W p)
    linear_combination (1 / 2 : ℝ) * hL + (1 / 2 : ℝ) * hk - (f p / 2) * hXY

/-- **Math.** The generalized Koszul connection is symmetric and metric-compatible. -/
theorem leviCivitaConnectionGeneral_isLeviCivita (g : RiemannianMetric I M) :
    (leviCivitaConnectionGeneral g).IsLeviCivita g := by
  apply AffineConnection.isLeviCivita_of_koszulDual g
  intro X Y Z p
  exact g.koszulDualSection_dual X Y Z p

/-- **Math.** The Levi-Civita theorem without an inner product on the manifold model. -/
theorem existsUnique_leviCivitaGeneral (g : RiemannianMetric I M) :
    ∃! nabla : AffineConnection I M, nabla.IsLeviCivita g :=
  AffineConnection.exists_unique_isLeviCivita_of_koszulDual g
    ⟨leviCivitaConnectionGeneral g,
      fun X Y Z p => g.koszulDualSection_dual X Y Z p⟩

end GeneralModel

end MorganTianLib

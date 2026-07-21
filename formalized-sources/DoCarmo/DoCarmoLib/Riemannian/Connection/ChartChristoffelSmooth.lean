import DoCarmoLib.Riemannian.Connection.ChartChristoffel


/-!
# Smoothness of the chart Christoffel symbols

`chartChristoffel g α i j k` is `C^∞` on the interior of the chart target,
reusing the existing Gram / inverse-Gram entry smoothness
(`TensorBundle/MusicalIso`): the Christoffel symbol is a finite sum of products
of inverse-Gram entries with first partial derivatives of Gram entries, all
pulled back through the chart inverse.

Builds on `Connection/ChartChristoffel` + the existing chart-Gram foundation.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Chart helpers -/

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
/-- **Math.** The extended-chart source coincides with the chart source. -/
lemma extChartAt_source_eq_chartAt_source (x₀ : M) :
    (extChartAt I x₀).source = (chartAt H x₀).source := by
  rw [extChartAt_source]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The tangent-bundle trivialization base set is the chart source. -/
lemma trivializationAt_baseSet_eq_chartAt_source (x₀ : M) :
    (trivializationAt E (TangentSpace I) x₀).baseSet = (chartAt H x₀).source :=
  rfl

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [IsManifold I ∞ M] in
/-- **Math.** Boundaryless: the chart target is its own interior. -/
lemma extChartAt_target_subset_interior_of_boundaryless [I.Boundaryless] (α : M) :
    (extChartAt I α).target ⊆ interior (extChartAt I α).target := by
  intro y hy
  exact (isOpen_extChartAt_target (I := I) α).interior_eq.symm ▸ hy

/-! ## Gram / inverse-Gram pulled-back smoothness -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The chart Gram entry pulled back to `E` is `C^∞` on the chart
target. -/
lemma chartGramOnE_contDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-- **Math.** The pulled-back inverse Gram matrix entry on the chart target. -/
def chartInvGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
@[simp] lemma chartInvGramOnE_def
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartInvGramOnE (I := I) g α i j y =
      chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** The pulled-back inverse Gram entry is `C^∞` on the chart target. -/
lemma chartInvGramOnE_contDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartInvGramOnE (I := I) g α i j) (extChartAt I α).target := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hsubset : (extChartAt I α).target ⊆
      (extChartAt I α).symm ⁻¹'
        (trivializationAt E (TangentSpace I) α).baseSet := by
    intro y hy
    have hsource : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
      (extChartAt I α).map_target hy
    rw [extChartAt_source_eq_chartAt_source (I := I)] at hsource
    rw [trivializationAt_baseSet_eq_chartAt_source]
    exact hsource
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun x : M => chartInvGramMatrix (I := I) g α x i j) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target := hbase.comp hsymm hsubset
  exact hcomp.contDiffOn

/-! ## Christoffel smoothness -/

omit [InnerProductSpace ℝ E] [NeZero (Module.finrank ℝ E)] in
/-- **Math.** **Smoothness of `chartChristoffel`.** The chart Christoffel symbol
is `C^∞` on the interior of the chart target. -/
theorem chartChristoffel_contDiffOn_interior
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ ∞ (chartChristoffel (I := I) g α i j k)
      (interior (extChartAt I α).target) := by
  classical
  have hrewrite : (chartChristoffel (I := I) g α i j k) =
      fun y : E =>
        (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := by
    funext y
    rw [chartChristoffel_def]
    refine congrArg (fun t => (1 / 2 : ℝ) * t) ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rfl
  rw [hrewrite]
  have hsum_smooth :
      ContDiffOn ℝ ∞
        (fun y : E => ∑ l : Fin (Module.finrank ℝ E),
          chartInvGramOnE (I := I) g α k l y *
            (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
             partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y))
        (interior (extChartAt I α).target) := by
    refine ContDiffOn.sum (fun l _ => ?_)
    refine ContDiffOn.mul ?_ ?_
    · exact (chartInvGramOnE_contDiffOn (I := I) g α k l).mono interior_subset
    · have hpartial : ∀ a p q : Fin (Module.finrank ℝ E),
          ContDiffOn ℝ ∞
            (partialDeriv (E := E) a (chartGramOnE (I := I) g α p q))
            (interior (extChartAt I α).target) := by
        intro a p q
        unfold partialDeriv
        have hG : ContDiffOn ℝ ∞ (chartGramOnE (I := I) g α p q)
            (interior (extChartAt I α).target) :=
          (chartGramOnE_contDiffOn (I := I) g α p q).mono interior_subset
        have hfderiv : ContDiffOn ℝ ∞
            (fderiv ℝ (chartGramOnE (I := I) g α p q))
            (interior (extChartAt I α).target) :=
          hG.fderiv_of_isOpen isOpen_interior (by rw [ENat.coe_top_add_one])
        exact hfderiv.clm_apply contDiffOn_const
      exact ((hpartial i l j).add (hpartial j l i)).sub (hpartial l i j)
  exact (contDiffOn_const (c := (1 / 2 : ℝ))).mul hsum_smooth

end Riemannian

end

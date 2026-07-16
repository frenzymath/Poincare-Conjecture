/- Vendored from DoCarmo `OpenGALib/Riemannian/Connection/ChartChristoffel.lean`. Namespace `Riemannian` mapped to
   `PetersenLib`; engineering infrastructure only, not a blueprint node. -/
import PetersenLib.Vendored.OpenGA.TensorBundle.MusicalIso

set_option linter.unusedSectionVars false

/-!
# Chart-coordinate Christoffel symbols

The Levi-Civita Christoffel symbols `Γᵏ_{ij}` expressed in a chart at `α`,
computed directly from the metric Gram matrix in coordinates via the textbook
formula `Γᵏ_{ij} = ½ Gᵏˡ (∂ᵢG_{lj} + ∂ⱼG_{li} − ∂_lG_{ij})`. These coordinate
symbols are what the geodesic equation `γ'' = −Γ(γ', γ')` is written against.

Built on OpenGALib's existing chart-Gram foundation (`TensorBundle/MusicalIso`:
`chartGramMatrix`, `chartInvGramMatrix` and their smoothness, in the
`Module.finBasis ℝ E` chart frame). Migrated from `external/differential-geometry`
(reference only) and **rebased onto the existing Gram infrastructure** rather
than duplicating it.

Reference: do Carmo Ch.2; Lee, *Riemannian Manifolds* Ch.5.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib

open PetersenLib.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** The partial derivative of `u : E → ℝ` at `y` along the `i`-th
chart-frame basis vector `(Module.finBasis ℝ E) i` (the same basis underlying
`chartGramMatrix`). -/
def partialDeriv (i : Fin (Module.finrank ℝ E)) (u : E → ℝ) (y : E) : ℝ :=
  fderiv ℝ u y ((Module.finBasis ℝ E) i)

/-- **Math.** The chart Gram entry `G_{ij}(α, ·)` pulled back to the chart target
via the chart inverse. -/
def chartGramOnE (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) : E → ℝ :=
  fun y => chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j

@[simp] lemma chartGramOnE_def
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y =
      chartGramMatrix (I := I) g α ((extChartAt I α).symm y) i j := rfl

/-- **Math.** Symmetry of the chart Gram entries pulled back to `E`. -/
lemma chartGramOnE_symm
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) (y : E) :
    chartGramOnE (I := I) g α i j y = chartGramOnE (I := I) g α j i y := by
  unfold chartGramOnE
  rw [chartGramMatrix_apply, chartGramMatrix_apply]
  exact g.symm _ _ _

/-- **Math.** The chart-coordinate **Christoffel symbol** of the second kind at
`α`: `Γᵏ_{ij}(g, α)(y) = ½ Σ_l Gᵏˡ(α, x_y) (∂ᵢG_{lj} + ∂ⱼG_{li} − ∂_lG_{ij})(y)`,
with `x_y := (extChartAt I α).symm y`, using the existing `chartGramMatrix` /
`chartInvGramMatrix`. -/
def chartChristoffel (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) : ℝ :=
  (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
    chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
      (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
       partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
       partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y)

@[simp] lemma chartChristoffel_def
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      (1 / 2 : ℝ) * ∑ l : Fin (Module.finrank ℝ E),
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) k l *
          (partialDeriv (E := E) i (chartGramOnE (I := I) g α l j) y +
           partialDeriv (E := E) j (chartGramOnE (I := I) g α l i) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y) := rfl

/-- **Math.** **Symmetry of the Christoffel symbol** in the lower indices — the
torsion-free property of the Levi-Civita connection, read off the coordinate
formula. -/
theorem chartChristoffel_symm
    (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E) :
    chartChristoffel (I := I) g α i j k y =
      chartChristoffel (I := I) g α j i k y := by
  classical
  rw [chartChristoffel_def, chartChristoffel_def]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro l _
  congr 1
  have hsym : chartGramOnE (I := I) g α i j =
      chartGramOnE (I := I) g α j i :=
    funext (fun y' => chartGramOnE_symm (I := I) g α i j y')
  rw [show partialDeriv (E := E) l (chartGramOnE (I := I) g α i j) y =
        partialDeriv (E := E) l (chartGramOnE (I := I) g α j i) y from by
    rw [hsym]]
  ring

/-- **Math.** **Christoffel contraction with the Gram matrix.** Contracting the
Christoffel symbol `Γᵐ_{ki}` against the Gram matrix `G_{am}` recovers half the
metric-derivative combination: `Σ_m G_{am} Γᵐ_{ki} = ½(∂_k G_{ai} + ∂_i G_{ak} −
∂_a G_{ki})`. This is the contraction `G_{am} G^{ml} = δ_a^l` collapsing the
inverse-Gram factor in the Christoffel formula. -/
lemma chartGram_christoffel_contraction (g : RiemannianMetric I M) (α : M)
    (a k i : Fin (Module.finrank ℝ E)) (y : E)
    (hy : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    ∑ m, chartGramOnE (I := I) g α a m y * chartChristoffel (I := I) g α k i m y
      = (1 / 2 : ℝ) * (partialDeriv (E := E) k (chartGramOnE (I := I) g α a i) y
          + partialDeriv (E := E) i (chartGramOnE (I := I) g α a k) y
          - partialDeriv (E := E) a (chartGramOnE (I := I) g α k i) y) := by
  classical
  have hcontract : ∀ l : Fin (Module.finrank ℝ E),
      ∑ m, chartGramOnE (I := I) g α a m y *
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) m l
      = if a = l then (1 : ℝ) else 0 := by
    intro l
    have h1 : ∑ m, chartGramOnE (I := I) g α a m y *
        chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) m l
        = (chartGramMatrix (I := I) g α ((extChartAt I α).symm y) *
            chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y)) a l := by
      rw [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [chartGramOnE_def]
    rw [h1, chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hy, Matrix.one_apply]
  calc ∑ m, chartGramOnE (I := I) g α a m y * chartChristoffel (I := I) g α k i m y
      = ∑ m, ∑ l, chartGramOnE (I := I) g α a m y *
          ((1 / 2 : ℝ) * (chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) m l *
            (partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y +
             partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y -
             partialDeriv (E := E) l (chartGramOnE (I := I) g α k i) y))) := by
        simp_rw [chartChristoffel_def, Finset.mul_sum]
    _ = (1 / 2 : ℝ) * ∑ l, (∑ m, chartGramOnE (I := I) g α a m y *
          chartInvGramMatrix (I := I) g α ((extChartAt I α).symm y) m l) *
          (partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y +
           partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α k i) y) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
    _ = (1 / 2 : ℝ) * ∑ l, (if a = l then (1 : ℝ) else 0) *
          (partialDeriv (E := E) k (chartGramOnE (I := I) g α l i) y +
           partialDeriv (E := E) i (chartGramOnE (I := I) g α l k) y -
           partialDeriv (E := E) l (chartGramOnE (I := I) g α k i) y) := by
        simp_rw [hcontract]
    _ = (1 / 2 : ℝ) * (partialDeriv (E := E) k (chartGramOnE (I := I) g α a i) y
          + partialDeriv (E := E) i (chartGramOnE (I := I) g α a k) y
          - partialDeriv (E := E) a (chartGramOnE (I := I) g α k i) y) := by
        congr 1
        simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Math.** **Metric-compatibility in chart components.** The derivative of the
Gram matrix is recovered from the Christoffel symbols:
`∂_k G_{ij} = Σ_m (G_{mj} Γᵐ_{ki} + G_{im} Γᵐ_{kj})`. This is the coordinate form
of `∇g = 0` for the Levi-Civita connection — the identity feeding the
metric-compatibility of the covariant derivative along a curve. -/
theorem partialDeriv_chartGramOnE_eq (g : RiemannianMetric I M) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) (y : E)
    (hy : (extChartAt I α).symm y ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    partialDeriv (E := E) k (chartGramOnE (I := I) g α i j) y
      = ∑ m, (chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
            + chartGramOnE (I := I) g α i m y * chartChristoffel (I := I) g α k j m y) := by
  classical
  have hsymP : ∀ (p q r : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) r (chartGramOnE (I := I) g α p q) y
        = partialDeriv (E := E) r (chartGramOnE (I := I) g α q p) y := by
    intro p q r
    unfold partialDeriv
    rw [show chartGramOnE (I := I) g α p q = chartGramOnE (I := I) g α q p from
      funext fun y' => chartGramOnE_symm (I := I) g α p q y']
  rw [Finset.sum_add_distrib]
  have e1 : ∑ m, chartGramOnE (I := I) g α m j y * chartChristoffel (I := I) g α k i m y
      = ∑ m, chartGramOnE (I := I) g α j m y * chartChristoffel (I := I) g α k i m y :=
    Finset.sum_congr rfl fun m _ => by rw [chartGramOnE_symm (I := I) g α m j]
  rw [e1, chartGram_christoffel_contraction (I := I) g α j k i y hy,
    chartGram_christoffel_contraction (I := I) g α i k j y hy,
    hsymP j i k, hsymP j k i, hsymP k i j]
  ring

end PetersenLib

end

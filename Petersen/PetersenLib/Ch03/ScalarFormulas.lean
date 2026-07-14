import PetersenLib.Ch03.RiemannConstantCurvature

/-!
# Petersen Ch. 3, §3.1.5 — Formulas for the scalar curvature

The orthonormal-basis formulas for the scalar curvature
(Petersen §3.1.5, `rem:pet-ch3-scalar-curvature-formulas`): in a
`g`-orthonormal basis `e₁, …, eₙ` of `T_pM`,

`scal = ∑ⱼ g(Ric(eⱼ), eⱼ) = ∑ᵢⱼ g(R(eᵢ,eⱼ)eⱼ, eᵢ)
      = ∑ᵢⱼ g(𝔯(eᵢ∧eⱼ), eᵢ∧eⱼ) = ∑ᵢ ∑_{j≠i} sec(eᵢ,eⱼ)`

(`scalarCurvature_formulas`; the last two sums run over all ordered pairs, so
they equal `2·∑_{i<j}` of the same summands — in particular the third is
`2·tr 𝔯`, the trace of the curvature operator in the orthonormal basis
`{eᵢ∧eⱼ}_{i<j}` of `Λ²T_pM`). When `n = 2` the scalar curvature is twice the
sectional curvature of the tangent plane
(`scalarCurvature_eq_two_mul_sectionalCurvature`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.5.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-- The trace of an endomorphism of `T_pM` in a `g`-orthonormal basis:
`tr f = ∑ᵢ g(f(eᵢ), eᵢ)`. -/
theorem trace_eq_sum_metricInner {g : RiemannianMetric I M} (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (f : Module.End ℝ (TangentSpace I p)) :
    LinearMap.trace ℝ (TangentSpace I p) f
      = ∑ i, g.metricInner p (f (b i)) (b i) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ b]
  simp only [Matrix.trace, Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [orthonormal_basis_repr_eq_metricInner p b hb]

/-- Symmetry of the sectional curvature in its two arguments
(Petersen §3.1.3): `sec(v,w) = sec(w,v)`, from the pair-swap symmetry of `R`
and the symmetry of the Gram determinant. -/
theorem sectionalCurvature_comm {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M) (v w : TangentSpace I p) :
    sectionalCurvature D p v w = sectionalCurvature D p w v := by
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  rw [sectionalCurvature_eq_curvatureTensorFourAt,
    sectionalCurvature_eq_curvatureTensorFourAt]
  have h := hAlg.pairSwap w v v w
  rw [h, bivectorInnerProduct_swap_pair]

/-- Distinct vectors of a basis are linearly independent as a pair. -/
theorem basis_linearIndependent_pair {p : M}
    {ι : Type*} (b : Module.Basis ι ℝ (TangentSpace I p)) {i j : ι}
    (hij : i ≠ j) : LinearIndependent ℝ ![b i, b j] := by
  have h : ![b i, b j] = ⇑b ∘ ![i, j] := by
    funext k
    fin_cases k <;> rfl
  rw [h]
  refine b.linearIndependent.comp ![i, j] ?_
  intro a c hac
  fin_cases a <;> fin_cases c <;> simp_all <;>
    first
      | rfl
      | exact absurd hac hij
      | exact absurd hac.symm hij

/-- **Math.** The scalar curvature as the trace of the Ricci `(1,1)`-tensor in
a `g`-orthonormal basis: `scal(p) = ∑ⱼ g(Ric(eⱼ), eⱼ) = ∑ⱼ Ric(eⱼ,eⱼ)`. -/
theorem scalarCurvature_eq_sum_ricci {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature D p
      = ∑ j, RicciCurvature D.toAffineConnection p (b j) (b j) := by
  show LinearMap.trace ℝ (TangentSpace I p) (ricciEndomorphismLinear D p) = _
  rw [trace_eq_sum_metricInner p b hb]
  refine Finset.sum_congr rfl fun j _ => ?_
  show g.metricInner p (ricciEndomorphism D p (b j)) (b j) = _
  rw [metricInner_ricciEndomorphism]

/-- **Math.** **Formulas for the scalar curvature** (Petersen §3.1.5,
`rem:pet-ch3-scalar-curvature-formulas`): in a `g`-orthonormal basis
`e₁, …, eₙ` of `T_pM`,
`scal = ∑ⱼ g(Ric(eⱼ),eⱼ) = ∑ᵢⱼ g(R(eᵢ,eⱼ)eⱼ,eᵢ) = ∑ᵢⱼ g(𝔯(eᵢ∧eⱼ), eᵢ∧eⱼ)
= ∑ᵢ∑_{j≠i} sec(eᵢ,eⱼ)`. Each double sum counts every unordered pair twice
(the diagonal terms vanish), so the third equals `2·tr 𝔯` and the fourth is
`2·∑_{i<j} sec(eᵢ,eⱼ)`. -/
theorem scalarCurvature_formulas {g : RiemannianMetric I M}
    (D : RiemannianConnection I g) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature D p
        = ∑ j, RicciCurvature D.toAffineConnection p (b j) (b j)
    ∧ scalarCurvature D p
        = ∑ i, ∑ j, curvatureTensorFourAt D p (b i) (b j) (b j) (b i)
    ∧ scalarCurvature D p
        = ∑ i, ∑ j, bivectorEndoInner g p
            (curvatureOperator D p (wedgeEndo g p (b i) (b j)))
            (wedgeEndo g p (b i) (b j))
    ∧ scalarCurvature D p
        = ∑ i, ∑ j ∈ Finset.univ.erase i, sectionalCurvature D p (b i) (b j) := by
  classical
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  -- second formula: expand the Ricci diagonal by the trace formula
  have h2 : scalarCurvature D p
      = ∑ i, ∑ j, curvatureTensorFourAt D p (b i) (b j) (b j) (b i) := by
    rw [scalarCurvature_eq_sum_ricci D p b hb]
    rw [Finset.sum_congr rfl fun j _ => ricciCurvature_eq_sum D p b hb (b j) (b j)]
    rw [Finset.sum_comm]
  refine ⟨scalarCurvature_eq_sum_ricci D p b hb, h2, ?_, ?_⟩
  · -- third formula: each summand is the defining property of `𝔯`
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [bivectorEndoInner_curvatureOperator_wedge_wedge]
  · -- fourth formula: drop the vanishing diagonal, identify `sec` terms
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ i)]
    have hdiag : curvatureTensorFourAt D p (b i) (b i) (b i) (b i) = 0 := by
      simpa using hAlg.self_left (b i) (b i) (b i)
    rw [hdiag, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : j ≠ i := Finset.ne_of_mem_erase hj
    -- `sec(eᵢ,eⱼ) = R⁴(eⱼ,eᵢ,eᵢ,eⱼ)`, denominator 1, then pair-swap
    have hbip : bivectorInnerProduct g p (b i) (b j) (b i) (b j) = 1 := by
      rw [bivectorInnerProduct, hb i i, hb j j, hb i j]
      simp [hij.symm]
    rw [sectionalCurvature_eq_curvatureTensorFourAt, hbip, div_one]
    exact hAlg.pairSwap (b i) (b j) (b j) (b i)

/-- **Math.** In dimension `2` (Petersen §3.1.5): `scal(p) = 2·sec(T_pM)`,
the scalar curvature is twice the sectional curvature of the tangent plane. -/
theorem scalarCurvature_eq_two_mul_sectionalCurvature
    {g : RiemannianMetric I M} (D : RiemannianConnection I g) (p : M)
    (b : Module.Basis (Fin 2) ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    scalarCurvature D p = 2 * sectionalCurvature D p (b 0) (b 1) := by
  have h := (scalarCurvature_formulas D p b hb).2.2.2
  rw [h]
  have h0 : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  have h1 : (Finset.univ.erase (1 : Fin 2)) = {0} := by decide
  rw [Fin.sum_univ_two, h0, h1, Finset.sum_singleton, Finset.sum_singleton,
    sectionalCurvature_comm D p (b 1) (b 0)]
  ring

end PetersenLib

/- Vendored from DoCarmo `OpenGALib/Riemannian/TensorBundle/MusicalIso.lean` (identical shared OpenGA infra).
   Namespace `Riemannian` mapped to `PetersenLib`; `AffineConnection` renamed
   `DCAffineConnection` to keep the Petersen blueprint anchor name free.
   Engineering infrastructure only — not a blueprint node. -/
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import PetersenLib.Vendored.OpenGA.TensorBundle.SmoothOrthoFrame

/-!
# Smoothness of the musical isomorphism

For a smooth Riemannian metric $g$, the musical isomorphism
$\sharp_g : T^*M \to TM$ at $x$ sends $\varphi \in T_x^*M$ to the unique
tangent vector $V$ with $g_x(V, W) = \varphi(W)$ for all $W$. This is
`g.metricRiesz x φ` in OpenGALib.

This file establishes smoothness of $x \mapsto \sharp_g\,\varphi(x)$ via
the chart-local representation
$$\sharp_g\,\varphi(x) = \sum_{i,j} G^{ij}(x)\,\varphi_j(x)\,e_i(x),$$
where $e_i$ is the chart-basis frame, $G_{ij} = g_x(e_i, e_j)$ is the
chart Gram matrix, and $G^{ij}$ is its entrywise inverse. The Gram matrix
is symmetric positive-definite on the trivialization base set, so its
determinant is strictly positive and its inverse is smooth via the
cofactor / adjugate formula.

**Ground truth**: do Carmo §3 ex. 8 (Riesz duality); Lee 2018 §13
(musical isomorphisms). The chart-Gram-matrix machinery is ported from
the `differential-geometry` external library (`Integral/Measure/ChartDensity`,
`Geometry/Gradient`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace PetersenLib
namespace Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ## Stage 1: the chart Gram matrix -/

/-- **Math.** The Gram matrix of the chart-basis family
`chartBasisVecFiber α · x` at $x$ under the inner product `g.inner x`. -/
def chartGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  Matrix.of fun i j =>
    g.inner x
      (chartBasisVecFiber (I := I) α i x)
      (chartBasisVecFiber (I := I) α j x)

@[simp] lemma chartGramMatrix_apply
    (g : RiemannianMetric I M) (α : M) (x : M)
    (i j : Fin (Module.finrank ℝ E)) :
    chartGramMatrix (I := I) g α x i j =
      g.inner x
        (chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α j x) := rfl

/-- **Math.** The Gram matrix is Hermitian (symmetric, real entries). -/
lemma chartGramMatrix_isHermitian
    (g : RiemannianMetric I M) (α : M) (x : M) :
    (chartGramMatrix (I := I) g α x).IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  show star (chartGramMatrix (I := I) g α x j i)
    = chartGramMatrix (I := I) g α x i j
  rw [chartGramMatrix_apply, chartGramMatrix_apply, star_trivial]
  exact g.symm x
    (chartBasisVecFiber (I := I) α j x)
    (chartBasisVecFiber (I := I) α i x)

/-! ## Stage 2: positive-definiteness on the base set -/

/-- **Math.** The Gram-matrix quadratic form equals the metric-inner-product
squared norm of the corresponding linear combination of chart-basis vectors. -/
lemma chartGramMatrix_dotProduct_mulVec
    (g : RiemannianMetric I M) (α : M) (x : M)
    (c : Fin (Module.finrank ℝ E) → ℝ) :
    star c ⬝ᵥ (chartGramMatrix (I := I) g α x) *ᵥ c =
      g.inner x
        (∑ i, c i • chartBasisVecFiber (I := I) α i x)
        (∑ j, c j • chartBasisVecFiber (I := I) α j x) := by
  have hexpand :
      g.inner x
          (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          (∑ j, c j • chartBasisVecFiber (I := I) α j x)
        = ∑ i, ∑ j, (c i * c j) *
            g.inner x
              (chartBasisVecFiber (I := I) α i x)
              (chartBasisVecFiber (I := I) α j x) := by
    have hL :
        g.inner x (∑ i, c i • chartBasisVecFiber (I := I) α i x)
          = ∑ i, c i • g.inner x (chartBasisVecFiber (I := I) α i x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [map_smul]
    rw [hL, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [ContinuousLinearMap.smul_apply]
    have hR :
        g.inner x (chartBasisVecFiber (I := I) α i x)
            (∑ j, c j • chartBasisVecFiber (I := I) α j x)
          = ∑ j, c j *
              g.inner x
                (chartBasisVecFiber (I := I) α i x)
                (chartBasisVecFiber (I := I) α j x) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [map_smul, smul_eq_mul]
    rw [hR, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  rw [hexpand]
  simp only [dotProduct, Matrix.mulVec, chartGramMatrix_apply, Pi.star_apply,
    star_trivial]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- **Math.** The Gram matrix of the chart-basis family is positive-definite
on the trivialization base set. -/
lemma chartGramMatrix_posDef
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    (chartGramMatrix (I := I) g α x).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (chartGramMatrix_isHermitian (I := I) g α x) ?_
  intro c hc
  set w : TangentSpace I x :=
    ∑ i, c i • chartBasisVecFiber (I := I) α i x with hw_def
  have heq := chartGramMatrix_dotProduct_mulVec (I := I) g α x c
  rw [heq]
  have hwnz : w ≠ 0 := by
    intro hw0
    have hli := chartBasisFamily_linearIndependent (I := I) α hx
    rw [Fintype.linearIndependent_iff] at hli
    have : c = 0 := funext (hli c hw0)
    exact hc this
  exact g.pos x w hwnz

/-- **Math.** The determinant of the Gram matrix is strictly positive on
the trivialization base set. -/
lemma chartGramMatrix_det_pos
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    0 < (chartGramMatrix (I := I) g α x).det :=
  (chartGramMatrix_posDef (I := I) g α hx).det_pos

/-! ## Stage 3: smoothness of Gram-matrix entries -/

/-- **Eng.** Each Gram-matrix entry is smooth on the trivialization base set,
via `ContMDiffOn.clm_bundle_apply₂` on `g.contMDiff` and two `chartBasisVec`. -/
lemma chartGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => chartGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  have hg : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartBasisVec_contMDiffOn (I := I) α i
  have hw := chartBasisVec_contMDiffOn (I := I) α j
  have happ :
      ContMDiffOn I (I.prod 𝓘(ℝ, ℝ)) ∞
        (fun m : M => (⟨m,
            g.inner m
              (chartBasisVecFiber (I := I) α i m)
              (chartBasisVecFiber (I := I) α j m)⟩ :
              TotalSpace ℝ (Bundle.Trivial M ℝ)))
        (trivializationAt E (TangentSpace I) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := E) (F₂ := E) (F₃ := ℝ)
      (b := id) hg hv hw
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2

/-- **Eng.** The determinant of the Gram matrix is smooth on the
trivialization base set. Expands `Matrix.det` as a finite sum of
finite products and chains entry smoothness. -/
lemma chartGramMatrix_det_contMDiffOn
    (g : RiemannianMetric I M) (α : M) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x => (chartGramMatrix (I := I) g α x).det)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix (I := I) g α x).det)
        = (fun x : M =>
            ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
              (Equiv.Perm.sign σ : ℝ) *
                ∏ i, chartGramMatrix (I := I) g α x (σ i) i) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun i _ => ?_)
  exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ i) i

/-! ## Stage 4: smoothness of the adjugate entries -/

/-- **Eng.** Each adjugate entry of the Gram matrix is smooth on the
trivialization base set: a polynomial in the smooth Gram-matrix entries
via `Matrix.adjugate_apply` + `updateRow`. -/
lemma chartGramMatrix_adjugate_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hexp :
      (fun x : M => (chartGramMatrix (I := I) g α x).adjugate i j) =
        (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
          (Pi.single i (1 : ℝ))).det) := by
    funext x
    exact Matrix.adjugate_apply _ _ _
  rw [hexp]
  have hexp2 :
      (fun x : M => ((chartGramMatrix (I := I) g α x).updateRow j
          (Pi.single i (1 : ℝ))).det) =
        (fun x : M => ∑ σ : Equiv.Perm (Fin (Module.finrank ℝ E)),
          (Equiv.Perm.sign σ : ℝ) *
            ∏ k, (chartGramMatrix (I := I) g α x).updateRow j
                (Pi.single i (1 : ℝ)) (σ k) k) := by
    funext x
    rw [Matrix.det_apply]
    simp [Units.smul_def]
  rw [hexp2]
  refine contMDiffOn_finset_sum (fun σ _ => ?_)
  refine ContMDiffOn.mul
    (contMDiffOn_const (c := ((Equiv.Perm.sign σ : ℤ) : ℝ))) ?_
  refine contMDiffOn_finset_prod (fun k _ => ?_)
  by_cases hσk : σ k = j
  · have heq :
        (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          (fun _ : M => (Pi.single (M := fun _ : Fin (Module.finrank ℝ E) => ℝ)
            i (1 : ℝ)) k) := by
      funext x
      rw [hσk, Matrix.updateRow_self]
    rw [heq]
    exact contMDiffOn_const
  · have heq :
        (fun x : M => (chartGramMatrix (I := I) g α x).updateRow j
            (Pi.single i (1 : ℝ)) (σ k) k) =
          (fun x : M => chartGramMatrix (I := I) g α x (σ k) k) := by
      funext x
      rw [Matrix.updateRow_ne hσk]
    rw [heq]
    exact chartGramMatrix_entry_contMDiffOn (I := I) g α (σ k) k

/-! ## Stage 5: the inverse Gram matrix and its smoothness -/

/-- **Math.** The inverse Gram matrix at $(\alpha, x)$. On the chart base
set, the matrix inverse of the (positive-definite) Gram matrix. -/
def chartInvGramMatrix (g : RiemannianMetric I M) (α : M) (x : M) :
    Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  (chartGramMatrix (I := I) g α x)⁻¹

/-- **Math.** On the chart base set, the inverse Gram matrix is a one-sided inverse. -/
lemma chartInvGramMatrix_mul_chartGramMatrix
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartInvGramMatrix (I := I) g α x * chartGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.nonsing_inv_mul _ hdet_unit

/-- **Math.** Symmetric form: Gram · inverse Gram = 1 on the base set. -/
lemma chartGramMatrix_mul_chartInvGramMatrix
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet) :
    chartGramMatrix (I := I) g α x * chartInvGramMatrix (I := I) g α x = 1 := by
  have hpos := chartGramMatrix_posDef (I := I) g α hx
  have hdet_unit : IsUnit (chartGramMatrix (I := I) g α x).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpos.det_pos)
  unfold chartInvGramMatrix
  exact Matrix.mul_nonsing_inv _ hdet_unit

/-- **Eng.** Each entry of the inverse Gram matrix is smooth on the chart
base set, via the cofactor / adjugate formula. -/
lemma chartInvGramMatrix_entry_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContMDiffOn I 𝓘(ℝ) ∞
      (fun x : M => chartInvGramMatrix (I := I) g α x i j)
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  have hcongr : ∀ x ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      chartInvGramMatrix (I := I) g α x i j =
        ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j := by
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
      ne_of_gt hdet_pos
    unfold chartInvGramMatrix
    rw [Matrix.inv_def]
    change (Ring.inverse (chartGramMatrix (I := I) g α x).det •
            (chartGramMatrix (I := I) g α x).adjugate) i j =
      ((chartGramMatrix (I := I) g α x).det)⁻¹ *
          (chartGramMatrix (I := I) g α x).adjugate i j
    rw [Matrix.smul_apply, smul_eq_mul]
    congr 1
    exact Ring.inverse_eq_inv _
  refine ContMDiffOn.congr ?_ hcongr
  refine ContMDiffOn.mul ?_ ?_
  · have hdet_smooth :
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun x : M => (chartGramMatrix (I := I) g α x).det)
          (trivializationAt E (TangentSpace I) α).baseSet :=
      chartGramMatrix_det_contMDiffOn (I := I) g α
    intro x hx
    have hdet_pos := chartGramMatrix_det_pos (I := I) g α hx
    have hdet_ne : (chartGramMatrix (I := I) g α x).det ≠ 0 :=
      ne_of_gt hdet_pos
    have hsmooth_inv : ContDiffAt ℝ ∞ (fun y : ℝ => y⁻¹)
        (chartGramMatrix (I := I) g α x).det := contDiffAt_inv _ hdet_ne
    have h_at := hdet_smooth x hx
    exact hsmooth_inv.contMDiffAt.comp_contMDiffWithinAt x h_at
  · exact chartGramMatrix_adjugate_entry_contMDiffOn (I := I) g α i j

/-! ## Stage 6: chart-coordinate expression of the Riesz dual

At any base-set point $x$, the Riesz dual of a covector $\varphi$ admits the
explicit chart-frame expression
$$\sharp_g\,\varphi(x) = \sum_i \Bigl(\sum_j G^{ij}(x)\,\varphi(e_j(x))\Bigr)\,
    e_i(x),$$
derived by `g.metricRiesz_unique` against the bilinear-form action on the
chart frame.

This is the algebraic heart of the smoothness argument: every quantity on
the right-hand side is smooth on the base set (Gram-matrix inverse entries
via Stage 5, chart-basis vectors via `SmoothOrthoFrame`, and the covector
section by hypothesis), so the LHS is smooth too. -/

private lemma metricRiesz_chart_form_inner_e
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ)
    (k : Fin (Module.finrank ℝ E)) :
    g.inner x
        (∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x)) •
            chartBasisVecFiber (I := I) α i x)
        (chartBasisVecFiber (I := I) α k x)
      = φ (chartBasisVecFiber (I := I) α k x) := by
  -- Expand g.inner over the outer sum in the first argument.
  rw [show g.inner x
        (∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x)) •
            chartBasisVecFiber (I := I) α i x)
        = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x)) •
            g.inner x (chartBasisVecFiber (I := I) α i x) from ?_]
  · -- Now goal: ∑ i, (∑ j, G⁻¹_{ij} φ(e_j)) • g.inner x e_i (e_k) = φ(e_k)
    rw [ContinuousLinearMap.sum_apply]
    -- Goal: ∑ i, ((∑ j, G⁻¹_{ij} φ(e_j)) • g.inner x e_i) (e_k) = φ(e_k)
    have hsmul : ∀ i,
        ((∑ j, chartInvGramMatrix (I := I) g α x i j *
            φ (chartBasisVecFiber (I := I) α j x)) •
              g.inner x (chartBasisVecFiber (I := I) α i x))
            (chartBasisVecFiber (I := I) α k x) =
          (∑ j, chartInvGramMatrix (I := I) g α x i j *
              φ (chartBasisVecFiber (I := I) α j x)) *
            chartGramMatrix (I := I) g α x i k := by
      intro i
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rfl
    rw [Finset.sum_congr rfl (fun i _ => hsmul i)]
    -- Goal: ∑ i, (∑ j, G⁻¹_{ij} φ(e_j)) * G_{ik} = φ(e_k)
    have hdistrib : ∀ i,
        (∑ j, chartInvGramMatrix (I := I) g α x i j *
            φ (chartBasisVecFiber (I := I) α j x)) *
          chartGramMatrix (I := I) g α x i k
            = ∑ j, chartInvGramMatrix (I := I) g α x i j *
                φ (chartBasisVecFiber (I := I) α j x) *
              chartGramMatrix (I := I) g α x i k := by
      intro i
      rw [Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun i _ => hdistrib i)]
    -- Goal: ∑ i, ∑ j, G⁻¹_{ij} φ(e_j) G_{ik} = φ(e_k)
    rw [Finset.sum_comm]
    -- Goal: ∑ j, ∑ i, G⁻¹_{ij} φ(e_j) G_{ik} = φ(e_k)
    have hfact : ∀ j,
        (∑ i, chartInvGramMatrix (I := I) g α x i j *
            φ (chartBasisVecFiber (I := I) α j x) *
          chartGramMatrix (I := I) g α x i k)
          = (∑ i, chartGramMatrix (I := I) g α x i k *
              chartInvGramMatrix (I := I) g α x i j) *
            φ (chartBasisVecFiber (I := I) α j x) := by
      intro j
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    rw [Finset.sum_congr rfl (fun j _ => hfact j)]
    -- Goal: ∑ j, (∑ i, G_{ik} G⁻¹_{ij}) φ(e_j) = φ(e_k)
    -- Use symmetry: G_{ik} = G_{ki}, then (G * G⁻¹)_{kj} = δ_{kj}.
    have hsym : ∀ i j,
        chartGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x i j
          = chartGramMatrix (I := I) g α x k i *
            chartInvGramMatrix (I := I) g α x i j := by
      intro i j
      have := (chartGramMatrix_isHermitian (I := I) g α x).apply k i
      simp only [star_trivial] at this
      rw [this]
    have hkj : ∀ j,
        (∑ i, chartGramMatrix (I := I) g α x i k *
            chartInvGramMatrix (I := I) g α x i j)
          = (1 : Matrix (Fin (Module.finrank ℝ E))
              (Fin (Module.finrank ℝ E)) ℝ) k j := by
      intro j
      have hsum : (∑ i, chartGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x i j)
          = ∑ i, chartGramMatrix (I := I) g α x k i *
              chartInvGramMatrix (I := I) g α x i j :=
        Finset.sum_congr rfl (fun i _ => hsym i j)
      rw [hsum]
      have hmul := chartGramMatrix_mul_chartInvGramMatrix (I := I) g α hx
      have hprod_eq :
          (chartGramMatrix (I := I) g α x *
              chartInvGramMatrix (I := I) g α x) k j
            = (1 : Matrix (Fin (Module.finrank ℝ E))
                (Fin (Module.finrank ℝ E)) ℝ) k j := by
        rw [hmul]
      rw [← hprod_eq]
      rfl
    rw [Finset.sum_congr rfl (fun j _ => by rw [hkj j])]
    -- Goal: ∑ j, (1 : Matrix _ _ ℝ) k j * φ(e_j) = φ(e_k)
    rw [Finset.sum_eq_single k]
    · simp [Matrix.one_apply_eq]
    · intro j _ hjk
      have : (1 : Matrix (Fin (Module.finrank ℝ E))
                (Fin (Module.finrank ℝ E)) ℝ) k j = 0 :=
        Matrix.one_apply_ne (Ne.symm hjk)
      rw [this, zero_mul]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · -- side goal: g.inner x ∑ᵢ cᵢ • vᵢ = ∑ᵢ cᵢ • g.inner x vᵢ
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_smul]

/-- **Math.** **Chart-coordinate form of the Riesz dual** at a base-set point $x$. -/
private theorem metricRiesz_chart_form
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (φ : TangentSpace I x →L[ℝ] ℝ) :
    g.metricRiesz x φ =
      ∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
              φ (chartBasisVecFiber (I := I) α j x)) •
        chartBasisVecFiber (I := I) α i x := by
  symm
  apply g.metricRiesz_unique
  intro W
  -- Reduce to equality on the chart basis via Module.Basis.ext.
  have hLM_eq :
      (g.inner x
          (∑ i, (∑ j, chartInvGramMatrix (I := I) g α x i j *
                  φ (chartBasisVecFiber (I := I) α j x)) •
              chartBasisVecFiber (I := I) α i x) :
          TangentSpace I x →ₗ[ℝ] ℝ)
        = (φ : TangentSpace I x →ₗ[ℝ] ℝ) := by
    apply (chartBasisFamily (I := I) α hx).ext
    intro k
    rw [chartBasisFamily_apply (I := I) α hx k]
    exact metricRiesz_chart_form_inner_e (I := I) g α hx φ k
  have := congrArg (fun (L : TangentSpace I x →ₗ[ℝ] ℝ) => L W) hLM_eq
  show g.metricInner x _ W = φ W
  exact this

/-! ## Stage 7: chart-local smoothness and the musical-iso section primitive -/

/-- **Eng.** **Chart-local smoothness** of the Riesz-section in chart-frame form.
Given a covector field $\Phi$ whose action on each chart-basis vector
$\Phi(y)(e_j(y))$ is smooth on the trivialization base set, the
chart-local linear combination
$$y \mapsto \sum_i \Bigl(\sum_j G^{ij}(y)\,\Phi(y)(e_j(y))\Bigr)\,e_i(y)$$
is smooth as a tangent-bundle section on the base set.

Mechanism: reduce to scalar smoothness via
`Trivialization.contMDiffOn_section_baseSet_iff`; on the base set, the
trivialization is fiber-linear, so the trivialized fiber of the sum is
$\sum_i c_i(y) \cdot (\mathrm{Module.finBasis}\,\mathbb R\,E)_i$, a finite
sum of smooth scalars times constant model-space vectors. -/
lemma metricRiesz_chartLocal_total_contMDiffOn
    (g : RiemannianMetric I M) (α : M)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun y => Φ y (chartBasisVecFiber (I := I) α j y))
          (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y
        (∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                Φ y (chartBasisVecFiber (I := I) α j y)) •
          chartBasisVecFiber (I := I) α i y))
      (trivializationAt E (TangentSpace I) α).baseSet := by
  classical
  set triv := trivializationAt E (TangentSpace I) α with htriv_def
  set s := triv.baseSet
  -- Step 1: smoothness of each scalar coefficient.
  have hcoef : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffOn I 𝓘(ℝ) ∞
        (fun y => ∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) s := by
    intro i
    refine contMDiffOn_finset_sum (fun j _ => ?_)
    exact (chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j).mul (hΦ j)
  -- Step 2: reduce bundle-section smoothness to scalar smoothness via
  -- `Trivialization.contMDiffOn_section_baseSet_iff`. We pick the
  -- trivialization at α (same as in the chart-Gram-matrix machinery).
  rw [triv.contMDiffOn_section_baseSet_iff (IB := I) (n := ∞)]
  -- Goal: ContMDiffOn I 𝓘(ℝ, E) ∞
  --   (fun y => (triv ⟨y, ∑ i, c_i(y) • e_i(y)⟩).2) s
  -- Use fiber-linearity of triv on s to push triv inside the sum +
  -- through scalar multiplication, ending with constant model-basis
  -- vectors.
  have hsnd_eq : ∀ y ∈ s,
      (triv ⟨y,
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                Φ y (chartBasisVecFiber (I := I) α j y)) •
            chartBasisVecFiber (I := I) α i y⟩).2
        = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) •
          (Module.finBasis ℝ E i : E) := by
    intro y hy
    -- Pointwise equation: `(triv ⟨y, v⟩).2 = continuousLinearEquivAt R y hy v`
    -- for any fiber element v. Comes from `apply_eq_prod_continuousLinearEquivAt`
    -- by taking snd.
    have hsnd_apply : ∀ v : TangentSpace I y,
        (triv ⟨y, v⟩).2 = triv.continuousLinearEquivAt ℝ y hy v := by
      intro v
      have h := triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy v
      exact congrArg Prod.snd h
    rw [hsnd_apply]
    -- Apply linearity (`map_sum`, `map_smul`) and the chart-basis evaluation.
    rw [map_sum (triv.continuousLinearEquivAt ℝ y hy)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [(triv.continuousLinearEquivAt ℝ y hy).map_smul]
    congr 1
    rw [← hsnd_apply (chartBasisVecFiber (I := I) α i y)]
    exact trivializationAt_chartBasisVec_snd (I := I) α i hy
  have hRHS_smooth :
      ContMDiffOn I 𝓘(ℝ, E) ∞
        (fun y => ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) •
          (Module.finBasis ℝ E i : E)) s := by
    refine contMDiffOn_finset_sum (fun i _ => ?_)
    exact (hcoef i).smul (contMDiffOn_const (c := (Module.finBasis ℝ E i : E)))
  exact hRHS_smooth.congr (fun y hy => hsnd_eq y hy)

/-- **Math.** **Smoothness of the musical isomorphism section** at a
base-set point. Given $\Phi$ whose chart-basis evaluations are smooth on
the trivialization base set, $y \mapsto \sharp_g\,\Phi(y)$ is smooth.
Framework primitive consumed by gradient + Koszul-covariant-derivative
smoothness. -/
theorem metricRiesz_section_contMDiffAt
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
        ContMDiffOn I 𝓘(ℝ) ∞
          (fun y => Φ y (chartBasisVecFiber (I := I) α j y))
          (trivializationAt E (TangentSpace I) α).baseSet) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (g.metricRiesz y (Φ y))) x := by
  have hChartLocal :=
    metricRiesz_chartLocal_total_contMDiffOn (I := I) g α (Φ := Φ) hΦ
  -- Replace chart-local form with metricRiesz via Task 7.
  have hcongr : ∀ y ∈ (trivializationAt E (TangentSpace I) α).baseSet,
      (∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
              Φ y (chartBasisVecFiber (I := I) α j y)) •
            chartBasisVecFiber (I := I) α i y) = g.metricRiesz y (Φ y) := by
    intro y hy
    exact (metricRiesz_chart_form (I := I) g α hy (Φ y)).symm
  have hMR :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E y (g.metricRiesz y (Φ y)))
        (trivializationAt E (TangentSpace I) α).baseSet := by
    refine hChartLocal.congr ?_
    intro y hy
    have h := hcongr y hy
    show TotalSpace.mk' E y _ = TotalSpace.mk' E y _
    rw [h]
  -- Base set is open: `(chartAt H α).source` open ⟹ baseSet open.
  have hopen : IsOpen (trivializationAt E (TangentSpace I) α).baseSet :=
    (trivializationAt E (TangentSpace I) α).open_baseSet
  exact (hMR x hx).contMDiffAt (hopen.mem_nhds hx)

/-- **Math.** Per-point variant of `metricRiesz_section_contMDiffAt`.
Math: same conclusion (Riesz section smooth at $x$). Eng: input hypothesis
relaxed to `ContMDiffWithinAt baseSet x` per chart-basis index, easier
to discharge for `koszulFunctional`-style covectors with bump-function
extensions. -/
theorem metricRiesz_section_contMDiffAt_of_within
    (g : RiemannianMetric I M) (α : M) {x : M}
    (hx : x ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    {Φ : (y : M) → TangentSpace I y →L[ℝ] ℝ}
    (hΦ : ∀ j : Fin (Module.finrank ℝ E),
        ContMDiffWithinAt I 𝓘(ℝ) ∞
          (fun y => Φ y (chartBasisVecFiber (I := I) α j y))
          (trivializationAt E (TangentSpace I) α).baseSet x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
      (fun y : M => TotalSpace.mk' E y (g.metricRiesz y (Φ y))) x := by
  classical
  set triv := trivializationAt E (TangentSpace I) α with htriv_def
  set s := triv.baseSet
  have hopen : IsOpen s := triv.open_baseSet
  have hs_nhds : s ∈ nhds x := hopen.mem_nhds hx
  -- Step 1: per-point smoothness of each scalar coefficient.
  have hcoef_at : ∀ i : Fin (Module.finrank ℝ E),
      ContMDiffAt I 𝓘(ℝ) ∞
        (fun y => ∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) x := by
    intro i
    have hsum :
        ContMDiffWithinAt I 𝓘(ℝ) ∞
          (fun y => ∑ j, chartInvGramMatrix (I := I) g α y i j *
              Φ y (chartBasisVecFiber (I := I) α j y)) s x := by
      refine contMDiffWithinAt_finset_sum (fun j _ => ?_)
      exact ((chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j) x hx).mul (hΦ j)
    exact hsum.contMDiffAt hs_nhds
  -- Step 2: per-point smoothness of the bundle-section sum at x.
  -- Reduce to scalar smoothness of the trivialized fiber via the equation
  -- `(triv ⟨y, sum⟩).2 = ∑ i, c_i(y) • (Module.finBasis ℝ E i : E)` on s.
  have hsnd_eq : ∀ y ∈ s,
      (triv ⟨y,
          ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                Φ y (chartBasisVecFiber (I := I) α j y)) •
            chartBasisVecFiber (I := I) α i y⟩).2
        = ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
            Φ y (chartBasisVecFiber (I := I) α j y)) •
          (Module.finBasis ℝ E i : E) := by
    intro y hy
    have hsnd_apply : ∀ v : TangentSpace I y,
        (triv ⟨y, v⟩).2 = triv.continuousLinearEquivAt ℝ y hy v := by
      intro v
      exact congrArg Prod.snd (triv.apply_eq_prod_continuousLinearEquivAt ℝ y hy v)
    rw [hsnd_apply]
    rw [map_sum (triv.continuousLinearEquivAt ℝ y hy)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [(triv.continuousLinearEquivAt ℝ y hy).map_smul]
    congr 1
    rw [← hsnd_apply (chartBasisVecFiber (I := I) α i y)]
    exact trivializationAt_chartBasisVec_snd (I := I) α i hy
  -- Smoothness of the chart-form section at x via `contMDiffAt_section_iff`.
  have hChartLocal_at :
      ContMDiffAt I (I.prod 𝓘(ℝ, E)) ∞
        (fun y : M => TotalSpace.mk' E y
          (∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
                  Φ y (chartBasisVecFiber (I := I) α j y)) •
              chartBasisVecFiber (I := I) α i y)) x := by
    rw [triv.contMDiffAt_section_iff (IB := I) (n := ∞) hx]
    have hRHS_at :
        ContMDiffAt I 𝓘(ℝ, E) ∞
          (fun y => ∑ i, (∑ j, chartInvGramMatrix (I := I) g α y i j *
              Φ y (chartBasisVecFiber (I := I) α j y)) •
            (Module.finBasis ℝ E i : E)) x := by
      refine contMDiffAt_finset_sum (fun i _ => ?_)
      exact (hcoef_at i).smul (contMDiffAt_const (c := (Module.finBasis ℝ E i : E)))
    refine hRHS_at.congr_of_eventuallyEq ?_
    filter_upwards [hs_nhds] with y hy
    exact hsnd_eq y hy
  -- Step 3: replace chart-form with metricRiesz on a nbhd of x.
  refine hChartLocal_at.congr_of_eventuallyEq ?_
  filter_upwards [hs_nhds] with y hy
  show TotalSpace.mk' E y _ = TotalSpace.mk' E y _
  rw [(metricRiesz_chart_form (I := I) g α hy (Φ y)).symm]


end Tensor
end PetersenLib

end

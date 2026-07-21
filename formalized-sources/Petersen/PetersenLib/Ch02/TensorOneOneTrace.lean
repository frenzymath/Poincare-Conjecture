import PetersenLib.Ch02.TensorOneOne
import PetersenLib.Ch02.VolumeDivergence
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Petersen Ch. 2, §2.5 — the trace of a `(1,1)`-tensor field

The fibrewise (frame-independent) trace `tr S : M → ℝ` of a `(1,1)`-tensor field
`S` (`traceEndField`), with the metric frame-sum formula
`tr S = Σᵢ g(Eᵢ, S(Eᵢ))` for a `g`-orthonormal frame `Eᵢ`
(`traceEndField_eq_sum`), from Mathlib's `LinearMap.trace_eq_sum_inner` and the
fact that the tangent-fibre inner product is `g`.

This is the trace half of Exercises 2.5.9(1) and 2.5.10(1).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.5, Exercises 9–10.
-/

set_option linter.unusedSectionVars false

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

noncomputable section

namespace PetersenLib

open Module (finrank)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Trace

variable [FiniteDimensional ℝ E] [NeZero (finrank ℝ E)] [hm : HasMetric I M]

/-- **Math.** The **trace** of a `(1,1)`-tensor field `S`, `tr S : M → ℝ`, the
fibrewise trace `x ↦ tr(S_x)` of the endomorphism `S_x` (Petersen §2.5, Ex. 9/10).
It is frame-independent (does not reference the metric). -/
def traceEndField (S : EndField I M) : M → ℝ :=
  fun x => LinearMap.trace ℝ (TangentSpace I x) (S x).toLinearMap

theorem traceEndField_apply (S : EndField I M) (x : M) :
    traceEndField S x = LinearMap.trace ℝ (TangentSpace I x) (S x).toLinearMap := rfl

/-- **Math.** The **metric frame-sum formula for the trace**: for any `g`-orthonormal
frame `E₁, …, Eₙ` of `T_xM`, `tr(S_x) = Σᵢ g(Eᵢ, S(Eᵢ))`. Immediate from Mathlib's
`LinearMap.trace_eq_sum_inner` (trace as a sum of inner products over an orthonormal
basis) and the fact that the tangent-fibre inner product is `g`
(`hasMetric_metricInner_eq_inner`). -/
theorem traceEndField_eq_sum (S : EndField I M) (x : M)
    (v : Fin (finrank ℝ E) → TangentSpace I x)
    (hv : ∀ i j, hm.metric.metricInner x (v i) (v j) = if i = j then (1 : ℝ) else 0) :
    traceEndField S x = ∑ i, hm.metric.metricInner x (v i) (S x (v i)) := by
  -- assemble the orthonormal frame into an orthonormal basis
  have hon : Orthonormal ℝ v := orthonormal_of_metricInner_ite hv
  have hb : Orthonormal ℝ (basisOfMetricOrthonormal hv) := by
    have : (basisOfMetricOrthonormal hv : Fin (finrank ℝ E) → TangentSpace I x) = v := by
      funext i; exact basisOfMetricOrthonormal_apply hv i
    rw [show ⇑(basisOfMetricOrthonormal hv) = v from this]
    exact hon
  set b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ (TangentSpace I x) :=
    (basisOfMetricOrthonormal hv).toOrthonormalBasis hb with hbdef
  have hbi : ∀ i, b i = v i := by
    intro i
    rw [hbdef, Module.Basis.coe_toOrthonormalBasis, basisOfMetricOrthonormal_apply]
  rw [traceEndField_apply, LinearMap.trace_eq_sum_inner (S x).toLinearMap b]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hbi i, hasMetric_metricInner_eq_inner]
  rfl

end Trace

section TraceCommute

variable [I.Boundaryless] [CompleteSpace E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
  [NeZero (finrank ℝ E)] [SigmaCompactSpace M] [T2Space M] [hm : HasMetric I M]

/-! ## Exercise 2.5.9(1): `tr(∇_X S) = ∇_X(tr S)` -/

/-- **Math.** **Exercise 2.5.9(1).** For a smooth `(1,1)`-tensor `S`, contraction
commutes with covariant differentiation: `∇_X(tr S) = tr(∇_X S)`. Formalized
against a smooth `g`-orthonormal frame `Eᵢ` near `x` (which computes both the
trace, by `traceEndField_eq_sum`, and its `(∇_X S)`-contraction). The proof:
differentiate `tr S = Σᵢ g(Eᵢ, S(Eᵢ))` by metric compatibility, subtract the
frame contraction of `∇_X S`, and cancel the remaining
`Σᵢ [g(∇_X Eᵢ, S(Eᵢ)) + g(Eᵢ, S(∇_X Eᵢ))]` using the skew-symmetry
`g(∇_X Eᵢ, Eⱼ) + g(Eᵢ, ∇_X Eⱼ) = 0` of the connection form (from `∇g = 0` applied
to `g(Eᵢ, Eⱼ) = δᵢⱼ`) together with the orthonormal frame expansion. -/
theorem traceEndField_covariantDerivative_commute
    (S : EndField I M) (hS : IsSmoothEndField S)
    (X : Π q : M, TangentSpace I q)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then (1 : ℝ) else 0) :
    directionalDerivative X (traceEndField S) x
      = ∑ i, hm.metric.metricInner x (Efr i x)
          (covariantDerivativeEndField (hm.metric.leviCivita).toAffineConnection X S (Efr i) x) := by
  classical
  set g := hm.metric with hg
  set D := g.leviCivita with hD
  have hxU : x ∈ U := mem_of_mem_nhds hU
  have hSsmooth : ∀ i, IsSmoothVectorField (applyEndField S (Efr i)) := fun i => hS _ (hEs i)
  -- abbreviations
  set a : Fin (finrank ℝ E) → Fin (finrank ℝ E) → ℝ :=
    fun i j => g.metricInner x (D.covField X (Efr i) x) (Efr j x) with ha
  -- linearity of the fibre pairing over finite `•`-sums
  have hlinL : ∀ (c : Fin (finrank ℝ E) → ℝ) (v : Fin (finrank ℝ E) → TangentSpace I x)
      (w : TangentSpace I x),
      g.metricInner x (∑ j, c j • v j) w = ∑ j, c j * g.metricInner x (v j) w := by
    intro c v w
    simp only [hg, hasMetric_metricInner_eq_inner, sum_inner, real_inner_smul_left]
  have hlinR : ∀ (c : Fin (finrank ℝ E) → ℝ) (u : TangentSpace I x)
      (v : Fin (finrank ℝ E) → TangentSpace I x),
      g.metricInner x u (∑ j, c j • v j) = ∑ j, c j * g.metricInner x u (v j) := by
    intro c u v
    simp only [hg, hasMetric_metricInner_eq_inner, inner_sum, real_inner_smul_right]
  -- (1) the trace equals the frame sum near `x`, so its derivative splits
  have htr : traceEndField S =ᶠ[𝓝 x]
      fun y => ∑ i, g.metricInner y (Efr i y) (S y (Efr i y)) := by
    filter_upwards [hU] with y hy
    exact traceEndField_eq_sum S y (fun i => Efr i y) (fun i j => horth y hy i j)
  have hdiff : ∀ i, MDifferentiableAt I 𝓘(ℝ)
      (fun y => g.metricInner y (Efr i y) (S y (Efr i y))) x := by
    intro i
    have hcm := (metricOperator_isTensorOperator g).smooth_eval
      ![Efr i, applyEndField S (Efr i)]
      (by intro j; fin_cases j; exacts [hEs i, hSsmooth i])
    exact hcm.mdifferentiableAt (by decide)
  have hmf : mfderiv I 𝓘(ℝ) (traceEndField S) x
      = mfderiv I 𝓘(ℝ) (fun y => ∑ i, g.metricInner y (Efr i y) (S y (Efr i y))) x :=
    htr.mfderiv_eq
  have hcongr : directionalDerivative X (traceEndField S) x
      = directionalDerivative X (fun y => ∑ i, g.metricInner y (Efr i y) (S y (Efr i y))) x := by
    simp only [directionalDerivative_apply]
    exact congrArg (fun L => L (X x)) hmf
  rw [hcongr, directionalDerivative_finset_sum (fun i _ => hdiff i) X]
  -- (2) differentiate each summand by metric compatibility
  have hsummand : ∀ i, directionalDerivative X
      (fun y => g.metricInner y (Efr i y) (S y (Efr i y))) x
      = g.metricInner x (D.covField X (Efr i) x) (S x (Efr i x))
        + g.metricInner x (Efr i x) (D.covField X (applyEndField S (Efr i)) x) := by
    intro i
    have hmc := D.metric_compat (hEs i) (hSsmooth i) x (X x)
    rw [dirTangent_eq_directionalDerivative] at hmc
    simpa only [AffineConnection.covField_apply, applyEndField_apply] using hmc
  rw [Finset.sum_congr rfl (fun i _ => hsummand i)]
  -- (3) rewrite the RHS frame contraction
  have hrhs : ∀ i, g.metricInner x (Efr i x)
      (covariantDerivativeEndField D.toAffineConnection X S (Efr i) x)
      = g.metricInner x (Efr i x) (D.covField X (applyEndField S (Efr i)) x)
        - g.metricInner x (Efr i x) (S x (D.covField X (Efr i) x)) := by
    intro i
    rw [covariantDerivativeEndField_apply, ← AffineConnection.covField_apply,
      ← AffineConnection.covField_apply, g.metricInner_sub_right]
  rw [Finset.sum_congr rfl (fun i _ => hrhs i)]
  -- (4) skew-symmetry of the connection form `a i j + a j i = 0`
  have hskew : ∀ i j, a i j + a j i = 0 := by
    intro i j
    have hconst : (fun y => g.metricInner y (Efr i y) (Efr j y)) =ᶠ[𝓝 x]
        fun _ => (if i = j then (1 : ℝ) else 0) := by
      filter_upwards [hU] with y hy; exact horth y hy i j
    have hd0 : directionalDerivative X (fun y => g.metricInner y (Efr i y) (Efr j y)) x = 0 := by
      rw [directionalDerivative_apply, hconst.mfderiv_eq, mfderiv_const]; rfl
    have hmc := D.metric_compat (hEs i) (hEs j) x (X x)
    rw [dirTangent_eq_directionalDerivative, hd0] at hmc
    have h1 : a i j = g.metricInner x (D.cov x (X x) (Efr i)) (Efr j x) := rfl
    have h2 : a j i = g.metricInner x (Efr i x) (D.cov x (X x) (Efr j)) := by
      show g.metricInner x (D.cov x (X x) (Efr j)) (Efr i x) = _
      exact g.metricInner_comm x (D.cov x (X x) (Efr j)) (Efr i x)
    rw [h1, h2]; linarith [hmc]
  -- expansion of `∇_X Eᵢ` in the orthonormal frame at `x`
  have hexp : ∀ i, D.covField X (Efr i) x = ∑ j, a i j • Efr j x :=
    fun i => metricInner_orthonormal_expansion (horth x hxU) (D.covField X (Efr i) x)
  -- (5) expand each residual summand `g(∇Eᵢ,SEᵢ) + g(Eᵢ,S∇Eᵢ)` in the frame
  have hres : ∀ i, g.metricInner x (D.covField X (Efr i) x) (S x (Efr i x))
        + g.metricInner x (Efr i x) (S x (D.covField X (Efr i) x))
      = ∑ j, (a i j * g.metricInner x (Efr j x) (S x (Efr i x))
          + a i j * g.metricInner x (Efr i x) (S x (Efr j x))) := by
    intro i
    have hL : g.metricInner x (D.covField X (Efr i) x) (S x (Efr i x))
        = ∑ j, a i j * g.metricInner x (Efr j x) (S x (Efr i x)) := by
      conv_lhs => rw [hexp i]
      exact hlinL (a i) (fun j => Efr j x) (S x (Efr i x))
    have hR : g.metricInner x (Efr i x) (S x (D.covField X (Efr i) x))
        = ∑ j, a i j * g.metricInner x (Efr i x) (S x (Efr j x)) := by
      conv_lhs => rw [hexp i, map_sum]
      rw [show (fun j => (S x) (a i j • Efr j x)) = fun j => a i j • (S x) (Efr j x) from
        funext fun j => by rw [map_smul]]
      exact hlinR (a i) (Efr i x) (fun j => S x (Efr j x))
    rw [hL, hR, ← Finset.sum_add_distrib]
  -- reduce to the residual sum, cancelling the shared `g(Eᵢ,∇(S Eᵢ))` terms
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Finset.sum_congr rfl (fun i _ => by rw [← hres i]; ring :
      ∀ i ∈ Finset.univ,
        (g.metricInner x (D.covField X (Efr i) x) (S x (Efr i x))
            + g.metricInner x (Efr i x) (D.covField X (applyEndField S (Efr i)) x))
          - (g.metricInner x (Efr i x) (D.covField X (applyEndField S (Efr i)) x)
            - g.metricInner x (Efr i x) (S x (D.covField X (Efr i) x)))
        = ∑ j, (a i j * g.metricInner x (Efr j x) (S x (Efr i x))
            + a i j * g.metricInner x (Efr i x) (S x (Efr j x))))]
  -- (6) the double sum vanishes by skew-symmetry
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_add_distrib), Finset.sum_add_distrib,
    show (∑ i, ∑ j, a i j * g.metricInner x (Efr j x) (S x (Efr i x)))
        = ∑ i, ∑ j, a j i * g.metricInner x (Efr i x) (S x (Efr j x)) from Finset.sum_comm,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  rw [← add_mul, add_comm (a j i) (a i j), hskew i j, zero_mul]

/-! ## Exercise 2.5.10(1): `tr(L_X S) = L_X(tr S)` -/

/-- **Math.** **Exercise 2.5.10(1).** For a smooth `(1,1)`-tensor `S`, contraction
commutes with Lie differentiation: `L_X(tr S) = tr(L_X S)`. Since `tr S : M → ℝ`
is a function, `L_X(tr S) = D_X(tr S)`; the trace of `L_X S` is computed against a
smooth `g`-orthonormal frame `Eᵢ` near `x` (as `∑ᵢ g(Eᵢ, (L_X S)(Eᵢ))`, mirroring
Ex. 2.5.9(1)). The proof reduces to the covariant case: torsion-freeness of the
Levi-Civita connection gives the pointwise identity
`(L_X S)(Y) = (∇_X S)(Y) − ∇_{S Y}X + S(∇_Y X)`, so the frame contraction splits as
`tr(∇_X S) − tr(∇X ∘ S) + tr(S ∘ ∇X)`, where `∇X : v ↦ ∇_v X` is the fibrewise
endomorphism (linear in the direction because a connection is a `(1,1)`-tensor in
its direction slot). The two composition traces cancel by cyclicity of the trace
(`LinearMap.trace_mul_comm`), leaving `tr(∇_X S) = ∇_X(tr S)` from
`traceEndField_covariantDerivative_commute`. -/
theorem traceEndField_lieDerivative_commute
    (S : EndField I M) (hS : IsSmoothEndField S)
    {X : Π q : M, TangentSpace I q} (hX : IsSmoothVectorField X)
    {Efr : Fin (finrank ℝ E) → Π q : M, TangentSpace I q}
    (hEs : ∀ i, IsSmoothVectorField (Efr i))
    {U : Set M} {x : M} (hU : U ∈ 𝓝 x)
    (horth : ∀ y ∈ U, ∀ i j,
      hm.metric.metricInner y (Efr i y) (Efr j y) = if i = j then (1 : ℝ) else 0) :
    directionalDerivative X (traceEndField S) x
      = ∑ i, hm.metric.metricInner x (Efr i x) (lieDerivativeEndField X S (Efr i) x) := by
  classical
  have hxU : x ∈ U := mem_of_mem_nhds hU
  -- Ex. 2.5.9(1): the covariant trace already commutes with `∇_X`.
  have hA := traceEndField_covariantDerivative_commute S hS X hEs hU horth
  set g := hm.metric with hg
  set D := g.leviCivita with hD
  -- trace-against-frame for an arbitrary fibre endomorphism at `x`
  have htr : ∀ R : TangentSpace I x →ₗ[ℝ] TangentSpace I x,
      LinearMap.trace ℝ (TangentSpace I x) R
        = ∑ i, g.metricInner x (Efr i x) (R (Efr i x)) := by
    intro R
    have hvv : ∀ i j, g.metricInner x (Efr i x) (Efr j x) = if i = j then (1 : ℝ) else 0 :=
      fun i j => horth x hxU i j
    have hon : Orthonormal ℝ (fun i => Efr i x) := orthonormal_of_metricInner_ite hvv
    have hb : Orthonormal ℝ (basisOfMetricOrthonormal hvv) := by
      have hcoe : (basisOfMetricOrthonormal hvv : Fin (finrank ℝ E) → TangentSpace I x)
          = fun i => Efr i x := by
        funext i; exact basisOfMetricOrthonormal_apply hvv i
      rw [show ⇑(basisOfMetricOrthonormal hvv) = fun i => Efr i x from hcoe]
      exact hon
    set b : OrthonormalBasis (Fin (finrank ℝ E)) ℝ (TangentSpace I x) :=
      (basisOfMetricOrthonormal hvv).toOrthonormalBasis hb with hbdef
    have hbi : ∀ i, b i = Efr i x := by
      intro i
      rw [hbdef, Module.Basis.coe_toOrthonormalBasis, basisOfMetricOrthonormal_apply]
    rw [LinearMap.trace_eq_sum_inner R b]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hbi i, hasMetric_metricInner_eq_inner]
  -- torsion-free identity `(L_X S)(Y) = (∇_X S)(Y) − ∇_{S Y}X + S(∇_Y X)`
  have hval : ∀ i, lieDerivativeEndField X S (Efr i) x
      = covariantDerivativeEndField D.toAffineConnection X S (Efr i) x
        - D.cov x (S x (Efr i x)) X + S x (D.cov x (Efr i x) X) := by
    intro i
    have hSi : IsSmoothVectorField (applyEndField S (Efr i)) := hS _ (hEs i)
    have htf1 := D.torsion_free hX hSi x
    have htf2 := D.torsion_free hX (hEs i) x
    rw [lieDerivativeEndField_apply, covariantDerivativeEndField_apply, ← htf1, ← htf2,
      map_sub]
    simp only [applyEndField_apply]
    abel
  -- pair each summand with `Eᵢ` and split the fibre pairing
  have hsummand : ∀ i,
      g.metricInner x (Efr i x) (lieDerivativeEndField X S (Efr i) x)
      = g.metricInner x (Efr i x)
          (covariantDerivativeEndField D.toAffineConnection X S (Efr i) x)
        - g.metricInner x (Efr i x) (D.cov x (S x (Efr i x)) X)
        + g.metricInner x (Efr i x) (S x (D.cov x (Efr i x) X)) := by
    intro i
    rw [hval i, g.metricInner_add_right, g.metricInner_sub_right]
  -- the two composition traces `tr(∇X ∘ S) = tr(S ∘ ∇X)` cancel by cyclicity
  have hBC : ∑ i, g.metricInner x (Efr i x) (D.cov x (S x (Efr i x)) X)
      = ∑ i, g.metricInner x (Efr i x) (S x (D.cov x (Efr i x) X)) := by
    let Pmap : TangentSpace I x →ₗ[ℝ] TangentSpace I x :=
      { toFun := fun v => D.cov x v X
        map_add' := fun v w => D.add_direction x v w X
        map_smul' := fun c v => D.smul_direction x c v X }
    let Qmap : TangentSpace I x →ₗ[ℝ] TangentSpace I x := (S x).toLinearMap
    have e1 : ∑ i, g.metricInner x (Efr i x) (D.cov x (S x (Efr i x)) X)
        = LinearMap.trace ℝ (TangentSpace I x) (Pmap * Qmap) := (htr (Pmap * Qmap)).symm
    have e2 : ∑ i, g.metricInner x (Efr i x) (S x (D.cov x (Efr i x) X))
        = LinearMap.trace ℝ (TangentSpace I x) (Qmap * Pmap) := (htr (Qmap * Pmap)).symm
    rw [e1, e2]
    exact LinearMap.trace_mul_comm ℝ Pmap Qmap
  rw [Finset.sum_congr rfl (fun i _ => hsummand i), Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← hA, hBC]
  ring

end TraceCommute

end PetersenLib

end

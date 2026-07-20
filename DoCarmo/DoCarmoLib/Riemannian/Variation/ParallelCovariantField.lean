import DoCarmoLib.Riemannian.Variation.CovariantField
import DoCarmoLib.Riemannian.Jacobi.ParallelFieldAlong

/-!
# Parallel fields as covariant-derivative pairs

Two small bridges from the parallel-field predicate `IsParallelFieldAlongOn`
(`Jacobi/ParallelFieldAlong.lean`) to the covariant-derivative-pair predicate
`IsCovariantDerivFieldAlongOn` (`Variation/CovariantField.lean`) that the second-variation
formulas of `Variation/SecondVariationFormula.lean` consume.  They are what let the fields of
do Carmo's Ch. 9 §3 applications — a parallel field `e` along a geodesic, and the scaled field
`V(t)=φ(t)\,e(t)` of Bonnet–Myers (`φ=\sin\pi t`) and Synge–Weinstein — be presented as the
`(V, DV)` pairs the theorems require.

* `IsParallelFieldAlongOn.isCovariantDerivFieldAlongOn` — a parallel field carries the
  covariant derivative `0` (`IsParallelSolOn` *is* `IsCovariantDerivSolOn` with `DV = 0`).  In
  particular the velocity of a geodesic (`isParallelFieldAlongOn_velocity`) supplies the
  geodesic hypothesis `hgeo : IsCovariantDerivFieldAlongOn … (fun _ => 0)`.
* `IsParallelFieldAlongOn.smul_fun` — for a differentiable scalar `φ : ℝ → ℝ` and a parallel
  field `e`, the field `φ·e` carries the covariant derivative `φ'·e`, by the Leibniz rule
  `D/dt(φ·e) = φ'·e + φ·(De/dt) = φ'·e` (the second term drops because `e` is parallel).  This
  is do Carmo's `D V/dt = φ' e` for `V = φ e`, and its second covariant derivative
  `D²V/dt² = φ'' e` is a second application.

Reference: do Carmo, *Riemannian Geometry*, Ch. 2, Prop. 2.2 (b) (Leibniz), used at Ch. 9 §3.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false
set_option autoImplicit false

noncomputable section

namespace Riemannian.Variation

open Riemannian.Jacobi

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** A **parallel field** `e` along `γ` carries the covariant derivative `0`: the
pair `(e, 0)` is an `IsCovariantDerivFieldAlongOn`.  `IsParallelSolOn` is literally
`IsCovariantDerivSolOn` with the covariant-derivative slot `0` (the chart certificate's
derivative is `0 - Γ = -Γ`).

Applied to `isParallelFieldAlongOn_velocity`, this discharges the geodesic hypothesis
`hgeo : IsCovariantDerivFieldAlongOn g γ γ' (fun _ => 0)` of the second-variation formulas. -/
theorem _root_.Riemannian.Jacobi.IsParallelFieldAlongOn.isCovariantDerivFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : ℝ → E} {a b : ℝ}
    (he : Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b) :
    IsCovariantDerivFieldAlongOn (I := I) g γ e (fun _ => 0) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := he t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
  intro t ht
  have hz : chartVectorRep (I := I) γ α (fun _ => (0 : E)) t = 0 := by
    simp [chartVectorRep_apply]
  rw [hz, zero_sub]
  exact hcert t ht

/-- **Math.** do Carmo Ch. 2, Prop. 2.2 (b), the **Leibniz rule** for a parallel field: if
`e` is parallel along `γ` and `φ : ℝ → ℝ` is differentiable, then `φ·e` carries the covariant
derivative `φ'·e`:
$$\frac{D}{dt}(\varphi\,e) = \varphi'\,e + \varphi\,\frac{De}{dt} = \varphi'\,e .$$

This is the field do Carmo's Ch. 9 §3 proofs use: `V(t) = (\sin\pi t)\,e(t)` with `e`
parallel has `V' = (\pi\cos\pi t)\,e` (this lemma) and `V'' = (-\pi^2\sin\pi t)\,e` (a second
application), giving the pair `(V, V')` that `deriv_deriv_dcEnergy_eq_indexForm` consumes. -/
theorem _root_.Riemannian.Jacobi.IsParallelFieldAlongOn.smul_fun
    {g : RiemannianMetric I M} {γ : ℝ → M} {e : ℝ → E} {φ : ℝ → ℝ} {a b : ℝ}
    (he : Jacobi.IsParallelFieldAlongOn (I := I) g γ e a b) (hφ : Differentiable ℝ φ) :
    IsCovariantDerivFieldAlongOn (I := I) g γ (fun t => φ t • e t)
      (fun t => deriv φ t • e t) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hcert⟩ := he t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
  intro t ht
  -- read `φ·e` and `φ'·e` in the chart as `φ • (chartVectorRep e)`, resp. `φ' • (…)`
  have hVc : chartVectorRep (I := I) γ α (fun τ => φ τ • e τ)
      = fun τ => φ τ • chartVectorRep (I := I) γ α e τ := by
    funext τ; simp only [chartVectorRep_apply, map_smul]
  have hDVc : chartVectorRep (I := I) γ α (fun τ => deriv φ τ • e τ)
      = fun τ => deriv φ τ • chartVectorRep (I := I) γ α e τ := by
    funext τ; simp only [chartVectorRep_apply, map_smul]
  rw [hVc, hDVc]
  -- the parallel certificate gives `(chartVectorRep e)' = -Γ(u̇, chartVectorRep e, u)`
  have hWderiv := hcert t ht
  -- the scalar `φ` is differentiable
  have hφderiv : HasDerivWithinAt φ (deriv φ t)
      (Icc a' b') t := (hφ t).hasDerivAt.hasDerivWithinAt
  -- product rule for scalar • vector
  have hprod := hφderiv.smul hWderiv
  convert hprod using 1
  rw [Geodesic.chartChristoffelContraction_smul_right, smul_neg]
  abel

end Riemannian.Variation

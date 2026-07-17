import PoincareLib.Ch01.ChartIndexSeam

/-!
# Poincaré Ch. 1 — the second variation *is* the abstract index form

This file closes the loop between the two halves of
`prop:minimal-geodesic-no-conjugate` (Morgan–Tian, Ch. 1).

The two halves speak different languages, and until now the sentence that translates
one into the other did not exist:

* **Half 1** (`exists_indexForm_neg_of_isConjugatePointAt`, `IndexFormConjugate`) produces,
  from a conjugate point, a field whose **abstract** index form
  `indexForm (frameCurvOp g γ e)` — a manifold-free quadratic form on solutions of the
  Jacobi ODE `y″ + ℛ(t) y = 0`, read in a parallel `g`-orthonormal frame — is strictly
  **negative**.
* **Half 2** computes the second derivative of the energy of a broken chart variation and
  gets, piece by piece, an integral of the **chart** integrand `chartIndexIntegrand`
  (`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`, `PieceSecondVariation`).

`chartIndexIntegrand_eq_indexIntegrand_frameVec` below says the two integrands are **the
same real number**, pointwise in `t`. It is the composition of the two seams that now
exist:

* `chartIndexIntegrand_eq_metricIndexIntegrand` (`ChartIndexSeam`) — chart integrand
  `=` the intrinsic metric integrand `⟨DV, DV⟩_g + ℛ(V, γ′, γ′, V)`, the step where the
  do Carmo ↔ Morgan–Tian sign flip is absorbed;
* `indexIntegrand_frameVec` (`FrameIndexBridge`) — the intrinsic metric integrand `=` the
  abstract `indexIntegrand (frameCurvOp g γ e)` of the frame coefficients, because the
  coefficient map is a `g`-isometry and `frameCurvOp` is minus the curvature form.

Consequently the second variation of energy, computed in charts, is literally the index
form in which half 1 delivers its negative direction: a minimal geodesic forces
`indexForm ≥ 0`, a conjugate point forces `indexForm < 0`, and the two halves collide.

Blueprint: `prop:minimal-geodesic-no-conjugate`, `claim:second-variation-minimal-geodesic`,
`lem:index-form-negative-at-conjugate`, `lem:second-variation-energy-chart`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open Set Filter Riemannian Module
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- **Math.** **The chart index integrand of the second variation is the abstract index
integrand of the frame coefficients.**

Let `γ` be a geodesic, `V` a field along it with covariant derivative `DV`, and `e` a
`g`-orthonormal frame along `γ`. Let `u` be a `C²` two-parameter chart family whose
`s = 0` line reads `γ` in the chart at `α` and whose `∂_s`-field on that line reads `V`.
Then, at every time `t` whose foot lies in the chart source,

`chartIndexIntegrand (chartMetricBilin g α) (chartChristoffelBilin g α) u t`
  `= indexIntegrand (frameCurvOp g γ e) (frameVec V) (frameVec DV) (frameVec V) (frameVec DV) t`.

The left side is what the second variation of the energy of the broken chart variation
*produces* (`deriv_deriv_pieceEnergy_eq_integral_chartIndexIntegrand`); the right side is
the integrand of the *abstract* index form in which half 1 of
`prop:minimal-geodesic-no-conjugate` (`exists_indexForm_neg_of_isConjugatePointAt`)
delivers its strictly negative direction. So the two halves of the proposition are
statements about the same quadratic form, and may be compared. -/
theorem chartIndexIntegrand_eq_indexIntegrand_frameVec (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {V DV : ℝ → E} {e : Fin (Module.finrank ℝ E) → ℝ → E}
    {u : ℝ × ℝ → E} {t : ℝ}
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0)
    (hsrc : γ t ∈ (chartAt H α).source)
    (hgeo : Geodesic.HasGeodesicEquationAt (I := I) g γ t) (hγc : ContinuousAt γ t)
    (hu : ContDiff ℝ 2 u)
    (hline : ∀ᶠ s in 𝓝 t, u ((0 : ℝ), s) = extChartAt I α (γ s))
    (hvar : ∀ᶠ s in 𝓝 t, fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
      = chartVectorRep (I := I) γ α V s)
    (hDV : covariantDerivCoord (I := I) g α (fun s => extChartAt I α (γ s))
      (chartVectorRep (I := I) γ α V) t = chartVectorRep (I := I) γ α DV t) :
    chartIndexIntegrand (chartMetricBilin (I := I) g α)
        (chartChristoffelBilin (I := I) g α) u t
      = indexIntegrand (frameCurvOp (I := I) g γ e)
          (frameVec (I := I) g γ e V) (frameVec (I := I) g γ e DV)
          (frameVec (I := I) g γ e V) (frameVec (I := I) g γ e DV) t :=
  (chartIndexIntegrand_eq_metricIndexIntegrand_of_contDiff (I := I) g hsrc hgeo hγc hu
      hline hvar hDV).trans
    (indexIntegrand_frameVec (I := I) horth)

/-- **Math.** The same identity with the covariant-derivative hypothesis `hDV` discharged
from `IsJacobiFieldAlongOn`, the workspace's own predicate for "`DV` is the covariant
derivative of the Jacobi field `V` along `γ`" — so the interface is demonstrably not
vacuous. Times range over the *open* piece `Ioo c d`, since that is where the chart
covariant derivative is available two-sidedly. -/
theorem chartIndexIntegrand_eq_indexIntegrand_frameVec_of_isJacobiFieldAlongOn
    {g : RiemannianMetric I M} {γ : ℝ → M} {V DV : ℝ → E} {a b : ℝ}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {α : M} {c d : ℝ} {u : ℝ × ℝ → E} {t : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ V DV a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ τ ∈ Icc a b, ContinuousAt γ τ)
    (hsub : Icc c d ⊆ Icc a b)
    (hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H α).source)
    (ht : t ∈ Ioo c d)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0)
    (hu : ContDiff ℝ 2 u)
    (hline : ∀ᶠ s in 𝓝 t, u ((0 : ℝ), s) = extChartAt I α (γ s))
    (hvar : ∀ᶠ s in 𝓝 t, fderiv ℝ u ((0 : ℝ), s) ((1 : ℝ), (0 : ℝ))
      = chartVectorRep (I := I) γ α V s) :
    chartIndexIntegrand (chartMetricBilin (I := I) g α)
        (chartChristoffelBilin (I := I) g α) u t
      = indexIntegrand (frameCurvOp (I := I) g γ e)
          (frameVec (I := I) g γ e V) (frameVec (I := I) g γ e DV)
          (frameVec (I := I) g γ e V) (frameVec (I := I) g γ e DV) t :=
  chartIndexIntegrand_eq_indexIntegrand_frameVec (I := I) g horth
    (hsrc t (Ioo_subset_Icc_self ht))
    (hgeo t (hsub (Ioo_subset_Icc_self ht)))
    (hγc t (hsub (Ioo_subset_Icc_self ht))) hu hline hvar
    (covariantDerivCoord_chartVectorRep_of_isJacobiFieldAlongOn (I := I) hJac hgeo hγc
      hsub hsrc ht)

end PoincareLib

#print axioms PoincareLib.chartIndexIntegrand_eq_indexIntegrand_frameVec
#print axioms PoincareLib.chartIndexIntegrand_eq_indexIntegrand_frameVec_of_isJacobiFieldAlongOn

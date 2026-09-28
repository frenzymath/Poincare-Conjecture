import PetersenLib.Ch02.ChristoffelSymbols

/-!
# Petersen Ch. 2, §2.2 — Normal coordinates and normal frames

Petersen (§2.2, def:pet-ch2-normal-coordinates-frame) calls a coordinate system
*normal* at `p` when the metric components are Euclidean to first order there —
`g_{ij}|_p = δ_{ij}` and `∂_k g_{ij}|_p = 0` — and an orthonormal frame
`E_1, …, E_n` *normal* at `p` when `(∇_v E_i)|_p = 0` for every direction `v`.

* `isNormalCoordinatesAt` — the chart Gram matrix is the identity at `p` and all
  its chart partial derivatives vanish at `p`
  (def:pet-ch2-normal-coordinates-frame);
* `isNormalFrameAt` — an orthonormal frame with vanishing covariant derivative at
  `p` (def:pet-ch2-normal-coordinates-frame);
* `christoffelSymbols_vanish_normalCoordinates` — in coordinates normal at `p`
  the Christoffel symbols vanish, `Γ^k_{ij}|_p = 0`, so the covariant derivative
  is computed at `p` exactly as in Euclidean space
  (rem:pet-ch2-christoffel-normal-coordinates).

The Christoffel-vanishing is immediate from the metric formula
`christoffelSymbols_metric_formula` (`Γ^k_{ij} = ½ g^{kl}(∂_i g_{lj} + ∂_j g_{li}
− ∂_l g_{ij})`): every partial derivative of the Gram matrix vanishes at `p`, so
the whole coordinate expression collapses to `0`.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §2.2.
-/

set_option linter.unusedSectionVars false

open Bundle Set Function Finset
open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [I.Boundaryless] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** A coordinate system is **normal at `p`** (Petersen §2.2,
def:pet-ch2-normal-coordinates-frame) when the chart Gram matrix is the identity
at `p`, `g_{ij}|_p = δ_{ij}`, and all of its chart partial derivatives vanish at
`p`, `∂_k g_{ij}|_p = 0`. -/
def isNormalCoordinatesAt (g : RiemannianMetric I M) (p : M) : Prop :=
  (∀ i j : Fin (Module.finrank ℝ E),
      chartGramOnE (I := I) g p i j (extChartAt I p p) = (if i = j then (1 : ℝ) else 0)) ∧
  (∀ i j k : Fin (Module.finrank ℝ E),
      partialDeriv (E := E) k (chartGramOnE (I := I) g p i j) (extChartAt I p p) = 0)

/-- **Math.** An orthonormal frame `F_1, …, F_n` near `p` is **normal at `p`**
(Petersen §2.2, def:pet-ch2-normal-coordinates-frame) when it is orthonormal at
`p`, `g(F_i, F_j)|_p = δ_{ij}`, and its covariant derivative vanishes at `p`,
`(∇_v F_i)|_p = 0` for every direction `v ∈ T_pM`. -/
def isNormalFrameAt (g : RiemannianMetric I M) (p : M)
    (F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x) : Prop :=
  (∀ i j, g.metricInner p (F i p) (F j p) = (if i = j then (1 : ℝ) else 0)) ∧
  (∀ i, ∀ v : TangentSpace I p, (g.leviCivita).cov p v (F i) = 0)

/-- **Math.** **In coordinates normal at `p` the Christoffel symbols vanish**
(Petersen §2.2, rem:pet-ch2-christoffel-normal-coordinates): `Γ^k_{ij}|_p = 0`.
Immediate from the metric formula `christoffelSymbols_metric_formula`, since every
partial derivative of the Gram matrix vanishes at `p`. Consequently the covariant
derivative at `p` is computed exactly as in Euclidean space,
`(∇_Y X)|_p = (Y^i ∂_i X^j)|_p ∂_j|_p`. -/
theorem christoffelSymbols_vanish_normalCoordinates (g : RiemannianMetric I M) (p : M)
    (h : isNormalCoordinatesAt (I := I) g p) (i j k : Fin (Module.finrank ℝ E)) :
    christoffelSymbolsSecondKind g p i j k = 0 := by
  rw [christoffelSymbols_metric_formula, chartChristoffel_def]
  simp only [h.2, add_zero, sub_zero, mul_zero, Finset.sum_const_zero]

end PetersenLib

end

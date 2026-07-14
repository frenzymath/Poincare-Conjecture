import OpenGALib.Riemannian.Manifold.DoCarmoCh2
import OpenGALib.Riemannian.Connection.ChartChristoffel

/-!
# The chart-Christoffel bridge for do Carmo Prop. 2.2 property (c)

do Carmo's Proposition 2.2 characterises the covariant derivative `D/dt` along a
curve by three properties; property (c) says that when the field along the curve
is the restriction of a global field `Y`, then `DY/dt = ∇_{dc/dt} Y` for the
Levi-Civita connection `∇`. The coordinate core of (c) is already proven
(`Riemannian.covariantDerivCoord_induced`); the sole remaining ingredient is the
identification of the coordinate connection built from the metric Christoffel
symbols (`Riemannian.chartChristoffel`) with the abstract Koszul–Riesz
Levi-Civita connection (`RiemannianMetric.leviCivitaConnection`).

This file records the **algebraic heart** of that identification — do Carmo's
formula (10). Evaluating the Koszul formula (9) on a coordinate frame
`X₁, …, X_n` (with `X_i = ∂/∂x_i` in a chart), the bracket terms drop out
(`[X_i, X_j] = 0`) and the directional derivatives of the metric become partial
derivatives of the Gram matrix (`X_i⟨X_j, X_k⟩ = ∂_i g_{jk}`), so the Koszul
right-hand side collapses to exactly the Gram contraction
`∑_m G_{km} Γ^m_{ij}` of the chart Christoffel symbols
(`chartGram_christoffel_contraction`). The result is the pointwise identity

`⟨X_k, ∇_{X_i} X_j⟩ = ∑_m G_{km} Γ^m_{ij}`,

which is formula (10) tested against the frame, and hence

`∇_{X_i} X_j = ∑_m Γ^m_{ij} X_m`

by non-degeneracy of the metric on the frame basis.

The two genuinely analytic facts about the coordinate frame — bracket vanishing
`[X_i, X_j] = 0` and the directional-derivative–partial-derivative identity
`X_i⟨X_j, X_k⟩ = ∂_i g_{jk}` — enter as explicit hypotheses `hbr` / `hdir`,
isolating them from the algebra; discharging them for the concrete chart frame
`Riemannian.Tensor.chartBasisVec` is the remaining manifold-analytic step of the
bridge `lem:dc-ch2-2-2-c-bridge`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 2 §2, Prop. 2.2 and eq. (10).
-/

set_option linter.unusedSectionVars false

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff Matrix

namespace Riemannian

open Riemannian.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **Math.** do Carmo Ch. 2, eq. (10) — the **chart-Christoffel bridge**, inner
form. For a Levi-Civita connection `∇` (`nabla.IsLeviCivita g`) and a coordinate
frame `X : Fin n → 𝒳(M)` with, at the point `p`,

* vanishing pairwise brackets `[X_a, X_b](p) = 0` (`hbr`), and
* `X_r⟨X_a, X_b⟩(p) = ∂_r G_{ab}` the partial derivative of the chart Gram matrix
  read in the chart at `α` (`hdir`),

the inner product of the frame field `X_k` with `∇_{X_i} X_j` at `p` equals the
Gram contraction of the chart Christoffel symbols:
`⟨X_k, ∇_{X_i} X_j⟩ = ∑_m G_{km} Γ^m_{ij}`.

This is the Koszul formula (9) evaluated on the coordinate frame: the three
bracket terms vanish by `hbr`, the three directional derivatives become the
partial derivatives `∂ G` by `hdir`, and the resulting metric-derivative
combination is `2 ∑_m G_{km} Γ^m_{ij}` by
`chartGram_christoffel_contraction`. -/
theorem christoffel_bridge_inner
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (α p : M)
    (X : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (hbr : ∀ a b, DCLieBracket (X a) (X b) p = 0)
    (hdir : ∀ r a b, (X r).dir (fun q => g.metricInner q (X a q) (X b q)) p
        = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α p))
    (hy : (extChartAt I α).symm (extChartAt I α p)
        ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (i j k : Fin (Module.finrank ℝ E)) :
    g.metricInner p (X k p) ((nabla.cov (X i) (X j)) p)
      = ∑ m, chartGramOnE (I := I) g α k m (extChartAt I α p)
          * chartChristoffel (I := I) g α i j m (extChartAt I α p) := by
  classical
  set y := extChartAt I α p with hyv
  -- Koszul formula (9) with `∇_Y X = ∇_{X_i} X_j`, tested against `Z = X_k`.
  have K := AffineConnection.koszul_formula g nabla hLC.1 hLC.2 (X j) (X i) (X k) p
  -- The three bracket terms vanish because the frame has vanishing pairwise brackets.
  have hb1 : g.metricInner p (DCLieBracket (X j) (X k) p) (X i p) = 0 := by
    rw [hbr j k, g.metricInner_zero_left]
  have hb2 : g.metricInner p (DCLieBracket (X i) (X k) p) (X j p) = 0 := by
    rw [hbr i k, g.metricInner_zero_left]
  have hb3 : g.metricInner p (DCLieBracket (X j) (X i) p) (X k p) = 0 := by
    rw [hbr j i, g.metricInner_zero_left]
  -- The three directional derivatives become partial derivatives of the Gram matrix.
  have hd1 := hdir j i k
  have hd2 := hdir i k j
  have hd3 := hdir k j i
  -- The Gram contraction of the Christoffel symbols.
  have hc := chartGram_christoffel_contraction (I := I) g α k i j y hy
  -- Symmetry of the Gram matrix under exchanging its two indices, passed through
  -- the partial derivative.
  have hsymP : ∀ (a b r : Fin (Module.finrank ℝ E)),
      partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) y
        = partialDeriv (E := E) r (chartGramOnE (I := I) g α b a) y := by
    intro a b r
    unfold partialDeriv
    rw [show chartGramOnE (I := I) g α a b = chartGramOnE (I := I) g α b a from
      funext fun z => chartGramOnE_symm (I := I) g α a b z]
  have s1 := hsymP i k j
  have s2 := hsymP j i k
  linarith [K, hb1, hb2, hb3, hd1, hd2, hd3, hc, s1, s2]

/-- **Math.** do Carmo Ch. 2, eq. (10) — the **chart-Christoffel bridge**, vector
form. Under the same coordinate-frame hypotheses as `christoffel_bridge_inner`,
plus that the frame realises the chart basis at `p`
(`hval : X a p = chartBasisVecFiber α a p`) so that `{X_a p}` is a basis of
`T_pM`, the Levi-Civita covariant derivative of the frame fields is given by the
chart Christoffel symbols:
`∇_{X_i} X_j = ∑_m Γ^m_{ij} X_m` at `p`.

This is do Carmo's formula (10) itself. It is obtained from the inner form
`christoffel_bridge_inner` — which gives `⟨X_k, ∇_{X_i} X_j⟩ = ∑_m G_{km} Γ^m_{ij}`
for every `k` — by non-degeneracy of the metric (`metricInner_eq_iff_eq`): both
sides have the same inner product against every tangent vector, expanded in the
chart-basis `chartBasisFamily`. -/
theorem christoffel_bridge_vector
    (g : RiemannianMetric I M) (nabla : AffineConnection I M)
    (hLC : nabla.IsLeviCivita g) (α p : M)
    (X : Fin (Module.finrank ℝ E) → SmoothVectorField I M)
    (hbr : ∀ a b, DCLieBracket (X a) (X b) p = 0)
    (hdir : ∀ r a b, (X r).dir (fun q => g.metricInner q (X a q) (X b q)) p
        = partialDeriv (E := E) r (chartGramOnE (I := I) g α a b) (extChartAt I α p))
    (hb : p ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (hpe : (extChartAt I α).symm (extChartAt I α p) = p)
    (hval : ∀ a, X a p = chartBasisVecFiber (I := I) α a p)
    (i j : Fin (Module.finrank ℝ E)) :
    (nabla.cov (X i) (X j)) p
      = ∑ m, chartChristoffel (I := I) g α i j m (extChartAt I α p) • X m p := by
  classical
  set y := extChartAt I α p with hyv
  -- The Gram matrix at `p`, read in the chart, is the frame inner product.
  have hgram : ∀ a b, chartGramOnE (I := I) g α a b y = g.metricInner p (X a p) (X b p) := by
    intro a b
    rw [chartGramOnE_def, hpe, chartGramMatrix_apply, hval a, hval b]
    rfl
  -- Bilinear expansion of the metric against a linear combination of frame vectors.
  have expandC : ∀ (U : TangentSpace I p) (c : Fin (Module.finrank ℝ E) → ℝ),
      g.metricInner p U (∑ m, c m • X m p) = ∑ m, c m * g.metricInner p U (X m p) := by
    intro U c
    show (g.inner p U) (∑ m, c m • X m p) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_eq_mul]; rfl
  -- Inner identity against each frame vector: both `∇` and the Christoffel sum agree.
  have key : ∀ k, g.metricInner p (X k p) ((nabla.cov (X i) (X j)) p)
      = g.metricInner p (X k p) (∑ m, chartChristoffel (I := I) g α i j m y • X m p) := by
    intro k
    have hInner := christoffel_bridge_inner (I := I) g nabla hLC α p X hbr hdir
      (by rw [hpe]; exact hb) i j k
    rw [hInner, expandC (X k p) (fun m => chartChristoffel (I := I) g α i j m y)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hgram k m, mul_comm]
  -- Non-degeneracy on the chart-basis: equal inner products against everything.
  refine (g.metricInner_eq_iff_eq p _ _).mp (fun Z => ?_)
  set B := chartBasisFamily (I := I) α hb with hB
  have hBval : ∀ m, (B m : TangentSpace I p) = X m p := by
    intro m; rw [hB, chartBasisFamily_apply, hval m]
  have hZ : Z = ∑ m, (B.repr Z m) • X m p := by
    conv_lhs => rw [← B.sum_repr Z]
    exact Finset.sum_congr rfl fun m _ => by rw [hBval m]
  rw [hZ, expandC _ (fun m => B.repr Z m), expandC _ (fun m => B.repr Z m)]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  rw [g.metricInner_comm p _ (X m p), g.metricInner_comm p _ (X m p)]
  exact key m

end Riemannian

end

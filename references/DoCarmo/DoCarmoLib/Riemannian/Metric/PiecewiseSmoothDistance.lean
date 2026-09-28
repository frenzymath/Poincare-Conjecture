import DoCarmoLib.Riemannian.Manifold.DoCarmoCh3CurveRegularity
import DoCarmoLib.Riemannian.Metric.RiemannianDistancePiecewise

/-!
# do Carmo's distance, infimized over his own curve class

`RiemannianDistancePiecewise` defines `piecewiseRiemannianEDist` as an infimum
over explicit data `(γ, n, τ)` and proves it equals mathlib's
`riemannianEDist`.  That is the right statement, but the competitor condition is
spelled out inline rather than named, so nothing connects it to Definition 3.1 —
the definition whose curves do Carmo is actually infimizing over in Ch. 7,
Definition 2.4.

This file supplies that link.  `IsPiecewiseSmoothCurve`
(`DoCarmoCh3CurveRegularity`) is Definition 3.1 read with do Carmo's own
convention that "differentiable" means `C^∞`, so:

* `piecewiseRiemannianEDist_le_pathELength_of_isPiecewiseSmoothCurve` — the
  distance is below the length of every curve in the book's class, which is the
  `≤` half of Definition 2.4 stated against Definition 3.1 rather than against
  raw partition data;
* `riemannianEDist_eq_iInf_isPiecewiseSmoothCurve` — the distance *is* the
  infimum of `pathELength` over Definition 3.1 curves joining the two points.

The second is do Carmo's Definition 2.4 verbatim, with his curve class in the
index of the infimum.  It uses the smoothing theorem
`exists_piecewiseSmooth_pathELength_le` for the hard direction, via the already
proved `piecewiseRiemannianEDist_eq_riemannianEDist`.
-/

open Bundle Manifold Set
open scoped ContDiff Manifold Topology ENNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]

/-- **Math.** A curve in do Carmo's own Definition 3.1 class is one of the
competitors of his Definition 2.4 infimum: the piecewise distance between its
endpoints is at most its length.

This is the `≤` half of Definition 2.4, stated against the named curve class
rather than against raw partition data. -/
theorem piecewiseRiemannianEDist_le_pathELength_of_isPiecewiseSmoothCurve
    (g : RiemannianMetric I M) {c : ℝ → M} {a b : ℝ}
    (hc : Geodesic.IsPiecewiseSmoothCurve I c a b) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨g.toRiemannianMetric⟩
    piecewiseRiemannianEDist (I := I) g (c a) (c b)
      ≤ Manifold.pathELength I c a b := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨-, n, τ, hn, hτ0, hτn, hstrict, hpieces⟩ := hc
  have hτ : ∀ i < n, τ i ≤ τ (i + 1) := fun i hi => (hstrict i hi).le
  have hle : piecewiseRiemannianEDist (I := I) g (c (τ 0)) (c (τ n))
      ≤ Manifold.pathELength I c (τ 0) (τ n) := by
    unfold piecewiseRiemannianEDist
    refine iInf_le_of_le c ?_
    refine iInf_le_of_le n ?_
    refine iInf_le_of_le τ ?_
    refine iInf_le_of_le hn ?_
    refine iInf_le_of_le hτ ?_
    refine iInf_le_of_le hpieces ?_
    exact iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl)
  simpa [hτ0, hτn] using hle

/-- **Math.** **do Carmo Ch. 7, Definition 2.4**, over his own curve class: the
Riemannian distance between `x` and `y` is the infimum of the lengths of the
Definition 3.1 curves joining them.

The `≤` direction is the smoothing theorem
(`exists_piecewiseSmooth_pathELength_le`, through
`piecewiseRiemannianEDist_eq_riemannianEDist`): a `C¹` competitor for mathlib's
infimum is replaced by a chart-straight polygon in the book's class of nearly
the same length.  The `≥` direction telescopes the per-piece bound
`riemannianEDist ≤ pathELength` across the vertices. -/
theorem riemannianEDist_eq_iInf_isPiecewiseSmoothCurve
    (g : RiemannianMetric I M) (x y : M) :
    letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
      ⟨g.toRiemannianMetric⟩
    Manifold.riemannianEDist I x y =
      ⨅ (c : ℝ → M) (a : ℝ) (b : ℝ)
        (_ : Geodesic.IsPiecewiseSmoothCurve I c a b)
        (_ : c a = x) (_ : c b = y),
        Manifold.pathELength I c a b := by
  letI : RiemannianBundle (fun z : M ↦ TangentSpace I z) :=
    ⟨g.toRiemannianMetric⟩
  apply le_antisymm
  · -- every competitor bounds the distance from above, by the telescoped
    -- per-piece bound
    refine le_iInf fun c => le_iInf fun a => le_iInf fun b => ?_
    refine le_iInf fun hc => le_iInf fun hx => le_iInf fun hy => ?_
    obtain ⟨-, n, τ, hn, hτ0, hτn, hstrict, hpieces⟩ := hc
    have hτ : ∀ i < n, τ i ≤ τ (i + 1) := fun i hi => (hstrict i hi).le
    have hτ0n : τ 0 ≤ τ n :=
      Riemannian.Exponential.partition_le hτ (Nat.zero_le n) le_rfl
    have hbound := riemannianEDist_le_pathELength_piecewise_partition g
      (γ := c) (n := n) (τ := τ) (s := τ 0) (t := τ n)
      (fun i hi => (hpieces i hi).of_le (by norm_num)) le_rfl hτ0n le_rfl
    rw [hτ0, hτn] at hbound
    rw [← hx, ← hy]
    exact hbound
  · -- conversely, every `C¹` competitor for mathlib's infimum is matched, up to
    -- `1 + ε`, by a chart-straight polygon in do Carmo's class.  The polygon
    -- produced by the smoothing theorem carries the *integer* partition
    -- `i ↦ (i : ℝ)`, which is strict, so it is a Definition 3.1 curve.
    -- it suffices to beat every strict upper bound `R` of the distance
    refine le_of_forall_gt fun R hR => ?_
    obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hR
    obtain ⟨epsilon, hepsilon, hgap⟩ := exists_pos_ofReal_one_add_mul_lt hlen
    obtain ⟨sigma, n, tau, hn, htau, hsmooth, hsigma0, hsigma1, hsigmaLen⟩ :=
      exists_piecewiseSmooth_pathELength_le (I := I) g hγ hepsilon
    -- the polygon's integer partition is strict, so it is a Definition 3.1 curve
    have hcurve : Geodesic.IsPiecewiseSmoothCurve I sigma (tau 0) (tau n) :=
      Geodesic.IsPiecewiseDifferentiableCurveOfOrder.of_pieces hn rfl rfl htau
        hsmooth
    refine lt_of_le_of_lt (iInf_le_of_le sigma (iInf_le_of_le (tau 0)
      (iInf_le_of_le (tau n) (iInf_le_of_le hcurve
        (iInf_le_of_le (hsigma0.trans hγ0) (iInf_le_of_le (hsigma1.trans hγ1)
          le_rfl)))))) ?_
    exact hsigmaLen.trans_lt hgap

end Riemannian

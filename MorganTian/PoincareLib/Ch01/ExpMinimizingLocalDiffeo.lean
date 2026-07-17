/-
# The exponential map is a local diffeomorphism along a minimal geodesic

`cor:exponential-local-diffeomorphism`: if `γ` is a minimal geodesic on `[0, 1]` starting at `p`
with `X(0) = γ'(0)`, then for every `t₀ < 1` the restriction `γ|[0, t₀]` is again minimal and
`exp_p` is a local diffeomorphism near `t₀ · X(0)`.

The content of "`exp_p` is a local diffeomorphism near `t₀ X(0)`" — the content the book's proof
actually establishes — is that the differential `d(exp_p)_{t₀ X(0)}` is a **linear isomorphism**,
together with **local injectivity** of `exp_p` near that point.  Both are already available for a
**unit** radial geodesic inside its minimizing radius
(`expDifferential_isEquiv_of_minimizing_radial`,
`expMapGlobal_locallyInjective_of_minimizing_radial`).  This file is the normalization that recovers
the book's statement for a general minimal geodesic: with `ℓ = |X(0)|_g` and `u = ℓ⁻¹ · X(0)` the
unit direction, `t₀ · X(0) = (t₀ℓ) · u` lies at parameter `t₀ℓ < ℓ`, strictly inside the minimizing
radius, and `globalGeodesic_smul` reparameterizes `γ` onto `γ_u`.

Blueprint: `cor:exponential-local-diffeomorphism`, `prop:minimal-geodesic-no-conjugate`,
`lem:exponential-differential-jacobi`.
-/
import PoincareLib.Ch01.NoConjugateOfMinimizing
import PoincareLib.Ch01.CutLocus

open Set Filter Riemannian Module MeasureTheory
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)]

/-- **Math.** **`cor:exponential-local-diffeomorphism`.** Let `γ_v = exp_p(· v)` be minimal on
`[0, 1]` (`IsMinimizingUpTo … v 1`) with `X(0) = v ≠ 0`. Then for every `t₀ ∈ (0, 1)`:

1. `γ_v|[0, t₀]` is again minimal (`IsMinimizingUpTo … v t₀`);
2. the differential of `exp_p` at `t₀ · v` is a continuous linear isomorphism `D` (read in a chart
   `ζ` about `γ_v(t₀)`);
3. `exp_p` is injective on a neighbourhood of `t₀ · v`.

Together (2) and (3) are the sense in which "`exp_p` is a local diffeomorphism near `t₀ X(0)`",
exactly as the book's proof establishes it (`d(exp_p)_{t₀ X(0)}` an isomorphism).

Blueprint: `cor:exponential-local-diffeomorphism`. -/
theorem expMapGlobal_localDiffeo_of_minimizing
    (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]
    (p : M) {v : E} (hv0 : (v : TangentSpace I p) ≠ 0)
    (hmin : IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) 1)
    {t₀ : ℝ} (ht₀0 : 0 < t₀) (ht₀1 : t₀ < 1) :
    IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) t₀ ∧
      (∃ (ζ : M) (D : E ≃L[ℝ] E),
        expMapGlobal (I := I) g hg p ((t₀ • v : E) : TangentSpace I p) ∈ (chartAt H ζ).source ∧
        HasStrictFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w))
          (D : E →L[ℝ] E) (t₀ • v)) ∧
      (∃ U ∈ 𝓝 ((t₀ • v : E)), Set.InjOn (expMapGlobal (I := I) g hg p) U) := by
  classical
  -- the length `ℓ = |v|_g > 0`, and the unit direction `u = ℓ⁻¹ • v`
  have hpos : 0 < g.metricInner p (v : TangentSpace I p) v := g.metricInner_self_pos p v hv0
  set ℓ : ℝ := Real.sqrt (g.metricInner p (v : TangentSpace I p) v) with hℓ
  have hℓ0 : 0 < ℓ := Real.sqrt_pos.mpr hpos
  have hℓsq : ℓ * ℓ = g.metricInner p (v : TangentSpace I p) v := Real.mul_self_sqrt hpos.le
  set u : E := ℓ⁻¹ • v with hu_def
  -- `u` is a unit vector
  have hu : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p) = 1 := by
    -- proved through a genuinely `TangentSpace`-typed vector so the bilinear-smul lemmas key-match
    -- (writing `ℓ⁻¹ • v` with `v : E` would pick `E`'s smul instance, not the tangent one)
    have key : ∀ w : TangentSpace I p, g.metricInner p (ℓ⁻¹ • w) (ℓ⁻¹ • w)
        = ℓ⁻¹ * (ℓ⁻¹ * g.metricInner p w w) := by
      intro w
      rw [g.metricInner_smul_left, g.metricInner_smul_right]
    have huk : g.metricInner p (u : TangentSpace I p) (u : TangentSpace I p)
        = ℓ⁻¹ * (ℓ⁻¹ * g.metricInner p (v : TangentSpace I p) v) := key (v : TangentSpace I p)
    rw [huk, ← hℓsq]
    field_simp
  -- `c = t₀ · ℓ` lies strictly inside `(0, ℓ)`, and `t₀ • v = c • u`
  set c : ℝ := t₀ * ℓ with hc_def
  have hc0 : 0 < c := mul_pos ht₀0 hℓ0
  have hcℓ : c < ℓ := by
    have h := mul_lt_mul_of_pos_right ht₀1 hℓ0
    simpa using h
  have hcu : (c • u : E) = t₀ • v := by
    show (t₀ * ℓ) • (ℓ⁻¹ • v) = t₀ • v
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hℓ0.ne', mul_one]
  -- the radial minimizing hypothesis for the unit direction `u` on `(0, ℓ)`
  have hmin_u : ∀ s ∈ Ioo (0 : ℝ) ℓ,
      s ≤ dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s) := by
    intro s hs
    have hs0 : 0 ≤ ℓ⁻¹ * s := mul_nonneg (inv_nonneg.mpr hℓ0.le) hs.1.le
    have hs1 : ℓ⁻¹ * s ≤ 1 := by
      rw [← inv_mul_cancel₀ hℓ0.ne']
      exact le_of_lt (mul_lt_mul_of_pos_left hs.2 (inv_pos.mpr hℓ0))
    have hmv : IsMinimizingUpTo (I := I) g hg p (v : TangentSpace I p) (ℓ⁻¹ * s) :=
      IsMinimizingUpTo.mono g hg p v hmin hs0 hs1
    have hmu : IsMinimizingUpTo (I := I) g hg p (u : TangentSpace I p) s :=
      (isMinimizingUpTo_smul g hg p (v : TangentSpace I p) (inv_pos.mpr hℓ0) s).2 hmv
    have heq : dist p (globalGeodesic (I := I) g hg p (u : TangentSpace I p) s)
        = Real.sqrt (g.metricInner p (u : TangentSpace I p) u) * s := hmu
    rw [hu, Real.sqrt_one, one_mul] at heq
    exact heq.ge
  refine ⟨IsMinimizingUpTo.mono g hg p v hmin ht₀0.le ht₀1.le, ?_, ?_⟩
  · -- the differential is a linear isomorphism at `t₀ • v = c • u`
    obtain ⟨ζ, D, hmem, hFD⟩ :=
      expDifferential_isEquiv_of_minimizing_radial (I := I) g hg p hu hc0 hcℓ hmin_u
    rw [hcu] at hmem hFD
    exact ⟨ζ, D, hmem, hFD⟩
  · -- `exp_p` is injective on a neighbourhood of `t₀ • v = c • u`
    obtain ⟨U, hU, hinj⟩ :=
      expMapGlobal_locallyInjective_of_minimizing_radial (I := I) g hg p hu hc0 hcℓ hmin_u
    rw [hcu] at hU
    exact ⟨U, hU, hinj⟩

end PoincareLib

end

#print axioms PoincareLib.expMapGlobal_localDiffeo_of_minimizing

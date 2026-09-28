import MorganTianLib.Ch01.JacobiManifold
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Algebra.Order.Field.Pointwise

/-!
# Poincaré Ch. 1, §1.4 — Jacobi fields and conjugate points under a time rescaling

A geodesic may be run at any constant speed: if `γ` is a geodesic then so is
`γ_c := γ ∘ (c · ·)`, at `c` times the speed (`Riemannian.Geodesic.isGeodesic_comp_mul_left`).
This file transports the *Jacobi* theory across that rescaling.

The point of doing so is that the comparison estimates of §1.5
(`lem:conjugate-sturm`, `MorganTianLib.not_isConjugatePointAt_of_sectionalCurvatureAt_le`) are
stated for **unit-speed** geodesics, while `exp_p` at a tangent vector `v` is the time-`1` value
of the geodesic `γ_v` of speed `|v|_g`. The bridge between "no conjugate point at parameter
`|v|` along the unit-speed geodesic" and "no conjugate point at parameter `1` along `γ_v`" is
exactly a rescaling, and that is what `isConjugatePointAt_comp_mul_left` supplies.

## The rescaling

For `c > 0`, if `(J, DJ)` is a Jacobi field along `γ` on `[0, c·T]`, then

  `J_c(s) = J(c·s)`,  `DJ_c(s) = c · DJ(c·s)`

is a Jacobi field along `γ_c` on `[0, T]`. The factor `c` on the covariant derivative is forced:
`DJ` is a *derivative* in the time parameter, so it picks up one factor of `c` under `t = c·s`,
whereas `J` is a value and picks up none.

Checking the chart pair system is pure homogeneity bookkeeping, since `u̇` picks up a factor `c`:

* `∇J = DJ` reads `J' = DJ − Γ(u̇, J)`, and both sides scale by `c` — the `Γ` term because
  `Γ` is *linear* in its velocity slot (`chartChristoffelContraction_smul_left`).
* `∇DJ = −ℛ(J, u̇)u̇` reads `DJ' = −ℛ(J, u̇)u̇ − Γ(u̇, DJ)`, and both sides scale by `c²` — the
  curvature term because `ℛ(J, u̇)u̇` is *quadratic* in `u̇` (`chartCurvature_smul_velocity`), the
  `Γ` term because it is linear in `u̇` and `DJ` already carries one factor of `c`.

## Main results

* `chartCurvature_smul_velocity` — `ℛ(X, cY)(cZ) = c² · ℛ(X, Y)Z`.
* `IsJacobiFieldOn.comp_mul_left` — the chart-level pair system, rescaled.
* `IsJacobiFieldAlongOn.comp_mul_left` — the manifold-level Jacobi field, rescaled.
* `isConjugatePointAt_comp_mul_left` — a conjugate point at `c·T` along `γ` is a conjugate
  point at `T` along `γ ∘ (c · ·)`.

Blueprint: `def:conjugate-point`, `lem:jacobi-field-coordinates`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

/-! ### Homogeneity of the chart curvature in the velocity slots -/

section AbstractHomogeneity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Math.** **The curvature of a connection is quadratic in its two velocity slots.**
`ℛ(X, cY)(cZ) = c² · ℛ(X, Y)Z`, directly from
`ℛ(X,Y)Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X,Γ(Y,Z)) − Γ(Y,Γ(X,Z))`: each of the four terms is
separately linear in `Y` and in `Z`, `Γ` being a bundled bilinear map and `fderiv ℝ Γ x` a
bundled linear map into bilinear maps.

This is the homogeneity that makes the Jacobi equation `∇∇J = −ℛ(J, u̇)u̇` scale by `c²` when the
geodesic is run at `c` times the speed. -/
theorem christoffelCurvature_smul_velocity (Γ : E → E →L[ℝ] E →L[ℝ] E) (x X Y Z : E) (c : ℝ) :
    christoffelCurvature Γ x X (c • Y) (c • Z)
      = (c * c) • christoffelCurvature Γ x X Y Z := by
  simp only [christoffelCurvature, map_smul, ContinuousLinearMap.smul_apply, smul_smul,
    smul_sub, smul_add]

end AbstractHomogeneity

/-! ### The chart pair system under a time rescaling -/

section Rescale

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless]

/-- **Math.** **The chart curvature is quadratic in the velocity slots**, in the packaging used
by the Jacobi pair system. -/
theorem chartCurvature_smul_velocity (g : RiemannianMetric I M) (α : M) (y X Y Z : E) (c : ℝ) :
    chartCurvature (I := I) g α y X (c • Y) (c • Z)
      = (c * c) • chartCurvature (I := I) g α y X Y Z :=
  christoffelCurvature_smul_velocity _ y X Y Z c

/-- **Math.** **Homogeneity of the Christoffel contraction in its first vector slot**:
`Γ(a·v, w)(y) = a · Γ(v, w)(y)`. The contraction is symmetric in its two vector slots
(`chartChristoffelContraction_symm`) and homogeneous in the second
(`chartChristoffelContraction_smul_right`), so it is homogeneous in the first. -/
theorem chartChristoffelContraction_smul_left (g : RiemannianMetric I M) (α : M)
    (a : ℝ) (v w y : E) :
    Geodesic.chartChristoffelContraction (I := I) g α (a • v) w y
      = a • Geodesic.chartChristoffelContraction (I := I) g α v w y := by
  rw [Geodesic.chartChristoffelContraction_symm (I := I) g α (a • v) w y,
    Geodesic.chartChristoffelContraction_smul_right (I := I) g α w a v y,
    Geodesic.chartChristoffelContraction_symm (I := I) g α w v y]

/-- **Math.** Membership in the rescaled interval: for `c > 0`, `s ∈ [a/c, b/c] ↔ c·s ∈ [a, b]`. -/
private theorem mem_Icc_div_iff {c a b s : ℝ} (hc : 0 < c) :
    s ∈ Icc (a / c) (b / c) ↔ c * s ∈ Icc a b := by
  simp only [mem_Icc, div_le_iff₀ hc, le_div_iff₀ hc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-- **Math.** **The chart Jacobi pair system under a time rescaling.** For `c > 0`, if
`(J, DJ)` solves the chart pair system along the chart curve `u` on `[c·a, c·b]`, then
`(J(c·−), c·DJ(c·−))` solves it along `u(c·−)` on `[a, b]`.

The two equations scale by `c` and `c²` respectively; see the module docstring. -/
theorem IsJacobiFieldOn.comp_mul_left {g : RiemannianMetric I M} {α : M} {u J DJ : ℝ → E}
    {c a b : ℝ} (hc : 0 < c)
    (h : IsJacobiFieldOn (I := I) g α u J DJ (c * a) (c * b)) :
    IsJacobiFieldOn (I := I) g α (fun s => u (c * s)) (fun s => J (c * s))
      (fun s => c • DJ (c * s)) a b := by
  have hIcc : c • Icc a b = Icc (c * a) (c * b) := LinearOrderedField.smul_Icc hc
  -- the rescaled chart velocity picks up one factor of `c`
  have hderivu : ∀ t : ℝ, deriv (fun s => u (c * s)) t = c • deriv u (c * t) := fun t =>
    deriv_comp_mul_left c u t
  have hmem : ∀ t ∈ Icc a b, c * t ∈ Icc (c * a) (c * b) := fun t ht =>
    ⟨mul_le_mul_of_nonneg_left ht.1 hc.le, mul_le_mul_of_nonneg_left ht.2 hc.le⟩
  constructor
  · -- `∇J = DJ`, scaling by `c`
    intro t ht
    have h1 := h.hasDerivWithinAt_fst (c * t) (hmem t ht)
    have h2 : HasDerivWithinAt (fun s => J (c * s))
        (c • (DJ (c * t) - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u (c * t)) (J (c * t)) (u (c * t)))) (Icc a b) t := by
      rw [hasDerivWithinAt_comp_mul_left_smul_iff, hIcc]
      exact h1
    have hrhs : c • (DJ (c * t) - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u (c * t)) (J (c * t)) (u (c * t)))
        = c • DJ (c * t) - Geodesic.chartChristoffelContraction (I := I) g α
            (deriv (fun s => u (c * s)) t) (J (c * t)) (u (c * t)) := by
      rw [hderivu t, chartChristoffelContraction_smul_left, smul_sub]
    rwa [hrhs] at h2
  · -- `∇DJ = −ℛ(J, u̇)u̇`, scaling by `c²`
    intro t ht
    have h1 := h.hasDerivWithinAt_snd (c * t) (hmem t ht)
    -- first rescale time, then multiply the field by the constant `c`
    have h2 : HasDerivWithinAt (fun s => DJ (c * s))
        (c • (-(chartCurvature (I := I) g α (u (c * t)) (J (c * t))
              (deriv u (c * t)) (deriv u (c * t)))
            - Geodesic.chartChristoffelContraction (I := I) g α
                (deriv u (c * t)) (DJ (c * t)) (u (c * t)))) (Icc a b) t := by
      rw [hasDerivWithinAt_comp_mul_left_smul_iff, hIcc]
      exact h1
    have h3 := h2.const_smul c
    -- the target right-hand side is `(c·c) •` the original one
    have hrhs : c • c • (-(chartCurvature (I := I) g α (u (c * t)) (J (c * t))
              (deriv u (c * t)) (deriv u (c * t)))
            - Geodesic.chartChristoffelContraction (I := I) g α
                (deriv u (c * t)) (DJ (c * t)) (u (c * t)))
        = -(chartCurvature (I := I) g α (u (c * t)) (J (c * t))
              (deriv (fun s => u (c * s)) t) (deriv (fun s => u (c * s)) t))
            - Geodesic.chartChristoffelContraction (I := I) g α
                (deriv (fun s => u (c * s)) t) (c • DJ (c * t)) (u (c * t)) := by
      rw [hderivu t, chartCurvature_smul_velocity, chartChristoffelContraction_smul_left,
        Geodesic.chartChristoffelContraction_smul_right, smul_smul, smul_sub, smul_neg,
        smul_smul]
    exact hrhs ▸ h3

/-- **Math.** **A Jacobi field along `γ`, rescaled to a Jacobi field along `γ(c·−)`.**
For `c > 0` and `T ≥ 0`: if `(J, DJ)` is a Jacobi field along `γ` on `[0, c·T]`, then
`(J(c·−), c·DJ(c·−))` is a Jacobi field along `γ(c·−)` on `[0, T]`.

The chart windows transport along the homeomorphism `s ↦ c·s` of `ℝ`, which carries `[0,T]` onto
`[0, c·T]`; the chart readings of the fields transport because the tangent coordinate change is
linear (so the factor `c` on `DJ` passes through it). -/
theorem IsJacobiFieldAlongOn.comp_mul_left {g : RiemannianMetric I M} {γ : ℝ → M}
    {J DJ : ℝ → E} {c T : ℝ} (hc : 0 < c)
    (h : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 (c * T)) :
    IsJacobiFieldAlongOn (I := I) g (fun s => γ (c * s)) (fun s => J (c * s))
      (fun s => c • DJ (c * s)) 0 T := by
  intro t₀ ht₀
  -- the rescaled time lies in the original window
  have hct₀ : c * t₀ ∈ Icc (0 : ℝ) (c * T) :=
    ⟨mul_nonneg hc.le ht₀.1, mul_le_mul_of_nonneg_left ht₀.2 hc.le⟩
  obtain ⟨α, a', b', hab', hmem', hsub', hnhds', hsrc', hsys'⟩ := h (c * t₀) hct₀
  -- pull the chart window back along `s ↦ c·s`
  refine ⟨α, a' / c, b' / c, by gcongr, (mem_Icc_div_iff hc).2 hmem', ?_, ?_, ?_, ?_⟩
  · -- the pulled-back window sits inside `[0, T]`
    intro s hs
    have hcs := hsub' ((mem_Icc_div_iff hc).1 hs)
    exact ⟨nonneg_of_mul_nonneg_right hcs.1 hc, le_of_mul_le_mul_left hcs.2 hc⟩
  · -- the pulled-back window is a neighbourhood of `t₀` within `[0, T]`
    have hmaps : MapsTo (fun s : ℝ => c * s) (Icc 0 T) (Icc 0 (c * T)) := fun s hs =>
      ⟨mul_nonneg hc.le hs.1, mul_le_mul_of_nonneg_left hs.2 hc.le⟩
    have hcont : ContinuousWithinAt (fun s : ℝ => c * s) (Icc 0 T) t₀ :=
      (continuous_const.mul continuous_id).continuousWithinAt
    have hpre : (fun s : ℝ => c * s) ⁻¹' Icc a' b' ∈ 𝓝[Icc 0 T] t₀ :=
      (hcont.tendsto_nhdsWithin hmaps) hnhds'
    have hset : (fun s : ℝ => c * s) ⁻¹' Icc a' b' = Icc (a' / c) (b' / c) := by
      ext s; exact (mem_Icc_div_iff hc).symm
    rwa [hset] at hpre
  · -- the rescaled curve stays in the chart on the pulled-back window
    intro s hs
    exact hsrc' (c * s) ((mem_Icc_div_iff hc).1 hs)
  · -- the chart pair system, rescaled
    have hca : c * (a' / c) = a' := by field_simp
    have hcb : c * (b' / c) = b' := by field_simp
    have hsys := IsJacobiFieldOn.comp_mul_left (I := I) (g := g) (α := α)
      (u := fun τ => extChartAt I α (γ τ))
      (J := chartVectorRep (I := I) γ α J) (DJ := chartVectorRep (I := I) γ α DJ)
      (c := c) (a := a' / c) (b := b' / c) hc (by rw [hca, hcb]; exact hsys')
    -- identify the rescaled chart readings with the chart readings of the rescaled fields
    have hDJ : (fun s => c • chartVectorRep (I := I) γ α DJ (c * s))
        = chartVectorRep (I := I) (fun s => γ (c * s)) α (fun s => c • DJ (c * s)) := by
      funext s
      simp only [chartVectorRep, map_smul]
    rw [hDJ] at hsys
    exact hsys

/-- **Math.** **A conjugate point survives a time rescaling.** For `c > 0` and `T ≥ 0`: if
`γ(c·T)` is conjugate to `γ(0)` along `γ`, then the point at parameter `T` of the rescaled
geodesic `γ(c·−)` — the *same* point of `M` — is conjugate to its start along `γ(c·−)`.

Contrapositively (the form used to prove `lem:local-diffeomorphism-bounded-curvature`): a
no-conjugate-point statement for a **unit-speed** geodesic up to parameter `c` yields a
no-conjugate-point statement at parameter `1` for the geodesic run at speed `c`. -/
theorem isConjugatePointAt_comp_mul_left {g : RiemannianMetric I M} {γ : ℝ → M} {c T : ℝ}
    (hc : 0 < c) (h : IsConjugatePointAt (I := I) g γ (c * T)) :
    IsConjugatePointAt (I := I) g (fun s => γ (c * s)) T := by
  obtain ⟨J, DJ, hJac, ⟨t, htmem, htne⟩, hJ0, hJ1⟩ := h
  refine ⟨fun s => J (c * s), fun s => c • DJ (c * s),
    hJac.comp_mul_left hc, ⟨t / c, ⟨div_nonneg htmem.1 hc.le, ?_⟩, ?_⟩,
    by simpa using hJ0, by simpa using hJ1⟩
  · -- the witness time rescales into `[0, T]`
    rw [div_le_iff₀ hc, mul_comm]
    exact htmem.2
  · -- and the field is still nonzero there
    show J (c * (t / c)) ≠ 0
    rwa [mul_div_cancel₀ t hc.ne']

end Rescale

end MorganTianLib

end

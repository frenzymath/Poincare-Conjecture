import MorganTianLib.Ch01.JacobiExistence
import MorganTianLib.Ch01.JacobiManifold
import MorganTianLib.Ch01.GlobalExp

/-!
# Poincaré Ch. 1, §1.4 — Jacobi fields along the *constant* geodesic

Every no-conjugate-point theorem in this development (`lem:conjugate-sturm`, and through it
`not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`) hypothesises a **unit-speed** geodesic,
so none of them says anything at the zero initial vector: `γ_0` is the constant curve at `p`,
whose speed is `0`, not `1`. Yet `lem:local-diffeomorphism-bounded-curvature` asserts that `exp_p`
is a local diffeomorphism on the *whole* ball `B(0, π/√K)` — a ball that contains the origin. The
blueprint dismisses this with "the same holds trivially at `v = 0`". This file supplies the
"trivially".

## The argument

Along the constant geodesic `γ ≡ p` the velocity `γ̇` vanishes identically, so *every* term of the
chart-level Jacobi pair system that carries a velocity dies:

* the Christoffel contraction `Γ(γ̇, ·)` vanishes (`chartChristoffelContraction_zero_left`);
* the curvature term `ℛ(J, γ̇)γ̇` vanishes, because `ℛ` is linear in each of the two velocity
  slots (`chartCurvature_zero_velocity`, new here).

The system therefore degenerates to `J' = DJ`, `DJ' = 0`, whose solutions are the **affine**
fields `J(t) = t·Z`, `DJ(t) = Z`. Concretely: for each `Z` the pair `(t ↦ t·Z, t ↦ Z)` *is* a
Jacobi field along `γ` (`isJacobiFieldAlongOn_const_linear`), and by Grönwall uniqueness
(`IsJacobiFieldAlongOn.eqOn_zero`) it is the *only* one with that initial data. So a Jacobi field
vanishing at `0` is exactly `J(t) = t·DJ(0)`, and it vanishes again at `t₁ > 0` only if
`DJ(0) = 0`, i.e. only if it is identically zero. Hence no conjugate point — at any positive
parameter, under no curvature hypothesis whatsoever.

## Main results

* `chartCurvature_zero_velocity` — `ℛ(X, 0)0 = 0`.
* `globalGeodesic_zero_vec` — `γ_0 = ` the constant curve at `p`.
* `isJacobiFieldAlongOn_const_linear` — `(t·Z, Z)` is a Jacobi field along the constant geodesic.
* `not_isConjugatePointAt_const` — the constant geodesic has no conjugate point at any `t₁ > 0`.
* `not_isConjugatePointAt_one_zero_vec` — the form consumed by the exponential-map results:
  `γ_0` has no conjugate point of `p` at parameter `1`.

Blueprint: `lem:local-diffeomorphism-bounded-curvature`, `def:conjugate-point`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

open Riemannian.Geodesic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M]

/-! ### The curvature term dies on a zero velocity -/

/-- **Math.** `ℛ(X, 0)0 = 0`: the curvature of a connection is linear in each of its three
slots, so it vanishes as soon as one of them does. Here the two slots that are filled with the
*velocity* of the curve are the ones that vanish, which is what kills the curvature term of the
Jacobi equation along a constant geodesic.

All four terms of `christoffelCurvature Γ x X Y Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X,Γ(Y,Z))
− Γ(Y,Γ(X,Z))` vanish at `Y = Z = 0`, each by `map_zero` of a continuous linear map. -/
theorem christoffelCurvature_zero_velocity (Γ : E → E →L[ℝ] E →L[ℝ] E) (x X : E) :
    christoffelCurvature Γ x X 0 0 = 0 := by
  simp [christoffelCurvature]

/-- **Math.** The chart-level Riemann curvature `ℛ(X, 0)0` vanishes.
Blueprint: `lem:covariant-commutation-jacobi`. -/
theorem chartCurvature_zero_velocity (g : RiemannianMetric I M) (α : M) (y X : E) :
    chartCurvature (I := I) g α y X 0 0 = 0 :=
  christoffelCurvature_zero_velocity (chartChristoffelBilin (I := I) g α) y X

/-! ### The affine fields are Jacobi fields along a constant curve -/

/-- **Math.** **The chart-level Jacobi system degenerates to `J'' = 0` along a constant curve.**
For a constant chart curve `u ≡ y` the velocity `u̇` vanishes, so both the Christoffel
contraction and the curvature term of the Jacobi pair system vanish, leaving `J' = DJ`,
`DJ' = 0`. The affine pair `(t ↦ t·Z, t ↦ Z)` solves it. -/
theorem isJacobiFieldOn_const_linear (g : RiemannianMetric I M) (α : M) (y Z : E) (a b : ℝ) :
    IsJacobiFieldOn (I := I) g α (fun _ => y) (fun t => t • Z) (fun _ => Z) a b := by
  have hd : ∀ t : ℝ, deriv (fun _ : ℝ => y) t = 0 := fun t => deriv_const t y
  refine ⟨fun t _ => ?_, fun t _ => ?_⟩
  · -- `J' = DJ − Γ(u̇, J)(u) = Z − 0 = Z`
    have hgoal : Z - Geodesic.chartChristoffelContraction (I := I) g α
        (deriv (fun _ : ℝ => y) t) (t • Z) ((fun _ : ℝ => y) t) = Z := by
      rw [hd t, Geodesic.chartChristoffelContraction_zero_left, sub_zero]
    rw [hgoal]
    exact (by simpa using ((hasDerivAt_id t).smul_const Z) :
      HasDerivAt (fun s : ℝ => s • Z) Z t).hasDerivWithinAt
  · -- `DJ' = −ℛ(J, u̇)u̇ − Γ(u̇, DJ)(u) = −0 − 0 = 0`
    have hgoal : -(chartCurvature (I := I) g α ((fun _ : ℝ => y) t) ((fun s : ℝ => s • Z) t)
          (deriv (fun _ : ℝ => y) t) (deriv (fun _ : ℝ => y) t))
        - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv (fun _ : ℝ => y) t) ((fun _ : ℝ => Z) t) ((fun _ : ℝ => y) t) = 0 := by
      rw [hd t, chartCurvature_zero_velocity, Geodesic.chartChristoffelContraction_zero_left,
        neg_zero, sub_zero]
    rw [hgoal]
    exact hasDerivWithinAt_const t (Icc a b) Z

/-- **Math.** **The affine field `(t·Z, Z)` is a Jacobi field along the constant geodesic.**
Manifold form: a single chart — the one at `p` itself — covers the whole (constant) curve, and
in it the reading `chartVectorRep` is the identity (`tangentCoordChange_self`), so the chart-level
statement `isJacobiFieldOn_const_linear` transfers verbatim.
Blueprint: `def:conjugate-point`. -/
theorem isJacobiFieldAlongOn_const_linear (g : RiemannianMetric I M) (p : M) (Z : E)
    {a b : ℝ} (hab : a < b) :
    IsJacobiFieldAlongOn (I := I) g (fun _ => p) (fun t => t • Z) (fun _ => Z) a b := by
  -- in the chart at `p`, the reading of a field along the *constant* curve is the field itself
  have hrep : ∀ J : ℝ → E, chartVectorRep (I := I) (fun _ : ℝ => p) p J = J := by
    intro J
    funext τ
    exact tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) p)
  intro t₀ ht₀
  refine ⟨p, a, b, hab, ht₀, subset_rfl, self_mem_nhdsWithin,
    fun τ _ => mem_chart_source H p, ?_⟩
  rw [hrep, hrep]
  exact isJacobiFieldOn_const_linear g p (extChartAt I p p) Z a b

/-! ### No conjugate point along the constant geodesic -/

/-- **Math.** **The constant geodesic has no conjugate point.** Along `γ ≡ p` every Jacobi field
with `J(0) = 0` is the affine field `J(t) = t·DJ(0)`: the difference of `J` and that affine field
is a Jacobi field vanishing to first order at `0`, hence identically zero by Grönwall uniqueness
(`IsJacobiFieldAlongOn.eqOn_zero`). Such a `J` vanishes again at `t₁ > 0` only if `DJ(0) = 0`,
i.e. only if `J ≡ 0`. So there is no *nontrivial* Jacobi field vanishing at both ends: no
conjugate point, at any positive parameter, under no curvature hypothesis at all.

This is the `v = 0` case that the unit-speed comparison theorems (`lem:conjugate-sturm`) cannot
reach, and that `lem:local-diffeomorphism-bounded-curvature` needs in order to cover the *centre*
of the ball `B(0, π/√K)`.
Blueprint: `def:conjugate-point`, `lem:local-diffeomorphism-bounded-curvature`. -/
theorem not_isConjugatePointAt_const (g : RiemannianMetric I M) (p : M) {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ¬ IsConjugatePointAt (I := I) g (fun _ => p) t₁ := by
  rintro ⟨J, DJ, hJac, ⟨s, hs, hsne⟩, hJ0, hJt₁⟩
  have hgeo : IsGeodesicOn (I := I) g (fun _ : ℝ => p) (Icc 0 t₁) :=
    (isGeodesic_const (I := I) g p).isGeodesicOn (Icc 0 t₁)
  have hγc : ∀ t ∈ Icc (0 : ℝ) t₁, ContinuousAt (fun _ : ℝ => p) t :=
    fun _ _ => continuousAt_const
  -- the affine Jacobi field with the same initial data as `(J, DJ)`
  set Z : E := DJ 0 with hZ
  have hlin : IsJacobiFieldAlongOn (I := I) g (fun _ : ℝ => p)
      (fun t => t • Z) (fun _ => Z) 0 t₁ :=
    isJacobiFieldAlongOn_const_linear g p Z ht₁
  -- their difference vanishes to first order at `0`, hence identically
  have hdiff := hJac.sub ht₁ hgeo hγc hlin
  have hvan := hdiff.eqOn_zero ht₁.le hgeo hγc (by simp [hJ0]) (by simp [hZ])
  -- so `J t = t·Z` on `[0, t₁]`
  have hJeq : ∀ t ∈ Icc (0 : ℝ) t₁, J t = t • Z := fun t ht =>
    sub_eq_zero.mp (hvan t ht).1
  -- `J t₁ = 0` forces `Z = 0`
  have hZ0 : Z = 0 := by
    have h := hJeq t₁ (right_mem_Icc.2 ht₁.le)
    rw [hJt₁] at h
    exact (smul_eq_zero.mp h.symm).resolve_left ht₁.ne'
  -- hence `J ≡ 0`, contradicting the nontriviality of the witness
  exact hsne (by rw [hJeq s hs, hZ0, smul_zero])

section Global

variable (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) [CompleteSpace M]

/-- **Math.** **`γ_0` is the constant curve at `p`.** The constant curve is a geodesic
(`isGeodesic_const`) with initial data `(p, 0)`, so by the intrinsic uniqueness of
`globalGeodesic` it *is* `γ_0`.
Blueprint: `def:exponential-map`. -/
theorem globalGeodesic_zero_vec (p : M) :
    globalGeodesic (I := I) g hg p (0 : TangentSpace I p) = fun _ => p :=
  (globalGeodesic_eq g hg (isGeodesic_const (I := I) g p) continuous_const rfl
    (hasDerivAt_const (0 : ℝ) (extChartAt I p p))).symm

/-- **Math.** `exp_p(0) = p`. Blueprint: `def:exponential-map`. -/
@[simp] theorem expMapGlobal_zero_vec (p : M) :
    expMapGlobal (I := I) g hg p (0 : TangentSpace I p) = p := by
  rw [expMapGlobal_def, globalGeodesic_zero_vec g hg p]

/-- **Math.** **No conjugate point at parameter `1` along `γ_0`** — the zero-vector case of
`not_isConjugatePointAt_one_of_sectionalCurvatureAt_le`, which that theorem excludes by its
hypothesis `v ≠ 0` (it goes through the *unit-speed* Sturm comparison). Here no curvature
hypothesis is needed at all.
Blueprint: `lem:local-diffeomorphism-bounded-curvature`. -/
theorem not_isConjugatePointAt_one_zero_vec (p : M) :
    ¬ IsConjugatePointAt (I := I) g
      (globalGeodesic (I := I) g hg p (0 : TangentSpace I p)) 1 := by
  rw [globalGeodesic_zero_vec g hg p]
  exact not_isConjugatePointAt_const g p one_pos

end Global

end MorganTianLib

end

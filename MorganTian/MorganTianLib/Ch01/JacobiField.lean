import MorganTianLib.Ch01.ChartCurvature
import OpenGALib.Riemannian.Geodesic.LinearODE

/-!
# Poincaré Ch. 1 — Jacobi fields along a chart curve

With the chart-level curvature `chartCurvature` available
(`MorganTianLib.Ch01.ChartCurvature`), the Jacobi equation
`∇_X∇_X J + ℛ(J, X)X = 0` along a coordinate curve `u` becomes a first-order
linear system for the **covariant pair** `(J, ∇J)`:
`J' = ∇J − Γ(u̇, J)(u)` and `(∇J)' = −ℛ(J, u̇)u̇ − Γ(u̇, ∇J)(u)`.
This file provides that layer, in the same interval-relative
`HasDerivWithinAt` style as `MorganTianLib.Ch01.ParallelFrame`:

* `chartCurvatureEndo g α y v : E →L[ℝ] E` — the Jacobi operator
  `Y ↦ ℛ(Y, v)v` at the chart point `y` (continuous-linear in `Y`);
* `IsJacobiFieldOn g α u J DJ a b` — `(J, DJ)` solves the covariant pair
  system on `[a, b]` (one-sided derivatives at the endpoints); at interior
  times `DJ` is the coordinate covariant derivative of `J` and
  `∇DJ = −ℛ(J, u̇)u̇` — the Jacobi equation
  (`covariantDerivCoord_fst` / `covariantDerivCoord_snd`);
* `jacobiPairCoeffCoord` — the pair-system coefficient
  `A(t)(x, w) = (w − Γ(u̇,x)(u), −ℛ(x,u̇)u̇ − Γ(u̇,w)(u))`, and the bridge
  `IsJacobiFieldOn.isSolOn_pair` / `isJacobiFieldOn_of_isSolOn` to
  OpenGALib's first-order theory `Riemannian.LinearODE.IsSolOn`;
* `exists_isJacobiFieldOn_Icc` — **existence** with prescribed initial data
  `(J a, ∇J a) = (J₀, DJ₀)`;
* `IsJacobiFieldOn.eqOn_of_left` / `eqOn_of_right` — **uniqueness** given
  initial (resp. final) data (Grönwall for the pair system); in particular
  `eqOn_zero`: a Jacobi field with vanishing initial data vanishes — so a
  Jacobi field with `∇J(0) = Z ≠ 0` is not identically zero;
* superposition `add` / `const_smul`: Jacobi fields along `u` form a linear
  space, parameterized by the initial covariant pair.

This is the "existence and uniqueness of the Jacobi field `Y_Z`" step of
Morgan–Tian's `lem:exponential-differential-jacobi`, realized on the chart
pair system rather than through a parallel frame (the frame is only needed
later, for the norm comparisons).

Blueprint: `lem:covariant-commutation-jacobi`,
`lem:second-order-linear-ode`, `lem:exponential-differential-jacobi`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.2.
-/

open Set Riemannian
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### The Jacobi operator `Y ↦ ℛ(Y, v)v` -/

/-- **Math.** Additivity of the chart curvature in its first vector slot. -/
theorem chartCurvature_add_left (g : RiemannianMetric I M) (α : M)
    (y v : E) (X X' : E) :
    chartCurvature (I := I) g α y (X + X') v v
      = chartCurvature (I := I) g α y X v v
        + chartCurvature (I := I) g α y X' v v := by
  simp only [chartCurvature_def, christoffelCurvature, map_add,
    ContinuousLinearMap.add_apply]
  abel

/-- **Math.** Homogeneity of the chart curvature in its first vector slot. -/
theorem chartCurvature_smul_left (g : RiemannianMetric I M) (α : M)
    (y v : E) (c : ℝ) (X : E) :
    chartCurvature (I := I) g α y (c • X) v v
      = c • chartCurvature (I := I) g α y X v v := by
  simp only [chartCurvature_def, christoffelCurvature, map_smul,
    ContinuousLinearMap.smul_apply, smul_sub, smul_add]

/-- **Math.** The **Jacobi operator** `Y ↦ ℛ(Y, v)v` at the chart point `y`,
as a continuous linear endomorphism — the operator `R(t)` of the Jacobi
equation `y'' + R(t)y = 0` once evaluated along a geodesic
(`y = u(t)`, `v = u̇(t)`). -/
def chartCurvatureEndo (g : RiemannianMetric I M) (α : M) (y v : E) :
    E →L[ℝ] E :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X => chartCurvature (I := I) g α y X v v
      map_add' := chartCurvature_add_left (I := I) g α y v
      map_smul' := chartCurvature_smul_left (I := I) g α y v }

@[simp] theorem chartCurvatureEndo_apply (g : RiemannianMetric I M) (α : M)
    (y v X : E) :
    chartCurvatureEndo (I := I) g α y v X
      = chartCurvature (I := I) g α y X v v := rfl

/-! ### Jacobi fields along a coordinate curve -/

/-- **Math.** The pair `(J, DJ)` is a **Jacobi field along `u` on `[a, b]`**
(with covariant-derivative field `DJ`): it solves the covariant pair system
`J' = DJ − Γ(u̇, J)(u)`, `DJ' = −ℛ(J, u̇)u̇ − Γ(u̇, DJ)(u)` on `[a, b]`
(one-sided derivatives at the endpoints). The first equation says exactly
`∇J = DJ`, the second `∇DJ = −ℛ(J, u̇)u̇`, i.e. Morgan–Tian's Jacobi
equation `∇_X∇_X J + ℛ(J, X)X = 0`.

Blueprint: `lem:covariant-commutation-jacobi`,
`lem:exponential-differential-jacobi`. -/
structure IsJacobiFieldOn (g : RiemannianMetric I M) (α : M)
    (u J DJ : ℝ → E) (a b : ℝ) : Prop where
  hasDerivWithinAt_fst : ∀ t ∈ Icc a b, HasDerivWithinAt J
    (DJ t - Geodesic.chartChristoffelContraction (I := I) g α
      (deriv u t) (J t) (u t)) (Icc a b) t
  hasDerivWithinAt_snd : ∀ t ∈ Icc a b, HasDerivWithinAt DJ
    (-(chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t))
      - Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) (DJ t) (u t)) (Icc a b) t

namespace IsJacobiFieldOn

variable {g : RiemannianMetric I M} {α : M} {u J DJ Z DZ : ℝ → E} {a b : ℝ}

theorem continuousOn_fst (h : IsJacobiFieldOn (I := I) g α u J DJ a b) :
    ContinuousOn J (Icc a b) :=
  fun t ht => (h.hasDerivWithinAt_fst t ht).continuousWithinAt

theorem continuousOn_snd (h : IsJacobiFieldOn (I := I) g α u J DJ a b) :
    ContinuousOn DJ (Icc a b) :=
  fun t ht => (h.hasDerivWithinAt_snd t ht).continuousWithinAt

/-- **Math.** At interior times, `DJ` is the coordinate covariant derivative
of `J` along `u`: `∇J = DJ`. -/
theorem covariantDerivCoord_fst (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    covariantDerivCoord (I := I) g α u J t = DJ t := by
  have hd := (h.hasDerivWithinAt_fst t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  rw [covariantDerivCoord_def, hd.deriv]
  abel

/-- **Math.** At interior times, the coordinate covariant derivative of `DJ`
is `−ℛ(J, u̇)u̇` — combined with `covariantDerivCoord_fst`, this is the
Jacobi equation `∇∇J + ℛ(J, u̇)u̇ = 0` along `u`. -/
theorem covariantDerivCoord_snd (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    {t : ℝ} (ht : t ∈ Ioo a b) :
    covariantDerivCoord (I := I) g α u DJ t
      = -(chartCurvature (I := I) g α (u t) (J t) (deriv u t) (deriv u t)) := by
  have hd := (h.hasDerivWithinAt_snd t (Ioo_subset_Icc_self ht)).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)
  rw [covariantDerivCoord_def, hd.deriv]
  abel

end IsJacobiFieldOn

/-! ### The covariant pair system -/

/-- **Math.** The coefficient of the first-order covariant pair system for
the Jacobi equation along `u`:
`A(t)(x, w) = (w − Γ(u̇, x)(u), −ℛ(x, u̇)u̇ − Γ(u̇, w)(u))`. -/
def jacobiPairCoeffCoord (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (t : ℝ) : (E × E) →L[ℝ] E × E :=
  ((ContinuousLinearMap.snd ℝ E E)
      - (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)).comp
          (ContinuousLinearMap.fst ℝ E E)).prod
    (-((chartCurvatureEndo (I := I) g α (u t) (deriv u t)).comp
          (ContinuousLinearMap.fst ℝ E E))
      - (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)).comp
          (ContinuousLinearMap.snd ℝ E E))

@[simp] theorem jacobiPairCoeffCoord_apply (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) (t : ℝ) (p : E × E) :
    jacobiPairCoeffCoord (I := I) g α u t p
      = (p.2 - Geodesic.chartChristoffelContraction (I := I) g α
            (deriv u t) (p.1) (u t),
        -(chartCurvature (I := I) g α (u t) (p.1) (deriv u t) (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g α
              (deriv u t) (p.2) (u t)) := rfl

/-- **Math.** The pair curve `t ↦ (J t, DJ t)` of a Jacobi field solves the
first-order linear system `W' = A(t)W`. -/
theorem IsJacobiFieldOn.isSolOn_pair {g : RiemannianMetric I M} {α : M}
    {u J DJ : ℝ → E} {a b : ℝ}
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b) :
    Riemannian.LinearODE.IsSolOn (jacobiPairCoeffCoord (I := I) g α u) a b
      (fun t => (J t, DJ t)) := by
  intro t ht
  have := (h.hasDerivWithinAt_fst t ht).prodMk (h.hasDerivWithinAt_snd t ht)
  simpa using this

/-- **Math.** Conversely, the components of a solution of the pair system
form a Jacobi field. -/
theorem isJacobiFieldOn_of_isSolOn {g : RiemannianMetric I M} {α : M}
    {u : ℝ → E} {a b : ℝ} {W : ℝ → E × E}
    (h : Riemannian.LinearODE.IsSolOn
      (jacobiPairCoeffCoord (I := I) g α u) a b W) :
    IsJacobiFieldOn (I := I) g α u (fun t => (W t).1) (fun t => (W t).2)
      a b where
  hasDerivWithinAt_fst t ht := by
    have := (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t
      (h t ht)
    simpa using this
  hasDerivWithinAt_snd t ht := by
    have := (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivWithinAt t
      (h t ht)
    simpa using this

/-- **Math.** **Existence of Jacobi fields along a coordinate curve** with
prescribed initial position and covariant derivative `(J a, ∇J a) = (J₀, DJ₀)`
— by reduction to the first-order linear pair system and OpenGALib's
`Riemannian.LinearODE.exists_hasDerivWithinAt_Icc`. The continuity and bound
on the pair coefficient hold for any `C¹` curve staying over the interior of
the chart target (the coefficient is built from the `C^∞` maps
`chartChristoffelBilin` and `chartCurvature` there).

Blueprint: `lem:exponential-differential-jacobi` (existence of `Y_Z`). -/
theorem exists_isJacobiFieldOn_Icc (g : RiemannianMetric I M) (α : M)
    (u : ℝ → E) {a b : ℝ} (hab : a ≤ b) {K : ℝ≥0}
    (hcont : ContinuousOn (jacobiPairCoeffCoord (I := I) g α u) (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖jacobiPairCoeffCoord (I := I) g α u t‖₊ ≤ K)
    (J₀ DJ₀ : E) :
    ∃ J DJ : ℝ → E, J a = J₀ ∧ DJ a = DJ₀
      ∧ IsJacobiFieldOn (I := I) g α u J DJ a b := by
  have hA := Riemannian.LinearODE.exists_hasDerivWithinAt_Icc hab
    (jacobiPairCoeffCoord (I := I) g α u) (J₀, DJ₀) hcont hK
  obtain ⟨W, hWa, hW⟩ := hA
  exact ⟨fun t => (W t).1, fun t => (W t).2,
    show (W a).1 = J₀ by rw [hWa],
    show (W a).2 = DJ₀ by rw [hWa],
    isJacobiFieldOn_of_isSolOn hW⟩

namespace IsJacobiFieldOn

variable {g : RiemannianMetric I M} {α : M} {u J DJ Z DZ : ℝ → E} {a b : ℝ}

/-- **Math.** **Forward uniqueness**: two Jacobi fields along `u` with the
same initial position and covariant derivative agree on `[a, b]` (Grönwall
for the pair system). Blueprint: `lem:exponential-differential-jacobi`
(uniqueness of `Y_Z`). -/
theorem eqOn_of_left {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖jacobiPairCoeffCoord (I := I) g α u t‖₊ ≤ K)
    (h₁ : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (h₂ : IsJacobiFieldOn (I := I) g α u Z DZ a b)
    (hJ : J a = Z a) (hDJ : DJ a = DZ a) :
    EqOn J Z (Icc a b) ∧ EqOn DJ DZ (Icc a b) := by
  have h1 := h₁.isSolOn_pair
  have h2 := h₂.isSolOn_pair
  have hpair := Riemannian.LinearODE.IsSolOn.eqOn_of_left hK h1 h2
    (show (J a, DJ a) = (Z a, DZ a) by rw [hJ, hDJ])
  exact ⟨fun t ht => congrArg Prod.fst (hpair ht),
    fun t ht => congrArg Prod.snd (hpair ht)⟩

/-- **Math.** **Backward uniqueness**: two Jacobi fields along `u` with the
same position and covariant derivative at the right endpoint agree on
`[a, b]` (time-reversed Grönwall). -/
theorem eqOn_of_right {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖jacobiPairCoeffCoord (I := I) g α u t‖₊ ≤ K)
    (h₁ : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (h₂ : IsJacobiFieldOn (I := I) g α u Z DZ a b)
    (hJ : J b = Z b) (hDJ : DJ b = DZ b) :
    EqOn J Z (Icc a b) ∧ EqOn DJ DZ (Icc a b) := by
  have h1 := h₁.isSolOn_pair
  have h2 := h₂.isSolOn_pair
  have hpair := Riemannian.LinearODE.IsSolOn.eqOn_of_right hK h1 h2
    (show (J b, DJ b) = (Z b, DZ b) by rw [hJ, hDJ])
  exact ⟨fun t ht => congrArg Prod.fst (hpair ht),
    fun t ht => congrArg Prod.snd (hpair ht)⟩

/-- **Math.** Superposition: the sum of two Jacobi fields along `u` is a
Jacobi field. -/
theorem add (h₁ : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (h₂ : IsJacobiFieldOn (I := I) g α u Z DZ a b) :
    IsJacobiFieldOn (I := I) g α u (J + Z) (DJ + DZ) a b where
  hasDerivWithinAt_fst t ht := by
    have h := (h₁.hasDerivWithinAt_fst t ht).add (h₂.hasDerivWithinAt_fst t ht)
    have heq : (DJ t - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) (J t) (u t))
        + (DZ t - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) (Z t) (u t))
        = (DJ + DZ) t - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) ((J + Z) t) (u t) := by
      simp only [Pi.add_apply]
      rw [show Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
          (J t + Z t) (u t)
        = Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (J t) (u t)
          + Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
              (Z t) (u t) from
        Geodesic.chartChristoffelContraction_add_right (I := I) g α _ _ _ _]
      abel
    rw [← heq]
    exact h
  hasDerivWithinAt_snd t ht := by
    have h := (h₁.hasDerivWithinAt_snd t ht).add (h₂.hasDerivWithinAt_snd t ht)
    have heq : (-(chartCurvature (I := I) g α (u t) (J t) (deriv u t)
            (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (DJ t) (u t))
        + (-(chartCurvature (I := I) g α (u t) (Z t) (deriv u t) (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (DZ t) (u t))
        = -(chartCurvature (I := I) g α (u t) ((J + Z) t) (deriv u t)
            (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            ((DJ + DZ) t) (u t) := by
      simp only [Pi.add_apply]
      rw [chartCurvature_add_left (I := I) g α _ _,
        show Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (DJ t + DZ t) (u t)
          = Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
              (DJ t) (u t)
            + Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
                (DZ t) (u t) from
          Geodesic.chartChristoffelContraction_add_right (I := I) g α _ _ _ _]
      abel
    rw [← heq]
    exact h

/-- **Math.** Superposition: a scalar multiple of a Jacobi field along `u` is
a Jacobi field. -/
theorem const_smul (c : ℝ) (h : IsJacobiFieldOn (I := I) g α u J DJ a b) :
    IsJacobiFieldOn (I := I) g α u (c • J) (c • DJ) a b where
  hasDerivWithinAt_fst t ht := by
    have hd := (h.hasDerivWithinAt_fst t ht).const_smul c
    have heq : c • (DJ t - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) (J t) (u t))
        = (c • DJ) t - Geodesic.chartChristoffelContraction (I := I) g α
            (deriv u t) ((c • J) t) (u t) := by
      simp only [Pi.smul_apply]
      rw [show Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
          (c • J t) (u t)
        = c • Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (J t) (u t) from
        Geodesic.chartChristoffelContraction_smul_right (I := I) g α _ _ _ _,
        smul_sub]
    rw [← heq]
    exact hd
  hasDerivWithinAt_snd t ht := by
    have hd := (h.hasDerivWithinAt_snd t ht).const_smul c
    have heq : c • (-(chartCurvature (I := I) g α (u t) (J t) (deriv u t)
            (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (DJ t) (u t))
        = -(chartCurvature (I := I) g α (u t) ((c • J) t) (deriv u t)
            (deriv u t))
          - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
              ((c • DJ) t) (u t) := by
      simp only [Pi.smul_apply]
      rw [chartCurvature_smul_left (I := I) g α _ _,
        show Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
            (c • DJ t) (u t)
          = c • Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
              (DJ t) (u t) from
          Geodesic.chartChristoffelContraction_smul_right (I := I) g α _ _ _ _,
        smul_sub, smul_neg]
    rw [← heq]
    exact hd

end IsJacobiFieldOn

/-- **Math.** The zero pair is a Jacobi field along any curve. -/
theorem isJacobiFieldOn_zero (g : RiemannianMetric I M) (α : M) (u : ℝ → E)
    (a b : ℝ) :
    IsJacobiFieldOn (I := I) g α u (fun _ => 0) (fun _ => 0) a b where
  hasDerivWithinAt_fst t _ := by
    have h0 : Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
        (0 : E) (u t) = 0 := by
      exact (chartChristoffelContractionRight (I := I) g α (deriv u t)
        (u t)).map_zero
    simpa [h0] using hasDerivWithinAt_const t (Icc a b) (0 : E)
  hasDerivWithinAt_snd t _ := by
    have h0 : Geodesic.chartChristoffelContraction (I := I) g α (deriv u t)
        (0 : E) (u t) = 0 := by
      exact (chartChristoffelContractionRight (I := I) g α (deriv u t)
        (u t)).map_zero
    have hR0 : chartCurvature (I := I) g α (u t) (0 : E) (deriv u t)
        (deriv u t) = 0 := by
      simpa using (chartCurvatureEndo (I := I) g α (u t) (deriv u t)).map_zero
    simpa [h0, hR0] using hasDerivWithinAt_const t (Icc a b) (0 : E)

/-- **Math.** A Jacobi field with vanishing initial position and covariant
derivative vanishes identically; contrapositively, the Jacobi field `Y_Z`
with `∇Y_Z(a) = Z ≠ 0` is not identically zero.
Blueprint: `lem:exponential-differential-jacobi`. -/
theorem IsJacobiFieldOn.eqOn_zero {g : RiemannianMetric I M} {α : M}
    {u J DJ : ℝ → E} {a b : ℝ} {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖jacobiPairCoeffCoord (I := I) g α u t‖₊ ≤ K)
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (hJ0 : J a = 0) (hDJ0 : DJ a = 0) :
    EqOn J 0 (Icc a b) ∧ EqOn DJ 0 (Icc a b) :=
  h.eqOn_of_left hK (isJacobiFieldOn_zero (I := I) g α u a b)
    (by simpa using hJ0) (by simpa using hDJ0)

/-! ### Continuity of the pair coefficient along a `C¹` curve

For a curve `u` that is continuous with continuous derivative on `[a, b]` and
stays over the interior of the chart target, the coefficient of the covariant
pair system is continuous — the Christoffel contraction and the Jacobi
operator are built from the `C^∞` map `chartChristoffelBilin` and its first
derivative. This discharges the abstract hypotheses of
`exists_isJacobiFieldOn_Icc` and the Grönwall bounds. -/

/-- **Math.** The parallel-transport coefficient is the bilinear packaging of
the Christoffel contraction, with the slots reordered. -/
theorem chartChristoffelContractionRight_eq_bilin (g : RiemannianMetric I M)
    (α : M) (v y : E) :
    chartChristoffelContractionRight (I := I) g α v y
      = chartChristoffelBilin (I := I) g α y v := by
  ext w
  rw [chartChristoffelContractionRight_apply, chartChristoffelBilin_apply]

/-- **Math.** Decomposition of the Jacobi operator `Y ↦ ℛ(Y, v)v` into
continuous-linear-map algebra in the point-dependent data
`Γ = chartChristoffelBilin g α y` and its derivative — the form used to read
off continuity along a curve. -/
theorem chartCurvatureEndo_eq (g : RiemannianMetric I M) (α : M) (y v : E) :
    chartCurvatureEndo (I := I) g α y v
      = (ContinuousLinearMap.apply ℝ E v).comp
          ((ContinuousLinearMap.apply ℝ (E →L[ℝ] E) v).comp
            (fderiv ℝ (chartChristoffelBilin (I := I) g α) y))
        - (ContinuousLinearMap.apply ℝ E v).comp
            (fderiv ℝ (chartChristoffelBilin (I := I) g α) y v)
        + (ContinuousLinearMap.apply ℝ E
              (chartChristoffelBilin (I := I) g α y v v)).comp
            (chartChristoffelBilin (I := I) g α y)
        - (chartChristoffelBilin (I := I) g α y v).comp
            ((ContinuousLinearMap.apply ℝ E v).comp
              (chartChristoffelBilin (I := I) g α y)) := by
  ext X
  simp only [chartCurvatureEndo_apply, chartCurvature_def, christoffelCurvature,
    ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply]

section Continuity

variable (g : RiemannianMetric I M) (α : M) {u : ℝ → E} {a b : ℝ}

/-- **Math.** Continuity of the parallel-transport coefficient along a `C¹`
curve over the interior of the chart target. -/
theorem continuousOn_chartChristoffelContractionRight_comp
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) :
    ContinuousOn (fun t => chartChristoffelContractionRight (I := I) g α
      (deriv u t) (u t)) (Icc a b) := by
  have hΓb : ContinuousOn (chartChristoffelBilin (I := I) g α)
      (interior (extChartAt I α).target) :=
    (contDiffOn_chartChristoffelBilin (I := I) g α).continuousOn
  have hcomp : ContinuousOn
      (fun t => chartChristoffelBilin (I := I) g α (u t)) (Icc a b) :=
    hΓb.comp hu hmem
  refine (hcomp.clm_apply hu').congr fun t _ => ?_
  rw [chartChristoffelContractionRight_eq_bilin]

/-- **Math.** Continuity of the Jacobi operator `ℛ(·, u̇)u̇` along a `C¹`
curve over the interior of the chart target. -/
theorem continuousOn_chartCurvatureEndo_comp
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) :
    ContinuousOn (fun t => chartCurvatureEndo (I := I) g α (u t) (deriv u t))
      (Icc a b) := by
  have hΓb_cd := contDiffOn_chartChristoffelBilin (I := I) g α
  have hG : ContinuousOn
      (fun t => chartChristoffelBilin (I := I) g α (u t)) (Icc a b) :=
    hΓb_cd.continuousOn.comp hu hmem
  have hDG : ContinuousOn
      (fun t => fderiv ℝ (chartChristoffelBilin (I := I) g α) (u t))
      (Icc a b) :=
    (hΓb_cd.continuousOn_fderiv_of_isOpen isOpen_interior
      (by norm_num)).comp hu hmem
  have happE : ContinuousOn
      (fun t => ContinuousLinearMap.apply ℝ E (deriv u t)) (Icc a b) :=
    (ContinuousLinearMap.apply ℝ E).continuous.comp_continuousOn hu'
  have happEE : ContinuousOn
      (fun t => ContinuousLinearMap.apply ℝ (E →L[ℝ] E) (deriv u t))
      (Icc a b) :=
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] E)).continuous.comp_continuousOn hu'
  -- the four blocks of `chartCurvatureEndo_eq`
  have h1 := happE.clm_comp (happEE.clm_comp hDG)
  have h2 := happE.clm_comp (hDG.clm_apply hu')
  have h3 : ContinuousOn (fun t => (ContinuousLinearMap.apply ℝ E
      (chartChristoffelBilin (I := I) g α (u t) (deriv u t) (deriv u t))).comp
        (chartChristoffelBilin (I := I) g α (u t))) (Icc a b) :=
    ((ContinuousLinearMap.apply ℝ E).continuous.comp_continuousOn
      ((hG.clm_apply hu').clm_apply hu')).clm_comp hG
  have h4 := (hG.clm_apply hu').clm_comp (happE.clm_comp hG)
  refine (((h1.sub h2).add h3).sub h4).congr fun t _ => ?_
  rw [chartCurvatureEndo_eq]
  simp only [Pi.add_apply]

/-- **Math.** Continuity of the covariant pair coefficient along a `C¹` curve
over the interior of the chart target. -/
theorem continuousOn_jacobiPairCoeffCoord
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) :
    ContinuousOn (jacobiPairCoeffCoord (I := I) g α u) (Icc a b) := by
  have hΓ := continuousOn_chartChristoffelContractionRight_comp (I := I) g α
    hu hu' hmem
  have hR := continuousOn_chartCurvatureEndo_comp (I := I) g α hu hu' hmem
  have h1 : ContinuousOn (fun t => (ContinuousLinearMap.snd ℝ E E)
      - (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)).comp
          (ContinuousLinearMap.fst ℝ E E)) (Icc a b) :=
    continuousOn_const.sub (hΓ.clm_comp continuousOn_const)
  have h2 : ContinuousOn (fun t =>
      -((chartCurvatureEndo (I := I) g α (u t) (deriv u t)).comp
          (ContinuousLinearMap.fst ℝ E E))
      - (chartChristoffelContractionRight (I := I) g α (deriv u t) (u t)).comp
          (ContinuousLinearMap.snd ℝ E E)) (Icc a b) :=
    ((hR.clm_comp continuousOn_const).neg).sub (hΓ.clm_comp continuousOn_const)
  have h12 := h1.prodMk h2
  exact (ContinuousLinearMap.prodₗᵢ (E := E × E) (F := E) (G := E)
    ℝ).continuous.comp_continuousOn h12

/-- **Math.** A Grönwall bound for the pair coefficient on a compact interval,
from continuity. -/
theorem exists_nnnorm_jacobiPairCoeffCoord_le
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target) :
    ∃ K : ℝ≥0, ∀ t ∈ Icc a b,
      ‖jacobiPairCoeffCoord (I := I) g α u t‖₊ ≤ K := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_jacobiPairCoeffCoord (I := I) g α hu hu' hmem)
  refine ⟨⟨max C 0, le_max_right _ _⟩, fun t ht => ?_⟩
  rw [← NNReal.coe_le_coe, coe_nnnorm]
  exact (hC t ht).trans (le_max_left _ _)

/-- **Math.** **Existence of Jacobi fields along a `C¹` chart curve** with
prescribed initial position and covariant derivative — the abstract
continuity/bound hypotheses of `exists_isJacobiFieldOn_Icc` discharged for a
curve staying over the interior of the chart target.

Blueprint: `lem:jacobi-field-coordinates`. -/
theorem exists_isJacobiFieldOn_Icc_of_curve (hab : a ≤ b)
    (hu : ContinuousOn u (Icc a b)) (hu' : ContinuousOn (deriv u) (Icc a b))
    (hmem : ∀ t ∈ Icc a b, u t ∈ interior (extChartAt I α).target)
    (J₀ DJ₀ : E) :
    ∃ J DJ : ℝ → E, J a = J₀ ∧ DJ a = DJ₀
      ∧ IsJacobiFieldOn (I := I) g α u J DJ a b := by
  have hcont := continuousOn_jacobiPairCoeffCoord (I := I) g α hu hu' hmem
  obtain ⟨K, hK⟩ := exists_nnnorm_jacobiPairCoeffCoord_le (I := I) g α
    hu hu' hmem
  exact exists_isJacobiFieldOn_Icc (I := I) g α u hab hcont hK J₀ DJ₀

end Continuity

end MorganTianLib

end

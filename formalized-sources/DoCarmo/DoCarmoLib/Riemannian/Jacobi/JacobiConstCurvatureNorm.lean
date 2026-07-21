import DoCarmoLib.Riemannian.Jacobi.JacobiConstantCurvatureConjugate

/-!
# do Carmo Ch. 8, §2 — the norm of a constant-curvature Jacobi field is manifold-independent

This file provides the **intrinsic norm formula** for a Jacobi field vanishing at the
initial point on a manifold of constant sectional curvature `K₀`, and its immediate
consequence: two such fields on two manifolds of the *same* constant curvature, whose
initial covariant derivatives have matching invariants, have equal norms at every time.

This is the analytic core of the isometry claim in E. Cartan's theorem
(`thm:dc-ch8-2-1`) restricted to the same-curvature case used by
`cor:dc-ch8-2-2`/`cor:dc-ch8-2-3`/`thm:dc-ch8-4-1`: the map
`f = exp_{p̃} ∘ i ∘ exp_p⁻¹` sends a tangent vector `v = J(ℓ)` (the value of the
Jacobi field `J` with `J(0)=0`) to `J̃(ℓ)`, where `J̃` is the Jacobi field with
`J̃(0)=0`, `∇J̃(0)=i(∇J(0))`; and `|J̃(ℓ)| = |J(ℓ)|` because in constant curvature the
norm of such a Jacobi field depends only on `K₀`, the (unit) speed, the time, and the
two scalar invariants `⟨∇J(0),γ'(0)⟩` and `|∇J(0)|²`, all preserved by the linear
isometry `i`.

## Mathematics

Along a unit-speed geodesic `γ` in constant curvature `K₀`, the Jacobi field `J` with
`J(0)=0`, `∇J(0)=Z` decomposes as the sum of a **tangential** field
`J_∥(t)=a t·γ'(t)` (`a=⟨Z,γ'(0)⟩`, do Carmo Remark 2.2's `tγ'` field) and a **normal**
field `J_⊥(t)=h(t)·w(t)`, where `w` is the parallel transport of `Z_⊥=Z-a γ'(0)` and
`h` is the scalar solution of `h''+K₀h=0`, `h(0)=0`, `h'(0)=1`
(`sin(t√K₀)/√K₀`, `t`, `sinh(t√(−K₀))/√(−K₀)`). Because parallel transport is an
isometry and preserves orthogonality, `J_∥(t)⊥J_⊥(t)`, `|γ'(t)|²=1`,
`|w(t)|²=|Z_⊥|²=|Z|²−a²`, so

  `|J(t)|² = t²a² + h(t)²(|Z|²−a²)`,

which involves no manifold-dependent data beyond `K₀` (through `h`).

## Contents

* `isJacobiFieldAlongOn_of_constantCurvature` — the sign-uniform manifold normal
  Jacobi field `h·w` for any scalar solution `h` of `h''+K₀h=0` and any parallel
  normal field `w` (generalizes `isJacobiFieldAlongOn_constCurvatureSol_pos` from the
  specific `K₀>0` `sin` solution to all three curvature signs at once).
* `metricInner_jacobiField_eq_of_constantCurvature` — **the norm formula**
  `|J(t)|² = t²⟨Z,γ'(0)⟩² + h(t)²(|Z|²−⟨Z,γ'(0)⟩²)`.
* `metricInner_jacobiField_transfer_of_constantCurvature` — **the transfer**:
  matching initial invariants across two same-`K₀` manifolds ⟹ equal norms.

Blueprint: `lem:dc-ch8-2-1-jacobi-norm-const`, feeding `cor:dc-ch8-2-2`,
`cor:dc-ch8-2-3`.

Reference: do Carmo, *Riemannian Geometry*, Ch. 8, §2.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### The sign-uniform manifold normal Jacobi field -/

/-- **Math.** **do Carmo Ch. 5, Example 2.3 (manifold form, any sign of `K₀`).**  On a
manifold of constant sectional curvature `K₀`, given a **parallel** field `w` along the
unit-speed geodesic `γ` that is **normal** to `γ'` (`hperp`), and any scalar `h` solving
the Jacobi equation `h''+K₀h=0` (through the derivative facts `hd1 : h' = Dh`,
`hd2 : Dh' = −K₀h`), the field `J(t)=h(t)·w(t)` is a Jacobi field along `γ`, with
covariant derivative `DJ(t)=Dh(t)·w(t)`.

This generalizes `isJacobiFieldAlongOn_constCurvatureSol_pos` (which is the special case
`K₀>0`, `h(t)=sin(t√K₀)/√K₀`): the underlying chart lemma
`isJacobiFieldOn_of_constantCurvature` already accepts an arbitrary scalar solution, so a
single statement covers all three curvature signs. -/
theorem isJacobiFieldAlongOn_of_constantCurvature_of_speedSq (g : RiemannianMetric I M)
    {K₀ c : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {a b : ℝ} (_hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc a b, Geodesic.speedSq (I := I) g γ τ = c)
    (w : ℝ → E) (hwPar : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hperp : ∀ τ ∈ Icc a b,
      g.metricInner (γ τ) (w τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-(K₀ * c) * h t) t) :
    IsJacobiFieldAlongOn (I := I) g γ
      (fun τ => h τ • w τ) (fun τ => Dh τ • w τ) a b := by
  intro t₀ ht₀
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, _⟩ := hwPar t₀ ht₀
  refine ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, ?_⟩
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu_def
  have hwloc := hwPar.isParallelSolOn_of_mem_source hgeo hγc hsub hsrc (β := α)
  have hu_tgt : ∀ t ∈ Icc a' b', u t ∈ (extChartAt I α).target := fun t ht =>
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht)
  have hunit : ∀ t ∈ Icc a' b',
      chartMetricInner (I := I) g α (u t) (deriv u t) (deriv u t) = c := by
    intro t ht
    rw [chartMetricInner_deriv_extChartAt (I := I)
      (hgeo.hasGeodesicEquationAt (hsub ht)) (hγc t (hsub ht)) (hsrc t ht)]
    exact hspeed t (hsub ht)
  have hperp' : ∀ t ∈ Icc a' b',
      chartMetricInner (I := I) g α (u t) (chartVectorRep (I := I) γ α w t) (deriv u t) = 0 := by
    intro t ht
    have hv := chartVectorRep_velocity (I := I) g α
      (hgeo.hasGeodesicEquationAt (hsub ht)) (hγc t (hsub ht)) (hsrc t ht)
    rw [← hv, ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht) w
      (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1)]
    exact hperp t (hsub ht)
  have hcert := isJacobiFieldOn_of_constantCurvature_of_speedSq (I := I) g hK α u
    (chartVectorRep (I := I) γ α w) h Dh
    hu_tgt hunit hperp' hwloc hd1 hd2
  refine hcert.congr ?_ ?_ <;>
    · intro τ hτ
      simp only [chartVectorRep_apply, map_smul]

/-- **Math.** **do Carmo Ch. 5, Example 2.3 (manifold form, any sign of `K₀`)** — the
unit-speed specialization of `isJacobiFieldAlongOn_of_constantCurvature_of_speedSq`. -/
theorem isJacobiFieldAlongOn_of_constantCurvature (g : RiemannianMetric I M) {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc a b, Geodesic.speedSq (I := I) g γ τ = 1)
    (w : ℝ → E) (hwPar : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hperp : ∀ τ ∈ Icc a b,
      g.metricInner (γ τ) (w τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-K₀ * h t) t) :
    IsJacobiFieldAlongOn (I := I) g γ
      (fun τ => h τ • w τ) (fun τ => Dh τ • w τ) a b :=
  isJacobiFieldAlongOn_of_constantCurvature_of_speedSq (I := I) g hK hab hgeo hγc hspeed
    w hwPar hperp h Dh hd1 (by simpa using hd2)

/-! ### The intrinsic norm formula -/

/-- **Eng.** Gram–Schmidt over a Riemannian inner product, at arbitrary speed: the component
of `Z` orthogonal to a vector `V` of squared norm `c ≠ 0` is `Z − (⟨Z,V⟩/c)·V`; it is
orthogonal to `V` and has squared norm `|Z|² − ⟨Z,V⟩²/c`. Stated over `TangentSpace I x` so
the bilinear-form lemmas apply directly; the caller bridges to `E`-typed fields by
definitional equality. -/
private theorem metricInner_gramSchmidt_perp_of_speedSq (g : RiemannianMetric I M) (x : M)
    (Z V : TangentSpace I x) {c : ℝ} (hV : g.metricInner x V V = c) (hc : c ≠ 0) :
    g.metricInner x (Z - (g.metricInner x Z V / c) • V) V = 0
    ∧ g.metricInner x (Z - (g.metricInner x Z V / c) • V) (Z - (g.metricInner x Z V / c) • V)
        = g.metricInner x Z Z - (g.metricInner x Z V) ^ 2 / c := by
  have hZV : g.metricInner x V Z = g.metricInner x Z V := g.metricInner_comm x V Z
  refine ⟨?_, ?_⟩
  · rw [g.metricInner_sub_left, g.metricInner_smul_left, hV, div_mul_cancel₀ _ hc, sub_self]
  · simp only [g.metricInner_sub_left, g.metricInner_sub_right, g.metricInner_smul_left,
      g.metricInner_smul_right, hV, hZV]
    field_simp
    ring

/-- **Eng.** Gram–Schmidt over a Riemannian inner product: the component of `Z`
orthogonal to a **unit** vector `V` is orthogonal to `V` and has squared norm
`|Z|² − ⟨Z,V⟩²`. The `c = 1` case of `metricInner_gramSchmidt_perp_of_speedSq`. -/
private theorem metricInner_gramSchmidt_perp (g : RiemannianMetric I M) (x : M)
    (Z V : TangentSpace I x) (hV : g.metricInner x V V = 1) :
    g.metricInner x (Z - g.metricInner x Z V • V) V = 0
    ∧ g.metricInner x (Z - g.metricInner x Z V • V) (Z - g.metricInner x Z V • V)
        = g.metricInner x Z Z - (g.metricInner x Z V) ^ 2 := by
  have h := metricInner_gramSchmidt_perp_of_speedSq g x Z V hV one_ne_zero
  simpa using h

/-- **Eng.** Squared norm of an orthogonal combination `p·(r·V) + q·W` (with `⟨V,W⟩=0`):
`⟨p(rV)+qW, p(rV)+qW⟩ = (pr)²⟨V,V⟩ + q²⟨W,W⟩`. The nested scalar `p·(r·V)` matches the
tangential Jacobi field `a₀·(t·γ'(t))` exactly. Stated over `TangentSpace I x`. -/
private theorem metricInner_scaledOrthoCombination (g : RiemannianMetric I M) (x : M)
    (V W : TangentSpace I x) (p r q : ℝ) (hVW : g.metricInner x V W = 0) :
    g.metricInner x (p • (r • V) + q • W) (p • (r • V) + q • W)
      = (p * r) ^ 2 * g.metricInner x V V + q ^ 2 * g.metricInner x W W := by
  have hWV : g.metricInner x W V = 0 := by rw [g.metricInner_comm x W V]; exact hVW
  simp only [g.metricInner_add_left, g.metricInner_add_right, g.metricInner_smul_left,
    g.metricInner_smul_right, hVW, hWV]
  ring

/-- **Math.** **The norm of a constant-curvature Jacobi field vanishing at `0`.**  Along a
unit-speed geodesic `γ : [0,ℓ] → M` on a manifold of constant sectional curvature `K₀`,
let `J` be the Jacobi field with `J(0)=0` and covariant derivative `DJ`, and let `h` be
the scalar solution of `h''+K₀h=0` with `h(0)=0`, `h'(0)=1`. Then

  `|J(t)|² = t²·⟨Z,γ'(0)⟩² + h(t)²·(|Z|² − ⟨Z,γ'(0)⟩²)`,   `Z = DJ(0)`,

where `⟨·,·⟩` is the metric at `γ(0)` and `γ'(0)=mfderiv γ 0 1`. The right-hand side
involves **no** manifold-dependent data beyond `K₀` (through `h`), the time `t`, and the
two scalar invariants `⟨Z,γ'(0)⟩` and `|Z|²`; this is the mechanism behind E. Cartan's
theorem in constant curvature (`transfer` corollary below).

Proof: the Jacobi field decomposes (by uniqueness) as `a t·γ'(t) + h(t)·w(t)`, where
`a=⟨Z,γ'(0)⟩`, `w` is the parallel transport of `Z − a γ'(0)` (normal to `γ'`), and the
tangential/normal parts are orthogonal because parallel transport preserves the inner
product; expanding `|J|²` and using `|γ'|²=1`, `⟨γ',w⟩=0`, `|w|²=|Z|²−a²` gives the
claim. -/
theorem metricInner_jacobiField_eq_of_constantCurvature_of_speedSq
    (g : RiemannianMetric I M) {K₀ c : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ τ = c) (hc : c ≠ 0)
    (J DJ : ℝ → E) (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 ℓ) (hJ0 : J 0 = 0)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-(K₀ * c) * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ℓ) :
    g.metricInner (γ t) (J t) (J t)
      = t ^ 2 * (g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ^ 2 / c
        + (h t) ^ 2 * (g.metricInner (γ 0) (DJ 0) (DJ 0)
            - (g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ^ 2 / c) := by
  classical
  -- notation for the initial data
  set v₀ : E := mfderiv 𝓘(ℝ, ℝ) I γ 0 1 with hv₀
  set a₀ : ℝ := g.metricInner (γ 0) (DJ 0) v₀ with ha₀
  -- the velocity field is parallel
  have hvelPar : IsParallelFieldAlongOn (I := I) g γ
      (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) 0 ℓ :=
    isParallelFieldAlongOn_velocity g hℓ hgeo hγc
  -- speed `c` at `0`
  have hvv0 : g.metricInner (γ 0) v₀ v₀ = c := by
    have := hspeed 0 ⟨le_rfl, hℓ.le⟩; rwa [Geodesic.speedSq_def] at this
  -- Gram–Schmidt facts for the normal component `Z − (a₀/c) v₀`
  obtain ⟨hperp0, hnorm0⟩ :=
    metricInner_gramSchmidt_perp_of_speedSq g (γ 0) (DJ 0) v₀ hvv0 hc
  rw [← ha₀] at hperp0 hnorm0
  -- the parallel transport `w` of the normal component
  obtain ⟨w, hwPar, hw0⟩ :=
    exists_parallelFieldAlongOn (I := I) hℓ hgeo hγc (DJ 0 - (a₀ / c) • v₀)
  -- `w` stays normal to `γ'`
  have hperp : ∀ τ ∈ Icc (0 : ℝ) ℓ,
      g.metricInner (γ τ) (w τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0 := by
    intro τ hτ
    rw [IsParallelFieldAlongOn.metricInner_const (I := I) hℓ.le hwPar hvelPar hgeo hγc hτ, hw0]
    exact hperp0
  -- the normal + tangential Jacobi fields and their sum
  have hJperp := isJacobiFieldAlongOn_of_constantCurvature_of_speedSq (I := I) g hK hℓ hgeo hγc
    hspeed w hwPar hperp h Dh hd1 hd2
  have hJpar := (isJacobiFieldAlongOn_smul_velocity (I := I) g hℓ hgeo hγc).smul (a₀ / c)
  have hJsum := hJpar.add hℓ hgeo hγc hJperp
  -- uniqueness identifies `J` with the decomposition `(a₀/c) (t γ'(t)) + h(t) w(t)`
  obtain ⟨hJt, -⟩ := IsJacobiFieldAlongOn.eqOn_of_initial (I := I) hℓ hgeo hγc hJF hJsum
    (by rw [hJ0]; simp only [zero_smul, h0, add_zero]; exact (smul_zero (a₀ / c)).symm)
    (by simp only [Dh0, one_smul, hw0, ← hv₀]; abel) t ht
  -- the pointwise inner products
  have hvvt : g.metricInner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = c := by
    have := hspeed t ht; rwa [Geodesic.speedSq_def] at this
  have hvwt : g.metricInner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (w t : TangentSpace I (γ t)) = 0 := by
    rw [g.metricInner_comm]; exact hperp t ht
  have hwwt : g.metricInner (γ t) (w t : TangentSpace I (γ t)) (w t)
      = g.metricInner (γ 0) (DJ 0) (DJ 0) - a₀ ^ 2 / c := by
    rw [IsParallelFieldAlongOn.metricInner_const (I := I) hℓ.le hwPar hwPar hgeo hγc ht, hw0]
    exact hnorm0
  -- expand `|J t|²` in the orthogonal decomposition `J t = (a₀/c) (t γ'(t)) + h(t) w(t)`
  rw [hJt]
  refine (metricInner_scaledOrthoCombination g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (w t)
    (a₀ / c) t (h t) hvwt).trans ?_
  rw [hvvt, hwwt]
  field_simp

/-- **Math.** **The norm of a constant-curvature Jacobi field vanishing at `0`** — the
unit-speed (`c = 1`) specialization of
`metricInner_jacobiField_eq_of_constantCurvature_of_speedSq`. -/
theorem metricInner_jacobiField_eq_of_constantCurvature (g : RiemannianMetric I M) {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ τ = 1)
    (J DJ : ℝ → E) (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 ℓ) (hJ0 : J 0 = 0)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-K₀ * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ℓ) :
    g.metricInner (γ t) (J t) (J t)
      = t ^ 2 * (g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ^ 2
        + (h t) ^ 2 * (g.metricInner (γ 0) (DJ 0) (DJ 0)
            - (g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1)) ^ 2) := by
  have := metricInner_jacobiField_eq_of_constantCurvature_of_speedSq (I := I) g hK hℓ hgeo hγc
    hspeed one_ne_zero J DJ hJF hJ0 h Dh hd1 (by simpa using hd2) h0 Dh0 ht
  simpa using this

/-! ### No conjugate points before the first zero of the scalar solution -/

/-- **Math.** **Cauchy–Schwarz, in the form the norm formula produces.** If `⟨V,V⟩ = c ≠ 0`
then `⟨Z,Z⟩ − ⟨Z,V⟩²/c ≥ 0`, since that quantity is the squared norm of the component of `Z`
orthogonal to `V`, and the metric is positive semidefinite. This is exactly the sign of the
`h(t)²` coefficient in `metricInner_jacobiField_eq_of_constantCurvature_of_speedSq`. -/
theorem metricInner_sub_sq_div_speedSq_nonneg (g : RiemannianMetric I M) (x : M)
    (Z V : TangentSpace I x) {c : ℝ} (hV : g.metricInner x V V = c) (hc : c ≠ 0) :
    0 ≤ g.metricInner x Z Z - (g.metricInner x Z V) ^ 2 / c := by
  rw [← (metricInner_gramSchmidt_perp_of_speedSq g x Z V hV hc).2]
  exact g.metricInner_self_nonneg x _

/-- **Math.** **In constant curvature, there is no conjugate point where the scalar solution is
nonzero.**  Along a geodesic `γ : [0,ℓ] → M` of squared speed `c ≠ 0` on a manifold of
constant sectional curvature `K₀`, if the scalar solution `h` of `h'' + K₀c·h = 0`,
`h(0)=0`, `h'(0)=1` satisfies `h(ℓ) ≠ 0`, then `γ(ℓ)` is **not** conjugate to `γ(0)`.

(Only this direction is proved here. The converse — that a zero of `h` *is* a conjugate
point — is not; for `K₀ > 0` it is witnessed at the first zero by
`isConjugatePointAt_constCurvature_pos`, which additionally needs `2 ≤ n`.)

The criterion is **sign-uniform**: for `K₀ ≤ 0` the solution `h` is `t` or
`sinh(t√(−K₀c))/√(−K₀c)`, which never vanishes for `t > 0`, recovering the
nonpositive-curvature statement; for `K₀ > 0`, `h(t) = sin(t√(K₀c))/√(K₀c)` first vanishes at
`t = π/√(K₀c)`, so the hypothesis holds throughout `0 < ℓ < π/√(K₀c)` — the interval that
matters, though not the only place `h` is nonzero.

This is what supplies the no-conjugate-point hypothesis of
`isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate` on a **ball** around `p` in positive
constant curvature, where no nonpositive-curvature argument is available — the input
`cor:dc-ch8-2-2` needs in order to reach every `q = exp_p(v)` in a normal neighbourhood.

Proof: the norm formula gives `|J(ℓ)|² = (a²/c)ℓ² + h(ℓ)²(|Z|² − a²/c)` with
`a = ⟨Z,γ'(0)⟩`, `Z = DJ(0)`. Both summands are nonnegative (`c > 0` by positive
definiteness, and `|Z|² − a²/c ≥ 0` by Cauchy–Schwarz), so `J(ℓ) = 0` forces both to vanish:
the first gives `a = 0`, and then the second, with `h(ℓ) ≠ 0`, gives `|Z|² = 0`, i.e.
`DJ(0) = 0`. So `J` has vanishing initial data and is identically zero by Grönwall
uniqueness — contradicting the nontriviality clause of conjugacy. -/
theorem not_isConjugatePointAt_of_constantCurvature_of_speedSq (g : RiemannianMetric I M)
    {K₀ c : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ τ = c) (hc : c ≠ 0)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-(K₀ * c) * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1)
    (hhℓ : h ℓ ≠ 0) :
    ¬ IsConjugatePointAt (I := I) g γ ℓ := by
  classical
  rintro ⟨J, DJ, hJF, ⟨t₁, ht₁, hJt₁⟩, hJ0, hJℓ⟩
  set v₀ : E := mfderiv 𝓘(ℝ, ℝ) I γ 0 1 with hv₀
  set a₀ : ℝ := g.metricInner (γ 0) (DJ 0) v₀ with ha₀
  -- the speed at `0`, and its positivity
  have hvv0 : g.metricInner (γ 0) v₀ v₀ = c := by
    have := hspeed 0 ⟨le_rfl, hℓ.le⟩; rwa [Geodesic.speedSq_def] at this
  have hcnn : 0 ≤ c := by
    rw [← hvv0]; exact g.metricInner_self_nonneg (γ 0) (v₀ : TangentSpace I (γ 0))
  have hcpos : 0 < c := lt_of_le_of_ne hcnn (Ne.symm hc)
  -- the norm formula at `t = ℓ`, where `J` vanishes
  have hform := metricInner_jacobiField_eq_of_constantCurvature_of_speedSq (I := I) g hK hℓ
    hgeo hγc hspeed hc J DJ hJF hJ0 h Dh hd1 hd2 h0 Dh0 (right_mem_Icc.mpr hℓ.le)
  rw [hJℓ] at hform
  have hsum : (0 : ℝ)
      = ℓ ^ 2 * a₀ ^ 2 / c + (h ℓ) ^ 2 * (g.metricInner (γ 0) (DJ 0) (DJ 0) - a₀ ^ 2 / c) :=
    (g.metricInner_zero_left (γ ℓ) (0 : TangentSpace I (γ ℓ))).symm.trans hform
  -- both summands are nonnegative
  have hperp : 0 ≤ g.metricInner (γ 0) (DJ 0) (DJ 0) - a₀ ^ 2 / c :=
    metricInner_sub_sq_div_speedSq_nonneg g (γ 0) (DJ 0) v₀ hvv0 hc
  have hterm1 : 0 ≤ ℓ ^ 2 * a₀ ^ 2 / c := by positivity
  have hterm2 : 0 ≤ (h ℓ) ^ 2 * (g.metricInner (γ 0) (DJ 0) (DJ 0) - a₀ ^ 2 / c) :=
    mul_nonneg (sq_nonneg _) hperp
  -- so each vanishes
  have hz1 : ℓ ^ 2 * a₀ ^ 2 / c = 0 := by linarith
  have hz2 : (h ℓ) ^ 2 * (g.metricInner (γ 0) (DJ 0) (DJ 0) - a₀ ^ 2 / c) = 0 := by linarith
  -- the tangential part forces `a₀ = 0`
  have ha0 : a₀ = 0 := by
    have h1 : ℓ ^ 2 * a₀ ^ 2 = 0 := by
      rcases div_eq_zero_iff.1 hz1 with h' | h'
      · exact h'
      · exact absurd h' hc
    rcases mul_eq_zero.1 h1 with h' | h'
    · exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).1 h') hℓ.ne'
    · exact (pow_eq_zero_iff (n := 2) (by norm_num)).1 h'
  -- and then the normal part, with `h ℓ ≠ 0`, forces `|DJ 0|² = 0`
  have hZZ : g.metricInner (γ 0) (DJ 0) (DJ 0) = 0 := by
    rcases mul_eq_zero.1 hz2 with h' | h'
    · exact absurd ((pow_eq_zero_iff (n := 2) (by norm_num)).1 h') hhℓ
    · rw [ha0] at h'; simpa using h'
  -- positive definiteness: `DJ 0 = 0`
  have hDJ0 : DJ 0 = 0 := by
    by_contra hne
    exact absurd hZZ (g.metricInner_self_pos (γ 0) (DJ 0 : TangentSpace I (γ 0)) hne).ne'
  -- Grönwall uniqueness kills `J`, contradicting the nontriviality clause
  exact hJt₁ (hJF.eqOn_zero hℓ.le hgeo hγc hJ0 hDJ0 t₁ ht₁).1

/-- **Math.** **No conjugate points on the ball `K₀·c·ℓ² < π²`.**  The `h`-free form of
`not_isConjugatePointAt_of_constantCurvature_of_speedSq`: along a geodesic of squared speed
`c ≠ 0` on a manifold of constant sectional curvature `K₀`, if `K₀·c·ℓ² < π²` then `γ(ℓ)` is
not conjugate to `γ(0)`.

The single numerical condition covers all three signs. For `K₀ ≤ 0` it is vacuous, recovering
the classical "no conjugate points in nonpositive curvature". For `K₀ > 0` it reads
`ℓ√(K₀c) < π`; applied along `γ_v` at `ℓ = 1` with `c = |v|²` it becomes `|v| < π/√K₀`, i.e.
**non-conjugacy on the ball of radius `π/√K₀`** — the neighbourhood `V` of `cor:dc-ch8-2-2`.
This is the hypothesis of `isLocalDiffeomorphAt_expMapGlobal_of_not_conjugate`, and the bound
is sharp: `γ(π/√K₀)` really is conjugate to `γ(0)`
(`isConjugatePointAt_constCurvature_pos`, do Carmo `ex:dc-ch5-3-3`).

Blueprint: `lem:dc-ch8-2-1-no-conjugate`. -/
theorem not_isConjugatePointAt_of_constantCurvature_of_lt_pi (g : RiemannianMetric I M)
    {K₀ c : ℝ} (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ τ = c) (hc : c ≠ 0)
    (hlt : K₀ * c * ℓ ^ 2 < Real.pi ^ 2) :
    ¬ IsConjugatePointAt (I := I) g γ ℓ := by
  obtain ⟨h, Dh, hd1, hd2, h0, Dh0, hne⟩ := exists_constCurvatureSol_ne_zero (K₀ * c) hℓ hlt
  exact not_isConjugatePointAt_of_constantCurvature_of_speedSq (I := I) g hK hℓ hgeo hγc
    hspeed hc h Dh hd1 hd2 h0 Dh0 hne

/-! ### The transfer between two spaces of the same constant curvature -/

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
  [I'.Boundaryless] [SigmaCompactSpace M'] [T2Space M']

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` isometry step in constant curvature.**
Let `M` and `M'` both have constant sectional curvature `K₀`, and let `γ`, `γ̃` be
unit-speed geodesics on `[0,ℓ]`. Let `J`, `J̃` be the Jacobi fields with `J(0)=0`,
`J̃(0)=0`. If the two scalar invariants of the initial covariant derivatives match,
`⟨DJ̃(0),γ̃'(0)⟩ = ⟨DJ(0),γ'(0)⟩` and `|DJ̃(0)|² = |DJ(0)|²`, then

  `|J̃(t)|² = |J(t)|²`   for every `t ∈ [0,ℓ]`.

For `f = exp_{p̃} ∘ i ∘ exp_p⁻¹` with `i` a linear isometry and
`DJ̃(0)=i(DJ(0))`, `γ̃'(0)=i(γ'(0))`, both invariants are automatically preserved
(`i` preserves inner products), so `df_q` is norm-preserving — the isometry claim of
E. Cartan's theorem. -/
theorem metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') {K₀ c : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    {γ : ℝ → M} {γ' : ℝ → M'} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ τ = c)
    (hgeo' : IsGeodesicOn (I := I') g' γ' (Icc 0 ℓ))
    (hγc' : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ' t)
    (hspeed' : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I') g' γ' τ = c) (hc : c ≠ 0)
    (J DJ : ℝ → E) (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 ℓ) (hJ0 : J 0 = 0)
    (Jt DJt : ℝ → E) (hJFt : IsJacobiFieldAlongOn (I := I') g' γ' Jt DJt 0 ℓ) (hJt0 : Jt 0 = 0)
    (hmatch_a : g'.metricInner (γ' 0) (DJt 0) (mfderiv 𝓘(ℝ, ℝ) I' γ' 0 1)
      = g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1))
    (hmatch_n : g'.metricInner (γ' 0) (DJt 0) (DJt 0) = g.metricInner (γ 0) (DJ 0) (DJ 0))
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-(K₀ * c) * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ℓ) :
    g'.metricInner (γ' t) (Jt t) (Jt t) = g.metricInner (γ t) (J t) (J t) := by
  rw [metricInner_jacobiField_eq_of_constantCurvature_of_speedSq (I := I') g' hK' hℓ hgeo' hγc'
        hspeed' hc Jt DJt hJFt hJt0 h Dh hd1 hd2 h0 Dh0 ht,
    metricInner_jacobiField_eq_of_constantCurvature_of_speedSq (I := I) g hK hℓ hgeo hγc
        hspeed hc J DJ hJF hJ0 h Dh hd1 hd2 h0 Dh0 ht,
    hmatch_a, hmatch_n]

/-- **Math.** **do Carmo Ch. 8, `thm:dc-ch8-2-1` isometry step in constant curvature** — the
unit-speed (`c = 1`) specialization of
`metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq`. -/
theorem metricInner_jacobiField_transfer_of_constantCurvature
    (g : RiemannianMetric I M) (g' : RiemannianMetric I' M') {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    (hK' : g'.leviCivitaConnection.IsConstantCurvature g' K₀)
    {γ : ℝ → M} {γ' : ℝ → M'} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 ℓ))
    (hγc : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I) g γ τ = 1)
    (hgeo' : IsGeodesicOn (I := I') g' γ' (Icc 0 ℓ))
    (hγc' : ∀ t ∈ Icc (0 : ℝ) ℓ, ContinuousAt γ' t)
    (hspeed' : ∀ τ ∈ Icc (0 : ℝ) ℓ, Geodesic.speedSq (I := I') g' γ' τ = 1)
    (J DJ : ℝ → E) (hJF : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 ℓ) (hJ0 : J 0 = 0)
    (Jt DJt : ℝ → E) (hJFt : IsJacobiFieldAlongOn (I := I') g' γ' Jt DJt 0 ℓ) (hJt0 : Jt 0 = 0)
    (hmatch_a : g'.metricInner (γ' 0) (DJt 0) (mfderiv 𝓘(ℝ, ℝ) I' γ' 0 1)
      = g.metricInner (γ 0) (DJ 0) (mfderiv 𝓘(ℝ, ℝ) I γ 0 1))
    (hmatch_n : g'.metricInner (γ' 0) (DJt 0) (DJt 0) = g.metricInner (γ 0) (DJ 0) (DJ 0))
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-K₀ * h t) t) (h0 : h 0 = 0) (Dh0 : Dh 0 = 1)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) ℓ) :
    g'.metricInner (γ' t) (Jt t) (Jt t) = g.metricInner (γ t) (J t) (J t) :=
  metricInner_jacobiField_transfer_of_constantCurvature_of_speedSq (I := I) (I' := I') g g'
    hK hK' hℓ hgeo hγc hspeed hgeo' hγc' hspeed' one_ne_zero J DJ hJF hJ0 Jt DJt hJFt hJt0
    hmatch_a hmatch_n h Dh hd1 (by simpa using hd2) h0 Dh0 ht

end Riemannian.Jacobi

end

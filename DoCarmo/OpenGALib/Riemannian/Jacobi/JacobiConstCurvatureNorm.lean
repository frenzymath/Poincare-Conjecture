import OpenGALib.Riemannian.Jacobi.JacobiConstantCurvatureConjugate

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
theorem isJacobiFieldAlongOn_of_constantCurvature (g : RiemannianMetric I M) {K₀ : ℝ}
    (hK : g.leviCivitaConnection.IsConstantCurvature g K₀)
    {γ : ℝ → M} {a b : ℝ} (_hab : a < b) (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hspeed : ∀ τ ∈ Icc a b, Geodesic.speedSq (I := I) g γ τ = 1)
    (w : ℝ → E) (hwPar : IsParallelFieldAlongOn (I := I) g γ w a b)
    (hperp : ∀ τ ∈ Icc a b,
      g.metricInner (γ τ) (w τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0)
    (h Dh : ℝ → ℝ) (hd1 : ∀ t, HasDerivAt h (Dh t) t)
    (hd2 : ∀ t, HasDerivAt Dh (-K₀ * h t) t) :
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
      chartMetricInner (I := I) g α (u t) (deriv u t) (deriv u t) = 1 := by
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
  have hcert := isJacobiFieldOn_of_constantCurvature (I := I) g hK α u
    (chartVectorRep (I := I) γ α w) h Dh
    hu_tgt hunit hperp' hwloc hd1 hd2
  refine hcert.congr ?_ ?_ <;>
    · intro τ hτ
      simp only [chartVectorRep_apply, map_smul]

/-! ### The intrinsic norm formula -/

/-- **Eng.** Gram–Schmidt over a Riemannian inner product: the component of `Z`
orthogonal to a **unit** vector `V` is orthogonal to `V` and has squared norm
`|Z|² − ⟨Z,V⟩²`. Stated over `TangentSpace I x` so the bilinear-form lemmas apply
directly; the caller bridges to `E`-typed fields by definitional equality. -/
private theorem metricInner_gramSchmidt_perp (g : RiemannianMetric I M) (x : M)
    (Z V : TangentSpace I x) (hV : g.metricInner x V V = 1) :
    g.metricInner x (Z - g.metricInner x Z V • V) V = 0
    ∧ g.metricInner x (Z - g.metricInner x Z V • V) (Z - g.metricInner x Z V • V)
        = g.metricInner x Z Z - (g.metricInner x Z V) ^ 2 := by
  have hZV : g.metricInner x V Z = g.metricInner x Z V := g.metricInner_comm x V Z
  refine ⟨?_, ?_⟩
  · rw [g.metricInner_sub_left, g.metricInner_smul_left, hV, mul_one, sub_self]
  · simp only [g.metricInner_sub_left, g.metricInner_sub_right, g.metricInner_smul_left,
      g.metricInner_smul_right, hV, hZV]
    ring

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
  classical
  -- notation for the initial data
  set v₀ : E := mfderiv 𝓘(ℝ, ℝ) I γ 0 1 with hv₀
  set a₀ : ℝ := g.metricInner (γ 0) (DJ 0) v₀ with ha₀
  -- the velocity field is parallel
  have hvelPar : IsParallelFieldAlongOn (I := I) g γ
      (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) 0 ℓ :=
    isParallelFieldAlongOn_velocity g hℓ hgeo hγc
  -- unit speed at `0`
  have hvv0 : g.metricInner (γ 0) v₀ v₀ = 1 := by
    have := hspeed 0 ⟨le_rfl, hℓ.le⟩; rwa [Geodesic.speedSq_def] at this
  -- Gram–Schmidt facts for the normal component `Z − a₀ v₀`
  obtain ⟨hperp0, hnorm0⟩ := metricInner_gramSchmidt_perp g (γ 0) (DJ 0) v₀ hvv0
  rw [← ha₀] at hperp0 hnorm0
  -- the parallel transport `w` of the normal component
  obtain ⟨w, hwPar, hw0⟩ := exists_parallelFieldAlongOn (I := I) hℓ hgeo hγc (DJ 0 - a₀ • v₀)
  -- `w` stays normal to `γ'`
  have hperp : ∀ τ ∈ Icc (0 : ℝ) ℓ,
      g.metricInner (γ τ) (w τ : TangentSpace I (γ τ)) (mfderiv 𝓘(ℝ, ℝ) I γ τ 1) = 0 := by
    intro τ hτ
    rw [IsParallelFieldAlongOn.metricInner_const (I := I) hℓ.le hwPar hvelPar hgeo hγc hτ, hw0]
    exact hperp0
  -- the normal + tangential Jacobi fields and their sum
  have hJperp := isJacobiFieldAlongOn_of_constantCurvature (I := I) g hK hℓ hgeo hγc hspeed
    w hwPar hperp h Dh hd1 hd2
  have hJpar := (isJacobiFieldAlongOn_smul_velocity (I := I) g hℓ hgeo hγc).smul a₀
  have hJsum := hJpar.add hℓ hgeo hγc hJperp
  -- uniqueness identifies `J` with the decomposition `a₀ (t γ'(t)) + h(t) w(t)`
  obtain ⟨hJt, -⟩ := IsJacobiFieldAlongOn.eqOn_of_initial (I := I) hℓ hgeo hγc hJF hJsum
    (by rw [hJ0]; simp only [zero_smul, h0, add_zero]; exact (smul_zero a₀).symm)
    (by simp only [Dh0, one_smul, hw0, ← hv₀]; abel) t ht
  -- the pointwise inner products
  have hvvt : g.metricInner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1 := by
    have := hspeed t ht; rwa [Geodesic.speedSq_def] at this
  have hvwt : g.metricInner (γ t)
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (w t : TangentSpace I (γ t)) = 0 := by
    rw [g.metricInner_comm]; exact hperp t ht
  have hwwt : g.metricInner (γ t) (w t : TangentSpace I (γ t)) (w t)
      = g.metricInner (γ 0) (DJ 0) (DJ 0) - a₀ ^ 2 := by
    rw [IsParallelFieldAlongOn.metricInner_const (I := I) hℓ.le hwPar hwPar hgeo hγc ht, hw0]
    exact hnorm0
  -- expand `|J t|²` in the orthogonal decomposition `J t = a₀ (t γ'(t)) + h(t) w(t)`
  rw [hJt]
  exact (metricInner_scaledOrthoCombination g (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (w t)
    a₀ t (h t) hvwt).trans (by rw [hvvt, hwwt]; ring)

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
    g'.metricInner (γ' t) (Jt t) (Jt t) = g.metricInner (γ t) (J t) (J t) := by
  rw [metricInner_jacobiField_eq_of_constantCurvature (I := I') g' hK' hℓ hgeo' hγc' hspeed'
        Jt DJt hJFt hJt0 h Dh hd1 hd2 h0 Dh0 ht,
    metricInner_jacobiField_eq_of_constantCurvature (I := I) g hK hℓ hgeo hγc hspeed
        J DJ hJF hJ0 h Dh hd1 hd2 h0 Dh0 ht,
    hmatch_a, hmatch_n]

end Riemannian.Jacobi

end

import DoCarmoLib.Riemannian.Jacobi.JacobiDimension

/-!
# The velocity Jacobi fields `γ'` and `t γ'`, and the sharp multiplicity bound

do Carmo, *Riemannian Geometry*, Ch. 5, §2 (Remark 2.2) and §3 (Remark 3.2,
Corollary 3.8).

Along a geodesic `γ : [0, L] → M` the two "trivial" Jacobi fields are

* `γ'(t)` itself — a Jacobi field with `J = γ'`, `DJ = 0` (`Dγ'/dt = 0` because
  `γ` is a geodesic, and `ℛ(γ', γ')γ' = 0` by curvature antisymmetry), and
* `t γ'(t)` — a Jacobi field with `J(t) = t γ'(t)`, `DJ(t) = γ'(t)`.

The second vanishes only at `t = 0` and has initial velocity `γ'(0)`; this is the
observation do Carmo uses (Remark 2.2) to deduce that the multiplicity of a
conjugate point never exceeds `n − 1` (Remark 3.2): the endpoint map
`Θ : J'(0) ↦ J(L)` on Jacobi fields with `J(0) = 0` sends `γ'(0)` to `L γ'(L) ≠ 0`
(for a non-constant geodesic), so `γ'(0) ∉ ker Θ`, hence `ker Θ ⊊ E` and the
multiplicity `dim ker Θ ≤ n − 1`.

## Contents

* `chartCurvature_self_fst` — `ℛ(v, v)w = 0` (antisymmetry of the chart curvature
  in its first pair).
* `isJacobiFieldOn_velocity`, `isJacobiFieldOn_smul_velocity` — the chart-level
  Jacobi pairs `(u̇, 0)` and `(t u̇, u̇)` along the chart curve `u = φ_α ∘ γ`.
* `chartVectorRep_velocity` — the chart reading of the own-foot velocity field
  `V(τ) = γ'(τ)` is the chart velocity `u̇ = deriv (φ_α ∘ γ)`.
* `isJacobiFieldAlongOn_velocity`, `isJacobiFieldAlongOn_smul_velocity` — the
  manifold-level velocity Jacobi fields (**Remark 2.2**).
* `conjugateMultiplicity_le_finrank_sub_one` — the sharp bound `≤ n − 1`
  (**Remark 3.2**).
* `finrank_velocityPerp_eq` — the space of Jacobi fields with `J(0) = 0`,
  `⟨J'(0), γ'(0)⟩ = 0` has dimension `n − 1` (**Corollary 3.8**, dimension clause).

Reference: do Carmo, *Riemannian Geometry*, Ch. 5, Remark 2.2, Remark 3.2,
Corollary 3.8.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace Riemannian.Jacobi

open Riemannian.Geodesic Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-! ### Curvature antisymmetry in the first pair -/

/-- **Math.** The chart curvature vanishes when its first two vector slots agree:
`ℛ(v, v)w = 0`. Immediate from the definition
`ℛ(X, Y)Z = (∂_XΓ)(Y,Z) − (∂_YΓ)(X,Z) + Γ(X, Γ(Y,Z)) − Γ(Y, Γ(X,Z))`, whose two
antisymmetric pairs cancel when `X = Y`. -/
theorem chartCurvature_self_fst (g : RiemannianMetric I M) (α : M) (y v w : E) :
    chartCurvature (I := I) g α y v v w = 0 := by
  simp only [chartCurvature_def, christoffelCurvature]
  abel

/-! ### The chart-level velocity Jacobi pairs -/

variable (g : RiemannianMetric I M) (α : M) {γ : ℝ → M} {a b : ℝ}

/-- **Math.** **The geodesic velocity `γ'` as a chart Jacobi pair** (do Carmo
Remark 2.2, first field). Along the chart curve `u = φ_α ∘ γ` of a geodesic, the
pair `(J, DJ) = (u̇, 0)` solves the chart Jacobi system: `∇J = ∇u̇ = 0 = DJ`
(geodesic equation) and `∇DJ = 0 = −ℛ(u̇, u̇)u̇` (curvature antisymmetry). -/
theorem isJacobiFieldOn_velocity
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source) :
    IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (deriv (fun τ => extChartAt I α (γ τ))) (fun _ => 0) a b := by
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu
  constructor
  · intro t ht
    obtain ⟨_hev, a', hd2, heq⟩ :=
      (hgeo.hasGeodesicEquationAt ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)
    have ha' : a' = -Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) (deriv u t) (u t) := eq_neg_of_add_eq_zero_left heq
    have hgoal : (fun _ : ℝ => (0 : E)) t - Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) (deriv u t) (u t) = a' := by rw [ha']; simp
    rw [hgoal]
    exact hd2.hasDerivWithinAt
  · intro t ht
    obtain ⟨_hev, a', hd2, heq⟩ :=
      (hgeo.hasGeodesicEquationAt ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)
    have hgoal : -(chartCurvature (I := I) g α (u t) (deriv u t) (deriv u t) (deriv u t))
        - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) ((fun _ : ℝ => (0 : E)) t)
          (u t) = (0 : E) := by
      rw [chartCurvature_self_fst, chartChristoffelContraction_zero_right]; simp
    rw [hgoal]
    exact hasDerivWithinAt_const _ _ _

/-- **Math.** **The Jacobi field `t γ'` as a chart Jacobi pair** (do Carmo
Remark 2.2, second field). Along the chart curve `u = φ_α ∘ γ` of a geodesic, the
pair `(J, DJ) = (t ↦ t u̇(t), u̇)` solves the chart Jacobi system:
`∇J = u̇ + t∇u̇ = u̇ = DJ` and `∇DJ = ∇u̇ = 0 = −ℛ(t u̇, u̇)u̇`. -/
theorem isJacobiFieldOn_smul_velocity
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hsrc : ∀ t ∈ Icc a b, γ t ∈ (chartAt H α).source) :
    IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (fun t => t • deriv (fun τ => extChartAt I α (γ τ)) t)
      (deriv (fun τ => extChartAt I α (γ τ))) a b := by
  set u : ℝ → E := fun τ => extChartAt I α (γ τ) with hu
  constructor
  · intro t ht
    obtain ⟨_hev, a', hd2, heq⟩ :=
      (hgeo.hasGeodesicEquationAt ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)
    have ha' : a' = -Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) (deriv u t) (u t) := eq_neg_of_add_eq_zero_left heq
    have hgoal : deriv u t - Geodesic.chartChristoffelContraction (I := I) g α
          (deriv u t) (t • deriv u t) (u t)
        = t • a' + (1 : ℝ) • deriv u t := by
      rw [chartChristoffelContraction_smul_right, ha', smul_neg, one_smul]; abel
    rw [hgoal]
    exact ((hasDerivAt_id t).smul hd2).hasDerivWithinAt
  · intro t ht
    obtain ⟨_hev, a', hd2, heq⟩ :=
      (hgeo.hasGeodesicEquationAt ht).solvesGeodesicODEAt (hγc t ht) (hsrc t ht)
    have ha' : a' = -Geodesic.chartChristoffelContraction (I := I) g α
        (deriv u t) (deriv u t) (u t) := eq_neg_of_add_eq_zero_left heq
    have hgoal : -(chartCurvature (I := I) g α (u t) (t • deriv u t) (deriv u t) (deriv u t))
        - Geodesic.chartChristoffelContraction (I := I) g α (deriv u t) (deriv u t) (u t) = a' := by
      rw [chartCurvature_smul_fst, chartCurvature_self_fst, smul_zero, neg_zero, zero_sub, ha']
    rw [hgoal]
    exact hd2.hasDerivWithinAt

/-! ### The own-foot velocity field and its chart reading -/

/-- **Math.** The chart-`α` reading of the own-foot velocity field
`V(τ) = γ'(τ) = mfderiv γ τ 1` is the chart velocity `u̇ = deriv (φ_α ∘ γ)`, at any
time whose foot lies in the chart source. This is the first-order chart-change
transfer (`HasGeodesicEquationAt.deriv_extChartAt_eq`) read through
`mfderiv_apply_one`. -/
theorem chartVectorRep_velocity {σ : ℝ}
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    (hsrc : γ σ ∈ (chartAt H α).source) :
    chartVectorRep (I := I) γ α (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) σ
      = deriv (fun τ => extChartAt I α (γ τ)) σ := by
  rw [chartVectorRep_apply, h.mfderiv_apply_one hcont, ← h.deriv_extChartAt_eq hcont hsrc]

/-- **Math.** The chart-`α` reading of the scaled velocity field `t ↦ t γ'(t)`. -/
theorem chartVectorRep_smul_velocity {σ : ℝ}
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ σ) (hcont : ContinuousAt γ σ)
    (hsrc : γ σ ∈ (chartAt H α).source) :
    chartVectorRep (I := I) γ α (fun τ => τ • mfderiv 𝓘(ℝ, ℝ) I γ τ 1) σ
      = σ • deriv (fun τ => extChartAt I α (γ τ)) σ := by
  have hv := chartVectorRep_velocity g α h hcont hsrc
  rw [chartVectorRep_apply] at hv ⊢
  rw [← hv]
  exact map_smul (tangentCoordChange I (γ σ) α (γ σ)) σ (mfderiv 𝓘(ℝ, ℝ) I γ σ 1)

/-! ### The manifold-level velocity Jacobi fields (Remark 2.2) -/

section Manifold

variable (hab : a < b)
  (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
  (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)

include hab hgeo hγc

/-- **Math.** **A local chart interval.** Around any `t₀ ∈ [a, b]` there is a
nondegenerate subinterval `[a', b'] ⊆ [a, b]`, a neighbourhood of `t₀` within
`[a, b]`, all of whose `γ`-feet lie in the chart at `γ t₀`. -/
theorem exists_chart_subinterval (t₀ : ℝ) (ht₀ : t₀ ∈ Icc a b) :
    ∃ a' b' : ℝ, a' < b' ∧ t₀ ∈ Icc a' b' ∧ Icc a' b' ⊆ Icc a b ∧
      Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
      ∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H (γ t₀)).source := by
  have hnhd : γ ⁻¹' (chartAt H (γ t₀)).source ∈ 𝓝 t₀ :=
    (hγc t₀ ht₀).preimage_mem_nhds
      ((chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhd
  refine ⟨max a (t₀ - ε / 2), min b (t₀ + ε / 2),
    max_lt (lt_min hab (by linarith [ht₀.1])) (lt_min (by linarith [ht₀.2]) (by linarith)),
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩,
    Icc_subset_Icc (le_max_left _ _) (min_le_left _ _), ?_, ?_⟩
  · refine mem_nhdsWithin.2 ⟨Ioo (t₀ - ε / 2) (t₀ + ε / 2), isOpen_Ioo,
      ⟨by linarith, by linarith⟩, fun σ hσ => ?_⟩
    exact ⟨max_le hσ.2.1 hσ.1.1.le, le_min hσ.2.2 hσ.1.2.le⟩
  · intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t₀ - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t₀ + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    rw [abs_lt]; constructor <;> linarith

/-- **Math.** **do Carmo Ch. 5, Remark 2.2 (second field): `t γ'` is a Jacobi
field.** The manifold field `J(t) = t γ'(t)` (with covariant derivative
`DJ(t) = γ'(t)`) is a Jacobi field along `γ`. -/
theorem isJacobiFieldAlongOn_smul_velocity :
    IsJacobiFieldAlongOn (I := I) g γ
      (fun τ => τ • mfderiv 𝓘(ℝ, ℝ) I γ τ 1)
      (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) a b := by
  intro t₀ ht₀
  obtain ⟨a', b', hab', ht₀', hsub, hnbhd, hsrc⟩ :=
    exists_chart_subinterval g hab hgeo hγc t₀ ht₀
  refine ⟨γ t₀, a', b', hab', ht₀', hsub, hnbhd, hsrc, ?_⟩
  refine (isJacobiFieldOn_smul_velocity g (γ t₀)
    (fun τ hτ => hgeo τ (hsub hτ)) (fun τ hτ => hγc τ (hsub hτ)) hsrc).congr ?_ ?_
  · intro τ hτ
    exact chartVectorRep_smul_velocity g (γ t₀)
      (hgeo.hasGeodesicEquationAt (hsub hτ)) (hγc τ (hsub hτ)) (hsrc τ hτ)
  · intro τ hτ
    exact chartVectorRep_velocity g (γ t₀)
      (hgeo.hasGeodesicEquationAt (hsub hτ)) (hγc τ (hsub hτ)) (hsrc τ hτ)

/-- **Math.** **do Carmo Ch. 5, Remark 2.2 (first field): `γ'` is a Jacobi
field.** The manifold field `J(t) = γ'(t)` (with covariant derivative
`DJ(t) = 0`, since `γ` is a geodesic) is a Jacobi field along `γ`. -/
theorem isJacobiFieldAlongOn_velocity :
    IsJacobiFieldAlongOn (I := I) g γ
      (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) (fun _ => 0) a b := by
  intro t₀ ht₀
  obtain ⟨a', b', hab', ht₀', hsub, hnbhd, hsrc⟩ :=
    exists_chart_subinterval g hab hgeo hγc t₀ ht₀
  refine ⟨γ t₀, a', b', hab', ht₀', hsub, hnbhd, hsrc, ?_⟩
  refine (isJacobiFieldOn_velocity g (γ t₀)
    (fun τ hτ => hgeo τ (hsub hτ)) (fun τ hτ => hγc τ (hsub hτ)) hsrc).congr ?_ ?_
  · intro τ hτ
    exact chartVectorRep_velocity g (γ t₀)
      (hgeo.hasGeodesicEquationAt (hsub hτ)) (hγc τ (hsub hτ)) (hsrc τ hτ)
  · intro τ hτ
    simp [chartVectorRep_apply]

end Manifold

/-! ### The sharp multiplicity bound (Remark 3.2) -/

/-- **Math.** **do Carmo Ch. 5, Remark 3.2 (sharp bound).** For a *non-constant*
geodesic `γ : [0, L] → M` (`γ'(L) ≠ 0`), the multiplicity of the conjugate point
`γ(L)` never exceeds `n − 1`.

The endpoint map `Θ : J'(0) ↦ J(L)` on Jacobi fields with `J(0) = 0` sends the
initial velocity `γ'(0)` to `Θ(γ'(0)) = J_{tγ'}(L) = L γ'(L) ≠ 0`, where
`J_{tγ'}(t) = t γ'(t)` is the Jacobi field of `isJacobiFieldAlongOn_smul_velocity`.
Hence `γ'(0) ∉ ker Θ`, so `ker Θ ⊊ E` and the multiplicity `dim ker Θ ≤ n − 1`. -/
theorem conjugateMultiplicity_le_finrank_sub_one
    {L : ℝ} (hab : (0 : ℝ) < L)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 L))
    (hγc : ∀ t ∈ Icc (0 : ℝ) L, ContinuousAt γ t)
    (hVL : mfderiv 𝓘(ℝ, ℝ) I γ L 1 ≠ 0) :
    conjugateMultiplicity hab hgeo hγc ≤ Module.finrank ℝ E - 1 := by
  have hJF := isJacobiFieldAlongOn_smul_velocity g hab hgeo hγc
  set v₀ : E := mfderiv 𝓘(ℝ, ℝ) I γ 0 1 with hv₀
  set vL : E := mfderiv 𝓘(ℝ, ℝ) I γ L 1 with hvL
  have hJ0 : (fun τ => τ • mfderiv 𝓘(ℝ, ℝ) I γ τ 1) 0 = (0 : E) := by
    show (0 : ℝ) • v₀ = 0; rw [zero_smul]
  have hDJ0 : (fun τ => mfderiv 𝓘(ℝ, ℝ) I γ τ 1) 0 = v₀ := hv₀.symm
  -- `Θ(γ'(0)) = L γ'(L)`
  have hkey : jacobiEndpointOfVel hab hgeo hγc v₀ = L • vL := by
    rw [jacobiEndpointOfVel_apply]
    have heq := eqOn_jacobiJ hab hgeo hγc (0, v₀) hJF hJ0 hDJ0
    have hL := (heq L (right_mem_Icc.2 hab.le)).1
    -- `(fun τ => τ • γ'(τ)) L = L • γ'(L)`
    simpa using hL.symm
  have hne : jacobiEndpointOfVel hab hgeo hγc v₀ ≠ 0 := by
    rw [hkey]; exact smul_ne_zero hab.ne' hVL
  have hnotmem : v₀ ∉ LinearMap.ker (jacobiEndpointOfVel hab hgeo hγc) :=
    fun h => hne (LinearMap.mem_ker.1 h)
  have hlt : LinearMap.ker (jacobiEndpointOfVel hab hgeo hγc) < ⊤ := by
    refine lt_of_le_of_ne le_top (fun h => hnotmem ?_)
    rw [h]; exact Submodule.mem_top
  have hfr : Module.finrank ℝ (LinearMap.ker (jacobiEndpointOfVel hab hgeo hγc))
      < Module.finrank ℝ E := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    rwa [finrank_top] at this
  exact Nat.le_sub_one_of_lt hfr

/-! ### Dimension of the normal Jacobi fields (Corollary 3.8, dimension clause) -/

/-- **Math.** The tangential-pairing functional at the base point `x`:
`w ↦ ⟨w, v₀⟩_g`. Under the parametrization of Jacobi fields with `J(0) = 0` by their
initial velocity `w = J'(0)`, this is `w ↦ ⟨J'(0), γ'(0)⟩` (with `x = γ(0)`,
`v₀ = γ'(0)`); its kernel is do Carmo's space `𝒥^⊥` of Jacobi fields with `J(0) = 0`
and `⟨J, γ'⟩ ≡ 0` (\cref{cor:dc-ch5-3-8}). -/
def velocityFunctional (g : RiemannianMetric I M) (x : M) (v₀ : E) : Module.Dual ℝ E where
  toFun w := g.metricInner x w v₀
  map_add' w₁ w₂ := g.metricInner_add_left x w₁ w₂ v₀
  map_smul' c w := by
    change g.metricInner x (c • w) v₀ = c • g.metricInner x w v₀
    rw [smul_eq_mul]
    exact g.metricInner_smul_left x c w v₀

@[simp] theorem velocityFunctional_apply (g : RiemannianMetric I M) (x : M) (v₀ w : E) :
    velocityFunctional (I := I) g x v₀ w = g.metricInner x w v₀ := rfl

/-- **Math.** **do Carmo Ch. 5, Corollary 3.8 (dimension clause).** For `v₀ ≠ 0`
(a non-constant geodesic, `v₀ = γ'(0)`), the space of initial velocities `w` with
`⟨w, v₀⟩_g = 0` has dimension `n − 1`. Via the linear parametrization of Jacobi
fields with `J(0) = 0` by `w = J'(0)` and the equivalence `⟨J, γ'⟩ ≡ 0 ⟺
⟨J'(0), γ'(0)⟩ = 0` (\cref{cor:dc-ch5-3-8}, the `chartMetricInner_jacobi_velocity_eq_zero_iff`
clause), this is do Carmo's assertion that the space `𝒥^⊥` of Jacobi fields with
`J(0) = 0`, `J'(0) ⟂ γ'(0)` has dimension `n − 1`.

The functional `⟨·, v₀⟩_g` is a nonzero element of the dual (it is positive on
`v₀`), so its kernel is a hyperplane. -/
theorem finrank_velocityPerp_eq (g : RiemannianMetric I M) {x : M} {v₀ : E}
    (hv₀ : v₀ ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (velocityFunctional (I := I) g x v₀))
      = Module.finrank ℝ E - 1 := by
  have hφ : velocityFunctional (I := I) g x v₀ ≠ 0 := by
    intro h
    have h0 : velocityFunctional (I := I) g x v₀ v₀ = 0 := by rw [h]; rfl
    rw [velocityFunctional_apply] at h0
    exact absurd h0 (g.metricInner_self_pos x v₀ hv₀).ne'
  have hrank := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
  omega

end Riemannian.Jacobi

end

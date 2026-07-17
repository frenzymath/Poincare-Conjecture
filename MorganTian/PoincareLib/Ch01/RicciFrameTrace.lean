import PoincareLib.Ch01.FrameRadialBridge
import PoincareLib.Ch01.GaussLemma

/-!
# Poincaré Ch. 1, §1.6 — the manifold→frame bridge for the Ricci hypothesis

`FrameRadialBridge` transports a *sectional* curvature bound `−k ≤ K(P)` into the
algebraic hypothesis `−k‖x‖² ≤ ⟪ℛ x, x⟫` consumed by the (vector) Riccati
comparison.  Morgan–Tian's **Ricci** comparison (`thm:ricci-curvature-comparison`,
`lem:volume-element-comparison`) needs the *traced* version of the same
dictionary, and this file supplies it.

The frame Jacobi operator `ℛ(t) = frameCurvOp g γ e t` on the coefficient space
`𝔼 = EuclideanSpace ℝ (Fin n)` has matrix `−frameCurvᵢⱼ(t) = −ℛ(Eⱼ, γ', γ', Eᵢ)`
in the standard basis.  Its **trace** is therefore

`Tr ℛ(t) = −∑ᵢ ℛ(Eᵢ, γ', γ', Eᵢ) = ∑ᵢ ℛ(γ', Eᵢ, γ', Eᵢ) = Ric(γ'(t), γ'(t))`,

the two rewritings being the pair symmetry `R_{ijkl} = R_{klij}` and the
antisymmetry in the last pair, and the last step the orthonormal-basis formula for
the Ricci trace (`Riemannian.ricciForm_eq_sum`) applied to the orthonormal basis
`{Eᵢ(t)}` of `T_{γ t}M` that the parallel frame supplies.

Main results:

* `trace_frameCurvOp_eq_ricciAt` — **`Tr ℛ(t) = Ric(γ'(t), γ'(t))`**, the
  headline: the geometric hypothesis `Ric ≥ −(n−1)k` becomes the algebraic
  hypothesis `Tr ℛ ≥ −(n−1)k` of the trace-Riccati comparison
  (`le_trace_frameCurvOp_of_ricci_ge`);
* `frameCurvOp_radial_eq_zero` — **the radial direction is in the kernel of `ℛ`**:
  if the frame vector `Eᵢ₀(t)` is the velocity `γ'(t)`, then the `i₀`-th column of
  `ℛ(t)` vanishes, by antisymmetry of the curvature form in its *first* pair
  (`ℛ(γ', γ', γ', ·) = 0`).  This is why the Jacobi operator only sees the
  `(n−1)`-dimensional normal bundle;
* `isParallelAlongOn_mfderivVelocity` — **the velocity of a geodesic is parallel
  along it** (that *is* the geodesic equation `∇_{γ'}γ' = 0`, read in a chart);
* `exists_orthonormalParallelFrameAlong_velocity` — a parallel `g`-orthonormal
  frame along a unit-speed geodesic whose **`0`-th vector is the velocity**:
  extend the orthonormal singleton `{γ'(a)}` to an orthonormal basis of
  `T_{γ a}M` and parallel-transport it; the transported `0`-th field and `γ'`
  are two parallel fields with the same initial value, hence agree (parallel
  transport is a `g`-isometry, so their difference has constant — zero — length).

Blueprint: `thm:ricci-curvature-comparison`, `lem:volume-element-comparison`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.6.
-/

open Set Filter Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M] [I.Boundaryless]

/-- The coefficient space of the parallel frame (see `FrameRadialBridge`). -/
local notation "𝔼" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The standard orthonormal basis of the coefficient space. -/
local notation "𝔟" => EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ

/-! ### The frame at a fixed time, packaged as an orthonormal basis -/

/-- **Math.** A `g`-orthonormal frame at `γ t` — `n = dim M` vectors with
`⟨Eᵢ, Eⱼ⟩_g = δᵢⱼ` — *is* an orthonormal basis of the inner-product space
`(T_{γ t}M, g)`.  (An orthonormal family of `dim M` vectors is automatically a
basis; this is the packaging `Riemannian.ricciForm_eq_sum` asks for.)

Blueprint: `thm:ricci-curvature-comparison`. -/
def frameOrthonormalBasis (g : RiemannianMetric I M) {q : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (horth : ∀ i j, g.metricInner q (e i) (e j) = if i = j then 1 else 0) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I q) :=
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI hOrth : Orthonormal ℝ e := metricInner_orthonormal_family (I := I) g horth
  (basisOfOrthonormalOfCardEqFinrank hOrth
      (by exact Fintype.card_fin _ : Fintype.card (Fin (Module.finrank ℝ E))
        = Module.finrank ℝ (TangentSpace I q))).toOrthonormalBasis (by
    rw [coe_basisOfOrthonormalOfCardEqFinrank]; exact hOrth)

/-- **Math.** The `i`-th vector of `frameOrthonormalBasis` is `Eᵢ`. -/
theorem frameOrthonormalBasis_apply (g : RiemannianMetric I M) {q : M}
    {e : Fin (Module.finrank ℝ E) → TangentSpace I q}
    (horth : ∀ i j, g.metricInner q (e i) (e j) = if i = j then 1 else 0)
    (i : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    frameOrthonormalBasis (I := I) g horth i = e i := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hOrth : Orthonormal ℝ e := metricInner_orthonormal_family (I := I) g horth
  show (basisOfOrthonormalOfCardEqFinrank hOrth _).toOrthonormalBasis _ i = e i
  rw [Module.Basis.coe_toOrthonormalBasis]
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank hOrth _) i

/-! ### The trace of the frame Jacobi operator is the Ricci curvature -/

/-- **Math.** The diagonal entries of the frame Jacobi operator:
`⟪ℛ(t) bᵢ, bᵢ⟫ = −ℛᵢᵢ(t)`, by orthonormality of the standard basis of the
coefficient space. -/
theorem inner_frameCurvOp_basisFun_self (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) (i : Fin (Module.finrank ℝ E)) :
    ⟪frameCurvOp (I := I) g γ e t (𝔟 i : 𝔼), (𝔟 i : 𝔼)⟫
      = -(frameCurv (I := I) g γ e i i t) := by
  classical
  rw [inner_frameCurvOp_apply]
  simp only [basisFun_inner (E := E), mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- **Math.** **The trace of the frame Jacobi operator is the Ricci curvature of
the velocity** — the manifold→frame bridge for Morgan–Tian's Ricci hypothesis:

`Tr ℛ(t) = Ric(γ'(t), γ'(t))`.

The matrix of `ℛ(t) = frameCurvOp g γ e t` in the standard basis of the
coefficient space is `−frameCurvᵢⱼ = −ℛ(Eⱼ, γ', γ', Eᵢ)`, so
`Tr ℛ(t) = −∑ᵢ ℛ(Eᵢ, γ', γ', Eᵢ)`.  The pair-swap symmetry `R_{ijkl} = R_{klij}`
turns `ℛ(Eᵢ, γ', γ', Eᵢ)` into `ℛ(γ', Eᵢ, Eᵢ, γ')`, and antisymmetry in the last
pair turns that into `−ℛ(γ', Eᵢ, γ', Eᵢ)`; hence
`Tr ℛ(t) = ∑ᵢ ℛ(γ', Eᵢ, γ', Eᵢ)`, which is exactly the orthonormal-basis formula
(`Riemannian.ricciForm_eq_sum`) for `Ric(γ', γ')` in the basis `{Eᵢ(t)}` of
`T_{γ t}M` supplied by the `g`-orthonormal frame.

This is the identity that converts the geometric hypothesis `Ric ≥ −(n−1)k` into
the algebraic hypothesis `Tr ℛ ≥ −(n−1)k` of the trace-Riccati comparison.

Blueprint: `thm:ricci-curvature-comparison`, `lem:volume-element-comparison`. -/
theorem trace_frameCurvOp_eq_ricciAt {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t : ℝ}
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0) :
    LinearMap.trace ℝ 𝔼 ↑(frameCurvOp (I := I) g γ e t)
      = ricciAt g g.leviCivitaConnection hLC (γ t)
          (mfderivVelocity (I := I) (E := E) γ t)
          (mfderivVelocity (I := I) (E := E) γ t) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set v : TangentSpace I (γ t) := mfderivVelocity (I := I) (E := E) γ t with hv
  have hB : IsAlgCurvatureForm (curvatureFormAt g g.leviCivitaConnection (γ t)) :=
    isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC (γ t)
  -- the trace, computed in the standard basis of the coefficient space
  have htr : LinearMap.trace ℝ 𝔼 ↑(frameCurvOp (I := I) g γ e t)
      = ∑ i, -(frameCurv (I := I) g γ e i i t) := by
    rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin (Module.finrank ℝ E)) ℝ)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (real_inner_comm (frameCurvOp (I := I) g γ e t (𝔟 i : 𝔼)) (𝔟 i : 𝔼)).trans
      (inner_frameCurvOp_basisFun_self (I := I) g γ e t i)
  -- each diagonal entry is a Ricci summand: `−ℛ(Eᵢ, γ', γ', Eᵢ) = ℛ(γ', Eᵢ, γ', Eᵢ)`
  have hdiag : ∀ i, -(frameCurv (I := I) g γ e i i t)
      = curvatureFormAt g g.leviCivitaConnection (γ t) v (e i t) v (e i t) := by
    intro i
    have h1 : curvatureFormAt g g.leviCivitaConnection (γ t) (e i t) v v (e i t)
        = curvatureFormAt g g.leviCivitaConnection (γ t) v (e i t) (e i t) v :=
      hB.pairSwap (e i t) v v (e i t)
    have h2 : curvatureFormAt g g.leviCivitaConnection (γ t) v (e i t) (e i t) v
        = - curvatureFormAt g g.leviCivitaConnection (γ t) v (e i t) v (e i t) :=
      hB.antisymm₃₄ v (e i t) (e i t) v
    show -(curvatureFormAt g g.leviCivitaConnection (γ t) (e i t) v v (e i t)) = _
    rw [h1, h2, neg_neg]
  -- the Ricci trace, in the orthonormal basis supplied by the frame
  have hric : ricciAt g g.leviCivitaConnection hLC (γ t) v v
      = ∑ i, curvatureFormAt g g.leviCivitaConnection (γ t) v (e i t) v (e i t) := by
    have h := ricciForm_eq_sum hB v v
      (frameOrthonormalBasis (I := I) g (q := γ t) (e := fun i => (e i t : TangentSpace I (γ t)))
        horth)
    refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
    rw [frameOrthonormalBasis_apply (I := I) g horth i]
  rw [htr, hric]
  exact Finset.sum_congr rfl fun i _ => hdiag i

/-- **Math.** **Morgan–Tian's Ricci hypothesis, converted.**  If
`Ric(γ'(t), γ'(t)) ≥ −(n−1)k` then the frame Jacobi operator satisfies
`Tr ℛ(t) ≥ −(n−1)k` — the hypothesis consumed by the trace-Riccati comparison
(and hence by the volume-element comparison).  Immediate from
`trace_frameCurvOp_eq_ricciAt`.

Blueprint: `thm:ricci-curvature-comparison`, `lem:volume-element-comparison`. -/
theorem le_trace_frameCurvOp_of_ricci_ge {g : RiemannianMetric I M} {γ : ℝ → M}
    {e : Fin (Module.finrank ℝ E) → ℝ → E} {t k : ℝ}
    (hLC : (g.leviCivitaConnection).IsLeviCivita g)
    (horth : ∀ i j, g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
      = if i = j then 1 else 0)
    (hric : -(((Module.finrank ℝ E : ℝ) - 1) * k)
      ≤ ricciAt g g.leviCivitaConnection hLC (γ t)
          (mfderivVelocity (I := I) (E := E) γ t)
          (mfderivVelocity (I := I) (E := E) γ t)) :
    -(((Module.finrank ℝ E : ℝ) - 1) * k)
      ≤ LinearMap.trace ℝ 𝔼 ↑(frameCurvOp (I := I) g γ e t) := by
  rw [trace_frameCurvOp_eq_ricciAt (I := I) hLC horth]
  exact hric

/-! ### The radial direction is in the kernel of the frame Jacobi operator -/

/-- **Math.** **The radial direction is in the kernel of the Jacobi operator.**
If the frame's `i₀`-th vector at time `t` *is* the velocity, `Eᵢ₀(t) = γ'(t)`,
then the `i₀`-th column of `ℛ(t) = frameCurvOp g γ e t` vanishes:

`ℛ(t) bᵢ₀ = 0`.

Indeed the `(i, i₀)` entry is `−ℛ(Eᵢ₀, γ', γ', Eᵢ) = −ℛ(γ', γ', γ', Eᵢ) = 0` by
antisymmetry of the curvature form in its **first** pair.  Geometrically:
`R(γ', γ')γ' = 0`, so the Jacobi operator only acts on the `(n−1)`-dimensional
normal bundle — which is why the model comparison has `n−1` in it.

Blueprint: `thm:ricci-curvature-comparison`, `lem:volume-element-comparison`. -/
theorem frameCurvOp_radial_eq_zero (g : RiemannianMetric I M) (γ : ℝ → M)
    (e : Fin (Module.finrank ℝ E) → ℝ → E) (t : ℝ) {i₀ : Fin (Module.finrank ℝ E)}
    (hrad : (e i₀ t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t) :
    frameCurvOp (I := I) g γ e t (𝔟 i₀ : 𝔼) = 0 := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hLC : (g.leviCivitaConnection).IsLeviCivita g :=
    (g.leviCivitaConnection).isLeviCivita_of_koszulDual g
      (fun X Y W r => g.koszulDualSection_dual X Y W r)
  have hB : IsAlgCurvatureForm (curvatureFormAt g g.leviCivitaConnection (γ t)) :=
    isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC (γ t)
  set v : TangentSpace I (γ t) := mfderivVelocity (I := I) (E := E) γ t with hv
  -- the whole `i₀`-th column vanishes: `ℛ(γ', γ', γ', Eᵢ) = 0`
  have hcol : ∀ i, frameCurv (I := I) g γ e i i₀ t = 0 := by
    intro i
    have h : curvatureFormAt g g.leviCivitaConnection (γ t) v v v (e i t)
        = - curvatureFormAt g g.leviCivitaConnection (γ t) v v v (e i t) :=
      hB.antisymm₁₂ v v v (e i t)
    show curvatureFormAt g g.leviCivitaConnection (γ t) (e i₀ t) v v (e i t) = 0
    rw [show (e i₀ t : TangentSpace I (γ t)) = v from hrad]
    linarith
  rw [frameCurvOp_apply]
  simp only [basisFun_inner (E := E), mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, hcol, neg_zero, zero_smul, Finset.sum_const_zero]

/-! ### A parallel orthonormal frame whose first vector is the velocity -/

/-- **Math.** **The velocity of a geodesic is parallel along it.**  This *is* the
geodesic equation `∇_{γ'} γ' = 0`: in any chart containing the foot, the chart
reading of `γ'` is the chart velocity `u̇` (`chartVectorRep_velocity_of_geodesicAt`)
and the second-order geodesic ODE `ü + Γ(u̇, u̇)(u) = 0` says precisely that `u̇`
solves the (first-order, linear) parallel-transport ODE with `V = u̇`.

Blueprint: `lem:parallel-frame`, `thm:ricci-curvature-comparison`. -/
theorem isParallelAlongOn_mfderivVelocity {g : RiemannianMetric I M} {γ : ℝ → M}
    {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t) :
    IsParallelAlongOn (I := I) g γ (mfderivVelocity (I := I) γ) a b := by
  classical
  intro t₀ ht₀
  -- a relative interval around `t₀` whose `γ`-image lies in the chart at `γ t₀`
  have hnhds : γ ⁻¹' (chartAt H (γ t₀)).source ∈ 𝓝 t₀ :=
    (hγc t₀ ht₀).preimage_mem_nhds
      ((chartAt H (γ t₀)).open_source.mem_nhds (mem_chart_source H (γ t₀)))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  set α : M := γ t₀ with hα
  set c := max a (t₀ - ε / 2) with hc
  set d := min b (t₀ + ε / 2) with hd
  have hcd : c < d :=
    max_lt (lt_min hab (by linarith [ht₀.1])) (lt_min (by linarith [ht₀.2]) (by linarith))
  have htcd : t₀ ∈ Icc c d :=
    ⟨max_le ht₀.1 (by linarith), le_min ht₀.2 (by linarith)⟩
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc (le_max_left _ _) (min_le_left _ _)
  have hsrc : ∀ τ ∈ Icc c d, γ τ ∈ (chartAt H α).source := by
    intro τ hτ
    refine hball ?_
    rw [Metric.mem_ball, Real.dist_eq]
    have h1 : t₀ - ε / 2 ≤ τ := le_trans (le_max_right _ _) hτ.1
    have h2 : τ ≤ t₀ + ε / 2 := le_trans hτ.2 (min_le_right _ _)
    have h3 : |τ - t₀| ≤ ε / 2 := abs_le.2 ⟨by linarith, by linarith⟩
    linarith
  have hnb : Icc c d ∈ 𝓝[Icc a b] t₀ := by
    have hmem : Icc (t₀ - ε / 2) (t₀ + ε / 2) ∈ 𝓝 t₀ :=
      Icc_mem_nhds (by linarith) (by linarith)
    have h := inter_mem_nhdsWithin (Icc a b) hmem
    rwa [Icc_inter_Icc] at h
  -- the chart reading of the velocity is the chart velocity
  have hrep : ∀ σ ∈ Icc c d,
      chartVectorRep (I := I) γ α (mfderivVelocity (I := I) γ) σ
        = deriv (fun s => extChartAt I α (γ s)) σ := fun σ hσ =>
    chartVectorRep_velocity_of_geodesicAt (I := I) (hgeo σ (hsub hσ))
      (hγc σ (hsub hσ)) (hsrc σ hσ)
  refine ⟨α, c, d, hcd, htcd, hsub, hnb, hsrc, ?_⟩
  intro τ hτ
  obtain ⟨-, acc, hacc, heq⟩ :=
    Geodesic.HasGeodesicEquationAt.solvesGeodesicODEAt (I := I) (hgeo τ (hsub hτ))
      (hγc τ (hsub hτ)) (hsrc τ hτ)
  have hcr : Geodesic.chartReading (I := I) α γ = fun s => extChartAt I α (γ s) := rfl
  rw [hcr] at hacc heq
  have hderiv : HasDerivWithinAt (chartVectorRep (I := I) γ α (mfderivVelocity (I := I) γ))
      acc (Icc c d) τ :=
    hacc.hasDerivWithinAt.congr hrep (hrep τ hτ)
  rw [hrep τ hτ, neg_eq_of_add_eq_zero_left heq]
  exact hderiv

/-- **Math.** **Two tangent vectors with the same Gram data coincide.**  If all
four pairings `⟨x,x⟩_g, ⟨x,y⟩_g, ⟨y,x⟩_g, ⟨y,y⟩_g` have the same value `c`, then
`x = y`: their difference has `|x − y|²_g = c − c − (c − c) = 0`, and `g` is
positive definite.  (This is how ODE uniqueness for parallel transport is read off
from the fact that parallel transport is a `g`-isometry: two parallel fields with
the same initial value have all four pairings constant and equal.) -/
theorem eq_of_metricInner_eq_const (g : RiemannianMetric I M) {q : M}
    {x y : TangentSpace I q} {c : ℝ}
    (h1 : g.metricInner q x x = c) (h2 : g.metricInner q x y = c)
    (h3 : g.metricInner q y x = c) (h4 : g.metricInner q y y = c) : x = y := by
  by_contra hne
  have hsub : x - y ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hpos := g.metricInner_self_pos q (x - y) hsub
  rw [g.metricInner_sub_left, g.metricInner_sub_right, g.metricInner_sub_right,
    h1, h2, h3, h4] at hpos
  linarith

/-- **Math.** **A parallel orthonormal frame whose `0`-th vector is the velocity.**
Along a **unit-speed** geodesic `γ : [a,b] → M` there is a family `E₀, …, E_{n−1}`
parallel along `γ`, `g`-orthonormal at every `γ t`, and with

`E₀(t) = γ'(t)`   for every `t ∈ [a,b]`.

Extend the orthonormal singleton `{γ'(a)}` to an orthonormal basis of `T_{γ a}M`
(`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`) and parallel-transport
it (`exists_parallelFrameAlong`): the Gram matrix of a parallel family is constant,
so orthonormality propagates.  The transported `0`-th field and the velocity are
*both* parallel along `γ` (`isParallelAlongOn_mfderivVelocity`) with the same value
at `a`, hence agree: parallel transport is a `g`-isometry, so all four pairings
`⟨E₀, E₀⟩, ⟨E₀, γ'⟩, ⟨γ', E₀⟩, ⟨γ', γ'⟩` are constant, whence
`|E₀(t) − γ'(t)|²_g = |E₀(a) − γ'(a)|²_g = 0`.

This is the frame in which the radial direction is in the kernel of the Jacobi
operator (`frameCurvOp_radial_eq_zero`) — the frame Morgan–Tian's Ricci and
volume comparisons are computed in.

Blueprint: `lem:parallel-frame`, `thm:ricci-curvature-comparison`. -/
theorem exists_orthonormalParallelFrameAlong_velocity
    {g : RiemannianMetric I M} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc a b,
      g.metricInner (γ t) (mfderivVelocity (I := I) (E := E) γ t)
        (mfderivVelocity (I := I) (E := E) γ t) = 1) :
    ∃ e : Fin (Module.finrank ℝ E) → ℝ → E,
      (∀ i, IsParallelAlongOn (I := I) g γ (e i) a b)
        ∧ (∀ t ∈ Icc a b, ∀ i j,
            g.metricInner (γ t) (e i t : TangentSpace I (γ t)) (e j t)
              = if i = j then 1 else 0)
        ∧ ∀ t ∈ Icc a b,
            (e 0 t : TangentSpace I (γ t)) = mfderivVelocity (I := I) (E := E) γ t := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have haIcc : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  set v₀ : TangentSpace I (γ a) := mfderivVelocity (I := I) (E := E) γ a with hv₀
  -- the velocity has unit length at `a`
  have hnorm : ‖v₀‖ = 1 := by
    have h1 : ‖v₀‖ * ‖v₀‖ = 1 := by
      rw [← real_inner_self_eq_norm_mul_norm]
      exact hunit a haIcc
    rcases mul_self_eq_one_iff.mp h1 with h | h
    · exact h
    · exact absurd h (by linarith [norm_nonneg v₀])
  -- extend `{γ'(a)}` to an orthonormal basis of `T_{γ a}M`
  have hcard : Module.finrank ℝ (TangentSpace I (γ a))
      = Fintype.card (Fin (Module.finrank ℝ E)) := (Fintype.card_fin _).symm
  have hsingle : Orthonormal ℝ
      (Set.restrict ({0} : Set (Fin (Module.finrank ℝ E))) (fun _ => v₀)) := by
    constructor
    · intro i
      simpa using hnorm
    · intro i j hij
      exact absurd (Subtype.ext ((Set.mem_singleton_iff.mp i.2).trans
        (Set.mem_singleton_iff.mp j.2).symm)) hij
  obtain ⟨bas, hbas⟩ := hsingle.exists_orthonormalBasis_extension_of_card_eq hcard
  have hbas0 : bas 0 = v₀ := hbas 0 rfl
  have h0 : ∀ i j, g.metricInner (γ a) (bas i : TangentSpace I (γ a)) (bas j)
      = if i = j then 1 else 0 := fun i j => orthonormal_iff_ite.mp bas.orthonormal i j
  -- parallel-transport the basis
  obtain ⟨e, hinit, hpar, hgram⟩ :=
    exists_parallelFrameAlong (I := I) hab hgeo hγc
      (fun i => (bas i : TangentSpace I (γ a)))
  refine ⟨e, hpar, fun t ht i j => by rw [hgram i j t ht]; exact h0 i j, ?_⟩
  -- the `0`-th transported field and the velocity are parallel with the same initial value
  have hvel : IsParallelAlongOn (I := I) g γ (mfderivVelocity (I := I) γ) a b :=
    isParallelAlongOn_mfderivVelocity (I := I) hab hgeo hγc
  have he0a : (e 0 a : TangentSpace I (γ a)) = mfderivVelocity (I := I) (E := E) γ a := by
    rw [hinit 0, hbas0]
  intro t ht
  -- the four pairings are constant along `γ`
  have hVV := (hpar 0).metricInner_eq (hpar 0) hgeo hγc t ht
  have hVW := (hpar 0).metricInner_eq hvel hgeo hγc t ht
  have hWV := hvel.metricInner_eq (hpar 0) hgeo hγc t ht
  have hWW := hvel.metricInner_eq hvel hgeo hγc t ht
  rw [he0a] at hVV hVW hWV
  -- all four pairings equal `|γ'(a)|²_g`, so the difference vanishes
  exact eq_of_metricInner_eq_const (I := I) g hVV hVW hWV hWW

end PoincareLib

end

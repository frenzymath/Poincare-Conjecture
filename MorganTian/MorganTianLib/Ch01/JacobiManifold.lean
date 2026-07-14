import MorganTianLib.Ch01.CurvatureSectionalBound
import MorganTianLib.Ch01.SturmContinuation
import MorganTianLib.Ch01.Geodesics
import OpenGALib.Riemannian.Geodesic.HopfRinow.ConstantSpeed
import OpenGALib.Riemannian.Geodesic.HopfRinow.MetricBridge

/-!
# Poincaré Ch. 1, §1.4 — Jacobi fields along a geodesic and conjugate points

Manifold-level Jacobi fields along a curve `γ : ℝ → M` and Morgan–Tian's
conjugate points, on top of the chart-level Jacobi pair system
(`MorganTianLib.Ch01.JacobiField`).

A tangent vector at `γ τ` is carried, as everywhere in this development, in
the coordinates of the chart at its own foot (`TangentSpace I (γ τ) = E`), so
a *field along `γ`* is a plain map `J : ℝ → E` read at time `τ` as an element
of `T_{γ τ} M`. Its reading in the chart at a fixed basepoint `α` is
`chartVectorRep γ α J := τ ↦ tangentCoordChange I (γ τ) α (γ τ) (J τ)`.

* `IsJacobiFieldAlongOn g γ J DJ a b` — `(J, DJ)` is a Jacobi field along `γ`
  on `[a, b]`: near every time, in the chart at some basepoint containing the
  nearby piece of `γ`, the chart readings satisfy the chart Jacobi pair
  system `IsJacobiFieldOn`. The notion is chart-local, so it survives
  geodesics that leave any single chart.
* `IsConjugatePointAt g γ t₁` — Morgan–Tian's conjugate point: a Jacobi field
  along `γ` on `[0, t₁]`, vanishing at `0` and at `t₁` but not identically.
* `IsJacobiFieldAlongOn.sqrt_metricInner_comparison` — the manifold Sturm
  comparison `√⟨∇J(0), ∇J(0)⟩ · s_K(t) ≤ √⟨J(t), J(t)⟩` for a Jacobi field
  with `J(0) = 0` along a unit-speed geodesic with sectional curvature `≤ K`
  (`K ≥ 0`, `√K·T < π`).
* `IsJacobiFieldAlongOn.ne_zero_of_sectionalCurvatureAt_le` — with
  `∇J(0) ≠ 0` the field has no zero on `(0, T]`.
* `IsJacobiFieldAlongOn.eqOn_zero` — a Jacobi field along a geodesic
  vanishing together with its covariant derivative at the left endpoint
  vanishes identically (chart-local Grönwall uniqueness, propagated by a
  connectedness walk).
* `not_isConjugatePointAt_of_sectionalCurvatureAt_le` — **no conjugate
  points below `π/√K`** (blueprint `lem:conjugate-sturm`).

The multi-chart passage needs no Christoffel change-of-chart law: all
comparison data is carried by the chart-independent scalars `F = ⟨J, J⟩`,
`G = ⟨∇J, J⟩`, `Hh = ⟨∇J, ∇J⟩` (intrinsic metric pairings, computed in each
chart through `chartMetricInner_extChartAt_eq_metricInner`), which satisfy
`F' = 2G`, `G' = −⟨ℛ(J,u̇)u̇, J⟩ + Hh ≥ −K·F + Hh` and `G² ≤ F·Hh`; the
scalar Sturm continuation `scalar_sturm_comparison_extend` then propagates
the first-chart comparison `jacobi_frame_sturm_comparison` to the whole
interval.

Blueprint: `def:conjugate-point`, `lem:conjugate-sturm`.

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, §1.4–1.5.
-/

open Set Riemannian Filter
open scoped ContDiff Manifold Topology NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace MorganTianLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### Chart readings of tangent vectors carried at their own foot -/

/-- **Math.** Reading back the chart-`α` coordinates of a tangent vector at
`x` through the fibre trivialization recovers the vector: the inverse
trivialization at `α` over `x` undoes the tangent coordinate change
`T_x M → E` into the chart at `α`. -/
theorem trivializationAt_symm_tangentCoordChange {α x : M}
    (hx : x ∈ (chartAt H α).source) (v : E) :
    (trivializationAt E (TangentSpace I) α).symm x
        (tangentCoordChange I x α x v) = v := by
  rw [trivializationAt_symm_eq_tangentCoordChange (I := I) α hx,
    tangentCoordChange_comp (I := I)
      ⟨⟨mem_extChartAt_source (I := I) x,
        by rw [extChartAt_source]; exact hx⟩, mem_extChartAt_source (I := I) x⟩,
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x)]

/-- **Math.** The chart-`α` reading of a tangent vector at `x` vanishes iff
the vector does: the tangent coordinate change is a linear isomorphism. -/
theorem tangentCoordChange_eq_zero_iff {α x : M}
    (hx : x ∈ (chartAt H α).source) {v : E} :
    tangentCoordChange I x α x v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h2 := congrArg ((trivializationAt E (TangentSpace I) α).symm x) h
    rw [trivializationAt_symm_tangentCoordChange (I := I) hx,
      trivializationAt_symm_eq_tangentCoordChange (I := I) α hx] at h2
    simpa using h2
  · rintro rfl
    exact (tangentCoordChange I x α x).map_zero

/-- **Math.** The chart Gram pairing of the chart-`α` readings of two tangent
vectors at `x` is their intrinsic metric pairing: the chart-independence of
`⟨·, ·⟩_g` along a curve, pointwise form. -/
theorem chartMetricInner_tangentCoordChange (g : RiemannianMetric I M)
    {α x : M} (hx : x ∈ (chartAt H α).source) (v w : TangentSpace I x) :
    chartMetricInner (I := I) g α (extChartAt I α x)
        (tangentCoordChange I x α x v) (tangentCoordChange I x α x w)
      = g.metricInner x v w := by
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g α hx,
    trivializationAt_symm_tangentCoordChange (I := I) hx,
    trivializationAt_symm_tangentCoordChange (I := I) hx]

/-- **Math.** Positive definiteness of the intrinsic metric pairing:
`0 < ⟨v, v⟩_g` for `v ≠ 0` in `T_x M`. -/
theorem metricInner_self_pos (g : RiemannianMetric I M) {x : M}
    {v : TangentSpace I x} (hv : v ≠ 0) :
    0 < g.metricInner x v v := by
  have hx : x ∈ (chartAt H x).source := mem_chart_source H x
  rw [← chartMetricInner_tangentCoordChange (I := I) g hx v v,
    tangentCoordChange_self (I := I) (mem_extChartAt_source (I := I) x)]
  refine chartMetricInner_pos (I := I) g x ?_ hv
  rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
  exact FiberBundle.mem_baseSet_trivializationAt' x

/-- **Math.** Nonnegativity of the intrinsic metric pairing. -/
theorem metricInner_self_nonneg (g : RiemannianMetric I M) (x : M)
    (v : TangentSpace I x) :
    0 ≤ g.metricInner x v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (metricInner_self_pos (I := I) g hv).le

/-! ### Cauchy–Schwarz for the chart Gram pairing -/

/-- **Math.** Nonnegativity of the chart Gram quadratic form over the
trivialization base set. -/
theorem chartMetricInner_self_nonneg (g : RiemannianMetric I M) (α : M) {y : E}
    (hbase : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) (a : E) :
    0 ≤ chartMetricInner (I := I) g α y a a := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [chartMetricInner_zero_left]
  · exact (chartMetricInner_pos (I := I) g α hbase ha).le

/-- **Math.** **Cauchy–Schwarz** for the chart Gram pairing:
`⟨a, b⟩² ≤ ⟨a, a⟩ ⟨b, b⟩`, by nonnegativity of the discriminant of
`λ ↦ ⟨λa + b, λa + b⟩`. -/
theorem chartMetricInner_sq_le (g : RiemannianMetric I M) (α : M) {y : E}
    (hbase : (extChartAt I α).symm y
      ∈ (trivializationAt E (TangentSpace I) α).baseSet) (a b : E) :
    chartMetricInner (I := I) g α y a b ^ 2
      ≤ chartMetricInner (I := I) g α y a a
        * chartMetricInner (I := I) g α y b b := by
  have key : ∀ lam : ℝ, 0 ≤ chartMetricInner (I := I) g α y a a * (lam * lam)
      + 2 * chartMetricInner (I := I) g α y a b * lam
      + chartMetricInner (I := I) g α y b b := by
    intro lam
    have h0 := chartMetricInner_self_nonneg (I := I) g α hbase (lam • a + b)
    have hexp : chartMetricInner (I := I) g α y (lam • a + b) (lam • a + b)
        = chartMetricInner (I := I) g α y a a * (lam * lam)
          + 2 * chartMetricInner (I := I) g α y a b * lam
          + chartMetricInner (I := I) g α y b b := by
      rw [chartMetricInner_add_left, chartMetricInner_add_right,
        chartMetricInner_add_right, chartMetricInner_smul_left,
        chartMetricInner_smul_right, chartMetricInner_smul_left,
        chartMetricInner_smul_right, chartMetricInner_comm (I := I) g α y b a]
      ring
    rw [hexp] at h0
    linarith
  have hd := discrim_le_zero key
  rw [discrim] at hd
  nlinarith [hd]

/-! ### Manifold-level Jacobi fields along a curve -/

/-- **Math.** The reading, in the chart at the fixed basepoint `α`, of a
field of tangent vectors along `γ` carried at their own feet: at time `τ`
the vector `J τ ∈ T_{γ τ} M` is pushed into the chart at `α` by the tangent
coordinate change. -/
def chartVectorRep (γ : ℝ → M) (α : M) (J : ℝ → E) : ℝ → E :=
  fun τ => tangentCoordChange I (γ τ) α (γ τ) (J τ)

@[simp] theorem chartVectorRep_apply (γ : ℝ → M) (α : M) (J : ℝ → E) (τ : ℝ) :
    chartVectorRep (I := I) γ α J τ
      = tangentCoordChange I (γ τ) α (γ τ) (J τ) := rfl

/-- **Math.** **Jacobi field along a curve, manifold form** (Morgan–Tian
§1.4). A pair of fields `J, DJ : ℝ → E` along `γ` (each `J τ` read as an
element of `T_{γ τ} M`) is a *Jacobi field with covariant derivative `DJ` on
`[a, b]`* if near every time `t₀ ∈ [a, b]` there are a chart basepoint `α`
and a subinterval `[a', b'] ∋ t₀`, a neighbourhood of `t₀` in `[a, b]` whose
`γ`-image lies in the chart at `α`, on which the chart readings of `(J, DJ)`
satisfy the chart Jacobi pair system `∇J = DJ`,
`∇DJ = −ℛ(J, u̇)u̇` (`IsJacobiFieldOn`). The notion is chart-local, so it is
meaningful for curves that leave any single chart.

Blueprint: `def:conjugate-point` (the "Jacobi field along `γ`" it
quantifies over), `lem:jacobi-field-coordinates`. -/
def IsJacobiFieldAlongOn (g : RiemannianMetric I M) (γ : ℝ → M)
    (J DJ : ℝ → E) (a b : ℝ) : Prop :=
  ∀ t₀ ∈ Icc a b, ∃ (α : M) (a' b' : ℝ), a' < b' ∧ t₀ ∈ Icc a' b' ∧
    Icc a' b' ⊆ Icc a b ∧ Icc a' b' ∈ 𝓝[Icc a b] t₀ ∧
    (∀ τ ∈ Icc a' b', γ τ ∈ (chartAt H α).source) ∧
    IsJacobiFieldOn (I := I) g α (fun τ => extChartAt I α (γ τ))
      (chartVectorRep (I := I) γ α J) (chartVectorRep (I := I) γ α DJ) a' b'

/-- **Math.** **Conjugate point** (Morgan–Tian §1.4). For a geodesic `γ`
beginning at `p = γ 0`, the point `γ t₁` is *conjugate along `γ`* if there
is a Jacobi field along `γ|_{[0,t₁]}`, not identically zero, vanishing at
`p` and at `γ t₁`. (Morgan–Tian leave the vanishing at `p` implicit in the
phrase "geodesic beginning at `p`"; it is used in their proofs and is made
explicit here.)

Blueprint: `def:conjugate-point`. -/
def IsConjugatePointAt (g : RiemannianMetric I M) (γ : ℝ → M) (t₁ : ℝ) : Prop :=
  ∃ J DJ : ℝ → E, IsJacobiFieldAlongOn (I := I) g γ J DJ 0 t₁ ∧
    (∃ t ∈ Icc (0:ℝ) t₁, J t ≠ 0) ∧ J 0 = 0 ∧ J t₁ = 0

/-! ### The fixed-chart geodesic package

Along a geodesic, in any chart whose source contains the relevant piece of
`γ`, the chart curve `u = φ_α ∘ γ` is `C¹` and its velocity has the intrinsic
squared speed as chart Gram norm — first-order chart-change transfer only,
no Christoffel transformation law. -/

section GeodesicPackage

variable [I.Boundaryless]

/-- **Math.** Along a geodesic, the fixed-chart curve `u = φ_α ∘ γ` is
(two-sidedly) differentiable at every time whose foot lies in the chart. -/
theorem IsGeodesicOn.differentiableAt_extChartAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {α : M} {τ : ℝ} (hτ : τ ∈ s) (hc : ContinuousAt γ τ)
    (hsrc : γ τ ∈ (chartAt H α).source) :
    DifferentiableAt ℝ (fun t => extChartAt I α (γ t)) τ :=
  (((hgeo τ hτ).eventually_hasDerivAt_extChartAt hc hsrc).self_of_nhds).differentiableAt

/-- **Math.** Along a geodesic, the fixed-chart velocity `u̇` is continuous
at every time whose foot lies in the chart. -/
theorem IsGeodesicOn.continuousAt_deriv_extChartAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {s : Set ℝ} (hgeo : IsGeodesicOn (I := I) g γ s)
    {α : M} {τ : ℝ} (hτ : τ ∈ s) (hc : ContinuousAt γ τ)
    (hsrc : γ τ ∈ (chartAt H α).source) :
    ContinuousAt (deriv (fun t => extChartAt I α (γ t))) τ :=
  (hgeo τ hτ).continuousAt_deriv_extChartAt hc hsrc

/-- **Math.** The chart Gram norm of the fixed-chart velocity of a geodesic
is the intrinsic squared speed: `⟨u̇, u̇⟩_{G(u)} = |γ̇|²_g`, in any chart
containing the foot. -/
theorem chartMetricInner_deriv_extChartAt {g : RiemannianMetric I M}
    {γ : ℝ → M} {τ : ℝ}
    (h : Geodesic.HasGeodesicEquationAt (I := I) g γ τ)
    (hc : ContinuousAt γ τ) {α : M} (hsrc : γ τ ∈ (chartAt H α).source) :
    chartMetricInner (I := I) g α (extChartAt I α (γ τ))
        (deriv (fun t => extChartAt I α (γ t)) τ)
        (deriv (fun t => extChartAt I α (γ t)) τ)
      = Geodesic.speedSq (I := I) g γ τ := by
  rw [h.deriv_extChartAt_eq hc hsrc,
    chartMetricInner_tangentCoordChange (I := I) g hsrc,
    Geodesic.speedSq_def, h.mfderiv_apply_one hc]

/-- **Math.** Differentiability of the chart Gram coefficients at points of
the chart target. -/
theorem differentiableAt_chartGramOnE (g : RiemannianMetric I M) (α : M)
    {y : E} (hy : y ∈ (extChartAt I α).target)
    (i j : Fin (Module.finrank ℝ E)) :
    DifferentiableAt ℝ (chartGramOnE (I := I) g α i j) y :=
  ((chartGramOnE_contDiffOn (I := I) g α i j).contDiffAt
    (extChartAt_target_mem_nhds' (I := I) hy)).differentiableAt (by norm_num)

end GeodesicPackage

/-! ### Chart-independent scalars along a Jacobi field

`F = ⟨J, J⟩`, `G = ⟨DJ, J⟩`, `Hh = ⟨DJ, DJ⟩` are intrinsic metric pairings;
in any chart containing the foot they are computed by the chart Gram pairing
of the chart readings, and the chart Jacobi system yields `F' = 2G` and
`G' = −⟨ℛ(J,u̇)u̇, J⟩ + Hh`. -/

section Scalars

variable [I.Boundaryless]

/-- **Math.** The intrinsic pairing `⟨V, W⟩_g` along `γ` equals the chart
Gram pairing of the chart readings, in any chart containing the foot. -/
theorem metricInner_eq_chartMetricInner_rep (g : RiemannianMetric I M)
    {γ : ℝ → M} {α : M} {τ : ℝ} (hsrc : γ τ ∈ (chartAt H α).source)
    (V W : ℝ → E) :
    g.metricInner (γ τ) (V τ : TangentSpace I (γ τ)) (W τ)
      = chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ) (chartVectorRep (I := I) γ α W τ) :=
  (chartMetricInner_tangentCoordChange (I := I) g hsrc (V τ) (W τ)).symm

/-- **Math.** Continuity, within a chart interval, of the chart Gram pairing
of two continuous coordinate fields along a continuous chart curve. -/
theorem continuousOn_chartMetricInner_pairing (g : RiemannianMetric I M)
    (α : M) {u V W : ℝ → E} {a b : ℝ}
    (hu : ContinuousOn u (Icc a b))
    (hmem : ∀ τ ∈ Icc a b, u τ ∈ (extChartAt I α).target)
    (hV : ContinuousOn V (Icc a b)) (hW : ContinuousOn W (Icc a b)) :
    ContinuousOn (fun τ => chartMetricInner (I := I) g α (u τ) (V τ) (W τ))
      (Icc a b) := by
  simp only [chartMetricInner_def]
  refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
  · intro τ hτ
    exact ((differentiableAt_chartGramOnE (I := I) g α (hmem τ hτ) i j).continuousAt.comp_continuousWithinAt
      (hu τ hτ))
  · exact ((Geodesic.chartCoordFunctional (E := E) i).continuous.comp_continuousOn hV).congr
      fun τ _ => rfl
  · exact ((Geodesic.chartCoordFunctional (E := E) j).continuous.comp_continuousOn hW).congr
      fun τ _ => rfl

/-- **Math.** At its own basepoint chart, the chart Gram pairing is the
intrinsic pairing on the nose. -/
theorem chartMetricInner_self_chart (g : RiemannianMetric I M) (x : M) (a c : E) :
    chartMetricInner (I := I) g x (extChartAt I x x) a c
      = g.metricInner x (a : TangentSpace I x) c := by
  rw [chartMetricInner_extChartAt_eq_metricInner (I := I) g x (mem_chart_source H x),
    trivializationAt_symm_self, trivializationAt_symm_self]

/-- **Math.** **Cauchy–Schwarz** for the intrinsic metric pairing:
`⟨v, w⟩² ≤ ⟨v, v⟩ ⟨w, w⟩` in `T_x M`. -/
theorem metricInner_sq_le (g : RiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) :
    g.metricInner x v w ^ 2 ≤ g.metricInner x v v * g.metricInner x w w := by
  have hbase : (extChartAt I x).symm (extChartAt I x x)
      ∈ (trivializationAt E (TangentSpace I) x).baseSet := by
    rw [(extChartAt I x).left_inv (mem_extChartAt_source (I := I) x)]
    exact FiberBundle.mem_baseSet_trivializationAt' x
  have h := chartMetricInner_sq_le (I := I) g x (y := extChartAt I x x) hbase v w
  rwa [chartMetricInner_self_chart, chartMetricInner_self_chart,
    chartMetricInner_self_chart] at h

/-- **Math.** The readback of the chart image of a foot in the chart source
lies in the trivialization base set. -/
theorem symm_extChartAt_mem_baseSet {α x : M} (hx : x ∈ (chartAt H α).source) :
    (extChartAt I α).symm (extChartAt I α x)
      ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
  rw [(extChartAt I α).left_inv (by rw [extChartAt_source]; exact hx)]
  exact hx

end Scalars

/-! ### Chart-local derivative identities for the scalars -/

section Derivs

variable [I.Boundaryless]

/-- **Math.** Continuity on `[a, b]` of the intrinsic pairing of two fields
along `γ`, each of which is one of the two components of a Jacobi field:
chart-locally the pairing is the chart Gram pairing of the (continuous)
chart readings. -/
private theorem continuousOn_metricInner_pair {g : RiemannianMetric I M}
    {γ : ℝ → M} {J DJ V W : ℝ → E} {a b : ℝ}
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hV : V = J ∨ V = DJ) (hW : W = J ∨ W = DJ) :
    ContinuousOn
      (fun τ => g.metricInner (γ τ) (V τ : TangentSpace I (γ τ)) (W τ))
      (Icc a b) := by
  intro t ht
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hJF⟩ := hJac t ht
  have hrepV : ContinuousOn (chartVectorRep (I := I) γ α V) (Icc a' b') := by
    rcases hV with rfl | rfl
    · exact hJF.continuousOn_fst
    · exact hJF.continuousOn_snd
  have hrepW : ContinuousOn (chartVectorRep (I := I) γ α W) (Icc a' b') := by
    rcases hW with rfl | rfl
    · exact hJF.continuousOn_fst
    · exact hJF.continuousOn_snd
  have hu : ContinuousOn (fun τ => extChartAt I α (γ τ)) (Icc a' b') := by
    intro τ hτ
    exact ((continuousAt_extChartAt' (I := I)
      (by rw [extChartAt_source]; exact hsrc τ hτ)).comp
        (hγc τ (hsub hτ))).continuousWithinAt
  have hmem : ∀ τ ∈ Icc a' b', extChartAt I α (γ τ) ∈ (extChartAt I α).target :=
    fun τ hτ => (extChartAt I α).map_source
      (by rw [extChartAt_source]; exact hsrc τ hτ)
  have hform := continuousOn_chartMetricInner_pairing (I := I) g α hu hmem hrepV hrepW
  have hcw : ContinuousWithinAt
      (fun τ => g.metricInner (γ τ) (V τ : TangentSpace I (γ τ)) (W τ))
      (Icc a' b') t := by
    refine (hform t ht').congr ?_ ?_
    · intro τ hτ
      exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc τ hτ) V W
    · exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht') V W
  exact hcw.mono_of_mem_nhdsWithin hnbhd

/-- **Math.** The curvature-pairing bound along a unit-speed geodesic:
in any chart containing the foot, `⟨ℛ(v, u̇)u̇, v⟩ ≤ K ⟨v, v⟩` for every
coordinate vector `v`, from the sectional bound `K(P) ≤ K` at the foot and
`⟨u̇, u̇⟩ = 1`. -/
private theorem chart_curvature_pairing_bound [SigmaCompactSpace M] [T2Space M]
    {g : RiemannianMetric I M} {γ : ℝ → M} {K : ℝ} (hK : 0 ≤ K) {τ : ℝ}
    (hgeoτ : Geodesic.HasGeodesicEquationAt (I := I) g γ τ)
    (hγcτ : ContinuousAt γ τ)
    {α : M} (hsrcτ : γ τ ∈ (chartAt H α).source)
    (hunitτ : Geodesic.speedSq (I := I) g γ τ = 1)
    (hsecτ : ∀ v w : TangentSpace I (γ τ),
      sectionalCurvatureAt g g.leviCivitaConnection (γ τ) v w ≤ K)
    (v : E) :
    chartMetricInner (I := I) g α (extChartAt I α (γ τ))
        (chartCurvature (I := I) g α (extChartAt I α (γ τ)) v
          (deriv (fun s => extChartAt I α (γ s)) τ)
          (deriv (fun s => extChartAt I α (γ s)) τ)) v
      ≤ K * chartMetricInner (I := I) g α (extChartAt I α (γ τ)) v v := by
  have hy : extChartAt I α (γ τ) ∈ (extChartAt I α).target :=
    (extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrcτ)
  have hpt : (extChartAt I α).symm (extChartAt I α (γ τ)) = γ τ :=
    (extChartAt I α).left_inv (by rw [extChartAt_source]; exact hsrcτ)
  have hsec' : ∀ v w : TangentSpace I ((extChartAt I α).symm (extChartAt I α (γ τ))),
      sectionalCurvatureAt g g.leviCivitaConnection
        ((extChartAt I α).symm (extChartAt I α (γ τ))) v w ≤ K := by
    rw [hpt]; exact hsecτ
  have hpair := chartCurvature_pairing_le_of_sectionalCurvatureAt_le' (I := I) g
    hK hy hsec' v (deriv (fun s => extChartAt I α (γ s)) τ)
  have hspeed : chartMetricInner (I := I) g α (extChartAt I α (γ τ))
      (deriv (fun s => extChartAt I α (γ s)) τ)
      (deriv (fun s => extChartAt I α (γ s)) τ) = 1 := by
    rw [chartMetricInner_deriv_extChartAt (I := I) hgeoτ hγcτ hsrcτ, hunitτ]
  rw [hspeed, mul_one] at hpair
  exact hpair

/-- **Math.** Restriction of the chart Jacobi pair system to a subinterval. -/
theorem _root_.MorganTianLib.IsJacobiFieldOn.mono
    {g : RiemannianMetric I M} {α : M} {u J DJ : ℝ → E} {a b a' b' : ℝ}
    (h : IsJacobiFieldOn (I := I) g α u J DJ a b)
    (ha : a ≤ a') (hb : b' ≤ b) :
    IsJacobiFieldOn (I := I) g α u J DJ a' b' where
  hasDerivWithinAt_fst := fun t ht =>
    (h.hasDerivWithinAt_fst t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)
  hasDerivWithinAt_snd := fun t ht =>
    (h.hasDerivWithinAt_snd t (Icc_subset_Icc ha hb ht)).mono (Icc_subset_Icc ha hb)

/-- **Math.** The interior derivative identities for the chart-independent
scalars along a Jacobi field on a unit-speed geodesic with sectional
curvature `≤ K`: `F' = 2G` and `G'` exists with `G' ≥ −K·F + Hh`, where
`F = ⟨J, J⟩`, `G = ⟨DJ, J⟩`, `Hh = ⟨DJ, DJ⟩`. -/
private theorem jacobi_scalar_derivs [SigmaCompactSpace M] [T2Space M]
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {T K : ℝ}
    (hK : 0 ≤ K)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 T)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 T))
    (hγc : ∀ t ∈ Icc (0:ℝ) T, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0:ℝ) T, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0:ℝ) T, ∀ v w : TangentSpace I (γ t),
      sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w ≤ K)
    {t : ℝ} (ht : t ∈ Ioo (0:ℝ) T) :
    HasDerivAt (fun τ => g.metricInner (γ τ) (J τ : TangentSpace I (γ τ)) (J τ))
      (2 * g.metricInner (γ t) (DJ t : TangentSpace I (γ t)) (J t)) t ∧
    ∃ G', HasDerivAt
        (fun τ => g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (J τ)) G' t ∧
      -(K * g.metricInner (γ t) (J t : TangentSpace I (γ t)) (J t))
          + g.metricInner (γ t) (DJ t : TangentSpace I (γ t)) (DJ t) ≤ G' := by
  have htmem : t ∈ Icc (0:ℝ) T := Ioo_subset_Icc_self ht
  obtain ⟨α, a', b', hab', ht', hsub, hnbhd, hsrc, hJF⟩ := hJac t htmem
  have hIccnhds : Icc a' b' ∈ 𝓝 t := by
    rwa [nhdsWithin_eq_nhds.2 (Icc_mem_nhds ht.1 ht.2)] at hnbhd
  have htIoo : t ∈ Ioo a' b' := by
    have h := mem_interior_iff_mem_nhds.2 hIccnhds
    rwa [interior_Icc] at h
  have hut : DifferentiableAt ℝ (fun s => extChartAt I α (γ s)) t :=
    hgeo.differentiableAt_extChartAt htmem (hγc t htmem) (hsrc t ht')
  have hGdiff : ∀ i j, DifferentiableAt ℝ (chartGramOnE (I := I) g α i j)
      (extChartAt I α (γ t)) := fun i j =>
    differentiableAt_chartGramOnE (I := I) g α
      ((extChartAt I α).map_source (by rw [extChartAt_source]; exact hsrc t ht')) i j
  have hbase : (extChartAt I α).symm (extChartAt I α (γ t))
      ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    symm_extChartAt_mem_baseSet (I := I) (hsrc t ht')
  have hrepJd : DifferentiableAt ℝ (chartVectorRep (I := I) γ α J) t :=
    ((hJF.hasDerivWithinAt_fst t (Ioo_subset_Icc_self htIoo)).hasDerivAt
      hIccnhds).differentiableAt
  have hrepDJd : DifferentiableAt ℝ (chartVectorRep (I := I) γ α DJ) t :=
    ((hJF.hasDerivWithinAt_snd t (Ioo_subset_Icc_self htIoo)).hasDerivAt
      hIccnhds).differentiableAt
  have hev : ∀ V W : ℝ → E,
      (fun τ => g.metricInner (γ τ) (V τ : TangentSpace I (γ τ)) (W τ))
        =ᶠ[𝓝 t] (fun τ => chartMetricInner (I := I) g α (extChartAt I α (γ τ))
          (chartVectorRep (I := I) γ α V τ) (chartVectorRep (I := I) γ α W τ)) := by
    intro V W
    filter_upwards [hIccnhds] with τ hτ
    exact metricInner_eq_chartMetricInner_rep (I := I) g (hsrc τ hτ) V W
  constructor
  · -- F' = 2 G
    have hdF := hasDerivAt_chartMetricInner_along (I := I) g α
      (fun s => extChartAt I α (γ s)) (chartVectorRep (I := I) γ α J)
      (chartVectorRep (I := I) γ α J) hut hrepJd hrepJd hGdiff hbase
    rw [hJF.covariantDerivCoord_fst htIoo] at hdF
    have hval : chartMetricInner (I := I) g α (extChartAt I α (γ t))
          (chartVectorRep (I := I) γ α DJ t) (chartVectorRep (I := I) γ α J t)
        + chartMetricInner (I := I) g α (extChartAt I α (γ t))
          (chartVectorRep (I := I) γ α J t) (chartVectorRep (I := I) γ α DJ t)
        = 2 * g.metricInner (γ t) (DJ t : TangentSpace I (γ t)) (J t) := by
      rw [chartMetricInner_comm (I := I) g α (extChartAt I α (γ t))
        (chartVectorRep (I := I) γ α J t) (chartVectorRep (I := I) γ α DJ t),
        ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht') DJ J]
      ring
    rw [hval] at hdF
    exact hdF.congr_of_eventuallyEq (hev J J)
  · -- G' = -⟨ℛ(J,u̇)u̇, J⟩ + Hh ≥ -K F + Hh
    have hdG := hasDerivAt_chartMetricInner_along (I := I) g α
      (fun s => extChartAt I α (γ s)) (chartVectorRep (I := I) γ α DJ)
      (chartVectorRep (I := I) γ α J) hut hrepDJd hrepJd hGdiff hbase
    rw [hJF.covariantDerivCoord_fst htIoo, hJF.covariantDerivCoord_snd htIoo] at hdG
    refine ⟨_, hdG.congr_of_eventuallyEq (hev DJ J), ?_⟩
    rw [chartMetricInner_neg_left,
      ← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht') DJ DJ]
    have hpair := chart_curvature_pairing_bound (I := I) hK (hgeo t htmem)
      (hγc t htmem) (hsrc t ht') (hunit t htmem) (hsec t htmem)
      (chartVectorRep (I := I) γ α J t)
    rw [← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc t ht') J J] at hpair
    linarith

end Derivs

/-! ### The manifold Sturm comparison -/

section Main

variable [I.Boundaryless] [SigmaCompactSpace M] [T2Space M]

/-- **Math.** **Manifold Sturm comparison for Jacobi fields** (Morgan–Tian
§1.5). Let `γ` be a unit-speed geodesic on `[0, T]` with all sectional
curvatures `≤ K` along it, `K ≥ 0`, `√K · T < π`. A Jacobi field `(J, DJ)`
along `γ` with `J 0 = 0` satisfies
`√⟨DJ(0), DJ(0)⟩ · s_K(t) ≤ √⟨J(t), J(t)⟩` for `t ∈ (0, T]`.

The comparison is carried across charts by the chart-independent scalars
`F = ⟨J, J⟩`, `G = ⟨DJ, J⟩`, `Hh = ⟨DJ, DJ⟩` and the scalar Sturm
continuation; the first-chart input is `jacobi_frame_sturm_comparison`.

Blueprint: `lem:conjugate-sturm`. -/
theorem IsJacobiFieldAlongOn.sqrt_metricInner_comparison
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hπ : Real.sqrt K * T < Real.pi)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 T)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 T))
    (hγc : ∀ t ∈ Icc (0:ℝ) T, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0:ℝ) T, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0:ℝ) T, ∀ v w : TangentSpace I (γ t),
      sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w ≤ K)
    (hJ0 : J 0 = 0) :
    ∀ t ∈ Ioc (0:ℝ) T,
      Real.sqrt (g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0))
          * sinK K t
        ≤ Real.sqrt (g.metricInner (γ t) (J t : TangentSpace I (γ t)) (J t)) := by
  intro t ht
  by_cases hDJ0 : DJ 0 = 0
  · -- degenerate slope: the left side vanishes
    have hc0 : g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0) = 0 := by
      rw [hDJ0]; exact g.metricInner_zero_left (γ 0) 0
    rw [hc0, Real.sqrt_zero, zero_mul]
    exact Real.sqrt_nonneg _
  -- first-chart data at time 0
  obtain ⟨α₀, a₀, b₀, hab₀, h0mem, hsub₀, hnbhd₀, hsrc₀, hJF₀⟩ :=
    hJac 0 ⟨le_rfl, hT.le⟩
  have ha₀ : a₀ = 0 :=
    le_antisymm (h0mem.1) (hsub₀ ⟨le_rfl, hab₀.le⟩).1
  subst ha₀
  have hb₀T : b₀ ≤ T := (hsub₀ ⟨hab₀.le, le_rfl⟩).2
  have hπ₀ : Real.sqrt K * b₀ < Real.pi :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hb₀T (Real.sqrt_nonneg K)) hπ
  -- the geodesic package in the first chart
  have hu_diff : ∀ τ ∈ Icc (0:ℝ) b₀,
      DifferentiableAt ℝ (fun s => extChartAt I α₀ (γ s)) τ := fun τ hτ =>
    hgeo.differentiableAt_extChartAt (hsub₀ hτ) (hγc τ (hsub₀ hτ)) (hsrc₀ τ hτ)
  have hu_cont : ContinuousOn (fun s => extChartAt I α₀ (γ s)) (Icc (0:ℝ) b₀) :=
    fun τ hτ => (hu_diff τ hτ).continuousAt.continuousWithinAt
  have hu'_cont : ContinuousOn (deriv (fun s => extChartAt I α₀ (γ s)))
      (Icc (0:ℝ) b₀) := fun τ hτ =>
    (hgeo.continuousAt_deriv_extChartAt (hsub₀ hτ) (hγc τ (hsub₀ hτ))
      (hsrc₀ τ hτ)).continuousWithinAt
  have hGram : ∀ τ ∈ Icc (0:ℝ) b₀, ∀ i j, DifferentiableAt ℝ
      (chartGramOnE (I := I) g α₀ i j) (extChartAt I α₀ (γ τ)) := fun τ hτ i j =>
    differentiableAt_chartGramOnE (I := I) g α₀
      ((extChartAt I α₀).map_source
        (by rw [extChartAt_source]; exact hsrc₀ τ hτ)) i j
  have hbase₀ : ∀ τ ∈ Icc (0:ℝ) b₀,
      (extChartAt I α₀).symm (extChartAt I α₀ (γ τ))
        ∈ (trivializationAt E (TangentSpace I) α₀).baseSet := fun τ hτ =>
    symm_extChartAt_mem_baseSet (I := I) (hsrc₀ τ hτ)
  have hmem₀ : ∀ τ ∈ Icc (0:ℝ) b₀,
      extChartAt I α₀ (γ τ) ∈ interior (extChartAt I α₀).target := fun τ hτ => by
    rw [(isOpen_extChartAt_target α₀).interior_eq]
    exact (extChartAt I α₀).map_source
      (by rw [extChartAt_source]; exact hsrc₀ τ hτ)
  have hΓcont := continuousOn_chartChristoffelContractionRight_comp (I := I) g α₀
    hu_cont hu'_cont hmem₀
  -- curvature-pairing bound in the first chart
  have hcurv₀ : ∀ τ ∈ Ioo (0:ℝ) b₀,
      chartMetricInner (I := I) g α₀ (extChartAt I α₀ (γ τ))
          (chartCurvature (I := I) g α₀ (extChartAt I α₀ (γ τ))
            (chartVectorRep (I := I) γ α₀ J τ)
            (deriv (fun s => extChartAt I α₀ (γ s)) τ)
            (deriv (fun s => extChartAt I α₀ (γ s)) τ))
          (chartVectorRep (I := I) γ α₀ J τ)
        ≤ K * chartMetricInner (I := I) g α₀ (extChartAt I α₀ (γ τ))
            (chartVectorRep (I := I) γ α₀ J τ)
            (chartVectorRep (I := I) γ α₀ J τ) := by
    intro τ hτ
    have hτ' : τ ∈ Icc (0:ℝ) T := hsub₀ (Ioo_subset_Icc_self hτ)
    exact chart_curvature_pairing_bound (I := I) hK (hgeo τ hτ') (hγc τ hτ')
      (hsrc₀ τ (Ioo_subset_Icc_self hτ)) (hunit τ hτ') (hsec τ hτ')
      (chartVectorRep (I := I) γ α₀ J τ)
  have hJ0rep : chartVectorRep (I := I) γ α₀ J 0 = 0 := by
    simp [chartVectorRep_apply, hJ0]
  -- the first-chart Sturm comparison
  have hframe := jacobi_frame_sturm_comparison (I := I) hab₀ hK hπ₀ hJF₀
    hu_diff hGram hbase₀ hΓcont hcurv₀ hJ0rep
  -- convert it into the intrinsic start hypothesis
  have h0Icc : (0:ℝ) ∈ Icc (0:ℝ) b₀ := ⟨le_rfl, hab₀.le⟩
  have hstart : ∀ τ ∈ Ioc (0:ℝ) b₀,
      Real.sqrt (g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0))
          * sinK K τ
        ≤ Real.sqrt (g.metricInner (γ τ) (J τ : TangentSpace I (γ τ)) (J τ)) := by
    intro τ hτ
    have h := hframe τ hτ
    rwa [← metricInner_eq_chartMetricInner_rep (I := I) g (hsrc₀ 0 h0Icc) DJ DJ,
      ← metricInner_eq_chartMetricInner_rep (I := I) g
        (hsrc₀ τ (Ioc_subset_Icc_self hτ)) J J] at h
  -- the chart-independent scalar hypotheses on all of [0, T]
  have hFc := continuousOn_metricInner_pair (I := I) hJac hγc
    (Or.inl rfl) (Or.inl rfl)
  have hHhcont := continuousOn_metricInner_pair (I := I) hJac hγc
    (Or.inr rfl) (Or.inr rfl)
  have hF0 : g.metricInner (γ 0) (J 0 : TangentSpace I (γ 0)) (J 0) = 0 := by
    rw [hJ0]; exact g.metricInner_zero_left (γ 0) 0
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hHhcont
  have hHhC : ∀ᶠ τ in 𝓝[>] (0:ℝ),
      g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (DJ τ) ≤ C := by
    filter_upwards [Ioo_mem_nhdsGT hT] with τ hτ
    have h := hC τ (Ioo_subset_Icc_self hτ)
    rw [Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hc : 0 < Real.sqrt
      (g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0)) :=
    Real.sqrt_pos.2 (metricInner_self_pos (I := I) g hDJ0)
  -- assemble the scalar Sturm continuation
  have key := scalar_sturm_comparison_extend (K := K) (T := T) (b₀ := b₀)
    (F := fun τ => g.metricInner (γ τ) (J τ : TangentSpace I (γ τ)) (J τ))
    (G := fun τ => g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (J τ))
    (Hh := fun τ => g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (DJ τ))
    hK hab₀ hb₀T hπ hc hFc hF0
    (fun τ hτ => metricInner_self_nonneg (I := I) g (γ τ) (J τ))
    (fun τ hτ => (jacobi_scalar_derivs (I := I) hK hJac hgeo hγc hunit hsec hτ).1)
    (fun τ hτ => (jacobi_scalar_derivs (I := I) hK hJac hgeo hγc hunit hsec hτ).2)
    (fun τ hτ => by
      have h := metricInner_sq_le (I := I) g (γ τ) (DJ τ) (J τ)
      calc g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (J τ) ^ 2
          ≤ g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (DJ τ)
            * g.metricInner (γ τ) (J τ : TangentSpace I (γ τ)) (J τ) := h
        _ = g.metricInner (γ τ) (J τ : TangentSpace I (γ τ)) (J τ)
            * g.metricInner (γ τ) (DJ τ : TangentSpace I (γ τ)) (DJ τ) := by ring)
    hHhC hstart
  exact key t ht

/-- **Math.** **No vanishing below `π/√K`** (Morgan–Tian §1.5): a Jacobi
field along a unit-speed geodesic with sectional curvature `≤ K`, vanishing
at `0` with `DJ(0) ≠ 0`, has no zero on `(0, T]` when `√K · T < π`.

Blueprint: `lem:conjugate-sturm`. -/
theorem IsJacobiFieldAlongOn.ne_zero_of_sectionalCurvatureAt_le
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {T K : ℝ}
    (hT : 0 < T) (hK : 0 ≤ K) (hπ : Real.sqrt K * T < Real.pi)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ 0 T)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 T))
    (hγc : ∀ t ∈ Icc (0:ℝ) T, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0:ℝ) T, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0:ℝ) T, ∀ v w : TangentSpace I (γ t),
      sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w ≤ K)
    (hJ0 : J 0 = 0) (hDJ0 : DJ 0 ≠ 0) :
    ∀ t ∈ Ioc (0:ℝ) T, J t ≠ 0 := by
  intro t ht hJt
  have hcomp := hJac.sqrt_metricInner_comparison hT hK hπ hgeo hγc hunit hsec hJ0 t ht
  rw [hJt] at hcomp
  have hz : g.metricInner (γ t) ((0:E) : TangentSpace I (γ t)) (0:E) = 0 :=
    g.metricInner_zero_left (γ t) 0
  rw [hz, Real.sqrt_zero] at hcomp
  have hDJpos : 0 < g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0) :=
    metricInner_self_pos (I := I) g hDJ0
  have hsin : 0 < sinK K t := by
    refine sinK_pos K t hK ht.1 ?_
    calc Real.sqrt K * t ≤ Real.sqrt K * T :=
          mul_le_mul_of_nonneg_left ht.2 (Real.sqrt_nonneg K)
      _ < Real.pi := hπ
  have : 0 < Real.sqrt (g.metricInner (γ 0) (DJ 0 : TangentSpace I (γ 0)) (DJ 0))
      * sinK K t := mul_pos (Real.sqrt_pos.2 hDJpos) hsin
  exact absurd (lt_of_lt_of_le this hcomp) (lt_irrefl 0)

/-- **Math.** **Grönwall uniqueness along the geodesic**: a Jacobi field
along a geodesic vanishing together with its covariant derivative at the
left endpoint vanishes identically on the interval — chart-local uniqueness
of the Jacobi pair system, propagated by a connectedness walk (the set of
times up to which the pair vanishes is closed by continuity and open by
chart-local uniqueness). -/
theorem IsJacobiFieldAlongOn.eqOn_zero
    {g : RiemannianMetric I M} {γ : ℝ → M} {J DJ : ℝ → E} {a b : ℝ}
    (hab : a ≤ b)
    (hJac : IsJacobiFieldAlongOn (I := I) g γ J DJ a b)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc a b))
    (hγc : ∀ t ∈ Icc a b, ContinuousAt γ t)
    (hJa : J a = 0) (hDJa : DJ a = 0) :
    ∀ t ∈ Icc a b, J t = 0 ∧ DJ t = 0 := by
  classical
  -- the set of times up to which the pair vanishes
  set S : Set ℝ := {s | s ∈ Icc a b ∧ ∀ τ ∈ Icc a s, J τ = 0 ∧ DJ τ = 0} with hS
  have haS : a ∈ S := ⟨left_mem_Icc.2 hab, fun τ hτ => by
    obtain rfl : τ = a := le_antisymm hτ.2 hτ.1
    exact ⟨hJa, hDJa⟩⟩
  have hSb : ∀ s ∈ S, s ≤ b := fun s hs => hs.1.2
  have hbdd : BddAbove S := ⟨b, fun s hs => hSb s hs⟩
  have hSne : S.Nonempty := ⟨a, haS⟩
  set c := sSup S with hcdef
  have hac : a ≤ c := le_csSup hbdd haS
  have hcb : c ≤ b := csSup_le hSne hSb
  -- everything strictly below the supremum vanishes
  have hbelow : ∀ τ ∈ Ico a c, J τ = 0 ∧ DJ τ = 0 := by
    intro τ hτ
    obtain ⟨s, hsS, hτs⟩ := exists_lt_of_lt_csSup hSne hτ.2
    exact hsS.2 τ ⟨hτ.1, hτs.le⟩
  -- chart data at the supremum
  obtain ⟨α, a', b', hab', hc', hsub', hnbhd', hsrc', hJF'⟩ := hJac c ⟨hac, hcb⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.1 hnbhd'
  -- the pair vanishes at the supremum itself
  have hcz : J c = 0 ∧ DJ c = 0 := by
    rcases eq_or_lt_of_le hac with heq | hlt
    · rw [← heq]; exact ⟨hJa, hDJa⟩
    · -- a < c: the chart readings vanish on a left approach interval and are
      -- continuous within the chart interval, hence vanish at c
      have ha'c : a' < c := by
        have hτmem : max a (c - ε / 2) ∈ Metric.ball c ε ∩ Icc a b := by
          constructor
          · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by
              simp only [sub_nonpos]; exact max_le hlt.le (by linarith)), neg_sub]
            have : c - ε / 2 ≤ max a (c - ε / 2) := le_max_right _ _
            linarith
          · exact ⟨le_max_left _ _, le_trans (max_le hlt.le (by linarith)) hcb⟩
        have := hball hτmem
        exact lt_of_le_of_lt this.1 (max_lt hlt (by linarith))
      set m := max a' (max a (c - ε / 2)) with hm_def
      have hmc : m < c := max_lt ha'c (max_lt hlt (by linarith))
      have hLsub : Ioo m c ⊆ Icc a' b' := fun τ hτ =>
        ⟨le_trans (le_max_left _ _) hτ.1.le, le_trans hτ.2.le hc'.2⟩
      have hLbelow : Ioo m c ⊆ Ico a c := fun τ hτ =>
        ⟨le_trans (le_trans (le_max_left _ _) (le_max_right a' _)) hτ.1.le, hτ.2⟩
      have hcclosure : c ∈ closure (Ioo m c) := by
        rw [closure_Ioo hmc.ne]; exact ⟨hmc.le, le_rfl⟩
      have hNeBot : (𝓝[Ioo m c] c).NeBot :=
        mem_closure_iff_nhdsWithin_neBot.1 hcclosure
      constructor
      · refine (tangentCoordChange_eq_zero_iff (I := I) (hsrc' c hc')).1 ?_
        refine tendsto_nhds_unique (f := chartVectorRep (I := I) γ α J)
          (l := 𝓝[Ioo m c] c)
          (((hJF'.continuousOn_fst c hc').mono hLsub) : Tendsto _ _ _) ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hJτ : J τ = 0 := (hbelow τ (hLbelow hτ)).1
        simp [chartVectorRep_apply, hJτ]
      · refine (tangentCoordChange_eq_zero_iff (I := I) (hsrc' c hc')).1 ?_
        refine tendsto_nhds_unique (f := chartVectorRep (I := I) γ α DJ)
          (l := 𝓝[Ioo m c] c)
          (((hJF'.continuousOn_snd c hc').mono hLsub) : Tendsto _ _ _) ?_
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hDJτ : DJ τ = 0 := (hbelow τ (hLbelow hτ)).2
        simp [chartVectorRep_apply, hDJτ]
  -- the supremum is b: otherwise chart-local uniqueness pushes past it
  have hcb' : c = b := by
    by_contra hne
    have hclt : c < b := lt_of_le_of_ne hcb hne
    -- the chart interval extends strictly past c
    have hcb'2 : c < b' := by
      have hτmem : min b (c + ε / 2) ∈ Metric.ball c ε ∩ Icc a b := by
        constructor
        · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by
            simp only [sub_nonneg]; exact le_min hclt.le (by linarith))]
          have : min b (c + ε / 2) ≤ c + ε / 2 := min_le_right _ _
          linarith
        · exact ⟨le_trans hac (le_min hclt.le (by linarith)), min_le_left _ _⟩
      have := hball hτmem
      exact lt_of_lt_of_le (lt_min hclt (by linarith)) this.2
    set b'' := min b' (min b (c + ε / 2)) with hb''_def
    have hcb'' : c < b'' := lt_min hcb'2 (lt_min hclt (by linarith))
    have hb''sub : Icc c b'' ⊆ Icc a' b' := fun τ hτ =>
      ⟨le_trans hc'.1 hτ.1, le_trans hτ.2 (min_le_left _ _)⟩
    have hb''ab : Icc c b'' ⊆ Icc a b := fun τ hτ =>
      ⟨le_trans hac hτ.1, le_trans hτ.2 (le_trans (min_le_right _ _)
        (min_le_left _ _))⟩
    -- geodesic package on [c, b'']
    have hu_diff : ∀ τ ∈ Icc c b'',
        DifferentiableAt ℝ (fun s => extChartAt I α (γ s)) τ := fun τ hτ =>
      hgeo.differentiableAt_extChartAt (hb''ab hτ) (hγc τ (hb''ab hτ))
        (hsrc' τ (hb''sub hτ))
    have hu_cont : ContinuousOn (fun s => extChartAt I α (γ s)) (Icc c b'') :=
      fun τ hτ => (hu_diff τ hτ).continuousAt.continuousWithinAt
    have hu'_cont : ContinuousOn (deriv (fun s => extChartAt I α (γ s)))
        (Icc c b'') := fun τ hτ =>
      (hgeo.continuousAt_deriv_extChartAt (hb''ab hτ) (hγc τ (hb''ab hτ))
        (hsrc' τ (hb''sub hτ))).continuousWithinAt
    have hmem : ∀ τ ∈ Icc c b'',
        extChartAt I α (γ τ) ∈ interior (extChartAt I α).target := fun τ hτ => by
      rw [(isOpen_extChartAt_target α).interior_eq]
      exact (extChartAt I α).map_source
        (by rw [extChartAt_source]; exact hsrc' τ (hb''sub hτ))
    obtain ⟨Kb, hKb⟩ := exists_nnnorm_jacobiPairCoeffCoord_le (I := I) g α
      hu_cont hu'_cont hmem
    -- chart-local uniqueness from c
    have hb''b' : b'' ≤ b' := by rw [hb''_def]; exact min_le_left _ _
    have hmono := hJF'.mono hc'.1 hb''b'
    have hJc0 : chartVectorRep (I := I) γ α J c = 0 := by
      simp [chartVectorRep_apply, hcz.1]
    have hDJc0 : chartVectorRep (I := I) γ α DJ c = 0 := by
      simp [chartVectorRep_apply, hcz.2]
    have hz := hmono.eqOn_zero hKb hJc0 hDJc0
    -- b'' belongs to S, contradicting the supremum
    have hb''S : b'' ∈ S := by
      refine ⟨⟨le_trans hac hcb''.le, le_trans (min_le_right _ _)
        (min_le_left _ _)⟩, fun τ hτ => ?_⟩
      rcases lt_or_ge τ c with hτc | hτc
      · exact hbelow τ ⟨hτ.1, hτc⟩
      · rcases eq_or_lt_of_le hτc with heq | hτc'
        · rw [← heq]; exact hcz
        · have hτmem : τ ∈ Icc c b'' := ⟨hτc, hτ.2⟩
          constructor
          · exact (tangentCoordChange_eq_zero_iff (I := I)
              (hsrc' τ (hb''sub hτmem))).1 (hz.1 hτmem)
          · exact (tangentCoordChange_eq_zero_iff (I := I)
              (hsrc' τ (hb''sub hτmem))).1 (hz.2 hτmem)
    exact absurd (le_csSup hbdd hb''S) (not_le.2 hcb'')
  -- conclude
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · rw [heq, ← hcb']; exact hcz
  · exact hbelow t ⟨ht.1, hcb' ▸ hlt⟩

/-- **Math.** **No conjugate points below `π/√K`** (Morgan–Tian §1.5,
blueprint `lem:conjugate-sturm`). Along a unit-speed geodesic
`γ : [0, t₁] → M` whose sectional curvatures are all `≤ K` with `K ≥ 0` and
`√K · t₁ < π` (i.e. `t₁ < π/√K`, with the convention `π/√0 = ∞`), the point
`γ t₁` is not conjugate to `γ 0` along `γ`.

Blueprint: `lem:conjugate-sturm`. -/
theorem not_isConjugatePointAt_of_sectionalCurvatureAt_le
    {g : RiemannianMetric I M} {γ : ℝ → M} {t₁ K : ℝ}
    (ht₁ : 0 < t₁) (hK : 0 ≤ K) (hπ : Real.sqrt K * t₁ < Real.pi)
    (hgeo : IsGeodesicOn (I := I) g γ (Icc 0 t₁))
    (hγc : ∀ t ∈ Icc (0:ℝ) t₁, ContinuousAt γ t)
    (hunit : ∀ t ∈ Icc (0:ℝ) t₁, Geodesic.speedSq (I := I) g γ t = 1)
    (hsec : ∀ t ∈ Icc (0:ℝ) t₁, ∀ v w : TangentSpace I (γ t),
      sectionalCurvatureAt g g.leviCivitaConnection (γ t) v w ≤ K) :
    ¬ IsConjugatePointAt (I := I) g γ t₁ := by
  rintro ⟨J, DJ, hJac, ⟨t, htmem, htne⟩, hJ0, hJt₁⟩
  by_cases hDJ0 : DJ 0 = 0
  · exact htne (hJac.eqOn_zero ht₁.le hgeo hγc hJ0 hDJ0 t htmem).1
  · exact hJac.ne_zero_of_sectionalCurvatureAt_le ht₁ hK hπ hgeo hγc hunit hsec
      hJ0 hDJ0 t₁ ⟨ht₁, le_rfl⟩ hJt₁

end Main

end MorganTianLib

end

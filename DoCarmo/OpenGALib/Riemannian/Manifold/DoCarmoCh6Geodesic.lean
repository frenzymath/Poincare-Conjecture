import OpenGALib.Riemannian.Manifold.DoCarmoCh6Eigen

/-!
# do Carmo Chapter 6, Prop. 2.9 — the totally geodesic criterion

do Carmo's Proposition 2.9: an immersion is geodesic at `p ∈ M` if and only if
every geodesic of `M` starting from `p` is a geodesic of the ambient `M̄` at
`p`.

In the identified patch picture (`DCImmersedPatch`), a curve of `M` through `p`
that is geodesic *at* `p` is represented by the extension of its velocity field:
a tangent field `X` with `X(p) = x` whose induced covariant self-derivative
`∇_X X` vanishes at `p` (`IsGeodesicFieldAt`). Being a geodesic of the ambient
manifold at `p` then reads `∇̄_X X (p) = 0` for the ambient connection. With
this rendering, Prop. 2.9 becomes
`isGeodesicAt_iff_forall_isGeodesicFieldAt`, and its proof is do Carmo's: by
the Gauss decomposition `∇̄_X X = ∇_X X + B(X, X)`, the ambient acceleration of
a geodesic field at `p` is exactly `B(x, x)`, so it vanishes for every such
field iff `II_η(x) = H_η(x, x) = ⟨B(x,x), η⟩ = 0` for every `x` and `η` — which
is `IsGeodesicAt` (do Carmo's displayed computation
`H_η(x, x) = ⟨N, ∇̄_X X⟩(p)` is `secondFundQuadAt_eq_metricInner_cov`).

Two pieces of genuinely new infrastructure make the "only if" direction work:

* `exists_contMDiff_dirTangent_eq_one` — a smooth global scalar with prescribed
  value `0` and derivative `1` at `p` along a given `v ≠ 0` (a chart coordinate
  functional cut off by a smooth bump);
* `exists_isGeodesicFieldAt` — through every `x ∈ T_pM` there is a geodesic
  field at `p`: correct a tangent extension `X₀` of `x` by `f • W`, where
  `W(p) = −(∇_{X₀} X₀)(p)` and `f(p) = 0`, `df_p(x) = 1`, so the Leibniz
  first-order term cancels the unwanted acceleration.

*Deferred (do Carmo's literal quantifier):* do Carmo quantifies over genuine
geodesics of `M` through `p` (curves with `∇_{γ'} γ' = 0` on their whole
domain). Producing such curves inside the distribution requires the leaf-wise
geodesic ODE theory that is blocked by the missing chart-Christoffel ↔
Levi-Civita bridge and smooth ODE dependence (see inbox `I-0086`, `I-0100`);
every genuine geodesic through `p` yields a geodesic field at `p` by extending
its velocity, so the class quantified over here is the correct "at `p`"
relaxation and the statement above is the honest pointwise content of
Prop. 2.9.

The file closes with do Carmo's Remark 2.9 — the geometric interpretation of
sectional curvature: at a point where the patch is geodesic, `B` vanishes, so
Gauss' theorem gives `K_S(p) = K(p, σ)` — the sectional curvature of the patch
and of the ambient manifold agree on tangent planes at `p`
(`sectionalCurvature_eq_of_isGeodesicAt` and companions). This is the displayed
equation of the remark for the geodesic surface `S = exp_p(σ ∩ B)`, read for an
abstract patch geodesic at `p`; the construction of `S` itself from the
exponential map is deferred (blueprint node `rem:dc-ch6-2-9-exp-surface`).

Reference: do Carmo, *Riemannian Geometry*, Ch. 6 §2, Prop. 2.9 and Rem. 2.9.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [CompleteSpace E] [SigmaCompactSpace M] in
/-- **Math.** Smooth scalar functions with prescribed first-order data at a
point: for every `v ∈ T_pM̄`, `v ≠ 0`, there is a globally smooth
`f : M̄ → ℝ` with `f(p) = 0` and `df_p(v) = 1`. Construction: a norming linear
functional of `v`, read through the chart at `p` and cut off by a smooth bump
at `p`. -/
theorem exists_contMDiff_dirTangent_eq_one (p : M) {v : TangentSpace I p}
    (hv : v ≠ 0) :
    ∃ (f : M → ℝ) (_ : ContMDiff I 𝓘(ℝ, ℝ) ∞ f),
      f p = 0 ∧ dirTangent (I := I) f v = 1 := by
  classical
  -- a continuous linear functional with `ℓ v = 1`
  have hvE : ‖show E from v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  obtain ⟨ℓ₀, -, hℓ₀⟩ := exists_dual_vector ℝ (show E from v) hvE
  set ℓ : E →L[ℝ] ℝ := ‖show E from v‖⁻¹ • ℓ₀ with hℓdef
  have hℓv : ℓ (show E from v) = 1 := by
    simp only [hℓdef, ContinuousLinearMap.smul_apply, hℓ₀, smul_eq_mul]
    exact inv_mul_cancel₀ hvE
  -- the shifted chart coordinate function
  set c₀ : ℝ := ℓ (extChartAt I p p) with hc₀
  set h : M → ℝ := fun q => ℓ (extChartAt I p q) - c₀ with hh
  -- a smooth bump at `p`
  let χ : SmoothBumpFunction I p := Classical.arbitrary _
  refine ⟨fun q => χ q • h q, ?_, ?_, ?_⟩
  · -- global smoothness: `h` is smooth on the chart source, then cut by `χ`
    refine χ.contMDiff_smul ?_
    have hext : ContMDiffOn I 𝓘(ℝ, E) ∞ (extChartAt I p) (chartAt H p).source :=
      contMDiffOn_extChartAt
    exact (ℓ.contMDiff.comp_contMDiffOn hext).sub contMDiffOn_const
  · -- value at `p`
    show χ p • (ℓ (extChartAt I p p) - c₀) = 0
    rw [hc₀, sub_self, smul_zero]
  · -- derivative at `p` along `v`
    have hext : HasMFDerivAt I 𝓘(ℝ, E) (extChartAt I p) p
        (ContinuousLinearMap.id ℝ (TangentSpace I p)) := by
      have hmd : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I p) p :=
        (hasMFDerivAt_extChartAt (I := I) (mem_chart_source H p)).mdifferentiableAt
      have := hmd.hasMFDerivAt
      rwa [mfderiv_extChartAt_self] at this
    have hcomp : HasMFDerivAt I 𝓘(ℝ, ℝ) (fun q => ℓ (extChartAt I p q)) p
        (ℓ : E →L[ℝ] ℝ) := by
      simpa using ℓ.hasMFDerivAt.comp p hext
    have hsub := hcomp.sub (hasMFDerivAt_const (c := c₀) (x := p))
    have hev : (fun q => χ q • h q) =ᶠ[𝓝 p]
        ((fun q => ℓ (extChartAt I p q)) - fun _ => c₀) := by
      filter_upwards [χ.eventuallyEq_one] with q hq
      simp [hq, hh]
    have hfd := hsub.congr_of_eventuallyEq hev
    have hmf := hfd.mfderiv
    show dirTangent (I := I) (fun q => χ q • h q) v = 1
    rw [dirTangent, hmf]
    show ℓ (show E from v) - 0 = 1
    rw [sub_zero]
    exact hℓv

namespace AffineConnection

omit [CompleteSpace E] in
/-- **Math.** The covariant derivative `∇_X Z` vanishes at `p` when the
direction field vanishes there — tensoriality of the direction slot, read at a
point. -/
theorem cov_apply_eq_zero_of_apply_eq_zero_left (nabla : AffineConnection I M)
    {X : SmoothVectorField I M} (Z : SmoothVectorField I M) {p : M}
    (hXp : X p = 0) : nabla.cov X Z p = 0 := by
  have hcongr : nabla.cov X Z p = nabla.cov (X - X) Z p :=
    nabla.cov_congr_apply_left Z (by rw [SmoothVectorField.sub_apply, sub_self, hXp])
  rw [hcongr, nabla.cov_sub_left, sub_self]

end AffineConnection

namespace DCImmersedPatch

variable {g : RiemannianMetric I M} (D : DCImmersedPatch I M g)
variable (nabla : AffineConnection I M)

/-- **Math.** do Carmo Ch. 6, Prop. 2.9 setup: a **geodesic field at `p`** — a
tangent field whose induced covariant self-derivative `∇_X X` vanishes at `p`.
In the identified patch picture this is the velocity extension of a curve of
`M` through `p` that is geodesic at `p` (do Carmo's "geodesic `γ` of `M`
starting from `p`", read at the point `p`). -/
def IsGeodesicFieldAt (X : SmoothVectorField I M) (p : M) : Prop :=
  D.IsTangentField X ∧ D.inducedCov nabla X X p = 0

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.9 (existence half): through every
`x ∈ T_pM` there passes a geodesic field at `p`. Correct a tangent extension
`X₀` of `x` by `f • W` with `W(p) = −(∇_{X₀}X₀)(p)`, `f(p) = 0` and
`df_p(x) = 1`: the Leibniz first-order term `X₀(f)·W` then cancels the unwanted
covariant acceleration at `p`, and all other correction terms vanish there. -/
theorem exists_isGeodesicFieldAt {p : M} {x : TangentSpace I p}
    (hx : x ∈ D.tang p) :
    ∃ X : SmoothVectorField I M, D.IsGeodesicFieldAt nabla X p ∧ X p = x := by
  by_cases hx0 : x = 0
  · -- the zero field is a geodesic field through `x = 0`
    subst hx0
    refine ⟨0, ⟨fun q => by rw [SmoothVectorField.zero_apply]; exact zero_mem _, ?_⟩,
      SmoothVectorField.zero_apply p⟩
    have hcov : nabla.cov 0 0 p = 0 :=
      nabla.cov_apply_eq_zero_of_apply_eq_zero_left 0
        (SmoothVectorField.zero_apply p)
    show D.tangentProj (nabla.cov 0 0) p = 0
    rw [D.tangentProj_congr_apply (Y := 0) (by rw [hcov, SmoothVectorField.zero_apply]),
      D.tangentProj_zero, SmoothVectorField.zero_apply]
  · -- the correction construction
    obtain ⟨f, hf, hfp, hfd⟩ := exists_contMDiff_dirTangent_eq_one (I := I) p hx0
    set X₀ : SmoothVectorField I M := D.tangentExtension p x with hX₀def
    have hX₀t : D.IsTangentField X₀ := D.isTangentField_tangentExtension p x
    have hX₀p : X₀ p = x := D.tangentExtension_apply_self hx
    set a : TangentSpace I p := D.inducedCov nabla X₀ X₀ p with hadef
    have hamem : a ∈ D.tang p := D.isTangentField_inducedCov nabla X₀ X₀ p
    set W : SmoothVectorField I M := D.tangentExtension p (-a) with hWdef
    have hWt : D.IsTangentField W := D.isTangentField_tangentExtension p (-a)
    have hWp : W p = -a := D.tangentExtension_apply_self (neg_mem hamem)
    set X : SmoothVectorField I M := X₀ + SmoothVectorField.smul f hf W with hXdef
    have hXt : D.IsTangentField X := fun q => by
      rw [hXdef, SmoothVectorField.add_apply, SmoothVectorField.smul_apply]
      exact add_mem (hX₀t q) (Submodule.smul_mem _ _ (hWt q))
    have hXp : X p = x := by
      rw [hXdef, SmoothVectorField.add_apply, SmoothVectorField.smul_apply, hfp,
        hX₀p, zero_smul, add_zero]
    -- expand `∇_X X` by bilinearity and the Leibniz rule
    have hexp : D.inducedCov nabla X X
        = D.inducedCov nabla X₀ X₀
          + (SmoothVectorField.smul f hf (D.inducedCov nabla X₀ W)
             + SmoothVectorField.smul (X₀.dir f) (X₀.dir_contMDiff hf) W)
          + SmoothVectorField.smul f hf (D.inducedCov nabla W X) := by
      conv_lhs => rw [hXdef]
      rw [D.inducedCov_add_left, D.inducedCov_smul_left, ← hXdef,
        D.inducedCov_add_right, D.inducedCov_smul_right nabla hf X₀ hWt]
    have hdirp : X₀.dir f p = 1 := by
      have hrfl : X₀.dir f p = dirTangent (I := I) f (X₀ p) := rfl
      rw [hrfl, hX₀p]
      exact hfd
    refine ⟨X, ⟨hXt, ?_⟩, hXp⟩
    have hval := congrArg (fun F : SmoothVectorField I M => F p) hexp
    simp only [SmoothVectorField.add_apply, SmoothVectorField.smul_apply, hfp,
      zero_smul, zero_add, add_zero, hdirp, one_smul, hWp, ← hadef] at hval
    rw [hval, add_neg_cancel]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, Prop. 2.9, the displayed computation: for a
tangent field `X` with `X(p) = x` and a normal vector `η` at `p`,
`II_η(x) = H_η(x, x) = ⟨∇̄_X X, η⟩(p)` — the second fundamental form along `η`
evaluates the *ambient* covariant acceleration against `η` (do Carmo derives
this via the Weingarten pairing `⟨N, ∇̄_X X⟩ = −⟨∇̄_X N, X⟩`; here it is the
Gauss decomposition paired against `η`). -/
theorem secondFundQuadAt_eq_metricInner_cov {p : M} {x : TangentSpace I p}
    {X : SmoothVectorField I M} (hXt : D.IsTangentField X) (hXp : X p = x)
    {η : TangentSpace I p} (hη : η ∈ D.normalSpace p) :
    D.secondFundQuadAt nabla p η x = g.metricInner p (nabla.cov X X p) η := by
  rw [secondFundQuadAt, secondFundScalarAt, ← hXp,
    D.secondFundFormAt_apply_apply nabla hXt X p]
  show g.metricInner p (D.normalProj (nabla.cov X X) p) η = _
  rw [D.normalProj_apply, g.metricInner_sub_left,
    D.inner_eq_zero_of_mem_tang_of_mem_normalSpace (D.tangentProj_mem _ p) hη,
    sub_zero]

omit [CompleteSpace E] in
/-- **Math.** do Carmo Ch. 6, **Prop. 2.9** (totally geodesic criterion): the
immersion is geodesic at `p ∈ M` if and only if every geodesic field at `p`
(the velocity extension of a geodesic of `M` through `p`, read at `p`) has
vanishing *ambient* covariant acceleration at `p` — i.e. every geodesic of `M`
starting from `p` is a geodesic of `M̄` at `p`.

`⇒`: by the Gauss decomposition `∇̄_X X = ∇_X X + B(X, X)`, at `p` the ambient
acceleration of a geodesic field is `B(x, x)`, which vanishes because all the
second fundamental forms do. `⇐`: through every `x ∈ T_pM` there is a geodesic
field at `p` (`exists_isGeodesicFieldAt`); its ambient acceleration `B(x, x)`
vanishes by hypothesis, so `II_η(x) = ⟨B(x, x), η⟩ = 0` for every `η`. -/
theorem isGeodesicAt_iff_forall_isGeodesicFieldAt (p : M) :
    D.IsGeodesicAt nabla p ↔
      ∀ X : SmoothVectorField I M, D.IsGeodesicFieldAt nabla X p →
        nabla.cov X X p = 0 := by
  constructor
  · rintro hgeo X ⟨hXt, hind⟩
    -- Gauss decomposition at `p`
    have hsplit := congrArg (fun F : SmoothVectorField I M => F p)
      (D.cov_eq_inducedCov_add_secondFundForm nabla X X)
    simp only [SmoothVectorField.add_apply] at hsplit
    -- the second fundamental form vanishes at `p`
    have hB : D.secondFundFormAt nabla p (X p) (X p) = 0 := by
      refine D.eq_of_inner_eq_of_mem_normalSpace
        (D.secondFundFormAt_mem nabla p _ _) (zero_mem _) fun w hw => ?_
      rw [g.metricInner_zero_left]
      exact hgeo w hw (X p) (hXt p)
    have hBfield : D.secondFundForm nabla X X p = 0 := by
      rw [← D.secondFundFormAt_apply_apply nabla hXt X p, hB]
    rw [hsplit, hind, hBfield, add_zero]
  · intro hgeo η hη x hx
    obtain ⟨X, hXfield, hXp⟩ := D.exists_isGeodesicFieldAt nabla hx
    have hcov : nabla.cov X X p = 0 := hgeo X hXfield
    rw [D.secondFundQuadAt_eq_metricInner_cov nabla hXfield.1 hXp hη, hcov,
      g.metricInner_zero_left]

omit [CompleteSpace E] in
/-- **Math.** Consequence of Prop. 2.9 for the global notion: a totally
geodesic immersion sends geodesic fields to ambient-geodesic data at every
point. -/
theorem IsTotallyGeodesic.cov_apply_eq_zero {D : DCImmersedPatch I M g}
    {nabla : AffineConnection I M} (htot : D.IsTotallyGeodesic nabla)
    {X : SmoothVectorField I M} {p : M} (hX : D.IsGeodesicFieldAt nabla X p) :
    nabla.cov X X p = 0 :=
  (D.isGeodesicAt_iff_forall_isGeodesicFieldAt nabla p).mp (htot p) X hX

/-! ### do Carmo Rem. 2.9 — the geometric interpretation of sectional curvature

At a point where the patch is geodesic the second fundamental form vanishes,
so Gauss' theorem (`thm:dc-ch6-2-5`) has vanishing right-hand side: the
sectional curvature of the patch agrees with the ambient sectional curvature
of the tangent plane. This is the displayed equation `K_S(p) = K(p, σ)` of
do Carmo's Remark 2.9 — for the surface `S = exp_p(σ ∩ B)` of small geodesics
tangent to a plane `σ ⊆ T_pM`, which is geodesic at `p` by Prop. 2.9 — read at
the level of an abstract patch geodesic at `p`; Riemann's original definition
of sectional curvature. -/

/-- **Math.** At a point where the patch is geodesic, the (vector-valued)
second fundamental form vanishes on tangent fields: `B(X, Y)(p) = 0` — the
field-level form of `isGeodesicAt_iff_secondFundFormAt_eq_zero`. -/
theorem secondFundForm_apply_eq_zero_of_isGeodesicAt
    (hLC : nabla.IsLeviCivita g) {p : M} (hgeo : D.IsGeodesicAt nabla p)
    {X Y : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) :
    D.secondFundForm nabla X Y p = 0 := by
  rw [← D.secondFundFormAt_apply_apply nabla hY X p]
  exact (D.isGeodesicAt_iff_secondFundFormAt_eq_zero nabla hLC p).mp hgeo
    (X p) (hX p) (Y p) (hY p)

/-- **Math.** do Carmo Ch. 6, Rem. 2.9, numerator form: at a point where the
patch is geodesic, the sectional numerators of the induced and the ambient
connection agree on tangent fields:

`⟨R(X,Y)X, Y⟩(p) = ⟨R̄(X,Y)X, Y⟩(p)`.

By Gauss' theorem (Thm. 2.5, `inducedCurvature_inner_sub_curvature_inner`)
the difference is `⟨B(X,X), B(Y,Y)⟩ − |B(X,Y)|²`, and `B` vanishes at `p`. -/
theorem inducedCurvature_inner_eq_curvature_inner_of_isGeodesicAt
    (hLC : nabla.IsLeviCivita g) {p : M} (hgeo : D.IsGeodesicAt nabla p)
    {X Y : SmoothVectorField I M} (hX : D.IsTangentField X)
    (hY : D.IsTangentField Y) :
    g.metricInner p (D.inducedCurvature nabla X Y X p) (Y p)
      = g.metricInner p (nabla.curvature X Y X p) (Y p) := by
  have h := D.inducedCurvature_inner_sub_curvature_inner nabla hLC hX hY p
  rw [D.secondFundForm_apply_eq_zero_of_isGeodesicAt nabla hLC hgeo hX hX,
    D.secondFundForm_apply_eq_zero_of_isGeodesicAt nabla hLC hgeo hX hY] at h
  simp only [g.metricInner_zero_left] at h
  linarith

/-- **Math.** do Carmo Ch. 6, Rem. 2.9 (geometric interpretation of sectional
curvature): `K_S(p) = K(p, σ)` — at a point where the patch is geodesic, the
sectional curvature of the patch (for a two-dimensional patch: its Gaussian
curvature `K_S(p)`) equals the ambient sectional curvature of the tangent
plane `σ` spanned by the values of the tangent fields. Stated, like Gauss'
theorem (`gauss_theorem`), for tangent fields whose values at `p` are
orthonormal — the plane `σ` is genuinely two-dimensional and the normalization
`|x|²|y|² − ⟨x,y⟩²` of `def:dc-ch4-3-2` equals `1`. -/
theorem sectionalCurvature_eq_of_isGeodesicAt (hLC : nabla.IsLeviCivita g)
    {p : M} (hgeo : D.IsGeodesicAt nabla p) {X Y : SmoothVectorField I M}
    (hX : D.IsTangentField X) (hY : D.IsTangentField Y)
    (hXX : g.metricInner p (X p) (X p) = 1)
    (hYY : g.metricInner p (Y p) (Y p) = 1)
    (hXY : g.metricInner p (X p) (Y p) = 0) :
    g.metricInner p (D.inducedCurvature nabla X Y X p) (Y p)
        / (g.metricInner p (X p) (X p) * g.metricInner p (Y p) (Y p)
            - g.metricInner p (X p) (Y p) ^ 2)
      = g.metricInner p (nabla.curvature X Y X p) (Y p)
        / (g.metricInner p (X p) (X p) * g.metricInner p (Y p) (Y p)
            - g.metricInner p (X p) (Y p) ^ 2) := by
  rw [hXX, hYY, hXY,
    D.inducedCurvature_inner_eq_curvature_inner_of_isGeodesicAt nabla hLC
      hgeo hX hY]

/-- **Math.** The pointwise reading on a plane `σ = span(x, y) ⊆ T_pM`: the
sectional numerators computed on the chosen tangent extensions of `x` and `y`
agree for the induced and the ambient connection. -/
theorem inducedCurvatureAt_inner_eq_of_isGeodesicAt
    (hLC : nabla.IsLeviCivita g) {p : M} (hgeo : D.IsGeodesicAt nabla p)
    {x y : TangentSpace I p} (_hx : x ∈ D.tang p) (hy : y ∈ D.tang p) :
    g.metricInner p (D.inducedCurvature nabla (D.tangentExtension p x)
        (D.tangentExtension p y) (D.tangentExtension p x) p) y
      = g.metricInner p (nabla.curvature (D.tangentExtension p x)
        (D.tangentExtension p y) (D.tangentExtension p x) p) y := by
  have h := D.inducedCurvature_inner_eq_curvature_inner_of_isGeodesicAt nabla
    hLC hgeo (D.isTangentField_tangentExtension p x)
    (D.isTangentField_tangentExtension p y)
  rwa [D.tangentExtension_apply_self hy] at h

end DCImmersedPatch

end Riemannian

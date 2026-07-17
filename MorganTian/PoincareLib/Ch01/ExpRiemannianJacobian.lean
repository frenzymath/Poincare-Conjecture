import PoincareLib.Ch01.RiemannianJacobian
import PoincareLib.Ch01.ExpChartDifferentiable
import PoincareLib.Ch01.SegmentInjective

/-!
# Morgan–Tian Ch. 1, §1.4 — the Riemannian Jacobian of `exp_p`

`Ch01/RiemannianJacobian.lean` proves the change-of-variables formula
`riemannianMeasure_image_eq_lintegral_jacobian`:

  `μ_g (φ '' U) = ∫⁻ v in U, ρ(v)`,

for `φ : E → M` continuous, injective on `U`, and carrying a **Riemannian Jacobian** `ρ`
(`HasRiemannianJacobianOn`). To apply it with `φ = exp_p` — the leading gap `(a'1)/(a'3)` of
`thm:bishop-gromov` — one must supply that `ρ` and prove `exp_p` has it. That is this file.

## The canonical density

`HasRiemannianJacobianOn` fixes `ρ(v) = |det D_α| · √(det gᵢⱼ)` at `φ(v)`, read in **any** chart
`α`; the subtlety (spelled out in `RiemannianJacobian`) is that neither factor is chart-independent
but their product is. So the value is unambiguous, and we may *define* `ρ` by reading it in the one
chart that is always available at `exp_p(v)` — namely the preferred chart **at `exp_p(v)` itself**,
whose source always contains its own centre:

  `expRiemannianJacobian g hg p v
     = |det d(x_{exp_p v} ∘ exp_p)_v| · √(det gᵢⱼ(exp_p v))`.

## The proof

`differentiableAt_extChartAt_expMapGlobal` already gives that `exp_p`, read in *every* chart, is
differentiable everywhere on `T_pM` (no conjugate-point or comparison hypothesis: this is a
pure smoothness fact). So the derivative `D_α` in the requested chart `α` exists. Chart-invariance
of the product is then two elementary transformation laws:

* the chain rule through the transition map identifies `D_α = A · D_{ζ}` with
  `A = tangentCoordChange I ζ α (exp_p v)` (`hasFDerivWithinAt_tangentCoordChange`), so
  `|det D_α| = |det A| · |det D_ζ|`;
* the `(0,2)`-tensor law `sqrt_chartGramMatrix_det_change` gives
  `√(det g^α) = |det (tangentCoordChange I α ζ (exp_p v))| · √(det g^ζ)`;

and the two coordinate changes `A` and its opposite are mutually inverse, so
`|det A| · |det (tangentCoordChange I α ζ …)| = 1` and the product is the same in every chart.
No injectivity, no measure theory: this is the pointwise differential-geometric input to the
manifold change of variables, valid on **all** of `T_pM`.

Blueprint: `lem:riemannian-measure-jacobian-global`, `thm:bishop-gromov` (item `(a'1)/(a'3)`).

Reference: Morgan–Tian, *Ricci Flow and the Poincaré Conjecture*, Ch. 1, §1.4.
-/

open MeasureTheory Measure Set Filter Function Metric Riemannian Riemannian.Geodesic Module
open scoped ENNReal NNReal Topology ContDiff Manifold Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PoincareLib

-- Diamond-free model-space block (see `ExpContinuity`): no standalone `[NormedSpace ℝ E]`.
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [SigmaCompactSpace M] [T2Space (TangentBundle I M)] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [Nonempty M]

/-- **Math.** Two tangent coordinate changes at the same base point, in opposite order, are
mutually inverse, so the absolute values of their determinants are reciprocal:
`|det (tangentCoordChange I α β q)| · |det (tangentCoordChange I β α q)| = 1`. -/
theorem abs_det_tangentCoordChange_mul (α β : M) {q : M}
    (hα : q ∈ (chartAt H α).source) (hβ : q ∈ (chartAt H β).source) :
    |LinearMap.det ((tangentCoordChange I α β q : E →L[ℝ] E) : E →ₗ[ℝ] E)|
      * |LinearMap.det ((tangentCoordChange I β α q : E →L[ℝ] E) : E →ₗ[ℝ] E)| = 1 := by
  have hαe : q ∈ (extChartAt I α).source := by rw [extChartAt_source (I := I)]; exact hα
  have hβe : q ∈ (extChartAt I β).source := by rw [extChartAt_source (I := I)]; exact hβ
  have hcomp : (tangentCoordChange I α β q : E →L[ℝ] E).comp
      (tangentCoordChange I β α q : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    rw [tangentCoordChange_comp (I := I) ⟨⟨hβe, hαe⟩, hβe⟩, tangentCoordChange_self (I := I) hβe]
  have hdet : LinearMap.det ((tangentCoordChange I α β q : E →L[ℝ] E) : E →ₗ[ℝ] E)
      * LinearMap.det ((tangentCoordChange I β α q : E →L[ℝ] E) : E →ₗ[ℝ] E) = 1 := by
    rw [← LinearMap.det_comp]
    have : ((tangentCoordChange I α β q : E →L[ℝ] E) : E →ₗ[ℝ] E).comp
        ((tangentCoordChange I β α q : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = (ContinuousLinearMap.id ℝ E : E →ₗ[ℝ] E) := by
      rw [← ContinuousLinearMap.coe_comp, hcomp]
    rw [this]
    simp
  rw [← abs_mul, hdet, abs_one]

/-- **Math.** The **Riemannian Jacobian density of `exp_p`**, read in the preferred chart at
`exp_p(v)`:

  `expRiemannianJacobian g hg p v
     = |det d(x_{exp_p v} ∘ exp_p)_v| · √(det gᵢⱼ(exp_p v))`.

By `hasRiemannianJacobianOn_expMapGlobal` this value is chart-independent, i.e. it is the honest
`|det d(exp_p)_v|` measured against the coordinate volume on `T_pM` and `μ_g` at `exp_p(v)`. It is
the density `BishopGromovBall.expBallVolume` integrates. -/
def expRiemannianJacobian (g : RiemannianMetric I M) (hg : g.IsRiemannianDist) (p : M)
    (v : E) : ℝ :=
  |(fderiv ℝ (fun w : E => extChartAt I (expMapGlobal (I := I) g hg p v)
      (expMapGlobal (I := I) g hg p w)) v).det|
    * chartVolumeDensity (I := I) g (expMapGlobal (I := I) g hg p v)
        (extChartAt I (expMapGlobal (I := I) g hg p v) (expMapGlobal (I := I) g hg p v))

/-- **Math.** **`exp_p` has Riemannian Jacobian `expRiemannianJacobian g hg p` on all of `T_pM`.**

For every set `U` and every chart `α` around `exp_p(v)`, the map `exp_p` read in `α` is
differentiable at `v` and `expRiemannianJacobian g hg p v = |det D_α| · √(det gᵢⱼ(exp_p v))`. This
is exactly the hypothesis `riemannianMeasure_image_eq_lintegral_jacobian` needs, so with
`U = segmentDomain ∩ B(0,r)` (where `exp_p` is injective) it yields
`μ_g (exp_p '' U) = ∫⁻_U expRiemannianJacobian` — the polar-integral half of `thm:bishop-gromov`.

Blueprint: `lem:riemannian-measure-jacobian-global`. -/
theorem hasRiemannianJacobianOn_expMapGlobal (g : RiemannianMetric I M) (hg : g.IsRiemannianDist)
    (p : M) (U : Set E) :
    HasRiemannianJacobianOn (I := I) g (expMapGlobal (I := I) g hg p) U
      (expRiemannianJacobian (I := I) g hg p) := by
  classical
  intro α v _hvU hα
  set q : M := expMapGlobal (I := I) g hg p v with hqdef
  -- the reference chart: the preferred chart at `q = exp_p v`, always containing `q`
  set ζ : M := q with hζdef
  have hζsrc : q ∈ (extChartAt I ζ).source := mem_extChartAt_source (I := I) ζ
  -- both chart sources, as `chartAt` sources (needed by the Gram-determinant law)
  have hα' : q ∈ (chartAt H α).source := by rw [← extChartAt_source (I := I)]; exact hα
  have hζ' : q ∈ (chartAt H ζ).source := mem_chart_source H ζ
  -- `D₀`: the derivative of `exp_p` read in the reference chart `ζ`
  set D₀ : E →L[ℝ] E := fderiv ℝ (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) v
    with hD₀def
  have hD₀ : HasFDerivAt (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) D₀ v :=
    (differentiableAt_extChartAt_expMapGlobal (I := I) g hg p ζ hζsrc).hasFDerivAt
  -- the transition `x_α ∘ x_ζ⁻¹` is differentiable at the `ζ`-coordinates of `q`, with
  -- derivative `A = tangentCoordChange I ζ α q`
  set A : E →L[ℝ] E := tangentCoordChange I ζ α q with hAdef
  have hτ : HasFDerivAt ((extChartAt I α) ∘ (extChartAt I ζ).symm) A (extChartAt I ζ q) := by
    have hd := hasFDerivWithinAt_tangentCoordChange (I := I) (x := ζ) (y := α) (z := q)
      ⟨hζsrc, hα⟩
    rw [I.range_eq_univ] at hd
    exact hasFDerivWithinAt_univ.mp hd
  -- the requested derivative of `exp_p` in the chart `α`
  set D : E →L[ℝ] E := A.comp D₀ with hDdef
  have hcomp : HasFDerivAt
      ((extChartAt I α) ∘ (extChartAt I ζ).symm ∘ (fun w : E => extChartAt I ζ
        (expMapGlobal (I := I) g hg p w))) D v := by
    have hval : (fun w : E => extChartAt I ζ (expMapGlobal (I := I) g hg p w)) v
        = extChartAt I ζ q := rfl
    exact (hval ▸ hτ).comp v hD₀
  -- near `v` this composite is the chart-`α` reading of `exp_p`
  have hev : (fun w : E => extChartAt I α (expMapGlobal (I := I) g hg p w))
      =ᶠ[𝓝 v] ((extChartAt I α) ∘ (extChartAt I ζ).symm ∘ (fun w : E => extChartAt I ζ
        (expMapGlobal (I := I) g hg p w))) := by
    have hopen : IsOpen {w : E | expMapGlobal (I := I) g hg p w ∈ (extChartAt I ζ).source} :=
      (isOpen_extChartAt_source (I := I) ζ).preimage (continuous_expMapGlobal (I := I) g hg p)
    have hmem : v ∈ {w : E | expMapGlobal (I := I) g hg p w ∈ (extChartAt I ζ).source} := hζsrc
    refine Filter.eventuallyEq_of_mem (hopen.mem_nhds hmem) fun w hw => ?_
    simp only [Function.comp_apply]
    rw [(extChartAt I ζ).left_inv hw]
  have hD : HasFDerivAt (fun w : E => extChartAt I α (expMapGlobal (I := I) g hg p w)) D v :=
    hcomp.congr_of_eventuallyEq hev
  refine ⟨D, hD.hasFDerivWithinAt, ?_⟩
  -- the determinant/density identity, chart-invariance in one direction
  -- `chartVolumeDensity` at coordinates of `q` is `√(det g_{ij}(q))`
  have hcvd_ζ : chartVolumeDensity (I := I) g ζ (extChartAt I ζ q)
      = Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g ζ q).det) := by
    rw [chartVolumeDensity, (extChartAt I ζ).left_inv hζsrc]
  have hcvd_α : chartVolumeDensity (I := I) g α (extChartAt I α q)
      = Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g α q).det) := by
    rw [chartVolumeDensity, (extChartAt I α).left_inv hα]
  -- Gram-determinant law: `√(det g^α) = |det (tcc I α ζ q)| · √(det g^ζ)`
  have hgram : Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g α q).det)
      = |LinearMap.det ((tangentCoordChange I α ζ q : E →L[ℝ] E) : E →ₗ[ℝ] E)|
          * Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g ζ q).det) :=
    sqrt_chartGramMatrix_det_change (I := I) g ζ α hζ' hα'
  -- `|det D| = |det A| · |det D₀|`
  have hdetD : |D.det| = |LinearMap.det ((A : E →L[ℝ] E) : E →ₗ[ℝ] E)| * |D₀.det| := by
    show |LinearMap.det ((D : E →L[ℝ] E) : E →ₗ[ℝ] E)| = _
    rw [hDdef]
    rw [show ((A.comp D₀ : E →L[ℝ] E) : E →ₗ[ℝ] E)
        = ((A : E →L[ℝ] E) : E →ₗ[ℝ] E).comp ((D₀ : E →L[ℝ] E) : E →ₗ[ℝ] E) from
      ContinuousLinearMap.coe_comp A D₀, LinearMap.det_comp, abs_mul]
  -- the reciprocal-determinant cancellation
  have hcancel : |LinearMap.det ((A : E →L[ℝ] E) : E →ₗ[ℝ] E)|
      * |LinearMap.det ((tangentCoordChange I α ζ q : E →L[ℝ] E) : E →ₗ[ℝ] E)| = 1 :=
    abs_det_tangentCoordChange_mul (I := I) ζ α hζ' hα'
  -- assemble
  show expRiemannianJacobian (I := I) g hg p v = |D.det| * chartVolumeDensity (I := I) g α
      (extChartAt I α q)
  rw [expRiemannianJacobian, ← hqdef, ← hζdef, ← hD₀def, hcvd_ζ, hcvd_α, hgram, hdetD]
  rw [show |LinearMap.det ((A : E →L[ℝ] E) : E →ₗ[ℝ] E)| * |D₀.det|
      * (|LinearMap.det ((tangentCoordChange I α ζ q : E →L[ℝ] E) : E →ₗ[ℝ] E)|
        * Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g ζ q).det))
      = (|LinearMap.det ((A : E →L[ℝ] E) : E →ₗ[ℝ] E)|
          * |LinearMap.det ((tangentCoordChange I α ζ q : E →L[ℝ] E) : E →ₗ[ℝ] E)|)
        * (|D₀.det| * Real.sqrt ((Riemannian.Tensor.chartGramMatrix (I := I) g ζ q).det)) by ring,
    hcancel, one_mul]

variable (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Math.** **Change of variables for `exp_p` on the segment domain.** For any measurable
`U ⊆ U_p` (the segment domain, where `exp_p` is injective), the Riemannian measure of the image
is the integral of the Jacobian:

  `μ_g (exp_p '' U) = ∫⁻ v in U, expRiemannianJacobian g hg p v`.

This assembles the keystone `hasRiemannianJacobianOn_expMapGlobal` with the injectivity of `exp_p`
on `U_p` (`injOn_expMapGlobal_segmentDomain`) and the general manifold change of variables
`riemannianMeasure_image_eq_lintegral_jacobian`. It is the polar-integral identity `(a')` that
`thm:bishop-gromov` needs, before the cut locus (a null set) is added back.

Blueprint: `thm:bishop-gromov` (item `(a')`). -/
theorem riemannianMeasure_image_segmentDomain_eq_lintegral (g : RiemannianMetric I M)
    (hg : g.IsRiemannianDist) (p : M) {U : Set E} (hU : MeasurableSet U)
    (hUsub : U ⊆ segmentDomain (I := I) g hg p) :
    riemannianMeasure (I := I) g μ (expMapGlobal (I := I) g hg p '' U)
      = ∫⁻ v in U, ENNReal.ofReal (expRiemannianJacobian (I := I) g hg p v) ∂μ :=
  riemannianMeasure_image_eq_lintegral_jacobian μ g hU
    (continuous_expMapGlobal (I := I) g hg p)
    ((injOn_expMapGlobal_segmentDomain (I := I) g hg p).mono hUsub)
    (hasRiemannianJacobianOn_expMapGlobal (I := I) g hg p U)

end PoincareLib

end

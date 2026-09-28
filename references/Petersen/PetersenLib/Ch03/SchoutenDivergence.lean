import PetersenLib.Ch03.Exercises
import PetersenLib.Ch03.ScalarFormulas
import PetersenLib.Ch03.RicciSectional

/-!
# Petersen Ch. 3, §3.4 — Exercise 3.4.26: the divergence of the Schouten tensor

Petersen §3.4, Exercise 3.4.26 (first identity): the divergence adjoint of the
Schouten tensor `P` is `∇*P = −1/(n−1)·d(scal)`.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

section Bridges

/-- Bridge: the abstract Ricci contraction of the pointwise curvature form is
minus the manifold Ricci tensor (the abstract layer uses the do Carmo
curvature-sign convention, flipped from Petersen's). -/
private theorem ricciForm_curvatureTensorFourAt_eq (D : RiemannianConnection I g)
    (p : M) (v w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩;
    ricciForm (isAlgCurvatureForm_curvatureTensorFourAt D p) v w
      = -RicciCurvature D.toAffineConnection p v w := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace I p) with hb
  have hbo : ∀ i j, g.metricInner p (b.toBasis i) (b.toBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    rw [OrthonormalBasis.coe_toBasis]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  rw [ricciForm_eq_sum _ v w b, ricciCurvature_eq_sum D p b.toBasis hbo v w,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [OrthonormalBasis.coe_toBasis]
  have h := (isAlgCurvatureForm_curvatureTensorFourAt D p).antisymm₁₂ (b i) v w (b i)
  linarith

/-- Bridge: the abstract scalar contraction of the pointwise curvature form is
minus the manifold scalar curvature. -/
private theorem algScalarCurvature_curvatureTensorFourAt_eq
    (D : RiemannianConnection I g) (p : M) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩;
    algScalarCurvature (isAlgCurvatureForm_curvatureTensorFourAt D p)
      = -scalarCurvature D p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace I p) with hb
  have hbo : ∀ i j, g.metricInner p (b.toBasis i) (b.toBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    rw [OrthonormalBasis.coe_toBasis]
    exact orthonormal_iff_ite.mp b.orthonormal i j
  rw [algScalarCurvature_eq_sum_ricci _ b,
    scalarCurvature_eq_sum_ricci D p b.toBasis hbo, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ricciForm_curvatureTensorFourAt_eq D p (b i) (b i), OrthonormalBasis.coe_toBasis]

end Bridges

/-- **Math.** Petersen §3.4, Exercise 3.4.26 (first identity): the **divergence
adjoint of the Schouten tensor** `P` is proportional to `d(scal)`.

Petersen's identity reads `∇*P = −1/(n−1)·d(scal)`, where `P = 2/(n−2)·Ric −
scal/((n−1)(n−2))·g` is the Schouten tensor (Exercise 3.4.24). Here the Schouten
tensor is expressed through the abstract-layer `schoutenForm` of the pointwise
curvature form `curvatureTensorFourAt`, which — like the abstract `ricciForm`
and `algScalarCurvature` — carries the *do Carmo* curvature-sign convention,
opposite to the manifold-level `RicciCurvature`/`scalarCurvature` (`ricciForm =
−Ric`, `algScalarCurvature = −scal`; cf. `weylForm`). Consequently
`schoutenForm (curvatureTensorFourAt) = −P`, so Petersen's `∇*P = −1/(n−1)·d(scal)`
becomes here `∇*(schoutenForm) = +1/(n−1)·d(scal)`.

Only the Schouten (first) identity is formalized; the Weyl-divergence second
identity requires covariant-divergence infrastructure for a general `(0,4)`-tensor
field, which does not yet exist. -/
theorem exercise3_4_26 (D : RiemannianConnection I g)
    (hn : 2 < Module.finrank ℝ E) (p : M) (w : TangentSpace I p) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩;
    divergenceAdjoint D
        (fun q x y => schoutenForm (isAlgCurvatureForm_curvatureTensorFourAt D q) x y)
        p w
      = (1 / ((Module.finrank ℝ E : ℝ) - 1)) * dirTangent (scalarCurvature D) w := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn_def
  have hn2R : (2 : ℝ) < n := by rw [hn_def]; exact_mod_cast hn
  have hne2 : n - 2 ≠ 0 := by linarith
  have hne1 : n - 1 ≠ 0 := by linarith
  set c2 : ℝ := (n - 1) * (n - 2) with hc2_def
  set a : ℝ := -(2 / (n - 2)) with ha_def
  -- the manifold Schouten field, `= schoutenForm` after the sign bridges
  set S : Π q : M, TangentSpace I q → TangentSpace I q → ℝ :=
    fun q x y => a * RicciCurvature D.toAffineConnection q x y
      + (c2⁻¹ * scalarCurvature D q) * g.metricInner q x y with hS_def
  set φ : M → ℝ := fun q => c2⁻¹ * scalarCurvature D q with hφ_def
  have hφsm : ContMDiff I 𝓘(ℝ) ∞ φ :=
    contMDiff_const.mul (contMDiff_scalarCurvature D)
  -- Step 0: identify the Schouten field with `S`
  have hSeq : (fun q x y =>
        schoutenForm (isAlgCurvatureForm_curvatureTensorFourAt D q) x y) = S := by
    funext q x y
    rw [hS_def]
    simp only [schoutenForm, ricciForm_curvatureTensorFourAt_eq D q x y,
      algScalarCurvature_curvatureTensorFourAt_eq D q]
    have hxy : (inner ℝ x y : ℝ) = g.metricInner q x y := rfl
    have hfr : Module.finrank ℝ (TangentSpace I q) = Module.finrank ℝ E := rfl
    rw [hxy, hfr, ← hn_def, ha_def, hc2_def]
    field_simp
    ring
  rw [hSeq]
  -- the frame orthonormal at `p`
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  have horthe : ∀ i j, g.metricInner p (e i) (e j) = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  set W : Π x : M, TangentSpace I x := ⇑(extendTangentVector p w) with hWdef
  have hW : IsSmoothVectorField W := (extendTangentVector p w).smooth
  have hWp : W p = w := extendTangentVector_apply p w
  -- Step 1: per-frame decomposition of the covariant derivative of `S`
  have hterm : ∀ i, covariantDerivativeTwoTensorAt D.toAffineConnection S p
        (e i) (e i) w
      = a * covariantDerivativeTwoTensorAt D.toAffineConnection
          (fun q => RicciCurvature D.toAffineConnection q) p (e i) (e i) w
        + g.metricInner p (e i) w * dirTangent φ (e i) := by
    intro i
    set Fi : Π x : M, TangentSpace I x := ⇑(extendTangentVector p (e i))
      with hFidef
    have hFi : IsSmoothVectorField Fi := (extendTangentVector p (e i)).smooth
    have hFip : Fi p = e i := extendTangentVector_apply p (e i)
    set Rfun : M → ℝ :=
      fun q => RicciCurvature D.toAffineConnection q (Fi q) (W q) with hRfun_def
    set Gfun : M → ℝ := fun q => g.metricInner q (Fi q) (W q) with hGfun_def
    have hRsm : ContMDiff I 𝓘(ℝ) ∞ Rfun :=
      contMDiff_ricciCurvature_eval D hFi hW
    have hGsm : ContMDiff I 𝓘(ℝ) ∞ Gfun := by
      have h := (metricOperator_isTensorOperator g).smooth_eval ![Fi, W]
        (by
          intro k
          fin_cases k
          · simpa using hFi
          · simpa using hW)
      have e' : (metricOperator g ![Fi, W] : M → ℝ)
          = fun q => g.metricInner q (Fi q) (W q) := by
        funext q
        simp [metricOperator]
      rwa [e'] at h
    -- differentiabilities at `p`
    have hRd : MDifferentiableAt I 𝓘(ℝ) (fun q => a * Rfun q) p :=
      (contMDiff_const.mul hRsm).mdifferentiableAt (by simp)
    have hPGd : MDifferentiableAt I 𝓘(ℝ) (fun q => φ q * Gfun q) p :=
      (hφsm.mul hGsm).mdifferentiableAt (by simp)
    -- directional derivative of the evaluated `S`
    have hdirS : directionalDerivative Fi (fun q => a * Rfun q + φ q * Gfun q) p
        = a * directionalDerivative Fi Rfun p
          + (φ p * directionalDerivative Fi Gfun p
              + Gfun p * directionalDerivative Fi φ p) := by
      have hsplit : (fun q => a * Rfun q + φ q * Gfun q)
          = (fun q => a * Rfun q) + (fun q => φ q * Gfun q) := rfl
      have hcs : directionalDerivative Fi (fun q => a * Rfun q) p
          = a * directionalDerivative Fi Rfun p :=
        directionalDerivative_const_smul (hRsm.mdifferentiableAt (by simp)) a Fi
      have hmul : directionalDerivative Fi (fun q => φ q * Gfun q) p
          = φ p * directionalDerivative Fi Gfun p
            + Gfun p * directionalDerivative Fi φ p :=
        directionalDerivative_mul (hφsm.mdifferentiableAt (by simp))
          (hGsm.mdifferentiableAt (by simp)) Fi
      rw [hsplit, directionalDerivative_add hRd hPGd Fi, hcs, hmul]
    -- metric compatibility on `Gfun`
    have hcompat : directionalDerivative Fi Gfun p
        = g.metricInner p (D.cov p (Fi p) Fi) (W p)
          + g.metricInner p (Fi p) (D.cov p (Fi p) W) := by
      have h := D.metric_compat hFi hW p (Fi p)
      rw [dirTangent_eq_directionalDerivative] at h
      exact h
    -- assemble both covariant derivatives
    rw [covariantDerivativeTwoTensorAt, covariantDerivativeTwoTensorAt]
    -- rewrite the `dirTangent`s through `Fi`-directional derivatives
    have hdtS : dirTangent (fun q => S q (Fi q) (W q)) (e i)
        = directionalDerivative Fi (fun q => a * Rfun q + φ q * Gfun q) p := by
      rw [← hFip]; rfl
    have hdtR : dirTangent (fun q => RicciCurvature D.toAffineConnection q
          (Fi q) (W q)) (e i)
        = directionalDerivative Fi Rfun p := by
      rw [← hFip]; rfl
    have hdtφ : dirTangent φ (e i) = directionalDerivative Fi φ p := by
      rw [← hFip]; rfl
    -- the `S`-evaluations of the extended frame reduce to explicit terms
    have hSval : ∀ u v : TangentSpace I p,
        S p u v = a * RicciCurvature D.toAffineConnection p u v
          + φ p * g.metricInner p u v := fun u v => rfl
    rw [hdtS, hdirS, hSval, hSval, hdtR, hcompat, hFip, hWp, hdtφ]
    simp only [hGfun_def, hFip, hWp]
    ring
  -- Step 2: sum over the frame → `a·∇*Ric − dφ(w)` shape
  have hsum : divergenceAdjoint D S p w
      = a * divergenceAdjoint D (fun q => RicciCurvature D.toAffineConnection q) p w
        - dirTangent φ w := by
    rw [divergenceAdjoint, divergenceAdjoint, ← he]
    -- `∑ᵢ g(eᵢ,w)·dφ(eᵢ) = dφ(w)`
    obtain ⟨b, hbcoe⟩ := exists_orthonormalBasis_of_family p
      (v := fun i : Fin (Module.finrank ℝ E) => e i) horthe
    have hb : ∀ i, b i = e i := fun i => congrFun hbcoe i
    have hbo : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
      intro i j
      rw [hb i, hb j]; exact horthe i j
    have hwexp : w = ∑ i, g.metricInner p w (e i) • e i := by
      conv_lhs => rw [← b.sum_repr w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [orthonormal_basis_repr_eq_metricInner p b hbo, hb i]
    have hdfw : dirTangent φ w
        = ∑ i, g.metricInner p w (e i) * dirTangent φ (e i) := by
      conv_lhs => rw [hwexp]
      show (mfderiv I 𝓘(ℝ) φ p) (∑ i, g.metricInner p w (e i) • e i) = _
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
    have hgsum : ∑ i, g.metricInner p (e i) w * dirTangent φ (e i)
        = dirTangent φ w := by
      rw [hdfw]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [g.metricInner_comm p (e i) w]
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
      ← Finset.mul_sum, hgsum]
    ring
  -- Step 3: contracted Bianchi + the scalar-curvature differential
  rw [hsum]
  have hCB := contractedBianchiIdentity D p w
  have hRdiv : divergenceAdjoint D
        (fun q => RicciCurvature D.toAffineConnection q) p w
      = -(1 / 2) * dirTangent (scalarCurvature D) w := by
    rw [hCB]; ring
  have hdφw : dirTangent φ w = c2⁻¹ * dirTangent (scalarCurvature D) w := by
    set W' : Π x : M, TangentSpace I x := ⇑(extendTangentVector p w) with hW'def
    have hW'p : W' p = w := extendTangentVector_apply p w
    have h1 : dirTangent φ w = directionalDerivative W' φ p := by rw [← hW'p]; rfl
    have h2 : dirTangent (scalarCurvature D) w
        = directionalDerivative W' (scalarCurvature D) p := by rw [← hW'p]; rfl
    rw [h1, h2, hφ_def]
    exact directionalDerivative_const_smul
      ((contMDiff_scalarCurvature D p).mdifferentiableAt (by simp)) _ W'
  rw [hRdiv, hdφw, ha_def, hc2_def]
  field_simp
  ring

end PetersenLib

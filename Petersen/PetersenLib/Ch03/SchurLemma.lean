import PetersenLib.Ch03.ContractedBianchi
import PetersenLib.Ch03.ConstantOfZeroDifferential
import PetersenLib.Ch03.RiemannConstantCurvature
import PetersenLib.Ch03.ScalarFormulas

/-!
# Petersen Ch. 3, §3.1.5 — Schur's lemma and the Einstein characterization

**Lemma 3.1.4 (Schur, 1886)** (`schurLemma`): if `dim M = n ≥ 3` and, for a
function `f : M → ℝ`, either (1) `sec(π) = f(p)` for every 2-plane
`π ⊂ T_pM`, or (2) `Ric = (n−1)·f·g` pointwise, then `f` is constant, and the
metric has constant curvature, respectively is Einstein.

**Corollary 3.1.6** (`einstein_iff_ricci_eq_scal_div_n_metric`): an
`n(>2)`-dimensional Riemannian manifold is Einstein iff
`Ric = (scal/n)·g`.

## Proof

By the contracted Bianchi identity: hypothesis (2) forces
`∇*Ric = −(n−1)·df` and `scal = n(n−1)·f`, so
`n(n−1)·df = d(scal) = −2·∇*Ric = 2(n−1)·df`, whence `(n−1)(n−2)·df = 0` and
`df ≡ 0`; on a connected manifold `f` is then constant
(`apply_eq_of_mfderiv_eq_zero`). Hypothesis (1) reduces to (2) by the
pointwise Riemann argument (`ricciCurvature_eq_of_pointwise_constant_sec`,
the pointwise form of `constantCurvature_isEinstein`).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.5.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

open Riemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]
  {g : RiemannianMetric I M}

/-! ## Pointwise Riemann: constant sectional curvature at `p` forces
`Ric = (n−1)·c·g` at `p` -/

/-- The pointwise form of `constantCurvature_isEinstein`: if every 2-plane at
the single point `p` has sectional curvature `c`, then
`Ric_p = (n−1)·c·g_p`. -/
theorem ricciCurvature_eq_of_pointwise_constant_sec
    (D : RiemannianConnection I g) (p : M) {c : ℝ}
    (h : ∀ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] →
      sectionalCurvature D p v w = c) (v w : TangentSpace I p) :
    RicciCurvature D.toAffineConnection p v w
      = ((Module.finrank ℝ E : ℝ) - 1) * c * g.metricInner p v w := by
  classical
  have halg := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hG : ∀ a b : TangentSpace I p,
      g.metricBilin p a b = g.metricBilin p b a :=
    fun a b => g.metricInner_comm p a b
  have hpair := isAlgCurvatureForm_bivectorPairing (g.metricBilin p) hG
  -- Step 1: the diagonal identity for all pairs
  have hdiag : ∀ x y : TangentSpace I p, curvatureTensorFourAt D p x y x y
      = -c * bivectorPairing (g.metricBilin p) x y x y := by
    intro x y
    by_cases hxy : LinearIndependent ℝ ![y, x]
    · have hsec := h y x hxy
      rw [sectionalCurvature_eq_curvatureTensorFourAt] at hsec
      have hpos : 0 < bivectorInnerProduct g p y x y x :=
        bivectorInnerProduct_self_pos g p hxy
      rw [div_eq_iff hpos.ne'] at hsec
      have h34 : curvatureTensorFourAt D p x y x y
          = -curvatureTensorFourAt D p x y y x := halg.antisymm₃₄ x y x y
      rw [h34, hsec, bivectorInnerProduct_eq_bivectorPairing]
      simp only [bivectorPairing, RiemannianMetric.metricBilin_apply]
      ring
    · have hxy' : ¬LinearIndependent ℝ ![x, y] := fun hLI =>
        hxy (LinearIndependent.pair_symm_iff.mp hLI)
      have hL : curvatureTensorFourAt D p x y x y = 0 :=
        halg.diag_eq_zero_of_not_linearIndependent hxy'
      have hR : bivectorPairing (g.metricBilin p) x y x y = 0 :=
        hpair.diag_eq_zero_of_not_linearIndependent hxy'
      rw [hL, hR, mul_zero]
  -- Step 2: upgrade to the full tensor identity
  have hfull := halg.eq_smul_bivectorPairing_of_const (g.metricBilin p) hG
    (-c) hdiag
  -- Step 3: trace in a `g`-orthonormal basis
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace I p) with hbdef
  have hb : ∀ i j, g.metricInner p (b.toBasis i) (b.toBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp b.orthonormal i j
    rw [OrthonormalBasis.coe_toBasis]
    exact h1
  rw [ricciCurvature_eq_sum D p b.toBasis hb v w]
  have hsum : ∑ i, curvatureTensorFourAt D p (b.toBasis i) v w (b.toBasis i)
      = ∑ i, -c * (g.metricInner p v (b.toBasis i)
          * g.metricInner p (b.toBasis i) w - g.metricInner p v w) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hf : curvatureTensorFourAt D p (b.toBasis i) v w (b.toBasis i)
        = -c * bivectorPairing (g.metricBilin p) (b.toBasis i) v w
            (b.toBasis i) := hfull _ v w _
    have hbii : g.metricInner p (b.toBasis i) (b.toBasis i) = 1 := by
      rw [hb i i, if_pos rfl]
    rw [hf]
    simp only [bivectorPairing, RiemannianMetric.metricBilin_apply, hbii]
    ring
  rw [hsum, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← metricInner_eq_sum_mul p b.toBasis hb v w, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  have hfr : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
  rw [hfr]
  ring

/-! ## The scalar curvature and divergence adjoint of a pointwise-Einstein
metric -/

section PointwiseEinstein

variable (D : RiemannianConnection I g) {f : M → ℝ}

/-- Under `Ric = (n−1)·f·g`, the scalar curvature is `n(n−1)·f`. -/
theorem scalarCurvature_of_ricci_eq (hric : ∀ (p : M) (v w : TangentSpace I p),
    RicciCurvature D.toAffineConnection p v w
      = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w) (p : M) :
    scalarCurvature D p
      = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) * f p := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set b := stdOrthonormalBasis ℝ (TangentSpace I p) with hbdef
  have hb : ∀ i j, g.metricInner p (b.toBasis i) (b.toBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp b.orthonormal i j
    rw [OrthonormalBasis.coe_toBasis]
    exact h1
  rw [scalarCurvature_eq_sum_ricci D p b.toBasis hb]
  have hterm : ∀ i, RicciCurvature D.toAffineConnection p (b.toBasis i)
        (b.toBasis i)
      = ((Module.finrank ℝ E : ℝ) - 1) * f p := by
    intro i
    rw [hric p (b.toBasis i) (b.toBasis i), hb i i, if_pos rfl, mul_one]
  rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, Fintype.card_fin]
  have hfr : Module.finrank ℝ (TangentSpace I p) = Module.finrank ℝ E := rfl
  rw [hfr]
  ring

/-- Under `Ric = (n−1)·f·g` (with `f` differentiable), the divergence adjoint
of the Ricci tensor is `−(n−1)·df`. -/
theorem divergenceAdjoint_ricci_of_ricci_eq
    (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hric : ∀ (p : M) (v w : TangentSpace I p),
      RicciCurvature D.toAffineConnection p v w
        = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w)
    (p : M) (w : TangentSpace I p) :
    divergenceAdjoint D (fun q => RicciCurvature D.toAffineConnection q) p w
      = -(((Module.finrank ℝ E : ℝ) - 1) * dirTangent f w) := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  have horthe : ∀ i j, g.metricInner p (e i) (e j) = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  set W : Π x : M, TangentSpace I x := ⇑(extendTangentVector p w) with hWdef
  have hW : IsSmoothVectorField W := (extendTangentVector p w).smooth
  have hWp : W p = w := extendTangentVector_apply p w
  -- each frame term reduces to `(n−1)·df(eᵢ)·g(eᵢ,w)`
  have hterm : ∀ i, covariantDerivativeTwoTensorAt D.toAffineConnection
        (fun q => RicciCurvature D.toAffineConnection q) p (e i) (e i) w
      = ((Module.finrank ℝ E : ℝ) - 1) * dirTangent f (e i)
          * g.metricInner p (e i) w := by
    intro i
    set Fi : Π x : M, TangentSpace I x := ⇑(extendTangentVector p (e i))
      with hFidef
    have hFi : IsSmoothVectorField Fi := (extendTangentVector p (e i)).smooth
    have hFip : Fi p = e i := extendTangentVector_apply p (e i)
    -- rewrite the evaluated Ricci function through the hypothesis
    have hfun : (fun q => RicciCurvature D.toAffineConnection q (Fi q) (W q))
        = fun q => (((Module.finrank ℝ E : ℝ) - 1) * f q)
            * g.metricInner q (Fi q) (W q) := by
      funext q
      rw [hric q (Fi q) (W q)]
    -- the directional derivative of the product
    have hgsm : ContMDiff I 𝓘(ℝ) ∞ (fun q => g.metricInner q (Fi q) (W q)) := by
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
    have hcf : ContMDiff I 𝓘(ℝ) ∞
        (fun q => ((Module.finrank ℝ E : ℝ) - 1) * f q) :=
      contMDiff_const.mul hf
    have hdirprod : directionalDerivative Fi
          (fun q => (((Module.finrank ℝ E : ℝ) - 1) * f q)
            * g.metricInner q (Fi q) (W q)) p
        = (((Module.finrank ℝ E : ℝ) - 1) * f p)
            * directionalDerivative Fi
                (fun q => g.metricInner q (Fi q) (W q)) p
          + g.metricInner p (Fi p) (W p)
            * directionalDerivative Fi
                (fun q => ((Module.finrank ℝ E : ℝ) - 1) * f q) p :=
      directionalDerivative_mul ((hcf p).mdifferentiableAt (by simp))
        ((hgsm p).mdifferentiableAt (by simp)) Fi
    have hdirconst : directionalDerivative Fi
          (fun q => ((Module.finrank ℝ E : ℝ) - 1) * f q) p
        = ((Module.finrank ℝ E : ℝ) - 1) * directionalDerivative Fi f p :=
      directionalDerivative_const_smul ((hf p).mdifferentiableAt (by simp))
        _ Fi
    -- metric compatibility for the metric factor
    have hcompat : directionalDerivative Fi
          (fun q => g.metricInner q (Fi q) (W q)) p
        = g.metricInner p (D.cov p (Fi p) Fi) (W p)
          + g.metricInner p (Fi p) (D.cov p (Fi p) W) := by
      have h := D.metric_compat hFi hW p (Fi p)
      rw [dirTangent_eq_directionalDerivative] at h
      exact h
    -- assemble
    rw [covariantDerivativeTwoTensorAt]
    have hdt : dirTangent (fun q => RicciCurvature D.toAffineConnection q
          (Fi q) (W q)) (e i)
        = directionalDerivative Fi
            (fun q => RicciCurvature D.toAffineConnection q (Fi q) (W q)) p := by
      rw [← hFip]
      rfl
    have hdtf : dirTangent f (e i) = directionalDerivative Fi f p := by
      rw [← hFip]
      rfl
    rw [hdt, hfun, hdirprod, hdirconst, hcompat,
      hric p (D.cov p (e i) (⇑(extendTangentVector p (e i)))) w,
      hric p (e i) (D.cov p (e i) (⇑(extendTangentVector p w)))]
    have hcov1 : D.cov p (Fi p) Fi
        = D.cov p (e i) (⇑(extendTangentVector p (e i))) := by
      rw [hFip]
    have hcov2 : D.cov p (Fi p) W
        = D.cov p (e i) (⇑(extendTangentVector p w)) := by
      rw [hFip]
    rw [← hcov1, ← hcov2, hFip, hWp, hdtf]
    ring
  -- sum and expand `w` in the orthonormal basis
  rw [divergenceAdjoint, Finset.sum_congr rfl fun i _ => hterm i]
  -- `df(w) = ∑ᵢ g(w,eᵢ)·df(eᵢ)`
  have horthe' : ∀ i j : Fin (Module.finrank ℝ E),
      g.metricInner p (e i) (e j) = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp e.orthonormal i j
  obtain ⟨b, hbcoe⟩ := exists_orthonormalBasis_of_family p
    (v := fun i : Fin (Module.finrank ℝ E) => e i) horthe'
  have hb : ∀ i, b i = e i := fun i => congrFun hbcoe i
  have hbo : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hb i, hb j]
    exact horthe' i j
  have hwexp : w = ∑ i, g.metricInner p w (e i) • e i := by
    conv_lhs => rw [← b.sum_repr w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [orthonormal_basis_repr_eq_metricInner p b hbo, hb i]
  have hdfw : dirTangent f w
      = ∑ i, g.metricInner p w (e i) * dirTangent f (e i) := by
    conv_lhs => rw [hwexp]
    show (mfderiv I 𝓘(ℝ) f p) (∑ i, g.metricInner p w (e i) • e i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [map_smul]
      rfl
  rw [hdfw, Finset.mul_sum, neg_inj]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [g.metricInner_comm p (e i) w]
  ring

end PointwiseEinstein

/-! ## Lemma 3.1.4 — Schur's lemma -/

/-- The analytic core of Schur's lemma: if `Ric = (n−1)·f·g` with `n ≥ 3`,
then `f` has vanishing differential everywhere. -/
theorem mfderiv_eq_zero_of_ricci_eq (D : RiemannianConnection I g)
    (hn : 3 ≤ Module.finrank ℝ E) {f : M → ℝ}
    (hric : ∀ (p : M) (v w : TangentSpace I p),
      RicciCurvature D.toAffineConnection p v w
        = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w)
    (p : M) : mfderiv I 𝓘(ℝ) f p = 0 := by
  classical
  have hn3 : (3 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn
  have hne : (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 :=
    by nlinarith
  -- `f` is smooth, being a constant multiple of the scalar curvature
  have hn1 : (Module.finrank ℝ E : ℝ) - 1 ≠ 0 := by nlinarith
  have hf : ContMDiff I 𝓘(ℝ) ∞ f := by
    have hfe : f = fun q => ((Module.finrank ℝ E : ℝ)
        * ((Module.finrank ℝ E : ℝ) - 1))⁻¹ * scalarCurvature D q := by
      funext q
      rw [scalarCurvature_of_ricci_eq D hric q]
      field_simp
    rw [hfe]
    exact contMDiff_const.mul (contMDiff_scalarCurvature D)
  -- `d(scal) = n(n−1)·df`
  have hdscal : ∀ w : TangentSpace I p, dirTangent (scalarCurvature D) w
      = (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)
        * dirTangent f w := by
    intro w
    have hfun : scalarCurvature D = fun q => (Module.finrank ℝ E : ℝ)
        * ((Module.finrank ℝ E : ℝ) - 1) * f q := by
      funext q
      rw [scalarCurvature_of_ricci_eq D hric q]
    set W : Π x : M, TangentSpace I x := ⇑(extendTangentVector p w) with hWdef
    have hWp : W p = w := extendTangentVector_apply p w
    have h1 : dirTangent (scalarCurvature D) w
        = directionalDerivative W (scalarCurvature D) p := by
      rw [← hWp]
      rfl
    have h2 : dirTangent f w = directionalDerivative W f p := by
      rw [← hWp]
      rfl
    rw [h1, h2, hfun]
    exact directionalDerivative_const_smul ((hf p).mdifferentiableAt (by simp))
      _ W
  -- contracted Bianchi forces `(n−1)(n−2)·df = 0`
  have hdf0 : ∀ w : TangentSpace I p, dirTangent f w = 0 := by
    intro w
    have hcb := contractedBianchiIdentity D p w
    rw [hdscal w, divergenceAdjoint_ricci_of_ricci_eq D hf hric p w] at hcb
    have hfac : ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)
          - 2 * ((Module.finrank ℝ E : ℝ) - 1)) * dirTangent f w = 0 := by
      linear_combination hcb
    have hcoef : (Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)
        - 2 * ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by nlinarith
    exact (mul_eq_zero.mp hfac).resolve_left hcoef
  ext w
  exact hdf0 w

/-- **Math.** **Lemma 3.1.4 (Schur, 1886)** (Petersen §3.1.5): let `(M,g)` be
connected of dimension `n ≥ 3` and `f : M → ℝ`. If either

1. `sec(π) = f(p)` for all 2-planes `π ⊂ T_pM` and all `p`, or
2. `Ric = (n−1)·f·g` pointwise,

then `f` is constant; moreover the metric has constant curvature `f x`,
respectively is Einstein with Einstein constant `(n−1)·f x`, for every
`x : M`. -/
theorem schurLemma [PreconnectedSpace M] (D : RiemannianConnection I g)
    (hn : 3 ≤ Module.finrank ℝ E) {f : M → ℝ} :
    ((∀ (p : M) (v w : TangentSpace I p), LinearIndependent ℝ ![v, w] →
        sectionalCurvature D p v w = f p) →
      (∀ x y : M, f x = f y)
        ∧ ∀ x : M, HasConstantCurvature D (f x))
    ∧ ((∀ (p : M) (v w : TangentSpace I p),
        RicciCurvature D.toAffineConnection p v w
          = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w) →
      (∀ x y : M, f x = f y)
        ∧ ∀ x : M, IsEinstein D (((Module.finrank ℝ E : ℝ) - 1) * f x)) := by
  have core : (∀ (p : M) (v w : TangentSpace I p),
      RicciCurvature D.toAffineConnection p v w
        = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w) →
      ∀ x y : M, f x = f y := by
    intro hric
    have hf : ContMDiff I 𝓘(ℝ) ∞ f := by
      have hn3 : (3 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn
      have hne : (Module.finrank ℝ E : ℝ)
          * ((Module.finrank ℝ E : ℝ) - 1) ≠ 0 := by nlinarith
      have hn1 : (Module.finrank ℝ E : ℝ) - 1 ≠ 0 := by nlinarith
      have hfe : f = fun q => ((Module.finrank ℝ E : ℝ)
          * ((Module.finrank ℝ E : ℝ) - 1))⁻¹ * scalarCurvature D q := by
        funext q
        rw [scalarCurvature_of_ricci_eq D hric q]
        field_simp
      rw [hfe]
      exact contMDiff_const.mul (contMDiff_scalarCurvature D)
    exact apply_eq_of_mfderiv_eq_zero (hf.mdifferentiable (by simp))
      (mfderiv_eq_zero_of_ricci_eq D hn hric)
  constructor
  · -- (1) constant sectional curvature pointwise
    intro hsec
    have hric : ∀ (p : M) (v w : TangentSpace I p),
        RicciCurvature D.toAffineConnection p v w
          = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w :=
      fun p v w => ricciCurvature_eq_of_pointwise_constant_sec D p
        (fun a b hab => hsec p a b hab) v w
    have hconst := core hric
    refine ⟨hconst, fun x p v w hvw => ?_⟩
    rw [hsec p v w hvw]
    exact hconst p x
  · -- (2) pointwise Einstein
    intro hric
    have hconst := core hric
    refine ⟨hconst, fun x p v w => ?_⟩
    rw [hric p v w, hconst p x]

/-! ## Corollary 3.1.6 — the Einstein characterization -/

/-- **Math.** **Corollary 3.1.6** (Petersen §3.1.5): a connected Riemannian
manifold of dimension `n > 2` is Einstein if and only if
`Ric = (scal/n)·g`. -/
theorem einstein_iff_ricci_eq_scal_div_n_metric [PreconnectedSpace M]
    (D : RiemannianConnection I g) (hn : 2 < Module.finrank ℝ E) :
    (∃ k : ℝ, IsEinstein D k)
      ↔ ∀ (p : M) (v w : TangentSpace I p),
          RicciCurvature D.toAffineConnection p v w
            = scalarCurvature D p / (Module.finrank ℝ E : ℝ)
              * g.metricInner p v w := by
  classical
  have hn' : 3 ≤ Module.finrank ℝ E := hn
  have hnR : (3 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := by exact_mod_cast hn'
  have hnne : (Module.finrank ℝ E : ℝ) ≠ 0 := by nlinarith
  have hn1ne : (Module.finrank ℝ E : ℝ) - 1 ≠ 0 := by nlinarith
  constructor
  · -- Einstein ⇒ `Ric = (scal/n)·g`
    rintro ⟨k, hk⟩
    intro p v w
    -- trace: `scal = n·k`
    have hscal : scalarCurvature D p = (Module.finrank ℝ E : ℝ) * k := by
      have hric' : ∀ (q : M) (a c : TangentSpace I q),
          RicciCurvature D.toAffineConnection q a c
            = ((Module.finrank ℝ E : ℝ) - 1)
              * (k / ((Module.finrank ℝ E : ℝ) - 1)) * g.metricInner q a c := by
        intro q a c
        rw [hk q a c]
        field_simp
      rw [scalarCurvature_of_ricci_eq D hric' p]
      field_simp
    rw [hk p v w, hscal]
    field_simp
  · -- `Ric = (scal/n)·g` ⇒ Einstein
    intro hric
    -- Schur with `f = scal/(n(n−1))`
    set f : M → ℝ := fun q => scalarCurvature D q
      / ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1)) with hf
    have hric' : ∀ (p : M) (v w : TangentSpace I p),
        RicciCurvature D.toAffineConnection p v w
          = ((Module.finrank ℝ E : ℝ) - 1) * f p * g.metricInner p v w := by
      intro p v w
      rw [hric p v w, hf]
      field_simp
    have hschur := (schurLemma D hn').2 hric'
    rcases isEmpty_or_nonempty M with hM | hM
    · exact ⟨0, fun p => (IsEmpty.false p).elim⟩
    · obtain ⟨x⟩ := hM
      exact ⟨((Module.finrank ℝ E : ℝ) - 1) * f x, hschur.2 x⟩

end PetersenLib

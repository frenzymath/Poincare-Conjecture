import PetersenLib.Ch03.CurvatureOperator
import PetersenLib.Ch03.RicciSectional
import Mathlib.Tactic.TFAE

/-!
# Petersen Ch. 3, §3.1.3 — Riemann's constant-curvature equivalence (1854)

Riemann's proposition (Petersen §3.1.3,
`prop:pet-ch3-riemann-constant-curvature-equivalence`): for fixed `p ∈ M` and
`k ∈ ℝ`, the following are equivalent —

1. `sec(π) = k` for all 2-planes `π ⊆ T_pM`;
2. `R(v₁,v₂)v₃ = −k·(v₁∧v₂)(v₃)` for all `v₁, v₂, v₃ ∈ T_pM`;
3. `R_v(w) = k·(w − g(w,v)v)` for all `w` and unit `v`;
4. `𝔯(ω) = k·ω` for every bivector `ω ∈ Λ²T_pM` (skew endomorphism).

The proof pivots through the diagonal condition
`R(x,y,x,y) = −k·g(x∧y, x∧y)` for **all** pairs `x, y`: (1) ⟹ diag splits
into the linearly independent case (the sectional hypothesis) and the
dependent case (both sides vanish); diag ⟹ (2) is the polarization argument
`IsAlgCurvatureForm.eq_smul_bivectorPairing_of_const` (Petersen's
`D = R − R_k` computation); (3) ⟹ diag rescales the unit-vector hypothesis
by homogeneity; diag ⟹ (1) divides by `|v∧w|² > 0` (strict Cauchy–Schwarz);
and (2) ⟺ (4) goes through the defining property and uniqueness of the
curvature operator.

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.3.
-/

open scoped ContDiff Manifold Topology Bundle

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ## Auxiliary positivity and existence facts -/

/-- Symmetry of the bivector inner product under swapping the pair. -/
theorem bivectorInnerProduct_swap_pair (g : RiemannianMetric I M) (p : M)
    (x y : TangentSpace I p) :
    bivectorInnerProduct g p y x y x = bivectorInnerProduct g p x y x y := by
  rw [bivectorInnerProduct, bivectorInnerProduct, g.metricInner_comm p y x]
  ring

/-- A `g`-orthonormal basis of `T_pM` exists (Gram–Schmidt, through the
`RiemannianBundle` fibre-instance bridge). -/
theorem exists_metricOrthonormalBasis (g : RiemannianMetric I M) (p : M) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ (TangentSpace I p))) ℝ
        (TangentSpace I p),
      ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
  letI rb : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  classical
  refine ⟨(stdOrthonormalBasis ℝ (TangentSpace I p)).toBasis, fun i j => ?_⟩
  have h := orthonormal_iff_ite.mp
    (stdOrthonormalBasis ℝ (TangentSpace I p)).orthonormal i j
  simpa using h

/-! ## The diagonal pivot -/

section Pivot

variable {g : RiemannianMetric I M}

/-- (1) ⟹ diagonal: `R(x,y,x,y) = −k·|x∧y|²` for **all** `x, y` — on
independent pairs from the sectional hypothesis, on dependent pairs both
sides vanish. -/
theorem diag_of_sectionalCurvature_const (D : RiemannianConnection I g)
    (p : M) (k : ℝ)
    (h1 : ∀ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] →
      sectionalCurvature D p v w = k) (x y : TangentSpace I p) :
    curvatureTensorFourAt D p x y x y
      = -k * bivectorInnerProduct g p x y x y := by
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  by_cases hxy : LinearIndependent ℝ ![x, y]
  · -- independent: `sec(x,y) = k`, numerator `R(y,x,x,y) = −R(x,y,x,y)`
    have hsec := h1 x y hxy
    rw [sectionalCurvature_eq_curvatureTensorFourAt] at hsec
    have hpos := bivectorInnerProduct_self_pos g p hxy
    have hnum : curvatureTensorFourAt D p y x x y
        = k * bivectorInnerProduct g p x y x y := by
      rw [div_eq_iff hpos.ne'] at hsec
      exact hsec
    have ha := hAlg.antisymm₁₂ y x x y
    rw [hnum] at ha
    linarith [ha]
  · -- dependent pair: both sides vanish
    have hz1 : curvatureTensorFourAt D p x y x y = 0 := by
      simpa using hAlg.diag_eq_zero_of_not_linearIndependent hxy
    have hz2 : bivectorInnerProduct g p x y x y = 0 := by
      have hb := isAlgCurvatureForm_bivectorPairing (g.metricBilin p)
        (fun a b => g.metricInner_comm p a b)
      rw [bivectorInnerProduct_eq_bivectorPairing]
      simpa using hb.diag_eq_zero_of_not_linearIndependent hxy
    rw [hz1, hz2]
    ring

/-- diagonal ⟹ (1): divide by `|v∧w|² > 0`. -/
theorem sectionalCurvature_const_of_diag (D : RiemannianConnection I g)
    (p : M) (k : ℝ)
    (hd : ∀ x y : TangentSpace I p, curvatureTensorFourAt D p x y x y
      = -k * bivectorInnerProduct g p x y x y)
    (v w : TangentSpace I p) (hvw : LinearIndependent ℝ ![v, w]) :
    sectionalCurvature D p v w = k := by
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hpos := bivectorInnerProduct_self_pos g p hvw
  rw [sectionalCurvature_eq_curvatureTensorFourAt]
  have h1 := hAlg.antisymm₃₄ w v v w
  have h2 := hd w v
  have h3 := bivectorInnerProduct_swap_pair g p v w
  rw [h1, h2, h3, neg_mul, neg_neg, mul_div_assoc, div_self hpos.ne',
    mul_one]

/-- diagonal ⟹ (2): the polarization argument, through
`IsAlgCurvatureForm.eq_smul_bivectorPairing_of_const`. -/
theorem curvature_eq_of_diag (D : RiemannianConnection I g) (p : M) (k : ℝ)
    (hd : ∀ x y : TangentSpace I p, curvatureTensorFourAt D p x y x y
      = -k * bivectorInnerProduct g p x y x y)
    (x y z : TangentSpace I p) :
    curvatureTensorAt D.toAffineConnection p x y z
      = (-k) • bivectorSkewMap g p x y z := by
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  have hfull : ∀ a b c d : TangentSpace I p, curvatureTensorFourAt D p a b c d
      = -k * bivectorPairing (g.metricBilin p) a b c d := by
    refine hAlg.eq_smul_bivectorPairing_of_const (g.metricBilin p)
      (fun a b => g.metricInner_comm p a b) (-k) ?_
    intro a b
    rw [← bivectorInnerProduct_eq_bivectorPairing]
    exact hd a b
  refine ((g.metricInner_eq_iff_eq p _ _).mp fun t => ?_)
  calc g.metricInner p (curvatureTensorAt D.toAffineConnection p x y z) t
      = curvatureTensorFourAt D p x y z t := rfl
    _ = -k * bivectorPairing (g.metricBilin p) x y z t := hfull x y z t
    _ = -k * bivectorInnerProduct g p x y z t := by
        rw [bivectorInnerProduct_eq_bivectorPairing]
    _ = -k * g.metricInner p (bivectorSkewMap g p x y z) t := by
        rw [bivectorSkewMap_metricInner]
    _ = g.metricInner p ((-k) • bivectorSkewMap g p x y z) t := by
        rw [g.metricInner_smul_left]

/-- (3) ⟹ diagonal, rescaling the unit-vector hypothesis by homogeneity. -/
theorem diag_of_directionalCurvature (D : RiemannianConnection I g) (p : M)
    (k : ℝ)
    (h3 : ∀ v w : TangentSpace I p, g.metricInner p v v = 1 →
      directionalCurvatureOperator D.toAffineConnection p v w
        = k • (w - g.metricInner p w v • v))
    (x y : TangentSpace I p) :
    curvatureTensorFourAt D p x y x y
      = -k * bivectorInnerProduct g p x y x y := by
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  rcases eq_or_ne y 0 with hy | hy
  · subst hy
    rw [hAlg.zero_two x x 0, bivectorInnerProduct,
      g.metricInner_zero_right, g.metricInner_zero_left]
    ring
  · -- normalize `y = c • u` with `u` a unit vector, using quartic homogeneity
    have hyy : 0 < g.metricInner p y y := g.metricInner_self_pos p y hy
    -- the diagonal identity for any unit vector `u` and any scale `c`
    have key : ∀ u : TangentSpace I p, g.metricInner p u u = 1 → ∀ c : ℝ,
        curvatureTensorFourAt D p x (c • u) x (c • u)
          = -k * bivectorInnerProduct g p x (c • u) x (c • u) := by
      intro u huu c
      have hunit : curvatureTensorFourAt D p x u x u
          = -k * bivectorInnerProduct g p x u x u := by
        have h := congrArg (fun z : TangentSpace I p => g.metricInner p z x)
          (h3 u x huu)
        have hL : g.metricInner p
            (directionalCurvatureOperator D.toAffineConnection p u x) x
            = curvatureTensorFourAt D p x u u x := rfl
        have hR : g.metricInner p
            (k • (x - g.metricInner p x u • u) : TangentSpace I p) x
            = k * (g.metricInner p x x
              - g.metricInner p x u * g.metricInner p u x) := by
          rw [g.metricInner_smul_left, g.metricInner_sub_left,
            g.metricInner_smul_left]
        simp only at h
        rw [hL, hR] at h
        have ha := hAlg.antisymm₃₄ x u u x
        have hbipu : bivectorInnerProduct g p x u x u
            = g.metricInner p x x
              - g.metricInner p x u * g.metricInner p u x := by
          rw [bivectorInnerProduct, huu]
          ring
        rw [hbipu]
        linarith [h, ha]
      rw [hAlg.smul_two, hAlg.smul_four, hunit]
      have hbip : bivectorInnerProduct g p x (c • u) x (c • u)
          = c * (c * bivectorInnerProduct g p x u x u) := by
        simp only [bivectorInnerProduct, g.metricInner_smul_left,
          g.metricInner_smul_right]
        ring
      rw [hbip]
      ring
    -- apply with `c = √g(y,y)`, `u = c⁻¹ • y`
    have hcpos : 0 < Real.sqrt (g.metricInner p y y) := Real.sqrt_pos.mpr hyy
    have huu : g.metricInner p ((Real.sqrt (g.metricInner p y y))⁻¹ • y)
        ((Real.sqrt (g.metricInner p y y))⁻¹ • y) = 1 := by
      rw [g.metricInner_smul_left, g.metricInner_smul_right, ← mul_assoc,
        ← Real.sqrt_inv]
      rw [Real.mul_self_sqrt (by positivity)]
      exact inv_mul_cancel₀ hyy.ne'
    have hyu : y = Real.sqrt (g.metricInner p y y)
        • ((Real.sqrt (g.metricInner p y y))⁻¹ • y) := by
      rw [smul_smul, mul_inv_cancel₀ hcpos.ne', one_smul]
    calc curvatureTensorFourAt D p x y x y
        = curvatureTensorFourAt D p x (Real.sqrt (g.metricInner p y y)
            • ((Real.sqrt (g.metricInner p y y))⁻¹ • y)) x
            (Real.sqrt (g.metricInner p y y)
            • ((Real.sqrt (g.metricInner p y y))⁻¹ • y)) := by rw [← hyu]
      _ = -k * bivectorInnerProduct g p x (Real.sqrt (g.metricInner p y y)
            • ((Real.sqrt (g.metricInner p y y))⁻¹ • y)) x
            (Real.sqrt (g.metricInner p y y)
            • ((Real.sqrt (g.metricInner p y y))⁻¹ • y)) :=
          key _ huu _
      _ = -k * bivectorInnerProduct g p x y x y := by rw [← hyu]

end Pivot

/-! ## Riemann's proposition -/

variable {g : RiemannianMetric I M}

/-- **Math.** **Riemann, 1854** (Petersen §3.1.3, Prop.; recorded as
`prop:pet-ch3-riemann-constant-curvature-equivalence`): for fixed `p ∈ M` and
`k ∈ ℝ`, the following are equivalent:

1. `sec(π) = k` for every 2-plane `π ⊆ T_pM`;
2. `R(v₁,v₂)v₃ = −k·(v₁∧v₂)(v₃)` for all `v₁, v₂, v₃ ∈ T_pM`;
3. `R_v(w) = k·(w − g(w,v)v) = k·prj_{v^⊥}(w)` for all `w ∈ T_pM` and unit `v`;
4. `𝔯(ω) = k·ω` for all `ω ∈ Λ²T_pM` (i.e. on every skew endomorphism). -/
theorem riemann_constantCurvature_equivalence
    (D : RiemannianConnection I g) (p : M) (k : ℝ) :
    [(∀ v w : TangentSpace I p, LinearIndependent ℝ ![v, w] →
        sectionalCurvature D p v w = k),
      (∀ v₁ v₂ v₃ : TangentSpace I p,
        curvatureTensorAt D.toAffineConnection p v₁ v₂ v₃
          = (-k) • bivectorSkewMap g p v₁ v₂ v₃),
      (∀ v w : TangentSpace I p, g.metricInner p v v = 1 →
        directionalCurvatureOperator D.toAffineConnection p v w
          = k • (w - g.metricInner p w v • v)),
      (∀ A : Module.End ℝ (TangentSpace I p), IsSkewAt g p A →
        curvatureOperator D p A = k • A)].TFAE := by
  have hAlg := isAlgCurvatureForm_curvatureTensorFourAt D p
  tfae_have 1 → 2 := fun h1 =>
    curvature_eq_of_diag D p k (diag_of_sectionalCurvature_const D p k h1)
  tfae_have 2 → 3 := by
    intro h2 v w hv
    show curvatureTensorAt D.toAffineConnection p w v v = _
    rw [h2 w v v]
    show (-k) • (g.metricInner p w v • v - g.metricInner p v v • w)
      = k • (w - g.metricInner p w v • v)
    rw [hv]
    module
  tfae_have 3 → 1 := fun h3 =>
    sectionalCurvature_const_of_diag D p k
      (diag_of_directionalCurvature D p k h3)
  tfae_have 2 → 4 := by
    intro h2 A hA
    obtain ⟨b, hb⟩ := exists_metricOrthonormalBasis g p
    have h04 : ∀ x y z t : TangentSpace I p,
        curvatureTensorFourAt D p x y z t
          = -k * bivectorInnerProduct g p x y z t := by
      intro x y z t
      show g.metricInner p (curvatureTensorAt D.toAffineConnection p x y z) t
        = _
      rw [h2 x y z, g.metricInner_smul_left, bivectorSkewMap_metricInner]
    have hskew : ∀ B : Module.End ℝ (TangentSpace I p), IsSkewAt g p B →
        IsSkewAt g p ((k • LinearMap.id
          : Module.End ℝ (TangentSpace I p) →ₗ[ℝ]
            Module.End ℝ (TangentSpace I p)) B) := by
      intro B hB v w
      simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      show g.metricInner p ((k • B) v) w = -g.metricInner p v ((k • B) w)
      simp only [LinearMap.smul_apply]
      rw [g.metricInner_smul_left, g.metricInner_smul_right, hB v w]
      ring
    have hL : ∀ x y v w : TangentSpace I p,
        bivectorEndoInner g p
          ((k • LinearMap.id
            : Module.End ℝ (TangentSpace I p) →ₗ[ℝ]
              Module.End ℝ (TangentSpace I p)) (wedgeEndo g p x y))
          (wedgeEndo g p v w)
        = curvatureTensorFourAt D p x y w v := by
      intro x y v w
      simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
      rw [bivectorEndoInner_smul_left, bivectorEndoInner_wedgeEndo_wedgeEndo,
        h04 x y w v]
      rw [bivectorInnerProduct, bivectorInnerProduct]
      ring
    have huniq := curvatureOperator_unique D p b hb
      (k • LinearMap.id) hskew hL hA
    rw [← huniq]
    simp only [LinearMap.smul_apply, LinearMap.id_coe, id_eq]
  tfae_have 4 → 1 := by
    intro h4
    refine sectionalCurvature_const_of_diag D p k (fun x y => ?_)
    have hw := h4 (wedgeEndo g p x y) (isSkewAt_wedgeEndo g p x y)
    have h1 := bivectorEndoInner_curvatureOperator_wedge_wedge D p x y x y
    rw [hw, bivectorEndoInner_smul_left,
      bivectorEndoInner_wedgeEndo_wedgeEndo] at h1
    have ha := hAlg.antisymm₃₄ x y y x
    linarith [h1, ha]
  tfae_finish

/-- **Math.** Constant curvature `k` (Petersen §3.1.3,
`def:pet-ch3-constant-curvature`) restated through Riemann's proposition: the
sectional-curvature definition `HasConstantCurvature` holds iff at every
point the curvature tensor is the constant-curvature model tensor
`R(v₁,v₂)v₃ = −k·(v₁∧v₂)(v₃)`. -/
theorem hasConstantCurvature_iff_curvature_eq
    (D : RiemannianConnection I g) (k : ℝ) :
    HasConstantCurvature D k
      ↔ ∀ (p : M) (v₁ v₂ v₃ : TangentSpace I p),
          curvatureTensorAt D.toAffineConnection p v₁ v₂ v₃
            = (-k) • bivectorSkewMap g p v₁ v₂ v₃ := by
  constructor
  · intro h p
    have hiff := (riemann_constantCurvature_equivalence D p k).out 0 1
    exact hiff.mp (fun v w hvw => h p v w hvw)
  · intro h p v w hvw
    have hiff := (riemann_constantCurvature_equivalence D p k).out 1 0
    exact hiff.mp (h p) v w hvw

end PetersenLib

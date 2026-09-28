import PetersenLib.Ch03.GramFrame

/-!
# Petersen Ch. 3, §3.1.5 — the covariant derivative of the Ricci tensor

The covariant derivative of the Ricci tensor
`(∇_X Ric)(Y,Z) = D_X(Ric(Y,Z)) − Ric(∇_X Y, Z) − Ric(Y, ∇_X Z)`
(`covariantDerivativeRicci`), pointwise linearity and symmetry of `Ric`, and
the **trace–derivative commutation**
(`covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour`): for any
smooth frame `F` that is `g`-orthonormal at `p`,

`(∇_X Ric)(Y,Z)|_p = ∑ᵢ (∇_X R)(Fᵢ, Y, Z, Fᵢ)|_p`,

i.e. the covariant derivative of the trace is the trace of the covariant
derivative. The frame-derivative corrections cancel against the derivative of
the inverse Gram matrix — no parallel frame is needed. Similarly
(`directionalDerivative_scalarCurvature_eq_sum`)

`d(scal)(X)|_p = ∑ᵢ (∇_X Ric)(Fᵢ, Fᵢ)|_p`.

These are the analytic inputs for the contracted Bianchi identity
(Prop. 3.1.5).

Reference: Petersen, *Riemannian Geometry* (3rd ed.), §3.1.5.
-/

open Bundle Set Function Finset Filter
open scoped ContDiff Manifold Topology Bundle

set_option linter.unusedSectionVars false

noncomputable section

namespace PetersenLib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [CompleteSpace E]
  [SigmaCompactSpace M] [T2Space M] [LocallyCompactSpace M]

/-! ## Directional-derivative helpers -/

/-- Functions agreeing near `p` have equal directional derivatives at `p`. -/
theorem directionalDerivative_congr_nhds {f h : M → ℝ} {p : M}
    (hfh : f =ᶠ[𝓝 p] h) (X : Π x : M, TangentSpace I x) :
    directionalDerivative X f p = directionalDerivative X h p := by
  simp only [directionalDerivative_apply]
  rw [hfh.mfderiv_eq]
  rfl

/-- The directional derivative of a finite sum of smooth-at-`p` functions. -/
theorem directionalDerivative_finsetSum {ι : Type*} (s : Finset ι)
    {f : ι → M → ℝ} {p : M}
    (hf : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) ∞ (f i) p)
    (X : Π x : M, TangentSpace I x) :
    directionalDerivative X (fun q => ∑ i ∈ s, f i q) p
      = ∑ i ∈ s, directionalDerivative X (f i) p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have e : (fun q : M => ∑ i ∈ (∅ : Finset ι), f i q)
          = fun _ : M => (0 : ℝ) := by
        funext q; simp
      rw [e, Finset.sum_empty]
      exact directionalDerivative_const X 0 p
  | insert a s ha ih =>
      have hfa : ContMDiffAt I 𝓘(ℝ) ∞ (f a) p := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, ContMDiffAt I 𝓘(ℝ) ∞ (f i) p :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : ContMDiffAt I 𝓘(ℝ) ∞ (fun q => ∑ i ∈ s, f i q) p :=
        ContMDiffAt.sum hfs
      have e : (fun q => ∑ i ∈ insert a s, f i q)
          = fun q => f a q + ∑ i ∈ s, f i q := by
        funext q; exact Finset.sum_insert ha
      have hadd : directionalDerivative X
            (fun q => f a q + ∑ i ∈ s, f i q) p
          = directionalDerivative X (f a) p
            + directionalDerivative X (fun q => ∑ i ∈ s, f i q) p :=
        directionalDerivative_add (hfa.mdifferentiableAt (by simp))
          (hsum.mdifferentiableAt (by simp)) X
      rw [e, hadd, ih hfs, Finset.sum_insert ha]

/-! ## Pointwise linearity and symmetry of the Ricci tensor -/

variable {g : RiemannianMetric I M}

theorem ricciCurvature_add_left (D : AffineConnection I M) (p : M)
    (v₁ v₂ w : TangentSpace I p) :
    RicciCurvature D p (v₁ + v₂) w
      = RicciCurvature D p v₁ w + RicciCurvature D p v₂ w := by
  simp only [RicciCurvature]
  rw [← map_add]
  congr 1
  ext x
  simp only [LinearMap.add_apply, curvatureTensorAtFirstLinear_apply]
  exact curvatureTensorAt_add_middle D p x v₁ v₂ w

theorem ricciCurvature_smul_left (D : AffineConnection I M) (p : M)
    (c : ℝ) (v w : TangentSpace I p) :
    RicciCurvature D p (c • v) w = c * RicciCurvature D p v w := by
  simp only [RicciCurvature]
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext x
  simp only [LinearMap.smul_apply, curvatureTensorAtFirstLinear_apply]
  exact curvatureTensorAt_smul_middle D p c x v w

theorem ricciCurvature_add_right (D : AffineConnection I M) (p : M)
    (v w₁ w₂ : TangentSpace I p) :
    RicciCurvature D p v (w₁ + w₂)
      = RicciCurvature D p v w₁ + RicciCurvature D p v w₂ := by
  simp only [RicciCurvature]
  rw [← map_add]
  congr 1
  ext x
  simp only [LinearMap.add_apply, curvatureTensorAtFirstLinear_apply]
  exact curvatureTensorAt_add_field D p x v w₁ w₂

theorem ricciCurvature_smul_right (D : AffineConnection I M) (p : M)
    (c : ℝ) (v w : TangentSpace I p) :
    RicciCurvature D p v (c • w) = c * RicciCurvature D p v w := by
  simp only [RicciCurvature]
  rw [← smul_eq_mul, ← map_smul]
  congr 1
  ext x
  simp only [LinearMap.smul_apply, curvatureTensorAtFirstLinear_apply]
  exact curvatureTensorAt_smul_field D p c x v w

/-- **Math.** The Ricci tensor is symmetric: `Ric(v,w) = Ric(w,v)`
(Petersen §3.1.4) — by the pair-swap symmetry of `R`. -/
theorem ricciCurvature_comm (D : RiemannianConnection I g) (p : M)
    (v w : TangentSpace I p) :
    RicciCurvature D.toAffineConnection p v w
      = RicciCurvature D.toAffineConnection p w v := by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  set e := stdOrthonormalBasis ℝ (TangentSpace I p) with he
  have hb : ∀ i j, g.metricInner p (e.toBasis i) (e.toBasis j)
      = if i = j then 1 else 0 := by
    intro i j
    have h1 := orthonormal_iff_ite.mp e.orthonormal i j
    rw [OrthonormalBasis.coe_toBasis]
    exact h1
  have halg := isAlgCurvatureForm_curvatureTensorFourAt D p
  rw [ricciCurvature_eq_sum D p e.toBasis hb v w,
    ricciCurvature_eq_sum D p e.toBasis hb w v]
  refine Finset.sum_congr rfl fun i _ => ?_
  calc curvatureTensorFourAt D p (e.toBasis i) v w (e.toBasis i)
      = curvatureTensorFourAt D p w (e.toBasis i) (e.toBasis i) v :=
        halg.pairSwap ..
    _ = curvatureTensorFourAt D p (e.toBasis i) w v (e.toBasis i) := by
        rw [halg.antisymm₁₂ w (e.toBasis i) (e.toBasis i) v,
          halg.antisymm₃₄ (e.toBasis i) w (e.toBasis i) v, neg_neg]

/-! ## The covariant derivative of the Ricci tensor -/

/-- **Math.** The **covariant derivative of the Ricci tensor** (Petersen
§2.2.2 applied to `Ric`): the Leibniz-defined `(0,3)`-tensor
`(∇_X Ric)(Y,Z) = D_X(Ric(Y,Z)) − Ric(∇_X Y, Z) − Ric(Y, ∇_X Z)`. -/
def covariantDerivativeRicci (D : RiemannianConnection I g)
    (X Y Z : Π x : M, TangentSpace I x) : M → ℝ :=
  fun p => directionalDerivative X
      (fun q => RicciCurvature D.toAffineConnection q (Y q) (Z q)) p
    - RicciCurvature D.toAffineConnection p
        (D.toAffineConnection.covField X Y p) (Z p)
    - RicciCurvature D.toAffineConnection p (Y p)
        (D.toAffineConnection.covField X Z p)

theorem covariantDerivativeRicci_apply (D : RiemannianConnection I g)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    covariantDerivativeRicci D X Y Z p
      = directionalDerivative X
          (fun q => RicciCurvature D.toAffineConnection q (Y q) (Z q)) p
        - RicciCurvature D.toAffineConnection p
            (D.toAffineConnection.covField X Y p) (Z p)
        - RicciCurvature D.toAffineConnection p (Y p)
            (D.toAffineConnection.covField X Z p) := rfl

/-- `∇Ric` is symmetric in its two tensor slots, like `Ric`. -/
theorem covariantDerivativeRicci_comm (D : RiemannianConnection I g)
    (X Y Z : Π x : M, TangentSpace I x) (p : M) :
    covariantDerivativeRicci D X Y Z p = covariantDerivativeRicci D X Z Y p := by
  have e : (fun q => RicciCurvature D.toAffineConnection q (Y q) (Z q))
      = fun q => RicciCurvature D.toAffineConnection q (Z q) (Y q) := by
    funext q
    exact ricciCurvature_comm D q (Y q) (Z q)
  rw [covariantDerivativeRicci_apply, covariantDerivativeRicci_apply, e,
    ricciCurvature_comm D p (D.toAffineConnection.covField X Y p) (Z p),
    ricciCurvature_comm D p (Y p) (D.toAffineConnection.covField X Z p)]
  ring

/-! ## The frame-correction cancellation -/

/-- The algebraic heart of trace–derivative commutation: for an orthonormal
basis `bᵢ` of `T_pM` and arbitrary vectors `Aᵢ` (the frame derivatives), the
first-and-last-slot corrections match the Gram-derivative corrections. -/
private theorem frame_correction_cancel (D : RiemannianConnection I g) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (A : ι → TangentSpace I p) (y z : TangentSpace I p) :
    ∑ i, (curvatureTensorFourAt D p (A i) y z (b i)
        + curvatureTensorFourAt D p (b i) y z (A i))
      = ∑ i, ∑ j, curvatureTensorFourAt D p (b i) y z (b j)
          * (g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
  classical
  have halg := isAlgCurvatureForm_curvatureTensorFourAt D p
  -- Parseval: `A i = ∑ⱼ g(Aᵢ, bⱼ) • bⱼ`
  have hA : ∀ i, A i = ∑ j, g.metricInner p (A i) (b j) • b j := by
    intro i
    conv_lhs => rw [← b.sum_repr (A i)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [orthonormal_basis_repr_eq_metricInner p b hb]
  have hfirst : ∀ i, curvatureTensorFourAt D p (A i) y z (b i)
      = ∑ j, g.metricInner p (A i) (b j)
          * curvatureTensorFourAt D p (b j) y z (b i) := by
    intro i
    conv_lhs => rw [hA i]
    exact halg.sum_left Finset.univ _ b y z (b i)
  have hlast : ∀ i, curvatureTensorFourAt D p (b i) y z (A i)
      = ∑ j, g.metricInner p (A i) (b j)
          * curvatureTensorFourAt D p (b i) y z (b j) := by
    intro i
    conv_lhs => rw [hA i]
    exact halg.sum_four Finset.univ _ b (b i) y z
  have hsplit : ∑ i, (curvatureTensorFourAt D p (A i) y z (b i)
        + curvatureTensorFourAt D p (b i) y z (A i))
      = (∑ i, ∑ j, g.metricInner p (A i) (b j)
            * curvatureTensorFourAt D p (b j) y z (b i))
        + ∑ i, ∑ j, g.metricInner p (A i) (b j)
            * curvatureTensorFourAt D p (b i) y z (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfirst i, hlast i, ← Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, g.metricInner p (A i) (b j)
        * curvatureTensorFourAt D p (b j) y z (b i))
      = ∑ i, ∑ j, g.metricInner p (A j) (b i)
          * curvatureTensorFourAt D p (b i) y z (b j) :=
    Finset.sum_comm
  rw [hsplit, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g.metricInner_comm p (b i) (A j)]
  ring

/-! ## An orthonormal family is a basis -/

/-- A `g`-orthonormal family of `n = dim M` tangent vectors at `p` extends to a
`Module.Basis` whose coercion is the family. -/
theorem exists_orthonormalBasis_of_family (p : M)
    {v : Fin (Module.finrank ℝ E) → TangentSpace I p}
    (horth : ∀ i j, g.metricInner p (v i) (v j) = if i = j then 1 else 0) :
    ∃ b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p),
      ⇑b = v := by
  have hgram : gramMatrix g p v = 1 := by
    ext i j
    rw [gramMatrix_apply, horth, Matrix.one_apply]
  have hdet : (gramMatrix g p v).det ≠ 0 := by
    rw [hgram, Matrix.det_one]
    exact one_ne_zero
  have hli := linearIndependent_of_gramMatrix_det_ne_zero p hdet
  have hcard : Fintype.card (Fin (Module.finrank ℝ E))
      = Module.finrank ℝ (TangentSpace I p) := by
    rw [Fintype.card_fin]
    rfl
  exact ⟨basisOfLinearIndependentOfCardEqFinrank hli hcard,
    coe_basisOfLinearIndependentOfCardEqFinrank hli hcard⟩

/-! ## The derivative of the inverse Gram matrix -/

/-- The derivative of the inverse Gram matrix of a frame orthonormal at `p`:
`D_X (G⁻¹)ᵢⱼ|_p = −(g(∇_X Fᵢ, Fⱼ) + g(Fᵢ, ∇_X Fⱼ))|_p` — differentiate
`G·G⁻¹ = 1` and use metric compatibility. -/
theorem directionalDerivative_cramerInverse_gram (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i))
    (X : Π x : M, TangentSpace I x) {p : M}
    (horth : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0)
    (i j : Fin (Module.finrank ℝ E)) :
    directionalDerivative X
        (fun q => cramerInverse (gramMatrixField g F q) i j) p
      = -(g.metricInner p (D.cov p (X p) (F i)) (F j p)
          + g.metricInner p (F i p) (D.cov p (X p) (F j))) := by
  classical
  have hev := gramMatrixField_det_ne_zero_eventually hF horth
  have hG1 : gramMatrixField g F p = 1 :=
    gramMatrixField_eq_one_of_orthonormal horth
  have hdetp : (gramMatrixField g F p).det ≠ 0 := by
    rw [hG1, Matrix.det_one]
    exact one_ne_zero
  have hGsm : ∀ a b, ContMDiff I 𝓘(ℝ) ∞
      (fun q => gramMatrixField g F q a b) :=
    fun a b => contMDiff_gramMatrixField_entry hF a b
  have hGinvSm : ∀ a b, ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => cramerInverse (gramMatrixField g F q) a b) p :=
    fun a b => contMDiffAt_matrix_cramerInverse (fun c d => hGsm c d) hdetp a b
  -- `G·G⁻¹ = 1` near `p`, entrywise
  have hconst : (fun q => ∑ k, gramMatrixField g F q i k
        * cramerInverse (gramMatrixField g F q) k j)
      =ᶠ[𝓝 p] fun _ => ((1 : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) i j) := by
    filter_upwards [hev] with q hq
    have hmul : (gramMatrixField g F q * cramerInverse (gramMatrixField g F q))
        i j = (1 : Matrix _ _ ℝ) i j := by
      rw [mul_cramerInverse hq]
    rw [Matrix.mul_apply] at hmul
    exact hmul
  have hdd0 : directionalDerivative X
      (fun q => ∑ k, gramMatrixField g F q i k
        * cramerInverse (gramMatrixField g F q) k j) p = 0 := by
    rw [directionalDerivative_congr_nhds hconst X]
    exact directionalDerivative_const X _ p
  -- expand the sum and each product
  have hterm : ∀ k, ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => gramMatrixField g F q i k
        * cramerInverse (gramMatrixField g F q) k j) p :=
    fun k => ((hGsm i k) p).mul (hGinvSm k j)
  rw [directionalDerivative_finsetSum Finset.univ (fun k _ => hterm k) X]
    at hdd0
  have hprod : ∀ k, directionalDerivative X
        (fun q => gramMatrixField g F q i k
          * cramerInverse (gramMatrixField g F q) k j) p
      = (if i = k then 1 else 0) * directionalDerivative X
            (fun q => cramerInverse (gramMatrixField g F q) k j) p
        + (if k = j then 1 else 0) * directionalDerivative X
            (fun q => gramMatrixField g F q i k) p := by
    intro k
    have hmul : directionalDerivative X
          (fun q => gramMatrixField g F q i k
            * cramerInverse (gramMatrixField g F q) k j) p
        = gramMatrixField g F p i k * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) k j) p
          + cramerInverse (gramMatrixField g F p) k j * directionalDerivative X
              (fun q => gramMatrixField g F q i k) p :=
      directionalDerivative_mul (((hGsm i k) p).mdifferentiableAt (by simp))
        ((hGinvSm k j).mdifferentiableAt (by simp)) X
    rw [hmul, hG1, cramerInverse_one, Matrix.one_apply, Matrix.one_apply]
  rw [Finset.sum_congr rfl fun k _ => hprod k, Finset.sum_add_distrib] at hdd0
  -- collapse both Kronecker deltas
  have hδ1 : ∑ k, (if i = k then (1:ℝ) else 0) * directionalDerivative X
        (fun q => cramerInverse (gramMatrixField g F q) k j) p
      = directionalDerivative X
          (fun q => cramerInverse (gramMatrixField g F q) i j) p := by
    have he : ∀ k, (if i = k then (1:ℝ) else 0) * directionalDerivative X
          (fun q => cramerInverse (gramMatrixField g F q) k j) p
        = if i = k then directionalDerivative X
            (fun q => cramerInverse (gramMatrixField g F q) k j) p else 0 :=
      fun k => by split_ifs <;> simp
    rw [Finset.sum_congr rfl fun k _ => he k, Finset.sum_ite_eq]
    simp
  have hδ2 : ∑ k, (if k = j then (1:ℝ) else 0) * directionalDerivative X
        (fun q => gramMatrixField g F q i k) p
      = directionalDerivative X (fun q => gramMatrixField g F q i j) p := by
    have he : ∀ k, (if k = j then (1:ℝ) else 0) * directionalDerivative X
          (fun q => gramMatrixField g F q i k) p
        = if k = j then directionalDerivative X
            (fun q => gramMatrixField g F q i k) p else 0 :=
      fun k => by split_ifs <;> simp
    rw [Finset.sum_congr rfl fun k _ => he k, Finset.sum_ite_eq']
    simp
  rw [hδ1, hδ2] at hdd0
  -- metric compatibility identifies the Gram-entry derivative
  have hDG : directionalDerivative X (fun q => gramMatrixField g F q i j) p
      = g.metricInner p (D.cov p (X p) (F i)) (F j p)
        + g.metricInner p (F i p) (D.cov p (X p) (F j)) := by
    have h := D.metric_compat (hF i) (hF j) p (X p)
    rw [dirTangent_eq_directionalDerivative] at h
    exact h
  linarith [hdd0, hDG]

/-! ## Trace–derivative commutation for the Ricci tensor -/

/-- **Math.** **The covariant derivative commutes with the Ricci trace**: for
a smooth frame `F` that is `g`-orthonormal at `p`,
`(∇_X Ric)(Y,Z)|_p = ∑ᵢ (∇_X R)(Fᵢ, Y, Z, Fᵢ)|_p`. The frame-derivative
corrections cancel against the derivative of the inverse Gram matrix. -/
theorem covariantDerivativeRicci_eq_sum_covariantDerivativeCurvatureFour
    (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i))
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : IsSmoothVectorField X) (hY : IsSmoothVectorField Y)
    (hZ : IsSmoothVectorField Z) {p : M}
    (horth : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0) :
    covariantDerivativeRicci D X Y Z p
      = ∑ i, covariantDerivativeCurvatureFour D X (F i) Y Z (F i) p := by
  classical
  have hev := gramMatrixField_det_ne_zero_eventually hF horth
  have hG1 : gramMatrixField g F p = 1 :=
    gramMatrixField_eq_one_of_orthonormal horth
  have hdetp : (gramMatrixField g F p).det ≠ 0 := by
    rw [hG1, Matrix.det_one]
    exact one_ne_zero
  have hGsm : ∀ a b, ContMDiff I 𝓘(ℝ) ∞
      (fun q => gramMatrixField g F q a b) :=
    fun a b => contMDiff_gramMatrixField_entry hF a b
  have hGinvSm : ∀ a b, ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => cramerInverse (gramMatrixField g F q) a b) p :=
    fun a b => contMDiffAt_matrix_cramerInverse (fun c d => hGsm c d) hdetp a b
  have hR4sm : ∀ i j, ContMDiff I 𝓘(ℝ) ∞
      (curvatureTensorFour D (F i) Y Z (F j)) :=
    fun i j => contMDiff_curvatureTensorFour D (hF i) hY hZ (hF j)
  obtain ⟨b, hbcoe⟩ := exists_orthonormalBasis_of_family p horth
  have hb : ∀ i, b i = F i p := fun i => congrFun hbcoe i
  have hbo : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hb i, hb j]
    exact horth i j
  -- Step 1: the local Gram-inverse model for `Ric(Y,Z)`
  have hlocal : (fun q => RicciCurvature D.toAffineConnection q (Y q) (Z q))
      =ᶠ[𝓝 p] fun q => ∑ i, ∑ j, cramerInverse (gramMatrixField g F q) i j
        * curvatureTensorFour D (F i) Y Z (F j) q := by
    filter_upwards [hev] with q hq
    exact ricciCurvature_eval_eq_sum_gramInv D hF hY hZ hq
  -- Step 2: differentiate the double sum
  have hterm_sm : ∀ i j, ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => cramerInverse (gramMatrixField g F q) i j
        * curvatureTensorFour D (F i) Y Z (F j) q) p :=
    fun i j => (hGinvSm i j).mul ((hR4sm i j) p)
  have hdd1 : directionalDerivative X
        (fun q => RicciCurvature D.toAffineConnection q (Y q) (Z q)) p
      = ∑ i, ∑ j, directionalDerivative X
          (fun q => cramerInverse (gramMatrixField g F q) i j
            * curvatureTensorFour D (F i) Y Z (F j) q) p := by
    rw [directionalDerivative_congr_nhds hlocal X,
      directionalDerivative_finsetSum Finset.univ
        (fun i _ => ContMDiffAt.sum fun j _ => hterm_sm i j) X]
    exact Finset.sum_congr rfl fun i _ =>
      directionalDerivative_finsetSum Finset.univ (fun j _ => hterm_sm i j) X
  -- Step 3: product rule; `G⁻¹(p) = 1`
  have hprod : ∀ i j, directionalDerivative X
        (fun q => cramerInverse (gramMatrixField g F q) i j
          * curvatureTensorFour D (F i) Y Z (F j) q) p
      = (if i = j then 1 else 0)
          * directionalDerivative X (curvatureTensorFour D (F i) Y Z (F j)) p
        + curvatureTensorFour D (F i) Y Z (F j) p
          * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) i j) p := by
    intro i j
    have hmul : directionalDerivative X
          (fun q => cramerInverse (gramMatrixField g F q) i j
            * curvatureTensorFour D (F i) Y Z (F j) q) p
        = cramerInverse (gramMatrixField g F p) i j
            * directionalDerivative X (curvatureTensorFour D (F i) Y Z (F j)) p
          + curvatureTensorFour D (F i) Y Z (F j) p
            * directionalDerivative X
                (fun q => cramerInverse (gramMatrixField g F q) i j) p :=
      directionalDerivative_mul ((hGinvSm i j).mdifferentiableAt (by simp))
        (((hR4sm i j) p).mdifferentiableAt (by simp)) X
    rw [hmul, hG1, cramerInverse_one, Matrix.one_apply]
  -- Step 4: collapse the Kronecker delta
  have hdelta : ∀ f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∑ i, ∑ j, (if i = j then (1:ℝ) else 0) * f i j) = ∑ i, f i i := by
    intro f
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : ∀ j, (if i = j then (1:ℝ) else 0) * f i j
        = if i = j then f i j else 0 := fun j => by split_ifs <;> simp
    rw [Finset.sum_congr rfl fun j _ => he j, Finset.sum_ite_eq]
    simp
  -- Step 5: rearranged Leibniz rule for each diagonal term
  have hcdc : ∀ i, directionalDerivative X
        (curvatureTensorFour D (F i) Y Z (F i)) p
      = covariantDerivativeCurvatureFour D X (F i) Y Z (F i) p
        + curvatureTensorFour D
            (D.toAffineConnection.covField X (F i)) Y Z (F i) p
        + curvatureTensorFour D (F i)
            (D.toAffineConnection.covField X Y) Z (F i) p
        + curvatureTensorFour D (F i) Y
            (D.toAffineConnection.covField X Z) (F i) p
        + curvatureTensorFour D (F i) Y Z
            (D.toAffineConnection.covField X (F i)) p := by
    intro i
    have h := covariantDerivativeCurvatureFour_apply D X (F i) Y Z (F i) p
    linarith
  -- pointwise conversions
  have hcovF : ∀ i, IsSmoothVectorField
      (D.toAffineConnection.covField X (F i)) := fun i => D.smooth_cov hX (hF i)
  have hcovY : IsSmoothVectorField (D.toAffineConnection.covField X Y) :=
    D.smooth_cov hX hY
  have hcovZ : IsSmoothVectorField (D.toAffineConnection.covField X Z) :=
    D.smooth_cov hX hZ
  have hconv1 : ∀ i, curvatureTensorFour D
        (D.toAffineConnection.covField X (F i)) Y Z (F i) p
      = curvatureTensorFourAt D p (D.cov p (X p) (F i)) (Y p) (Z p) (b i) := by
    intro i
    rw [← curvatureTensorFourAt_apply D (hcovF i) hY hZ p, hb i]
    rfl
  have hconv2 : ∀ i, curvatureTensorFour D (F i)
        (D.toAffineConnection.covField X Y) Z (F i) p
      = curvatureTensorFourAt D p (b i)
          (D.toAffineConnection.covField X Y p) (Z p) (b i) := by
    intro i
    rw [← curvatureTensorFourAt_apply D (hF i) hcovY hZ p, hb i]
  have hconv3 : ∀ i, curvatureTensorFour D (F i) Y
        (D.toAffineConnection.covField X Z) (F i) p
      = curvatureTensorFourAt D p (b i) (Y p)
          (D.toAffineConnection.covField X Z p) (b i) := by
    intro i
    rw [← curvatureTensorFourAt_apply D (hF i) hY hcovZ p, hb i]
  have hconv4 : ∀ i, curvatureTensorFour D (F i) Y Z
        (D.toAffineConnection.covField X (F i)) p
      = curvatureTensorFourAt D p (b i) (Y p) (Z p) (D.cov p (X p) (F i)) := by
    intro i
    rw [← curvatureTensorFourAt_apply D (hF i) hY hZ p, hb i]
    rfl
  have hconvR4 : ∀ i j, curvatureTensorFour D (F i) Y Z (F j) p
      = curvatureTensorFourAt D p (b i) (Y p) (Z p) (b j) := by
    intro i j
    rw [← curvatureTensorFourAt_apply D (hF i) hY hZ p, hb i, hb j]
  -- Step 6: the Gram-inverse derivative
  have hddGinv : ∀ i j, directionalDerivative X
        (fun q => cramerInverse (gramMatrixField g F q) i j) p
      = -(g.metricInner p (D.cov p (X p) (F i)) (b j)
          + g.metricInner p (b i) (D.cov p (X p) (F j))) := by
    intro i j
    rw [hb i, hb j]
    exact directionalDerivative_cramerInverse_gram D hF X horth i j
  -- Step 7: the Ricci corrections through the trace formula
  have hric1 : RicciCurvature D.toAffineConnection p
        (D.toAffineConnection.covField X Y p) (Z p)
      = ∑ i, curvatureTensorFourAt D p (b i)
          (D.toAffineConnection.covField X Y p) (Z p) (b i) :=
    ricciCurvature_eq_sum D p b hbo _ _
  have hric2 : RicciCurvature D.toAffineConnection p (Y p)
        (D.toAffineConnection.covField X Z p)
      = ∑ i, curvatureTensorFourAt D p (b i) (Y p)
          (D.toAffineConnection.covField X Z p) (b i) :=
    ricciCurvature_eq_sum D p b hbo _ _
  -- Step 8: assemble
  set A : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => D.cov p (X p) (F i) with hA
  have E1 : directionalDerivative X
        (fun q => RicciCurvature D.toAffineConnection q (Y q) (Z q)) p
      = (∑ i, covariantDerivativeCurvatureFour D X (F i) Y Z (F i) p)
        + (∑ i, curvatureTensorFourAt D p (A i) (Y p) (Z p) (b i))
        + (∑ i, curvatureTensorFourAt D p (b i)
            (D.toAffineConnection.covField X Y p) (Z p) (b i))
        + (∑ i, curvatureTensorFourAt D p (b i) (Y p)
            (D.toAffineConnection.covField X Z p) (b i))
        + (∑ i, curvatureTensorFourAt D p (b i) (Y p) (Z p) (A i))
        + ∑ i, ∑ j, curvatureTensorFourAt D p (b i) (Y p) (Z p) (b j)
            * -(g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
    rw [hdd1, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl
      fun j _ => hprod i j]
    have hsplit : ∑ i, ∑ j, ((if i = j then (1:ℝ) else 0)
          * directionalDerivative X (curvatureTensorFour D (F i) Y Z (F j)) p
        + curvatureTensorFour D (F i) Y Z (F j) p
          * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) i j) p)
        = (∑ i, ∑ j, (if i = j then (1:ℝ) else 0)
            * directionalDerivative X
                (curvatureTensorFour D (F i) Y Z (F j)) p)
          + ∑ i, ∑ j, curvatureTensorFour D (F i) Y Z (F j) p
              * directionalDerivative X
                  (fun q => cramerInverse (gramMatrixField g F q) i j) p := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]
    rw [hsplit, hdelta]
    have hdiag : ∑ i, directionalDerivative X
          (curvatureTensorFour D (F i) Y Z (F i)) p
        = (∑ i, covariantDerivativeCurvatureFour D X (F i) Y Z (F i) p)
          + (∑ i, curvatureTensorFourAt D p (A i) (Y p) (Z p) (b i))
          + (∑ i, curvatureTensorFourAt D p (b i)
              (D.toAffineConnection.covField X Y p) (Z p) (b i))
          + (∑ i, curvatureTensorFourAt D p (b i) (Y p)
              (D.toAffineConnection.covField X Z p) (b i))
          + ∑ i, curvatureTensorFourAt D p (b i) (Y p) (Z p) (A i) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcdc i, hconv1 i, hconv2 i, hconv3 i, hconv4 i]
    have hoff : ∑ i, ∑ j, curvatureTensorFour D (F i) Y Z (F j) p
          * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) i j) p
        = ∑ i, ∑ j, curvatureTensorFourAt D p (b i) (Y p) (Z p) (b j)
            * -(g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hconvR4 i j, hddGinv i j]
    rw [hdiag, hoff]
  have E2 : ∑ i, ∑ j, curvatureTensorFourAt D p (b i) (Y p) (Z p) (b j)
        * -(g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j))
      = -∑ i, ∑ j, curvatureTensorFourAt D p (b i) (Y p) (Z p) (b j)
          * (g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have E3 : (∑ i, curvatureTensorFourAt D p (A i) (Y p) (Z p) (b i))
        + ∑ i, curvatureTensorFourAt D p (b i) (Y p) (Z p) (A i)
      = ∑ i, ∑ j, curvatureTensorFourAt D p (b i) (Y p) (Z p) (b j)
          * (g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
    rw [← Finset.sum_add_distrib]
    exact frame_correction_cancel D p b hbo A (Y p) (Z p)
  rw [covariantDerivativeRicci_apply, E1, E2, hric1, hric2]
  linarith [E3]

/-! ## Trace–derivative commutation for the scalar curvature -/

theorem ricciCurvature_sum_smul_left (D : AffineConnection I M) (p : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : ι → TangentSpace I p)
    (w : TangentSpace I p) :
    RicciCurvature D p (∑ j ∈ s, c j • v j) w
      = ∑ j ∈ s, c j * RicciCurvature D p (v j) w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [show RicciCurvature D p 0 w = 0 by
      simpa using ricciCurvature_smul_left D p 0 0 w]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ricciCurvature_add_left,
        ricciCurvature_smul_left, ih, Finset.sum_insert ha]

theorem ricciCurvature_sum_smul_right (D : AffineConnection I M) (p : M)
    {ι : Type*} (s : Finset ι) (c : ι → ℝ) (v : TangentSpace I p)
    (w : ι → TangentSpace I p) :
    RicciCurvature D p v (∑ j ∈ s, c j • w j)
      = ∑ j ∈ s, c j * RicciCurvature D p v (w j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [show RicciCurvature D p v 0 = 0 by
      simpa using ricciCurvature_smul_right D p 0 v 0]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, ricciCurvature_add_right,
        ricciCurvature_smul_right, ih, Finset.sum_insert ha]

/-- The Ricci analogue of `frame_correction_cancel`. -/
private theorem ricci_frame_correction_cancel (D : RiemannianConnection I g)
    (p : M) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0)
    (A : ι → TangentSpace I p) :
    ∑ i, (RicciCurvature D.toAffineConnection p (A i) (b i)
        + RicciCurvature D.toAffineConnection p (b i) (A i))
      = ∑ i, ∑ j, RicciCurvature D.toAffineConnection p (b i) (b j)
          * (g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
  classical
  have hA : ∀ i, A i = ∑ j, g.metricInner p (A i) (b j) • b j := by
    intro i
    conv_lhs => rw [← b.sum_repr (A i)]
    exact Finset.sum_congr rfl fun j _ => by
      rw [orthonormal_basis_repr_eq_metricInner p b hb]
  have hfirst : ∀ i, RicciCurvature D.toAffineConnection p (A i) (b i)
      = ∑ j, g.metricInner p (A i) (b j)
          * RicciCurvature D.toAffineConnection p (b j) (b i) := by
    intro i
    conv_lhs => rw [hA i]
    exact ricciCurvature_sum_smul_left D.toAffineConnection p Finset.univ _ b
      (b i)
  have hlast : ∀ i, RicciCurvature D.toAffineConnection p (b i) (A i)
      = ∑ j, g.metricInner p (A i) (b j)
          * RicciCurvature D.toAffineConnection p (b i) (b j) := by
    intro i
    conv_lhs => rw [hA i]
    exact ricciCurvature_sum_smul_right D.toAffineConnection p Finset.univ _
      (b i) b
  have hsplit : ∑ i, (RicciCurvature D.toAffineConnection p (A i) (b i)
        + RicciCurvature D.toAffineConnection p (b i) (A i))
      = (∑ i, ∑ j, g.metricInner p (A i) (b j)
            * RicciCurvature D.toAffineConnection p (b j) (b i))
        + ∑ i, ∑ j, g.metricInner p (A i) (b j)
            * RicciCurvature D.toAffineConnection p (b i) (b j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfirst i, hlast i, ← Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, g.metricInner p (A i) (b j)
        * RicciCurvature D.toAffineConnection p (b j) (b i))
      = ∑ i, ∑ j, g.metricInner p (A j) (b i)
          * RicciCurvature D.toAffineConnection p (b i) (b j) :=
    Finset.sum_comm
  rw [hsplit, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [g.metricInner_comm p (b i) (A j)]
  ring

/-- **Math.** **The differential of the scalar curvature is the trace of
`∇Ric`**: for a smooth frame `F` that is `g`-orthonormal at `p`,
`d(scal)(X)|_p = ∑ᵢ (∇_X Ric)(Fᵢ, Fᵢ)|_p`. -/
theorem directionalDerivative_scalarCurvature_eq_sum
    (D : RiemannianConnection I g)
    {F : Fin (Module.finrank ℝ E) → Π x : M, TangentSpace I x}
    (hF : ∀ i, IsSmoothVectorField (F i))
    (X : Π x : M, TangentSpace I x) {p : M}
    (horth : ∀ i j, g.metricInner p (F i p) (F j p) = if i = j then 1 else 0) :
    directionalDerivative X (scalarCurvature D) p
      = ∑ i, covariantDerivativeRicci D X (F i) (F i) p := by
  classical
  have hev := gramMatrixField_det_ne_zero_eventually hF horth
  have hG1 : gramMatrixField g F p = 1 :=
    gramMatrixField_eq_one_of_orthonormal horth
  have hdetp : (gramMatrixField g F p).det ≠ 0 := by
    rw [hG1, Matrix.det_one]
    exact one_ne_zero
  have hGsm : ∀ a b, ContMDiff I 𝓘(ℝ) ∞
      (fun q => gramMatrixField g F q a b) :=
    fun a b => contMDiff_gramMatrixField_entry hF a b
  have hGinvSm : ∀ a b, ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => cramerInverse (gramMatrixField g F q) a b) p :=
    fun a b => contMDiffAt_matrix_cramerInverse (fun c d => hGsm c d) hdetp a b
  have hRicsm : ∀ i j, ContMDiff I 𝓘(ℝ) ∞
      (fun q => RicciCurvature D.toAffineConnection q (F i q) (F j q)) :=
    fun i j => contMDiff_ricciCurvature_eval D (hF i) (hF j)
  obtain ⟨b, hbcoe⟩ := exists_orthonormalBasis_of_family p horth
  have hb : ∀ i, b i = F i p := fun i => congrFun hbcoe i
  have hbo : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    rw [hb i, hb j]
    exact horth i j
  -- Step 1: the local Gram-inverse model for `scal`
  have hlocal : scalarCurvature D
      =ᶠ[𝓝 p] fun q => ∑ i, ∑ j, cramerInverse (gramMatrixField g F q) i j
        * RicciCurvature D.toAffineConnection q (F i q) (F j q) := by
    filter_upwards [hev] with q hq
    exact scalarCurvature_eq_sum_gramInv D hq
  -- Step 2: differentiate the double sum
  have hterm_sm : ∀ i j, ContMDiffAt I 𝓘(ℝ) ∞
      (fun q => cramerInverse (gramMatrixField g F q) i j
        * RicciCurvature D.toAffineConnection q (F i q) (F j q)) p :=
    fun i j => (hGinvSm i j).mul ((hRicsm i j) p)
  have hdd1 : directionalDerivative X (scalarCurvature D) p
      = ∑ i, ∑ j, directionalDerivative X
          (fun q => cramerInverse (gramMatrixField g F q) i j
            * RicciCurvature D.toAffineConnection q (F i q) (F j q)) p := by
    rw [directionalDerivative_congr_nhds hlocal X,
      directionalDerivative_finsetSum Finset.univ
        (fun i _ => ContMDiffAt.sum fun j _ => hterm_sm i j) X]
    exact Finset.sum_congr rfl fun i _ =>
      directionalDerivative_finsetSum Finset.univ (fun j _ => hterm_sm i j) X
  -- Step 3: product rule; `G⁻¹(p) = 1`
  have hprod : ∀ i j, directionalDerivative X
        (fun q => cramerInverse (gramMatrixField g F q) i j
          * RicciCurvature D.toAffineConnection q (F i q) (F j q)) p
      = (if i = j then 1 else 0) * directionalDerivative X
            (fun q => RicciCurvature D.toAffineConnection q (F i q) (F j q)) p
        + RicciCurvature D.toAffineConnection p (F i p) (F j p)
          * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) i j) p := by
    intro i j
    have hmul : directionalDerivative X
          (fun q => cramerInverse (gramMatrixField g F q) i j
            * RicciCurvature D.toAffineConnection q (F i q) (F j q)) p
        = cramerInverse (gramMatrixField g F p) i j * directionalDerivative X
              (fun q => RicciCurvature D.toAffineConnection q (F i q) (F j q)) p
          + RicciCurvature D.toAffineConnection p (F i p) (F j p)
            * directionalDerivative X
                (fun q => cramerInverse (gramMatrixField g F q) i j) p :=
      directionalDerivative_mul ((hGinvSm i j).mdifferentiableAt (by simp))
        (((hRicsm i j) p).mdifferentiableAt (by simp)) X
    rw [hmul, hG1, cramerInverse_one, Matrix.one_apply]
  have hdelta : ∀ f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ,
      (∑ i, ∑ j, (if i = j then (1:ℝ) else 0) * f i j) = ∑ i, f i i := by
    intro f
    refine Finset.sum_congr rfl fun i _ => ?_
    have he : ∀ j, (if i = j then (1:ℝ) else 0) * f i j
        = if i = j then f i j else 0 := fun j => by split_ifs <;> simp
    rw [Finset.sum_congr rfl fun j _ => he j, Finset.sum_ite_eq]
    simp
  -- Step 4: rearranged Leibniz rule for each diagonal term
  have hcdc : ∀ i, directionalDerivative X
        (fun q => RicciCurvature D.toAffineConnection q (F i q) (F i q)) p
      = covariantDerivativeRicci D X (F i) (F i) p
        + RicciCurvature D.toAffineConnection p (D.cov p (X p) (F i)) (F i p)
        + RicciCurvature D.toAffineConnection p (F i p)
            (D.cov p (X p) (F i)) := by
    intro i
    have h := covariantDerivativeRicci_apply D X (F i) (F i) p
    have hc : D.toAffineConnection.covField X (F i) p
        = D.cov p (X p) (F i) := rfl
    rw [hc] at h
    linarith
  -- Step 5: the Gram-inverse derivative and the corrections cancel
  have hddGinv : ∀ i j, directionalDerivative X
        (fun q => cramerInverse (gramMatrixField g F q) i j) p
      = -(g.metricInner p (D.cov p (X p) (F i)) (b j)
          + g.metricInner p (b i) (D.cov p (X p) (F j))) := by
    intro i j
    rw [hb i, hb j]
    exact directionalDerivative_cramerInverse_gram D hF X horth i j
  set A : Fin (Module.finrank ℝ E) → TangentSpace I p :=
    fun i => D.cov p (X p) (F i) with hA
  have E1 : directionalDerivative X (scalarCurvature D) p
      = (∑ i, covariantDerivativeRicci D X (F i) (F i) p)
        + (∑ i, (RicciCurvature D.toAffineConnection p (A i) (b i)
            + RicciCurvature D.toAffineConnection p (b i) (A i)))
        + ∑ i, ∑ j, RicciCurvature D.toAffineConnection p (b i) (b j)
            * -(g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
    rw [hdd1, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl
      fun j _ => hprod i j]
    have hsplit : ∑ i, ∑ j, ((if i = j then (1:ℝ) else 0)
          * directionalDerivative X
              (fun q => RicciCurvature D.toAffineConnection q (F i q) (F j q)) p
        + RicciCurvature D.toAffineConnection p (F i p) (F j p)
          * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) i j) p)
        = (∑ i, ∑ j, (if i = j then (1:ℝ) else 0)
            * directionalDerivative X
                (fun q => RicciCurvature D.toAffineConnection q
                  (F i q) (F j q)) p)
          + ∑ i, ∑ j, RicciCurvature D.toAffineConnection p (F i p) (F j p)
              * directionalDerivative X
                  (fun q => cramerInverse (gramMatrixField g F q) i j) p := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [← Finset.sum_add_distrib]
    rw [hsplit, hdelta]
    have hdiag : ∑ i, directionalDerivative X
          (fun q => RicciCurvature D.toAffineConnection q (F i q) (F i q)) p
        = (∑ i, covariantDerivativeRicci D X (F i) (F i) p)
          + ∑ i, (RicciCurvature D.toAffineConnection p (A i) (b i)
              + RicciCurvature D.toAffineConnection p (b i) (A i)) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hcdc i, hb i]
      ring
    have hoff : ∑ i, ∑ j, RicciCurvature D.toAffineConnection p (F i p) (F j p)
          * directionalDerivative X
              (fun q => cramerInverse (gramMatrixField g F q) i j) p
        = ∑ i, ∑ j, RicciCurvature D.toAffineConnection p (b i) (b j)
            * -(g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hddGinv i j, hb i, hb j]
    rw [hdiag, hoff]
  have E2 : ∑ i, ∑ j, RicciCurvature D.toAffineConnection p (b i) (b j)
        * -(g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j))
      = -∑ i, ∑ j, RicciCurvature D.toAffineConnection p (b i) (b j)
          * (g.metricInner p (A i) (b j) + g.metricInner p (b i) (A j)) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have E3 := ricci_frame_correction_cancel D p b hbo A
  rw [E1, E2]
  linarith [E3]

end PetersenLib
